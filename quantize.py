import torch
import torch.nn.functional as F
import torch.nn as nn
import matplotlib.pyplot as plt
from torch.utils.data import DataLoader
from torchvision import datasets, transforms
import pickle
import numpy as np
import os

class CNN(nn.Module):
    def __init__(self):
        super(CNN, self).__init__()
        self.quant = torch.quantization.QuantStub()  # QuantStub: 
        self.conv1 = nn.Conv2d(1, 5, 5, 2, bias=False)
        self.conv2=nn.Conv2d(5, 10, 5, 2, bias=False)
        self.fc = nn.Linear(10 * 4 * 4, 10, bias=False)
        self.dequant = torch.quantization.DeQuantStub() 

    def forward(self, x):
        x = self.quant(x)  
        x=self.conv1(x)
        x = F.relu(x)
        x= self.conv2(x)
        x=F.relu(x)
        x = x.reshape(x.size(0), -1)
        y = self.fc(x)
        y = self.dequant(y)  
        return y

device = torch.device('cuda:0' if torch.cuda.is_available() else 'cpu')
train_file = datasets.MNIST(
    root='./dataset/',
    train=True,
    transform=transforms.ToTensor()
)
train_loader = DataLoader(
    dataset=train_file,
    batch_size=128,
    shuffle=False
)
test_file = datasets.MNIST(
    root='./dataset/',
    train=False,
    transform=transforms.ToTensor()
)
test_loader = DataLoader(
    dataset=test_file,
    batch_size=1024,
    shuffle=False
)

if not os.path.exists("ck.pt"):
    model = CNN().to(device)
    optim = torch.optim.Adam(model.parameters(), 1e-3)
    lossf = nn.CrossEntropyLoss()
    ANS=[]
    for epoch in range(3):
        for step, (data, targets) in enumerate(train_loader):
            if step<5:
                ANS.append(data)
            optim.zero_grad()
            data = data.to(device)
            targets = targets.to(device)
            output = model(data)
            loss = lossf(output, targets)
            loss.backward()
            optim.step()
        print(f"{epoch} end!")
    loss = 0
    total = 0
    correct = 0
    with torch.no_grad():
        for data, targets in test_loader:
            data = data.to(device)
            targets = targets.to(device)
            output = model(data)
            loss += lossf(output, targets)
            correct += (output.argmax(1) == targets).sum()
            total += data.size(0)
    loss = loss.item()/len(test_loader)
    acc = correct.item()/total
    print(acc)
    torch.save(model.state_dict(),"ck.pt")



model=CNN()
model.load_state_dict(torch.load("ck.pt"))
model.qconfig = torch.quantization.get_default_qconfig('qnnpack')
model_fp32_prepared = torch.quantization.prepare(model)
input_fp32=pickle.load(open("1.pic",'rb'))
model_fp32_prepared(input_fp32)
model_int8 = torch.quantization.convert(model_fp32_prepared)
uint8_np_ndarray = torch.int_repr(model_int8.conv1.weight()).numpy()
IMAGE_WIDTH=28
LAYER2_WIDTH=4
conv1_intw=torch.int_repr(model_int8.conv1.weight()).numpy()
conv2_intw=torch.int_repr(model_int8.conv2.weight()).numpy()
fc_intw=torch.int_repr(model_int8.fc.weight()).numpy()
fc_intw=np.transpose(fc_intw)  # 320,10

def save_conv_kernel(conv_w,file):
    fi=open(file,"wb")
    OUT,IN,K,_=conv_w.shape 
    for i in range(OUT):
        for j in range(IN):
            for k in range(K):
                for p in range(K):
                    w=conv_w[i][j][k][p].item()
                    fi.write(w.to_bytes(4,'little',signed=True))
    fi.close()

def save_linear_kernel(w,file):
    fi=open(file,"wb")
    OUT,IN=w.shape 
    for i in range(OUT):
        for j in range(IN):
            fi.write(w[i][j].item().to_bytes(4,'little',signed=True))
    fi.close()


save_conv_kernel(conv1_intw,"conv1.dat")
save_conv_kernel(conv2_intw,"conv2.dat")
save_linear_kernel(fc_intw,"fc1.dat")

def conv_kernel(data,conv_w,STRIDE): 
    OUTPUT_C,INPUT_C,K,_=conv_w.shape
    C,IMAGE_WIDTH,_=data.shape
    LAYER_WIDTH= (IMAGE_WIDTH-K+1)//STRIDE
    output=np.zeros((OUTPUT_C,LAYER_WIDTH,LAYER_WIDTH))
    for output_c in range(OUTPUT_C):
        for x in range(LAYER_WIDTH):
            for y in range(LAYER_WIDTH):
                for input_c in range(INPUT_C):
                    for p in range(K):
                        for q in range(K):
                            output[output_c][x][y]+=data[input_c][x*STRIDE+p][y*STRIDE+q]*conv_w[output_c][input_c][p][q]
    return output


def linear_kernel(data,l_w):
    BATCH, DIM=data.shape
    DIM, OUT=l_w.shape
    output=np.zeros((BATCH, OUT))
    for b in range(BATCH):
        for out in range(OUT):
            for _in in range(DIM):
                output[b][out]+=data[b][_in]*l_w[_in][out]
    return output

def scale_then_clip(data,s):
    act_after_scale=np.floor(data/s)
    act_after_relu=np.clip(act_after_scale,0,63)
    return act_after_relu
S1=1024
S2=1024

CNT=0
TOT=0
for data, targets in test_loader:
    data = data.cpu()
    break

def save_img(img,file):
    fi=open(file,"wb")
    C,H,W=img.shape 
    for c in range(C):
        for i in range(H):
            for j in range(W):
                fi.write(int(img[c][i][j].item()).to_bytes(4,'little',signed=True))
    fi.close()

def gen_conv_kernel_layout(data,conv_w,STRIDE,file): 
    fi=open(file,"wb")
    OUTPUT_C,INPUT_C,K,_=conv_w.shape
    C,IMAGE_WIDTH,_=data.shape
    LAYER_WIDTH= (IMAGE_WIDTH-K+1)//STRIDE
    for output_c in range(OUTPUT_C):
        for x in range(LAYER_WIDTH):
            for y in range(LAYER_WIDTH):
                for input_c in range(INPUT_C):
                    for p in range(K):
                        for q in range(K):
                            dt_idx= input_c*IMAGE_WIDTH*IMAGE_WIDTH+  (x*STRIDE+p)*IMAGE_WIDTH+y*STRIDE+q
                            conv_idx=output_c*INPUT_C*K*K+input_c*K*K+p*K+q 
                            fi.write(dt_idx.to_bytes(4,'little',signed=True))
                            fi.write(conv_idx.to_bytes(4,'little',signed=True))
    return

def gen_linear_kernel_layout(data,l_w,file):
    fi=open(file,"wb")
    BATCH, DIM=data.shape
    DIM, OUT=l_w.shape
    output=np.zeros((BATCH, OUT))
    for b in range(BATCH):
        for out in range(OUT):
            for _in in range(DIM):
                dt_idx=b*DIM+_in
                l_idx=_in*OUT+out
                fi.write(dt_idx.to_bytes(4,'little',signed=True))
                fi.write(l_idx.to_bytes(4,'little',signed=True))

fi=open("results.dat","wb")
for id in range(len(data)):
    dt=data[id].numpy()
    dt=np.floor(dt*64)
    save_img(dt,f"images/img{id}.dat")
    output=conv_kernel(dt,conv1_intw,2)
    gen_conv_kernel_layout(dt,conv1_intw,2,"conv1.layout")
    act1_after_relu=scale_then_clip(output,S1)
    output2=conv_kernel(act1_after_relu,conv2_intw,2)
    gen_conv_kernel_layout(act1_after_relu,conv2_intw,2,"conv2.layout")
    act2_after_relu=scale_then_clip(output2,S2)
    after_reshape=np.reshape(act2_after_relu,[1,160])
    out=linear_kernel(after_reshape,fc_intw)
    gen_linear_kernel_layout(after_reshape,fc_intw,"fc1.layout")
    fi.write(out[0].argmax().item().to_bytes(4,'little',signed=True))
    fi.write(targets[id].item().to_bytes(4,'little',signed=True))
    if out[0].argmax()==targets[id]:
        CNT+=1
    if TOT%100==99:
        print(f"ACC: {CNT/TOT*100} Tested on: {TOT}")
        break
fi.close()
