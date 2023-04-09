import torch
import torch.nn.functional as F
import torch.nn as nn
import matplotlib.pyplot as plt
from torch.utils.data import DataLoader
from torchvision import datasets, transforms
BATCH_SIZE = 128
test_file = datasets.MNIST(
    root='./data/',
    train=False,
    transform=transforms.ToTensor()
)
test_loader = DataLoader(
    dataset=test_file,
    batch_size=BATCH_SIZE,
    shuffle=False
)

model=torch.jit.load("ck.pt")
model.eval()

for param in model.parameters():
    print(type(param), param.size())
#uint8_np_ndarray = torch.int_repr(model.conv1).numpy()
#print(f'{uint8_np_ndarray.dtype}\n{uint8_np_ndarray}')
total = 0
correct = 0
with torch.no_grad():
    for data, targets in test_loader:
        data = data.cpu()
        targets = targets.cpu()
        output = model(data)
        correct += (output.argmax(1) == targets).sum()
        total += data.size(0)
print(correct.item()/total)