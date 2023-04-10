# Halo2 verify MNIST

## How to run

Compile the repo

```
cargo build
```

Run the prove example
```
cargo run
```

Retrain the CNN and generate quantized weight:
```
rm ck.pt
python3 quantize.py
```
