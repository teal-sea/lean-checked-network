---
license: apache-2.0
---


# Lexnet
A neural network to generate syntax highlighting for C code, with the weights generated entirely by Anthropic's Claude Fable 5.1.

The model has about 984 parameters, with the other 9,556 being basically dense params that don't do much but pad out the useful weight matrices so they can multiply nicely.

## Usage
```sh
git clone https://huggingface.co/alpindale/lexnet.git && cd lexnet
cc -O3 -march=native -o lexnet lexnet.c -lm

./lexnet -w lexnet_weights.bin lexnet.c
```

## Model Details
| | |
| -- | -- |
| Developer | Claude Fable 5.1 |
| Type | bidirectional recurrent network, per-character sequence tagger |
| Task | Token classification over C source |
| Input | bytes (ASCII; ≥128 mapped to a null row) |
| Output | one class id per byte |
| Parameters | 984 non-zero; 9,566 dense |
| Recurrent state | 18 units forward, 7 backward |
| Depth | 6 forward layers, 2 backward layers, 1 linear head |
| Activations | `Clip(x, 0, hi)` — `hi=1` (ReLU1) for logic units, ∞ for two accumulators, 14 for a counter |
| Precision | float64 |
| Training data | None |
| Training compute | None |

## Performance
188 KB corpus, Apple M4 Pro:

![image](https://cdn-uploads.huggingface.co/production/uploads/635567189c72a7e742f1419c/plIzkVGgNC22JPjAxHwn0.png)

| executor | ns/char | K chars/s |
| -- | -- | -- |
| numpy reference | 17,000 | 59 |
| lexnet --interp (CSR, ~1K MACs/char) | 417 | 2,398 |
| Pygments `CLexer` | 447 | 2,238 |
| **lexnet compiled kernel** | **88** | **11,326** |
| tree-sitter-c parse + highlight query | 100 | 10,010 |
| tree-sitter-c parse only | 51 | 19,448 |