# The circle explanation as a proof

`mechanism.py` turns "the network adds angles on a circle" into a certificate: a computation in
exact integer arithmetic that, for each input pair it passes, proves the network's top answer
is `(a + b) mod p`. This file states the argument and its current reach. Status: **derived**.
The arithmetic is exact and the decomposition is checked against the real network on random
samples, but the argument is not yet written in Lean.

## Setting

The score of answer `c` for inputs `(a, b)` is

    N(a, b, c) = Σ_h W2[c, h] · (E1[a, h] + E2[b, h])²

with whole-number weights. Expanding the square:

    N = U[c, a] + V[c, b] + 2·X(a, b, c)
    U[c, a] = Σ_h W2[c,h]·E1[a,h]²      V[c, b] = Σ_h W2[c,h]·E2[b,h]²
    X(a, b, c) = Σ_h W2[c,h]·E1[a,h]·E2[b,h]

`U` and `V` are 113 × 113 tables, computed exactly. `X` is the part that would need all
113³ triples; the circle is what avoids that.

## The circle, in whole numbers

For each frequency `k`, the circle table is `Z_k(x) = round(M·cos(2πkx/p)) + i·round(M·sin(2πkx/p))`
with `M = 2^20`, a Gaussian integer for each `x`. Rounding is symmetric, so
`conj(Z_k(x)) = Z_k(-x)` exactly (checked). The angle-addition rule holds up to an exact defect:

    Z_k(x)·Z_k(y) = M·Z_k(x + y) + D_k(x, y)

`D_k` is computed for all `p²` pairs and its largest entry recorded.

Each neuron `h` has one frequency `k` (the one carrying most of its weight energy). Each of its
three weight columns is written, exactly, as a circle wave plus a remainder:

    2^30 · E1[x, h] = Re(ε_h · Z_k(x)) + r1_h(x)

and likewise for `E2` (coefficient φ_h, remainder r2_h) and `W2` (ψ_h, rw_h). The coefficients are
fitted (rounded Gaussian integers); the remainders are whatever is left, so the identity is exact
whatever the fit.

## The decomposition

Multiplying out `(wave + remainder)` three times splits `2^90·X` into:

1. **Three waves.** `Re(εZ(a))·Re(φZ(b))·Re(ψZ(c))` is, exactly, a quarter of
   `Re[εφψ Z(a)Z(b)Z(c) + εφψ̄ Z(a)Z(b)Z(-c) + εφ̄ψ Z(a)Z(-b)Z(c) + εφ̄ψ̄ Z(a)Z(-b)Z(-c)]`.
   Two uses of the angle-addition rule turn each product into one wave of a single combination
   (`a+b+c`, `a+b-c`, `a-b+c`, `a-b-c`) plus a bounded defect. Summed over neurons, the
   `a+b-c` wave peaks exactly at `c = a + b`: **this is the mechanism**. The other three are
   tables of 113 values each.
2. **One remainder, two waves.** For example `rw_h(c)·wave_e(a)·wave_f(b)`: the two waves combine
   by the same rule into a wave of `a+b` or `a-b`, giving a 113 × 113 table in `(c, a±b)`.
   Same for the `E1` and `E2` remainders.
3. **Two or more remainders.** Bounded per `(a, b)`, uniformly in `c`, by the Cauchy-Schwarz
   inequality over the neurons, with exact integer square roots rounded up.

## The certificate

For a pair `(a, b)` with `s = (a + b) mod p`, the network is right if `N(a,b,s) > N(a,b,c)` for
every `c ≠ s`. Each piece of the decomposition is a table indexed by one combination of `a`, `b`,
`c`, so its worst case over `c ≠ s` comes from the top two entries of that table: no loop over
`c` per pair is needed. The certificate adds those worst cases, subtracts the error bounds, and
passes if the total is positive. Total work is about `p²·H` multiplications for the whole table
(about 21 million here, counted from the code), against about 186 million for checking every score directly.

## Checks that the argument is sound

`mechanism.py` exits non-zero unless both hold:

- On 300 random triples `(a, b, c)`, the real score and the decomposition differ by at most the
  stated error bound (worst ratio seen: 0.12).
- On 200 random pairs, the certified lower bound never exceeds the true gap between the right
  answer's score and the best wrong one (0 violations).

## Where it stands

On the network in `network/trained.npz`: **10,473 of 12,769 pairs certified (82%)**.
Per-term costs, as a fraction of the peak wave's margin (median over a grid of pairs):

| Piece | Median cost |
| --- | --- |
| the other three waves | 0.13 |
| `W2` remainder through the circle | 0.11 |
| `E1` and `E2` remainders through the circle | 0.10 and 0.09 |
| `U` and `V` | 0.06 each |
| second-order remainders (Cauchy-Schwarz) | 0.37 |
| circle rounding | below 0.0001 |

The largest cost is the second-order bound, and it is loose: on samples the true second-order
term is about a tenth of the bound, because Cauchy-Schwarz assumes the remainders line up
across 114 neurons and they do not. Two further observations:

- Coverage rose with training: 69%, 77%, 85% at steps 12,000, 14,000 and 16,000, then 84% and
  82% at 18,000 and 20,000. The network used here is the final one, not the best checkpoint.
- In every live neuron the biggest remainder is the third harmonic (frequency `3k`). Adding it
  to the waves (`--harmonics 1,3`) shrinks the second-order cost but multiplies the number of
  wave tables, and coverage drops to 40% (5,062 pairs): summing worst cases over more tables costs more than
  the smaller remainder saves.

## Next steps

1. Tighten the second-order bound without paying `p³` (for example by grouping neurons by
   frequency before applying Cauchy-Schwarz).
2. Write the decomposition and its bounds in Lean, so the 82% (or more) becomes kernel-checked
   and the circle explanation becomes a theorem, not just an ablation.
