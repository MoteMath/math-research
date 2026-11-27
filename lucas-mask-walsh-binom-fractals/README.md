# Bitwise-Weighted Binomial & Lucas-Mask Fractal Engine (`adic-9`) (`lucas-mask-walsh-binom-fractals`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **9 / 10** | **8 / 10** | **8 / 10** | **10 / 10** | **84 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): **Name:** The Three-Stage Lucas-Mask Bit-Slice & 2-Adic Bit-Smoothness Engine (`LucasMaskEngine`). **Core Silicon Principle (Finite $\to$ Infinite Bridge):** Treating Lucas's theorem mod $2$ as a silicon bitmask filter $k \subseteq _ 2 n$ (`k &&& n = k`, equivalently `k & ~n = 0`), we construct a **reusable three-stage infinite proof engine** that lifts finite LSB bit-slice tra*

## For Mathematicians

**Name:** The Three-Stage Lucas-Mask Bit-Slice & 2-Adic Bit-Smoothness Engine (`LucasMaskEngine`). **Core Silicon Principle (Finite $\to$ Infinite Bridge):** Treating Lucas's theorem mod $2$ as a silicon bitmask filter $k \subseteq _ 2 n$ (`k &&& n = k`, equivalently `k & ~n = 0`), we construct a **reusable three-stage infinite proof engine** that lifts finite LSB bit-slice transition rules and a 2-state finite-state bitmask transducer into sharp, universally quantified ($\forall n, r, m \in \mathbb{N}$) 2-adic congruences and exact $v _ 2$ valuations across the entire Lucas Boolean cube $\{k : k \subseteq _ 2 n\}$: 1. **Stage 1 — Closed 2-State Bit-Slice Binomial Engine (`delta_two_state_div`, `delta_exact_mod2`):** - For any $n, j \in \mathbb{N}$ and shift $c \in \mathbb{Z}$, define the shifted Boolean Möbius derivative on the Lucas cube of $j$: - Using the unified bit-slice binomial expansion (`binomZ_two_mul`, proved by 10-line Pasc

## For Non-Mathematicians

**Name:** The Three-Stage Lucas-Mask Bit-Slice & 2-Adic Bit-Smoothness Engine (`LucasMaskEngine`). **Core Silicon Principle (Finite $\to$ Infinite Bridge):** Treating Lucas's theorem mod $2$ as a silicon bitmask filter $k \subseteq _ 2 n$ (`k &&& n = k`, equivalently `k & ~n = 0`), we construct a **reusable three-stage infinite proof engine** that lifts finite LSB bit-slice tra

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `LucasMaskWalshBinomFractals/Theorems.lean`, definitions in `LucasMaskWalshBinomFractals/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `delta_two_state_div` | The 2-state closed bit-slice divisibility invariant: For every `N`, every submask `j <=_2 N`: - State 0: for all `c` with `2 * c <= N`, `2^(popcount j - c) / Delta (N - 2*c) j c`. - State 1: for all `c >= 1` with `2 * c <= N + 1`, `2^(popcount j - c) / Delta (N - 2*c + 1) j c`. |
| `bitUnit_sq_lift` | **Stage 2 Law 3 (Higher Squaring Lift):** For all `s >= 1`, `BitUnit n s g -> BitUnit n (s + 1) (g^2)`. |
| `bitSmooth_pow_odd` | **Stage 2 Compiler (Odd Exponents):** If `f ∈ BitSmooth n E` with `f 0 = 1`, then for EVERY odd `r`, `f^r ∈ BitSmooth n E`. |
| `walsh_bitSmooth_spike` | **Stage 3 Bridge A (Unique Walsh Spike Theorem for `BitSmooth`):** For ANY `f ∈ BitSmooth n E` and ANY mask `m <=_2 n`: `walsh n m f ≡ (if m = E then 2^(popcount n) else 0) (mod 2^(popcount n + 1))`. |
| `walsh_lucas_binom_odd_pow` | **Main Theorem 1 (Walsh-Lucas Unique Spike Theorem for Odd Powers):** For ALL `n : Nat`, ALL odd `r : Nat`, and ALL masks `m <=_2 n`: `∑_{k <=_2 n} (-1)^popcount(k &&& m) * C(n, k)^r ≡ 2^(popcount n) * [m = E(n)] (mod 2^(popcount n + 1))`. |
| `walsh_lucas_binom_even_pow` | **Main Theorem 3 (Walsh-Lucas Higher-Modulus Congruence for Even Powers):** For ALL `n : Nat`, ALL positive even `r : Nat` (`r ≠ 0`, `r % 2 = 0`), and ALL `m <=_2 n`: `∑_{k <=_2 n} (-1)^popcount(k &&& m) * C(n, k)^r ≡ 2^(popcount n) * [m = 0] (mod 2^(popcount n + v2(r) + 1))`. |
| `walsh_lucas_mixed_product` | **Main Theorem 4 (Mixed-Product XOR-Spike Theorem):** For ALL `n, n1, n2 : Nat` with `n <=_2 n1` and `n <=_2 n2`, ALL odd `r1, r2`, and ALL `m <=_2 n`, the unique Walsh spike mask of `C(n1, k)^r1 * C(n2, k)^r2` on the Lucas cube of `n` is `(E(n1) ^^^ E(n2)) &&& n`. |
| `sharpness_squaring_jump_needs_spike_mask` | Machine-checked infinite theorem `sharpness_squaring_jump_needs_spike_mask` proved in pure Lean 4 `Init`. |

## Prior-Art Context

- - **Classical Prior Art:** - *Lucas (1878)*, *Kummer (1852)*, and *Fine (1947)* characterize $\binom{n}{k} \bmod 2$, $v _ 2\binom{n}{k}$, and the count $2^{\mathrm{pc}(n)}$ of odd binomial coefficients in row $n$ (and more generally binomial coefficients modulo prime powers). - *Granville (1997)*, *Davis–Webb (1990)*, *Huard–Spearman–Williams (1998)*, and *Rowland (2011)* establish $p$-adic generalizations of Lucas's theorem modulo $p^q$, explicit binary/base-$p$ patterns for $\binom{n}{k} \bmod p^2$ and $\bmod p^3$, and regular/automatic-sequence structure for binomial residues across Pascal's triangle (from which our Bonus Theorem 5, $\bino
- Hostile-verified PASS by `referee-4`; pure `leanprover/lean4:v4.34.1` `Init` stack with `enable_nanoda: true` and exact integer Python replay in `scripts/explore_and_verify.py`.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).