# Strided-Bitset Decomposition & 2-Adic Odd-Parity Ultrametric Dominance Engine (`adic-13`) (`strided-bitset-2adic-ultrametric`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **8 / 10** | **8 / 10** | **8 / 10** | **10 / 10** | **82 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): **Mechanism:** **Bitmask-Slice Carry-Convolution Bridge + 2-Adic Odd-Parity Ultrametric Dominance Engine** (with a kernel-`decide`-executable **Finite-Certificate Unit-Carry Compiler**). **Pure-Silicon Principle (Finite $\to$ Infinite Bridge):** For any period (stride) $m \ge 1$ and periodic bitmask $M \in \mathbb{N}$, define the $m$-periodic binary-support set generalizing the*

## For Mathematicians

**Mechanism:** **Bitmask-Slice Carry-Convolution Bridge + 2-Adic Odd-Parity Ultrametric Dominance Engine** (with a kernel-`decide`-executable **Finite-Certificate Unit-Carry Compiler**). **Pure-Silicon Principle (Finite $\to$ Infinite Bridge):** For any period (stride) $m \ge 1$ and periodic bitmask $M \in \mathbb{N}$, define the $m$-periodic binary-support set generalizing the $m$-strided Moser–de Bruijn set $S _ m := \mathcal{B}(m, 1)$ (bits supported only at multiples of $m$). Given any finite tuple of masks $(M _ 1, \dots, M _ k)$, let $r _ {M _ 1, \dots, M _ k}(n)$ denote the exact combinatorial tuple-representation count and write $r _ {k S _ m}(n)$ when $M _ 1 = \dots = M _ k = 1$. Our reusable Lean 4 proof engine operates in three composable silicon-native layers: 1. **Bitmask-Slice Carry-Convolution Bridge (`maskRepCount_slice`, `stridedRepCount_slice`):** Decomposes genuine bit-support predicates into base-$2^m$ digit slices a

## For Non-Mathematicians

**Mechanism:** **Bitmask-Slice Carry-Convolution Bridge + 2-Adic Odd-Parity Ultrametric Dominance Engine** (with a kernel-`decide`-executable **Finite-Certificate Unit-Carry Compiler**). **Pure-Silicon Principle (Finite $\to$ Infinite Bridge):** For any period (stride) $m \ge 1$ and periodic bitmask $M \in \mathbb{N}$, define the $m$-periodic binary-support set generalizing the

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `StridedBitset2adicUltrametric/Theorems.lean`, definitions in `StridedBitset2adicUltrametric/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `maskRepCount_slice` | **Master Bit-Slice Carry-Convolution Bridge:** Lifts the combinatorial tuple count `maskRepCount m masks n` directly from the binary-support predicate `InMask` to the exact base-`2^m` carry-convolution recurrence! |
| `ultrametric_odd_parity_lift` | **General Odd-Parity Ultrametric Dominance Engine (`ultrametric_odd_parity_lift`):** For ANY base `B ≥ 2`, ANY carry-convolution recurrence `f (B * q + r) = ∑_{c ≤ q} w c r * f (q - c)` with `f 0 = 1`, and ANY candidate valuation functional `V : Nat → Nat` with `V 0 = 0`: if at every `n = B * q + r > 0`, every active term `w c r > 0` satisfies `v2 (w c r) + V (q - c) ≥ V (B * q + r)` AND an **ODD** number of active terms achieve equality, then `∀ n : Nat, f n > 0 ∧ v2 (f n) = V n`. |
| `nonbinomial_3S2_add_N_v2` | **Non-Binomial Application 1 (Proved `∀ n : Nat` via `decide`):** The mixed periodic bitmask sumset `3 * S_2 + N` (`masks = [1, 1, 1, 3]` at stride `m = 2`, non-binomial digit weights `w0 = [1, 4, 7, 8]`, `w1 = [7, 4, 1, 0]`). |
| `even_window_strided_v2` | **THEOREM 1 (2-Parameter Infinite Family — Even-Window Strided Valuation Law):** For ALL strides `m ≥ 1`, ALL even multiplicities `k = 2^m + 2*t ∈ [2^m, 2^(m+1) - 2]`, and ALL `n : Nat`, the combinatorial sumset count `r_{k S_m}(n)` is strictly positive and has exact 2-adic valuation `evenWindowVal m t n` (with strict even-local-minimum alternation). |
| `upper_endpoint_v2_collapse` | **COROLLARY 1A (Universal `(2^(m+1) - 2)`-Collapse Theorem):** For EVERY stride `m ≥ 1` and EVERY `n : Nat`, the `(2^(m+1) - 2)`-fold `m`-strided Moser-de Bruijn sumset representation count has the EXACT 2-adic valuation of `n + 1`! `∀ m ≥ 1, ∀ n : Nat, v2 (stridedRepCount m (2^(m+1) - 2) n) = v2 (n + 1)`. |
| `pow2_strided_r_invariance` | **COROLLARY 2A (Exact `r`-Invariance / Stability Law):** For ALL strides `m ≥ 1`, ALL powers `r1, r2 ≥ m`, and ALL `a : Nat`, `v2 (r_{2^r1 S_m}(2^r1 * a)) = v2 (r_{2^r2 S_m}(2^r2 * a))`. |
| `witness_three_way_tie_survives` | Non-vacuity witness 3: Theorem 2 genuinely hits 3-way ties (tie multiplicity 3, odd -> no cancellation)! At `m = 2, r = 3 (K = 8), n = 12 (q = 3, rem = 0)`, the three recurrence terms are `C(8,0)*r(3) = 56`, `C(8,4)*r(2) = 70*28 = 1960`, `C(8,8)*r(1) = 8`, ALL with `v2 = 3`, summing to `2024` which still has `v2 = 3`! |
| `sharpness_above_window_cancellation` | **Sharpness Counterexample 3 (Even `k > 2^(m+1) - 2`, non-power-of-two):** At `m = 2, k = 10` (even, `10 > 6`, not a power of 2), at `n = 4`: terms `C(10,0)*r(1) = 10` and `C(10,4)*r(0) = 210` both have `v2 = 1`, causing a 2-way tie with 2-adic cancellation (`stridedRepCount 2 10 4 = 220`, `v2 220 = 2 > 1`)! |

## Prior-Art Context

- - **Classical Prior Art:** - Moser (1962) and de Bruijn (1964) studied unique additive decompositions into complementary bit-position sets (such as $S _ 2 + 2 S _ 2 = \mathbb{N}$), which are carry-free. - Kummer's theorem (1852) and Legendre's formula characterize $\nu _ 2\binom{n}{k}$, which covers the $m = 1$ special case $r _ {k S _ 1}(n) = \binom{n + k - 1}{k - 1}$. - Reznick (1990, *"Some binary partition functions"*) studied $d$-ary / binary partition and hyperbinary representation functions (related to Stern's diatomic sequence and base-$2^m$ digit-restricted partition counts). - Allouche and Shallit (2003, *Automatic Sequences*) provi
- Hostile-verified PASS by `referee-4`; pure `leanprover/lean4:v4.34.1` `Init` stack with `enable_nanoda: true` and exact integer Python replay in `scripts/explore_and_verify.py`.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).