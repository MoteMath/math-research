# Recursive Bit-Sliced Schur-Complement Determinant Engine (`bit-sliced-schur-det-engine`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **9 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **86 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): **Mechanism Name:** **Division-Free Bit-Sliced Block-Schur Lifting Compiler** (`det_block_schur_proportional` + `det_block_schur_right_unimodular` + `det_bitSliced_schur_lift`) **Silicon Principle:** For any $2^k \times 2^k$ matrix indexed by $k$-bit words $x, y \in \{0, \dots, 2^k - 1\}$, splitting row and column indices by their most significant bit (MSB, bit $k - 1$) partiti*

## For Mathematicians

**Mechanism Name:** **Division-Free Bit-Sliced Block-Schur Lifting Compiler** (`det_block_schur_proportional` + `det_block_schur_right_unimodular` + `det_bitSliced_schur_lift`) **Silicon Principle:** For any $2^k \times 2^k$ matrix indexed by $k$-bit words $x, y \in \{0, \dots, 2^k - 1\}$, splitting row and column indices by their most significant bit (MSB, bit $k - 1$) partitions $M _ k$ into four $2^{k-1} \times 2^{k-1}$ blocks: Classical Schur complements divide by $\det A$ (requiring a field or invertibility of $A$), which breaks down over arbitrary commutative rings $R$ (including $\mathbb{Z}$, polynomial rings, and zero-divisor quotient rings $\mathbb{Z}/m\mathbb{Z}$), and fails whenever a top-left scalar multiplier $\gamma = 0$ or $\gamma$ is a zero divisor. Our engine eliminates division completely in two layers, built from scratch on top of a genuine classical Leibniz/Levi-Civita determinant `det` (with `det_mul`, `det_blockUpp

## For Non-Mathematicians

**Mechanism Name:** **Division-Free Bit-Sliced Block-Schur Lifting Compiler** (`det_block_schur_proportional` + `det_block_schur_right_unimodular` + `det_bitSliced_schur_lift`) **Silicon Principle:** For any $2^k \times 2^k$ matrix indexed by $k$-bit words $x, y \in \{0, \dots, 2^k - 1\}$, splitting row and column indices by their most significant bit (MSB, bit $k - 1$) partiti

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `BitSlicedSchurDetEngine/Theorems.lean`, definitions in `BitSlicedSchurDetEngine/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `det_mul` | Multiplicativity of the classical Leibniz determinant over ANY commutative ring `R`. |
| `det_block_schur_left_unimodular` | Exact unimodular left Block-Schur complement over ANY commutative ring `R`. |
| `det_block_schur_right_scaled` | Exact division-free scaled right Block-Schur complement over ANY commutative ring `R`. |
| `det_bitSliced_schur_zero_iff` | **AUTOMATIC INVERTIBILITY DICHOTOMY LIFTER** over any `IntDomain R`. |
| `det_msbAnd_closed_form` | Machine-checked infinite theorem `det_msbAnd_closed_form` proved in pure Lean 4 `Init`. |
| `det_subsetDisjMat_closed_form` | Machine-checked infinite theorem `det_subsetDisjMat_closed_form` proved in pure Lean 4 `Init`. |
| `witness_zmod6_zero_divisors` | Witness 2 (Zero-Divisor Ring `ZMod 5` = Z/6Z Non-Vacuity — Invertible Unit Determinant!): In `Z/6Z`, `γ(1) = 2` and `γ(2) = 3` are BOTH zero divisors (`2 * 3 = 0`), yet our universal `CRing` closed-form theorem certifies `det H_2 = 1 (mod 6)` (a unit!)! |
| `counterexample_bool_plus_superset_breaks` | Sharpness Counterexample C (Kernel-Checked!): Adding the superset term `[y ⊆ x]` to `subsetDisjMat` (`a = c = 1`) breaks the `(a^2 - c^2)^(2^(k-1))` law: at `k = 1`, `det = 2 ≠ 0`, while at `k = 2`, `det = 0`! |

## Prior-Art Context

- 1. **Zero overlap with `CHARTER.md` Section 4:** - Distinct from `skew-thue-morse-pfaffian` (skew-symmetric Pfaffians / Walsh-Hadamard), `clmul-lift-determinants` (carryless polynomial multiplication / Hankel / Toeplitz over $\mathbb{F} _ 2[x]$), `zero-carry-spanning-trees` (Laplacian Kirchhoff trees of $x \mathbin{\&} y = 0$), `carry-determinants`, and `carry-blocks-determinants` (binary addition carry matrices). - Here we construct a **general, division-free commutative-ring block-Schur lifting compiler** and apply it to (i) nonlinear global highest-common-bit selection kernels $H _ k$ coupled with arbitrary non-uniform bit-pair weights and
- Hostile-verified PASS by `referee-3`; pure `leanprover/lean4:v4.34.1` `Init` stack with `enable_nanoda: true` and exact integer Python replay in `scripts/explore_and_verify.py`.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).