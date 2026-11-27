# Recursive Bit-Sliced Schur-Complement Determinant Engine (`bit-sliced-schur-det-engine`)

**Scope of the formal statement.** the commutative-ring class `CRing`, the Leibniz `det` and the residue ring `ZMod m := Fin (m+1)` are the package's own definitions in `Defs.lean`, not Mathlib's; in particular `ZMod 5` is `Fin 6`, i.e. Z/6Z.

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
| `det_msbAnd_closed_form` | Over any `CRing R`, for all `k` and `f : Nat -> R`: `det (msbAndMat k f)` is `f 0` for `k = 0`, `f 0 * (f 1 - f 0)` for `k = 1`, and `-(f 0 * prod_{j<k} (f (j+1) - f 0)^(2^(k-1-j)))` for `k >= 2`. |
| `det_subsetDisjMat_closed_form` | Over any `CRing R`, for all `k` and `a, c : R`: `det (subsetDisjMat (k+1) a c) = (a^2 - c^2)^(2^k)`. |
| `witness_zmod6_zero_divisors` | Machine-checked finite instance in the package's own residue ring `ZMod 5 := Fin 6` (that is, Z/6Z, not a field of 5 elements): `2 * 3 = 0`, and a specific 2x2 `hcbMat` determinant evaluates to `1`. It is a computation, not an application of the universal theorems. |
| `counterexample_bool_plus_superset_breaks` | Sharpness Counterexample C (Kernel-Checked!): Adding the superset term `[y ⊆ x]` to `subsetDisjMat` (`a = c = 1`) breaks the `(a^2 - c^2)^(2^(k-1))` law: at `k = 1`, `det = 2 ≠ 0`, while at `k = 2`, `det = 0`! |

## Prior-Art Context

- 1. **Zero overlap with `CHARTER.md` Section 4:** - Distinct from `skew-thue-morse-pfaffian` (skew-symmetric Pfaffians / Walsh-Hadamard), `clmul-lift-determinants` (carryless polynomial multiplication / Hankel / Toeplitz over $\mathbb{F} _ 2[x]$), `zero-carry-spanning-trees` (Laplacian Kirchhoff trees of $x \mathbin{\&} y = 0$), `carry-determinants`, and `carry-blocks-determinants` (binary addition carry matrices). - Here we construct a **general, division-free commutative-ring block-Schur lifting compiler** and apply it to (i) nonlinear global highest-common-bit selection kernels $H _ k$ coupled with arbitrary non-uniform bit-pair weights and
- Built against `leanprover/lean4:v4.34.1` (pure `Init` stack; `enable_nanoda: true` in `comparator.json`); `scripts/explore_and_verify.py` re-evaluates small instances in exact integer arithmetic (it proves nothing by itself).

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).