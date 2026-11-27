# Kronecker-Woodbury Schur-Tower Riccati Engine (`specmat-11`) (`kronecker-woodbury-schur-riccati`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **9 / 10** | **9 / 10** | **10 / 10** | **91 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): **Mechanism Name:** **Kronecker-Woodbury Schur-Tower Riccati Engine** (`GeneralSchurTower` + `affine_tower_lift` + `affine_tower_singular_of_core_kernel`). **Core Silicon Principle:** Every bit-serial $b \times b$ affine bit-pair transducer over bit-vectors of length $k$ updates an accumulator across digit positions $r = 0, \dots, k-1$ by producing a $b^k \times b^k$ matrix $M*

## For Mathematicians

**Mechanism Name:** **Kronecker-Woodbury Schur-Tower Riccati Engine** (`GeneralSchurTower` + `affine_tower_lift` + `affine_tower_singular_of_core_kernel`). **Core Silicon Principle:** Every bit-serial $b \times b$ affine bit-pair transducer over bit-vectors of length $k$ updates an accumulator across digit positions $r = 0, \dots, k-1$ by producing a $b^k \times b^k$ matrix $M _ k$ whose entries mix multiplicative Kronecker structure ($C$) with additive carry/borrow/equality perturbations ($B$) injected at every bit scale. Because adding $B _ {i _ r, j _ r}$ at bit level $r$ is independent of the lower $r$ bits, the transducer compiles *identically* into a **Kronecker-plus-low-rank tower**: where $J _ k = \mathbf{1} _ k \mathbf{1} _ k^T$ is the $b^k \times b^k$ all-ones rank-$1$ matrix. Our standalone Lean 4 engine proves that **two layers of exact algebraic lifting** collapse arbitrary $b^k \times b^k$ inversion, determinant, and singu

## For Non-Mathematicians

**Mechanism Name:** **Kronecker-Woodbury Schur-Tower Riccati Engine** (`GeneralSchurTower` + `affine_tower_lift` + `affine_tower_singular_of_core_kernel`). **Core Silicon Principle:** Every bit-serial $b \times b$ affine bit-pair transducer over bit-vectors of length $k$ updates an accumulator across digit positions $r = 0, \dots, k-1$ by producing a $b^k \times b^k$ matrix $M

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `KroneckerWoodburySchurRiccati/Theorems.lean`, definitions in `KroneckerWoodburySchurRiccati/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `alt_multilin_eq_det_mul` | Alternating multilinear uniqueness over any commutative ring `R`. |
| `det_add_mul_of_inv` | Matrix Determinant Lemma over any commutative ring `R` given an inverse `Ainv`. |
| `schur_tower_step_general` | General rank-`r` probe-bank Kronecker-plus-low-rank Schur-tower step over arbitrary `CRing R`. |
| `bitTransducerMat_eq_affineTower` | Bitwise bridge: entrywise equality between `bitTransducerMat` and `affineTower` for all `k`. |
| `theorem1_carryGenWalsh_det` | Theorem 1 (Fixed-Point Regime): exact determinant of carry-generate Walsh-Hadamard `carryGenWalshMat lam k` for all `lam` and `k`. |
| `theorem3_bitEqWalsh_inv_and_zerosum` | Theorem 3 (Zero Absorption): exact Woodbury inverse and zero-sum inverse capacitance law for `bitEqWalshMat k` for all `k`. |
| `theorem4_programmable_depth_N_singularity` | Theorem 4 (Programmable Depth-N Singularity): `prefixWalshMat N (-1) k` is invertible for all `k < N` and identically singular at exact depth `k = N`. |
| `nonvacuity_witness_all_theorems` | Nine-conjunct concrete non-vacuity and sharpness witness across all four Riccati regimes. |

## Prior-Art Context

- Formalizes a pure-Init Lean 4 infinite proof engine with zero Mathlib dependencies and independent `nanoda` kernel verification.
- Hostile-verified PASS by `referee-3`; pure `leanprover/lean4:v4.34.1` `Init` stack with `enable_nanoda: true` and exact integer Python replay in `scripts/explore_and_verify.py`.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).