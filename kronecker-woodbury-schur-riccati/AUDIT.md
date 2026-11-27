# Formal Verification Audit (`kronecker-woodbury-schur-riccati`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built KroneckerWoodburySchurRiccati.Defs (9.2s)
✔ [3/7] Built KroneckerWoodburySchurRiccati.Theorems (5.1s)
✔ [4/7] Built KroneckerWoodburySchurRiccati (1.4s)
✔ [6/7] Built Solution (1.4s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.4s)
warning: Challenge.lean:8:8: declaration uses `sorry`
warning: Challenge.lean:14:8: declaration uses `sorry`
warning: Challenge.lean:21:8: declaration uses `sorry`
warning: Challenge.lean:50:8: declaration uses `sorry`
warning: Challenge.lean:55:8: declaration uses `sorry`
warning: Challenge.lean:64:8: declaration uses `sorry`
warning: Challenge.lean:78:8: declaration uses `sorry`
warning: Challenge.lean:84:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `KroneckerWoodburySchurRiccati/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'KroneckerWoodburySchurRiccatiChallenge.alt_multilin_eq_det_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KroneckerWoodburySchurRiccatiChallenge.det_add_mul_of_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KroneckerWoodburySchurRiccatiChallenge.schur_tower_step_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KroneckerWoodburySchurRiccatiChallenge.bitTransducerMat_eq_affineTower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KroneckerWoodburySchurRiccatiChallenge.theorem1_carryGenWalsh_det' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KroneckerWoodburySchurRiccatiChallenge.theorem3_bitEqWalsh_inv_and_zerosum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KroneckerWoodburySchurRiccatiChallenge.theorem4_programmable_depth_N_singularity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KroneckerWoodburySchurRiccatiChallenge.nonvacuity_witness_all_theorems' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
