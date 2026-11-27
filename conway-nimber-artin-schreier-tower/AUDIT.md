# Formal Verification Audit (`conway-nimber-artin-schreier-tower`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built ConwayNimberArtinSchreierTower.Defs (8.6s)
✔ [3/7] Built ConwayNimberArtinSchreierTower.Theorems (17s)
✔ [4/7] Built ConwayNimberArtinSchreierTower (1.5s)
✔ [6/7] Built Solution (1.5s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.6s)
warning: Challenge.lean:8:8: declaration uses `sorry`
warning: Challenge.lean:12:8: declaration uses `sorry`
warning: Challenge.lean:16:8: declaration uses `sorry`
warning: Challenge.lean:21:8: declaration uses `sorry`
warning: Challenge.lean:26:8: declaration uses `sorry`
warning: Challenge.lean:32:8: declaration uses `sorry`
warning: Challenge.lean:42:8: declaration uses `sorry`
warning: Challenge.lean:47:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `ConwayNimberArtinSchreierTower/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'ConwayNimberArtinSchreierTowerChallenge.mul_inv' depends on axioms: [propext, Quot.sound]
'ConwayNimberArtinSchreierTowerChallenge.wp_bitLen_contraction' depends on axioms: [propext, Quot.sound]
'ConwayNimberArtinSchreierTowerChallenge.cosetHarmonic_eq_inv_wpIter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ConwayNimberArtinSchreierTowerChallenge.powerSum_binary_collapse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ConwayNimberArtinSchreierTowerChallenge.finite_table_evaluates_all_m' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ConwayNimberArtinSchreierTowerChallenge.dyadicProd_fourth_shell_period4' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ConwayNimberArtinSchreierTowerChallenge.sharpness_period_fails_at_k1_r2' depends on axioms: [propext]
'ConwayNimberArtinSchreierTowerChallenge.sharpness_popcount_boundary_nonzero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
