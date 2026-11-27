# Formal Verification Audit (`weighted-carry-jet-rationality`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.3s)
warning: Challenge.lean:17:8: declaration uses `sorry`
warning: Challenge.lean:24:8: declaration uses `sorry`
warning: Challenge.lean:31:8: declaration uses `sorry`
warning: Challenge.lean:40:8: declaration uses `sorry`
warning: Challenge.lean:49:8: declaration uses `sorry`
warning: Challenge.lean:58:8: declaration uses `sorry`
warning: Challenge.lean:66:8: declaration uses `sorry`
warning: Challenge.lean:76:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `WeightedCarryJetRationality/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'WeightedCarryJetRationalityChallenge.jetMat_pow_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'WeightedCarryJetRationalityChallenge.fps_rational_of_recurrence' depends on axioms: [propext, Quot.sound]
'WeightedCarryJetRationalityChallenge.binary_carry_borrow_gf' depends on axioms: [propext, Classical.choice, Quot.sound]
'WeightedCarryJetRationalityChallenge.binary_parity_corr_gf' depends on axioms: [propext, Classical.choice, Quot.sound]
'WeightedCarryJetRationalityChallenge.binary_triangular_square_covariance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'WeightedCarryJetRationalityChallenge.odd_radix_zero_covariance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'WeightedCarryJetRationalityChallenge.even_radix_perfect_square_covariance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'WeightedCarryJetRationalityChallenge.radix_parity_partition_formula' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
