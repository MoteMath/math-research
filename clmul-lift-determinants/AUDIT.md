# Formal Verification Audit (`clmul-lift-determinants`)

**Toolchain:** `leanprover/lean4:v4.34.1` with Mathlib `v4.34.1`  
**Audit date:** 2026-11-25

## Build & Challenge Checks

```text
$ lake build
✔ [3095/3100] Built ClmulLiftDeterminants.RevHadamard (24s)
✔ [3096/3100] Built ClmulLiftDeterminants.Theorems (22s)
✔ [3097/3100] Built ClmulLiftDeterminants (16s)
✔ [3099/3100] Built Solution (16s)
Build completed successfully (3100 jobs).

$ lake build Challenge
⚠ [1550/1551] Built Challenge (13s)
warning: Challenge.lean:23:8: declaration uses `sorry`
warning: Challenge.lean:31:8: declaration uses `sorry`
warning: Challenge.lean:39:8: declaration uses `sorry`
warning: Challenge.lean:47:8: declaration uses `sorry`
warning: Challenge.lean:55:8: declaration uses `sorry`
Build completed successfully (1551 jobs).
```

Zero errors, zero warnings outside the five intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `ClmulLiftDeterminants/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'ClmulLiftChallenge.det_oddClmulMatrix_pow_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClmulLiftChallenge.det_oddClmulMatrix_pow_two_add_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClmulLiftChallenge.det_oddClmulMatrix_pow_two_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClmulLiftChallenge.det_oddClmulMatrix_eq_zero_of_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClmulLiftChallenge.det_oddClmulMatrix_ne_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All five headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Quot.sound`, and `Classical.choice`), matching `comparator.json` with `enable_nanoda: true`.
