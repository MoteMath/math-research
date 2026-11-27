# Formal Verification Audit (`bitwise-smith-normal-form-lifter`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Replayed Challenge
warning: Challenge.lean:17:8: declaration uses `sorry`
warning: Challenge.lean:24:8: declaration uses `sorry`
warning: Challenge.lean:31:8: declaration uses `sorry`
warning: Challenge.lean:37:8: declaration uses `sorry`
warning: Challenge.lean:43:8: declaration uses `sorry`
warning: Challenge.lean:50:8: declaration uses `sorry`
warning: Challenge.lean:55:8: declaration uses `sorry`
warning: Challenge.lean:62:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `BitwiseSmithNormalFormLifter/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'BitwiseSmithNormalFormLifterChallenge.hasSNF_torsion_obstruction' depends on axioms: [propext, Quot.sound]
'BitwiseSmithNormalFormLifterChallenge.carriesK_kummer' depends on axioms: [propext, Quot.sound]
'BitwiseSmithNormalFormLifterChallenge.snf_affine_carry_parity' depends on axioms: [propext, Quot.sound]
'BitwiseSmithNormalFormLifterChallenge.snf_carry_sign_flat' depends on axioms: [propext, Quot.sound]
'BitwiseSmithNormalFormLifterChallenge.snf_carry_parity_one_dichotomy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitwiseSmithNormalFormLifterChallenge.snf_DMat' depends on axioms: [propext, Classical.choice, Quot.sound]
'BitwiseSmithNormalFormLifterChallenge.snf_bitwise_and' depends on axioms: [propext, Quot.sound]
'BitwiseSmithNormalFormLifterChallenge.snf_two_pow_popcount_and_unimod' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
