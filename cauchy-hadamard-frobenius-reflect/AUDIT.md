# Formal Verification Audit (`cauchy-hadamard-frobenius-reflect`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built CauchyHadamardFrobeniusReflect.Defs (12s)
✔ [3/7] Built CauchyHadamardFrobeniusReflect.Theorems (55s)
✔ [4/7] Built CauchyHadamardFrobeniusReflect (2.1s)
✔ [6/7] Built Solution (2.2s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.2s)
warning: Challenge.lean:18:8: declaration uses `sorry`
warning: Challenge.lean:23:8: declaration uses `sorry`
warning: Challenge.lean:31:8: declaration uses `sorry`
warning: Challenge.lean:38:8: declaration uses `sorry`
warning: Challenge.lean:45:8: declaration uses `sorry`
warning: Challenge.lean:52:8: declaration uses `sorry`
warning: Challenge.lean:59:8: declaration uses `sorry`
warning: Challenge.lean:67:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Exit codes: `lake build` = 0, `lake build Challenge` = 0. Zero errors, zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in the library modules or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'CauchyHadamardFrobeniusReflectChallenge.reflect_all_bitvec' depends on axioms: [propext, Classical.choice, Quot.sound]
'CauchyHadamardFrobeniusReflectChallenge.reflect_all_scales_and_widths' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CauchyHadamardFrobeniusReflectChallenge.binary_ito2_all_scales_widths' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CauchyHadamardFrobeniusReflectChallenge.binary_ito_general_n' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CauchyHadamardFrobeniusReflectChallenge.self_scale_ladder_all_scales_widths' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CauchyHadamardFrobeniusReflectChallenge.two_scale_ladder_all_scales_widths' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CauchyHadamardFrobeniusReflectChallenge.residue_conv_split_all_r_w' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CauchyHadamardFrobeniusReflectChallenge.frob_hadamard_orthogonal_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Exit code: 0. Every headline theorem depends only on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true`.
