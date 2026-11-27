# Formal Verification Audit (`automatic-word-avoidance-compiler`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built AutomaticWordAvoidanceCompiler.Defs (3.8s)
✔ [3/7] Built AutomaticWordAvoidanceCompiler.Theorems (182s)
✔ [4/7] Built AutomaticWordAvoidanceCompiler (1.0s)
✔ [6/7] Built Solution (2.2s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.0s)
warning: Challenge.lean:18:8: declaration uses `sorry`
warning: Challenge.lean:25:8: declaration uses `sorry`
warning: Challenge.lean:32:8: declaration uses `sorry`
warning: Challenge.lean:42:8: declaration uses `sorry`
warning: Challenge.lean:47:8: declaration uses `sorry`
warning: Challenge.lean:52:8: declaration uses `sorry`
warning: Challenge.lean:57:8: declaration uses `sorry`
warning: Challenge.lean:62:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the 8 intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `AutomaticWordAvoidanceCompiler/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'AutomaticWordAvoidanceCompilerChallenge.windowCert_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'AutomaticWordAvoidanceCompilerChallenge.powerAvoidCert_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AutomaticWordAvoidanceCompilerChallenge.overlapAvoidCert_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AutomaticWordAvoidanceCompilerChallenge.carryXor3_four_power_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AutomaticWordAvoidanceCompilerChallenge.carryAnd3_five_power_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AutomaticWordAvoidanceCompilerChallenge.carryAnd5_four_power_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AutomaticWordAvoidanceCompilerChallenge.carryXor5_six_power_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AutomaticWordAvoidanceCompilerChallenge.grayMod4_overlap_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every headline theorem depends exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true` (no `sorryAx`, no `Lean.ofReduceBool`).
