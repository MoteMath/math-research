# Formal Verification Audit (`carry-presburger-skolem-compiler`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built CarryPresburgerSkolemCompiler.Defs (7.0s)
✔ [3/7] Built CarryPresburgerSkolemCompiler.Theorems (158s)
✔ [4/7] Built CarryPresburgerSkolemCompiler (2.8s)
✔ [6/7] Built Solution (2.1s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.0s)
warning: Challenge.lean:18:8: declaration uses `sorry`
warning: Challenge.lean:25:8: declaration uses `sorry`
warning: Challenge.lean:32:8: declaration uses `sorry`
warning: Challenge.lean:39:8: declaration uses `sorry`
warning: Challenge.lean:45:8: declaration uses `sorry`
warning: Challenge.lean:50:8: declaration uses `sorry`
warning: Challenge.lean:55:8: declaration uses `sorry`
warning: Challenge.lean:59:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the 8 intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `CarryPresburgerSkolemCompiler/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'CarryPresburgerSkolemCompilerChallenge.cert_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarryPresburgerSkolemCompilerChallenge.synthesizeY_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarryPresburgerSkolemCompilerChallenge.cert_sound_univ' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarryPresburgerSkolemCompilerChallenge.carryCount_eq_popcount_defect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarryPresburgerSkolemCompilerChallenge.ternary_zero_carry_r0' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarryPresburgerSkolemCompilerChallenge.ternary_carry1_r2' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarryPresburgerSkolemCompilerChallenge.ternary_carry2_r0' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarryPresburgerSkolemCompilerChallenge.mersenne_collatz_rigidity_15' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every headline theorem depends exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true` (no `sorryAx`, no `Lean.ofReduceBool`).
