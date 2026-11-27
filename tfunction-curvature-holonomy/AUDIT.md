# Formal Verification Audit (`tfunction-curvature-holonomy`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built TfunctionCurvatureHolonomy.Defs (7.7s)
✔ [3/7] Built TfunctionCurvatureHolonomy.Theorems (88s)
✔ [4/7] Built TfunctionCurvatureHolonomy (3.5s)
✔ [6/7] Built Solution (2.3s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.1s)
warning: Challenge.lean:18:8: declaration uses `sorry`
warning: Challenge.lean:24:8: declaration uses `sorry`
warning: Challenge.lean:30:8: declaration uses `sorry`
warning: Challenge.lean:39:8: declaration uses `sorry`
warning: Challenge.lean:45:8: declaration uses `sorry`
warning: Challenge.lean:54:8: declaration uses `sorry`
warning: Challenge.lean:59:8: declaration uses `sorry`
warning: Challenge.lean:64:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Exit codes: `lake build` = 0, `lake build Challenge` = 0. Zero errors, zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in the library modules or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'TfunctionCurvatureHolonomyChallenge.singleCycle_succ_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TfunctionCurvatureHolonomyChallenge.holonomy_succ_iff_curvatureSum_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TfunctionCurvatureHolonomyChallenge.lift_singleCycle_from_w4' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TfunctionCurvatureHolonomyChallenge.singleCycle_xor_carryMask_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TfunctionCurvatureHolonomyChallenge.hybridH_singleCycle_iff_bits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TfunctionCurvatureHolonomyChallenge.runT_singleCycle_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TfunctionCurvatureHolonomyChallenge.runT_sharp_threshold' depends on axioms: [propext, Classical.choice, Quot.sound]
'TfunctionCurvatureHolonomyChallenge.no_universal_finite_threshold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Exit code: 0. Every headline theorem depends only on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true`.
