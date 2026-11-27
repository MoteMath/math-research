# Formal Verification Audit (`hensel-silicon-basin-classifier`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.0s)
warning: Challenge.lean:17:8: declaration uses `sorry`
warning: Challenge.lean:27:8: declaration uses `sorry`
warning: Challenge.lean:35:8: declaration uses `sorry`
warning: Challenge.lean:46:8: declaration uses `sorry`
warning: Challenge.lean:58:8: declaration uses `sorry`
warning: Challenge.lean:67:8: declaration uses `sorry`
warning: Challenge.lean:74:8: declaration uses `sorry`
warning: Challenge.lean:80:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `HenselSiliconBasinClassifier/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'HenselSiliconBasinClassifierChallenge.bPoly_absDeriv_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'HenselSiliconBasinClassifierChallenge.tfunc_fixedPoint_depth_le_width' depends on axioms: [propext, Quot.sound]
'HenselSiliconBasinClassifierChallenge.henselLift_periodic' depends on axioms: [propext, Quot.sound]
'HenselSiliconBasinClassifierChallenge.henselLift_basin_convergence' depends on axioms: [propext, Quot.sound]
'HenselSiliconBasinClassifierChallenge.fixedPointCount_lift' depends on axioms: [propext, Classical.choice, Quot.sound]
'HenselSiliconBasinClassifierChallenge.mapAsym_basin_4_nonPowerOfTwo' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'HenselSiliconBasinClassifierChallenge.mapSeven_fixedPointCount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'HenselSiliconBasinClassifierChallenge.mapHalfCycle_depth_exact_sharp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
