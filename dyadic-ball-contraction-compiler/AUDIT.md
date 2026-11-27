# Formal Verification Audit (`dyadic-ball-contraction-compiler`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built DyadicBallContractionCompiler.Defs (2.0s)
✔ [3/7] Built DyadicBallContractionCompiler.Theorems (20s)
✔ [4/7] Built DyadicBallContractionCompiler (1.6s)
✔ [6/7] Built Solution (1.8s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.1s)
warning: Challenge.lean:7:8: declaration uses `sorry`
warning: Challenge.lean:14:8: declaration uses `sorry`
warning: Challenge.lean:24:8: declaration uses `sorry`
warning: Challenge.lean:31:8: declaration uses `sorry`
warning: Challenge.lean:40:8: declaration uses `sorry`
warning: Challenge.lean:43:8: declaration uses `sorry`
warning: Challenge.lean:46:8: declaration uses `sorry`
warning: Challenge.lean:50:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `DyadicBallContractionCompiler/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'DyadicBallContractionCompilerChallenge.checkParamTree_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'DyadicBallContractionCompilerChallenge.contraction_fixed_point_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DyadicBallContractionCompilerChallenge.bring_quintic_residual_decay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DyadicBallContractionCompilerChallenge.bring_direct_oscillatory_contraction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DyadicBallContractionCompilerChallenge.certHalley_valid' does not depend on any axioms
'DyadicBallContractionCompilerChallenge.certBringAlt_valid' does not depend on any axioms
'DyadicBallContractionCompilerChallenge.mutation_reject_halley_no_subdivision' does not depend on any axioms
'DyadicBallContractionCompilerChallenge.mutation_reject_bring_alt_expanding_region' does not depend on any axioms
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
