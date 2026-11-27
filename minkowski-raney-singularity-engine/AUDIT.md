# Formal Verification Audit (`minkowski-raney-singularity-engine`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built MinkowskiRaneySingularityEngine.Defs (24s)
✔ [3/7] Built MinkowskiRaneySingularityEngine.Theorems (2.8s)
✔ [4/7] Built MinkowskiRaneySingularityEngine (1.4s)
✔ [6/7] Built Solution (1.5s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.6s)
warning: Challenge.lean:9:8: declaration uses `sorry`
warning: Challenge.lean:14:8: declaration uses `sorry`
warning: Challenge.lean:21:8: declaration uses `sorry`
warning: Challenge.lean:27:8: declaration uses `sorry`
warning: Challenge.lean:33:8: declaration uses `sorry`
warning: Challenge.lean:39:8: declaration uses `sorry`
warning: Challenge.lean:44:8: declaration uses `sorry`
warning: Challenge.lean:52:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `MinkowskiRaneySingularityEngine/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'MinkowskiRaneySingularityEngineChallenge.minkowskiQ_sbMat_mediant' depends on axioms: [propext, Quot.sound]
'MinkowskiRaneySingularityEngineChallenge.hellinger_tv_singularity' depends on axioms: [propext, Quot.sound]
'MinkowskiRaneySingularityEngineChallenge.singularity_D2' depends on axioms: [propext, Quot.sound]
'MinkowskiRaneySingularityEngineChallenge.bit_expansion_D2' depends on axioms: [propext, Quot.sound]
'MinkowskiRaneySingularityEngineChallenge.integral_convergence_D2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MinkowskiRaneySingularityEngineChallenge.exact_closed_form_D2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MinkowskiRaneySingularityEngineChallenge.row_col_duality_D5' depends on axioms: [propext, Quot.sound]
'MinkowskiRaneySingularityEngineChallenge.sharpness_hellinger_const_counterexample' does not depend on any axioms
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
