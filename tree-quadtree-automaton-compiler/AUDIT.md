# Formal Verification Audit (`tree-quadtree-automaton-compiler`)

**Toolchain:** `leanprover/lean4:v4.35.0` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built TreeQuadtreeAutomatonCompiler.Defs (79s)
✔ [3/7] Built TreeQuadtreeAutomatonCompiler.Theorems (69s)
✔ [4/7] Built TreeQuadtreeAutomatonCompiler (1.1s)
✔ [6/7] Built Solution (1.1s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.2s)
warning: Challenge.lean:8:8: declaration uses `sorry`
warning: Challenge.lean:16:8: declaration uses `sorry`
warning: Challenge.lean:22:8: declaration uses `sorry`
warning: Challenge.lean:27:8: declaration uses `sorry`
warning: Challenge.lean:32:8: declaration uses `sorry`
warning: Challenge.lean:43:8: declaration uses `sorry`
warning: Challenge.lean:47:8: declaration uses `sorry`
warning: Challenge.lean:52:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `TreeQuadtreeAutomatonCompiler/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'TreeQuadtreeAutomatonCompilerChallenge.timedBTA_sound' depends on axioms: [propext, Quot.sound]
'TreeQuadtreeAutomatonCompilerChallenge.factoredQTA_sound' depends on axioms: [propext, Quot.sound]
'TreeQuadtreeAutomatonCompilerChallenge.percEval_eq_QNet' depends on axioms: [propext, Classical.choice, Quot.sound]
'TreeQuadtreeAutomatonCompilerChallenge.percolation_duality_D33' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TreeQuadtreeAutomatonCompilerChallenge.d33_exact_completeness_height2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TreeQuadtreeAutomatonCompilerChallenge.hilbert_D4_mod15_annihilation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TreeQuadtreeAutomatonCompilerChallenge.nonvacuity_barrier_witnesses' depends on axioms: [propext, Quot.sound]
'TreeQuadtreeAutomatonCompilerChallenge.sharpness_and_nonvacuity_family3' depends on axioms: [propext]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
