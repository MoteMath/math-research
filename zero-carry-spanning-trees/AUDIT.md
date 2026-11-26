# Formal Verification Audit (`zero-carry-spanning-trees`)

**Toolchain:** `leanprover/lean4:v4.34.1`  
**Mathlib:** `v4.34.1` (`d13f23b723b8a846827a245b89c10fc7d3f11612`)  
**Audit date:** 2026-11-25

## Build & Challenge Checks

```text
$ lake build
✔ [3095/3099] Built ZeroCarrySpanningTrees.SpanningTrees (22s)
✔ [3096/3099] Built ZeroCarrySpanningTrees (16s)
✔ [3098/3099] Built Solution (16s)
Build completed successfully (3099 jobs).

$ lake build Challenge
⚠ [1550/1551] Built Challenge (12s)
warning: Challenge.lean:21:8: declaration uses `sorry`
warning: Challenge.lean:31:8: declaration uses `sorry`
warning: Challenge.lean:41:8: declaration uses `sorry`
warning: Challenge.lean:54:8: declaration uses `sorry`
warning: Challenge.lean:61:8: declaration uses `sorry`
Build completed successfully (1551 jobs).
```

Zero errors, zero warnings outside the five intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `ZeroCarrySpanningTrees/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'ZeroCarrySpanningTreesChallenge.det_zeroCarryWalk_charpoly' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroCarrySpanningTreesChallenge.det_zeroCarryCofactor_mixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroCarrySpanningTreesChallenge.det_zeroCarryCofactor_base' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroCarrySpanningTreesChallenge.det_binaryZeroCarryCofactor' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroCarrySpanningTreesChallenge.det_singleRadixZeroCarryCofactor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All five headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true`.
