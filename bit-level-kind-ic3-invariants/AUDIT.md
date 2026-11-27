# Formal Verification Audit (`bit-level-kind-ic3-invariants`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built BitLevelKindIc3Invariants.Defs (8.4s)
✔ [3/7] Built BitLevelKindIc3Invariants.Theorems (285s)
✔ [4/7] Built BitLevelKindIc3Invariants (1.9s)
✔ [6/7] Built Solution (1.9s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.7s)
warning: Challenge.lean:18:8: declaration uses `sorry`
warning: Challenge.lean:28:8: declaration uses `sorry`
warning: Challenge.lean:35:8: declaration uses `sorry`
warning: Challenge.lean:42:8: declaration uses `sorry`
warning: Challenge.lean:49:8: declaration uses `sorry`
warning: Challenge.lean:55:8: declaration uses `sorry`
warning: Challenge.lean:61:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Exit codes: `lake build` = 0, `lake build Challenge` = 0. Zero errors, zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in the library modules or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'BitLevelKindIc3InvariantsChallenge.checkOblig_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'BitLevelKindIc3InvariantsChallenge.checkKIndIC3_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'BitLevelKindIc3InvariantsChallenge.thm1_wrapSafeGray_safety' depends on axioms: [propext, Classical.choice, Quot.sound]
'BitLevelKindIc3InvariantsChallenge.thm2_carrySave_safety' depends on axioms: [propext, Classical.choice, Quot.sound]
'BitLevelKindIc3InvariantsChallenge.thm3_carryDefectPipeline_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitLevelKindIc3InvariantsChallenge.thm4_hybridSparseAdder_msb' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitLevelKindIc3InvariantsChallenge.thm5_avgFilter_oneULP' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Exit code: 0. Every headline theorem depends only on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true`.
