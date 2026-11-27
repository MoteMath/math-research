# Formal Verification Audit (`binary-gray-superposition-transfer`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built BinaryGraySuperpositionTransfer.Defs (9.4s)
✔ [3/7] Built BinaryGraySuperpositionTransfer.Theorems (57s)
✔ [4/7] Built BinaryGraySuperpositionTransfer (1.5s)
✔ [6/7] Built Solution (1.7s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.7s)
warning: Challenge.lean:8:8: declaration uses `sorry`
warning: Challenge.lean:12:8: declaration uses `sorry`
warning: Challenge.lean:17:8: declaration uses `sorry`
warning: Challenge.lean:21:8: declaration uses `sorry`
warning: Challenge.lean:25:8: declaration uses `sorry`
warning: Challenge.lean:30:8: declaration uses `sorry`
warning: Challenge.lean:33:8: declaration uses `sorry`
warning: Challenge.lean:37:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `BinaryGraySuperpositionTransfer/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'BinaryGraySuperpositionTransferChallenge.glue_alpha_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'BinaryGraySuperpositionTransferChallenge.gb_pm_recurrence' depends on axioms: [propext, Classical.choice, Quot.sound]
'BinaryGraySuperpositionTransferChallenge.gb_doublyCyclic_pm' depends on axioms: [propext, Classical.choice, Quot.sound]
'BinaryGraySuperpositionTransferChallenge.gbGraph_exactChrom' depends on axioms: [propext, Classical.choice, Quot.sound]
'BinaryGraySuperpositionTransferChallenge.gb_doublyCyclic_exactChrom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BinaryGraySuperpositionTransferChallenge.gb_chrom_root_two_sharp_k2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BinaryGraySuperpositionTransferChallenge.sb_pm_const_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'BinaryGraySuperpositionTransferChallenge.non_vacuity_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
