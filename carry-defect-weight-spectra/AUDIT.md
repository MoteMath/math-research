# Formal Verification Audit (`carry-defect-weight-spectra`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built CarryDefectWeightSpectra.Defs (7.5s)
✔ [3/7] Built CarryDefectWeightSpectra.Theorems (45s)
✔ [4/7] Built CarryDefectWeightSpectra (1.9s)
✔ [6/7] Built Solution (2.4s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.8s)
warning: Challenge.lean:17:8: declaration uses `sorry`
warning: Challenge.lean:23:8: declaration uses `sorry`
warning: Challenge.lean:29:8: declaration uses `sorry`
warning: Challenge.lean:35:8: declaration uses `sorry`
warning: Challenge.lean:41:8: declaration uses `sorry`
warning: Challenge.lean:51:8: declaration uses `sorry`
warning: Challenge.lean:56:8: declaration uses `sorry`
warning: Challenge.lean:62:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `CarryDefectWeightSpectra/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'CarryDefectWeightSpectraChallenge.spectrum_one_mod_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarryDefectWeightSpectraChallenge.mersenne_zero_defect_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarryDefectWeightSpectraChallenge.mersenne_spectrum_classify' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarryDefectWeightSpectraChallenge.defectWeight_shift_add' depends on axioms: [propext, Quot.sound]
'CarryDefectWeightSpectraChallenge.potentialCert_sound' depends on axioms: [propext, Quot.sound]
'CarryDefectWeightSpectraChallenge.spectrum_23' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarryDefectWeightSpectraChallenge.spectrum_175' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarryDefectWeightSpectraChallenge.spectrum_211' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
