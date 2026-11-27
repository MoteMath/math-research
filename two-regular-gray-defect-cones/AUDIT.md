# Formal Verification Audit (`two-regular-gray-defect-cones`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built TwoRegularGrayDefectCones.Defs (2.4s)
✔ [3/7] Built TwoRegularGrayDefectCones.Theorems (26s)
✔ [4/7] Built TwoRegularGrayDefectCones (1.7s)
✔ [6/7] Built Solution (1.9s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.2s)
warning: Challenge.lean:17:8: declaration uses `sorry`
warning: Challenge.lean:23:8: declaration uses `sorry`
warning: Challenge.lean:28:8: declaration uses `sorry`
warning: Challenge.lean:34:8: declaration uses `sorry`
warning: Challenge.lean:40:8: declaration uses `sorry`
warning: Challenge.lean:46:8: declaration uses `sorry`
warning: Challenge.lean:52:8: declaration uses `sorry`
warning: Challenge.lean:59:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the eight intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `TwoRegularGrayDefectCones/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'TwoRegularGrayDefectConesChallenge.checkConePosCert_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoRegularGrayDefectConesChallenge.gray_defect_nonneg_all_q' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoRegularGrayDefectConesChallenge.W_G_sharp_two_fifths_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TwoRegularGrayDefectConesChallenge.extremal_W_G_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoRegularGrayDefectConesChallenge.W_G_thue_morse_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoRegularGrayDefectConesChallenge.E_G_mod4_law' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoRegularGrayDefectConesChallenge.E_G_dyadic_parabolic_sandwich' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TwoRegularGrayDefectConesChallenge.S_q_second_diff_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All eight headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), with no `sorryAx` and no `Lean.ofReduceBool`, matching `comparator.json` with `enable_nanoda: true`.
