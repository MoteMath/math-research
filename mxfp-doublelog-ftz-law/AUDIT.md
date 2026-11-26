# Formal Verification Audit (`mxfp-doublelog-ftz-law`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **10 / 10** | **10 / 10** | **9 / 10** | **10 / 10** | **95 / 100** |

*Weighted composite: `3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 95 / 100`. See [`README.md`](README.md) for the full For Mathematicians, For Non-Mathematicians, and Prior-Art Context sections.*

## Build & Challenge Checks

```text
$ lake build
✔ [7/11] Built MxfpDoublelogFtz.DoubleLogLaw (5.7s)
✔ [8/11] Built MxfpDoublelogFtz (1.9s)
✔ [10/11] Built Solution (2.7s)
Build completed successfully (11 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.8s)
warning: Challenge.lean:23:8: declaration uses `sorry`
warning: Challenge.lean:36:8: declaration uses `sorry`
warning: Challenge.lean:57:8: declaration uses `sorry`
warning: Challenge.lean:79:8: declaration uses `sorry`
warning: Challenge.lean:122:8: declaration uses `sorry`
warning: Challenge.lean:142:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `MxfpDoublelogFtz/`, `MxfpDoublelogFtz.lean`, or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'MxfpDoublelogFtzChallenge.mxfp_e1_equals_e0_and_signed_unsigned_duality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MxfpDoublelogFtzChallenge.mxfp_universal_ef21_closed_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'MxfpDoublelogFtzChallenge.mxfp_doublelog_crossover_4b_cancellation_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MxfpDoublelogFtzChallenge.mxfp_e8m0_doublelog_shift_law' depends on axioms: [propext, Classical.choice, Quot.sound]
'MxfpDoublelogFtzChallenge.mxfp_ftz_four_to_the_b_underflow_penalty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MxfpDoublelogFtzChallenge.mxfp_ftz_hardware_bifurcation_e4m3_vs_e2mb' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.
