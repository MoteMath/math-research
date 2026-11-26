# Formal Verification Audit (`alibi-bitsplit-kulisch`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **10 / 10** | **9 / 10** | **10 / 10** | **10 / 10** | **95 / 100** |

*Weighted composite: `3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 95 / 100`. See [`README.md`](README.md) for the full For Mathematicians, For Non-Mathematicians, and Prior-Art Context sections.*

## Build & Challenge Checks

```text
$ lake build
✔ [6/10] Built AlibiBitsplitKulisch.AlibiSwamping (239s)
✔ [7/10] Built AlibiBitsplitKulisch (278s)
✔ [9/10] Built Solution (377s)
Build completed successfully (10 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (546s)
warning: Challenge.lean:30:8: declaration uses `sorry`
warning: Challenge.lean:66:8: declaration uses `sorry`
warning: Challenge.lean:84:8: declaration uses `sorry`
warning: Challenge.lean:107:8: declaration uses `sorry`
warning: Challenge.lean:129:8: declaration uses `sorry`
warning: Challenge.lean:159:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide`/`lemma` anywhere in `AlibiBitsplitKulisch/`, `AlibiBitsplitKulisch.lean`, or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'AlibiBitsplitKulischChallenge.alibi_content_swamping_and_dyadic_slope_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AlibiBitsplitKulischChallenge.bilinear_int_asymmetric_bitsplit_crossovers_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AlibiBitsplitKulischChallenge.absmax_pinned_superoutlier_bitsplit_reversal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AlibiBitsplitKulischChallenge.mxfp_w5a7_beats_w6a6_mantissa_parity_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AlibiBitsplitKulischChallenge.mixed_format_signed_kulisch_width_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AlibiBitsplitKulischChallenge.kulisch_int64_exact_associativity_vs_fp32_drift' depends on axioms: [propext, Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.
