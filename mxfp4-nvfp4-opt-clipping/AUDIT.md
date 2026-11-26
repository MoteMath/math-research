# Formal Verification Audit (`mxfp4-nvfp4-opt-clipping`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **10 / 10** | **10 / 10** | **10 / 10** | **10 / 10** | **97 / 100** |

*Weighted composite: `3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 97 / 100`. See [`README.md`](README.md) for the full For Mathematicians, For Non-Mathematicians, and Prior-Art Context sections.*

## Build & Challenge Checks

```text
$ lake build
✔ [2/10] Built Mxfp4OptClipping.Defs (8.8s)
✔ [3/10] Built Mxfp4OptClipping.RatOrder (17s)
✔ [5/10] Built Mxfp4OptClipping.E2M1NegZero (48s)
✔ [6/10] Built Mxfp4OptClipping.Mxfp4E8M0 (100s)
✔ [6/10] Built Mxfp4OptClipping.Nvfp4E4M3 (49s)
✔ [7/10] Built Mxfp4OptClipping (29s)
✔ [9/10] Built Solution (15s)
Build completed successfully (10 jobs).

$ lake build Challenge
⚠ [3/4] Replayed Challenge
warning: Challenge.lean:34:8: declaration uses `sorry`
warning: Challenge.lean:53:8: declaration uses `sorry`
warning: Challenge.lean:85:8: declaration uses `sorry`
warning: Challenge.lean:123:8: declaration uses `sorry`
warning: Challenge.lean:153:8: declaration uses `sorry`
warning: Challenge.lean:180:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `Mxfp4OptClipping/`, `Mxfp4OptClipping.lean`, or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'Mxfp4OptClippingChallenge.mxfp4_e8m0_scale_down_piecewise_linear_crossover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Mxfp4OptClippingChallenge.mxfp4_opt_e8m0_all_b_ef21_three_regime_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Mxfp4OptClippingChallenge.nvfp4_ceil_vs_nearest_e4m3_all_b_ef21_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Mxfp4OptClippingChallenge.nvfp4_opt_e4m3_b16_and_b1_synergy_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Mxfp4OptClippingChallenge.mxfp4_opt_e8m0_never_drops_two_exponents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Mxfp4OptClippingChallenge.e2m1_neg_zero_repurposing_exact_gain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.
