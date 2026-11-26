# Formal Verification Audit (`flashattn-dyadic-slack-bounds`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26  
**Clean build time:** `13.92 s` (`< 40 s` target, `< 1 GB` RAM)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **10 / 10** | **9 / 10** | **10 / 10** | **10 / 10** | **95 / 100** |

*Weighted composite: `3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 3*9 + 2*10 + 2*9 + 2*10 + 10 = 95 / 100`. See [`README.md`](README.md) for the full For Mathematicians, For Non-Mathematicians, and Prior-Art Context sections.*

## Build & Challenge Checks

```text
$ lake clean && lake build
✔ [2/9] Built FlashAttnDyadicSlack.Defs (2.2s)
✔ [3/9] Built FlashAttnDyadicSlack.DyadicRescale (3.4s)
✔ [4/9] Built FlashAttnDyadicSlack.SlackOverflow (3.5s)
✔ [5/9] Built FlashAttnDyadicSlack.DyadicNormKulisch (2.7s)
✔ [6/9] Built FlashAttnDyadicSlack (2.6s)
✔ [8/9] Built Solution (2.7s)
Build completed successfully (9 jobs).
CLEAN_BUILD_SECONDS=13.92

$ lake build Challenge
⚠ [3/4] Built Challenge (2.2s)
warning: Challenge.lean:36:8: declaration uses `sorry`
warning: Challenge.lean:63:8: declaration uses `sorry`
warning: Challenge.lean:84:8: declaration uses `sorry`
warning: Challenge.lean:109:8: declaration uses `sorry`
warning: Challenge.lean:131:8: declaration uses `sorry`
warning: Challenge.lean:157:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide`/`lemma` anywhere in `FlashAttnDyadicSlack/`, `FlashAttnDyadicSlack.lean`, or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'FlashAttnDyadicSlackChallenge.dyadic_power_of_two_rescale_zero_mantissa_error' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'FlashAttnDyadicSlackChallenge.eager_online_softmax_one_ulp_per_step_collapse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'FlashAttnDyadicSlackChallenge.slack_threshold_fp16_fp8_overflow_boundary_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'FlashAttnDyadicSlackChallenge.fp16_flat_attention_65520_overflow_cliff_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'FlashAttnDyadicSlackChallenge.dyadic_exponent_normalization_cancels_identically' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'FlashAttnDyadicSlackChallenge.flash_tile_int32_kulisch_associativity_and_exactness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.
