# Formal Verification Audit (`specdec-wiener-temp-bounds`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **10 / 10** | **9 / 10** | **10 / 10** | **10 / 10** | **95 / 100** |

*Weighted composite: `3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 3*9 + 2*10 + 2*9 + 2*10 + 10 = 95 / 100`. See [`README.md`](README.md) for the full For Mathematicians, For Non-Mathematicians, and Prior-Art Context sections.*

## Build & Challenge Checks

```text
$ lake clean && lake build
✔ [2/12] Built SpecDecWienerTemp.Defs (1.4s)
✔ [3/12] Built SpecDecWienerTemp.RatOrder (1.7s)
✔ [4/12] Built SpecDecWienerTemp.WienerMMSE (11s)
✔ [5/12] Built SpecDecWienerTemp.AcceptanceTV (11s)
✔ [6/12] Built SpecDecWienerTemp.SpecDecYield (11s)
✔ [7/12] Built SpecDecWienerTemp.AcceptanceRescue (11s)
✔ [8/12] Built SpecDecWienerTemp.Sub4BitDominance (3.7s)
✔ [9/12] Built SpecDecWienerTemp (1.1s)
✔ [11/12] Built Solution (1.4s)
Build completed successfully (12 jobs).
BUILD_EXIT=0 CLEAN_ELAPSED=21.37s

$ lake build Challenge
⚠ [3/4] Built Challenge (1.5s)
warning: Challenge.lean:32:8: declaration uses `sorry`
warning: Challenge.lean:50:8: declaration uses `sorry`
warning: Challenge.lean:75:8: declaration uses `sorry`
warning: Challenge.lean:102:8: declaration uses `sorry`
warning: Challenge.lean:123:8: declaration uses `sorry`
warning: Challenge.lean:150:8: declaration uses `sorry`
Build completed successfully (4 jobs).
CHALLENGE_EXIT=0
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide`/`lemma` anywhere in `SpecDecWienerTemp/`, `SpecDecWienerTemp.lean`, or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'SpecDecWienerTempChallenge.wiener_mmse_temperature_uniquely_minimizes_logit_mse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpecDecWienerTempChallenge.wiener_mmse_strictly_beats_variance_matching_and_uncalibrated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpecDecWienerTempChallenge.quantized_draft_tv_acceptance_lower_bound_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpecDecWienerTempChallenge.expected_specdec_yield_and_speedup_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpecDecWienerTempChallenge.sub4bit_self_speculative_dominance_over_fp8_bf16' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpecDecWienerTempChallenge.wiener_temperature_exact_acceptance_rescue_witnesses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS_EXIT=0
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.
