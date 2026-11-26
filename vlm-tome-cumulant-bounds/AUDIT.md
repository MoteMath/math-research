# Formal Verification Audit (`vlm-tome-cumulant-bounds`)

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
✔ [2/10] Built VlmTomeCumulant.Defs (1.2s)
✔ [3/10] Built VlmTomeCumulant.RatOrder (1.4s)
✔ [4/10] Built VlmTomeCumulant.WalshHadamardSimHash (3.2s)
✔ [5/10] Built VlmTomeCumulant.ScheduleFlopBounds (3.2s)
✔ [6/10] Built VlmTomeCumulant.ProportionalAttention (3.3s)
✔ [7/10] Built VlmTomeCumulant (948ms)
✔ [9/10] Built Solution (1.1s)
Build completed successfully (10 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.2s)
warning: Challenge.lean:36:8: declaration uses `sorry`
warning: Challenge.lean:64:8: declaration uses `sorry`
warning: Challenge.lean:84:8: declaration uses `sorry`
warning: Challenge.lean:119:8: declaration uses `sorry`
warning: Challenge.lean:152:8: declaration uses `sorry`
warning: Challenge.lean:183:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide`/`lemma` anywhere in `VlmTomeCumulant/`, `VlmTomeCumulant.lean`, or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'VlmTomeCumulantChallenge.unweighted_merge_tv_distortion_and_exact_ceiling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'VlmTomeCumulantChallenge.proportional_attention_zero_dispersion_exact_invariance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'VlmTomeCumulantChallenge.within_cluster_dispersion_jensen_underweight_and_cumulant2_bonus' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'VlmTomeCumulantChallenge.bipartite_wht_int4_outlier_rescue_vs_binary_walsh_tie' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'VlmTomeCumulantChallenge.vit_front_loaded_dominates_constant_r_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'VlmTomeCumulantChallenge.late_loaded_merging_flop_infeasibility_ceiling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.
