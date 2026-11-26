# Formal Verification Audit (`mxfp8-e2m5-e3m4-frontier`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **10 / 10** | **10 / 10** | **10 / 10** | **95 / 100** |

*Weighted composite: `3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 95 / 100`. See [`README.md`](README.md) for the full For Mathematicians, For Non-Mathematicians, and Prior-Art Context sections.*

## Build & Challenge Checks

```text
$ lake build
✔ [2/11] Built Mxfp8Frontier.Defs (1.2s)
✔ [3/11] Built Mxfp8Frontier.RatOrder (2.2s)
✔ [4/11] Built Mxfp8Frontier.GridCollapse (3.3s)
✔ [5/11] Built Mxfp8Frontier.DelayedScaling (3.3s)
✔ [6/11] Built Mxfp8Frontier.E4M3vsE5M2 (3.3s)
✔ [7/11] Built Mxfp8Frontier.FiveRegimeFrontier (2.7s)
✔ [8/11] Built Mxfp8Frontier (1.1s)
✔ [10/11] Built Solution (1.3s)
Build completed successfully (11 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.2s)
warning: Challenge.lean:31:8: declaration uses `sorry`
warning: Challenge.lean:52:8: declaration uses `sorry`
warning: Challenge.lean:80:8: declaration uses `sorry`
warning: Challenge.lean:115:8: declaration uses `sorry`
warning: Challenge.lean:154:8: declaration uses `sorry`
warning: Challenge.lean:176:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide`/`lemma` in any declaration across `Mxfp8Frontier/`, `Mxfp8Frontier.lean`, or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'Mxfp8FrontierChallenge.fp8_e1m6_collapse_to_int8_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mxfp8FrontierChallenge.mxfp8_e4m3_vs_e5m2_all_b_crossover_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Mxfp8FrontierChallenge.mxfp8_e8m0_complete_five_regime_frontier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Mxfp8FrontierChallenge.deepseek_fp32_scale_complete_five_regime_frontier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Mxfp8FrontierChallenge.delayed_scaling_spike_clipping_crossover_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Mxfp8FrontierChallenge.fp8_block_scaling_bias_invariance_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.
