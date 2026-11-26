# Formal Verification Audit (`sampling-gumbel-cdf-bounds`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **10 / 10** | **9 / 10** | **10 / 10** | **10 / 10** | **95 / 100** |

*Weighted composite: `3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 3*9 + 2*10 + 2*9 + 2*10 + 10 = 95 / 100`. See [`README.md`](README.md) for the full For Mathematicians, For Non-Mathematicians, and Prior-Art Context sections.*

## Build & Challenge Checks

```text
$ lake build
✔ [6/10] Built SamplingHorizons.SpecDec (546s)
✔ [7/10] Built SamplingHorizons (1.9s)
✔ [9/10] Built Solution (2.1s)
Build completed successfully (10 jobs).

$ lake build Challenge
⚠ [3/4] Replayed Challenge
warning: Challenge.lean:27:8: declaration uses `sorry`
warning: Challenge.lean:50:8: declaration uses `sorry`
warning: Challenge.lean:88:8: declaration uses `sorry`
warning: Challenge.lean:107:8: declaration uses `sorry`
warning: Challenge.lean:128:8: declaration uses `sorry`
warning: Challenge.lean:149:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide`/`lemma` anywhere in `SamplingHorizons/`, `SamplingHorizons.lean`, or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'SamplingHorizonsChallenge.gumbel_max_impossible_token_horizon_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SamplingHorizonsChallenge.specdec_exact_losslessness_vs_finite_residual_crash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SamplingHorizonsChallenge.specdec_q32_integer_exact_zero_leak' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SamplingHorizonsChallenge.descending_cdf_swamping_erasure_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SamplingHorizonsChallenge.fenwick_pairwise_tree_zero_swamping_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SamplingHorizonsChallenge.top_p_nucleus_mass_shortfall_lower_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.
