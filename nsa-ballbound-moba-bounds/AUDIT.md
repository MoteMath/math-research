# Formal Verification Audit (`nsa-ballbound-moba-bounds`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **10 / 10** | **9 / 10** | **10 / 10** | **10 / 10** | **95 / 100** |

*Weighted composite: `3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 3*9 + 2*10 + 2*9 + 2*10 + 10 = 95 / 100`. See [`README.md`](README.md) for the full For Mathematicians, For Non-Mathematicians, and Prior-Art Context sections.*

## Build & Challenge Checks

Clean `lake build` wall time: **`8.75 s`** (`TotalSeconds: 8.7484704`, well under the `< 40 s` and `< 1 GB` RAM budget).

```text
$ lake clean; lake build
✔ [2/11] Built NsaBallBoundMoba.Defs (1.1s)
✔ [3/11] Built NsaBallBoundMoba.RatOrder (1.7s)
✔ [4/11] Built NsaBallBoundMoba.MobaBlindspot (2.1s)
✔ [5/11] Built NsaBallBoundMoba.BallBoundExact (2.1s)
✔ [6/11] Built NsaBallBoundMoba.QuestAabbSeparation (2.2s)
✔ [7/11] Built NsaBallBoundMoba.NsaGateAndPopcnt (1.4s)
✔ [8/11] Built NsaBallBoundMoba (1.0s)
✔ [10/11] Built Solution (1.2s)
Build completed successfully (11 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.2s)
warning: Challenge.lean:37:8: declaration uses `sorry`
warning: Challenge.lean:58:8: declaration uses `sorry`
warning: Challenge.lean:83:8: declaration uses `sorry`
warning: Challenge.lean:109:8: declaration uses `sorry`
warning: Challenge.lean:138:8: declaration uses `sorry`
warning: Challenge.lean:167:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide`/`lemma` anywhere in `NsaBallBoundMoba/`, `NsaBallBoundMoba.lean`, or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'NsaBallBoundMobaChallenge.moba_antipodal_and_buried_needle_blindspot_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NsaBallBoundMobaChallenge.zero_sqrt_ball_bound_exact_soundness_zero_fn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NsaBallBoundMobaChallenge.ball_bound_strictly_tighter_than_quest_aabb_and_half_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NsaBallBoundMobaChallenge.quantization_absorbing_ball_bound_zero_fn_all_precisions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NsaBallBoundMobaChallenge.nsa_three_branch_convex_gate_antipodal_breakdown' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NsaBallBoundMobaChallenge.popcnt_twoplane_summary_bandwidth_dominance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.
