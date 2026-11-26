# Formal Verification Audit (`ring-attention-kulisch-bounds`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **10 / 10** | **10 / 10** | **10 / 10** | **95 / 100** |

*Weighted composite: `3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 95 / 100`. See [`README.md`](README.md) for the mathematical and practical context.*

## Build & Challenge Checks

```text
$ lake build
✔ [2/11] Built RingAttnKulisch.Defs (2.2s)
✔ [3/11] Built RingAttnKulisch.RatOrder (2.9s)
✔ [4/11] Built RingAttnKulisch.OnlineSoftmax (3.0s)
✔ [5/11] Built RingAttnKulisch.SinkVanishing (3.1s)
✔ [6/11] Built RingAttnKulisch.KulischInvariance (3.4s)
✔ [7/11] Built RingAttnKulisch.DescParadox (2.6s)
✔ [8/11] Built RingAttnKulisch (1.6s)
✔ [10/11] Built Solution (1.8s)
Build completed successfully (11 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.6s)
warning: Challenge.lean:35:8: declaration uses `sorry`
warning: Challenge.lean:54:8: declaration uses `sorry`
warning: Challenge.lean:75:8: declaration uses `sorry`
warning: Challenge.lean:96:8: declaration uses `sorry`
warning: Challenge.lean:119:8: declaration uses `sorry`
warning: Challenge.lean:142:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide`/`lemma` anywhere in `RingAttnKulisch/`, `RingAttnKulisch.lean`, or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'RingAttnKulischChallenge.online_softmax_merge_exact_associativity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'RingAttnKulischChallenge.attention_sink_l2r_desc_vanishing_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'RingAttnKulischChallenge.binary_tree_vs_l2r_sink_survival_separation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'RingAttnKulischChallenge.descending_mi_phase_transition_paradox' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'RingAttnKulischChallenge.fixed_point_kulisch_topology_partition_invariance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'RingAttnKulischChallenge.fixed_point_sink_cliff_elimination' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.
