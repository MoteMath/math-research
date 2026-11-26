# Formal Verification Audit (`allreduce-topology-xorvdc`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Build & Challenge Checks

```text
$ lake build
✔ [6/10] Built AllReduceXorVdc.TopologyLaws (57s)
✔ [7/10] Built AllReduceXorVdc (35s)
✔ [9/10] Built Solution (27s)
Build completed successfully (10 jobs).

$ lake build Challenge
⚠ [3/4] Replayed Challenge
warning: Challenge.lean:35:8: declaration uses `sorry`
warning: Challenge.lean:57:8: declaration uses `sorry`
warning: Challenge.lean:91:8: declaration uses `sorry`
warning: Challenge.lean:128:8: declaration uses `sorry`
warning: Challenge.lean:147:8: declaration uses `sorry`
warning: Challenge.lean:164:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide`/`lemma` anywhere in `AllReduceXorVdc/`, `AllReduceXorVdc.lean`, or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'AllReduceXorVdcChallenge.allreduce_subulp_drift_ring_vs_tree_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AllReduceXorVdcChallenge.allreduce_cancel_wipeout_ring_vs_tree_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AllReduceXorVdcChallenge.cross_rank_xor_vdc_bijection_and_exact_mse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AllReduceXorVdcChallenge.bf16_residual_stream_freeze_depth_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AllReduceXorVdcChallenge.kahan_compensated_residual_exact_recovery' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AllReduceXorVdcChallenge.fixed_scale_ternary_saturation_barrier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.
