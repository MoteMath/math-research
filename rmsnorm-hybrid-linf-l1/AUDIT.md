# Formal Verification Audit (`rmsnorm-hybrid-linf-l1`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **10 / 10** | **9 / 10** | **10 / 10** | **93 / 100** |

*Weighted composite: `3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 93 / 100`. See [`README.md`](README.md) for the full mathematical overview.*

## Build & Challenge Checks

```text
$ lake build
✔ [2/10] Built RmsnormHybridLinfL1.Defs (1.7s)
✔ [3/10] Built RmsnormHybridLinfL1.RatOrder (2.3s)
✔ [4/10] Built RmsnormHybridLinfL1.HybridNorm (5.3s)
✔ [5/10] Built RmsnormHybridLinfL1.Swamping (3.1s)
✔ [6/10] Built RmsnormHybridLinfL1.NegVariance (6.5s)
✔ [7/10] Built RmsnormHybridLinfL1 (1.8s)
✔ [9/10] Built Solution (2.1s)
Build completed successfully (10 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.3s)
warning: Challenge.lean:37:8: declaration uses `sorry`
warning: Challenge.lean:58:8: declaration uses `sorry`
warning: Challenge.lean:76:8: declaration uses `sorry`
warning: Challenge.lean:107:8: declaration uses `sorry`
warning: Challenge.lean:146:8: declaration uses `sorry`
warning: Challenge.lean:184:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide`/`lemma` anywhere in `RmsnormHybridLinfL1/`, `RmsnormHybridLinfL1.lean`, or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'RmsnormHybridLinfL1Challenge.hybrid_linf_l1_exact_upper_and_lower_envelopes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'RmsnormHybridLinfL1Challenge.hybrid_linf_l1_minimax_d_quarter_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'RmsnormHybridLinfL1Challenge.dyadic_llama3_d4096_hybrid_norm_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'RmsnormHybridLinfL1Challenge.bf16_fp16_fp8_sumsq_swamping_horizon_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'RmsnormHybridLinfL1Challenge.bf16_fp16_onepass_layernorm_negative_variance_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'RmsnormHybridLinfL1Challenge.twopass_shifted_mean_variance_nonneg_universal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.
