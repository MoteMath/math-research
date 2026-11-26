# Formal Verification Audit (`flashattn-bwd-signflip`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **10 / 10** | **9 / 10** | **10 / 10** | **10 / 10** | **95 / 100** |

*Weighted composite: `3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 95 / 100`. See [`README.md`](README.md) for the full For Mathematicians, For Non-Mathematicians, and Prior-Art Context sections.*

## Build & Challenge Checks

```text
$ lake build
✔ [2/10] Built FlashAttnBwdSignflip.Defs (1.5s)
✔ [3/10] Built FlashAttnBwdSignflip.RatOrder (1.7s)
✔ [4/10] Built FlashAttnBwdSignflip.SoftmaxJacobian (2.7s)
✔ [5/10] Built FlashAttnBwdSignflip.DcLeakage (7.9s)
✔ [6/10] Built FlashAttnBwdSignflip.KeyCenteringFormat (1.7s)
✔ [7/10] Built FlashAttnBwdSignflip (1.0s)
✔ [9/10] Built Solution (1.4s)
Build completed successfully (10 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.4s)
warning: Challenge.lean:28:8: declaration uses `sorry`
warning: Challenge.lean:48:8: declaration uses `sorry`
warning: Challenge.lean:86:8: declaration uses `sorry`
warning: Challenge.lean:118:8: declaration uses `sorry`
warning: Challenge.lean:164:8: declaration uses `sorry`
warning: Challenge.lean:196:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide`/`lemma` anywhere in `FlashAttnBwdSignflip/`, `FlashAttnBwdSignflip.lean`, or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'FlashAttnBwdSignflipChallenge.softmax_jacobian_zero_sum_and_cancellation_free_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'FlashAttnBwdSignflipChallenge.peaked_softmax_half_spurious_signflip_threshold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'FlashAttnBwdSignflipChallenge.direct_p_dp_midpoint_dc_leakage_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'FlashAttnBwdSignflipChallenge.flashattn_do_o_orthogonal_divergence_amplification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'FlashAttnBwdSignflipChallenge.key_centering_dq_invariance_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'FlashAttnBwdSignflipChallenge.unsigned_ue3m1_vs_mxfp4_dynamic_range_16x_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.
