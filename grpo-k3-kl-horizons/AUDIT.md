# Verification Audit (`grpo-k3-kl-horizons`)

## Toolchain & Trust Configuration

- **Lean Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib, zero external packages)
- **Comparator Config:** [`comparator.json`](comparator.json) (`"enable_nanoda": true`, permitted axioms: `["propext", "Classical.choice", "Quot.sound"]`)
- **Clean Rebuild Wall Time:** `12.63 s` (`lake clean && lake build && lake build Challenge && lake env lean scripts/PrintAxioms.lean`)
- **Forensic Grep Audit (`sorry`, `admit`, `axiom`, `native_decide`, `lemma` outside `Challenge.lean`):** `0` code occurrences (only doc-comment `Zero Mathlib, zero native_decide.` in `GrpoK3Kl/RatOrder.lean`).

---

## Verbatim Transcripts

### 1. `lake clean && lake build`

```text
✔ [2/10] Built GrpoK3Kl.Defs (1.3s)
✔ [3/10] Built GrpoK3Kl.RatOrder (1.4s)
✔ [4/10] Built GrpoK3Kl.SchulmanK3 (3.1s)
✔ [5/10] Built GrpoK3Kl.LogProbClipping (3.1s)
✔ [6/10] Built GrpoK3Kl.GrpoAdvantage (3.1s)
✔ [7/10] Built GrpoK3Kl (1.5s)
✔ [9/10] Built Solution (1.8s)
Build completed successfully (10 jobs).
```

### 2. `lake build Challenge`

```text
⚠ [3/4] Built Challenge (1.7s)
warning: Challenge.lean:29:8: declaration uses `sorry`
warning: Challenge.lean:48:8: declaration uses `sorry`
warning: Challenge.lean:92:8: declaration uses `sorry`
warning: Challenge.lean:112:8: declaration uses `sorry`
warning: Challenge.lean:135:8: declaration uses `sorry`
warning: Challenge.lean:164:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

### 3. `lake env lean scripts/PrintAxioms.lean`

```text
'GrpoK3KlChallenge.schulman_k3_exact_nonnegativity_and_quadratic_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GrpoK3KlChallenge.bf16_k3_negative_kl_and_deadzone_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'GrpoK3KlChallenge.fp8_bf16_logprob_cancellation_clip_collapse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GrpoK3KlChallenge.direct_logit_diff_binade_invariance' depends on axioms: [propext, Classical.choice, Quot.sound]
'GrpoK3KlChallenge.grpo_binary_reward_extreme_overweighting_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GrpoK3KlChallenge.grpo_bf16_onepass_negvar_and_fp8_mean_stall' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```
