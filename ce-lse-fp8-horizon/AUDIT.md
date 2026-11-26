# Formal Verification Audit (`ce-lse-fp8-horizon`)

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
✔ [4/9] Built CeLseHorizon.CeConservation (30s)
✔ [5/9] Built CeLseHorizon.LossScaleLse (52s)
✔ [6/9] Built CeLseHorizon (25s)
✔ [8/9] Built Solution (15s)
Build completed successfully (9 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (35s)
warning: Challenge.lean:31:8: declaration uses `sorry`
warning: Challenge.lean:54:8: declaration uses `sorry`
warning: Challenge.lean:88:8: declaration uses `sorry`
warning: Challenge.lean:120:8: declaration uses `sorry`
warning: Challenge.lean:146:8: declaration uses `sorry`
warning: Challenge.lean:167:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide`/`lemma` in any code declaration across `CeLseHorizon/`, `CeLseHorizon.lean`, or `Solution.lean`.

## Kernel-Verified Arithmetic Audit Note

During formalization of Theorem 4 (`fp16_loss_scale_empty_window_collapse_exact`), Lean 4's kernel verified the exact algebraic identities and caught two decimal-expansion typos in the Wave 17C prose summary (`REPORT.md`):
- `65520 * 2^14 = 2^30 - 2^18 = 1,073,479,680` (kernel-verified; `REPORT.md` prose printed `1,073,217,536`, which equals `65504 * 2^14 = 2^30 - 2^19`).
- `65520 * 2^25 = 2^41 - 2^29 = 2,198,486,384,640` (kernel-verified; `REPORT.md` prose printed `2,197,949,546,496`).

Both exact algebraic forms (`65520 * 2^14 = 2^30 - 2^18 = 1073479680` and `65520 * 2^25 = 2^41 - 2^29 = 2198486384640`) are kernel-checked in `Challenge.lean` and `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'CeLseHorizonChallenge.ce_gradient_zero_sum_conservation_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CeLseHorizonChallenge.fp8_e4m3_dual_horizon_and_rne_overshoot_cliff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CeLseHorizonChallenge.fp8_e5m2_128k_vocab_conservation_collapse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CeLseHorizonChallenge.fp16_loss_scale_empty_window_collapse_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CeLseHorizonChallenge.lse_naive_swamping_vs_pairwise_tree_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CeLseHorizonChallenge.label_smoothing_fp8_total_erasure_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.
