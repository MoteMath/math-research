# Verification Audit (`relu2-teal-deadzone-bounds`)

- **Date:** 2026-11-26
- **Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)
- **Comparator:** `comparator.json` with `"enable_nanoda": true`
- **Source Report:** `ai-math-continuous-20261126/wave31/w31-int4-ffn-sparsity/REPORT.md`

## 1. Clean Build (`lake clean && lake build`)

Elapsed wall time: **`7.11 s`** (`0` errors, `0` warnings).

```text
✔ [2/11] Built Relu2TealDeadzone.Defs (1.2s)
✔ [3/11] Built Relu2TealDeadzone.RatOrder (1.6s)
✔ [4/11] Built Relu2TealDeadzone.KurtosisOutliers (2.0s)
✔ [5/11] Built Relu2TealDeadzone.QuantOrderDichotomy (2.1s)
✔ [6/11] Built Relu2TealDeadzone.DeadzoneReclamation (2.0s)
✔ [7/11] Built Relu2TealDeadzone.MaskFlipBitmask (2.0s)
✔ [8/11] Built Relu2TealDeadzone (955ms)
✔ [10/11] Built Solution (1.2s)
Build completed successfully (11 jobs).
CLEAN_BUILD_SECONDS: 7.11
```

## 2. Trusted Challenge Build (`lake build Challenge`)

```text
⚠ [3/4] Built Challenge (1.2s)
warning: Challenge.lean:35:8: declaration uses `sorry`
warning: Challenge.lean:74:8: declaration uses `sorry`
warning: Challenge.lean:98:8: declaration uses `sorry`
warning: Challenge.lean:124:8: declaration uses `sorry`
warning: Challenge.lean:144:8: declaration uses `sorry`
warning: Challenge.lean:168:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

## 3. Axiom Audit (`lake env lean scripts/PrintAxioms.lean`)

All 6 headline theorems depend strictly on `[propext, Classical.choice, Quot.sound]`:

```text
'Relu2TealDeadzoneChallenge.relu2_exact_kurtosis_seventy_thirds_and_outlier_amplification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Relu2TealDeadzoneChallenge.relu2_quantization_order_uniform_pre_beats_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Relu2TealDeadzoneChallenge.relu2_quantization_order_fp_post_beats_pre_exact_4x' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Relu2TealDeadzoneChallenge.teal_cats_shifted_deadzone_reclamation_uniform_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Relu2TealDeadzoneChallenge.teal_cats_fp_superquadratic_logarithmic_density_bonus' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Relu2TealDeadzoneChallenge.prune_before_quantize_mask_flip_and_bitmask_crossover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 4. Package Validator (`validate_pkgs.py`)

```text
PASS relu2-teal-deadzone-bounds
```
