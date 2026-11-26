# Formal Verification Audit (`rope-q32-coprime-freeze`)

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
✔ [2/11] Built RopeQ32Coprime.Defs (1.3s)
✔ [3/11] Built RopeQ32Coprime.RatOrder (1.6s)
✔ [4/11] Built RopeQ32Coprime.Q32Modular (1.7s)
✔ [5/11] Built RopeQ32Coprime.FreezeHorizon (3.9s)
✔ [6/11] Built RopeQ32Coprime.RelativeErrorCayley (4.0s)
✔ [7/11] Built RopeQ32Coprime.RotationNormDrift (4.7s)
✔ [8/11] Built RopeQ32Coprime (1.1s)
✔ [10/11] Built Solution (1.3s)
Build completed successfully (11 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.2s)
warning: Challenge.lean:35:8: declaration uses `sorry`
warning: Challenge.lean:70:8: declaration uses `sorry`
warning: Challenge.lean:90:8: declaration uses `sorry`
warning: Challenge.lean:111:8: declaration uses `sorry`
warning: Challenge.lean:137:8: declaration uses `sorry`
warning: Challenge.lean:178:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide`/`lemma` anywhere in `RopeQ32Coprime/`, `RopeQ32Coprime.lean`, or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'RopeQ32CoprimeChallenge.rope_bf16_fp16_consecutive_freeze_run_exact' depends on axioms: [propext, Quot.sound]
'RopeQ32CoprimeChallenge.rope_high_freq_random_phase_horizon_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'RopeQ32CoprimeChallenge.q32_modular_odd_dyadic_zero_drift_exact' depends on axioms: [propext, Quot.sound]
'RopeQ32CoprimeChallenge.quantized_rotation_norm_drift_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'RopeQ32CoprimeChallenge.relative_position_factorization_error_decomposition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'RopeQ32CoprimeChallenge.dyadic_cayley_relative_composition_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.
