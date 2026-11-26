# Formal Verification Audit (`mrope-3d-coprime-bounds`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26  
**Full clean `lake build` wall time:** `11.66 s`

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **10 / 10** | **9 / 10** | **10 / 10** | **10 / 10** | **95 / 100** |

*Weighted composite: `3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 3*9 + 2*10 + 2*9 + 2*10 + 10 = 95 / 100`. See [`README.md`](README.md) for the full For Mathematicians, For Non-Mathematicians, and Prior-Art Context sections.*

## Build & Challenge Checks

```text
$ lake build
✔ [2/10] Built Mrope3dCoprime.Defs (1.0s)
✔ [3/10] Built Mrope3dCoprime.RatOrder (1.5s)
✔ [4/10] Built Mrope3dCoprime.SeparableFloor (6.6s)
✔ [5/10] Built Mrope3dCoprime.Bf16FreezeResolution (6.5s)
✔ [6/10] Built Mrope3dCoprime.Q32ModularPhase (6.5s)
✔ [7/10] Built Mrope3dCoprime (953ms)
✔ [9/10] Built Solution (1.2s)
Build completed successfully (10 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.1s)
warning: Challenge.lean:28:8: declaration uses `sorry`
warning: Challenge.lean:71:8: declaration uses `sorry`
warning: Challenge.lean:98:8: declaration uses `sorry`
warning: Challenge.lean:118:8: declaration uses `sorry`
warning: Challenge.lean:141:8: declaration uses `sorry`
warning: Challenge.lean:168:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide`/`lemma` anywhere in `Mrope3dCoprime/`, `Mrope3dCoprime.lean`, or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'Mrope3dCoprimeChallenge.separable_3d_mrope_axis_floor_theorem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Mrope3dCoprimeChallenge.coupled_3d_mrope_shatters_separable_floor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Mrope3dCoprimeChallenge.contiguous_mrope_bf16_width_freeze_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Mrope3dCoprimeChallenge.interleaved_vs_contiguous_mrope_resolution_gap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Mrope3dCoprimeChallenge.q32_3d_modular_phase_exact_relative_invariance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Mrope3dCoprimeChallenge.cross_modal_fp_phase_drift_vs_q32_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.
