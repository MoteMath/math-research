# Formal Verification Audit (`mhc-sinkhorn-fp8-bounds`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **9 / 10** | **9 / 10** | **10 / 10** | **91 / 100** |

*Weighted composite: `3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 91 / 100`. See [`README.md`](README.md) for the full For Mathematicians, For Non-Mathematicians, and Prior-Art Context sections.*

## Build & Challenge Checks

```text
$ lake build
✔ [4/10] Built MhcSinkhornFp8.ScalingAndContraction (3.3s)
✔ [5/10] Built MhcSinkhornFp8.FloatFixedPoints (32s)
✔ [6/10] Built MhcSinkhornFp8.CollapseAndOrthogonal (32s)
✔ [7/10] Built MhcSinkhornFp8 (1.3s)
✔ [9/10] Built Solution (1.7s)
Build completed successfully (10 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.9s)
warning: Challenge.lean:38:8: declaration uses `sorry`
warning: Challenge.lean:51:8: declaration uses `sorry`
warning: Challenge.lean:90:8: declaration uses `sorry`
warning: Challenge.lean:109:8: declaration uses `sorry`
warning: Challenge.lean:128:8: declaration uses `sorry`
warning: Challenge.lean:142:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide`/`lemma` anywhere in `MhcSinkhornFp8/`, `MhcSinkhornFp8.lean`, or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'MhcSinkhornFp8Challenge.sinkhorn_diagonal_scaling_invariance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MhcSinkhornFp8Challenge.antidiagonal_swamping_bf16_fp8_fixed_point' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MhcSinkhornFp8Challenge.fp8_support_collapse_sqrt_n_minus_1_fixed_point' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MhcSinkhornFp8Challenge.mode_b_exact_sum_symmetric_overshoot_fixed_point' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MhcSinkhornFp8Challenge.sinkhorn_interstream_contraction_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MhcSinkhornFp8Challenge.dyadic_orthogonal_zero_division_mixers_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.
