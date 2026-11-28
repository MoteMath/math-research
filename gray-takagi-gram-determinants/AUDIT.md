# Verification & Audit Receipt (`gray-takagi-gram-determinants`)

- **Toolchain:** `leanprover/lean4:v4.34.1` + Mathlib `v4.34.1`
- **Palomar Comparator Manifest:** [`comparator.json`](comparator.json) (`enable_nanoda: true`, 9 pinned theorems, 8 pinned definitions)
- **Permitted Axioms:** `[propext, Classical.choice, Quot.sound]` (zero `sorry`, zero `native_decide`, zero custom axioms)

## Build Receipt

```text
> lake build
✔ [3093/3097] Built GrayTakagiDet.Theorems (21s)
✔ [3094/3097] Built GrayTakagiDet (14s)
✔ [3096/3097] Built Solution (15s)
Build completed successfully (3097 jobs).

> lake build Challenge
⚠ [1550/1551] Built Challenge (10s)
warning: Challenge.lean:6:8: declaration uses `sorry`
warning: Challenge.lean:11:8: declaration uses `sorry`
warning: Challenge.lean:16:8: declaration uses `sorry`
warning: Challenge.lean:23:8: declaration uses `sorry`
warning: Challenge.lean:29:8: declaration uses `sorry`
warning: Challenge.lean:36:8: declaration uses `sorry`
warning: Challenge.lean:44:8: declaration uses `sorry`
warning: Challenge.lean:51:8: declaration uses `sorry`
warning: Challenge.lean:57:8: declaration uses `sorry`
Build completed successfully (1551 jobs).
```

## `#print axioms` Receipt (`lake env lean PrintAxioms.lean`)

```text
'GrayTakagiDet.takagi_le_grayPopSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'GrayTakagiDet.takagi_recurrence' depends on axioms: [propext, Classical.choice, Quot.sound]
'GrayTakagiDet.takagi_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'GrayTakagiDet.det_grayAndMat' depends on axioms: [propext, Classical.choice, Quot.sound]
'GrayTakagiDet.det_grayAndMat_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'GrayTakagiDet.det_grayDisjointMat' depends on axioms: [propext, Classical.choice, Quot.sound]
'GrayTakagiDet.det_grayOrMat' depends on axioms: [propext, Classical.choice, Quot.sound]
'GrayTakagiDet.det_grayXorMat' depends on axioms: [propext, Classical.choice, Quot.sound]
'GrayTakagiDet.det_grayAndMat_pow2_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Provenance

Discovered by zero-floating-point bare-metal RDNA3 (`gfx1100`) 32-prime CRT modular determinant mining in `alien-silicon-hunt-20261128` Track A (`mut_0_pow2_pop(and(gray(i),gray(j)))_n32`, score `145`, `NO_EXACT_OEIS_MATCH`, and `mut_0_pow2_pop(or(gray(i),gray(j)))_n32`, score `125`, `NO_EXACT_OEIS_MATCH`), validated bit-identically on CPU, lifted symbolically to all `q` over any commutative ring $R$, and proved unconditionally in Lean 4's kernel.
