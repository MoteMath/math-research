# Formal Verification Audit (`mxfp6-ef21-rotations`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **10 / 10** | **8 / 10** | **10 / 10** | **91 / 100** |

*Weighted composite: `3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 91 / 100`. See [`README.md`](README.md) for the full For Mathematicians, For Non-Mathematicians, and Prior-Art Context sections.*

## Build & Challenge Checks

```text
$ lake build
✔ [2/9] Built Mxfp6Ef21Rotations.Defs (1.6s)
✔ [3/9] Built Mxfp6Ef21Rotations.RatOrder (2.5s)
✔ [4/9] Built Mxfp6Ef21Rotations.EF21Universal (28s)
✔ [5/9] Built Mxfp6Ef21Rotations.Rotations (17s)
✔ [6/9] Built Mxfp6Ef21Rotations (1.1s)
✔ [8/9] Built Solution (1.1s)
Build completed successfully (9 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.2s)
warning: Challenge.lean:27:8: declaration uses `sorry`
warning: Challenge.lean:44:8: declaration uses `sorry`
warning: Challenge.lean:62:8: declaration uses `sorry`
warning: Challenge.lean:76:8: declaration uses `sorry`
warning: Challenge.lean:89:8: declaration uses `sorry`
warning: Challenge.lean:101:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide`/`lemma` anywhere in `Mxfp6Ef21Rotations/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'Mxfp6Ef21RotationsChallenge.mxfp6_e3m2_nvfp6_ef21_universal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mxfp6Ef21RotationsChallenge.mxfp6_e2m3_nvfp6_ef21_universal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mxfp6Ef21RotationsChallenge.mxfp6_e2m3_vs_e3m2_exact_crossover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Mxfp6Ef21RotationsChallenge.hadamard_weight_quantization_defect_and_min_dyadic_coherence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Mxfp6Ef21RotationsChallenge.goethals_seidel_native_e2m1_orthonormal_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Mxfp6Ef21RotationsChallenge.quaternion_4of8_sparse_orthogonality_universal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.
