# Formal Verification Audit (`paley32-mxfp4-outliers`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **9 / 10** | **9 / 10** | **10 / 10** | **91 / 100** |

*Weighted composite: `3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 91 / 100`. See [`README.md`](README.md) for the full For Mathematicians, For Non-Mathematicians, and Proof Architecture sections.*

## Build & Challenge Checks

```text
$ lake build
✔ [2/9] Built Paley32Mxfp4.Defs (1.4s)
✔ [3/9] Built Paley32Mxfp4.UniversalBounds (7.6s)
✔ [4/9] Built Paley32Mxfp4.Paley32 (110s)
✔ [5/9] Built Paley32Mxfp4.Hall16Bent (106s)
✔ [6/9] Built Paley32Mxfp4 (1.1s)
✔ [8/9] Built Solution (1.3s)
Build completed successfully (9 jobs).

$ lake build Challenge
⚠ [3/4] Replayed Challenge
warning: Challenge.lean:37:8: declaration uses `sorry`
warning: Challenge.lean:61:8: declaration uses `sorry`
warning: Challenge.lean:82:8: declaration uses `sorry`
warning: Challenge.lean:100:8: declaration uses `sorry`
warning: Challenge.lean:124:8: declaration uses `sorry`
warning: Challenge.lean:139:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide`/`lemma` anywhere in `Paley32Mxfp4/`, `Paley32Mxfp4.lean`, or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'Paley32Mxfp4Challenge.universal_orthogonal_k_sparse_papr_lower_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Paley32Mxfp4Challenge.paley32_orthogonality_and_zero_k4_collapse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Paley32Mxfp4Challenge.paley32_vs_sylvester32_k8_l4_reduction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Paley32Mxfp4Challenge.hall16_five_classes_orthogonality_and_k4_k8_duality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Paley32Mxfp4Challenge.bent_diagonal_n16_anti_resonance_exact' depends on axioms: [propext, Quot.sound]
'Paley32Mxfp4Challenge.mxfp4_e8m0_bulk_crush_threshold_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.
