# Formal Verification Audit (`deltanet-householder-e8`)

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
✔ [2/11] Built DeltaNetHouseholderE8.Defs (1.6s)
✔ [3/11] Built DeltaNetHouseholderE8.RatOrder (1.8s)
✔ [4/11] Built DeltaNetHouseholderE8.HouseholderSpectral (7.3s)
✔ [5/11] Built DeltaNetHouseholderE8.WyTriangular (7.3s)
✔ [6/11] Built DeltaNetHouseholderE8.WeylE8Closure (7.4s)
✔ [7/11] Built DeltaNetHouseholderE8.QuantizedTwoUlp (2.5s)
✔ [8/11] Built DeltaNetHouseholderE8 (1.1s)
✔ [10/11] Built Solution (1.3s)
Build completed successfully (11 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.4s)
warning: Challenge.lean:28:8: declaration uses `sorry`
warning: Challenge.lean:51:8: declaration uses `sorry`
warning: Challenge.lean:78:8: declaration uses `sorry`
warning: Challenge.lean:104:8: declaration uses `sorry`
warning: Challenge.lean:124:8: declaration uses `sorry`
warning: Challenge.lean:145:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide`/`lemma` anywhere in `DeltaNetHouseholderE8/`, `DeltaNetHouseholderE8.lean`, or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'DeltaNetHouseholderE8Challenge.householder_spectral_stability_iff_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DeltaNetHouseholderE8Challenge.quantized_unit_norm_supremum_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DeltaNetHouseholderE8Challenge.universal_two_ulp_safe_ceiling_theorem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DeltaNetHouseholderE8Challenge.wy_triangular_inverse_norm_growth_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DeltaNetHouseholderE8Challenge.d8_and_e8_weyl_root_zero_ulp_orthogonality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DeltaNetHouseholderE8Challenge.non_weyl_hamming_closure_obstruction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.
