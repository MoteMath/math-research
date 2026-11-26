# Formal Verification Audit (`unsigned-fp4-softmax-v`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **10 / 10** | **10 / 10** | **10 / 10** | **95 / 100** |

*Weighted composite: `3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 95 / 100`. See [`README.md`](README.md) for the full For Mathematicians, For Non-Mathematicians, and Prior-Art Context sections.*

## Build & Challenge Checks

```text
$ lake build
✔ [6/10] Built UnsignedFp4SoftmaxV.SimplexDriftSr (32s)
✔ [7/10] Built UnsignedFp4SoftmaxV (1.8s)
✔ [9/10] Built Solution (2.4s)
Build completed successfully (10 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (5.4s)
warning: Challenge.lean:34:8: declaration uses `sorry`
warning: Challenge.lean:56:8: declaration uses `sorry`
warning: Challenge.lean:101:8: declaration uses `sorry`
warning: Challenge.lean:133:8: declaration uses `sorry`
warning: Challenge.lean:160:8: declaration uses `sorry`
warning: Challenge.lean:182:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide`/`lemma` anywhere in `UnsignedFp4SoftmaxV/`, `UnsignedFp4SoftmaxV.lean`, or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'UnsignedFp4SoftmaxVChallenge.unsigned_fp4_e1m3_collapse_to_uint4' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'UnsignedFp4SoftmaxVChallenge.unsigned_fp4_all_b_ef21_regime_classification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'UnsignedFp4SoftmaxVChallenge.softmax_simplex_rtn_drift_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'UnsignedFp4SoftmaxVChallenge.stratified_xor_vdc_simplex_zero_drift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'UnsignedFp4SoftmaxVChallenge.attention_v_centering_simplex_drift_annihilation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'UnsignedFp4SoftmaxVChallenge.raw_v_e2m1_level_collapse_vs_centered_invariance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.
