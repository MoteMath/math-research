# Formal Verification Audit (`vcache-ipr-xorvdc-bounds`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **10 / 10** | **9 / 10** | **10 / 10** | **10 / 10** | **95 / 100** |

*Weighted composite: `3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 3*9 + 2*10 + 2*9 + 2*10 + 10 = 95 / 100`. See [`README.md`](README.md) for the full For Mathematicians, For Non-Mathematicians, and Prior-Art Context sections.*

## Build & Challenge Checks

Clean build + `Challenge` check + `#print axioms` total wall time: **`28.46 s`** (`< 40 s` budget).

```text
$ lake clean && lake build
✔ [2/11] Built VcacheIprXorvdc.Defs (1.0s)
✔ [3/11] Built VcacheIprXorvdc.RatHelpers (3.2s)
✔ [4/11] Built VcacheIprXorvdc.XorVdcStratified (4.4s)
✔ [5/11] Built VcacheIprXorvdc.PackingInt64Bounds (4.4s)
✔ [6/11] Built VcacheIprXorvdc.IprPhaseTransition (4.4s)
✔ [7/11] Built VcacheIprXorvdc.Rank1SinkWht (5.8s)
✔ [8/11] Built VcacheIprXorvdc (2.8s)
✔ [10/11] Built Solution (2.5s)
Build completed successfully (11 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (3.0s)
warning: Challenge.lean:42:8: declaration uses `sorry`
warning: Challenge.lean:79:8: declaration uses `sorry`
warning: Challenge.lean:117:8: declaration uses `sorry`
warning: Challenge.lean:149:8: declaration uses `sorry`
warning: Challenge.lean:174:8: declaration uses `sorry`
warning: Challenge.lean:196:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide`/`lemma` anywhere in `VcacheIprXorvdc/`, `VcacheIprXorvdc.lean`, or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'VcacheIprXorvdcChallenge.ipr_attention_averaging_sr_vs_rne_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'VcacheIprXorvdcChallenge.cross_format_int2_sr_beats_int4_mxfp4_rne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'VcacheIprXorvdcChallenge.xor_vdc_stratified_sr_superconvergence_and_iid_halving' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'VcacheIprXorvdcChallenge.rank1_attention_sink_ipr_crossover_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'VcacheIprXorvdcChallenge.rank1_split_wht_orthogonality_and_output_inversion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'VcacheIprXorvdcChallenge.sub4bit_vcache_packing_density_and_exact_int64_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.
