# Formal Verification Audit (`kahan-neumaier-fp8-bounds`)

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
✔ [2/11] Built KahanNeumaierFp8.Defs (1.5s)
✔ [3/11] Built KahanNeumaierFp8.XorVdcSr (4.3s)
✔ [4/11] Built KahanNeumaierFp8.RneFreeze (4.4s)
✔ [5/11] Built KahanNeumaierFp8.KulischInt32 (3.4s)
✔ [6/11] Built KahanNeumaierFp8.KahanNeumaier (3.5s)
✔ [7/11] Built KahanNeumaierFp8.BlockAccum (1.1s)
✔ [8/11] Built KahanNeumaierFp8 (904ms)
✔ [10/11] Built Solution (1.1s)
Build completed successfully (11 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.1s)
warning: Challenge.lean:34:8: declaration uses `sorry`
warning: Challenge.lean:59:8: declaration uses `sorry`
warning: Challenge.lean:80:8: declaration uses `sorry`
warning: Challenge.lean:99:8: declaration uses `sorry`
warning: Challenge.lean:126:8: declaration uses `sorry`
warning: Challenge.lean:152:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide`/`lemma` anywhere in `KahanNeumaierFp8/`, `KahanNeumaierFp8.lean`, or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'KahanNeumaierFp8Challenge.microbatch_rne_freeze_threshold_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KahanNeumaierFp8Challenge.kahan_late_dipole_spike_total_erasure_vs_neumaier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KahanNeumaierFp8Challenge.neumaier_self_swamping_ceiling_beats_by_kahan' depends on axioms: [propext, Quot.sound]
'KahanNeumaierFp8Challenge.fp8_e4m3fn_kulisch_int32_9362_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KahanNeumaierFp8Challenge.microbatch_xor_vdc_sr_zero_bias_and_stratification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KahanNeumaierFp8Challenge.shared_exponent_int32_block_accum_associativity' depends on axioms: [propext, Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.
