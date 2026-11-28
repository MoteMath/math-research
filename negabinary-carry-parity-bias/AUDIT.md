# Verification Audit — `negabinary-carry-parity-bias`

- **Toolchain:** `leanprover/lean4:v4.34.1` (Pure `Init`, zero Mathlib dependencies)
- **Date:** `2026-11-28`
- **Source Discovery:** Hour 7 of the 8-hour pure-silicon GPU hunt (`alien-silicon-hunt-20261128`, Track C `track_c_carry_twins.py`, AMD RX 7900 XTX `gfx1100`, `0` FP32/FP64 ISA ops, `0` VGPR spills, bit-identical CPU verification).

## Build & Axiom Receipts

### `lake build`
```text
✔ [3/4] Built Solution (7.3s)
Build completed successfully (4 jobs).
```
Zero errors, zero warnings, zero `sorry`, zero `native_decide`.

### `lake build Challenge`
```text
⚠ [3/4] Built Challenge (1.3s)
warning: Challenge.lean:9:8: declaration uses `sorry`
warning: Challenge.lean:25:8: declaration uses `sorry`
warning: Challenge.lean:37:8: declaration uses `sorry`
warning: Challenge.lean:50:8: declaration uses `sorry`
warning: Challenge.lean:58:8: declaration uses `sorry`
warning: Challenge.lean:65:8: declaration uses `sorry`
warning: Challenge.lean:74:8: declaration uses `sorry`
warning: Challenge.lean:89:8: declaration uses `sorry`
warning: Challenge.lean:101:8: declaration uses `sorry`
warning: Challenge.lean:114:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

### `lake env lean PrintAxioms.lean`
```text
'NegabinaryCarryParityBias.negabinParitySum_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'NegabinaryCarryParityBias.negabinParitySum_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NegabinaryCarryParityBias.negabinParitySum_spectral' depends on axioms: [propext, Classical.choice, Quot.sound]
'NegabinaryCarryParityBias.negabinBias_abs_le_one_third' depends on axioms: [propext, Classical.choice, Quot.sound]
'NegabinaryCarryParityBias.negabinBias_eq_pos_one_third_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'NegabinaryCarryParityBias.negabinBias_eq_neg_one_third_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'NegabinaryCarryParityBias.negabinZeroBias_bounded_family' depends on axioms: [propext, Classical.choice, Quot.sound]
'NegabinaryCarryParityBias.base2ParitySum_spectral' depends on axioms: [propext, Classical.choice, Quot.sound]
'NegabinaryCarryParityBias.base2Bias_asymmetric_barrier' depends on axioms: [propext, Classical.choice, Quot.sound]
'NegabinaryCarryParityBias.base2Bias_eq_pos_one_third_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Theorem-Signature Parity
All 10 theorems in `Challenge.lean` match `Solution.lean` byte-for-byte (`ALL_10_EXACT_MATCH`) and are registered in `comparator.json`.
