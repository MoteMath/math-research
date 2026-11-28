# Verification Audit — `f2-bilinear-hadamard-determinants`

- **Toolchain:** `leanprover/lean4:v4.34.1` + Mathlib `v4.34.1`
- **Date:** `2026-11-28`
- **Source Discovery:** Hour 8 Grand Finale of the 8-hour pure-silicon GPU hunt (`alien-silicon-hunt-20261128`, Track A `nim_sign_pop_0`, score 125, `NO_EXACT_OEIS_MATCH`, AMD RX 7900 XTX `gfx1100`, `0` FP32/FP64 ISA ops, `0` VGPR spills, bit-identical CPU verification).

## Build & Axiom Receipts

### `lake build`
```text
✔ [3093/3094] Built Solution (22s)
Build completed successfully (3094 jobs).
```
Zero errors, zero warnings, zero `sorry`, zero `native_decide`.

### `lake build Challenge`
```text
⚠ [1550/1551] Built Challenge (10s)
warning: Challenge.lean:8:8: declaration uses `sorry`
warning: Challenge.lean:21:8: declaration uses `sorry`
warning: Challenge.lean:40:8: declaration uses `sorry`
warning: Challenge.lean:54:8: declaration uses `sorry`
warning: Challenge.lean:69:8: declaration uses `sorry`
warning: Challenge.lean:77:8: declaration uses `sorry`
warning: Challenge.lean:87:8: declaration uses `sorry`
warning: Challenge.lean:100:8: declaration uses `sorry`
warning: Challenge.lean:116:8: declaration uses `sorry`
Build completed successfully (1551 jobs).
```

### `lake env lean PrintAxioms.lean`
```text
'F2BilinearHadamard.f2Bilin_xor_left_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'F2BilinearHadamard.bilinCharMat_det_block_elimination' depends on axioms: [propext, Classical.choice, Quot.sound]
'F2BilinearHadamard.walshCharMat_det_symmetric' depends on axioms: [propext, Classical.choice, Quot.sound]
'F2BilinearHadamard.bilinCharMat_det_symmetric' depends on axioms: [propext, Classical.choice, Quot.sound]
'F2BilinearHadamard.walshStandard_det' depends on axioms: [propext, Classical.choice, Quot.sound]
'F2BilinearHadamard.sierpinskiBitMat_cholesky_pivots' depends on axioms: [propext, Classical.choice, Quot.sound]
'F2BilinearHadamard.sierpinskiCharMat_det_all_n' depends on axioms: [propext, Classical.choice, Quot.sound]
'F2BilinearHadamard.nimCharMat_det_256' depends on axioms: [propext, Classical.choice, Quot.sound]
'F2BilinearHadamard.clmulBitMat_rank_collapse' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Theorem-Signature Parity
All 9 theorems in `Challenge.lean` match `Solution.lean` byte-for-byte (`ALL_9_EXACT_MATCH`) and are registered in `comparator.json`.
