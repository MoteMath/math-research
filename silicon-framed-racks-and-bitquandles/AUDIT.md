# Verification Audit — `silicon-framed-racks-and-bitquandles`

- **Toolchain:** `leanprover/lean4:v4.34.1` (Pure `Init`, zero Mathlib dependencies)
- **Date:** `2026-11-28`
- **Source Discovery:** Hour 6 of the 8-hour pure-silicon GPU hunt (`alien-silicon-hunt-20261128`, Track B `track_b_alien_algebra.py`, AMD RX 7900 XTX `gfx1100`, `0` FP32/FP64 ISA ops, `0` VGPR spills, bit-identical CPU verification).

## Build & Axiom Receipts

### `lake build`
```text
✔ [3/4] Built Solution (4.9s)
Build completed successfully (4 jobs).
```
Zero errors, zero warnings, zero `sorry`, zero `native_decide`.

### `lake build Challenge`
```text
⚠ [3/4] Built Challenge (1.2s)
warning: Challenge.lean:9:8: declaration uses `sorry`
warning: Challenge.lean:22:8: declaration uses `sorry`
warning: Challenge.lean:30:8: declaration uses `sorry`
warning: Challenge.lean:43:8: declaration uses `sorry`
warning: Challenge.lean:51:8: declaration uses `sorry`
warning: Challenge.lean:60:8: declaration uses `sorry`
warning: Challenge.lean:67:8: declaration uses `sorry`
warning: Challenge.lean:78:8: declaration uses `sorry`
warning: Challenge.lean:91:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

### `lake env lean PrintAxioms.lean`
```text
'SiliconRacksQuandles.cosetRack_laws' depends on axioms: [propext, Classical.choice, Quot.sound]
'SiliconRacksQuandles.carryXorRack_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'SiliconRacksQuandles.carryXorRack_framed_laws' depends on axioms: [propext, Classical.choice, Quot.sound]
'SiliconRacksQuandles.coreXorRack_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'SiliconRacksQuandles.coreXorRack_involutive_framed_laws' depends on axioms: [propext, Classical.choice, Quot.sound]
'SiliconRacksQuandles.coreXorRack_nonAlexander' depends on axioms: [propext, Classical.choice, Quot.sound]
'SiliconRacksQuandles.conjBitQuandle_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'SiliconRacksQuandles.conjBitQuandle_bothSided_laws' depends on axioms: [propext, Classical.choice, Quot.sound]
'SiliconRacksQuandles.conjBitQuandle_nonInvolutive_nonAlexander' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## Theorem-Signature Parity & Non-Vacuity
All 9 theorems in `Challenge.lean` match `Solution.lean` byte-for-byte and are registered in `comparator.json`:
1. `SiliconRacksQuandles.cosetRack_laws` — universal coset-shift rack theorem on `BitVec w`.
2. `SiliconRacksQuandles.carryXorRack_eq` — exact piecewise shift reduction for all `k < w`.
3. `SiliconRacksQuandles.carryXorRack_framed_laws` — left-bijective, LSD, non-idempotent (`0 ⋆ 0 ≠ 0`), non-RSD framed-link rack for all `k + 1 < w`.
4. `SiliconRacksQuandles.coreXorRack_eq` — exact zero-borrow low-bit cancellation reduction for all `k < w`.
5. `SiliconRacksQuandles.coreXorRack_involutive_framed_laws` — involutive, LSD, non-idempotent framed-link rack for all `1 ≤ k < w`.
6. `SiliconRacksQuandles.coreXorRack_nonAlexander` — concrete non-Alexander witness on `BitVec 4`.
7. `SiliconRacksQuandles.conjBitQuandle_eq` — exact bit-pair shift reduction for all `k < w`.
8. `SiliconRacksQuandles.conjBitQuandle_bothSided_laws` — idempotent, left-bijective, LSD, AND RSD both-sided knot quandle for all `k + 1 < w`.
9. `SiliconRacksQuandles.conjBitQuandle_nonInvolutive_nonAlexander` — non-involutive for all `k + 2 < w` plus concrete `BitVec 3` non-involutive and non-Alexander witnesses.
