# Verification & Audit Receipt (`clmul-carry-dynamics`)

- **Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib, zero external packages)
- **Palomar Comparator Manifest:** [`comparator.json`](comparator.json) (`enable_nanoda: true`, 10 pinned theorems, 12 pinned definitions)
- **Permitted Axioms:** `[propext, Classical.choice, Quot.sound]` (zero `sorry`, zero `native_decide`, zero custom axioms)

## Build Receipt

```text
> lake build
✔ [3/4] Built Solution (11s)
Build completed successfully (4 jobs).

> lake build Challenge
⚠ [3/4] Built Challenge (1.3s)
warning: Challenge.lean:6:8: declaration uses `sorry`
warning: Challenge.lean:11:8: declaration uses `sorry`
warning: Challenge.lean:19:8: declaration uses `sorry`
warning: Challenge.lean:26:8: declaration uses `sorry`
warning: Challenge.lean:34:8: declaration uses `sorry`
warning: Challenge.lean:43:8: declaration uses `sorry`
warning: Challenge.lean:51:8: declaration uses `sorry`
warning: Challenge.lean:58:8: declaration uses `sorry`
warning: Challenge.lean:64:8: declaration uses `sorry`
warning: Challenge.lean:71:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

## `#print axioms` Receipt (`lake env lean PrintAxioms.lean`)

```text
'ClmulCarryDynamics.clmul_xor' depends on axioms: [propext, Quot.sound]
'ClmulCarryDynamics.clmul_mod_injective_of_odd' depends on axioms: [propext, Quot.sound]
'ClmulCarryDynamics.hybrid_hull_dobell_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClmulCarryDynamics.kaprekarStep_add_one_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClmulCarryDynamics.kaprekarStep_image_char' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClmulCarryDynamics.kaprekarStep_universal_sink' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClmulCarryDynamics.kaprekarStep_w2_sharpness' depends on axioms: [propext, Quot.sound]
'ClmulCarryDynamics.carried_eq_clmul3_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClmulCarryDynamics.zeroCarry3Count_eq_fib' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClmulCarryDynamics.carried_clmul3_parity_sum' depends on axioms: [propext, Quot.sound]
```

## Provenance

All three theorem families originated from zero-floating-point bare-metal RDNA3 (`gfx1100`) GPU scans in `alien-silicon-hunt-20261128` (Track B `track_b_alien_algebra.hsaco` and Track C `track_c_carry_twins.hsaco`), were replayed bit-identically on CPU, and are unconditionally proved here for all bit-widths $w$ in Lean 4's kernel.
