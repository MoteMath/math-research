# Verification Audit (`silicon-bitrev-ld-and-quandles`)

- **Toolchain:** `leanprover/lean4:v4.34.1` (pure-Init, zero external dependencies)
- **Build:** `lake build` (`0` errors, `0` warnings, `0` `sorry` outside `Challenge.lean`)
- **Custom axioms / `native_decide` / `unsafe`:** `0`
- **Comparator config:** `comparator.json` pins all 7 definitions in `Defs.lean` and all 10 theorems in `Challenge.lean` with `enable_nanoda: true` and `permitted_axioms: ["propext", "Classical.choice", "Quot.sound"]`.

## Verbatim `#print axioms` Output

```text
'SiliconLDQuandles.partialInvLD_idemp' depends on axioms: [propext, Quot.sound]
'SiliconLDQuandles.partialInvLD_left_distrib' depends on axioms: [propext, Quot.sound]
'SiliconLDQuandles.partialInvLD_flexible' depends on axioms: [propext, Quot.sound]
'SiliconLDQuandles.partialInvLD_non_assoc_non_comm' depends on axioms: [propext]
'SiliconLDQuandles.bitrevShiftOp_eq_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'SiliconLDQuandles.bitrevShiftOp_ld_laws' depends on axioms: [propext, Classical.choice, Quot.sound]
'SiliconLDQuandles.cosetJump_quandle_laws' depends on axioms: [propext, Classical.choice, Quot.sound]
'SiliconLDQuandles.xorCarryOp_eq_and_not' depends on axioms: [propext, Classical.choice, Quot.sound]
'SiliconLDQuandles.xorCarryQuandle_twoBitMask' depends on axioms: [propext, Classical.choice, Quot.sound]
'SiliconLDQuandles.xorCarryQuandle_nonAlexander_nonInvolutive' depends on axioms: [propext, Classical.choice, Quot.sound]
```
