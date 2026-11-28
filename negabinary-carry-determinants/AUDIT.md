# Verification Audit (`negabinary-carry-determinants`)

- **Toolchain:** `leanprover/lean4:v4.34.1` with Mathlib `v4.34.1`
- **Sorry count outside `Challenge.lean`:** `0`
- **Custom axioms / `native_decide` / `unsafe`:** `0`
- **Comparator config:** `comparator.json` pins all 9 challenge theorems in `NegabinaryCarryDetChallenge` with `enable_nanoda: true` and `permitted_axioms: ["propext", "Classical.choice", "Quot.sound"]`.

## Verbatim `#print axioms` Output

```text
'NegabinaryCarryDetChallenge.negAdd_popcount_conservation' depends on axioms: [propext, Classical.choice, Quot.sound]
'NegabinaryCarryDetChallenge.runPrefix_iff_bits' depends on axioms: [propext, Classical.choice, Quot.sound]
'NegabinaryCarryDetChallenge.negZeroPosCarryMat_eq_LDL' depends on axioms: [propext, Classical.choice, Quot.sound]
'NegabinaryCarryDetChallenge.det_negZeroPosCarryMat' depends on axioms: [propext, Classical.choice, Quot.sound]
'NegabinaryCarryDetChallenge.det_negZeroBorrowMat' depends on axioms: [propext, Classical.choice, Quot.sound]
'NegabinaryCarryDetChallenge.negZeroPosCarry_ne_disjointBit' depends on axioms: [propext]
'NegabinaryCarryDetChallenge.det_negParityMat_decouple' depends on axioms: [propext, Classical.choice, Quot.sound]
'NegabinaryCarryDetChallenge.det_negKMat_decouple' depends on axioms: [propext, Classical.choice, Quot.sound]
'NegabinaryCarryDetChallenge.negParityMat_n34_anomaly' depends on axioms: [propext, Classical.choice, Quot.sound]
```
