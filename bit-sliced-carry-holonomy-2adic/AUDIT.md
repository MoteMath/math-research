# Formal Verification Audit (`bit-sliced-carry-holonomy-2adic`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built BitSlicedCarryHolonomy2adic.Defs (2.2s)
✔ [3/7] Built BitSlicedCarryHolonomy2adic.Theorems (19s)
✔ [4/7] Built BitSlicedCarryHolonomy2adic (1.8s)
✔ [6/7] Built Solution (1.9s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.1s)
warning: Challenge.lean:8:8: declaration uses `sorry`
warning: Challenge.lean:13:8: declaration uses `sorry`
warning: Challenge.lean:28:8: declaration uses `sorry`
warning: Challenge.lean:39:8: declaration uses `sorry`
warning: Challenge.lean:44:8: declaration uses `sorry`
warning: Challenge.lean:49:8: declaration uses `sorry`
warning: Challenge.lean:55:8: declaration uses `sorry`
warning: Challenge.lean:60:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `BitSlicedCarryHolonomy2adic/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'BitSlicedCarryHolonomy2adicChallenge.iter_testBit_eq_holonomy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitSlicedCarryHolonomy2adicChallenge.majority_carry_holonomy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitSlicedCarryHolonomy2adicChallenge.tower_to_min_period' depends on axioms: [propext, Classical.choice, Quot.sound]
'BitSlicedCarryHolonomy2adicChallenge.grayCarry_ge2_odd_period' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitSlicedCarryHolonomy2adicChallenge.quadAnd_v2' depends on axioms: [propext, Classical.choice, Quot.sound]
'BitSlicedCarryHolonomy2adicChallenge.affineXor_even_v2' depends on axioms: [propext, Classical.choice, Quot.sound]
'BitSlicedCarryHolonomy2adicChallenge.sharpness_affineXor_A0_period2' depends on axioms: [propext, Quot.sound]
'BitSlicedCarryHolonomy2adicChallenge.sharpness_carryless_gray_period_collapse' depends on axioms: [propext, Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
