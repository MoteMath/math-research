# Formal Verification Audit (`skew-thue-morse-pfaffian`)

**Toolchain:** `leanprover/lean4:v4.34.1` with Mathlib `v4.34.1`  
**Audit date:** 2026-11-25

## Build & Challenge Checks

```text
$ lake build
✔ [3093/3097] Built SkewThueMorsePfaffian.Theorems (24s)
✔ [3094/3097] Built SkewThueMorsePfaffian (17s)
✔ [3096/3097] Built Solution (16s)
Build completed successfully (3097 jobs).

$ lake build Challenge
⚠ [1550/1551] Replayed Challenge
warning: Challenge.lean:21:8: declaration uses `sorry`
warning: Challenge.lean:27:8: declaration uses `sorry`
warning: Challenge.lean:33:8: declaration uses `sorry`
warning: Challenge.lean:39:8: declaration uses `sorry`
Build completed successfully (1551 jobs).
```

Zero errors, zero warnings outside the four intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `SkewThueMorsePfaffian/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'SkewThueMorseChallenge.det_skewThueMorse_even' depends on axioms: [propext, Classical.choice, Quot.sound]
'SkewThueMorseChallenge.det_skewThueMorse_shift1_even' depends on axioms: [propext, Classical.choice, Quot.sound]
'SkewThueMorseChallenge.det_skewThueMorse_shift2_even' depends on axioms: [propext, Classical.choice, Quot.sound]
'SkewThueMorseChallenge.det_skewThueMorse_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All four headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Quot.sound`, and `Classical.choice`), matching `comparator.json` with `enable_nanoda: true`.
