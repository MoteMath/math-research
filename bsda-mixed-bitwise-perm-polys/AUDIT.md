# Formal Verification Audit (`bsda-mixed-bitwise-perm-polys`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [3/7] Built BsdaMixedBitwisePermPolys.Theorems (69s)
✔ [4/7] Built BsdaMixedBitwisePermPolys (1.7s)
✔ [6/7] Built Solution (1.8s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Replayed Challenge
warning: Challenge.lean:19:8: declaration uses `sorry`
warning: Challenge.lean:30:8: declaration uses `sorry`
warning: Challenge.lean:38:8: declaration uses `sorry`
warning: Challenge.lean:49:8: declaration uses `sorry`
warning: Challenge.lean:56:8: declaration uses `sorry`
warning: Challenge.lean:65:8: declaration uses `sorry`
warning: Challenge.lean:72:8: declaration uses `sorry`
warning: Challenge.lean:81:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the 8 intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `BsdaMixedBitwisePermPolys/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'BsdaMixedBitwisePermPolysChallenge.bijective_iff_forall_bitDeriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BsdaMixedBitwisePermPolysChallenge.bsda_bijective_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'BsdaMixedBitwisePermPolysChallenge.bsda_finite_slice_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'BsdaMixedBitwisePermPolysChallenge.maskedPoly_bijective_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'BsdaMixedBitwisePermPolysChallenge.rivest_classical_mod4_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BsdaMixedBitwisePermPolysChallenge.carryPair_bijective_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'BsdaMixedBitwisePermPolysChallenge.addXorCancel_bijective_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BsdaMixedBitwisePermPolysChallenge.klimovShamir_general_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every headline theorem depends exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true` (no `sorryAx`, no `Lean.ofReduceBool`).
