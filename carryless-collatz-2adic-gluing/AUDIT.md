# Formal Verification Audit (`carryless-collatz-2adic-gluing`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [6/7] Built Solution (2.1s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.7s)
warning: Challenge.lean:19:8: declaration uses `sorry`
warning: Challenge.lean:34:8: declaration uses `sorry`
warning: Challenge.lean:42:8: declaration uses `sorry`
warning: Challenge.lean:59:8: declaration uses `sorry`
warning: Challenge.lean:74:8: declaration uses `sorry`
warning: Challenge.lean:80:8: declaration uses `sorry`
warning: Challenge.lean:85:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the 7 intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `CarrylessCollatz2adicGluing/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'CarrylessCollatz2adicGluingChallenge.Syracuse_conjugacy' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarrylessCollatz2adicGluingChallenge.checkAffTable_iff_shiftFaithful' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarrylessCollatz2adicGluingChallenge.carried_carryless_3x1_syracuse_conjugate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarrylessCollatz2adicGluingChallenge.carryless_selfCoding_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarrylessCollatz2adicGluingChallenge.carried_mod4_eq1_collapse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarrylessCollatz2adicGluingChallenge.carryless_3x1_unique_nonzero_cycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarrylessCollatz2adicGluingChallenge.periodic_orbit_classification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every headline theorem depends exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true` (no `sorryAx`, no `Lean.ofReduceBool`).
