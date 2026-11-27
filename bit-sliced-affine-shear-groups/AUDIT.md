# Formal Verification Audit (`bit-sliced-affine-shear-groups`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built BitSlicedAffineShearGroups.Defs (5.1s)
✔ [3/7] Built BitSlicedAffineShearGroups.Theorems (55s)
✔ [4/7] Built BitSlicedAffineShearGroups (1.8s)
✔ [6/7] Built Solution (1.0s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.9s)
warning: Challenge.lean:20:8: declaration uses `sorry`
warning: Challenge.lean:29:8: declaration uses `sorry`
warning: Challenge.lean:36:8: declaration uses `sorry`
warning: Challenge.lean:42:8: declaration uses `sorry`
warning: Challenge.lean:49:8: declaration uses `sorry`
warning: Challenge.lean:55:8: declaration uses `sorry`
warning: Challenge.lean:59:8: declaration uses `sorry`
warning: Challenge.lean:69:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the 8 intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `BitSlicedAffineShearGroups/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'BitSlicedAffineShearGroupsChallenge.bsasce_master_order_bound' depends on axioms: [propext, Quot.sound]
'BitSlicedAffineShearGroupsChallenge.bsasce_derived_series_collapse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitSlicedAffineShearGroupsChallenge.theorem1_circuitE_exact_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitSlicedAffineShearGroupsChallenge.theorem2_circuitP_exact_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitSlicedAffineShearGroupsChallenge.theorem2_circuitFm_pairwise_non_conjugate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitSlicedAffineShearGroupsChallenge.theorem3_addXorShear_exact_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitSlicedAffineShearGroupsChallenge.theorem3_fiber1_wreath_normal_form' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitSlicedAffineShearGroupsChallenge.theorem4_circuitH_prime5_obstruction' depends on axioms: [propext, Quot.sound]
```

Every headline theorem depends exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true` (no `sorryAx`, no `Lean.ofReduceBool`).
