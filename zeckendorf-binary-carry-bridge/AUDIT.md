# Formal Verification Audit (`zeckendorf-binary-carry-bridge`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built ZeckendorfBinaryCarryBridge.Defs (2.1s)
✔ [3/7] Built ZeckendorfBinaryCarryBridge.Theorems (41s)
✔ [4/7] Built ZeckendorfBinaryCarryBridge (1.7s)
✔ [6/7] Built Solution (1.9s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.9s)
warning: Challenge.lean:8:8: declaration uses `sorry`
warning: Challenge.lean:13:8: declaration uses `sorry`
warning: Challenge.lean:20:8: declaration uses `sorry`
warning: Challenge.lean:28:8: declaration uses `sorry`
warning: Challenge.lean:35:8: declaration uses `sorry`
warning: Challenge.lean:50:8: declaration uses `sorry`
warning: Challenge.lean:62:8: declaration uses `sorry`
warning: Challenge.lean:67:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `ZeckendorfBinaryCarryBridge/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'ZeckendorfBinaryCarryBridgeChallenge.popcount_add_carry' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeckendorfBinaryCarryBridgeChallenge.master_carry_bridge_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ZeckendorfBinaryCarryBridgeChallenge.not_diff_basis_refutation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ZeckendorfBinaryCarryBridgeChallenge.rbonacci_uniqueness' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeckendorfBinaryCarryBridgeChallenge.rbonacci_master_invariants' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ZeckendorfBinaryCarryBridgeChallenge.sparse_r6_diff_basis_infinite_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ZeckendorfBinaryCarryBridgeChallenge.witness_nonvacuity_sparse_r6' depends on axioms: [propext, Quot.sound]
'ZeckendorfBinaryCarryBridgeChallenge.sharpness_non_confluence_still_obeys_carry_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
