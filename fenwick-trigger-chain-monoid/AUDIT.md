# Formal Verification Audit (`fenwick-trigger-chain-monoid`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.9s)
warning: Challenge.lean:17:8: declaration uses `sorry`
warning: Challenge.lean:23:8: declaration uses `sorry`
warning: Challenge.lean:30:8: declaration uses `sorry`
warning: Challenge.lean:36:8: declaration uses `sorry`
warning: Challenge.lean:47:8: declaration uses `sorry`
warning: Challenge.lean:54:8: declaration uses `sorry`
warning: Challenge.lean:64:8: declaration uses `sorry`
warning: Challenge.lean:71:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `FenwickTriggerChainMonoid/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'FenwickTriggerChainMonoidChallenge.evalWord_mod_eq_compile' depends on axioms: [propext, Classical.choice, Quot.sound]
'FenwickTriggerChainMonoidChallenge.compileTC_minimal' depends on axioms: [propext, Classical.choice, Quot.sound]
'FenwickTriggerChainMonoidChallenge.fenwick_free_monoid' depends on axioms: [propext, Classical.choice, Quot.sound]
'FenwickTriggerChainMonoidChallenge.fenwick_finite_monoid_card' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'FenwickTriggerChainMonoidChallenge.evalWord_D_spine' depends on axioms: [propext, Classical.choice, Quot.sound]
'FenwickTriggerChainMonoidChallenge.evalWord_U_spine' depends on axioms: [propext, Classical.choice, Quot.sound]
'FenwickTriggerChainMonoidChallenge.evalWord_twos_complement_duality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'FenwickTriggerChainMonoidChallenge.fenwick_depth_duality' depends on axioms: [propext, Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
