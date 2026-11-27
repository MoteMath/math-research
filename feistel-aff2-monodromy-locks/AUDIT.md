# Formal Verification Audit (`feistel-aff2-monodromy-locks`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built FeistelAff2MonodromyLocks.Defs (1.8s)
✔ [3/7] Built FeistelAff2MonodromyLocks.Theorems (24s)
✔ [4/7] Built FeistelAff2MonodromyLocks (1.6s)
✔ [6/7] Built Solution (1.7s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.6s)
warning: Challenge.lean:20:8: declaration uses `sorry`
warning: Challenge.lean:30:8: declaration uses `sorry`
warning: Challenge.lean:40:8: declaration uses `sorry`
warning: Challenge.lean:50:8: declaration uses `sorry`
warning: Challenge.lean:65:8: declaration uses `sorry`
warning: Challenge.lean:81:8: declaration uses `sorry`
warning: Challenge.lean:91:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the 7 intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `FeistelAff2MonodromyLocks/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'FeistelAff2MonodromyLocksChallenge.feistel_universal_2_3_period' depends on axioms: [propext, Quot.sound]
'FeistelAff2MonodromyLocksChallenge.theorem_I_universal_period12_lock' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'FeistelAff2MonodromyLocksChallenge.theorem_IIa_add_one_period6_lock' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'FeistelAff2MonodromyLocksChallenge.theorem_IIb_sub_one_exponential_escape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'FeistelAff2MonodromyLocksChallenge.theorem_IIIa_lsb_binomial_spectrum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'FeistelAff2MonodromyLocksChallenge.theorem_IIIb_ctz_period_lock' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'FeistelAff2MonodromyLocksChallenge.theorem_IV_universal_isoperiodic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every headline theorem depends exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true` (no `sorryAx`, no `Lean.ofReduceBool`).
