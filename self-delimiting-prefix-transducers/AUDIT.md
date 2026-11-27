# Formal Verification Audit (`self-delimiting-prefix-transducers`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [3/7] Built SelfDelimitingPrefixTransducers.Theorems (25s)
✔ [4/7] Built SelfDelimitingPrefixTransducers (2.5s)
✔ [6/7] Built Solution (3.1s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Replayed Challenge
warning: Challenge.lean:17:8: declaration uses `sorry`
warning: Challenge.lean:23:8: declaration uses `sorry`
warning: Challenge.lean:31:8: declaration uses `sorry`
warning: Challenge.lean:46:8: declaration uses `sorry`
warning: Challenge.lean:53:8: declaration uses `sorry`
warning: Challenge.lean:60:8: declaration uses `sorry`
warning: Challenge.lean:67:8: declaration uses `sorry`
warning: Challenge.lean:73:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `SelfDelimitingPrefixTransducers/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'SelfDelimitingPrefixTransducersChallenge.accepts_prefix_free' depends on axioms: [propext]
'SelfDelimitingPrefixTransducersChallenge.layer0_conservation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SelfDelimitingPrefixTransducersChallenge.order_type_omega_obstruction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SelfDelimitingPrefixTransducersChallenge.fibAut_kraft_conservation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SelfDelimitingPrefixTransducersChallenge.fibAut_zero_bias' depends on axioms: [propext, Classical.choice, Quot.sound]
'SelfDelimitingPrefixTransducersChallenge.fibAut_parity_duality_embedding' depends on axioms: [propext, Quot.sound]
'SelfDelimitingPrefixTransducersChallenge.runAut_bias_symmetric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SelfDelimitingPrefixTransducersChallenge.eliasLift_orderPreserving' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
