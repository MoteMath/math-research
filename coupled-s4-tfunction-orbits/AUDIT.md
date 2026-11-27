# Formal Verification Audit (`coupled-s4-tfunction-orbits`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.1s)
warning: Challenge.lean:17:8: declaration uses `sorry`
warning: Challenge.lean:26:8: declaration uses `sorry`
warning: Challenge.lean:32:8: declaration uses `sorry`
warning: Challenge.lean:42:8: declaration uses `sorry`
warning: Challenge.lean:50:8: declaration uses `sorry`
warning: Challenge.lean:56:8: declaration uses `sorry`
warning: Challenge.lean:66:8: declaration uses `sorry`
warning: Challenge.lean:74:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `CoupledS4TfunctionOrbits/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'CoupledS4TfunctionOrbitsChallenge.orbit_lift_exact_period' depends on axioms: [propext, Classical.choice, Quot.sound]
'CoupledS4TfunctionOrbitsChallenge.d4Elem_is_4cycle_iff' depends on axioms: [propext, Quot.sound]
'CoupledS4TfunctionOrbitsChallenge.full_period_of_D4_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
'CoupledS4TfunctionOrbitsChallenge.no_shear_never_full_period' depends on axioms: [propext, Quot.sound]
'CoupledS4TfunctionOrbitsChallenge.family1_full_period' depends on axioms: [propext, Classical.choice, Quot.sound]
'CoupledS4TfunctionOrbitsChallenge.ternPoly_exact_cycle_partition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CoupledS4TfunctionOrbitsChallenge.ternTwistY_exact_partition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CoupledS4TfunctionOrbitsChallenge.hybridTwoCycle_exact_two_cycles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
