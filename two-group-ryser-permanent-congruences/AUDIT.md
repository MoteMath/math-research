# Formal Verification Audit (`two-group-ryser-permanent-congruences`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.0s)
warning: Challenge.lean:17:8: declaration uses `sorry`
warning: Challenge.lean:23:8: declaration uses `sorry`
warning: Challenge.lean:30:8: declaration uses `sorry`
warning: Challenge.lean:36:8: declaration uses `sorry`
warning: Challenge.lean:43:8: declaration uses `sorry`
warning: Challenge.lean:52:8: declaration uses `sorry`
warning: Challenge.lean:59:8: declaration uses `sorry`
warning: Challenge.lean:65:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `TwoGroupRyserPermanentCongruences/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'TwoGroupRyserPermanentCongruencesChallenge.perm_eq_ryserSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoGroupRyserPermanentCongruencesChallenge.perm_mod_two_pow_succ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TwoGroupRyserPermanentCongruencesChallenge.xorCirc_perm_mod_two_pow_succ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TwoGroupRyserPermanentCongruencesChallenge.xorCirc_even_rowSum_dvd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TwoGroupRyserPermanentCongruencesChallenge.xorCirc_odd_mod_two_pow_add_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TwoGroupRyserPermanentCongruencesChallenge.hypercubeAdj_odd_mod' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TwoGroupRyserPermanentCongruencesChallenge.hypercubeAdj_even_dvd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TwoGroupRyserPermanentCongruencesChallenge.hypercubeMatching_even_dvd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
