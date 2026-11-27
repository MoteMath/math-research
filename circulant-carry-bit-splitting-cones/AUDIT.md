# Formal Verification Audit (`circulant-carry-bit-splitting-cones`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built CirculantCarryBitSplittingCones.Defs (12s)
✔ [3/7] Built CirculantCarryBitSplittingCones.Theorems (71s)
✔ [4/7] Built CirculantCarryBitSplittingCones (1.7s)
✔ [6/7] Built Solution (1.9s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (3.5s)
warning: Challenge.lean:8:8: declaration uses `sorry`
warning: Challenge.lean:23:8: declaration uses `sorry`
warning: Challenge.lean:29:8: declaration uses `sorry`
warning: Challenge.lean:37:8: declaration uses `sorry`
warning: Challenge.lean:43:8: declaration uses `sorry`
warning: Challenge.lean:50:8: declaration uses `sorry`
warning: Challenge.lean:56:8: declaration uses `sorry`
warning: Challenge.lean:61:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `CirculantCarryBitSplittingCones/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'CirculantCarryBitSplittingConesChallenge.hermitian_row0_telescope_symm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CirculantCarryBitSplittingConesChallenge.mersenne_mod3_recurrence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CirculantCarryBitSplittingConesChallenge.mersenne_mod6_dominance_breaks_at_2_pow_72' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CirculantCarryBitSplittingConesChallenge.mersenne_palindromy_naive_involutions_fail' does not depend on any axioms
'CirculantCarryBitSplittingConesChallenge.or_mul5_strict_evil_dominance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CirculantCarryBitSplittingConesChallenge.mul3_newman_benchmark' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CirculantCarryBitSplittingConesChallenge.hostile_mutation_U0_rejected' depends on axioms: [propext, Quot.sound]
'CirculantCarryBitSplittingConesChallenge.engineII_three_way_sharpness' depends on axioms: [propext]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
