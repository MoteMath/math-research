# Formal Verification Audit (`rhop-compressor-carry-confluence`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built RhopCompressorCarryConfluence.Defs (21s)
✔ [3/7] Built RhopCompressorCarryConfluence.Theorems (12s)
✔ [4/7] Built RhopCompressorCarryConfluence (2.4s)
✔ [6/7] Built Solution (2.4s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.3s)
warning: Challenge.lean:16:8: declaration uses `sorry`
warning: Challenge.lean:21:8: declaration uses `sorry`
warning: Challenge.lean:26:8: declaration uses `sorry`
warning: Challenge.lean:30:8: declaration uses `sorry`
warning: Challenge.lean:34:8: declaration uses `sorry`
warning: Challenge.lean:39:8: declaration uses `sorry`
warning: Challenge.lean:45:8: declaration uses `sorry`
warning: Challenge.lean:55:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the 8 intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `RhopCompressorCarryConfluence/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'RhopCompressorCarryConfluenceChallenge.carry_free_capacity_dichotomy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'RhopCompressorCarryConfluenceChallenge.rhop_capacity_dichotomy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'RhopCompressorCarryConfluenceChallenge.no_carry_free_6_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RhopCompressorCarryConfluenceChallenge.no_3hop_18_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RhopCompressorCarryConfluenceChallenge.cell42_bijection_right' depends on axioms: [propext, Quot.sound]
'RhopCompressorCarryConfluenceChallenge.netW_popcount_carry_conservation' depends on axioms: [propext, Quot.sound]
'RhopCompressorCarryConfluenceChallenge.confluence_csa_3state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'RhopCompressorCarryConfluenceChallenge.transducer_state_minimality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every headline theorem depends only on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true`.
