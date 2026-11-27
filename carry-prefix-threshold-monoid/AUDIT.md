# Formal Verification Audit (`carry-prefix-threshold-monoid`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built CarryPrefixThresholdMonoid.Defs (3.2s)
✔ [3/7] Built CarryPrefixThresholdMonoid.Theorems (17s)
✔ [4/7] Built CarryPrefixThresholdMonoid (2.4s)
✔ [6/7] Built Solution (3.4s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (3.2s)
warning: Challenge.lean:17:8: declaration uses `sorry`
warning: Challenge.lean:25:8: declaration uses `sorry`
warning: Challenge.lean:33:8: declaration uses `sorry`
warning: Challenge.lean:38:8: declaration uses `sorry`
warning: Challenge.lean:44:8: declaration uses `sorry`
warning: Challenge.lean:50:8: declaration uses `sorry`
warning: Challenge.lean:57:8: declaration uses `sorry`
warning: Challenge.lean:63:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `CarryPrefixThresholdMonoid/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'CarryPrefixThresholdMonoidChallenge.collapse_tree_universality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarryPrefixThresholdMonoidChallenge.collapse_sharpness_obstruction' depends on axioms: [propext, Quot.sound]
'CarryPrefixThresholdMonoidChallenge.aperiodic' depends on axioms: [propext, Quot.sound]
'CarryPrefixThresholdMonoidChallenge.enumBounded_length' depends on axioms: [propext, Quot.sound]
'CarryPrefixThresholdMonoidChallenge.tree_exact_carry_absorption' depends on axioms: [propext, Quot.sound]
'CarryPrefixThresholdMonoidChallenge.three_input_exact_absorption' depends on axioms: [propext, Quot.sound]
'CarryPrefixThresholdMonoidChallenge.three_input_resonant_triple_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarryPrefixThresholdMonoidChallenge.odd_modulus_never_absorbs' depends on axioms: [propext, Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
