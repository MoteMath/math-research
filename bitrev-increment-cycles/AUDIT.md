# Formal Verification Audit (`bitrev-increment-cycles`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib dependencies)  
**Audit date:** 2026-11-25

## Build & Challenge Checks

```text
$ lake build
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Replayed Challenge
warning: Challenge.lean:21:8: declaration uses `sorry`
warning: Challenge.lean:27:8: declaration uses `sorry`
warning: Challenge.lean:34:8: declaration uses `sorry`
warning: Challenge.lean:41:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the four intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `BitrevIncrementCycles/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'BitrevIncrementChallenge.bitrevInc_odd_single_cycle' depends on axioms: [propext, Classical.choice, Quot.sound]
'BitrevIncrementChallenge.bitrevInc_even_zero_period' depends on axioms: [propext, Quot.sound]
'BitrevIncrementChallenge.bitrevInc_single_cycle_iff_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'BitrevIncrementChallenge.bitrevInc_return_map' depends on axioms: [propext, Quot.sound]
```

All four headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Quot.sound`, and `Classical.choice`), matching `comparator.json` with `enable_nanoda: true`.
