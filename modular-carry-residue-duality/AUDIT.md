# Formal Verification Audit (`modular-carry-residue-duality`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built ModularCarryResidueDuality.Defs (7.1s)
✔ [3/7] Built ModularCarryResidueDuality.Theorems (18s)
✔ [4/7] Built ModularCarryResidueDuality (2.6s)
✔ [6/7] Built Solution (2.3s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.0s)
warning: Challenge.lean:15:8: declaration uses `sorry`
warning: Challenge.lean:20:8: declaration uses `sorry`
warning: Challenge.lean:27:8: declaration uses `sorry`
warning: Challenge.lean:33:8: declaration uses `sorry`
warning: Challenge.lean:40:8: declaration uses `sorry`
warning: Challenge.lean:48:8: declaration uses `sorry`
warning: Challenge.lean:54:8: declaration uses `sorry`
warning: Challenge.lean:59:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the eight intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `ModularCarryResidueDuality/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'ModularCarryResidueDualityChallenge.master_dual_carry_residue_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ModularCarryResidueDualityChallenge.synchronized_trace_divisibility_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ModularCarryResidueDualityChallenge.carry_complementarity_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ModularCarryResidueDualityChallenge.mersenne_dual_invariant_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ModularCarryResidueDualityChallenge.mersenne_divisibility_threshold_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ModularCarryResidueDualityChallenge.mersenne_reciprocal_popcount_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ModularCarryResidueDualityChallenge.negacyclic_reciprocal_popcount_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ModularCarryResidueDualityChallenge.fermat_reciprocal_popcount_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All eight headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true`. No `sorryAx` and no `Lean.ofReduceBool` (`native_decide`) appears.

## Exact Replay

`python scripts/explore_and_verify.py` exits 0 (exact Python integers, zero floats): it replays every law and the sharpness counterexamples (`t * d = 2` exceptions, Mersenne `t = 1, 2`, non-negacyclic `m = 7, 23`, non-period width, even modulus).
