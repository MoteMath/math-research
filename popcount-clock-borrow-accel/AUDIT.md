# Formal Verification Audit (`popcount-clock-borrow-accel`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built PopcountClockBorrowAccel.Defs (6.1s)
✔ [3/7] Built PopcountClockBorrowAccel.Theorems (31s)
✔ [4/7] Built PopcountClockBorrowAccel (2.0s)
✔ [6/7] Built Solution (2.2s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.1s)
warning: Challenge.lean:18:8: declaration uses `sorry`
warning: Challenge.lean:22:8: declaration uses `sorry`
warning: Challenge.lean:28:8: declaration uses `sorry`
warning: Challenge.lean:33:8: declaration uses `sorry`
warning: Challenge.lean:40:8: declaration uses `sorry`
warning: Challenge.lean:46:8: declaration uses `sorry`
warning: Challenge.lean:53:8: declaration uses `sorry`
warning: Challenge.lean:60:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Exit codes: `lake build` = 0, `lake build Challenge` = 0. Zero errors, zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in the library modules or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'PopcountClockBorrowAccelChallenge.T_xor_unit_clock' depends on axioms: [propext, Classical.choice, Quot.sound]
'PopcountClockBorrowAccelChallenge.T_xor_hits_mersenne_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'PopcountClockBorrowAccelChallenge.T_xor_sync_collision_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'PopcountClockBorrowAccelChallenge.T_sub_borrow_acceleration' depends on axioms: [propext, Classical.choice, Quot.sound]
'PopcountClockBorrowAccelChallenge.T_sub_hits_mersenne_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'PopcountClockBorrowAccelChallenge.F_xor_wrap_unique_2w_cycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'PopcountClockBorrowAccelChallenge.F_sub_wrap_unique_cycle' depends on axioms: [propext, Classical.choice, Quot.sound]
'PopcountClockBorrowAccelChallenge.complement_carry_borrow_conjugacy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Exit code: 0. Every headline theorem depends only on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true`.
