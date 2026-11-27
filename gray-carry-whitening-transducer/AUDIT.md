# Formal Verification Audit (`gray-carry-whitening-transducer`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built GrayCarryWhiteningTransducer.Defs (2.6s)
✔ [3/7] Built GrayCarryWhiteningTransducer.Theorems (18s)
✔ [4/7] Built GrayCarryWhiteningTransducer (1.9s)
✔ [6/7] Built Solution (2.6s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.1s)
warning: Challenge.lean:17:8: declaration uses `sorry`
warning: Challenge.lean:24:8: declaration uses `sorry`
warning: Challenge.lean:31:8: declaration uses `sorry`
warning: Challenge.lean:38:8: declaration uses `sorry`
warning: Challenge.lean:48:8: declaration uses `sorry`
warning: Challenge.lean:54:8: declaration uses `sorry`
warning: Challenge.lean:62:8: declaration uses `sorry`
warning: Challenge.lean:69:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `GrayCarryWhiteningTransducer/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'GrayCarryWhiteningTransducerChallenge.gray_carry_whitening_binary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GrayCarryWhiteningTransducerChallenge.gray_carry_whitening_gray_coords' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GrayCarryWhiteningTransducerChallenge.gray_carry_full_fiber_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GrayCarryWhiteningTransducerChallenge.gray_joint_carry_borrow_fiber_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GrayCarryWhiteningTransducerChallenge.gray_carry_borrow_orthogonal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GrayCarryWhiteningTransducerChallenge.radix_carry_whitening_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GrayCarryWhiteningTransducerChallenge.k_operand_whitening_impossibility' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GrayCarryWhiteningTransducerChallenge.radix_carry_borrow_orthogonality_binary_unique' depends on axioms: [propext,
 Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
