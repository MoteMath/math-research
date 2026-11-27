# Formal Verification Audit (`bit-slice-hankel-difference-ldu`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Replayed Challenge
warning: Challenge.lean:17:8: declaration uses `sorry`
warning: Challenge.lean:24:8: declaration uses `sorry`
warning: Challenge.lean:36:8: declaration uses `sorry`
warning: Challenge.lean:43:8: declaration uses `sorry`
warning: Challenge.lean:50:8: declaration uses `sorry`
warning: Challenge.lean:56:8: declaration uses `sorry`
warning: Challenge.lean:62:8: declaration uses `sorry`
warning: Challenge.lean:70:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `BitSliceHankelDifferenceLdu/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'BitSliceHankelDifferenceLduChallenge.hankel_affine_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'BitSliceHankelDifferenceLduChallenge.ecSeq_odd_master_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitSliceHankelDifferenceLduChallenge.ecSeq_odd_mod8_periodic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitSliceHankelDifferenceLduChallenge.ecSeq_odd_nonsingular' depends on axioms: [propext, Classical.choice, Quot.sound]
'BitSliceHankelDifferenceLduChallenge.ruler_family_odd_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'BitSliceHankelDifferenceLduChallenge.ruler_family_even_signed_square' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitSliceHankelDifferenceLduChallenge.signed_ruler_v2_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'BitSliceHankelDifferenceLduChallenge.popPow_hankel_factorization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
