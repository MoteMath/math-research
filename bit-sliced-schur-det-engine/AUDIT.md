# Formal Verification Audit (`bit-sliced-schur-det-engine`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built BitSlicedSchurDetEngine.Defs (14s)
✔ [3/7] Built BitSlicedSchurDetEngine.Theorems (9.1s)
✔ [4/7] Built BitSlicedSchurDetEngine (1.5s)
✔ [6/7] Built Solution (2.4s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.8s)
warning: Challenge.lean:8:8: declaration uses `sorry`
warning: Challenge.lean:12:8: declaration uses `sorry`
warning: Challenge.lean:18:8: declaration uses `sorry`
warning: Challenge.lean:25:8: declaration uses `sorry`
warning: Challenge.lean:37:8: declaration uses `sorry`
warning: Challenge.lean:44:8: declaration uses `sorry`
warning: Challenge.lean:50:8: declaration uses `sorry`
warning: Challenge.lean:62:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `BitSlicedSchurDetEngine/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'BitSlicedSchurDetEngineChallenge.det_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'BitSlicedSchurDetEngineChallenge.det_block_schur_left_unimodular' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitSlicedSchurDetEngineChallenge.det_block_schur_right_scaled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitSlicedSchurDetEngineChallenge.det_bitSliced_schur_zero_iff' depends on axioms: [propext, Quot.sound]
'BitSlicedSchurDetEngineChallenge.det_msbAnd_closed_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'BitSlicedSchurDetEngineChallenge.det_subsetDisjMat_closed_form' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitSlicedSchurDetEngineChallenge.witness_zmod6_zero_divisors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitSlicedSchurDetEngineChallenge.counterexample_bool_plus_superset_breaks' depends on axioms: [propext]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
