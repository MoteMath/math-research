# Formal Verification Audit (`sparse-e2m1-rotations`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Build & Challenge Checks

```text
$ lake build
✔ [4/8] Built SparseE2M1Rotations.Theorems (2.2s)
✔ [5/8] Built SparseE2M1Rotations (1.0s)
✔ [7/8] Built Solution (1.1s)
Build completed successfully (8 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.3s)
warning: Challenge.lean:25:8: declaration uses `sorry`
warning: Challenge.lean:40:8: declaration uses `sorry`
warning: Challenge.lean:51:8: declaration uses `sorry`
warning: Challenge.lean:65:8: declaration uses `sorry`
warning: Challenge.lean:76:8: declaration uses `sorry`
warning: Challenge.lean:84:8: declaration uses `sorry`
warning: Challenge.lean:93:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the seven intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `SparseE2M1Rotations/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'SparseE2M1Challenge.walshHadamard_doubly24_factorization' depends on axioms: [propext, Classical.choice, Quot.sound]
'SparseE2M1Challenge.single24_coherence_lower_bound' depends on axioms: [propext, Quot.sound]
'SparseE2M1Challenge.walsh_weighing_attains_coherence_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'SparseE2M1Challenge.skewConference_e2m1_orthogonal' depends on axioms: [propext, Quot.sound]
'SparseE2M1Challenge.q32_pow2_e2m1_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'SparseE2M1Challenge.q16_skew41_e2m1_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'SparseE2M1Challenge.g4k_doubly24_e2m1_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All seven headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `enable_nanoda: true`.
