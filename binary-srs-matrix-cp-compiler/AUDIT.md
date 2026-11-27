# Formal Verification Audit (`binary-srs-matrix-cp-compiler`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built BinarySrsMatrixCpCompiler.Defs (3.2s)
✔ [3/7] Built BinarySrsMatrixCpCompiler.Theorems (21s)
✔ [4/7] Built BinarySrsMatrixCpCompiler (1.7s)
✔ [6/7] Built Solution (1.6s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.1s)
warning: Challenge.lean:18:8: declaration uses `sorry`
warning: Challenge.lean:23:8: declaration uses `sorry`
warning: Challenge.lean:29:8: declaration uses `sorry`
warning: Challenge.lean:37:8: declaration uses `sorry`
warning: Challenge.lean:43:8: declaration uses `sorry`
warning: Challenge.lean:49:8: declaration uses `sorry`
warning: Challenge.lean:54:8: declaration uses `sorry`
warning: Challenge.lean:62:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the eight intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `BinarySrsMatrixCpCompiler/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'BinarySrsMatrixCpCompilerChallenge.cert_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'BinarySrsMatrixCpCompilerChallenge.convertible_iff_normalize_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BinarySrsMatrixCpCompilerChallenge.confluent_of_term_invariant' depends on axioms: [propext, Quot.sound]
'BinarySrsMatrixCpCompilerChallenge.ampSys_terminating' depends on axioms: [propext, Classical.choice, Quot.sound]
'BinarySrsMatrixCpCompilerChallenge.ampSys_confluent_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'BinarySrsMatrixCpCompilerChallenge.mod3_convertible_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'BinarySrsMatrixCpCompilerChallenge.mersenneSRS_master' depends on axioms: [propext, Classical.choice, Quot.sound]
'BinarySrsMatrixCpCompilerChallenge.fermatModSRS_master' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All eight headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true`; `confluent_of_term_invariant` needs only `[propext, Quot.sound]`.