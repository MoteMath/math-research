# Formal Verification Audit (`bitpack-raw-proof-meta-compiler`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built BitpackRawProofMetaCompiler.Defs (3.9s)
✔ [3/7] Built BitpackRawProofMetaCompiler.Theorems (8.7s)
✔ [4/7] Built BitpackRawProofMetaCompiler (1.4s)
✔ [6/7] Built Solution (1.5s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.5s)
warning: Challenge.lean:8:8: declaration uses `sorry`
warning: Challenge.lean:11:8: declaration uses `sorry`
warning: Challenge.lean:16:8: declaration uses `sorry`
warning: Challenge.lean:21:8: declaration uses `sorry`
warning: Challenge.lean:26:8: declaration uses `sorry`
warning: Challenge.lean:31:8: declaration uses `sorry`
warning: Challenge.lean:36:8: declaration uses `sorry`
warning: Challenge.lean:44:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `BitpackRawProofMetaCompiler/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'BitpackRawProofMetaCompilerChallenge.checkCert_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'BitpackRawProofMetaCompilerChallenge.soundness_verifyRawCert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitpackRawProofMetaCompilerChallenge.gray_3x_uncertainty' depends on axioms: [propext, Classical.choice, Quot.sound]
'BitpackRawProofMetaCompilerChallenge.pop_5x_9x_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'BitpackRawProofMetaCompilerChallenge.pop_3x_or_11x_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]
'BitpackRawProofMetaCompilerChallenge.pop_2var_3x_plus_y_xor' depends on axioms: [propext, Classical.choice, Quot.sound]
'BitpackRawProofMetaCompilerChallenge.pop_eq_3x_plus_y_cascade' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitpackRawProofMetaCompilerChallenge.bit_eq_3x_plus_y_collapse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
