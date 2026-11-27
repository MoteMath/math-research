# Formal Verification Audit (`integer-mps-mpo-tensor-verifier`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built IntegerMpsMpoTensorVerifier.Defs (1.6s)
✔ [3/7] Built IntegerMpsMpoTensorVerifier.Theorems (19s)
✔ [4/7] Built IntegerMpsMpoTensorVerifier (1.2s)
✔ [6/7] Built Solution (1.2s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.3s)
warning: Challenge.lean:17:8: declaration uses `sorry`
warning: Challenge.lean:23:8: declaration uses `sorry`
warning: Challenge.lean:28:8: declaration uses `sorry`
warning: Challenge.lean:37:8: declaration uses `sorry`
warning: Challenge.lean:41:8: declaration uses `sorry`
warning: Challenge.lean:45:8: declaration uses `sorry`
warning: Challenge.lean:53:8: declaration uses `sorry`
warning: Challenge.lean:57:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `IntegerMpsMpoTensorVerifier/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'IntegerMpsMpoTensorVerifierChallenge.sound_rightReductionCert' depends on axioms: [propext, Quot.sound]
'IntegerMpsMpoTensorVerifierChallenge.sound_orthogonalityCert' depends on axioms: [propext, Quot.sound]
'IntegerMpsMpoTensorVerifierChallenge.sound_recurrenceCert' depends on axioms: [propext, Quot.sound]
'IntegerMpsMpoTensorVerifierChallenge.thm_rs_carry_parametric_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'IntegerMpsMpoTensorVerifierChallenge.thm_carry_hadamard_fibonacci' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'IntegerMpsMpoTensorVerifierChallenge.thm_carry_borrow_orthogonal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'IntegerMpsMpoTensorVerifierChallenge.thm_carry_all_odd_traces_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'IntegerMpsMpoTensorVerifierChallenge.thm_carry_plus_borrow_tm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
