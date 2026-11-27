# Formal Verification Audit (`carry-run-cyclotomic-transfer`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [6/7] Built Solution (1.8s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Replayed Challenge
warning: Challenge.lean:21:8: declaration uses `sorry`
warning: Challenge.lean:33:8: declaration uses `sorry`
warning: Challenge.lean:47:8: declaration uses `sorry`
warning: Challenge.lean:60:8: declaration uses `sorry`
warning: Challenge.lean:69:8: declaration uses `sorry`
warning: Challenge.lean:78:8: declaration uses `sorry`
warning: Challenge.lean:85:8: declaration uses `sorry`
warning: Challenge.lean:95:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the 8 intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `CarryRunCyclotomicTransfer/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'CarryRunCyclotomicTransferChallenge.evenRadix_carryRun_outputParity_collapse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarryRunCyclotomicTransferChallenge.binary_carryRun_fullPopcount_collapse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarryRunCyclotomicTransferChallenge.evenRadix_rippleDepth_inputParity_collapse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarryRunCyclotomicTransferChallenge.binary_rippleDepth_plain_recurrence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarryRunCyclotomicTransferChallenge.binary_carryRun_absorption_recurrence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarryRunCyclotomicTransferChallenge.binary_zeroAbsorption_dichotomy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarryRunCyclotomicTransferChallenge.rippleOp_annihilator' depends on axioms: [propext, Quot.sound]
'CarryRunCyclotomicTransferChallenge.runOp_annihilator' depends on axioms: [propext, Quot.sound]
```

Every headline theorem depends exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true` (no `sorryAx`, no `Lean.ofReduceBool`).
