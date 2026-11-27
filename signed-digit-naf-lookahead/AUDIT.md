# Formal Verification Audit (`signed-digit-naf-lookahead`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built SignedDigitNafLookahead.Defs (3.0s)
✔ [3/7] Built SignedDigitNafLookahead.Theorems (29s)
✔ [4/7] Built SignedDigitNafLookahead (2.3s)
✔ [6/7] Built Solution (2.5s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (4.7s)
warning: Challenge.lean:18:8: declaration uses `sorry`
warning: Challenge.lean:26:8: declaration uses `sorry`
warning: Challenge.lean:33:8: declaration uses `sorry`
warning: Challenge.lean:40:8: declaration uses `sorry`
warning: Challenge.lean:47:8: declaration uses `sorry`
warning: Challenge.lean:57:8: declaration uses `sorry`
warning: Challenge.lean:67:8: declaration uses `sorry`
warning: Challenge.lean:74:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the eight intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `SignedDigitNafLookahead/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'SignedDigitNafLookaheadChallenge.nat_naf_conservation' depends on axioms: [propext, Classical.choice, Quot.sound]
'SignedDigitNafLookaheadChallenge.nafRecode_minimal_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'SignedDigitNafLookaheadChallenge.naf_global_minimal' depends on axioms: [propext, Quot.sound]
'SignedDigitNafLookaheadChallenge.countZeroDefectBin_recurrence' depends on axioms: [propext, Quot.sound]
'SignedDigitNafLookaheadChallenge.countZeroDefectSD_recurrence' depends on axioms: [propext, Quot.sound]
'SignedDigitNafLookaheadChallenge.olAdd_sound_and_subadditive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SignedDigitNafLookaheadChallenge.causal_adder_not_subadditive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SignedDigitNafLookaheadChallenge.chowRobertson_periodic_blowup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All eight headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), with no `sorryAx` and no `Lean.ofReduceBool`, matching `comparator.json` with `enable_nanoda: true`.
