# Formal Verification Audit (`stern-walsh-carry-resonance`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Replayed Challenge
warning: Challenge.lean:16:8: declaration uses `sorry`
warning: Challenge.lean:21:8: declaration uses `sorry`
warning: Challenge.lean:27:8: declaration uses `sorry`
warning: Challenge.lean:33:8: declaration uses `sorry`
warning: Challenge.lean:38:8: declaration uses `sorry`
warning: Challenge.lean:45:8: declaration uses `sorry`
warning: Challenge.lean:51:8: declaration uses `sorry`
warning: Challenge.lean:57:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings in `lake build`; the only warnings in `lake build Challenge` are the 8 intentional `sorry` placeholders in `Challenge.lean`. Zero `sorry`/`admit`/`native_decide`/`axiom` anywhere in `SternWalshCarryResonance/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'SternWalshCarryResonanceChallenge.stern_cw_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'SternWalshCarryResonanceChallenge.stern_walsh_spectrum' depends on axioms: [propext, Classical.choice, Quot.sound]
'SternWalshCarryResonanceChallenge.aStern_walsh_spectrum' depends on axioms: [propext, Classical.choice, Quot.sound]
'SternWalshCarryResonanceChallenge.twoStern_walsh_vanishing' depends on axioms: [propext, Classical.choice, Quot.sound]
'SternWalshCarryResonanceChallenge.carryStern_mod0_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'SternWalshCarryResonanceChallenge.carryStern_mod1_affine' depends on axioms: [propext, Classical.choice, Quot.sound]
'SternWalshCarryResonanceChallenge.carryStern_mod2_affine_dual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SternWalshCarryResonanceChallenge.quadStern_tm_closed_form' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All 8 headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true`.
