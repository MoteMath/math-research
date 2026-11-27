# Formal Verification Audit (`carryless-carried-resonance-curve`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.2s)
warning: Challenge.lean:16:8: declaration uses `sorry`
warning: Challenge.lean:22:8: declaration uses `sorry`
warning: Challenge.lean:28:8: declaration uses `sorry`
warning: Challenge.lean:34:8: declaration uses `sorry`
warning: Challenge.lean:40:8: declaration uses `sorry`
warning: Challenge.lean:51:8: declaration uses `sorry`
warning: Challenge.lean:58:8: declaration uses `sorry`
warning: Challenge.lean:65:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings in `lake build`; the only warnings in `lake build Challenge` are the 8 intentional `sorry` placeholders in `Challenge.lean`. Zero `sorry`/`admit`/`native_decide`/`axiom` anywhere in `CarrylessCarriedResonanceCurve/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'CarrylessCarriedResonanceCurveChallenge.henselLift_iff_dvd' depends on axioms: [propext, Quot.sound]
'CarrylessCarriedResonanceCurveChallenge.regime_I_carried_dominated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarrylessCarriedResonanceCurveChallenge.regime_II_carryless_dominated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarrylessCarriedResonanceCurveChallenge.regime_III_carried_dominated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarrylessCarriedResonanceCurveChallenge.resonant_bridge_master' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarrylessCarriedResonanceCurveChallenge.resonant_root_invariance_below_threshold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarrylessCarriedResonanceCurveChallenge.resonant_bit_root_shift_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarrylessCarriedResonanceCurveChallenge.resonance_curve_infinitely_inhabited' depends on axioms: [propext, Quot.sound]
```

All 8 headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true`.
