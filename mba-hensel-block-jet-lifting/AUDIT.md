# Formal Verification Audit (`mba-hensel-block-jet-lifting`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built MbaHenselBlockJetLifting.Defs (2.9s)
✔ [3/7] Built MbaHenselBlockJetLifting.Theorems (23s)
✔ [4/7] Built MbaHenselBlockJetLifting (2.4s)
✔ [6/7] Built Solution (2.4s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.7s)
warning: Challenge.lean:7:8: declaration uses `sorry`
warning: Challenge.lean:11:8: declaration uses `sorry`
warning: Challenge.lean:16:8: declaration uses `sorry`
warning: Challenge.lean:26:8: declaration uses `sorry`
warning: Challenge.lean:35:8: declaration uses `sorry`
warning: Challenge.lean:39:8: declaration uses `sorry`
warning: Challenge.lean:47:8: declaration uses `sorry`
warning: Challenge.lean:51:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `MbaHenselBlockJetLifting/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'MbaHenselBlockJetLiftingChallenge.evalMod_coherent' depends on axioms: [propext, Quot.sound]
'MbaHenselBlockJetLiftingChallenge.symDeriv0_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MbaHenselBlockJetLiftingChallenge.quadLiftFromJet_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MbaHenselBlockJetLiftingChallenge.thm1_constructive_lifts' depends on axioms: [propext, Classical.choice, Quot.sound]
'MbaHenselBlockJetLiftingChallenge.witness2_one_root' depends on axioms: [propext, Classical.choice, Quot.sound]
'MbaHenselBlockJetLiftingChallenge.witness3_quad_lift_concrete' depends on axioms: [propext]
'MbaHenselBlockJetLiftingChallenge.sharpness1_even_mask' depends on axioms: [propext]
'MbaHenselBlockJetLiftingChallenge.sharpness3_below_mask_threshold' depends on axioms: [propext]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
