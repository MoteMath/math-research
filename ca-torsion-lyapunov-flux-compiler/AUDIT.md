# Formal Verification Audit (`ca-torsion-lyapunov-flux-compiler`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built CaTorsionLyapunovFluxCompiler.Defs (2.6s)
✔ [3/7] Built CaTorsionLyapunovFluxCompiler.Theorems (8.9s)
✔ [4/7] Built CaTorsionLyapunovFluxCompiler (1.7s)
✔ [6/7] Built Solution (1.8s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.1s)
warning: Challenge.lean:23:8: declaration uses `sorry`
warning: Challenge.lean:30:8: declaration uses `sorry`
warning: Challenge.lean:36:8: declaration uses `sorry`
warning: Challenge.lean:43:8: declaration uses `sorry`
warning: Challenge.lean:49:8: declaration uses `sorry`
warning: Challenge.lean:58:8: declaration uses `sorry`
warning: Challenge.lean:65:8: declaration uses `sorry`
warning: Challenge.lean:72:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the eight intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `CaTorsionLyapunovFluxCompiler/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'CaTorsionLyapunovFluxCompilerChallenge.thm_pat101_conservation_0xac8c' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CaTorsionLyapunovFluxCompilerChallenge.thm_strict_fp_termination_0x2c48' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CaTorsionLyapunovFluxCompilerChallenge.thm_global_acyclicity_0x2c48' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CaTorsionLyapunovFluxCompilerChallenge.thm_travelingWave_locking_rule152' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CaTorsionLyapunovFluxCompilerChallenge.thm_microcanonical_0xf0e0' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CaTorsionLyapunovFluxCompilerChallenge.thm_blinker_convergence_rule108' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CaTorsionLyapunovFluxCompilerChallenge.thm_mod3_torsion_0xb0f0' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CaTorsionLyapunovFluxCompilerChallenge.thm_mod2_torsion_0x83bc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All eight headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true`. No `sorryAx` and no `Lean.ofReduceBool` appear.
