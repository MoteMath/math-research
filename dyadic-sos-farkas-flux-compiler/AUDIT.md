# Formal Verification Audit (`dyadic-sos-farkas-flux-compiler`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built DyadicSosFarkasFluxCompiler.Defs (2.1s)
✔ [3/7] Built DyadicSosFarkasFluxCompiler.Theorems (8.4s)
✔ [4/7] Built DyadicSosFarkasFluxCompiler (1.2s)
✔ [6/7] Built Solution (1.2s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.2s)
warning: Challenge.lean:18:8: declaration uses `sorry`
warning: Challenge.lean:27:8: declaration uses `sorry`
warning: Challenge.lean:40:8: declaration uses `sorry`
warning: Challenge.lean:45:8: declaration uses `sorry`
warning: Challenge.lean:51:8: declaration uses `sorry`
warning: Challenge.lean:56:8: declaration uses `sorry`
warning: Challenge.lean:61:8: declaration uses `sorry`
warning: Challenge.lean:66:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `DyadicSosFarkasFluxCompiler/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'DyadicSosFarkasFluxCompilerChallenge.farkasSOS_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'DyadicSosFarkasFluxCompilerChallenge.cyclic_flux_sound_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'DyadicSosFarkasFluxCompilerChallenge.thm1_asym_skew_quartic_cyclic_int' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DyadicSosFarkasFluxCompilerChallenge.thm3b_hypercube_asym_3pattern' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DyadicSosFarkasFluxCompilerChallenge.thm4_boolean_frustrated_triangle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DyadicSosFarkasFluxCompilerChallenge.thm5a_parametric_biharmonic_cyclic_int' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DyadicSosFarkasFluxCompilerChallenge.thm5b_open_biharmonic_stabilized_int' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DyadicSosFarkasFluxCompilerChallenge.thm6_nonlinear_farkas_refutation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
