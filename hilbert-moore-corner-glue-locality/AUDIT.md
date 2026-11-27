# Formal Verification Audit (`hilbert-moore-corner-glue-locality`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built HilbertMooreCornerGlueLocality.Defs (7.9s)
✔ [3/7] Built HilbertMooreCornerGlueLocality.Theorems (57s)
✔ [4/7] Built HilbertMooreCornerGlueLocality (1.9s)
✔ [6/7] Built Solution (2.3s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.9s)
warning: Challenge.lean:18:8: declaration uses `sorry`
warning: Challenge.lean:24:8: declaration uses `sorry`
warning: Challenge.lean:30:8: declaration uses `sorry`
warning: Challenge.lean:36:8: declaration uses `sorry`
warning: Challenge.lean:41:8: declaration uses `sorry`
warning: Challenge.lean:48:8: declaration uses `sorry`
warning: Challenge.lean:53:8: declaration uses `sorry`
warning: Challenge.lean:65:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Exit codes: `lake build` = 0, `lake build Challenge` = 0. Zero errors, zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in the library modules or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'HilbertMooreCornerGlueLocalityChallenge.hilbert2D_bijective_bv' depends on axioms: [propext, Quot.sound]
'HilbertMooreCornerGlueLocalityChallenge.hilbert2D_unit_step_and_hamming' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'HilbertMooreCornerGlueLocalityChallenge.hilbert2D_total_switching_energy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'HilbertMooreCornerGlueLocalityChallenge.hilbert2D_holder_l1_locality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'HilbertMooreCornerGlueLocalityChallenge.hilbert2D_twoCycle_binomial' depends on axioms: [propext, Quot.sound]
'HilbertMooreCornerGlueLocalityChallenge.hilbert2D_orbit_3smooth' depends on axioms: [propext, Quot.sound]
'HilbertMooreCornerGlueLocalityChallenge.moore2D_hamiltonian_cycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'HilbertMooreCornerGlueLocalityChallenge.hilbert3D_fixCount_fibonacci' depends on axioms: [propext, Quot.sound]
```

Exit code: 0. Every headline theorem depends only on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true`.
