# Formal Verification Audit (`dyadic-bilinear-schur-positivity`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built DyadicBilinearSchurPositivity.Defs (8.2s)
✔ [3/7] Built DyadicBilinearSchurPositivity.Theorems (3.7s)
✔ [4/7] Built DyadicBilinearSchurPositivity (1.4s)
✔ [6/7] Built Solution (1.5s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.4s)
warning: Challenge.lean:9:8: declaration uses `sorry`
warning: Challenge.lean:16:8: declaration uses `sorry`
warning: Challenge.lean:20:8: declaration uses `sorry`
warning: Challenge.lean:25:8: declaration uses `sorry`
warning: Challenge.lean:33:8: declaration uses `sorry`
warning: Challenge.lean:38:8: declaration uses `sorry`
warning: Challenge.lean:45:8: declaration uses `sorry`
warning: Challenge.lean:50:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `DyadicBilinearSchurPositivity/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'DyadicBilinearSchurPositivityChallenge.soundness_strict_pd' depends on axioms: [propext, Classical.choice, Quot.sound]
'DyadicBilinearSchurPositivityChallenge.v2Nat_xor_eq_absDiff' depends on axioms: [propext, Quot.sound]
'DyadicBilinearSchurPositivityChallenge.thm_monnaArch_strict_pd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DyadicBilinearSchurPositivityChallenge.monnaArch_direct_induction_fails' depends on axioms: [propext, Quot.sound]
'DyadicBilinearSchurPositivityChallenge.adelic_kernels_noncommuting' depends on axioms: [propext, Quot.sound]
'DyadicBilinearSchurPositivityChallenge.thm_adelic_sharp_dipole_k1' depends on axioms: [propext, Quot.sound]
'DyadicBilinearSchurPositivityChallenge.asym_nondiag_asymmetric_diag' depends on axioms: [propext, Quot.sound]
'DyadicBilinearSchurPositivityChallenge.thm_asym_nondiag_sharp_W00' depends on axioms: [propext, Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
