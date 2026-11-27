# Formal Verification Audit (`walsh-gray-conjugacy-spectra`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built WalshGrayConjugacySpectra.Defs (5.1s)
✔ [3/7] Built WalshGrayConjugacySpectra.Theorems (6.4s)
✔ [4/7] Built WalshGrayConjugacySpectra (1.4s)
✔ [6/7] Built Solution (1.8s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.6s)
warning: Challenge.lean:8:8: declaration uses `sorry`
warning: Challenge.lean:14:8: declaration uses `sorry`
warning: Challenge.lean:20:8: declaration uses `sorry`
warning: Challenge.lean:34:8: declaration uses `sorry`
warning: Challenge.lean:43:8: declaration uses `sorry`
warning: Challenge.lean:57:8: declaration uses `sorry`
warning: Challenge.lean:65:8: declaration uses `sorry`
warning: Challenge.lean:70:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `WalshGrayConjugacySpectra/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'WalshGrayConjugacySpectraChallenge.walsh_perm_conj' depends on axioms: [propext, Quot.sound]
'WalshGrayConjugacySpectraChallenge.spectral_period_lift' depends on axioms: [propext, Quot.sound]
'WalshGrayConjugacySpectraChallenge.even_symmetric_projectors' depends on axioms: [propext, Quot.sound]
'WalshGrayConjugacySpectraChallenge.hyperplane_even_trace_lift' depends on axioms: [propext, Quot.sound]
'WalshGrayConjugacySpectraChallenge.walsh_gray_mod4_antisym' depends on axioms: [propext, Classical.choice, Quot.sound]
'WalshGrayConjugacySpectraChallenge.walsh_bitrev_parity_dichotomy_odd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'WalshGrayConjugacySpectraChallenge.walsh_gray_rot_period' depends on axioms: [propext, Quot.sound]
'WalshGrayConjugacySpectraChallenge.sharp_nonlinear_inc2_not_scaled_perm' depends on axioms: [propext, Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
