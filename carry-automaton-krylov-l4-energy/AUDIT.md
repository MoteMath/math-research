# Formal Verification Audit (`carry-automaton-krylov-l4-energy`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built CarryAutomatonKrylovL4Energy.Defs (115s)
✔ [3/7] Built CarryAutomatonKrylovL4Energy.Theorems (56s)
✔ [4/7] Built CarryAutomatonKrylovL4Energy (1.6s)
✔ [6/7] Built Solution (2.1s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.9s)
warning: Challenge.lean:8:8: declaration uses `sorry`
warning: Challenge.lean:15:8: declaration uses `sorry`
warning: Challenge.lean:28:8: declaration uses `sorry`
warning: Challenge.lean:33:8: declaration uses `sorry`
warning: Challenge.lean:39:8: declaration uses `sorry`
warning: Challenge.lean:46:8: declaration uses `sorry`
warning: Challenge.lean:50:8: declaration uses `sorry`
warning: Challenge.lean:55:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `CarryAutomatonKrylovL4Energy/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'CarryAutomatonKrylovL4EnergyChallenge.apCorr_even' depends on axioms: [propext, Quot.sound]
'CarryAutomatonKrylovL4EnergyChallenge.bijTail_infinite_flat_spectrum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarryAutomatonKrylovL4EnergyChallenge.innerQRZ_dualStep' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarryAutomatonKrylovL4EnergyChallenge.paperfolding_direct_rec' depends on axioms: [propext, Quot.sound]
'CarryAutomatonKrylovL4EnergyChallenge.baumSweet_classical_rec' depends on axioms: [propext, Quot.sound]
'CarryAutomatonKrylovL4EnergyChallenge.mask6Cert_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarryAutomatonKrylovL4EnergyChallenge.mask6_totE4_rec' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarryAutomatonKrylovL4EnergyChallenge.rudinShapiro_E4_closed_form' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
