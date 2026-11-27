# Formal Verification Audit (`booth-csa-multiplier-invariants`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built BoothCsaMultiplierInvariants.Defs (6.6s)
✔ [3/7] Built BoothCsaMultiplierInvariants.Theorems (15s)
✔ [4/7] Built BoothCsaMultiplierInvariants (1.4s)
✔ [6/7] Built Solution (1.6s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.4s)
warning: Challenge.lean:7:8: declaration uses `sorry`
warning: Challenge.lean:12:8: declaration uses `sorry`
warning: Challenge.lean:22:8: declaration uses `sorry`
warning: Challenge.lean:31:8: declaration uses `sorry`
warning: Challenge.lean:40:8: declaration uses `sorry`
warning: Challenge.lean:47:8: declaration uses `sorry`
warning: Challenge.lean:55:8: declaration uses `sorry`
warning: Challenge.lean:61:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `BoothCsaMultiplierInvariants/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'BoothCsaMultiplierInvariantsChallenge.csa3to2_exact_mod' depends on axioms: [propext, Quot.sound]
'BoothCsaMultiplierInvariantsChallenge.lift_all_widths' depends on axioms: [propext, Classical.choice, Quot.sound]
'BoothCsaMultiplierInvariantsChallenge.zeroCarryTop_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'BoothCsaMultiplierInvariantsChallenge.unnormalized_csa_rshift_fails' depends on axioms: [propext, Quot.sound]
'BoothCsaMultiplierInvariantsChallenge.sec_cancellation_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BoothCsaMultiplierInvariantsChallenge.radix4_booth_tree_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BoothCsaMultiplierInvariantsChallenge.booth_acc_endpoints_tight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BoothCsaMultiplierInvariantsChallenge.badGuardCert_g2_rejected' does not depend on any axioms
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
