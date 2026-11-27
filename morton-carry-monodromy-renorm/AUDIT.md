# Formal Verification Audit (`morton-carry-monodromy-renorm`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built MortonCarryMonodromyRenorm.Defs (7.0s)
✔ [3/7] Built MortonCarryMonodromyRenorm.Theorems (14s)
✔ [4/7] Built MortonCarryMonodromyRenorm (1.7s)
✔ [6/7] Built Solution (1.9s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.4s)
warning: Challenge.lean:20:8: declaration uses `sorry`
warning: Challenge.lean:28:8: declaration uses `sorry`
warning: Challenge.lean:34:8: declaration uses `sorry`
warning: Challenge.lean:42:8: declaration uses `sorry`
warning: Challenge.lean:49:8: declaration uses `sorry`
warning: Challenge.lean:56:8: declaration uses `sorry`
warning: Challenge.lean:61:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the 7 intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `MortonCarryMonodromyRenorm/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'MortonCarryMonodromyRenormChallenge.cmr_full_period_compiler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MortonCarryMonodromyRenormChallenge.mortonRot_exact_period_all_d_n' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MortonCarryMonodromyRenormChallenge.mortonRot_orbit_iff_flagHelix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MortonCarryMonodromyRenormChallenge.morton2D_exact_period_all_z' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MortonCarryMonodromyRenormChallenge.morton2D_period_dichotomy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MortonCarryMonodromyRenormChallenge.delayed_fracture_exact_period' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MortonCarryMonodromyRenormChallenge.delayed_fracture_closed_form' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every headline theorem depends exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true` (no `sorryAx`, no `Lean.ofReduceBool`).
