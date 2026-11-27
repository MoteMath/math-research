# Formal Verification Audit (`dualrail-tropical-carry-horizon`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built DualrailTropicalCarryHorizon.Defs (5.0s)
✔ [3/7] Built DualrailTropicalCarryHorizon.Theorems (26s)
✔ [4/7] Built DualrailTropicalCarryHorizon (2.2s)
✔ [6/7] Built Solution (4.9s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (3.1s)
warning: Challenge.lean:17:8: declaration uses `sorry`
warning: Challenge.lean:25:8: declaration uses `sorry`
warning: Challenge.lean:34:8: declaration uses `sorry`
warning: Challenge.lean:42:8: declaration uses `sorry`
warning: Challenge.lean:49:8: declaration uses `sorry`
warning: Challenge.lean:56:8: declaration uses `sorry`
warning: Challenge.lean:63:8: declaration uses `sorry`
warning: Challenge.lean:73:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `DualrailTropicalCarryHorizon/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'DualrailTropicalCarryHorizonChallenge.potential_lift_all_widths' depends on axioms: [propext, Quot.sound]
'DualrailTropicalCarryHorizonChallenge.relational_bisim_mod_eq' depends on axioms: [propext, Quot.sound]
'DualrailTropicalCarryHorizonChallenge.avizAdd_exact_int' depends on axioms: [propext, Quot.sound]
'DualrailTropicalCarryHorizonChallenge.avizAdd_assoc_mod' depends on axioms: [propext, Quot.sound]
'DualrailTropicalCarryHorizonChallenge.avizAdd_horizon2' depends on axioms: [propext, Quot.sound]
'DualrailTropicalCarryHorizonChallenge.compileRight_equiv_all_widths' depends on axioms: [propext, Quot.sound]
'DualrailTropicalCarryHorizonChallenge.exact_horizon_achieved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DualrailTropicalCarryHorizonChallenge.no_horizon_cert_for_ripple' depends on axioms: [propext, Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
