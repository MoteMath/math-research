# Formal Verification Audit (`walnut-prophecy-skolem-lifter`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built WalnutProphecySkolemLifter.Defs (2.7s)
✔ [3/7] Built WalnutProphecySkolemLifter.Theorems (138s)
✔ [4/7] Built WalnutProphecySkolemLifter (1.0s)
✔ [6/7] Built Solution (2.0s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.7s)
warning: Challenge.lean:21:8: declaration uses `sorry`
warning: Challenge.lean:29:8: declaration uses `sorry`
warning: Challenge.lean:36:8: declaration uses `sorry`
warning: Challenge.lean:44:8: declaration uses `sorry`
warning: Challenge.lean:50:8: declaration uses `sorry`
warning: Challenge.lean:55:8: declaration uses `sorry`
warning: Challenge.lean:62:8: declaration uses `sorry`
warning: Challenge.lean:69:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the eight intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `WalnutProphecySkolemLifter/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'WalnutProphecySkolemLifterChallenge.homCert_sound' depends on axioms: [propext, Quot.sound]
'WalnutProphecySkolemLifterChallenge.existsCert_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'WalnutProphecySkolemLifterChallenge.prophecyCert_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'WalnutProphecySkolemLifterChallenge.universalCert_sound' depends on axioms: [propext, Quot.sound]
'WalnutProphecySkolemLifterChallenge.dfaGrayAdd_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'WalnutProphecySkolemLifterChallenge.grayAddParity_exact_square_spectrum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'WalnutProphecySkolemLifterChallenge.grayAddParity_exact_cube_spectrum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'WalnutProphecySkolemLifterChallenge.grayAddParity_fifth_power_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All eight headline theorems depend exclusively on Lean 4 standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true`; none depends on `sorryAx` or `Lean.ofReduceBool`.
