# Formal Verification Audit (`valuation-tower-poincare-recurrences`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built ValuationTowerPoincareRecurrences.Defs (2.0s)
✔ [3/7] Built ValuationTowerPoincareRecurrences.Theorems (11s)
✔ [4/7] Built ValuationTowerPoincareRecurrences (1.5s)
✔ [6/7] Built Solution (1.6s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.5s)
warning: Challenge.lean:19:8: declaration uses `sorry`
warning: Challenge.lean:30:8: declaration uses `sorry`
warning: Challenge.lean:41:8: declaration uses `sorry`
warning: Challenge.lean:53:8: declaration uses `sorry`
warning: Challenge.lean:61:8: declaration uses `sorry`
warning: Challenge.lean:68:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the 6 intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `ValuationTowerPoincareRecurrences/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'ValuationTowerPoincareRecurrencesChallenge.poincare_return' depends on axioms: [propext, Classical.choice, Quot.sound]
'ValuationTowerPoincareRecurrencesChallenge.poincareR_linearization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ValuationTowerPoincareRecurrencesChallenge.vtpr_full_period' depends on axioms: [propext, Classical.choice, Quot.sound]
'ValuationTowerPoincareRecurrencesChallenge.vtpr_universal_exact_minimal_period' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ValuationTowerPoincareRecurrencesChallenge.twistedLSB_exact_minimal_period' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ValuationTowerPoincareRecurrencesChallenge.wildQuad_exact_minimal_period' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every headline theorem depends exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true` (no `sorryAx`, no `Lean.ofReduceBool`).
