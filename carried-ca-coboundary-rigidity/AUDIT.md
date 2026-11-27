# Formal Verification Audit (`carried-ca-coboundary-rigidity`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built CarriedCaCoboundaryRigidity.Defs (7.3s)
✔ [3/7] Built CarriedCaCoboundaryRigidity.Theorems (7.9s)
✔ [4/7] Built CarriedCaCoboundaryRigidity (1.0s)
✔ [6/7] Built Solution (1.0s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.8s)
warning: Challenge.lean:20:8: declaration uses `sorry`
warning: Challenge.lean:29:8: declaration uses `sorry`
warning: Challenge.lean:39:8: declaration uses `sorry`
warning: Challenge.lean:44:8: declaration uses `sorry`
warning: Challenge.lean:49:8: declaration uses `sorry`
warning: Challenge.lean:55:8: declaration uses `sorry`
warning: Challenge.lean:60:8: declaration uses `sorry`
warning: Challenge.lean:65:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the eight intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `CarriedCaCoboundaryRigidity/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'CarriedCaCoboundaryRigidityChallenge.causal_bij_weight_rigidity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarriedCaCoboundaryRigidityChallenge.causal_bij_unbounded_both_sides' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarriedCaCoboundaryRigidityChallenge.carriedRule30_alt_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarriedCaCoboundaryRigidityChallenge.carriedRule30_iter_alt_exact' depends on axioms: [propext, Quot.sound]
'CarriedCaCoboundaryRigidityChallenge.altSemigroup_exact' depends on axioms: [propext, Quot.sound]
'CarriedCaCoboundaryRigidityChallenge.fredkinRouter_iter_popcount_exact' depends on axioms: [propext, Quot.sound]
'CarriedCaCoboundaryRigidityChallenge.walkInv_involutive' depends on axioms: [propext, Quot.sound]
'CarriedCaCoboundaryRigidityChallenge.rule54_105_period4' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All eight headline theorems depend exclusively on Lean 4 standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true`; none depends on `sorryAx` or `Lean.ofReduceBool`.
