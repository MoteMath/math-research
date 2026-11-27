# Formal Verification Audit (`hypercube-carry-shadow-collapse`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built HypercubeCarryShadowCollapse.Defs (14s)
✔ [3/7] Built HypercubeCarryShadowCollapse.Theorems (5.0s)
✔ [4/7] Built HypercubeCarryShadowCollapse (1.7s)
✔ [6/7] Built Solution (1.8s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.6s)
warning: Challenge.lean:16:8: declaration uses `sorry`
warning: Challenge.lean:23:8: declaration uses `sorry`
warning: Challenge.lean:28:8: declaration uses `sorry`
warning: Challenge.lean:34:8: declaration uses `sorry`
warning: Challenge.lean:40:8: declaration uses `sorry`
warning: Challenge.lean:46:8: declaration uses `sorry`
warning: Challenge.lean:53:8: declaration uses `sorry`
warning: Challenge.lean:58:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the 8 intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `HypercubeCarryShadowCollapse/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'HypercubeCarryShadowCollapseChallenge.checkGuardedBisimWitness_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'HypercubeCarryShadowCollapseChallenge.phi_carry_chain_collapse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'HypercubeCarryShadowCollapseChallenge.carryMask_eigen_sandwich_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'HypercubeCarryShadowCollapseChallenge.carryMask_dominated_absorption' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'HypercubeCarryShadowCollapseChallenge.baseB_carry_defect' depends on axioms: [propext, Classical.choice, Quot.sound]
'HypercubeCarryShadowCollapseChallenge.Q_closed_form_on_dom' depends on axioms: [propext, Classical.choice, Quot.sound]
'HypercubeCarryShadowCollapseChallenge.Q_collapse_universal' depends on axioms: [propext, Classical.choice, Quot.sound]
'HypercubeCarryShadowCollapseChallenge.Q_bitvec_nilpotent' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every headline theorem depends only on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true`.
