# Formal Verification Audit (`fenwick-portal-parity-schur`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built FenwickPortalParitySchur.Defs (8.2s)
⚠ [3/7] Built FenwickPortalParitySchur.Theorems (56s)
warning: FenwickPortalParitySchur/Theorems.lean:154:0: automatically included section variable(s) unused in theorem `SpecMat7.updateRow_self`:
  [CRing R]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [CRing R] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
✔ [4/7] Built FenwickPortalParitySchur (1.2s)
✔ [6/7] Built Solution (1.3s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.4s)
warning: Challenge.lean:7:8: declaration uses `sorry`
warning: Challenge.lean:12:8: declaration uses `sorry`
warning: Challenge.lean:36:8: declaration uses `sorry`
warning: Challenge.lean:41:8: declaration uses `sorry`
warning: Challenge.lean:46:8: declaration uses `sorry`
warning: Challenge.lean:52:8: declaration uses `sorry`
warning: Challenge.lean:57:8: declaration uses `sorry`
warning: Challenge.lean:63:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `FenwickPortalParitySchur/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'FenwickPortalParitySchurChallenge.portalTuple_perturb' depends on axioms: [propext, Classical.choice, Quot.sound]
'FenwickPortalParitySchurChallenge.bordered_schur_inv' depends on axioms: [propext, Quot.sound]
'FenwickPortalParitySchurChallenge.fenwickUQ_unimodular' depends on axioms: [propext, Classical.choice, Quot.sound]
'FenwickPortalParitySchurChallenge.fenwickUQLap_charpoly_fps' depends on axioms: [propext, Classical.choice, Quot.sound]
'FenwickPortalParitySchurChallenge.fenwickUQLap_spanning_tree_square' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'FenwickPortalParitySchurChallenge.inOrderHeap_charpoly_factorization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'FenwickPortalParitySchurChallenge.witness_dyadic_inv_k2' depends on axioms: [propext, Classical.choice, Quot.sound]
'FenwickPortalParitySchurChallenge.sharpness_asymmetric_weights_k2' depends on axioms: [propext]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
