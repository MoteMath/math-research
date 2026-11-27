# Formal Verification Audit (`group-ring-polylog-bit-inverses`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built GroupRingPolylogBitInverses.Defs (5.9s)
✔ [3/7] Built GroupRingPolylogBitInverses.Theorems (9.9s)
✔ [4/7] Built GroupRingPolylogBitInverses (1.4s)
✔ [6/7] Built Solution (1.4s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.4s)
warning: Challenge.lean:8:8: declaration uses `sorry`
warning: Challenge.lean:13:8: declaration uses `sorry`
warning: Challenge.lean:18:8: declaration uses `sorry`
warning: Challenge.lean:24:8: declaration uses `sorry`
warning: Challenge.lean:28:8: declaration uses `sorry`
warning: Challenge.lean:32:8: declaration uses `sorry`
warning: Challenge.lean:37:8: declaration uses `sorry`
warning: Challenge.lean:42:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `GroupRingPolylogBitInverses/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'GroupRingPolylogBitInversesChallenge.parseval_plancherel' depends on axioms: [propext, Quot.sound]
'GroupRingPolylogBitInversesChallenge.higman_rigidity' depends on axioms: [propext, Quot.sound]
'GroupRingPolylogBitInversesChallenge.binary01_no_self_inverse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GroupRingPolylogBitInversesChallenge.treeElem_wht' depends on axioms: [propext, Quot.sound]
'GroupRingPolylogBitInversesChallenge.treeElem_polylog_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GroupRingPolylogBitInversesChallenge.asymTree_non_self_inverse' depends on axioms: [propext, Quot.sound]
'GroupRingPolylogBitInversesChallenge.k3_no_spanning_ternary_dyadic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GroupRingPolylogBitInversesChallenge.unshiftedLift_breaks_ternary' depends on axioms: [propext, Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
