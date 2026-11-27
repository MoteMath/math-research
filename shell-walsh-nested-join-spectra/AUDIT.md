# Formal Verification Audit (`shell-walsh-nested-join-spectra`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built ShellWalshNestedJoinSpectra.Defs (15s)
✔ [3/7] Built ShellWalshNestedJoinSpectra.Theorems (2.8s)
✔ [4/7] Built ShellWalshNestedJoinSpectra (1.4s)
✔ [6/7] Built Solution (1.6s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.5s)
warning: Challenge.lean:8:8: declaration uses `sorry`
warning: Challenge.lean:12:8: declaration uses `sorry`
warning: Challenge.lean:24:8: declaration uses `sorry`
warning: Challenge.lean:31:8: declaration uses `sorry`
warning: Challenge.lean:40:8: declaration uses `sorry`
warning: Challenge.lean:45:8: declaration uses `sorry`
warning: Challenge.lean:53:8: declaration uses `sorry`
warning: Challenge.lean:59:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `ShellWalshNestedJoinSpectra/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'ShellWalshNestedJoinSpectraChallenge.det_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'ShellWalshNestedJoinSpectraChallenge.orthogonal_eigenbasis_kirchhoff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ShellWalshNestedJoinSpectraChallenge.shellLaplacian_kirchhoff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ShellWalshNestedJoinSpectraChallenge.carryXorLaplacian_kirchhoff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ShellWalshNestedJoinSpectraChallenge.dyadic_spanning_trees' depends on axioms: [propext, Classical.choice, Quot.sound]
'ShellWalshNestedJoinSpectraChallenge.evenSum_kirchhoff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ShellWalshNestedJoinSpectraChallenge.sharpness_c3_charpoly' depends on axioms: [propext, Classical.choice, Quot.sound]
'ShellWalshNestedJoinSpectraChallenge.witness_nonvacuous_engine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
