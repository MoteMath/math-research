# Formal Verification Audit (`walsh-mobius-runs-dihedral-spectra`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.9s)
warning: Challenge.lean:17:8: declaration uses `sorry`
warning: Challenge.lean:23:8: declaration uses `sorry`
warning: Challenge.lean:30:8: declaration uses `sorry`
warning: Challenge.lean:36:8: declaration uses `sorry`
warning: Challenge.lean:42:8: declaration uses `sorry`
warning: Challenge.lean:52:8: declaration uses `sorry`
warning: Challenge.lean:58:8: declaration uses `sorry`
warning: Challenge.lean:64:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `WalshMobiusRunsDihedralSpectra/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'WalshMobiusRunsDihedralSpectraChallenge.det_xorConv' depends on axioms: [propext, Classical.choice, Quot.sound]
'WalshMobiusRunsDihedralSpectraChallenge.charPoly_xorConv' depends on axioms: [propext, Classical.choice, Quot.sound]
'WalshMobiusRunsDihedralSpectraChallenge.det_andLattice' depends on axioms: [propext, Classical.choice, Quot.sound]
'WalshMobiusRunsDihedralSpectraChallenge.wht_transfer_compiler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'WalshMobiusRunsDihedralSpectraChallenge.det_runs_xorConv' depends on axioms: [propext, Classical.choice, Quot.sound]
'WalshMobiusRunsDihedralSpectraChallenge.runs_xorConv_neg_one_singular_odd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'WalshMobiusRunsDihedralSpectraChallenge.det_two_runs_andLattice_unimodular' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'WalshMobiusRunsDihedralSpectraChallenge.runs_andLattice_never_posdef' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
