# Formal Verification Audit (`f2-rank-bitwise-matrix-automata`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.8s)
warning: Challenge.lean:17:8: declaration uses `sorry`
warning: Challenge.lean:23:8: declaration uses `sorry`
warning: Challenge.lean:29:8: declaration uses `sorry`
warning: Challenge.lean:39:8: declaration uses `sorry`
warning: Challenge.lean:45:8: declaration uses `sorry`
warning: Challenge.lean:51:8: declaration uses `sorry`
warning: Challenge.lean:57:8: declaration uses `sorry`
warning: Challenge.lean:62:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `F2RankBitwiseMatrixAutomata/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'F2RankBitwiseMatrixAutomataChallenge.hasRank_kerCount' depends on axioms: [propext, Classical.choice, Quot.sound]
'F2RankBitwiseMatrixAutomataChallenge.hasRank_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'F2RankBitwiseMatrixAutomataChallenge.hasRank_isotropic_rank1_decouple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'F2RankBitwiseMatrixAutomataChallenge.M0_gray_nullity' depends on axioms: [propext, Classical.choice, Quot.sound]
'F2RankBitwiseMatrixAutomataChallenge.M0_kerCount' depends on axioms: [propext, Classical.choice, Quot.sound]
'F2RankBitwiseMatrixAutomataChallenge.M0_invertible_iff_pow2' depends on axioms: [propext, Classical.choice, Quot.sound]
'F2RankBitwiseMatrixAutomataChallenge.H_kerCount' depends on axioms: [propext, Classical.choice, Quot.sound]
'F2RankBitwiseMatrixAutomataChallenge.H0_invertible_iff_base4' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
