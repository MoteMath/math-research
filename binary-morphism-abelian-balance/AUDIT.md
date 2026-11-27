# Formal Verification Audit (`binary-morphism-abelian-balance`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.0s)
warning: Challenge.lean:17:8: declaration uses `sorry`
warning: Challenge.lean:25:8: declaration uses `sorry`
warning: Challenge.lean:33:8: declaration uses `sorry`
warning: Challenge.lean:42:8: declaration uses `sorry`
warning: Challenge.lean:50:8: declaration uses `sorry`
warning: Challenge.lean:58:8: declaration uses `sorry`
warning: Challenge.lean:65:8: declaration uses `sorry`
warning: Challenge.lean:73:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `BinaryMorphismAbelianBalance/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'BinaryMorphismAbelianBalanceChallenge.stratCert_sound_balance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BinaryMorphismAbelianBalanceChallenge.family_sigmaK_balance' depends on axioms: [propext, Classical.choice, Quot.sound]
'BinaryMorphismAbelianBalanceChallenge.family_sigmaK_prefix_sharp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BinaryMorphismAbelianBalanceChallenge.tauA_balance_infinite' depends on axioms: [propext, Classical.choice, Quot.sound]
'BinaryMorphismAbelianBalanceChallenge.tauB_balance_infinite' depends on axioms: [propext, Classical.choice, Quot.sound]
'BinaryMorphismAbelianBalanceChallenge.mu1_unstrat_impossible' depends on axioms: [propext]
'BinaryMorphismAbelianBalanceChallenge.mu1_strat_balance_infinite' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BinaryMorphismAbelianBalanceChallenge.mu2_strat_balance_infinite' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
