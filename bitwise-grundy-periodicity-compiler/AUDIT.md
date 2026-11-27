# Formal Verification Audit (`bitwise-grundy-periodicity-compiler`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built BitwiseGrundyPeriodicityCompiler.Defs (3.2s)
✔ [3/7] Built BitwiseGrundyPeriodicityCompiler.Theorems (53s)
✔ [4/7] Built BitwiseGrundyPeriodicityCompiler (2.8s)
✔ [6/7] Built Solution (3.4s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.9s)
warning: Challenge.lean:24:8: declaration uses `sorry`
warning: Challenge.lean:30:8: declaration uses `sorry`
warning: Challenge.lean:37:8: declaration uses `sorry`
warning: Challenge.lean:44:8: declaration uses `sorry`
warning: Challenge.lean:52:8: declaration uses `sorry`
warning: Challenge.lean:58:8: declaration uses `sorry`
warning: Challenge.lean:65:8: declaration uses `sorry`
warning: Challenge.lean:72:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the eight intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `BitwiseGrundyPeriodicityCompiler/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'BitwiseGrundyPeriodicityCompilerChallenge.kummer_borrow_popcount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitwiseGrundyPeriodicityCompilerChallenge.borrowCount_le_shift_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitwiseGrundyPeriodicityCompilerChallenge.isWinningMulti_iff_nimSum_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitwiseGrundyPeriodicityCompilerChallenge.dyadic_borrow_wall_periodicity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitwiseGrundyPeriodicityCompilerChallenge.checkCert_sound_grundy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitwiseGrundyPeriodicityCompilerChallenge.G_coprime_p5_period_5' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitwiseGrundyPeriodicityCompilerChallenge.grundyParity_not_eventually_periodic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitwiseGrundyPeriodicityCompilerChallenge.grundyParity_oneHeap_periodic_vs_twoHeap_aperiodic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All eight headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true`; there is no `sorryAx` and no `Lean.ofReduceBool`.
