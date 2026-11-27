# Formal Verification Audit (`bitwise-expander-walsh-gaps`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built BitwiseExpanderWalshGaps.Defs (12s)
✔ [3/7] Built BitwiseExpanderWalshGaps.Theorems (3.2s)
✔ [4/7] Built BitwiseExpanderWalshGaps (1.5s)
✔ [6/7] Built Solution (1.6s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.7s)
warning: Challenge.lean:8:8: declaration uses `sorry`
warning: Challenge.lean:14:8: declaration uses `sorry`
warning: Challenge.lean:20:8: declaration uses `sorry`
warning: Challenge.lean:30:8: declaration uses `sorry`
warning: Challenge.lean:39:8: declaration uses `sorry`
warning: Challenge.lean:47:8: declaration uses `sorry`
warning: Challenge.lean:54:8: declaration uses `sorry`
warning: Challenge.lean:61:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `BitwiseExpanderWalshGaps/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'BitwiseExpanderWalshGapsChallenge.wht_plancherel' depends on axioms: [propext, Classical.choice, Quot.sound]
'BitwiseExpanderWalshGapsChallenge.dirichletForm_eq_wht' depends on axioms: [propext, Classical.choice, Quot.sound]
'BitwiseExpanderWalshGapsChallenge.expander_mixing_lemma_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'BitwiseExpanderWalshGapsChallenge.mod3_exact_spectral_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'BitwiseExpanderWalshGapsChallenge.fib_expander_mixing_lemma' depends on axioms: [propext, Classical.choice, Quot.sound]
'BitwiseExpanderWalshGapsChallenge.witness_fib_k4' depends on axioms: [propext, Classical.choice, Quot.sound]
'BitwiseExpanderWalshGapsChallenge.sharpness_mod2_always_disconnected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitwiseExpanderWalshGapsChallenge.witness_mod3_eml_k5' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
