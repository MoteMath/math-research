# Formal Verification Audit (`nlfsr-holonomy-lasso-debruijn`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built NlfsrHolonomyLassoDebruijn.Defs (9.1s)
✔ [3/7] Built NlfsrHolonomyLassoDebruijn.Theorems (38s)
✔ [4/7] Built NlfsrHolonomyLassoDebruijn (2.3s)
✔ [6/7] Built Solution (2.0s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.9s)
warning: Challenge.lean:18:8: declaration uses `sorry`
warning: Challenge.lean:34:8: declaration uses `sorry`
warning: Challenge.lean:41:8: declaration uses `sorry`
warning: Challenge.lean:45:8: declaration uses `sorry`
warning: Challenge.lean:52:8: declaration uses `sorry`
warning: Challenge.lean:59:8: declaration uses `sorry`
warning: Challenge.lean:66:8: declaration uses `sorry`
warning: Challenge.lean:72:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Exit codes: `lake build` = 0, `lake build Challenge` = 0. Zero errors, zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in the library modules or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'NlfsrHolonomyLassoDebruijnChallenge.transducer_cert_period_doubling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NlfsrHolonomyLassoDebruijnChallenge.theorem1_H111_exact_two_cycles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NlfsrHolonomyLassoDebruijnChallenge.theorem1b_H121_debruijn' depends on axioms: [propext, Classical.choice, Quot.sound]
'NlfsrHolonomyLassoDebruijnChallenge.theorem2a_carry_pump_universal_giant_cycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NlfsrHolonomyLassoDebruijnChallenge.theorem2b_carry_barrier_hermetic' depends on axioms: [propext, Quot.sound]
'NlfsrHolonomyLassoDebruijnChallenge.theorem2c_linear_carry_barrier_exact_log_period' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NlfsrHolonomyLassoDebruijnChallenge.theorem3a_nonprefix_hybrid_nlfsr_debruijn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NlfsrHolonomyLassoDebruijnChallenge.theorem3b_prefix_tap_exact_cycle_splitting' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Exit code: 0. Every headline theorem depends only on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true`.
