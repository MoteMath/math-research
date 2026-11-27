# Formal Verification Audit (`reversible-circuit-coset-compiler`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built ReversibleCircuitCosetCompiler.Defs (5.3s)
✔ [3/7] Built ReversibleCircuitCosetCompiler.Theorems (35s)
✔ [4/7] Built ReversibleCircuitCosetCompiler (1.4s)
✔ [6/7] Built Solution (1.6s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.6s)
warning: Challenge.lean:8:8: declaration uses `sorry`
warning: Challenge.lean:14:8: declaration uses `sorry`
warning: Challenge.lean:24:8: declaration uses `sorry`
warning: Challenge.lean:30:8: declaration uses `sorry`
warning: Challenge.lean:37:8: declaration uses `sorry`
warning: Challenge.lean:43:8: declaration uses `sorry`
warning: Challenge.lean:47:8: declaration uses `sorry`
warning: Challenge.lean:51:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `ReversibleCircuitCosetCompiler/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'ReversibleCircuitCosetCompilerChallenge.sound_checkWindowEq' depends on axioms: [propext, Classical.choice, Quot.sound]
'ReversibleCircuitCosetCompilerChallenge.sound_coset_order' depends on axioms: [propext, Classical.choice, Quot.sound]
'ReversibleCircuitCosetCompilerChallenge.thm_d6_C_power_mod' depends on axioms: [propext, Classical.choice, Quot.sound]
'ReversibleCircuitCosetCompilerChallenge.thm_b3_AST_power_mod' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ReversibleCircuitCosetCompilerChallenge.thm_ptoff_dihedral_family' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ReversibleCircuitCosetCompilerChallenge.thm_t3_sharp_collapse_w2' depends on axioms: [propext, Quot.sound]
'ReversibleCircuitCosetCompilerChallenge.mut_window_out_of_bounds' depends on axioms: [propext, Quot.sound]
'ReversibleCircuitCosetCompilerChallenge.mut_order_lower_inflated' depends on axioms: [propext, Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
