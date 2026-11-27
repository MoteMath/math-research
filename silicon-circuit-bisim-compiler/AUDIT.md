# Formal Verification Audit (`silicon-circuit-bisim-compiler`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built SiliconCircuitBisimCompiler.Defs (6.9s)
✔ [3/7] Built SiliconCircuitBisimCompiler.Theorems (100s)
✔ [4/7] Built SiliconCircuitBisimCompiler (1.9s)
✔ [6/7] Built Solution (2.2s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.1s)
warning: Challenge.lean:21:8: declaration uses `sorry`
warning: Challenge.lean:36:8: declaration uses `sorry`
warning: Challenge.lean:58:8: declaration uses `sorry`
warning: Challenge.lean:71:8: declaration uses `sorry`
warning: Challenge.lean:84:8: declaration uses `sorry`
warning: Challenge.lean:95:8: declaration uses `sorry`
warning: Challenge.lean:105:8: declaration uses `sorry`
warning: Challenge.lean:114:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the 8 intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `SiliconCircuitBisimCompiler/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'SiliconCircuitBisimCompilerChallenge.slice_bisim_sound' depends on axioms: [propext, Quot.sound]
'SiliconCircuitBisimCompilerChallenge.prefix_all_topologies_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SiliconCircuitBisimCompilerChallenge.four_way_prefix_adder_equiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SiliconCircuitBisimCompilerChallenge.parallel_gray_decoder_equiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SiliconCircuitBisimCompilerChallenge.three_way_shifter_equiv' depends on axioms: [propext, Quot.sound]
'SiliconCircuitBisimCompilerChallenge.reed_muller_anf_butterfly_all_k' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SiliconCircuitBisimCompilerChallenge.gf4_butterfly_inverse_all_k' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SiliconCircuitBisimCompilerChallenge.bitonic_andOr_eq_oddEven_nand_all_k' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every headline theorem depends exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true` (no `sorryAx`, no `Lean.ofReduceBool`).
