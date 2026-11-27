# Formal Verification Audit (`mersenne-fermat-bitfold-crt`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.7s)
warning: Challenge.lean:16:8: declaration uses `sorry`
warning: Challenge.lean:22:8: declaration uses `sorry`
warning: Challenge.lean:29:8: declaration uses `sorry`
warning: Challenge.lean:37:8: declaration uses `sorry`
warning: Challenge.lean:42:8: declaration uses `sorry`
warning: Challenge.lean:47:8: declaration uses `sorry`
warning: Challenge.lean:52:8: declaration uses `sorry`
warning: Challenge.lean:58:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings in `lake build`; the only warnings in `lake build Challenge` are the 8 intentional `sorry` placeholders in `Challenge.lean`. Zero `sorry`/`admit`/`native_decide`/`axiom` anywhere in `MersenneFermatBitfoldCrt/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'MersenneFermatBitfoldCrtChallenge.mersenne_exact_threshold' depends on axioms: [propext, Quot.sound]
'MersenneFermatBitfoldCrtChallenge.fermat_exact_envelope' depends on axioms: [propext, Classical.choice, Quot.sound]
'MersenneFermatBitfoldCrtChallenge.total_carry_conservation' depends on axioms: [propext, Classical.choice, Quot.sound]
'MersenneFermatBitfoldCrtChallenge.tower_factorization' depends on axioms: [propext, Quot.sound]
'MersenneFermatBitfoldCrtChallenge.idemM_popcount' depends on axioms: [propext, Classical.choice, Quot.sound]
'MersenneFermatBitfoldCrtChallenge.idem_partition_of_unity' depends on axioms: [propext, Quot.sound]
'MersenneFermatBitfoldCrtChallenge.dyadic_butterfly_exact' depends on axioms: [propext, Quot.sound]
'MersenneFermatBitfoldCrtChallenge.mersenne_exact_min_depth_dichotomy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All 8 headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true`.
