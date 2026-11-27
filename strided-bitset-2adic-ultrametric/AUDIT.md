# Formal Verification Audit (`strided-bitset-2adic-ultrametric`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built StridedBitset2adicUltrametric.Defs (2.4s)
✔ [3/7] Built StridedBitset2adicUltrametric.Theorems (59s)
✔ [4/7] Built StridedBitset2adicUltrametric (2.1s)
✔ [6/7] Built Solution (2.2s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.3s)
warning: Challenge.lean:8:8: declaration uses `sorry`
warning: Challenge.lean:16:8: declaration uses `sorry`
warning: Challenge.lean:32:8: declaration uses `sorry`
warning: Challenge.lean:41:8: declaration uses `sorry`
warning: Challenge.lean:48:8: declaration uses `sorry`
warning: Challenge.lean:53:8: declaration uses `sorry`
warning: Challenge.lean:58:8: declaration uses `sorry`
warning: Challenge.lean:67:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `StridedBitset2adicUltrametric/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'StridedBitset2adicUltrametricChallenge.maskRepCount_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
'StridedBitset2adicUltrametricChallenge.ultrametric_odd_parity_lift' depends on axioms: [propext, Quot.sound]
'StridedBitset2adicUltrametricChallenge.nonbinomial_3S2_add_N_v2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'StridedBitset2adicUltrametricChallenge.even_window_strided_v2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'StridedBitset2adicUltrametricChallenge.upper_endpoint_v2_collapse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'StridedBitset2adicUltrametricChallenge.pow2_strided_r_invariance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'StridedBitset2adicUltrametricChallenge.witness_three_way_tie_survives' depends on axioms: [propext]
'StridedBitset2adicUltrametricChallenge.sharpness_above_window_cancellation' depends on axioms: [propext]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
