# Formal Verification Audit (`two-adic-newton-poly-optimality`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.3s)
warning: Challenge.lean:16:8: declaration uses `sorry`
warning: Challenge.lean:20:8: declaration uses `sorry`
warning: Challenge.lean:26:8: declaration uses `sorry`
warning: Challenge.lean:32:8: declaration uses `sorry`
warning: Challenge.lean:39:8: declaration uses `sorry`
warning: Challenge.lean:49:8: declaration uses `sorry`
warning: Challenge.lean:56:8: declaration uses `sorry`
warning: Challenge.lean:65:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings in `lake build`; the only warnings in `lake build Challenge` are the 8 intentional `sorry` placeholders in `Challenge.lean`. Zero `sorry`/`admit`/`native_decide`/`axiom` anywhere in `TwoAdicNewtonPolyOptimality/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'TwoAdicNewtonPolyOptimalityChallenge.fact_exactVal2' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoAdicNewtonPolyOptimalityChallenge.exact_2adic_poly_reciprocal_optimality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TwoAdicNewtonPolyOptimalityChallenge.exact_2adic_poly_optimality_pow2_sub_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TwoAdicNewtonPolyOptimalityChallenge.circuit_mulDepth_optimality_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TwoAdicNewtonPolyOptimalityChallenge.cert_minimal_step_optimality_closed' depends on axioms: [propext, Quot.sound]
'TwoAdicNewtonPolyOptimalityChallenge.recip_minimal_step_dumas' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TwoAdicNewtonPolyOptimalityChallenge.invSqrtS3_popcount_supergain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TwoAdicNewtonPolyOptimalityChallenge.invSqrtS4_eq_S2_double_valuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All 8 headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true`.
