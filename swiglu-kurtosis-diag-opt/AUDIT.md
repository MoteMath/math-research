# Formal Verification Audit (`swiglu-kurtosis-diag-opt`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **9 / 10** | **10 / 10** | **10 / 10** | **93 / 100** |

*Weighted composite: `3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 27 + 18 + 18 + 20 + 10 = 93 / 100`. See [`README.md`](README.md) for the full For Mathematicians, For Non-Mathematicians, and Prior-Art Context sections.*

## Build & Challenge Checks

```text
$ lake clean && lake build
✔ [2/10] Built SwiGluKurtosis.Defs (2.2s)
✔ [3/10] Built SwiGluKurtosis.RatOrder (1.9s)
✔ [4/10] Built SwiGluKurtosis.DiagonalEquiv (5.3s)
✔ [5/10] Built SwiGluKurtosis.BitAllocAndFP4 (5.3s)
✔ [6/10] Built SwiGluKurtosis.KurtosisLaws (5.4s)
✔ [7/10] Built SwiGluKurtosis (1.4s)
✔ [9/10] Built Solution (1.8s)
Build completed successfully (10 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.7s)
warning: Challenge.lean:29:8: declaration uses `sorry`
warning: Challenge.lean:49:8: declaration uses `sorry`
warning: Challenge.lean:77:8: declaration uses `sorry`
warning: Challenge.lean:100:8: declaration uses `sorry`
warning: Challenge.lean:133:8: declaration uses `sorry`
warning: Challenge.lean:156:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide`/`lemma` anywhere in `SwiGluKurtosis/`, `SwiGluKurtosis.lean`, or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'SwiGluKurtosisChallenge.reglu_exact_two_x_kurtosis_multiplication_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SwiGluKurtosisChallenge.correlated_bilinear_kurtosis_amplification_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SwiGluKurtosisChallenge.swiglu_zero_flop_diagonal_equivalence_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SwiGluKurtosisChallenge.swiglu_optimal_diagonal_scale_amgm_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SwiGluKurtosisChallenge.gated_ffn_asymmetric_bit_allocation_dominance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SwiGluKurtosisChallenge.mxfp4_block32_vs_nvfp4_block16_kurtosis_underflow_gap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.
