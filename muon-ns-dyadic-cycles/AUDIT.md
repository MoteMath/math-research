# Formal Verification Audit (`muon-ns-dyadic-cycles`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **10 / 10** | **9 / 10** | **10 / 10** | **10 / 10** | **95 / 100** |

*Weighted composite: `3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 3*9 + 2*10 + 2*9 + 2*10 + 10 = 95 / 100`. See [`README.md`](README.md) for the full For Mathematicians, For Non-Mathematicians, and Prior-Art Context sections.*

## Build & Challenge Checks

```text
$ lake build
✔ [2/10] Built MuonNsDyadic.Defs (1.7s)
✔ [3/10] Built MuonNsDyadic.RatOrder (1.2s)
✔ [4/10] Built MuonNsDyadic.OvershootPareto (2.7s)
✔ [5/10] Built MuonNsDyadic.OptimalDyadic (19s)
✔ [6/10] Built MuonNsDyadic.JordanCycles (54s)
✔ [7/10] Built MuonNsDyadic (1.1s)
✔ [9/10] Built Solution (1.3s)
Build completed successfully (10 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.3s)
warning: Challenge.lean:34:8: declaration uses `sorry`
warning: Challenge.lean:60:8: declaration uses `sorry`
warning: Challenge.lean:99:8: declaration uses `sorry`
warning: Challenge.lean:122:8: declaration uses `sorry`
warning: Challenge.lean:140:8: declaration uses `sorry`
warning: Challenge.lean:166:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide`/`lemma` anywhere in `MuonNsDyadic/`, `MuonNsDyadic.lean`, or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'MuonNsDyadicChallenge.jordan_bf16_nonunit_sum_and_period2_limit_cycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MuonNsDyadicChallenge.jordan_bf16_parenthesization_bifurcation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MuonNsDyadicChallenge.fp8_e4m3fn_optimal_quintic_exact_zero_error' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MuonNsDyadicChallenge.bf16_optimal_dyadic_quintic_one_ulp_confinement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MuonNsDyadicChallenge.polar_express_bf16_fp8_one_ulp_overshoot_cliff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MuonNsDyadicChallenge.stationary_quintic_slope_vs_fixedpoint_pareto' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.
