# Formal Verification Audit (`smoothquant-dyadic-minimax`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **10 / 10** | **10 / 10** | **10 / 10** | **95 / 100** |

*Weighted composite: `3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 95 / 100`. See [`README.md`](README.md) for the full For Mathematicians, For Non-Mathematicians, and Prior-Art Context sections.*

## Build & Challenge Checks

```text
$ lake build
✔ [2/10] Built SmoothquantDyadic.Defs (1.7s)
✔ [3/10] Built SmoothquantDyadic.RatOrder (1.4s)
✔ [4/10] Built SmoothquantDyadic.AsymmetricSQ (5.7s)
✔ [5/10] Built SmoothquantDyadic.DyadicBounds (6.9s)
✔ [6/10] Built SmoothquantDyadic.HadamardSynergy (6.9s)
✔ [7/10] Built SmoothquantDyadic (1.4s)
✔ [9/10] Built Solution (1.6s)
Build completed successfully (10 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.4s)
warning: Challenge.lean:31:8: declaration uses `sorry`
warning: Challenge.lean:69:8: declaration uses `sorry`
warning: Challenge.lean:87:8: declaration uses `sorry`
warning: Challenge.lean:108:8: declaration uses `sorry`
warning: Challenge.lean:134:8: declaration uses `sorry`
warning: Challenge.lean:177:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `SmoothquantDyadic/`, `SmoothquantDyadic.lean`, or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'SmoothquantDyadicChallenge.smoothquant_asymmetric_amgm_optimal_scale' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SmoothquantDyadicChallenge.dyadic_smoothquant_perchannel_l2_5_over_4_sharp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SmoothquantDyadicChallenge.dyadic_smoothquant_perchannel_l1_9_over_8_sharp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SmoothquantDyadicChallenge.dyadic_smoothquant_pertensor_5_2_vs_phase_shift_3_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SmoothquantDyadicChallenge.smoothquant_hadamard_noncommutation_separation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SmoothquantDyadicChallenge.channel_outlier_coupling_paradox_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.
