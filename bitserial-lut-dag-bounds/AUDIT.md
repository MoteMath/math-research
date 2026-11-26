# Formal Verification Audit (`bitserial-lut-dag-bounds`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **9 / 10** | **10 / 10** | **10 / 10** | **93 / 100** |

*Weighted composite: `3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 3*9 + 2*9 + 2*9 + 2*10 + 10 = 93 / 100`. See [`README.md`](README.md) for the full For Mathematicians, For Non-Mathematicians, and Prior-Art Context sections.*

## Build & Challenge Checks

```text
$ lake build
✔ [9/10] Built Solution (1.2s)
Build completed successfully (10 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.4s)
warning: Challenge.lean:34:8: declaration uses `sorry`
warning: Challenge.lean:52:8: declaration uses `sorry`
warning: Challenge.lean:87:8: declaration uses `sorry`
warning: Challenge.lean:115:8: declaration uses `sorry`
warning: Challenge.lean:142:8: declaration uses `sorry`
warning: Challenge.lean:167:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide`/`lemma` anywhere in `BitSerialLutDag/`, `BitSerialLutDag.lean`, or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'BitSerialLutDagChallenge.binary_lut_dag_lower_bound_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'BitSerialLutDagChallenge.tmac_depth2_optimal_12_vs_14_circuit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitSerialLutDagChallenge.ternary_lut_dag_bounds_and_symmetry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitSerialLutDagChallenge.popcnt_zero_lut_exact_bitserial_dot_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitSerialLutDagChallenge.lut_vs_popcnt_amortization_crossover_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitSerialLutDagChallenge.tmac_int16_overflow_threshold_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.
