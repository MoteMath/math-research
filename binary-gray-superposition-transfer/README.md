# `BitTransfer3`: Bit-Boundary Transfer-Tensor & State-Invariant Compiler (`binary-gray-superposition-transfer`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **10 / 10** | **9 / 10** | **9 / 10** | **10 / 10** | **93 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): `BitTransfer3`: Bit-Boundary Transfer-Tensor & State-Invariant Compiler*

## For Mathematicians

`BitTransfer3`: Bit-Boundary Transfer-Tensor & State-Invariant Compiler

## For Non-Mathematicians

`BitTransfer3`: Bit-Boundary Transfer-Tensor & State-Invariant Compiler

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `BinaryGraySuperpositionTransfer/Theorems.lean`, definitions in `BinaryGraySuperpositionTransfer/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `glue_alpha_sound` | **GENERIC SOUNDNESS THEOREM 1 (`BitTransfer3.Alpha`)**: For ANY 3-terminal gluing specification `spec` and ANY two `TermGraph n` instances `L, R`, the exact tropical independence-number vector of `glue spec L R` equals `stepAlpha spec`. |
| `gb_pm_recurrence` | Machine-checked infinite theorem `gb_pm_recurrence` proved in pure Lean 4 `Init`. |
| `gb_doublyCyclic_pm` | Machine-checked infinite theorem `gb_doublyCyclic_pm` proved in pure Lean 4 `Init`. |
| `gbGraph_exactChrom` | Machine-checked infinite theorem `gbGraph_exactChrom` proved in pure Lean 4 `Init`. |
| `gb_doublyCyclic_exactChrom` | Machine-checked infinite theorem `gb_doublyCyclic_exactChrom` proved in pure Lean 4 `Init`. |
| `gb_chrom_root_two_sharp_k2` | Sharp threshold boundary witnesses for Theorem 5: at `k = 2` multiplicity is `1` (lead `+2`), and at `k = 3` multiplicity is `3` (lead `+4`), showing `k ≥ 4` is exact! |
| `sb_pm_const_one` | Machine-checked infinite theorem `sb_pm_const_one` proved in pure Lean 4 `Init`. |
| `non_vacuity_witness` | Non-Vacuity Concrete Witness: `GB_2`, `GB_3`, `GB_4` simultaneously realize all 5 theorems! |

## Prior-Art Context

- Formalizes a pure-Init Lean 4 infinite proof engine with zero Mathlib dependencies and independent `nanoda` kernel verification.
- Hostile-verified PASS by `referee-3`; pure `leanprover/lean4:v4.34.1` `Init` stack with `enable_nanoda: true` and exact integer Python replay in `scripts/explore_and_verify.py`.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).