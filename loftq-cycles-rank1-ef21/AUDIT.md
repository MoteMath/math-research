# Formal Verification Audit (`loftq-cycles-rank1-ef21`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **10 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **91 / 100** |

*Weighted composite: `3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 91 / 100`. See [`README.md`](README.md) for the full For Mathematicians, For Non-Mathematicians, and Prior-Art Context sections.*

## Build & Challenge Checks

```text
$ lake build
✔ [7/11] Built LoftqCyclesRank1.LoftqEnergySaturation (14s)
✔ [8/11] Built LoftqCyclesRank1 (1.0s)
✔ [10/11] Built Solution (2.0s)
Build completed successfully (11 jobs).

$ lake build Challenge
⚠ [3/4] Replayed Challenge
warning: Challenge.lean:26:8: declaration uses `sorry`
warning: Challenge.lean:41:8: declaration uses `sorry`
warning: Challenge.lean:59:8: declaration uses `sorry`
warning: Challenge.lean:75:8: declaration uses `sorry`
warning: Challenge.lean:106:8: declaration uses `sorry`
warning: Challenge.lean:125:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide`/`lemma` anywhere in `LoftqCyclesRank1/`, `LoftqCyclesRank1.lean`, or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'LoftqCyclesRank1Challenge.rank1_onebit_ef21_contraction_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'LoftqCyclesRank1Challenge.rank1_ternary_2x2_contraction_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'LoftqCyclesRank1Challenge.coupled_orthogonal_beats_block_2x2_rotations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'LoftqCyclesRank1Challenge.loftq_alternating_monotone_energy_and_4m2_saturation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'LoftqCyclesRank1Challenge.loftq_explicit_3x3_symmetric_2cycle_witness' depends on axioms: [propext, Quot.sound]
'LoftqCyclesRank1Challenge.loftq_explicit_3x3_symmetric_3cycle_witness' depends on axioms: [propext, Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.
