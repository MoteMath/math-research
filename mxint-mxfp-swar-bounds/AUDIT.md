# Formal Verification Audit (`mxint-mxfp-swar-bounds`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **10 / 10** | **9 / 10** | **10 / 10** | **10 / 10** | **95 / 100** |

*Weighted composite: `3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 95 / 100`. See [`README.md`](README.md) for the full For Mathematicians, For Non-Mathematicians, and Prior-Art Context sections.*

## Build & Challenge Checks

```text
$ lake build
✔ [6/10] Built MxintMxfpSwar.HalfIntAsym (164s)
✔ [7/10] Built MxintMxfpSwar (236s)
✔ [9/10] Built Solution (285s)
Build completed successfully (10 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (44s)
warning: Challenge.lean:32:8: declaration uses `sorry`
warning: Challenge.lean:57:8: declaration uses `sorry`
warning: Challenge.lean:96:8: declaration uses `sorry`
warning: Challenge.lean:126:8: declaration uses `sorry`
warning: Challenge.lean:151:8: declaration uses `sorry`
warning: Challenge.lean:171:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide`/`lemma` anywhere in `MxintMxfpSwar/`, `MxintMxfpSwar.lean`, or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'MxintMxfpSwarChallenge.mxint_all_b_ef21_contraction_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'MxintMxfpSwarChallenge.mxint_vs_mxfp_exact_blocksize_crossover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MxintMxfpSwarChallenge.kulisch_mxint_zero_overflow_swar_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MxintMxfpSwarChallenge.half_integer_zero_free_o_one_over_b_collapse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MxintMxfpSwarChallenge.mxint4_asym_beats_sym_crossover_b16' depends on axioms: [propext, Classical.choice, Quot.sound]
'MxintMxfpSwarChallenge.mxint_exact_integer_associativity' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.
