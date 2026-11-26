# Formal Verification Audit (`spec-decoding-ot-bounds`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **10 / 10** | **8 / 10** | **10 / 10** | **91 / 100** |

Weighted score: `3 * 9 + 2 * 9 + 2 * 10 + 2 * 8 + 10 = 91 / 100`.

## Build & Challenge Checks

```text
$ lake build
✔ [2/10] Built SpecDecodingOt.Defs (1.5s)
✔ [3/10] Built SpecDecodingOt.RatHelpers (1.6s)
✔ [4/10] Built SpecDecodingOt.ReversibleBitVec (6.1s)
✔ [5/10] Built SpecDecodingOt.MultidraftOT (6.2s)
✔ [6/10] Built SpecDecodingOt.QuantizedDraft (6.1s)
✔ [7/10] Built SpecDecodingOt (1.0s)
✔ [9/10] Built Solution (1.2s)
Build completed successfully (10 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.1s)
warning: Challenge.lean:41:8: declaration uses `sorry`
warning: Challenge.lean:62:8: declaration uses `sorry`
warning: Challenge.lean:83:8: declaration uses `sorry`
warning: Challenge.lean:97:8: declaration uses `sorry`
warning: Challenge.lean:113:8: declaration uses `sorry`
warning: Challenge.lean:122:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide`/`lemma` declarations anywhere in `SpecDecodingOt/`, `SpecDecodingOt.lean`, or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'SpecDecodingOtChallenge.multidraft_corr_vs_iid_exact_gaps' depends on axioms: [propext, Classical.choice, Quot.sound]
'SpecDecodingOtChallenge.cyclic_madow_optimality_refutation_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpecDecodingOtChallenge.quantized_draft_loss_k1_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'SpecDecodingOtChallenge.quantized_draft_loss_multidraft_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpecDecodingOtChallenge.modular_bitvec_reversible_exact_inverse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpecDecodingOtChallenge.symplectic_float_reversible_unimodular' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `enable_nanoda: true`.
