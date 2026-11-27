# Exact Dyadic Sum-of-Squares and Telescoping Flux Compiler - kernel-checked Schmudgen-Farkas and infinite-dimensional cyclic/open flux positivity certificates (`dyadic-sos-farkas-flux-compiler`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **8 / 10** | **9 / 10** | **9 / 10** | **10 / 10** | **89 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): A complete, sorry-free, pure-Init (zero Mathlib) Lean 4 formalization of an exact dyadic Sum-of-Squares, Schmudgen-Farkas Positivstellensatz, and cyclic/open telescoping flux compiler discharging infinite-dimensional polynomial, hypercube 3-pattern density, Boolean frustrated-triangle, and parametric/open-boundary discrete biharmonic inequalities for all n >= 1, plus nonlinear Positivstellensatz refutations.*

## For Mathematicians

**Mechanism:** *Exact $\mathbb{Z}[1/2]$ Dyadic Gram–$LDL^T$ / Schmüdgen–Farkas Positivstellensatz Compiler with Cyclic & Open Telescoping-Flux Infinite-Dimensional Lifters*

## For Non-Mathematicians

A complete, sorry-free, pure-Init (zero Mathlib) Lean 4 formalization of an exact dyadic Sum-of-Squares, Schmudgen-Farkas Positivstellensatz, and cyclic/open telescoping flux compiler discharging infinite-dimensional polynomial, hypercube 3-pattern density, Boolean frustrated-triangle, and parametric/open-boundary discrete biharmonic inequalities for all n >= 1, plus nonlinear Positivstellensatz refutations.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `DyadicSosFarkasFluxCompiler/Theorems.lean`, definitions in `DyadicSosFarkasFluxCompiler/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `farkasSOS_sound` | Theorem 1 (exact dyadic Schmüdgen-Farkas Positivstellensatz soundness over all dyadic assignments). |
| `cyclic_flux_sound_int` | Theorem 2 (infinite-dimensional cyclic telescoping flux soundness over `Int` for all `n ≥ 1`). |
| `thm1_asym_skew_quartic_cyclic_int` | Theorem 3 (infinite-dimensional asymmetric skew-quartic cyclic inequality for all `n ≥ 1`). |
| `thm3b_hypercube_asym_3pattern` | Theorem 4 (sharp genuinely-cubic hypercube `[0, 1]^n` asymmetric 3-pattern density inequality for all `n ≥ 1`). |
| `thm4_boolean_frustrated_triangle` | Theorem 5 (sharp Boolean `{0, 1}^n` frustrated-triangle inequality using all four compiler layers). |
| `thm5a_parametric_biharmonic_cyclic_int` | Theorem 6 (doubly-infinite parametric discrete biharmonic-Sobolev cyclic inequality for all `n ≥ 1` and all `t : Int`). |
| `thm5b_open_biharmonic_stabilized_int` | Theorem 7 (sharp open-boundary discrete biharmonic stabilization inequality for all `n` and `x : Nat → Int`). |
| `thm6_nonlinear_farkas_refutation` | Theorem 8 (nonlinear exact dyadic Positivstellensatz refutation of `x^2 + y^2 ≤ 1 ∧ x + y ≥ 23/16`). |

## Prior-Art Context

- - **Relation to Classical SOS/Positivstellensatz Tactics & SDP Rounding Literature:** - Fixed-dimension polynomial SOS/Positivstellensatz checkers exist in proof assistants (e.g., Harrison's `SOS` in HOL Light, Besson's `Micromega`/`psatz` in Coq, and Lean/Mathlib's `polyrith`/`nlinarith`). - Rational SOS rounding and validated SDP certification in fixed dimension were studied by **Peyrl & Parrilo (2008)** (*Computing sum of squares decompositions with rational coefficients*, Theoretical Computer Science 409(2):269–281, projecting floating-point Gram matrices onto rational subspaces and checking exact rational $LDL^T$).
- Built against `leanprover/lean4:v4.34.1` (pure `Init` stack; `enable_nanoda: true` in `comparator.json`); `scripts/explore_and_verify.py` re-evaluates small instances in exact integer arithmetic (it proves nothing by itself).

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).