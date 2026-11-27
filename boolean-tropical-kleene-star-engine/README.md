# Boolean Tropical Kleene Star Engine - Conway-Schur Kleene stars over Kozen semirings applied to bit-twiddle graphs, ripple-carry ALU graphs and XOR walks for every dimension 2^k (`boolean-tropical-kleene-star-engine`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **8 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **84 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): A complete, sorry-free, pure-Init (zero Mathlib) Lean 4 formalization of a polymorphic Kozen Kleene-semiring matrix-star engine (block Conway-Schur and rank-one Sherman-Morrison star) with a reusable bit-doubling tower, instantiated on tropical, Boolean and XOR-set semirings for exact all-dimension results on bit-twiddle graphs, the asymmetric ripple-carry ALU graph (diameter 2^(k+1) - k - 2) and the non-collapsing active XOR-walk star with cycle subspace and max-XOR bottleneck.*

## For Mathematicians

**Mechanism Name:** **Bit-Sliced Kleene-Schur Engine (`BSKSE`)** — an algebraic $2 \times 2$ block Conway–Schur and Rank-1 Kleene Sherman–Morrison–Woodbury renormalization engine for $2^k \times 2^k$ bit-indexed matrices over arbitrary Kozen Kleene semirings.

## For Non-Mathematicians

A complete, sorry-free, pure-Init (zero Mathlib) Lean 4 formalization of a polymorphic Kozen Kleene-semiring matrix-star engine (block Conway-Schur and rank-one Sherman-Morrison star) with a reusable bit-doubling tower, instantiated on tropical, Boolean and XOR-set semirings for exact all-dimension results on bit-twiddle graphs, the asymmetric ripple-carry ALU graph (diameter 2^(k+1) - k - 2) and the non-collapsing active XOR-walk star with cycle subspace and max-XOR bottleneck.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `BooleanTropicalKleeneStarEngine/Theorems.lean`, definitions in `BooleanTropicalKleeneStarEngine/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `block_conway_schur_star` | Theorem 1 (Block Conway-Schur star): over any Kozen Kleene semiring, the Kleene star of a 2x2 block matrix is given by the Conway-Schur block formula from the stars of D and the Schur complement. |
| `bmi_trop_star_exact` | Theorem 2 (Tropical bit-twiddle star): for every k and cost function c, the tropical Kleene star of the bit-twiddle graph is its exact weighted distance matrix. |
| `bmiBoolPow_iff` | Theorem 3 (Boolean power law): for k >= 1, entry (x, y) of the t-th Boolean power is true iff the distance is at most t and the parity popcount x + popcount y + t is even. |
| `bmi_bool_star_eq_allTrue` | Theorem 4 (Boolean star): the Boolean Kleene star of the bit-twiddle graph is the all-true matrix. |
| `alu_exact_diameter_and_asymmetry` | Theorem 5 (ALU exact diameter and asymmetry): the ripple-carry ALU graph has distances bounded by 2^(k+1) - k - 2, attained from 0 to the maximum word, while the reverse distance is only k. |
| `bmi_xor_star_exact` | Theorem 6 (Active XOR-walk star): the active Sherman-Morrison XOR-walk matrix star equals the explicit non-collapsing star bmiXorStar for every k. |
| `bmi_xor_cycle_subspace` | Theorem 7 (XOR cycle subspace): v is reachable by a closed XOR walk at the origin iff v lies in the explicit subspace V_k. |
| `bmi_xor_max_bottleneck_exact` | Theorem 8 (Max-XOR bottleneck): the bottleneck of the XOR-walk star equals the alternating even mask, exactly attained and exactly maximal. |

## Prior-Art Context

- - **Classical foundations acknowledged:** Kozen's Kleene algebra axioms (1994), Conway's $2 \times 2$ block star-matrix identity (1971), and the classical Sherman–Morrison formula over fields are standard background. - **Contribution (prior-art status not established; no search was recorded):** 1. **Kleene-Algebra Rank-1 Sherman–Morrison + Bit-Sliced Corner-Bridge Tower (`BSKSE`)** formalized polymorphically in core Lean 4 with zero Mathlib and zero `Fin` casts (`Fin (n * 2)` matching `2 ^ (k + 1)` definitionally), unifying **both** collapsing integral semirings (`Bool`, `TropNat`) and **non-collapsing** non-integral semirings (`XorSet` + diagonal gauge similarity). 2. **The BM
- Built against `leanprover/lean4:v4.34.1` (pure `Init` stack; `enable_nanoda: true` in `comparator.json`); `scripts/explore_and_verify.py` re-evaluates small instances in exact integer arithmetic (it proves nothing by itself).

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).