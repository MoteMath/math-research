# `BitTransfer3`: Bit-Boundary Transfer-Tensor & State-Invariant Compiler (`binary-gray-superposition-transfer`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **10 / 10** | **9 / 10** | **9 / 10** | **10 / 10** | **93 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): `BitTransfer3`: Bit-Boundary Transfer-Tensor & State-Invariant Compiler*

## For Mathematicians

`GB_k` is the graph on the vertices `{0, ..., 2^k - 1}` whose edges are the binary path edges `{i, i+1}` together with the Gray-code path edges `{gray i, gray (i+1)}`, where `gray i = i XOR (i >> 1)` (`gbAdj` in `Defs.lean`). `BitTransfer3` is a transfer-tensor engine for 3-terminal graph families glued along the most significant bit; the exact perfect-matching count, independence number and chromatic count of `GB_k` are tied to small transfer vectors for all `k`.

## For Non-Mathematicians

The package proves facts about one explicit family of graphs (each vertex is a `k`-bit number; two numbers are joined if they differ by 1, or are consecutive in the Gray code) for every size `k` at once, plus a few concrete small cases.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `BinaryGraySuperpositionTransfer/Theorems.lean`, definitions in `BinaryGraySuperpositionTransfer/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `glue_alpha_sound` | **GENERIC SOUNDNESS THEOREM 1 (`BitTransfer3.Alpha`)**: For ANY 3-terminal gluing specification `spec` and ANY two `TermGraph n` instances `L, R`, the exact tropical independence-number vector of `glue spec L R` equals `stepAlpha spec`. |
| `gb_pm_recurrence` | For all `k >= 3`, the number of perfect matchings of `GB_{k+1}` equals `PM(GB_k)^2 + PM(GB_{k-1})^2`. |
| `gb_doublyCyclic_pm` | For all `k >= 2`, the doubly-cyclic closure of `GB_k` (`gbDoublyCyclic`, `GB_k` plus the two closing edges defined in `Defs.lean`) has exactly `2 * pmSeq k + 1` perfect matchings, where `pmSeq` is the sequence `a(1) = a(2) = 1`, `a(k+1) = a(k)^2 + a(k-1)^2`. |
| `gbGraph_exactChrom` | For all `k >= 2` and `q`, the number of proper `q`-colourings of `GB_k` equals the integer polynomial `gbChromPoly k` evaluated at `q`. |
| `gb_doublyCyclic_exactChrom` | The same colouring-count identity for the doubly-cyclic closure of `GB_k`, for all `k >= 2` and `q`. |
| `gb_chrom_root_two_sharp_k2` | Finite instance: `gbChromPoly 2 = 2(q-2) + (q-2)^2 r(q)` for some integer polynomial `r` (vanishing order 1 at `q = 2`, leading coefficient `2`). The `k = 3` case and any claim about `k >= 4` are not part of this statement. |
| `sb_pm_const_one` | For every depth `d`, the ablated family `SB` (the Gray bridge dropped from the gluing, `recGraph sbSpec d`) has exactly one perfect matching. |
| `non_vacuity_witness` | Machine-checked finite instance (a concrete computation, not one of the universal statements): `PM(GB_4) = 5`, `PM(doubly-cyclic GB_4) = 11`, `alpha(GB_4) = 7`, `alpha(doubly-cyclic GB_4) = 6`, and the colouring counts of `GB_3` at `q = 2, 3` are `0` and `60`. |

## Prior-Art Context

- Formalizes a pure-Init Lean 4 infinite proof engine with zero Mathlib dependencies and independent `nanoda` kernel verification.
- Built against `leanprover/lean4:v4.34.1` (pure `Init` stack; `enable_nanoda: true` in `comparator.json`); `scripts/explore_and_verify.py` re-evaluates small instances in exact integer arithmetic (it proves nothing by itself).

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).