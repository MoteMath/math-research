# Bit-Sliced Synchronous Automaton Reflection Engine - kernel-checked finite automaton certificates discharging all-width BitVec arithmetic and Gray-code theorems (`bit-sliced-synchronous-automata`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **8 / 10** | **9 / 10** | **9 / 10** | **10 / 10** | **86 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): A complete, sorry-free, pure-Init (zero Mathlib) Lean 4 formalization of a bit-sliced synchronous automaton reflection compiler (SyncAutomaton, AutomatonCert, bvProp_cert_sound) lifting finite kernel-decidable reachability certificates to universally quantified all-width BitVec w theorems for 3-operand carry-save quarter-sums, nested-average sandwiches, Gray-code Zeckendorf sparsity, and signed/unsigned floor averages.*

## For Mathematicians

**Mechanism Name:** **BitSync** — Latency-Aligned Pipelined Bit-Sliced Synchronous Automaton Reflection Compiler (`AutomatonCert` + `checkCert` + `bvProp_cert_sound`).

## For Non-Mathematicians

A complete, sorry-free, pure-Init (zero Mathlib) Lean 4 formalization of a bit-sliced synchronous automaton reflection compiler (SyncAutomaton, AutomatonCert, bvProp_cert_sound) lifting finite kernel-decidable reachability certificates to universally quantified all-width BitVec w theorems for 3-operand carry-save quarter-sums, nested-average sandwiches, Gray-code Zeckendorf sparsity, and signed/unsigned floor averages.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `BitSlicedSynchronousAutomata/Theorems.lean`, definitions in `BitSlicedSynchronousAutomata/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `checkCert_sound` | Theorem 1 (generic synchronous automaton certificate soundness across all stream lengths `w`). |
| `bvProp_cert_sound` | Theorem 2 (master reflection soundness meta-theorem: finite certificate proves `φ.eval w env = true` for all `w` and all `BitVec w` tuples). |
| `thm_signed_quarter_sum_net_overflow_iff` | Theorem 3 (3-operand signed carry-save quarter-sum exact net-overflow biconditional for all `w ≥ 2`). |
| `thm_unsigned_quarter_sum_no_overflow_iff` | Theorem 4 (3-operand unsigned carry-save quarter-sum exact no-overflow biconditional for all `w ≥ 2`). |
| `thm_signed_eq_unsigned_quarter_sum_iff` | Theorem 5 (3-operand signed vs. unsigned quarter-sum equality iff all three operands are non-negative). |
| `thm_signed_quarter_sum_mod_reconstruction` | Theorem 6 (exact mod-`2^w` Euclidean reconstruction of 3-operand signed quarter-sum under arbitrary overflow). |
| `thm_nested_avg_vs_quarter_sum_sandwich` | Theorem 7 (nested overflow-free average minus unsigned quarter-sum trapped in `[z >>> 2, (z >>> 2) + 1]`). |
| `thm_gray_triple_zeckendorf_iff` | Theorem 8 (Gray-code `3 * x` exact Zeckendorf-sparsity biconditional for all `w`). |

## Prior-Art Context

- - **Relation to Classical Literature & Proof Assistants:** - Decision procedures for Presburger/bit-vector arithmetic via LSB-first finite automata go back to Büchi (1960), Boudet–Comon, and Mona. In Lean 4 specifically, the closest prior art is LeanMLIR's `bv_automata` (width-polymorphic bit-vector decision via automata) alongside fixed-width SAT bit-blasters (`bv_decide`). For the 2-operand overflow-free average and Gray-code identities, classic references include Henry S. Warren Jr., *Hacker's Delight* (2nd ed., 2012, Ch. 2 & Ch. 13). - **What is new here:** 1. **Compositional Latency-Aligned Pipelining for Right Shifts (`ushr1`, `ashr1`)
- Built against `leanprover/lean4:v4.34.1` (pure `Init` stack; `enable_nanoda: true` in `comparator.json`); `scripts/explore_and_verify.py` re-evaluates small instances in exact integer arithmetic (it proves nothing by itself).

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).