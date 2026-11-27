# Bit-Level k-Induction and IC3 Invariant Engine - width-uniform finite certificates proving all-width, all-time hardware safety (`bit-level-kind-ic3-invariants`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **8 / 10** | **9 / 10** | **9 / 10** | **10 / 10** | **86 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): A complete, sorry-free, pure-Init (zero Mathlib) Lean 4 formalization of a width-uniform bit-level k-induction and IC3 invariant-certificate engine (checkKIndIC3_sound), lifting finite kernel-decidable proof obligations to all bit-widths w >= 1 and all time steps t for wrap-safe Gray counters, carry-save accumulators, 3-stage carry-defect pipelines, hybrid sparse adders, and 1-ULP averaging filters.*

## For Mathematicians

**Mechanism Name:** *Width-Uniform Bit-Sliced $k$-Induction & IC3/PDR Invariant-Certificate Engine (`KIndIC3`)* Classical hardware model checkers ($k$-induction, Sheeran–Singh–Stålmarck 2000; IC3/PDR, Bradley 2011) verify safety over **unbounded time** $\forall t \in \mathbb{N}$ at a **single fixed bit-width** $w$ (e.g., $w = 32$ or $64$) by bit-blasting the circuit to a propositional SAT solver. Proving safety simultaneously across **all bit-widths** $w \ge 1$ and **all clock cycles** $t \in \mathbb{N}$ (the doubly-infinite domain $\mathbb{N} _ {\ge 1} \times \mathbb{N}$) normally requires manual word-level SMT or hand-crafted induction proofs per circuit. `KIndIC3` bridges **finite binary certificates $\to$ doubly-infinite `BitVec w` safety theorems** via a **double-induction reflection compiler** implemented completely inside standalone Lean 4.34.1 (zero Mathlib, zero `native_decide`, zero `Prop` fields in certificates): 1. **Width-U

## For Non-Mathematicians

A complete, sorry-free, pure-Init (zero Mathlib) Lean 4 formalization of a width-uniform bit-level k-induction and IC3 invariant-certificate engine (checkKIndIC3_sound), lifting finite kernel-decidable proof obligations to all bit-widths w >= 1 and all time steps t for wrap-safe Gray counters, carry-save accumulators, 3-stage carry-defect pipelines, hybrid sparse adders, and 1-ULP averaging filters.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `BitLevelKindIc3Invariants/Theorems.lean`, definitions in `BitLevelKindIc3Invariants/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `checkOblig_sound` | Theorem 1 (width-uniform obligation checker soundness across all `w ≥ 1`, initial states, and input streams). |
| `checkKIndIC3_sound` | Theorem 2 (master k-induction + IC3 soundness meta-theorem: finite certificate certifies `Safe sys prop` for all `w ≥ 1` and all `t`). |
| `thm1_wrapSafeGray_safety` | Theorem 3 (wrap-safe Gray counter safety for all `w ≥ 1` and all `t`). |
| `thm2_carrySave_safety` | Theorem 4 (carry-save accumulator equivalence against reference adder for all `w ≥ 1`, all input streams `u`, and all `t`). |
| `thm3_carryDefectPipeline_zero` | Theorem 5 (3-stage carry-defect pipeline zero-defect invariant via pure `k = 3` induction for all `w ≥ 1` and all `t`). |
| `thm4_hybridSparseAdder_msb` | Theorem 6 (hybrid sparse adder MSB equivalence via combined IC3 + `k = 2` induction for all `w ≥ 1`, all `u`, and all `t`). |
| `thm5_avgFilter_oneULP` | Theorem 7 (averaging filter exact 1-ULP tracking bound `L ≤ M ∧ M - L ≤ 1` for all `w ≥ 1`, all `u`, and all `t`). |

## Prior-Art Context

- - **Vs. Classical Hardware Verification ($k$-Induction & IC3/PDR):** Sheeran–Singh–Stålmarck (2000) and Bradley (2011) verify safety for a fixed bit-width $w$ via SAT unrolling; proof-producing SAT checkers (DRAT/LRAT) still only certify one fixed width $w$. Word-level / parametric model checking (e.g., regular model checking, Kesten et al. 2001; Bouajjani et al. 2000) typically checks automata externally without a kernel-verified soundness proof in a theorem prover. - **Vs. Existing Lean 4 `bv_decide` / `omega` / `BitVec` Tactics:** Lean 4's `bv_decide` (LRAT bit-blasting) decides fixed-width `BitVec w` goals (one fixed $w$ at a time) and do
- Hostile-verified PASS by `referee-5`; pure `leanprover/lean4:v4.34.1` `Init` stack with `enable_nanoda: true` and exact integer Python replay in `scripts/explore_and_verify.py`.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).