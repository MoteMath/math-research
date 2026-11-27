# certcomp-6: Bottom-Up Tree-Automaton & Quadtree Proof Compiler (`tree-quadtree-automaton-compiler`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **89 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): **Name:** *Timed / Factored / Monotone-Upset Quadtree Automaton Compiler* (BU-FTA over `BTree α k` and `QTree α k`). **Principle.** A finite binary certificate (a bitmask of reachable states per phase, or a list of upset generators) is checked inside the Lean kernel by `decide`. A once-proved soundness meta-theorem turns "certificate accepted" into a statement for all `k : Nat`*

## For Mathematicians

**Name:** *Timed / Factored / Monotone-Upset Quadtree Automaton Compiler* (BU-FTA over `BTree α k` and `QTree α k`). **Principle.** A finite binary certificate (a bitmask of reachable states per phase, or a list of upset generators) is checked inside the Lean kernel by `decide`. A once-proved soundness meta-theorem turns "certificate accepted" into a statement for all `k : Nat`. Certificates are pure data (`Nat` bitmasks, lists of `Fin`), with no `Prop` fields. A broken certificate makes the checker return `false`, which is proved by `decide`. Engines in the Lean sources (Section 2): The upset engine only needs the generators of the invariant, not all of its elements. The meta-theorem takes monotonicity of `hTop`, `hBot` and `vGlue` as hypotheses. The graph instance proves them symbolically from `Reach.mono` (`hTopExec_mono`, `hBotExec_mono`, `vGlueExec_mono`).

## For Non-Mathematicians

**Name:** *Timed / Factored / Monotone-Upset Quadtree Automaton Compiler* (BU-FTA over `BTree α k` and `QTree α k`). **Principle.** A finite binary certificate (a bitmask of reachable states per phase, or a list of upset generators) is checked inside the Lean kernel by `decide`. A once-proved soundness meta-theorem turns "certificate accepted" into a statement for all `k : Nat`

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `TreeQuadtreeAutomatonCompiler/Theorems.lean`, definitions in `TreeQuadtreeAutomatonCompiler/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `timedBTA_sound` | General Soundness Meta-Theorem for Height-Timed Bottom-Up Binary Tree Automata. |
| `factoredQTA_sound` | Machine-checked infinite theorem `factoredQTA_sound` proved in pure Lean 4 `Init`. |
| `percEval_eq_QNet` | Machine-checked infinite theorem `percEval_eq_QNet` proved in pure Lean 4 `Init`. |
| `percolation_duality_D33` | Machine-checked infinite theorem `percolation_duality_D33` proved in pure Lean 4 `Init`. |
| `d33_exact_completeness_height2` | Machine-checked infinite theorem `d33_exact_completeness_height2` proved in pure Lean 4 `Init`. |
| `hilbert_D4_mod15_annihilation` | Machine-checked infinite theorem `hilbert_D4_mod15_annihilation` proved in pure Lean 4 `Init`. |
| `nonvacuity_barrier_witnesses` | Machine-checked infinite theorem `nonvacuity_barrier_witnesses` proved in pure Lean 4 `Init`. |
| `sharpness_and_nonvacuity_family3` | Machine-checked infinite theorem `sharpness_and_nonvacuity_family3` proved in pure Lean 4 `Init`. |

## Prior-Art Context

- * Bottom-up tree automata, their closure properties and decidability are classical (Comon et al., *TATA*). Reflection and certificate-checking tactics such as `decide` and `ring` are standard practice. The engine is therefore not claimed as a new theory. * The contribution is a small, reusable kernel-checked compiler with four features: a phase-indexed (period `p`) certificate so that height-dependent invariants such as `2^(2^k) mod 7` are covered; a factored 5-port form; a generator-only upset form with proved lattice monotonicity; and a Morton lift from period-2 binary trees to quadtrees. * The three families are instances found by exhausti
- Hostile-verified PASS by `referee-5`; pure `leanprover/lean4:v4.35.0` `Init` stack with `enable_nanoda: true` and exact integer Python replay in `scripts/explore_and_verify.py`.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).