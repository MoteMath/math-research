# Combinatorial Inequalities

Zero-Mathlib Lean 4 formalization of universal combinatorial inequalities and explicit counterexample disproofs discovered through binary math across permutations, finite additive subsets, and simple graphs.

## Main results

All headline statements in [`Challenge.lean`](Challenge.lean) are quantified universally over all $n, N \in \mathbb{N}$ and depend only on Lean's `Std` library (no Mathlib):

- **West stack vs. pop-stack inversion dominance (`stackInv_le_popInv`):** $\mathrm{inv}(S(p)) \le \mathrm{inv}(P(p))$ for every permutation $p \in S _ n$.
- **Sharp factor-3 two-stack bound (`avoids321_three_stack2Inv_le_pat231`):** $3\,\mathrm{inv}(S^2(p)) \le \mathrm{pat231}(p)$ for every $321$-avoiding permutation $p \in \mathrm{Av} _ n(321)$, sharp at both $k = 1$ and $k = 2$.
- **Stack descents bounded by input peaks (`stackDes_le_peaksCnt`):** $\mathrm{des}(S(p)) \le \mathrm{peaks}(p)$ for every $p \in S _ n$.
- **Quantitative Knuth bound (`stackInv_le_pat231`):** $\mathrm{inv}(S(p)) \le \mathrm{pat231}(p)$ for every $p \in S _ n$.
- **Quadratic descent-excess ceiling (`avoids231_two_inv_le_disp2_add_des`):** $2\,\mathrm{inv}(p) \le \mathrm{disp2}(p) + \mathrm{des}(p)(\mathrm{des}(p) + 1)$ for every $p \in \mathrm{Av} _ n(231)$.
- **Sidon reflection-asymmetry identity (`sidon_sym_defect_eq`):** $\mathrm{symDefect}(A) + 4 = 2|A|$ for every non-trivial finite Sidon set $A$.
- **Reflection-asymmetry Freiman refinement (`two_card_add_symDefect_le_diffset_add_one`):** $2|A| + \mathrm{symDefect}(A) \le |A - A| + 1$ for normalized $A \subseteq [0, N - 1]$.
- **Difference-folding bound (`three_diffset_le_two_sum2Diff1_add_one`):** $3|A - A| \le 2|2A - A| + 1$ for normalized $A \subseteq [0, N - 1]$.
- **Quantitative graph diameter and irregularity bounds (`connected_diam_le_indP4_add_two`, `albertson_le_orderedIndP3`):** $\mathrm{diam}(G) \le \mathrm{indP4}(G) + 2$ for connected graphs, and $\mathrm{albertson}(G) \le \mathrm{orderedIndP3}(G)$ for all simple graphs.
- **Explicit counterexample disproofs (`disproof_avoids231_inv_disp_lds`, `disproof_bipartite_dom_indNu_diam`):** Formal refutations at $n = 9$ and on a 25-vertex tree (`tree25`).

Additional proved clusters (Mantel, Gallai-Ore, Erdős-Szekeres, involution cycle bounds, sumset/dilate bounds) live in [`CombInequalities/ProvedDiscoveries.lean`](CombInequalities/ProvedDiscoveries.lean).

## Layout

- [`CombInequalities/CombDefs.lean`](CombInequalities/CombDefs.lean): Pure-`Std` definitions for finite graphs, additive subsets, and permutations (zero Mathlib).
- [`Challenge.lean`](Challenge.lean): Trusted statement file importing only `CombInequalities.CombDefs`, with `sorry` placeholders for Comparator.
- [`CombInequalities/ProvedDiscoveries.lean`](CombInequalities/ProvedDiscoveries.lean): All 23 proved theorem clusters.
- [`CombInequalities/OpenConjectures.lean`](CombInequalities/OpenConjectures.lean): Both formal disproofs and remaining open finite-stressed targets.
- [`Solution.lean`](Solution.lean): Proofs of all 12 challenge statements (zero `sorry`).
- [`scripts/PrintAxioms.lean`](scripts/PrintAxioms.lean) and [`AUDIT.md`](AUDIT.md): Axiom checks and verification record.

## Building and checking

From inside `combinatorial-inequalities/` (no Mathlib cache needed):

```sh
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

To run the full Palomar Comparator check on Linux:

```sh
bash ../.github/scripts/comparator-check.sh
```
