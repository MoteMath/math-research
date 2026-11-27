# Combinatorial Inequalities

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **6 / 10** | **6 / 10** | **7 / 10** | **6 / 10** | **10 / 10** | **66 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): four crisp, universally quantified permutation and additive-set bounds in pure `Std` (zero Mathlib), closely adjacent to the West/Defant stack-sorting, Diaconis–Graham footrule, and Freiman/Ruzsa/Bukh sumset traditions.*

## For Mathematicians

Formalized purely in Lean 4 `Std` (zero Mathlib), this project proves four universally quantified combinatorial inequalities for all $n, N \in \mathbb{N}$: (1) the factor-$3$ two-stack bound $3\,\mathrm{inv}(S^2(p)) \le \mathrm{pat} _ {231}(p)$ on $321$-avoiding permutations $p \in \mathrm{Av} _ n(321)$, where $S$ is West's stack-sorting map; (2) the descent-peak bound $\mathrm{des}(S(p)) \le \mathrm{peaks}(p)$ for all $p \in S _ n$; (3) the reverse Diaconis–Graham excess ceiling $2\,\mathrm{inv}(p) \le \mathrm{disp2}(p) + \mathrm{des}(p)(\mathrm{des}(p) + 1)$ on $\mathrm{Av} _ n(231)$; and (4) the finite-integer sumset-dilate inequality $3|A - A| \le 2|2A - A| + 1$ for normalized subsets $A \subseteq [0, N - 1]$.

## For Non-Mathematicians

This collection proves four universal "speed limits" on shuffling lists and combining sets of whole numbers, valid for **every** size without exception. Three of them measure how well a single-stack sorting machine cleans up a scrambled list — for instance, the number of downward steps left after one stack-sorting pass can never exceed the number of "peaks" (numbers taller than both neighbors) in the original list, and on lists without any 3-step decreasing triple, running the stack sorter twice cuts out-of-order pairs to at most one-third of the `2-3-1` patterns. The fourth shows that for any set of integers $A$, the number of distinct differences $a - b$ is capped by the number of combinations $2a - b$.

---

Zero-Mathlib Lean 4 formalization of four universal permutation and additive-set inequalities proved for all $n, N \in \mathbb{N}$ using only Lean's `Std` library.

## Main results

All headline statements in [`Challenge.lean`](Challenge.lean) depend only on [`CombInequalities/CombDefs.lean`](CombInequalities/CombDefs.lean) (pure `Std`, no Mathlib):

- **Factor-3 two-stack bound (`avoids321_three_stack2Inv_le_pat231`):** $3\,\mathrm{inv}(S^2(p)) \le \mathrm{pat} _ {231}(p)$ for every $321$-avoiding permutation $p \in \mathrm{Av} _ n(321)$. Only the bound is stated in `Challenge.lean`; optimality of the factor $3$ is not part of the statement.
- **Stack descents bounded by input peaks (`stackDes_le_peaksCnt`):** $\mathrm{des}(S(p)) \le \mathrm{peaks}(p)$ for every $p \in S _ n$.
- **Quadratic descent-excess ceiling (`avoids231_two_inv_le_disp2_add_des`):** $2\,\mathrm{inv}(p) \le \mathrm{disp2}(p) + \mathrm{des}(p)(\mathrm{des}(p) + 1)$ for every $p \in \mathrm{Av} _ n(231)$.
- **Difference-folding bound (`three_diffset_le_two_sum2Diff1_add_one`):** $3|A - A| \le 2|2A - A| + 1$ for normalized $A \subseteq [0, N - 1]$.

Supporting helper lemmas and classical combinatorial bounds (Mantel, Gallai-Ore, Erdős-Szekeres, Knuth's `231` inversion bound, West stack vs. pop-stack inversion dominance) remain in [`CombInequalities/ProvedDiscoveries.lean`](CombInequalities/ProvedDiscoveries.lean) as internal library material rather than challenge claims.

## Prior art and related work

- **Stack-sorting and two-stack-sortable permutations:** West's stack-sorting operator $S$ and two-stack-sortable permutations were introduced by J. West (*Permutations with restricted subsequences and stack-sortable permutations*, Ph.D. thesis, MIT, 1990) and enumerated by D. Zeilberger (*Discrete Math.* **102**, 1992, 85–93); see also C. Defant, *"Stack-Sorting Preimages of Permutation Classes"* ([arXiv:1809.03123](https://arxiv.org/abs/1809.03123)) and *"Pop-stack-sorting for Coxeter groups"* ([arXiv:2104.02675](https://arxiv.org/abs/2104.02675), which establishes the stronger weak-order inequality $S(p) \le _ R \mathrm{Pop}(p)$ subsuming $\mathrm{inv}(S(p)) \le \mathrm{inv}(P(p))$).
- **Located related work (added after an external novelty audit):** C. Defant, *"Stack-Sorting for Coxeter Groups"*, [arXiv:2104.03215](https://arxiv.org/abs/2104.03215), and M. H. Albert, M. D. Atkinson, M. Bouvel, A. Claesson and M. Dukes, *"On the inverse image of pattern classes under bubble sort"*, *J. Comb.* **2** (2011), [arXiv:1008.5299](https://arxiv.org/abs/1008.5299), treat the same stack-sorting and bubble-sort operators. No source for the exact inequalities above was found by that audit (a bounded search, not exhaustive).
- **Inversions vs. Spearman displacement:** P. Diaconis and R. L. Graham, *"Spearman's footrule as a measure of disarray"*, *J. R. Stat. Soc. B* **39** (1977), 262–268, prove $I(\pi) + T(\pi) \le D(\pi) \le 2 I(\pi)$ (with $D(\pi) = 2 I(\pi)$ iff $\pi \in \mathrm{Av}(321)$); see also T. K. Petersen and B. E. Tenner (2015) on shallow permutations. Here `avoids231_two_inv_le_disp2_add_des` bounds the reverse excess $2\,\mathrm{inv}(p) - D(p)$ on $\mathrm{Av}(231)$ by $\mathrm{des}(p)(\mathrm{des}(p) + 1)$.
- **Sumset and difference-set inequalities:** `three_diffset_le_two_sum2Diff1_add_one` sits alongside elementary finite-integer sumset/dilate bounds in the tradition of Freiman, Ruzsa, and B. Bukh (*"Sums of dilates"*, *Combin. Probab. Comput.* **17**, 2008, 627–639).

## Layout

- [`CombInequalities/CombDefs.lean`](CombInequalities/CombDefs.lean): Pure-`Std` definitions for finite graphs, additive subsets, and permutations (zero Mathlib).
- [`Challenge.lean`](Challenge.lean): Trusted statement file importing only `CombInequalities.CombDefs`, with `sorry` placeholders for Comparator.
- [`CombInequalities/ProvedDiscoveries.lean`](CombInequalities/ProvedDiscoveries.lean): Supporting proofs and internal lemmas.
- [`Solution.lean`](Solution.lean): Proofs of all 4 challenge statements (zero `sorry`).
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
