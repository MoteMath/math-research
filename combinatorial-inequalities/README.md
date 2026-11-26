# Combinatorial Inequalities

Zero-Mathlib Lean 4 formalization of four universal permutation and additive-set inequalities proved for all $n, N \in \mathbb{N}$ using only Lean's `Std` library.

## Main results

All headline statements in [`Challenge.lean`](Challenge.lean) depend only on [`CombInequalities/CombDefs.lean`](CombInequalities/CombDefs.lean) (pure `Std`, no Mathlib):

- **Sharp factor-3 two-stack bound (`avoids321_three_stack2Inv_le_pat231`):** $3\,\mathrm{inv}(S^2(p)) \le \mathrm{pat} _ {231}(p)$ for every $321$-avoiding permutation $p \in \mathrm{Av} _ n(321)$, sharp at both $k = 1$ and $k = 2$.
- **Stack descents bounded by input peaks (`stackDes_le_peaksCnt`):** $\mathrm{des}(S(p)) \le \mathrm{peaks}(p)$ for every $p \in S _ n$.
- **Quadratic descent-excess ceiling (`avoids231_two_inv_le_disp2_add_des`):** $2\,\mathrm{inv}(p) \le \mathrm{disp2}(p) + \mathrm{des}(p)(\mathrm{des}(p) + 1)$ for every $p \in \mathrm{Av} _ n(231)$.
- **Difference-folding bound (`three_diffset_le_two_sum2Diff1_add_one`):** $3|A - A| \le 2|2A - A| + 1$ for normalized $A \subseteq [0, N - 1]$.

Supporting helper lemmas and classical combinatorial bounds (Mantel, Gallai-Ore, Erdős-Szekeres, Knuth's `231` inversion bound, West stack vs. pop-stack inversion dominance) remain in [`CombInequalities/ProvedDiscoveries.lean`](CombInequalities/ProvedDiscoveries.lean) as internal library material rather than challenge claims.

## Prior art and related work

- **Stack-sorting and two-stack-sortable permutations:** West's stack-sorting operator $S$ and two-stack-sortable permutations were introduced by J. West (*Permutations with restricted subsequences and stack-sortable permutations*, Ph.D. thesis, MIT, 1990) and enumerated by D. Zeilberger (*Discrete Math.* **102**, 1992, 85–93); see also C. Defant, *"Preimages under the stack-sorting algorithm"* ([arXiv:1809.03123](https://arxiv.org/abs/1809.03123)) and *"Pop-stack-sorting for Coxeter groups"* ([arXiv:2104.02675](https://arxiv.org/abs/2104.02675), which establishes the stronger weak-order inequality $S(p) \le _ R \mathrm{Pop}(p)$ subsuming $\mathrm{inv}(S(p)) \le \mathrm{inv}(P(p))$).
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
