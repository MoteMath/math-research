# Sorting Operators

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **5 / 10** | **5 / 10** | **7 / 10** | **6 / 10** | **10 / 10** | **61 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): clean, constructive (`Init`-only, zero `Classical.choice`) cross-operator comparison between West stack-sort $S$ and single-pass bubble sort $B$, adjacent to Chung–Claesson–Dukes–Graham (2010), Albert et al. (2011), and Defant's weak-order framework.*

## For Mathematicians

Using only Lean 4's core `Init` library and constructive axioms (`[propext, Quot.sound]`, no `Classical.choice`), we prove five universal theorems comparing West's stack-sorting operator $S$ and single-pass bubble sort $B$ on arbitrary duplicate-free lists $xs$ of natural numbers: inversion dominance $\mathrm{inv}(S(xs)) \le \mathrm{inv}(B(xs))$, descent dominance $\mathrm{des}(S(xs)) \le \mathrm{des}(B(xs))$, exact coincidence $S(xs) = B(xs)$ on every $321$-avoiding list together with the explicit minimal strictness witness `[2, 1, 3, 0]` (which contains `321` yet satisfies $S = B$), and the quantitative pattern bound $\mathrm{inv}(B(xs)) \le \mathrm{pat} _ {321}(xs) + \mathrm{pat} _ {231}(xs)$ refining the classical characterization $B(\sigma) = \mathrm{id} \iff \sigma \in \mathrm{Av}(231, 321)$.

## For Non-Mathematicians

Compare two famous one-pass sorting steps on a row of distinct numbers: a single sweep of "bubble sort" (which walks left-to-right swapping any bigger item past its smaller neighbor) versus "stack sort" (which holds items on a temporary vertical stack whenever a smaller item arrives). We prove that for **any** starting list of any length, one pass of stack sort **always** beats or ties one pass of bubble sort — leaving no more out-of-order pairs and no more downward steps. Whenever the list has no 3-step downward chain (`big, medium, small`), both methods produce the **exact same output**, though `[2, 1, 3, 0]` shows they can occasionally agree even when a 3-step downward chain is present.

---

Zero-Mathlib (`Init`-only) Lean 4 formalization of universal cross-operator inequalities and structural identities relating West's stack-sorting operator $S$ and a single bubble-sort pass $B$ on duplicate-free lists of natural numbers. Every theorem depends only on `[propext, Quot.sound]` (no `Classical.choice`).

## Main results

The trusted statement file [`Challenge.lean`](Challenge.lean) declares 5 cross-operator theorems (standard single-operator bubble-sort lemmas and the classical maximum-splitting recurrences $S(L \mathbin{+\!\!+} [m] \mathbin{+\!\!+} R) = S(L) \mathbin{+\!\!+} S(R) \mathbin{+\!\!+} [m]$ and $B(L \mathbin{+\!\!+} [m] \mathbin{+\!\!+} R) = B(L) \mathbin{+\!\!+} R \mathbin{+\!\!+} [m]$ are kept as internal lemmas in [`SortingOperators/Theorems.lean`](SortingOperators/Theorems.lean)):

- **Inversion dominance (`inv_westSort_le_bubble`):** For every duplicate-free list $xs$,
  $\mathrm{inv}(S(xs)) \le \mathrm{inv}(B(xs))$.
- **Descent dominance (`des_westSort_le_bubble`):** For every duplicate-free list $xs$,
  $\mathrm{des}(S(xs)) \le \mathrm{des}(B(xs))$.
- **Coincidence on `321`-avoiding lists (`westSort_eq_bubble_of_avoids321`):** For every duplicate-free `321`-avoiding list $xs$, $S(xs) = B(xs)$.
- **Strictness witness (`exists_not_avoids321_westSort_eq_bubble`):** The converse fails: `xs = [2, 1, 3, 0]` is duplicate-free, contains the `321` pattern `(2, 1, 0)`, and satisfies $S(xs) = B(xs) = [1, 2, 0, 3]$.
- **Bubble-sort pattern bound (`inv_bubble_le_pat321_add_pat231`):** For every duplicate-free list $xs$,
  $\mathrm{inv}(B(xs)) \le \mathrm{pat} _ {321}(xs) + \mathrm{pat} _ {231}(xs)$.

## Prior art and related work

- **Bubble-sort operator and pattern classes:** Single-pass bubble sort $B$ and its characterization $B(\sigma) = \mathrm{id} \iff \sigma \in \mathrm{Av}(231, 321)$ (of which `inv_bubble_le_pat321_add_pat231` is a quantitative version) are studied in F. Chung, A. Claesson, M. Dukes, and R. Graham, *"Descent polynomials for permutations with bounded drop size"*, *Eur. J. Combin.* **31** (2010), 1853–1867, and M. H. Albert, M. D. Atkinson, M. Bouvel, A. Claesson, and M. Dukes, *"On the inverse image of pattern classes under bubble sort"*, *J. Comb.* **2** (2011), 231–243 ([arXiv:1008.5299](https://arxiv.org/abs/1008.5299)).
- **West's stack-sorting operator and weak order:** See J. West (Ph.D. thesis, MIT, 1990) and C. Defant ([arXiv:1809.03123](https://arxiv.org/abs/1809.03123), [arXiv:2104.02675](https://arxiv.org/abs/2104.02675)). Note that `inv_westSort_le_bubble` is also a direct consequence of value-inversion-set inclusion $\mathrm{Inv} _ {\mathrm{val}}(S(xs)) \subseteq \mathrm{Inv} _ {\mathrm{val}}(B(xs))$ (since surviving inversions of $S$ require a larger element strictly between the pair, while surviving inversions of $B$ require a larger element anywhere to the left of the smaller element).

## Building and checking

From inside `sorting-operators/` (no Mathlib cache needed):

```sh
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

To run the full Palomar Comparator check on Linux:

```sh
bash ../.github/scripts/comparator-check.sh
```
