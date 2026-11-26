# Sorting Operators

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
