# Sorting Operators

Zero-Mathlib (`Init`-only) Lean 4 formalization of universal cross-operator inequalities and structural identities relating West's stack-sorting operator $S$ and a single bubble-sort pass $B$ on lists of natural numbers. Every theorem depends only on `[propext, Quot.sound]` (no `Classical.choice`).

## Main results

The trusted statement file [`Challenge.lean`](Challenge.lean) declares 9 universal theorems:

- **Bubble-sort inversion-descent bound (`inv_bubble_add_des_le_inv`):** For every list $xs$,
  $\mathrm{inv}(B(xs)) + \mathrm{des}(xs) \le \mathrm{inv}(xs)$.
- **Bubble-sort descent monotonicity (`des_bubble_le_des`):** For every list $xs$,
  $\mathrm{des}(B(xs)) \le \mathrm{des}(xs)$ (proved via the stronger carry bound $\mathrm{des}(\mathrm{bubbleCarry}(m, xs)) \le \mathrm{des}(xs)$).
- **Dual maximum-splitting recurrences (`westSort_split_max`, `bubblePass_split_max`):** When $m$ strictly dominates all entries of $L$ and $R$,
  $S(L \mathbin{+\!\!+} [m] \mathbin{+\!\!+} R) = S(L) \mathbin{+\!\!+} S(R) \mathbin{+\!\!+} [m]$ and $B(L \mathbin{+\!\!+} [m] \mathbin{+\!\!+} R) = B(L) \mathbin{+\!\!+} R \mathbin{+\!\!+} [m]$.
- **Inversion dominance (`inv_westSort_le_bubble`):** For every duplicate-free list $xs$,
  $\mathrm{inv}(S(xs)) \le \mathrm{inv}(B(xs))$.
- **Descent dominance (`des_westSort_le_bubble`):** For every duplicate-free list $xs$,
  $\mathrm{des}(S(xs)) \le \mathrm{des}(B(xs))$.
- **Coincidence on `321`-avoiding lists (`westSort_eq_bubble_of_avoids321`):** For every duplicate-free `321`-avoiding list $xs$, $S(xs) = B(xs)$.
- **Strictness witness (`exists_not_avoids321_westSort_eq_bubble`):** The converse fails: `xs = [2, 1, 3, 0]` is duplicate-free, contains the `321` pattern `(2, 1, 0)`, and satisfies $S(xs) = B(xs) = [1, 2, 0, 3]$.
- **Bubble-sort pattern bound (`inv_bubble_le_pat321_add_pat231`):** For every duplicate-free list $xs$,
  $\mathrm{inv}(B(xs)) \le \mathrm{pat} _ {321}(xs) + \mathrm{pat} _ {231}(xs)$.

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
