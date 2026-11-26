# Weak-Bruhat Commutators

Zero-Mathlib (`Init`-only) Lean 4 formalization of the Bubble-Refined Order (`WeakBruhatLe` together with `DesBotSub`) and universal all-$k$ commutator laws for iterated bubble sort $B^k$, West's stack-sorting operator $S$, and pop-stack sorting $P$ on duplicate-free lists of natural numbers.

## Proof architecture

Neither West's maximum-splitting recurrence $S(L \mathbin{+\!\!+} [m] \mathbin{+\!\!+} R) = S(L) \mathbin{+\!\!+} S(R) \mathbin{+\!\!+} [m]$ nor Left Weak Bruhat monotonicity of $S$ or $P$ can establish iterated commutator inequalities such as $\mathrm{inv}(B^k(S(xs))) \le \mathrm{inv}(S(B^k(xs)))$ or $\mathrm{des}(B^k(P(xs))) \le \mathrm{des}(P(B^k(xs)))$ directly: `bubblePass` commutes across the maximum split differently from $S$ and $P$, and both $S$ and $P$ fail Left Weak Bruhat monotonicity (witnessed below at $u = [0, 1, 3, 4, 2] \le _ L [0, 1, 4, 3, 2] = v$).

Instead, this formalization lifts all three operators to value-inversion sets $\mathrm{Inv} _ {\mathrm{val}}(xs)$ (Left Weak Bruhat Order $\le _ L$) and descent-bottom sets $\mathrm{DesBot}(xs)$, defines the combined Bubble-Refined Order

```math
xs \preceq _ B ys \iff \mathrm{Inv} _ {\mathrm{val}}(xs) \subseteq \mathrm{Inv} _ {\mathrm{val}}(ys) \;\wedge\; \mathrm{DesBot}(xs) \subseteq \mathrm{DesBot}(ys),
```

and proves:
1. Exact set-theoretic characterizations of $\mathrm{Inv} _ {\mathrm{val}}$ for $B$, $S$, and $P$, and of $\mathrm{DesBot}$ for $B$.
2. Monotonicity of $B$ in $\preceq _ B$ (`bubbleOrder_bubblePass_mono`).
3. The $k = 1$ commutator inclusions $B(S(xs)) \preceq _ B S(B(xs))$ and $B(P(xs)) \preceq _ B P(B(xs))$ via right-valley transfer and the pure inversion-set characterization of $\mathrm{DesBot}$.
4. By induction on $k$ using $\preceq _ B$-monotonicity of $B$, the full iterated commutators $B^k(S(xs)) \preceq _ B S(B^k(xs))$ and $B^k(P(xs)) \preceq _ B P(B^k(xs))$ for all $k \in \mathbb{N}$, yielding inversion-count and descent-count commutator inequalities as cardinality corollaries.

## Main results

The trusted statement file [`Challenge.lean`](Challenge.lean) declares 13 theorems against the 121-line pure-`Init` definitions file [`WeakBruhatCommutators/Defs.lean`](WeakBruhatCommutators/Defs.lean):

- **Exact bubble-sort characterizations (`invSet_bubblePass_iff`, `desBot_bubblePass_iff`):**
  For every duplicate-free list $xs$,
  $(a, b) \in \mathrm{Inv} _ {\mathrm{val}}(B(xs)) \iff (a, b) \in \mathrm{Inv} _ {\mathrm{val}}(xs) \wedge \exists c > a,\; (c, b) \in \mathrm{Inv} _ {\mathrm{val}}(xs)$, and
  $b \in \mathrm{DesBot}(B(xs)) \iff b \in \mathrm{DesBot}(xs) \wedge \mathrm{leftInv}(xs, b) \ge 2$.
- **Bubble-Refined Order monotonicity (`bubbleOrder_bubblePass_mono`):**
  For permutations $xs, ys$ (duplicate-free), $xs \preceq _ B ys \implies B(xs) \preceq _ B B(ys)$.
- **Weak-Bruhat sandwich laws (`westSort_weakBruhat_bubblePass`, `westSort_weakBruhat_popSort`):**
  For every duplicate-free list $xs$, $S(xs) \le _ L B(xs)$ and $S(xs) \le _ L P(xs)$.
- **Iterated Bubble-West and Bubble-Pop commutators (`iterBubble_west_commutator`, `iterBubble_pop_commutator`):**
  For every $k \in \mathbb{N}$ and every duplicate-free list $xs$,
  $B^k(S(xs)) \preceq _ B S(B^k(xs))$ and $B^k(P(xs)) \preceq _ B P(B^k(xs))$.
- **Iterated inversion and descent commutator bounds (`invCnt_iterBubble_west_le`, `desCnt_iterBubble_west_le`, `invCnt_iterBubble_pop_le`, `desCnt_iterBubble_pop_le`):**
  For every $k \in \mathbb{N}$ and every duplicate-free list $xs$,
  $\mathrm{inv}(B^k(S(xs))) \le \mathrm{inv}(S(B^k(xs)))$,
  $\mathrm{des}(B^k(S(xs))) \le \mathrm{des}(S(B^k(xs)))$,
  $\mathrm{inv}(B^k(P(xs))) \le \mathrm{inv}(P(B^k(xs)))$, and
  $\mathrm{des}(B^k(P(xs))) \le \mathrm{des}(P(B^k(xs)))$.
- **Sharpness witnesses (`exists_westSort_popSort_not_weakBruhat_mono`, `exists_bubble_pop_incomparable`):**
  At $u = [0, 1, 3, 4, 2]$ and $v = [0, 1, 4, 3, 2]$, $u \le _ L v$ holds while both $S(u) \not\le _ L S(v)$ and $P(u) \not\le _ L P(v)$. At $xs = [3, 1, 2, 0]$, $B(xs) = [1, 2, 0, 3]$ and $P(xs) = [1, 3, 0, 2]$ are incomparable in $\le _ L$.

## Prior art and related work

- **Bubble sort, stack-sorting, and pop-stack sorting:** See J. West (Ph.D. thesis, MIT, 1990), P. Ungar (*"2N noncollinear points determine at least 2N directions"*, *J. Combin. Theory Ser. A* **33** (1982), 343-347), F. Chung, A. Claesson, M. Dukes, and R. Graham (*Eur. J. Combin.* **31** (2010), 1853-1867), M. H. Albert, M. D. Atkinson, M. Bouvel, A. Claesson, and M. Dukes ([arXiv:1008.5299](https://arxiv.org/abs/1008.5299)), and C. Defant ([arXiv:1809.03123](https://arxiv.org/abs/1809.03123), [arXiv:2104.02675](https://arxiv.org/abs/2104.02675)).
- **Weak Bruhat Order and sorting operators:** Left Weak Bruhat Order (inclusion of value-inversion sets) and its interaction with pop-stack sorting and bubble sort have been studied in the lattice-theoretic literature on Coxeter groups and Cambrian lattices (cf. N. Reading, C. Defant, and A. Claesson & B. A. Gudmundsson, [arXiv:1908.05564](https://arxiv.org/abs/1908.05564)). The exact `InvSet` characterizations of $B$, $S$, and $P$ and the fact that $B$ is weak-order monotone while $S$ and $P$ are not are natural structural tools; the combined Bubble-Refined Order $\preceq _ B$ packages both inversion-set and descent-bottom dominance into a single inductive invariant for all $k \in \mathbb{N}$.

## Building and checking

From inside `weak-bruhat-commutators/` (no Mathlib cache needed):

```sh
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

To run the full Palomar Comparator check on Linux:

```sh
bash ../.github/scripts/comparator-check.sh
```
