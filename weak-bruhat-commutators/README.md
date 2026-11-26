# Weak-Bruhat Commutators

Zero-Mathlib (`Init`-only) Lean 4 formalization of the Bubble-Refined Order (`WeakBruhatLe` together with `DesBotSub`) and universal all-$k$ commutator laws for iterated bubble sort $B^k$, West's stack-sorting operator $S$, and pop-stack sorting $P$ on duplicate-free lists of natural numbers.

## Proof architecture

Neither West's maximum-splitting recurrence $S(L \mathbin{+\!\!+} [m] \mathbin{+\!\!+} R) = S(L) \mathbin{+\!\!+} S(R) \mathbin{+\!\!+} [m]$ nor Right Weak Bruhat monotonicity of $S$ or $P$ can establish iterated commutator inequalities such as $\mathrm{inv}(B^k(S(xs))) \le \mathrm{inv}(S(B^k(xs)))$ or $\mathrm{des}(B^k(P(xs))) \le \mathrm{des}(P(B^k(xs)))$ directly: `bubblePass` commutes across the maximum split differently from $S$ and $P$, both $S$ and $P$ fail Right Weak Bruhat monotonicity (at $u = [0, 1, 3, 4, 2] \le _ R [0, 1, 4, 3, 2] = v$), and individual 0-Hecke adjacent swaps $\pi _ i$ fail both $\le _ R$-monotonicity and the $S$/$P$ commutator inequalities.

Instead, this formalization lifts all three operators to value-inversion sets $\mathrm{Inv} _ {\mathrm{val}}(xs)$ (Right Weak Bruhat Order $\le _ R$ in the Björner-Brenti / Defant one-line convention) and descent-bottom sets $\mathrm{DesBot}(xs)$, defines the combined Bubble-Refined Order

```math
xs \preceq _ B ys \iff \mathrm{Inv} _ {\mathrm{val}}(xs) \subseteq \mathrm{Inv} _ {\mathrm{val}}(ys) \;\wedge\; \mathrm{DesBot}(xs) \subseteq \mathrm{DesBot}(ys),
```

and proves:
1. The exact descent-bottom characterization of single-pass bubble sort (`desBot_bubblePass_iff`).
2. Monotonicity of $B$ in $\preceq _ B$ (`bubbleOrder_bubblePass_mono`).
3. The $k = 1$ commutator inclusions $B(S(xs)) \preceq _ B S(B(xs))$ and $B(P(xs)) \preceq _ B P(B(xs))$ via right-valley transfer and the pure inversion-set characterization of $\mathrm{DesBot}$.
4. By induction on $k$ using $\preceq _ B$-monotonicity of $B$, the full iterated commutators $B^k(S(xs)) \preceq _ B S(B^k(xs))$ and $B^k(P(xs)) \preceq _ B P(B^k(xs))$ for all $k \in \mathbb{N}$, yielding inversion-count and descent-count commutator inequalities as cardinality corollaries.

## Main results

The trusted statement file [`Challenge.lean`](Challenge.lean) declares 8 theorems against the 121-line pure-`Init` definitions file [`WeakBruhatCommutators/Defs.lean`](WeakBruhatCommutators/Defs.lean) (known structural facts such as Knuth's inversion-table decrement law `invSet_bubblePass_iff`, Defant's compulsiveness inequality $S(xs) \le _ R P(xs)$, $S(xs) \le _ R B(xs)$, and non-monotonicity of $S$ and $P$ are kept as internal lemmas in `WeakBruhatCommutators/`):

- **Exact descent-bottom law for bubble sort (`desBot_bubblePass_iff`):**
  For every duplicate-free list $xs$ and every $b \in \mathbb{N}$,
  $b \in \mathrm{DesBot}(B(xs)) \iff b \in \mathrm{DesBot}(xs) \wedge \mathrm{leftInv}(xs, b) \ge 2$.
- **Bubble-Refined Order monotonicity (`bubbleOrder_bubblePass_mono`):**
  For duplicate-free permutations $xs, ys$, $xs \preceq _ B ys \implies B(xs) \preceq _ B B(ys)$.
- **Iterated Bubble-West and Bubble-Pop commutators (`iterBubble_west_commutator`, `iterBubble_pop_commutator`):**
  For every $k \in \mathbb{N}$ and every duplicate-free list $xs$,
  $B^k(S(xs)) \preceq _ B S(B^k(xs))$ and $B^k(P(xs)) \preceq _ B P(B^k(xs))$.
- **Iterated inversion and descent commutator bounds (`invCnt_iterBubble_west_le`, `desCnt_iterBubble_west_le`, `invCnt_iterBubble_pop_le`, `desCnt_iterBubble_pop_le`):**
  For every $k \in \mathbb{N}$ and every duplicate-free list $xs$,
  $\mathrm{inv}(B^k(S(xs))) \le \mathrm{inv}(S(B^k(xs)))$,
  $\mathrm{des}(B^k(S(xs))) \le \mathrm{des}(S(B^k(xs)))$,
  $\mathrm{inv}(B^k(P(xs))) \le \mathrm{inv}(P(B^k(xs)))$, and
  $\mathrm{des}(B^k(P(xs))) \le \mathrm{des}(P(B^k(xs)))$.

## Prior art and related work

- **Bubble sort and inversion tables:** D. E. Knuth (*The Art of Computer Programming*, Vol. 3, §5.2.2) showed that a single bubble-sort pass decrements each positive entry of the inversion table by $1$; the internal lemma `invSet_bubblePass_iff` is the set-level refinement of that decrement law. Bubble-sort preimages, pattern classes, and drop-size descent polynomials are studied in F. Chung, A. Claesson, M. Dukes, and R. Graham (*Eur. J. Combin.* **31** (2010), 1853-1867), M. H. Albert, M. D. Atkinson, M. Bouvel, A. Claesson, and M. Dukes ([arXiv:1008.5299](https://arxiv.org/abs/1008.5299)), and M. Bouvel, L. Cioni, and L. Ferrari ([arXiv:2204.12936](https://arxiv.org/abs/2204.12936)).
- **West stack-sorting, pop-stack sorting, and Right Weak Bruhat Order:** See A. Björner and F. Brenti (*Combinatorics of Coxeter Groups*, Ch. 3) for the Right Weak Bruhat Order convention on value-inversion sets, J. West (Ph.D. thesis, MIT, 1990), P. Ungar (*J. Combin. Theory Ser. A* **33** (1982), 343-347), A. Claesson and B. A. Gudmundsson ([arXiv:1908.05564](https://arxiv.org/abs/1908.05564)), and C. Defant (*Pop-Stack-Sorting for Coxeter Groups*, [arXiv:2104.02675](https://arxiv.org/abs/2104.02675); *Stack-Sorting for Coxeter Groups*, [arXiv:2104.03215](https://arxiv.org/abs/2104.03215)). In Defant's terminology, $S(xs) \le _ R P(xs)$ expresses that $S$ is a compulsive map, and non-monotonicity of $P$ and $S$ in weak order is already noted in the literature (cf. [arXiv:2212.09316](https://arxiv.org/abs/2212.09316)); those facts are retained only as internal lemmas.

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
