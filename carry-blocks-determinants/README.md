# Carry-Blocks, Plateau Hankel, and Ultrametric XOR Determinants

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **6 / 10** | **7 / 10** | **9 / 10** | **7 / 10** | **9 / 10** | **73 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): division-free characteristic-independent proofs for carry-blocks unimodularity, universal plateau Hankel invariance, and ultrametric XOR bit-length matrices (the last sitting in the classical tree-distance / Walsh–Hadamard circulant lineage).*

## For Mathematicians

We formalize three division-free families of exact determinant evaluations valid over every commutative ring $R$ (including characteristic $2$). First, letting $\mathrm{carryBlocks} _ b(k, i, j)$ count maximal contiguous `1`-runs in the mixed-radix carry vector of $i + j$, we prove $\det(x^{\mathrm{carryBlocks} _ b(k, i, j)}) _ {0 \le i,j < P _ k} = (-1)^{\binom{P _ k - 1}{2}}(x - 1)^{P _ k - 1}$, extract linear unimodularity $\det(\mathrm{carryBlocks} _ b(k, i, j)) _ {1 \le i,j < P _ k} = (-1)^{\binom{P _ k - 1}{2}}$ over $R[X]$ without division, and deduce the binary Gray-code carry-transition determinant $(-1)^{\binom{2^k - 1}{2}} 2^{2^k - 1}$. Second, we prove universal 1-based and 0-based plateau Hankel formulas whose values depend only on two plateau constants $a, d$ and are completely invariant to all lower-index entries, yielding exact mixed-radix digit-length Hankel determinants. Third, we give a ring-universal formula for the shifted $(\mathbb{Z}/2\mathbb{Z})^k$-circulant ultrametric matrix $(\mathrm{bitlen}(i \oplus j) + t) _ {0 \le i,j < 2^k}$.

## For Non-Mathematicians

When you add two numbers in binary, carries often ripple in streaks (like adding `1` to `01111`, which creates one long unbroken chain of carries). If you build a table counting how many **separate carry streaks** happen when adding $i + j$, its determinant is always $+1$ or $-1$ — no matter how big the table or what mixed number bases you use! In the same project, we prove a "plateau rule" showing that if a table's entries flatten out on the right side, its determinant completely ignores almost everything in the top-left corner, and we give an exact formula for tables measuring the highest bit where two numbers $i$ and $j$ differ.

---

Lean 4 (Mathlib `v4.34.1`) formalization of exact closed-form determinant families valid over an arbitrary commutative ring $R$ (all proofs are division-free and hold in every characteristic).

## Main results

The trusted statement file [`Challenge.lean`](Challenge.lean) declares 10 universal determinant theorems:

### 1. Mixed-radix carry-blocks and Gray-code transitions

For any mixed radix $b : \mathbb{N} \to \mathbb{N}$ with $b _ r \ge 1$ and place values $P _ k = \prod _ {r < k} b _ r$, let $\mathrm{carryBlocks} _ b(k, i, j)$ denote the number of maximal contiguous `1`-runs in the first $k$ mixed-radix carry bits of $i + j$.

- **Exponential carry-blocks (`det_mixedCarryBlocks_exp`):** For every $x \in R$,

```math
\det\bigl(x^{\mathrm{carryBlocks}_b(k, i, j)}\bigr)_{0 \le i, j < P_k}
= (-1)^{\binom{P_k - 1}{2}} (x - 1)^{P_k - 1}.
```

- **Linear carry-blocks unimodularity (`det_mixedCarryBlocks_linear`, `det_binaryCarryBlocks`):** Extracted from `det_mixedCarryBlocks_exp` over $R[X]$ at $x = X + 1$ with zero division:

```math
\det\bigl(\mathrm{carryBlocks}_b(k, i, j)\bigr)_{1 \le i, j < P_k}
= (-1)^{\binom{P_k - 1}{2}} \in \{-1, 1\}.
```

- **Binary Gray-code carry transitions (`det_grayCarryTransitions`):** For $g(n) = n \oplus \lfloor n / 2 \rfloor$,

```math
\det\bigl(\mathrm{popcnt}(g(i + j) \oplus g(i) \oplus g(j))\bigr)_{1 \le i, j < 2^k}
= (-1)^{\binom{2^k - 1}{2}} 2^{2^k - 1}.
```

### 2. Universal plateau Hankel and mixed-radix digit-length matrices

- **1-based plateau Hankel (`det_plateauHankel_one`):** For any $N \ge 2$ and any $f : \mathbb{N} \to R$ with $f(N - 1) = a$ and $f(n) = a + d$ on $[N, 2N - 2]$, completely independent of $f(0), \dots, f(N - 2)$,

```math
\det\bigl(f(i + j)\bigr)_{1 \le i, j < N}
= (-1)^{\binom{N - 1}{2}} d^{N - 2} (a + d).
```

- **0-based plateau Hankel (`det_plateauHankel_zero`):** For any $1 \le M$ with $2 M \le N$ and any $f : \mathbb{N} \to R$ with $f(n) = a$ on $[M, N)$ and $f(n) = a + d$ on $[N, 2N - 2]$, completely independent of $f(1), \dots, f(M - 1)$,

```math
\det\bigl(f(i + j)\bigr)_{0 \le i, j < N}
= (-1)^{\binom{N - 1}{2}} d^{N - 2} \bigl(f(0)(a + d) - a^2\bigr).
```

- **Mixed-radix digit-length corollaries (`det_mixedDigitLen_one`, `det_mixedDigitLen_zero`):** For any mixed radix $b _ r \ge 2$ and $k \ge 1$, the 1-based and 0-based Hankel determinants of $\mathrm{mlen} _ b(k, i + j)$ equal $(-1)^{\binom{P _ k - 1}{2}} (k + 1)$ and $(-1)^{\binom{P _ k - 1}{2} + 1} k^2$, respectively.

### 3. Ultrametric XOR bit-length matrices

- **Shifted and unshifted XOR bit-length (`det_bitlen_xor_add_const`, `det_bitlen_xor`):** For every $k \in \mathbb{N}$ and every $t \in R$,

```math
\det\bigl(\mathrm{bitlen}(i \oplus j) + t\bigr)_{0 \le i, j < 2^k}
= \bigl((k - 1) 2^k + 1 + t \cdot 2^k\bigr) \prod_{r = 0}^{k - 1} \bigl(-(2^{r + 1} - 1)\bigr)^{2^{k - 1 - r}}.
```

## Prior art and related work

- **Ultrametric, tree-distance, and $(\mathbb{Z}/2\mathbb{Z})^k$-circulant determinants:** The matrix $(\mathrm{bitlen}(i \oplus j) + t) _ {0 \le i,j < 2^k}$ is a group circulant matrix over $(\mathbb{Z}/2\mathbb{Z})^k$ (diagonalizable over $\mathbb{Q}$ by the Walsh-Hadamard transform) and, at $t = 0$, is half the leaf-to-leaf graph distance matrix of the complete binary tree of height $k$. Determinants and inverses of tree-distance and ultrametric matrices belong to the classical lineage of R. L. Graham and H. O. Pollak (*Bell Syst. Tech. J.* **50**, 1971, 2495–2519), S. Martínez, G. Michon, and J. San Martín (*SIAM J. Matrix Anal. Appl.* **15**, 1994, 98–106), R. Nabben and R. S. Varga (*SIAM J. Matrix Anal. Appl.* **15**, 1994, 107–113), and C. Dellacherie, S. Martínez, and J. San Martín (*Inverse M-Matrices and Ultrametric Matrices*, Springer, 2014). The formalization here gives a division-free proof valid over any commutative ring $R$ (including characteristic $2$).
- **Carry-blocks and Gray-code determinants:** These follow the mixed-radix carry-matrix framework in [`../carry-determinants/`](../carry-determinants/), paired with the standard binary-reflected Gray-code transition property $\mathrm{popcnt}(g(i+j) \oplus g(i) \oplus g(j)) = 2 \cdot \mathrm{carryBlocks} _ 2(i, j)$.

## Building and checking

From inside `carry-blocks-determinants/`:

```sh
lake exe cache get
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

To run the full Palomar Comparator check on Linux:

```sh
bash ../.github/scripts/comparator-check.sh
```
