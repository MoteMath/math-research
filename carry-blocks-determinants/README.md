# Carry-Blocks, Plateau Hankel, and Ultrametric XOR Determinants

Lean 4 (Mathlib `v4.34.1`) formalization of four exact closed-form determinant families valid over an arbitrary commutative ring $R$ (all proofs are division-free and hold in every characteristic).

## Main results

The trusted statement file [`Challenge.lean`](Challenge.lean) declares 10 universal determinant theorems:

### 1. Mixed-radix carry-blocks and Gray-code transitions

For any mixed radix $b : \mathbb{N} \to \mathbb{N}$ with $b _ r \ge 1$ and place values $P _ k = \prod _ {r < k} b _ r$, let $\mathrm{carryBlocks} _ b(k, i, j)$ denote the number of maximal contiguous `1`-runs in the first $k$ mixed-radix carry bits of $i + j$.

- **Exponential carry-blocks (`det_mixedCarryBlocks_exp`):** For every $x \in R$,

```math
\det\bigl(x^{\mathrm{carryBlocks} _ b(k, i, j)}\bigr) _ {0 \le i, j < P _ k}
= (-1)^{\binom{P _ k - 1}{2}} (x - 1)^{P _ k - 1}.
```

- **Linear carry-blocks unimodularity (`det_mixedCarryBlocks_linear`, `det_binaryCarryBlocks`):** Extracted from `det_mixedCarryBlocks_exp` over $R[X]$ at $x = X + 1$ with zero division:

```math
\det\bigl(\mathrm{carryBlocks} _ b(k, i, j)\bigr) _ {1 \le i, j < P _ k}
= (-1)^{\binom{P _ k - 1}{2}} \in \{-1, 1\}.
```

- **Binary Gray-code carry transitions (`det_grayCarryTransitions`):** For $g(n) = n \oplus \lfloor n / 2 \rfloor$,

```math
\det\bigl(\mathrm{popcnt}(g(i + j) \oplus g(i) \oplus g(j))\bigr) _ {1 \le i, j < 2^k}
= (-1)^{\binom{2^k - 1}{2}} 2^{2^k - 1}.
```

### 2. Universal plateau Hankel and mixed-radix digit-length matrices

- **1-based plateau Hankel (`det_plateauHankel_one`):** For any $N \ge 2$ and any $f : \mathbb{N} \to R$ with $f(N - 1) = a$ and $f(n) = a + d$ on $[N, 2N - 2]$, completely independent of $f(0), \dots, f(N - 2)$,

```math
\det\bigl(f(i + j)\bigr) _ {1 \le i, j < N}
= (-1)^{\binom{N - 1}{2}} d^{N - 2} (a + d).
```

- **0-based plateau Hankel (`det_plateauHankel_zero`):** For any $1 \le M$ with $2 M \le N$ and any $f : \mathbb{N} \to R$ with $f(n) = a$ on $[M, N)$ and $f(n) = a + d$ on $[N, 2N - 2]$, completely independent of $f(1), \dots, f(M - 1)$,

```math
\det\bigl(f(i + j)\bigr) _ {0 \le i, j < N}
= (-1)^{\binom{N - 1}{2}} d^{N - 2} \bigl(f(0)(a + d) - a^2\bigr).
```

- **Mixed-radix digit-length corollaries (`det_mixedDigitLen_one`, `det_mixedDigitLen_zero`):** For any mixed radix $b _ r \ge 2$ and $k \ge 1$, the 1-based and 0-based Hankel determinants of $\mathrm{mlen} _ b(k, i + j)$ equal $(-1)^{\binom{P _ k - 1}{2}} (k + 1)$ and $(-1)^{\binom{P _ k - 1}{2} + 1} k^2$, respectively.

### 3. Ultrametric XOR bit-length matrices

- **Shifted and unshifted XOR bit-length (`det_bitlen_xor_add_const`, `det_bitlen_xor`):** For every $k \in \mathbb{N}$ and every $t \in R$,

```math
\det\bigl(\mathrm{bitlen}(i \oplus j) + t\bigr) _ {0 \le i, j < 2^k}
= \bigl((k - 1) 2^k + 1 + t \cdot 2^k\bigr) \prod _ {r = 0}^{k - 1} \bigl(-(2^{r + 1} - 1)\bigr)^{2^{k - 1 - r}}.
```

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
