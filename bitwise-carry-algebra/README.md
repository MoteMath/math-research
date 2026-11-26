# Bitwise Carry Algebra

Zero-Mathlib (`Init`-only) Lean 4 formalization of algebraic 2-cocycle laws for binary addition carries, Gray-code carry transitions, borrow-carry duality, and exact closed-form enumerations over $[0, 2^k) \times [0, 2^k)$.

## Main results

The trusted statement file [`Challenge.lean`](Challenge.lean) declares 8 universal theorems:

- **Carry-word 2-cocycle (`carryWord_cocycle`):** For $c(x, y) = (x + y) \oplus x \oplus y$,
  $c(x, y) \oplus c(x + y, z) \oplus c(y, z) \oplus c(x, y + z) = 0$ for all $x, y, z \in \mathbb{N}$.
- **Carry-popcount 2-cocycle (`carryPop_cocycle`):**
  $\mathrm{popcnt}(c(x, y)) + \mathrm{popcnt}(c(x + y, z)) = \mathrm{popcnt}(c(y, z)) + \mathrm{popcnt}(c(x, y + z))$ for all $x, y, z \in \mathbb{N}$.
- **Gray-code additivity defect (`gray_add_xor_eq_gray_carryWord`):** For $g(n) = n \oplus \lfloor n / 2 \rfloor$,
  $g(x + y) \oplus g(x) \oplus g(y) = g(c(x, y))$ for all $x, y \in \mathbb{N}$.
- **Gray-carry transition law (`popcnt_gray_carryWord`):**
  $\mathrm{popcnt}(g(x + y) \oplus g(x) \oplus g(y)) = 2 \cdot \mathrm{carryBlocks}(x, y)$ for all $x, y \in \mathbb{N}$, where $\mathrm{carryBlocks}(x, y)$ counts maximal contiguous runs of `1`-bits in the carry word $c(x, y)$.
- **Borrow-carry duality (`borrowWord_eq_carryWord`):** For the subtraction borrow word $b(x, y) = |x - y| \oplus x \oplus y$,
  $b(x, y) = c(\min(x, y), \max(x, y) - \min(x, y))$.
- **Exact total carry count (`sumSquare_carryPop`):**
  $2 \sum _ {0 \le i, j < 2^k} \mathrm{popcnt}(c(i, j)) + 4^k = k \cdot 4^k + 2^k$.
- **Exact total carry-block count (`sumSquare_carryBlocks`):**
  $8 \sum _ {0 \le i, j < 2^k} \mathrm{carryBlocks}(i, j) + 2 \cdot 2^k = (k + 2) \cdot 4^k$.
- **Zero-carry and single-carry-block pair counts (`count_zero_and_one_carryBlock`):**
  Over $[0, 2^k)^2$ there are exactly $3^k$ zero-carry pairs, and over $[0, 2^{k+2})^2$ there are exactly $(k + 2)(k + 7) \cdot 3^k / 2$ pairs with exactly one maximal carry block.

## Building and checking

From inside `bitwise-carry-algebra/` (no Mathlib cache needed):

```sh
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

To run the full Palomar Comparator check on Linux:

```sh
bash ../.github/scripts/comparator-check.sh
```
