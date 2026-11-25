# Carry Determinants

Machine-checked Lean 4 / Mathlib formalization of Cantor non-vanishing and exact closed-form multivariate determinant factorizations for mixed-radix Hankel and carry matrices over any commutative ring.

## Main results

For any mixed-radix sequence $b : \mathbb{N} \to \mathbb{N}$ with $b _ r \ge 1$ (or $b _ r \ge 2$ in Theorem 1), place values $P _ r = \prod _ {j < r} b _ j$, $N = P _ k$, suffix products $Q _ j = N / P _ {j+1}$, and any commutative ring $R$:

1. **Cantor non-vanishing (`mixedCarryPolyMatrix_det_ne_zero_iff`, `baseCarryPolyMatrix_det_ne_zero_iff`, `binaryCarryPolyMatrix_det_ne_zero`):** Over any nontrivial commutative ring $R$, the $n \times n$ polynomial carry determinant is nonzero if and only if every mixed-radix digit of $n - 1$ is extremal ($0$ or $b _ r - 1$). In base $2$, every $1 \le n \le 2^k$ has a nonzero determinant.
2. **Multivariate mixed-radix Hankel factorization (`det_mixedHankelMatrix`):**
```math
\det \left( \prod_{r=0}^{k-1} y_r^{d_r(i+j)} \cdot y_k^{\lfloor (i+j)/N \rfloor} \right)_{0 \le i, j < N}
  = (-1)^{\binom{N-1}{2}} \prod_{r=0}^{k-1} \left( y_k - y_r^{N / P_r} \right)^{(b_r - 1) P_r}.
```
3. **Full mixed-radix carry factorization (`det_carryMatrix_full`):**
```math
\det \left( \prod_{r=0}^{k-1} x_r^{e_r(i, j)} \right)_{0 \le i, j < N}
  = (-1)^{\binom{N-1}{2}} \prod_{r=0}^{k-1} \left( \left(\prod_{j=r}^{k-1} x_j^{Q_j}\right) - 1 \right)^{(b_r - 1) P_r}.
```
4. **Binary carry-word determinant (`det_binary_carry_word`):** For every $k \in \mathbb{N}$,
```math
\det \Big( (i + j) \oplus i \oplus j \Big)_{1 \le i, j < 2^k}
  = (-1)^{\binom{2^k - 1}{2}} \cdot 2^{k(2^k - 1)} \cdot \prod_{r=0}^{k-1} (k - r)^{2^r}.
```
5. **Kummer $p$-adic valuation determinant (`det_kummer_padicValNat_choose`):** For every prime $p$ and $k \in \mathbb{N}$,
```math
\det \left( v_p \binom{i+j}{i} \right)_{1 \le i, j < p^k}
  = (-1)^{\binom{p^k - 1}{2}} \prod_{r=0}^{k-1} \left( \frac{p^{k-r} - 1}{p - 1} \right)^{(p - 1) p^r}.
```
6. **Weighted linear carry (`det_weightedLinearCarryMatrix`) and Thue-Morse (`det_thueMorse_pow_two`):** Exact closed-form product formulas for arbitrary carry weights $w _ r$ and for $\det((-1)^{s _ 2(i+j)}) _ {0 \le i, j < 2^k} = 2^{2^k - 1}$ ($k \ge 2$).

## Layout

- [`CarryDeterminants/Defs.lean`](CarryDeterminants/Defs.lean): Pure-Mathlib definitions only (no proofs).
- [`Challenge.lean`](Challenge.lean): Trusted statement file importing only `CarryDeterminants.Defs`, with `sorry` placeholders for Comparator.
- [`CarryDeterminants/MixedRadix.lean`](CarryDeterminants/MixedRadix.lean): Mixed-radix digit/carry identities, generalized Kummer identity, and binary carry-word decomposition.
- [`CarryDeterminants/CantorNonVanishing.lean`](CarryDeterminants/CantorNonVanishing.lean): Vanishing direction, unique place-value pairing, tropical uniqueness, and Cantor characterization.
- [`CarryDeterminants/CarryFactorization.lean`](CarryDeterminants/CarryFactorization.lean): Multivariate factorization proofs and Corollaries 2.1 through 2.4.
- [`Solution.lean`](Solution.lean): Proofs of all 11 challenge statements (zero `sorry`).
- [`scripts/PrintAxioms.lean`](scripts/PrintAxioms.lean) and [`AUDIT.md`](AUDIT.md): Axiom checks and verification record.

## Building and checking

From inside `carry-determinants/`:

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
