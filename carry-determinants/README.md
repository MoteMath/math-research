# Carry Determinants

Machine-checked Lean 4 / Mathlib formalization of Cantor non-vanishing and exact closed-form multivariate determinant factorizations for mixed-radix Hankel and carry matrices over any commutative ring.

## Main results

For any mixed-radix sequence $b : \mathbb{N} \to \mathbb{N}$ with $b _ r \ge 1$ (or $b _ r \ge 2$ in Theorem 1), place values $P _ r = \prod _ {j < r} b _ j$, $N = P _ k$, suffix products $Q _ j = N / P _ {j+1}$, and any commutative ring $R$:

1. **Cantor non-vanishing (`mixedCarryPolyMatrix_det_ne_zero_iff`, `baseCarryPolyMatrix_det_ne_zero_iff`, `binaryCarryPolyMatrix_det_ne_zero`):** Over any nontrivial commutative ring $R$, the $n \times n$ polynomial carry determinant is nonzero if and only if every mixed-radix digit of $n - 1$ is extremal ($0$ or $b _ r - 1$). In base $2$, every $1 \le n \le 2^k$ has a nonzero determinant (see Prior art below for the $B = 2$ specialization).
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

## Prior art and related work

- **Weighted binary sum-of-digits Hankel determinants (Sobolewski & Ulas, 2026):** B. Sobolewski and M. Ulas, *"Hankel determinants of weighted binary sums of digits"*, [arXiv:2607.09376](https://arxiv.org/abs/2607.09376), study Hankel determinants of weighted binary digit sums $s _ {\mathbf{w}}(n)$ and their first differences $G _ {\mathbf{w}}(n)$, together with the column-modified determinant $\widetilde{\mathcal{G}} _ {\mathbf{w}}(n)$. Via Kummer's identity $s _ {\mathbf{w}}(i) + s _ {\mathbf{w}}(j) - s _ {\mathbf{w}}(i+j) = \sum _ {r=0}^{k-1} c _ r(i,j)(2 w _ r - w _ {r+1})$, the base-$2$ case of `det_weightedLinearCarryMatrix` (with weights $u _ r = 2 w _ r - w _ {r+1}$) is polynomially identical to $\widetilde{\mathcal{G}} _ {\mathbf{w}}(2^k)$, and their evaluation $g(2^m, 1, 1) = -\prod _ {j=1}^m (2^j - 1)^{2^{m-j}}$ equals `det_kummer_padicValNat_choose` at $p = 2$ ($k \ge 2$); choosing $w _ r = r \cdot 2^r$ also recovers `det_binary_carry_word`. The theorems here extend this to multiplicative/exponential multivariate matrices (`det_mixedHankelMatrix`, `det_carryMatrix_full`) in arbitrary mixed radix over arbitrary commutative rings without division.
- **Symmetric Pascal and binary carry matrices (Bacher & Chapman, 2004; Bacher, 2007):** R. Bacher and R. Chapman, *"Symmetric Pascal matrices modulo $p$"*, *Eur. J. Combin.* **25** (2004), 459–473 ([arXiv:math/0212144](https://arxiv.org/abs/math/0212144)), prove $\det(\binom{i+j}{i} \bmod 2) _ {0 \le i, j < n} = \pm 1$ for all $n$. Since $\binom{i+j}{i} \bmod 2$ is `baseCarryPolyMatrix 2 k n` specialized at $X = 0$, this already implies `binaryCarryPolyMatrix_det_ne_zero` over every nontrivial commutative ring. R. Bacher, *"Determinants related to Dirichlet characters modulo 2, 4 and 8 of binomial coefficients and the algebra of recurrence matrices"* ([arXiv:0708.1430](https://arxiv.org/abs/0708.1430)) and *"La suite de Thue-Morse et la catégorie $\mathrm{Rec}$"* ([arXiv:math/0703428](https://arxiv.org/abs/math/0703428)), also evaluate the $X = i$ specialization $\det(i^{v _ 2\binom{i+j}{i}})$ for all $n$. The Cantor extremal-digit characterization for general bases $B \ge 3$ and mixed radices (`mixedCarryPolyMatrix_det_ne_zero_iff`, `baseCarryPolyMatrix_det_ne_zero_iff`) is not covered by those base-$2$ / mod-$p$ Pascal results.
- **Thue-Morse Hankel determinants (APWW, 1998; Han, 2015; Bugeaud & Han, 2014):** J.-P. Allouche, J. Peyrière, Z.-X. Wen, and Z.-Y. Wen, *"Hankel determinants of the Thue-Morse sequence"*, *Ann. Inst. Fourier* **48**(1) (1998), 1–27, prove that $2^{1-n}\det((-1)^{s _ 2(i+j)}) _ {0 \le i,j < n}$ is odd (hence nonzero) for all $n \ge 1$; see also G.-N. Han ([arXiv:1406.1586](https://arxiv.org/abs/1406.1586)), Y. Bugeaud & G.-N. Han ([arXiv:1406.1587](https://arxiv.org/abs/1406.1587)), and [OEIS A186026](https://oeis.org/A186026). Here the exact power-of-two evaluation `det_thueMorse_pow_two` ($= 2^{2^k - 1}$ for $k \ge 2$) arises directly as a specialization of `det_mixedHankelMatrix`.

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
