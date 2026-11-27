# Two-Adic Newton Poly Optimality (`two-adic-newton-poly-optimality`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **7 / 10** | **8 / 10** | **8 / 10** | **8 / 10** | **10 / 10** | **79 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): Exact two-sided law $N \le 2(D+1) - \mathrm{pop}(D+1)$ for degree-$D$ polynomial 2-adic reciprocals, a universal multiplicative-depth ceiling $2^{k+1}$ for integer circuits, exact valuation orbits for reciprocal and inverse-square-root Newton steps (cubic popcount super-gain), certified from finite affine contraction certificates. Formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

Let $v _ 2$ be the 2-adic valuation and $\mathrm{pop}$ the binary popcount. The formalization contains four layers.

1. **Valuation algebra.** Legendre's law $v _ 2(n!) = n - \mathrm{pop}(n)$ and $v _ 2(2^n\, n!) = 2n - \mathrm{pop}(n)$ as exact valuations, plus an alternating odd-point sum identity equal to $2^n\, n!$ (`altOddSum_eq`) that powers the necessity direction.

2. **Affine contraction certificates.** A finite certificate $(d, s, m _ {\mathrm{crit}})$ for an iteration step gives the exact error valuation orbit $m _ {k+1} = d\, m _ k - s$ for every step count, and the two-sided minimal-step optimality law $(\forall \text{ valid } a,\ 2^N \mid \mathrm{res}) \iff (d - 1) N \le d^k ((d - 1) m _ 0 - s) + s$. Instances: reciprocal iterations of every order $d \ge 2$ with seeds $1$, $a$ and the Dumas seed (exact precisions $d^k$, $3 d^k$, $5 d^k$), and inverse square roots with the quadratic, cubic and quartic steps. The cubic step gains $(3^k - 1)/2$ bits beyond the quadratic baseline (**popcount super-gain**) and the quartic step equals two quadratic steps in valuation.

3. **Polynomial optimality.** For all $D$ and $N$: there is an integer polynomial of degree $\le D$ with $2^N \mid 1 - a\, p(a)$ for every odd $a$ if and only if $N \le 2(D+1) - \mathrm{pop}(D+1)$. Necessity uses only the $D + 2$ odd points $1, 3, \dots, 2D + 3$. For $D + 1 = 2^k$ the optimum is exactly $2^{k+1} - 1$ bits.

4. **Circuit optimality.** Every integer straight-line circuit computing an inverse modulo $2^N$ for all odd $a$ satisfies $N \le 2^{\mathrm{depth} + 1}$ in multiplicative depth (and $N \le 3$ at depth $0$). Kernel-checked sharpness: no cubic polynomial reaches $8$ bits, no depth-0 circuit reaches $4$ bits, and an explicit depth-2 circuit reaches $7$ bits.

## For Non-Mathematicians

Computers often need the inverse of an odd number "modulo a power of two", for instance inside fast division and cryptography. A standard trick is Newton's iteration, which doubles the number of correct bits at every step. This package proves exactly how good such tricks can be. If you are only allowed a polynomial of a given degree, the number of correct bits you can possibly get is an exact formula involving the number of ones in the binary expansion of the degree plus one, and a matching polynomial exists. If you are allowed arbitrary circuits, then the number of multiplications performed one after another sets a hard ceiling on the correct bits. The Lean proofs cover every degree and every precision, not just examples.

**Scope of the formal statement.** A "circuit" is the straight-line `PolyCircuit` of `Defs.lean` over the integers (multiplicative depth counts products); it is not a model of mod-$2^N$ hardware arithmetic.

## Headline Theorems

The trusted statements are in [`Challenge.lean`](Challenge.lean) (namespace `TwoAdicNewtonPolyOptimalityChallenge`) and are proved in [`Solution.lean`](Solution.lean) with identical signatures.

| Theorem | Statement |
| :--- | :--- |
| `fact_exactVal2` | For every $n$, $v _ 2(n!) = n - \mathrm{pop}(n)$ exactly (Legendre). |
| `exact_2adic_poly_reciprocal_optimality` | For all $D, N$: some integer polynomial $p$ of degree at most $D$ satisfies $2^N \mid 1 - a\, p(a)$ for every odd $a$ if and only if $N \le 2(D+1) - \mathrm{pop}(D+1)$. |
| `exact_2adic_poly_optimality_pow2_sub_one` | With at most $2^k$ coefficients the exact optimal precision is $2^{k+1} - 1$ bits. |
| `circuit_mulDepth_optimality_pos` | An integer circuit of multiplicative depth $k \ge 1$ that inverts every odd $a$ modulo $2^N$ has $N \le 2^{k+1}$. |
| `cert_minimal_step_optimality_closed` | For any affine contraction certificate, the universal precision after $k$ steps is exactly the closed form $(d - 1) N \le d^k ((d - 1) m _ 0 - s) + s$. |
| `recip_minimal_step_dumas` | The order-$d$ reciprocal iteration seeded by the Dumas seed inverts every odd $a$ modulo $2^N$ after $k$ steps if and only if $N \le 5 d^k$. |
| `invSqrtS3_popcount_supergain` | The cubic inverse-square-root step has exact error valuation $(3^k (2 m _ 0 - 3) + 3) / 2$, which exceeds the quadratic one by $(3^k - 1)/2$. |
| `invSqrtS4_eq_S2_double_valuation` | The quartic inverse-square-root step after $k$ steps has the same exact valuation $4^k (m _ 0 - 2) + 2$ as the quadratic step after $2k$ steps. |

## Layout

- [`TwoAdicNewtonPolyOptimality/Defs.lean`](TwoAdicNewtonPolyOptimality/Defs.lean): definitions needed to state the headline theorems.
- [`TwoAdicNewtonPolyOptimality/Theorems.lean`](TwoAdicNewtonPolyOptimality/Theorems.lean): all proofs (zero `sorry`, zero `native_decide`, zero custom axioms, no imports beyond `Init`).
- [`scripts/explore_and_verify.py`](scripts/explore_and_verify.py): exact pure-`int` replay and sharpness checks (no floating point).

## Prior-Art Context

- **Newton-Hensel inversion modulo $2^N$:** Hensel lifting and the classical bit-doubling iteration $x \mapsto x(2 - a x)$ (Montgomery 1985; Dumas, *On Newton-Raphson iteration for multiplicative inverses modulo prime powers*, 2014, for the Dumas seed; see also Dumas, arXiv:1209.6626).
- **Valuation of factorials and odd-point interpolation:** Legendre's formula; the exact odd-unit polynomial threshold is Bhargava's theory of generalized factorials (*The factorial function and generalizations*, 1997 / 2000), which the authors' proof does not cite directly. The threshold $2(D+1) - \mathrm{pop}(D+1)$ is the 2-adic valuation of $(2D+2)!$ (Legendre), and the integer sequence $2n - \mathrm{pop}(n)$ is [OEIS A005187](https://oeis.org/A005187), so the polynomial law is closely tied to factorial-valuation theory. The exact two-sided law for reciprocal-fit polynomials, the universal multiplicative-depth ceiling $2^{k+1}$, and the cubic and quartic inverse-square-root valuation laws were not found in the sources above; no search was recorded, and the polynomial law may be known in substance.
- **Review status:** not independently reviewed.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. Toolchain: `leanprover/lean4:v4.34.1`.
