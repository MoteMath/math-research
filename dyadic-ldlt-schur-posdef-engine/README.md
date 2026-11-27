# Exact Dyadic LDL-Transpose Positive-Definiteness Infinite Certificate Engine (`dyadic-ldlt-schur-posdef-engine`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **89 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): division-free exact $LDL ^ T$ over $\mathbb{Z}[1/2]$ with a non-scalar Schur-system automaton lifting finite pivot recursions to every dimension, applied to four non-Kronecker bitwise kernel families with sharp thresholds and explicit failing witnesses, formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

Over the exact ordered ring $\mathbb{Z}[1/2]$ of dyadic rationals (`Dyad`, mantissa and shift, decidable order, no reals) we prove: given an exact factorization $M = L D L ^ T$ with $L$ unit lower triangular, $M$ is strictly positive definite if and only if every pivot $D(r)$ is positive (`ldlt_strictlyPosDef_iff`), and a uniform pivot lower bound $\delta$ yields $v ^ T M v \ge \delta \sum _ r ((L ^ T v) _ r) ^ 2$ (`ldlt_quadForm_lower_bound`). Elimination commutes with taking leading blocks (`ldlt_prefix_restrict`).

The infinite-dimensional engine is a **non-scalar Schur system** (`SchurSystem`, `block_schur_ldlt_step`, `schurSystem_nested_iff`): a finite state recursion produces the Schur pivots for dyadic block sizes $2 ^ k$ and, by prefix restriction, for every $n$, supporting scalar, anti-diagonal and rank-one boundary couplings. It decides four families built from the van der Corput radical inverse $\phi _ 2$: the Hamming family is positive definite for all $n$ iff $4 \beta \le 3 c$ with critical instance $(4, 3)$ and a sharp failure at $n = 16$ for $(15/4, 3)$ (`vdcHamming_*`); a weighted family with uniform pivot bound; a Gray-weighted family positive definite for all $n$ with pivot bounds $2/3$ and $5/8$ (`grayWeighted_*`); and an exponential family with critical ratio $7/6$ and a $2$-sparse negative witness at $n = 32$ (`expVdc_*`).

## For Non-Mathematicians

A symmetric grid of numbers is "positive definite" if every nonzero weighting gives a positive total, a property needed for statistics and optimization. For an infinite family of grids it seems impossible to check every size. We build an exact bookkeeping method using only whole numbers and halves, with no rounding, whose pivots come from a small repeating recipe, and use it to find the precise tipping points of four families of bit-patterned grids, including cases that pass up to size $15$ or $31$ and then fail.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `DyadicLdltSchurPosdefEngine/Theorems.lean`, definitions in `DyadicLdltSchurPosdefEngine/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

**Scope of the formal statement.** Positive definiteness is stated for test vectors with entries in the dyadic ring $\mathbb{Z}[1/2]$ (the bespoke `Dyad` type), not for real vectors; the two notions agree by density of $\mathbb{Z}[1/2]$ in $\mathbb{R}$, which is not formalized here.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `ldlt_strictlyPosDef_iff` | Given an exact dyadic factorization $M = L D L ^ T$, $M$ is strictly positive definite if and only if every pivot $D(r)$ with $r < N$ is positive. |
| `ldlt_quadForm_lower_bound` | If every pivot satisfies $\delta \le D(r)$, then $\delta \sum _ r ((L ^ T v) _ r) ^ 2 \le v ^ T M v$ for every vector $v$. |
| `schurSystem_nested_iff` | For a nested Schur system agreeing with $M$ on all dyadic prefixes, every $n \times n$ leading block is strictly positive definite if and only if all Schur pivots up to $n$ are positive. |
| `vdcHamming_strictlyPosDef_all_n_iff` | For $\beta > 0$, the van der Corput Hamming matrix with parameters $(c, \beta)$ is strictly positive definite for every $n$ if and only if $4 \beta \le 3 c$. |
| `vdcHamming_critical_4_3_all_n` | At the critical parameters $(c, \beta) = (4, 3)$ the van der Corput Hamming matrix is strictly positive definite for every $n$. |
| `vdcHamming_sharp_15_4_fails_16` | At the parameters $(15/4, 3)$ the matrix is not strictly positive definite at $n = 16$ (although all smaller sizes pass). |
| `grayWeighted_strictlyPosDef_all_n` | The Gray-weighted dyadic matrix is strictly positive definite for every $n$. |
| `expVdc_critical_7_6_all_n` | The exponential van der Corput matrix with parameters $(7, 6)$ is strictly positive definite for every $n$. |

## Proof Architecture

1. **Exact dyadic ring (`Dyad`):** mantissa-and-shift representation of $\mathbb{Z}[1/2]$ with decidable equality and order and a proved ordered-ring structure.
2. **Division-free $LDL ^ T$ (`IsLDLTAlg`, `ldlt_strictlyPosDef_iff`, `ldlt_quadForm_lower_bound`, `ldlt_prefix_restrict`):** positive definiteness reduces to positivity of pivots, which are computed without division.
3. **Non-scalar Schur automaton (`SchurSystem`, `block_schur_ldlt_step`, `schurSystem_pivot_lb`, `schurSystem_nested_iff`):** a finite recursion on $2 \times 2$ block states computes pivots for all dyadic sizes and, by prefix restriction, for all $n$.
4. **Four families (`vdcHamming_*`, `weightedVdc_*`, `grayWeighted_*`, `expVdc_*`) and sharpness:** sharp thresholds, uniform pivot bounds, distinct fractal $L$ factors for Gray $J _ k$, and explicit finite failing witnesses, with kernel-checked non-vacuity.

## Prior-Art Context

- **Classical background:** plain $2 ^ {- \mathrm{pop}(x \oplus y)}$ is a Kronecker power of a $2 \times 2$ matrix, plain $2 ^ {- \lvert x - y \rvert}$ is the Kac-Murdock-Szego (1953) AR(1) Toeplitz covariance kernel (J. Rational Mech. Anal. 2, 767-800), and the base-2 van der Corput radical inverse is classical in quasi-Monte Carlo theory (Dick and Pillichshammer, *Digital Nets and Sequences*, Cambridge Univ. Press, 2010).
- **Contents (not independently reviewed; no prior-art search is recorded):** the division-free $\mathbb{Z}[1/2]$ $LDL ^ T$ iff engine, the non-scalar `SchurSystem` automaton and the four sharp-threshold families (Hamming, weighted, Gray-weighted, exponential).

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).
