# Two-Adic Biscaled Det Valuation - exact v2 of det M_n via biscaled unimodular elimination, with supercritical, critical and breakdown regimes (`two-adic-biscaled-det-valuation`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **9 / 10** | **8 / 10** | **8 / 10** | **10 / 10** | **84 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): A complete, sorry-free, pure-Init (zero Mathlib) Lean 4 formalization of a biscaled unimodular elimination engine giving the exact 2-adic valuation of determinants, with perturbation stability and a Mobius compiler for popcount-AND matrices, applied to the five-parameter hybrid matrix family to prove exact valuations in the supercritical regime e*popSum(n) - e, critical regimes popSum(n) - 1 and 2*popSum(n) - 2, the n = 1 jump, and an infinite breakdown line.*

## For Mathematicians

**Mechanism Name:** **2-Adic Bi-Scaled Elimination & Finite-Corner Mod-2 Certification Engine** (with Bit-Sliced 2D Boolean Möbius Compiler and Perturbation Stability Lifter). **Core Silicon Principle (Finite $\to$ Infinite Bridge for ALL $n \in \mathbb{N}$):** Classical Kronecker/Walsh determinant methods require matrix sizes $n = 2^k$ and exact $\mathbb{Z}$-factorizations. In contrast, our engine computes **exact $2$-adic valuations $v _ 2(\det M _ n)$ across ALL $n \in \mathbb{N}$** (including arbitrary non-powers of $2$, non-symmetric, non-Hankel, non-Kronecker matrices whose determinants have wildly growing, non-factorizing odd parts!) via a **three-stage finite-to-infinite pure-silicon pipeline**: 1. **Unimodular Bit-Sliced Elimination + Asymmetric Power-of-$2$ Bi-Scaling (`v2_det_biscaled_elimination_engine`):** Given any $n \times n$ integer matrix $M _ n$, unimodular integer transforms $U _ n, V _ n$ ($\det U _ n = \det V _ n =

## For Non-Mathematicians

A complete, sorry-free, pure-Init (zero Mathlib) Lean 4 formalization of a biscaled unimodular elimination engine giving the exact 2-adic valuation of determinants, with perturbation stability and a Mobius compiler for popcount-AND matrices, applied to the five-parameter hybrid matrix family to prove exact valuations in the supercritical regime e*popSum(n) - e, critical regimes popSum(n) - 1 and 2*popSum(n) - 2, the n = 1 jump, and an infinite breakdown line.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `TwoAdicBiscaledDetValuation/Theorems.lean`, definitions in `TwoAdicBiscaledDetValuation/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `v2_det_biscaled_elimination_engine` | Theorem 1 (Biscaled elimination engine): if unimodular U, V factor M into biscaled form 2^(a i + b j) times an odd-outside matrix Omega with invertible mod-2 leading block, then v2(det M) = sum (a i + b i). |
| `v2_det_perturbation_stability` | Theorem 2 (Perturbation stability): adding a perturbation divisible by one extra power of 2 in the biscaled frame leaves v2(det) unchanged. |
| `mob2_pop_and` | Theorem 3 (Mobius of popcount-AND): the Mobius transform of q^popcount(u AND v) is diagonal with entries (q - 1)^popcount(i). |
| `theorem_1A_supercritical` | Theorem 4 (Supercritical regime): for parameters 2^r u_a, 1 + 2^e u_q with r >= 2e - 1, v2(det) = e * popSum(n) - e for every n >= 2. |
| `theorem_1B_critical_I` | Theorem 5 (Critical regime I): at e = 1, v2(det) = popSum(n) - 1 for every n >= 2. |
| `theorem_1C_critical_II` | Theorem 6 (Critical regime II): at e = 2 with 4 u_a, v2(det) = 2 * popSum(n) - 2 for every n >= 2. |
| `theorem_n1_jump` | Theorem 7 (n = 1 jump): for the 1 x 1 hybrid matrix, v2(det) = 1 for all a, q. |
| `sharpness_S3_infinite_breakdown_line` | Theorem 8 (Infinite breakdown line): for every e >= 3 the subcritical parameter 2^(2e - 2) u_a at n = 4 does not have valuation e * popSum(4) - e. |

## Prior-Art Context

- - **Distinction from Lindström–Wilf (1969/1972) and Boolean-lattice determinants:** Classical Lindström–Wilf factorization yields exact $\mathbb{Z}$-determinants for meet-semilattice matrices $M(i, j) = f(i \,\&\, j)$ (such as $q^{\mathrm{pop}(i \,\&\, j)}$, whose determinant is identically $(q - 1)^{S(n)}$ with no non-trivial odd parts). Our family $M _ n(a, q, \lambda, c, d)$ destroys meet-semilattice factorizability by adding both the $2$-adic ultrametric kernel $a^{v _ 2((i \oplus j) + 1)}$ and the dense asymmetric kernel $2\lambda c^{\mathrm{pop}(j \setminus i)} d^{\mathrm{pop}(i \,\&\, j)}$. Under Möbius conjugation, the matrix does **n
- Hostile-verified PASS by `referee-3`; pure `leanprover/lean4:v4.34.1` `Init` stack with `enable_nanoda: true` and exact integer Python replay in `scripts/explore_and_verify.py`.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).