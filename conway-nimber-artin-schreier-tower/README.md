# Fermat-Tower Artin–Schreier Contraction & Block-Periodicity Engine (`adic-3`) (`conway-nimber-artin-schreier-tower`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **9 / 10** | **8 / 10** | **8 / 10** | **10 / 10** | **84 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): **Mechanism Name:** **Fermat-Tower Artin–Schreier Contraction & Block-Periodicity Compiler** (`ConwaySilicon.Nim`) **Core Silicon Principle (Finite $\to$ Infinite Bridge):** Conway's infinite nimber field $(\mathbb{N}, \oplus, \otimes) \cong \overline{\mathbb{F} _ 2} = \bigcup _ {k \ge 0} \mathbb{F} _ {2^{2^k}}$ is formalized directly as an inductive tower of depth-$k$ perfect*

## For Mathematicians

**Mechanism Name:** **Fermat-Tower Artin–Schreier Contraction & Block-Periodicity Compiler** (`ConwaySilicon.Nim`) **Core Silicon Principle (Finite $\to$ Infinite Bridge):** Conway's infinite nimber field $(\mathbb{N}, \oplus, \otimes) \cong \overline{\mathbb{F} _ 2} = \bigcup _ {k \ge 0} \mathbb{F} _ {2^{2^k}}$ is formalized directly as an inductive tower of depth-$k$ perfect binary bit-trees (`Nim k`, isomorphic to `Fin (2^(2^k))`), where: - nim-addition $\oplus$ is bitwise tree-XOR (`Nat.xor`), - half-Fermat scaling $S _ k(x) = x \otimes H _ k$ (where $H _ k = 2^{2^k - 1}$) is a 2-line divide-and-conquer linear bit-tree operator $S _ {k+1}(a, b) = (S _ k(a \oplus b),\; S _ k^2(a))$, - nim-multiplication $\otimes$ is Karatsuba/Fermat-block splitting over $F _ k^{\otimes 2} = F _ k \oplus H _ k$ (where $F _ k = 2^{2^k}$), - Frobenius squaring $\Phi _ k(x) = x^{\otimes 2}$ is $\Phi _ {k+1}(a, b) = (\Phi _ k(a),\; \Phi _ k(b) \oplus S _

## For Non-Mathematicians

**Mechanism Name:** **Fermat-Tower Artin–Schreier Contraction & Block-Periodicity Compiler** (`ConwaySilicon.Nim`) **Core Silicon Principle (Finite $\to$ Infinite Bridge):** Conway's infinite nimber field $(\mathbb{N}, \oplus, \otimes) \cong \overline{\mathbb{F} _ 2} = \bigcup _ {k \ge 0} \mathbb{F} _ {2^{2^k}}$ is formalized directly as an inductive tower of depth-$k$ perfect

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `ConwayNimberArtinSchreierTower/Theorems.lean`, definitions in `ConwayNimberArtinSchreierTower/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `mul_inv` | Simultaneous proof of field invertibility `x ≠ 0 → x ⊗ inv x = 1` for all `k`. |
| `wp_bitLen_contraction` | **Theorem B (Exact Artin-Schreier Bit-Length Contraction):** For every Fermat block `k` and every nonzero nimber `x ∈ Nim k`, applying `℘_k(x) = x^2 ⊕ x` drops `bitLen` by **exactly 1**. |
| `cosetHarmonic_eq_inv_wpIter` | **Theorem D2 (Universal Coset Nim-Harmonic Law):** For ALL `k`, ALL `m ≤ 2^k`, and ALL `X ∈ Nim k` with `X.toNat ≥ 2^m`: `⨁_{a < 2^m} (X ⊕ a)^{-1} = (℘^m(X))^{-1}`. |
| `powerSum_binary_collapse` | **Theorem E4 (Binary Power-Sum Collapse):** For ALL `k`, ALL `m ≤ 2^k` (even when `m` is NOT a power of 2, so `[0, 2^m)` is NOT a field!), and ALL exponents `d : Nat`: `⨁_{x < 2^m} x^d ∈ {0, 1}`. |
| `finite_table_evaluates_all_m` | **Theorem G4 (Finite-to-Infinite Evaluation Compiler):** For ANY `k, m, r, n` with `r < 2^k` and `m + r < 2^n`, the exponentially large `2^m`-term dyadic-coset nim-product `⨂_{a < 2^m} (2^(m + r) ⊕ a)` is **identically equal** to a single finite-table lookup at `m % 2^k` inside the fixed finite block `Nim (k + 1)`! |
| `dyadicProd_fourth_shell_period4` | For ALL blocks `n` and ALL `m` with `m + 3 < 2^n`, the fourth-shell coset nim-product `⨂_{a < 2^m} (2^(m+3) ⊕ a)` cycles with **exact period 4** through `[8, 8, 10, 11]`. |
| `sharpness_period_fails_at_k1_r2` | **Sharpness 1a:** Period `2^k` in Theorem G1/G2 FAILS at the exact boundary `r = 2^k` for `k = 1` (`r = 2`: `f_2(0) = 4 ≠ 5 = f_2(2)`). |
| `sharpness_popcount_boundary_nonzero` | **Sharpness 5:** Popcount Annihilation (`popcount d < m → S(m, d) = 0`, Theorem E2) FAILS at the exact boundary `popcount d = m` (`d = 2^m - 1`) for EVERY `k, m ≤ 2^k`! |

## Prior-Art Context

- - **Classical / Known Prior Art (explicitly credited as foundations, NOT claimed as novel):** - Conway (1976, *On Numbers and Games*, Ch. 6) and Lenstra (1977/1978, *On the algebraic closure of two* & *Nim Multiplication*, IHES / Séminaire de Théorie des Nombres de Bordeaux 1977–1978): $(\mathbb{N}, \oplus, \otimes)$ is $\overline{\mathbb{F} _ 2}$ via the Artin–Schreier tower $F _ k^2 + F _ k = H _ k$, with $[0, 2^{2^k}) \cong \mathbb{F} _ {2^{2^k}}$. - Moore (1896, *A two-fold generalization of Fermat's theorem*) and Ore (1933, *On a special class of polynomials*): linearized ($q$-)polynomials, Moore determinants, and subspace polynomials $\
- Hostile-verified PASS by `referee-4`; pure `leanprover/lean4:v4.34.1` `Init` stack with `enable_nanoda: true` and exact integer Python replay in `scripts/explore_and_verify.py`.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).