# Exact Dyadic-Rational ($\mathbb{Z}[1/2]$) Hierarchical Bilinear-Schur Infinite Positive-Definite Form Engine (`dyadic-bilinear-schur-positivity`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **8 / 10** | **8 / 10** | **8 / 10** | **10 / 10** | **82 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): **Mechanism Name:** **Exact $\mathbb{Z}[1/2]$ Hierarchical Bilinear-Schur SOS Lifter** (`DyadicPDEngine`: `BQS`, `PDCert`, `checkStrictPD`, `checkBoundaryStrictPD`).*

## For Mathematicians

**Mechanism Name:** **Exact $\mathbb{Z}[1/2]$ Hierarchical Bilinear-Schur SOS Lifter** (`DyadicPDEngine`: `BQS`, `PDCert`, `checkStrictPD`, `checkBoundaryStrictPD`).

## For Non-Mathematicians

**Mechanism Name:** **Exact $\mathbb{Z}[1/2]$ Hierarchical Bilinear-Schur SOS Lifter** (`DyadicPDEngine`: `BQS`, `PDCert`, `checkStrictPD`, `checkBoundaryStrictPD`).

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `DyadicBilinearSchurPositivity/Theorems.lean`, definitions in `DyadicBilinearSchurPositivity/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `soundness_strict_pd` | Mode 1 UNIVERSAL INFINITE SOUNDNESS THEOREM: If the finite Z[1/2] certificate passes `checkStrictPD`, then for EVERY `k : Nat` and EVERY nonzero `x : Fin (2^k) → ZHalf`, the target quadratic form is strictly positive! |
| `v2Nat_xor_eq_absDiff` | Pure-silicon 2-adic identity: `v_2(/i - j/) = ctz(i ^^^ j)` for ALL `i, j : Nat`! |
| `thm_monnaArch_strict_pd` | THEOREM 2 (Sharp Discrete Archimedean-Monna Distance Form Strict Positivity): For ALL `k : Nat` and ALL nonzero `x : Fin (2^k) → ZHalf`: `(1/2) * μ_k(x)^2 - A_k(x) > 0`. |
| `monnaArch_direct_induction_fails` | Direct-induction obstruction: naive `W = [[1/2, 0], [0, 0]]` produces an INDEFINITE `Δ` (principal 2×2 minor on indices `{0, 3}` has determinant `-1/64 < 0`)! |
| `adelic_kernels_noncommuting` | Non-commutativity witness at `k = 2` (4×4 matrices): `[R_2^{(1)}, A_2] ≠ 0`! |
| `thm_adelic_sharp_dipole_k1` | Machine-checked infinite theorem `thm_adelic_sharp_dipole_k1` proved in pure Lean 4 `Init`. |
| `asym_nondiag_asymmetric_diag` | Machine-checked infinite theorem `asym_nondiag_asymmetric_diag` proved in pure Lean 4 `Init`. |
| `thm_asym_nondiag_sharp_W00` | Machine-checked infinite theorem `thm_asym_nondiag_sharp_W00` proved in pure Lean 4 `Init`. |

## Prior-Art Context

- - **Classical Prior Art (honestly distinguished):** - Negative-type positivity of the continuous 2-adic metric $/x - y/ _ 2^s$ on zero-mean functions (Vladimirov 1994; Albeverio–Khrennikov–Shelkovich 2010, *Theory of $p$-Adic Distributions*) and of the 1D Euclidean metric $/s - t/$ (Schoenberg 1938), as well as the 2-adic-to-real Monna map $\rho : \mathbb{Z} _ 2 \to [0, 1]$ (Monna 1952, *Sur une transformation simple des nombres $p$-adiques en nombres réels*), are classical continuous/analytic objects and theorems proved via Fourier/Walsh transforms, $p$-adic distribution theory, or Brownian-motion integral representations. - Our **contributi
- Hostile-verified PASS by `referee-4`; pure `leanprover/lean4:v4.34.1` `Init` stack with `enable_nanoda: true` and exact integer Python replay in `scripts/explore_and_verify.py`.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).