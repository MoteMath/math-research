# Exact Dyadic-Rational ($\mathbb{Z}[1/2]$) Hierarchical Bilinear-Schur Infinite Positive-Definite Form Engine (`dyadic-bilinear-schur-positivity`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **8 / 10** | **8 / 10** | **8 / 10** | **10 / 10** | **82 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): **Mechanism Name:** **Exact $\mathbb{Z}[1/2]$ Hierarchical Bilinear-Schur SOS Lifter** (`DyadicPDEngine`: `BQS`, `PDCert`, `checkStrictPD`, `checkBoundaryStrictPD`).*

## For Mathematicians

A pure-data certificate `PDCert` for a finite bilinear-Schur system `BQS m` (a recursion that builds a quadratic form on vectors indexed by `Fin (2^k)` from forms on the half-size vectors of even and odd entries) is checked by the Boolean function `checkStrictPD`. `soundness_strict_pd` states that if the check passes, then for every `k` and every nonzero `x : Fin (2^k) → Z[1/2]` the target form is strictly positive. As an application, `thm_monnaArch_strict_pd` states `(1/2) μ_k(x)^2 - A_k(x) > 0` for all `k` and nonzero `x`, where `μ_k(x) = 2^{-k} Σ x_i` and `A_k(x) = 2^{-2k} Σ_{i,j} |ρ_k(i) - ρ_k(j)| x_i x_j` with `ρ_k` the bit reversal of the index (a discrete Monna-map distance form). The package also proves the identity `v_2(i xor j) = v_2(|i - j|)` for all `i, j` (`v2Nat_xor_eq_absDiff`) and contains finite instances: a 2×2 minor of determinant `-1/64` showing that naive induction fails, non-commutation of two kernels at `k = 2`, an inequality at `k = 1`, and two concrete values for an asymmetric system.

## For Non-Mathematicians

A computer can check a quadratic expression for positivity only on finitely many inputs. Here a small finite checklist (the certificate) is shown to guarantee positivity of a certain expression for vectors of every length `2^k`, which could not be tested one length at a time. It is applied to a distance-like expression built from reversing the binary digits of an index. Several of the listed results are single concrete cases, not statements for all sizes.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `DyadicBilinearSchurPositivity/Theorems.lean`, definitions in `DyadicBilinearSchurPositivity/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `soundness_strict_pd` | Mode 1 UNIVERSAL INFINITE SOUNDNESS THEOREM: If the finite Z[1/2] certificate passes `checkStrictPD`, then for EVERY `k : Nat` and EVERY nonzero `x : Fin (2^k) → ZHalf`, the target quadratic form is strictly positive! |
| `v2Nat_xor_eq_absDiff` | Pure-silicon 2-adic identity: `v_2(/i - j/) = ctz(i ^^^ j)` for ALL `i, j : Nat`! |
| `thm_monnaArch_strict_pd` | THEOREM 2 (Discrete Archimedean-Monna distance form, strict positivity): For ALL `k : Nat` and ALL nonzero `x : Fin (2^k) → ZHalf`: `(1/2) * μ_k(x)^2 - A_k(x) > 0`. |
| `monnaArch_direct_induction_fails` | Direct-induction obstruction: naive `W = [[1/2, 0], [0, 0]]` produces an INDEFINITE `Δ` (principal 2×2 minor on indices `{0, 3}` has determinant `-1/64 < 0`)! |
| `adelic_kernels_noncommuting` | Non-commutativity witness at `k = 2` (4×4 matrices): `[R_2^{(1)}, A_2] ≠ 0`! |
| `thm_adelic_sharp_dipole_k1` | Machine-checked finite instance: at `k = 1`, for the vector `(1, 0)`, the expression `3 μ² - 4 (μ - 2ν)² - 3 R - 2 A` (with `μ`, `ν`, the 2-adic Riesz form `R` and the Monna form `A`) is negative. |
| `asym_nondiag_asymmetric_diag` | Machine-checked finite instance: `sysAsym.F WAsymIndef 2` takes different values on the basis vectors with indices `0` and `3`. |
| `thm_asym_nondiag_sharp_W00` | Machine-checked finite instance: `sysAsym.F (mat2 0 2 2 (-2)) 1 (vec2 4 1) < 0`. |

## Prior-Art Context

- - **Classical Prior Art (honestly distinguished):** - Negative-type positivity of the continuous 2-adic metric $/x - y/ _ 2^s$ on zero-mean functions (Vladimirov 1994; Albeverio–Khrennikov–Shelkovich 2010, *Theory of $p$-Adic Distributions*) and of the 1D Euclidean metric $/s - t/$ (Schoenberg 1938), as well as the 2-adic-to-real Monna map $\rho : \mathbb{Z} _ 2 \to [0, 1]$ (Monna 1952, *Sur une transformation simple des nombres $p$-adiques en nombres réels*), are classical continuous/analytic objects and theorems proved via Fourier/Walsh transforms, $p$-adic distribution theory, or Brownian-motion integral representations. - Our **contribution** is the Lean-checked finite-certificate lifter described above (the remainder of this sentence is cut off in the original text; no prior-art search was recorded, and the package has not been independently reviewed).
- Built against `leanprover/lean4:v4.34.1` (pure `Init` stack; `enable_nanoda: true` in `comparator.json`); `scripts/explore_and_verify.py` re-evaluates small instances in exact integer arithmetic (it proves nothing by itself).

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).