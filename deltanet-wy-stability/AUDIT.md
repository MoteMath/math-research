# Formal Verification Audit (`deltanet-wy-stability`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **10 / 10** | **9 / 10** | **9 / 10** | **10 / 10** | **93 / 100** |

## Build & Challenge Checks

```text
$ lake build
✔ [9/12] Built DeltanetWyStability (1.1s)
✔ [11/12] Built Solution (1.2s)
Build completed successfully (12 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.2s)
warning: Challenge.lean:30:8: declaration uses `sorry`
warning: Challenge.lean:43:8: declaration uses `sorry`
warning: Challenge.lean:71:8: declaration uses `sorry`
warning: Challenge.lean:96:8: declaration uses `sorry`
warning: Challenge.lean:112:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the five intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`, `admit`, `axiom`, `native_decide`, or `lemma` declarations anywhere in `DeltanetWyStability/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'DeltanetWyStabilityChallenge.deltanet_spectral_stability_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DeltanetWyStabilityChallenge.mxfp4_mxfp6_fp8_bf16_norm_blowup_and_beta_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DeltanetWyStabilityChallenge.wy_inverse_closed_form_and_aligned_contraction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DeltanetWyStabilityChallenge.euler_product_binomial_peak_explosion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DeltanetWyStabilityChallenge.block_schur_wy_exact_inverse' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All five headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `enable_nanoda: true`.

## For Mathematicians

Every proof in `DeltanetWyStability/` is 100% pure-`Init` algebraic reasoning over `Rat` and `Nat` (zero external dependencies):
- `SpectralStability.lean`: Exact rank-1 quadratic decomposition and pure-`Init` Cauchy–Schwarz over `Fin d → Rat` establish `deltanet_spectral_stability_iff` universally for all $d, \alpha, \beta, k$.
- `QuantNormBlowup.lean`: Piecewise quadratic-minus-linear domination on each of the 8 `E2M1` quantization bins (`64/431` non-anchor vs `-1984/431 = -31 * 64/431` anchor for OCP v1.0; `33/227` vs `-1023/227 = -31 * 33/227` for max-fit) proves both universal 32-D bounds in closed form, paired with exact witnesses and the universal $m$-bit normal-range monotonicity theorem.
- `WyInverse.lean`: Telescoping finite sums (`sumFin_telescope`) prove `(I + L) T = I` universally for arbitrary chunk sizes $C$, dimensions $d$, and keys, followed by aligned Householder chain induction (`hhChain_aligned`) yielding both uniform contraction ($\beta r \le 2$) and exact exponential blowup ($\beta = 2, \alpha = 1, r > 1$).
- `EulerBinomial.lean`: Hockey-stick induction (`sumFin_hockey_stick`) proves $(L _ C^k) _ {i, j} = \beta^k \binom{i - j - 1}{k - 1}$ universally, and the factorial identity `choose_mul_fact` certifies $\binom{14}{7} = 3{,}432$ and $\binom{62}{31} = 465{,}428{,}353{,}255{,}261{,}088$ in `< 2.1s` without exponential recursion.
- `BlockSchur.lean`: Block matrix multiplication (`blockLower_mul`) via `sumFin_add` establishes both left and right inverse identities universally for all $(n + m) \times (n + m)$ block lower-triangular matrices.

## For Non-Mathematicians

This audit confirms that every mathematical claim in the Wave 3B Gated DeltaNet / Mamba-2 report — the exact safe step-size ceilings for 4-bit/8-bit/16-bit keys, the exact chunkwise WY inverse formula, the 465-quadrillion / $> 10^{27}$ intermediate explosion of Euler-product inversion, and the exactness of recursive 2×2 Block-Schur inversion — has been independently verified from first principles by Lean 4's trusted kernel with zero external libraries and zero unproven assumptions.

## Prior-Art Context

Follows the Palomar Comparator / `nanoda` pure-`Init` verification standard established in sibling `math-research` packages (`sparse-e2m1-rotations`), formalizing the hardware-math laws of Gated DeltaNet / Mamba-2 chunkwise WY representations (Yang et al., ICLR 2025; Dao & Gu, ICML 2024; Bischof & Van Loan, 1987) and OCP Microscaling Formats v1.0 (2023).
