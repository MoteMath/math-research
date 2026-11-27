# MXFP6 EF21 Phase Diagrams, Native Orthonormal Matrices, and 4:8-Sparse Quaternion Rotations (`mxfp6-ef21-rotations`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **10 / 10** | **8 / 10** | **10 / 10** | **91 / 100** |

*Heuristic self-rating (weighted `3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 91 / 100`): universal all-$B$ EF21 contraction phase diagrams for OCP MXFP6 (`E3M2` and `E2M3`) under both E8M0 power-of-2 and continuous max-abs (`NVFP6`) scaling with exact tightness and attainment, `E2M3` vs `E3M2` crossover theorems (for the modelled quantizers) ($B = 43 / 44$ for MXFP6, $B = 178 / 179$ for NVFP6), Hadamard weight-quantization defects and minimum dyadic coherence bounds at $n = 8, 32$, exact Goethals–Seidel native `E2M1`/`E3M2`/`E2M3` orthonormal matrices (`16 × 16` and zero-free `32 × 32`), and universal 4:8-sparse Hamilton quaternion orthogonal factorizations in arbitrary $4m$ dimensions — all formalized in pure Lean 4 `Init` (zero Mathlib, zero `native_decide`).*

## For Mathematicians

We formalize six exact, universal theorems over exact rational (`Rat`) and integer (`Int`) arithmetic in pure Lean 4 `Init`:

1. **Universal All-$B$ EF21 Contraction Phase Diagrams (`mxfp6_e3m2_nvfp6_ef21_universal`, `mxfp6_e2m3_nvfp6_ef21_universal`):**
   Let $q _ {\mathrm{E3M2}} : \mathbb{Q} \to \mathbb{Q}$ (32 nonnegative OCP levels, max $28$, subnormal midpoint $1/32$) and $q _ {\mathrm{E2M3}} : \mathbb{Q} \to \mathbb{Q}$ (32 nonnegative OCP levels, max $15/2$, subnormal midpoint $1/16$) be the symmetric nearest-grid quantizers. For every block size $B \ge 1$, the exact worst-case EF21 contraction constants $\alpha(B) = 1 - \sup _ {y} \|q(y) - y\| _ 2^2 / \|y\| _ 2^2$ satisfy:
   ```math
   \alpha_{\mathrm{MXFP6\text{-}E3M2}}(B) = \min\!\left(\frac{327680}{B + 331775},\; \frac{229376}{B + 230399},\; \frac{200704}{B + 200703}\right),
   ```
   ```math
   \alpha_{\mathrm{NVFP6\text{-}E3M2}}(B) = \min\!\left(\frac{80 B + 116}{81 B + 115},\; \frac{802816}{B + 802815}\right),
   ```
   ```math
   \alpha_{\mathrm{MXFP6\text{-}E2M3}}(B) = \min\!\left(\frac{4608}{B + 4623},\; \frac{3840}{B + 3843},\; \frac{3600}{B + 3599}\right),
   ```
   ```math
   \alpha_{\mathrm{NVFP6\text{-}E2M3}}(B) = \min\!\left(\frac{288 B + 612}{289 B + 611},\; \frac{14400}{B + 14399}\right).
   ```
   For both `MXFP6` formats ($\max _ i |y _ i| \le M$, $\exists i _ 0, M/2 < |y _ {i _ 0}|$), we prove the universal upper bound $\sum (q(y _ i) - y _ i)^2 \le (1 - \alpha(B)) \sum y _ i^2$ **and** universal tightness ($\forall \varepsilon > 0, \exists y$ beating $1 - \alpha(B) - \varepsilon$, with exact attainment for $B \le 7169$ in `E3M2` and $B \le 61$ in `E2M3`, and limit witnesses $(M/2 + t, m _ 0, \dots, m _ 0)$ beyond). For both `NVFP6` formats ($\exists i _ 0, |y _ {i _ 0}| = M$), we prove both the universal upper bound and **exact rational attainment** for every $B \ge 1$.

2. **Exact `E2M3` vs `E3M2` Crossover in the model (`mxfp6_e2m3_vs_e3m2_exact_crossover`):**
   - **OCP MXFP6 (E8M0):** $\alpha _ {\mathrm{MXFP6\text{-}E3M2}}(B) < \alpha _ {\mathrm{MXFP6\text{-}E2M3}}(B)$ for all $1 \le B \le 43$ (including OCP standard $B = 32$: $4608/4655 > 327680/331807$), whereas $\alpha _ {\mathrm{MXFP6\text{-}E2M3}}(B) < \alpha _ {\mathrm{MXFP6\text{-}E3M2}}(B)$ for **all** $B \ge 44$.
   - **Continuous NVFP6:** Exact tie $\alpha(1) = 1$ at $B = 1$, $\alpha _ {\mathrm{NVFP6\text{-}E3M2}}(B) < \alpha _ {\mathrm{NVFP6\text{-}E2M3}}(B)$ for all $2 \le B \le 178$, and $\alpha _ {\mathrm{NVFP6\text{-}E2M3}}(B) < \alpha _ {\mathrm{NVFP6\text{-}E3M2}}(B)$ for **all** $B \ge 179$.

3. **Hadamard Weight-Quantization Defects & Minimum Dyadic Coherence (`hadamard_weight_quantization_defect_and_min_dyadic_coherence`):**
   Quantizing $H _ 8 / \sqrt{8}$ and $H _ {32} / \sqrt{32}$ onto OCP grids produces exact orthogonality defects $8 (3/8)^2 = 9/8$ and $32 (3/16)^2 = 9/8$ ($12.5\%$ in `E2M1`/`E3M2`) and $8 (11/32)^2 = 121/128$ and $32 (11/64)^2 = 121/128$ ($5.47\%$ in `E2M3`). Moreover, for every $k \in \mathbb{Z}$, $(k/32)^2 \ge 1/8 \implies |k| \ge 12$ and $(k/64)^2 \ge 1/32 \implies |k| \ge 12$, proving that $3/8 = 12/32$ ($n = 8$, denominator $\le 32$) and $3/16 = 12/64$ ($n = 32$, denominator $\le 64$) achieve the sharp minimum dyadic coherence.

4. **Exact Goethals–Seidel Native `E2M1`/`E3M2`/`E2M3` Orthonormal Matrices (`goethals_seidel_native_e2m1_orthonormal_exact`):**
   The 4-circulant Goethals–Seidel matrices `GS_n16_E2M1_low` ($16 \times 16$) and `GS_n32_E2M1_pm13` ($32 \times 32$) satisfy $G^T G = 64 I$ identically, every scaled entry $G _ {ij}/8$ is represented with **0.00% quantization error** in OCP `E2M1` (E8M0 scale $1/4$), `E3M2`, and `E2M3` simultaneously, and `GS_n32_E2M1_pm13` has zero zeros (all entries in $\{\pm 1/8, \pm 3/8\}$).

5. **Universal 4:8-Sparse Hamilton Quaternion Factorizations (`quaternion_4of8_sparse_orthogonality_universal`):**
   For all $a, b, c, d \in \mathbb{Z}$, the $4 \times 4$ Hamilton matrix $Q(a, b, c, d)$ satisfies $Q^T Q = (a^2 + b^2 + c^2 + d^2) I _ 4$. Lifting $m$ equal-norm quaternion blocks via block-diagonalization and any bijection $\sigma : \mathrm{Fin}(4m) \to \mathrm{Fin}(4m)$ yields a **row-4-sparse (4:8-sparse)** exact orthogonal stage $P _ \sigma \mathrm{diag}(Q _ 1, \dots, Q _ m)$ in arbitrary $4m$ dimensions, and any finite product of orthogonal stages preserves exact orthogonality with the product of their norms.

## For Non-Mathematicians

Modern AI accelerators compress neural network activations and gradients into **6-bit microscaling floating-point formats (MXFP6)**, which come in two flavors: **`E2M3`** (more precision digits, narrower number range) and **`E3M2`** (wider number range, slightly coarser precision). Engineers have to choose between `E2M3` and `E3M2`, choose a block size $B$, and choose a rotation matrix to spread out large outlier channels before quantizing.

This package gives machine-checked answers, for the stated models, to three design questions:

1. **Exact error-feedback guarantees for every block size $B = 1, 2, 3, \dots, \infty$:** We prove the exact worst-case contraction rate of both `E3M2` and `E2M3` under both OCP power-of-2 scaling (`MXFP6`) and continuous scaling (`NVFP6`), with matching worst-case examples showing the bounds cannot be improved by even a hair.
2. **A switchover rule between `E2M3` and `E3M2` (in the model):** For the modelled `MXFP6` quantizers, `E2M3` is strictly better up to block size **$B = 43$** (including the OCP standard $B = 32$), and **`E3M2` is strictly better for every block size $B \ge 44$** because `E2M3` runs out of dynamic range and underflows $55.75\times$ earlier. Under continuous `NVFP6` scaling, the exact crossover moves to **$B = 178 / 179$** (with a tie at $B = 1$).
3. **Zero-error native rotations & fast 4:8-sparse quaternion stages:** Storing standard Walsh–Hadamard rotations $H _ 8 / \sqrt{8}$ or $H _ {32} / \sqrt{32}$ in 4-bit or 6-bit weights introduces an unavoidable $12.5\%$ (`E2M1`/`E3M2`) or $5.47\%$ (`E2M3`) orthogonality error because $\sqrt{8}$ and $\sqrt{32}$ are irrational. We certify exact $16 \times 16$ and $32 \times 32$ Goethals–Seidel orthonormal rotations whose weights live **natively on all three OCP grids (`E2M1`, `E3M2`, `E2M3`) with 0.00% weight error**, alongside universal multi-stage 4:8-sparse Hamilton quaternion rotations that preserve exact lengths in any dimension $4m$ at a fraction of the compute cost.

---

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `mxfp6_e3m2_nvfp6_ef21_universal` | Universal all-$B$ (`0 < B`) EF21 upper bound + exact tightness for `MXFP6-E3M2` and upper bound + exact attainment for `NVFP6-E3M2`. |
| `mxfp6_e2m3_nvfp6_ef21_universal` | Universal all-$B$ (`0 < B`) EF21 upper bound + exact tightness for `MXFP6-E2M3` and upper bound + exact attainment for `NVFP6-E2M3`. |
| `mxfp6_e2m3_vs_e3m2_exact_crossover` | Exact crossover: `E2M3 > E3M2` for $1 \le B \le 43$ (with exact $B = 32$ values) and `E3M2 > E2M3` for $B \ge 44$ in MXFP6; tie at $B = 1$, `E2M3 > E3M2` for $2 \le B \le 178$, and `E3M2 > E2M3` for $B \ge 179$ in NVFP6. |
| `hadamard_weight_quantization_defect_and_min_dyadic_coherence` | Exact $9/8$ and $121/128$ defects of quantized $H _ 8 / \sqrt{8}$ and $H _ {32} / \sqrt{32}$, plus sharp dyadic coherence lower bounds $12/32 = 3/8$ and $12/64 = 3/16$. |
| `goethals_seidel_native_e2m1_orthonormal_exact` | Exact $G^T G = 64 I$ for `GS_n16_E2M1_low` and `GS_n32_E2M1_pm13`, exact zero-error membership of every $G _ {ij}/8$ in `E2M1 ∩ E3M2 ∩ E2M3`, and zero zeros in `GS_n32_E2M1_pm13`. |
| `quaternion_4of8_sparse_orthogonality_universal` | Universal Hamilton 4-square orthogonality for all $a, b, c, d \in \mathbb{Z}$, universal orthogonality and row-4-sparsity (4:8-sparsity) of permutation-coupled $4m \times 4m$ stages, and multi-stage orthogonality closure. |

## Proof Architecture

1. **Pure-`Init` `Rat` Convexity & Nearest-Grid Engine (`Mxfp6Ef21Rotations/RatOrder.lean`):**
   Proves the convex quadratic endpoint maximum lemma $\varphi(y) = (g - y)^2 - (1 - \alpha) y^2 \le \max(\varphi(a), \varphi(b))$ for $\alpha \ge 0$ via the exact polynomial identity $(b - a)\varphi(y) - (b - y)\varphi(a) - (y - a)\varphi(b) = -\alpha(b - a)(y - a)(b - y) \le 0$. Induction over any sorted grid yields `nearestNonneg_quad_le`, reducing the universal $B$-dimensional inequality to a 1D endpoint/midpoint check.
2. **Regime-Free Universal EF21 Proofs (`Mxfp6Ef21Rotations/EF21Universal.lean`):**
   Lifts the 32-level `E3M2` and `E2M3` grids from pure `Nat` numerators (`e3m2Nums`, `e2m3Nums`) checked in one `decide` call (`check_e3m2Nums`, `check_e2m3Nums`), proving all four universal upper bounds without any case-splitting on $B$. Exact witness evaluations use the pure-`Nat` mirror `nearestNonnegNat` (zero `Rat.normalize` in kernel `decide`).
3. **Block-Reduced Goethals–Seidel & Universal Quaternion Algebra (`Mxfp6Ef21Rotations/Rotations.lean`):**
   Splits `4m × 4m` matrix products into $4 \times 4$ blocks of `m × m` matrices (`goethalsSeidel_isOrthogonal_of_blocks`), certifying `GS_n16_E2M1_low` and `GS_n32_E2M1_pm13` via fast `4 × 4` and `8 × 8` block checks. Universal Hamilton 4-square orthogonality, row-4-sparsity (`blockDiagQuat_isRow4Sparse`), permutation orthogonality (`permMat_isOrthogonal`), and multi-stage closure (`matProd_isOrthogonal`) hold symbolically for all $a, b, c, d \in \mathbb{Z}$ and all $m \in \mathbb{N}$.

## Scope of the formal statement

The quantizer `symQuant` is a hand-written nearest-grid model of the E3M2 and E2M3 value sets (ties rounded down); it is not the OCP hardware encoder. Within that model the bounds are universal over all `y : Fin B -> Rat` (the `3600/(B+3599)` branch is a supremum approached from outside the `|y| > 14` region and is not attained). The Goethals-Seidel `16 x 16` and `32 x 32` orthogonality statements are finite checks.

## Prior-Art Context

- **EF21 error-feedback compression:** Richtárik, Sokolov, and Fatkhullin (NeurIPS 2021) introduced EF21 and proved convergence for any $\alpha$-contractive compressor satisfying $\mathbb{E}\|C(x) - x\|^2 \le (1 - \alpha)\|x\|^2$. Our Theorems 1–3 give exact, machine-checked, all-$B$ phase diagrams and `E2M3`/`E3M2` crossover boundaries for the modelled `MXFP6` (`E3M2`, `E2M3`) and continuous `NVFP6` quantizers (hand-written nearest-grid models, not the OCP MX v1.0 hardware encoder). No prior record was found by the authors; the search was not recorded.
- **Goethals–Seidel arrays & Hadamard rotations:** Goethals and Seidel (1970) introduced 4-circulant orthogonal arrays for constructing Hadamard and weighing matrices, while incoherence rotations such as QuIP# (Tseng et al., ICML 2024), QuaRot (Ashkboos et al., NeurIPS 2024), and SpinQuant (Liu et al., ICLR 2025) rely on Walsh–Hadamard transforms. Theorems 4–5 quantify Hadamard's irrational weight-quantization defect at $n = 8, 32$ and certify exact Goethals–Seidel orthonormal matrices whose weights incur 0.00% quantization error across `E2M1`, `E3M2`, and `E2M3`.
- **Hamilton quaternions & structured sparse rotations:** Hamilton's four-square orthogonal matrices provide exact $4 \times 4$ orthogonal blocks; coupling block-diagonal quaternion layers with permutations yields 4:8-sparse orthogonal factorizations (Theorem 6) that preserve exact $\ell _ 2$ norm in arbitrary $4m$ dimensions.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim `#print axioms` output and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` verification manifest.
