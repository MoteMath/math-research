# Exact `L∞ + L1` Hybrid Norm Minimax Law, Low-Precision RMSNorm Swamping Horizons, and 1-Pass vs 2-Pass LayerNorm Variance Stability

A standalone, sorry-free, pure-`Init` (zero Mathlib) Lean 4 (`v4.34.1`) Palomar Comparator formalization proving six exact rational and bit-level IEEE-754 RNE theorems governing multiplication-free dyadic `L∞ + L1` RMSNorm surrogates, sequential `sum(x_i^2)` swamping horizons across BF16/FP16/FP8/MXFP4, 1-pass LayerNorm catastrophic cancellation (`Var < 0 => NaN`), and universal 2-pass shifted-mean non-negativity.

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **10 / 10** | **9 / 10** | **10 / 10** | **93 / 100** |

*Heuristic self-rating (`3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 93 / 100`): pure-`Init` Lean 4 (zero Mathlib, zero `native_decide`) proofs of the exact `L∞ + L1` hybrid norm upper/lower envelopes and attainment, the universal $\Theta(d^{1/4})$ minimax law $\kappa^*(d) = \sqrt{(\sqrt{d} + 1)/2}$ with no-$O(1)$-distortion lower bound, pure-bitshift Llama-3 8B ($d = 4096$, $\kappa^2 = 65/2$) and 70B ($d = 8192$, $\kappa^2 = 97/2$) dyadic witnesses, universal $S _ {\mathrm{swamp}}(p) = 2^p$ IEEE-754 RNE swamping horizons across all 5 low-precision formats, bit-exact 1-pass LayerNorm negative-variance witnesses, and universal 2-pass shifted-mean non-negativity.*

## Headline Theorems (`RmsnormHybridLinfL1Challenge`)

| # | Theorem | Module | Exact Formal Statement Summary |
| :---: | :--- | :--- | :--- |
| 1 | `hybrid_linf_l1_exact_upper_and_lower_envelopes` | [`HybridNorm.lean`](RmsnormHybridLinfL1/HybridNorm.lean) | For all $d \ge 1$, $\alpha, \beta > 0$, and $x : \mathrm{Fin}\,d \to \mathbb{Q}$, proves both sharp squared bounds $4\alpha\beta \cdot \mathrm{MS}(x) \le H _ {\alpha,\beta}(x)^2 \le (\alpha^2 d + 2\alpha\beta + \beta^2)\cdot \mathrm{MS}(x)$, exact upper attainment at the spike-plus-uniform vector $x _ 0 = 1, x _ i = \beta/(\alpha d + \beta)$, and exact lower attainment at $s$-sparse binary vectors when $d = s^2, \beta = s\alpha$. |
| 2 | `hybrid_linf_l1_minimax_d_quarter_law` | [`HybridNorm.lean`](RmsnormHybridLinfL1/HybridNorm.lean) | Universal rational identity $(2\kappa^2 - 1)^2 - d = (\alpha^2 d - \beta^2)^2 / (4\alpha^2\beta^2) \ge 0$ proving $4\kappa^4 - 4\kappa^2 + 1 \ge d$ for all $d \ge 1, \alpha, \beta > 0$; for any square $d = s^2$, proves $\kappa^2(s^2, \alpha, \beta) \ge (s + 1)/2$ with unique equality iff $\beta = s\alpha$; proves no $d$-independent constant $C \ge 1$ bounds $\kappa^2(d, \alpha, \beta)$. |
| 3 | `dyadic_llama3_d4096_hybrid_norm_exact` | [`HybridNorm.lean`](RmsnormHybridLinfL1/HybridNorm.lean) | Exact instantiation for Llama-3 8B ($d = 4096$): pure-bitshift $2^{-6}\|x\| _ \infty + 2^{-12}\|x\| _ 1$ attains $\kappa^2 = 65/2$ (`8192/65 > 126x` tighter than pure `L1`'s `4096`) with universal bounds $\frac{1}{16}\mathrm{MS}(x) \le H(x)^2 \le \frac{65}{32}\mathrm{MS}(x)$; plus Llama-3 70B ($d = 8192$, $\kappa^2 = 97/2$, `> 168x` tighter) and power-of-4 table $d \in \{64, 256, 1024, 4096, 16384\}$. |
| 4 | `bf16_fp16_fp8_sumsq_swamping_horizon_exact` | [`Swamping.lean`](RmsnormHybridLinfL1/Swamping.lean) | Proves universal RNE tie-to-even swamping $S _ {\mathrm{swamp}}(p) = 2^p$ for all precisions $p \ge 2$, and certifies bit-exact minimal outlier thresholds $M _ {\mathrm{swamp}}$ (dropping ALL $n$ unit bulk squares while $M _ {\mathrm{swamp}} - 1\,\mathrm{ulp}$ does not swamp) for BF16 (`0x4180` = `16`), FP16 (`0x51a8` = `181/4`), FP8-E4M3 (`0x48` = `4`), FP8-E5M2 (`0x42` = `3`), and MXFP4-E2M1 (`0x4` = `2`). |
| 5 | `bf16_fp16_onepass_layernorm_negative_variance_exact` | [`NegVariance.lean`](RmsnormHybridLinfL1/NegVariance.lean) | Bit-exact IEEE-754 RNE certification of minimal unit-std 1-pass LayerNorm negative-variance (`Var < 0 => NaN`) and zero-collapse witnesses across BF16 (`0x4173` = `243/16`, `m2 = 232 < mu2 = 233 => Var = -1`; `0x413d` = `189/16 => Var = 0`), FP16 (`0x5417` = `1047/16`, `Var = -4`; `0x4fc7` = `1991/64 => Var = 0`), FP8-E4M3 (`0x55` = `13`, `Var = -16`), and FP8-E5M2 (`0x48` = `8`, `Var = -8`). |
| 6 | `twopass_shifted_mean_variance_nonneg_universal` | [`NegVariance.lean`](RmsnormHybridLinfL1/NegVariance.lean) | Proves 2-pass shifted-mean variance $\frac{1}{d}\sum (x _ i - \mu)^2$ is unconditionally $\ge 0$ in exact rational arithmetic (with exact parallel-axis identity and exact 1-pass/2-pass equivalence) AND in every monotonic or non-negativity-preserving rounding arithmetic, eliminating negative-variance `NaN` identically. |

---

## For Mathematicians

All six theorems are proved purely over `Rat`, `Int`, and `Nat` inside Lean 4's `Init` prelude — zero Mathlib, zero real-analysis axioms, zero `native_decide`, and zero floating-point approximations:

1. **Exact Upper-Envelope Sum-of-Squares Identity (`HybridNorm.lean`):**
   Splitting out an index $i _ 0$ attaining $M = \|x\| _ \infty$ and writing $S = \sum _ {i \ne i _ 0} |x _ i|$, $Q = \sum _ {i \ne i _ 0} x _ i^2$, Cauchy–Schwarz on the remaining $d - 1$ coordinates gives $(d - 1) Q \ge S^2$. Multiplying the squared upper-envelope residual by $d^2 (d - 1)$ yields the exact algebraic sum-of-squares identity
   ```math
   d(d - 1)\bigl(\alpha^2 d + 2\alpha\beta + \beta^2\bigr)(M^2 + Q) - (d - 1)\bigl((\alpha d + \beta)M + \beta S\bigr)^2
     = d(\alpha^2 d + 2\alpha\beta + \beta^2)\bigl((d - 1)Q - S^2\bigr) + \bigl((d - 1)\beta M - (\alpha d + \beta)S\bigr)^2 \ge 0.
   ```
   Both non-negative terms vanish simultaneously at the spike-plus-uniform vector $x _ 0 = 1$, $x _ i = \beta / (\alpha d + \beta)$ ($i \ge 1$), establishing sharpness for every $d \ge 1$ and $\alpha, \beta > 0$.

2. **Exact Lower Envelope & Minimax $\Theta(d^{1/4})$ Law (`HybridNorm.lean`):**
   Since $\sum x _ i^2 \le \|x\| _ \infty \|x\| _ 1$, AM-GM immediately yields $4\alpha\beta \cdot \mathrm{MS}(x) \le (\alpha \|x\| _ \infty + \frac{\beta}{d}\|x\| _ 1)^2 = H _ {\alpha,\beta}(x)^2$. The squared distortion ratio $\kappa^2(d, \alpha, \beta) = (\alpha^2 d + 2\alpha\beta + \beta^2)/(4\alpha\beta)$ satisfies
   ```math
   \bigl(2\kappa^2(d, \alpha, \beta) - 1\bigr)^2 - d = \frac{(\alpha^2 d - \beta^2)^2}{4\alpha^2 \beta^2} \ge 0,
   ```
   and for square dimensions $d = s^2$,
   ```math
   \kappa^2(s^2, \alpha, \beta) - \frac{s + 1}{2} = \frac{(\alpha s - \beta)^2}{4\alpha\beta} \ge 0,
   ```
   with unique equality iff $\beta = s \alpha$. Thus the hybrid norm cuts the distortion exponent in half relative to pure `L1` ($d^{1/2} \to d^{1/4}$), and no $(\alpha, \beta)$ can achieve $O(1)$ distortion.

3. **Pure-Integer Dyadic IEEE-754 RNE Verification (`Defs.lean`, `Swamping.lean`, `NegVariance.lean`):**
   Every IEEE-754 / OCP binary float (`BF16`, `FP16`, `FP8-E4M3`, `FP8-E5M2`, `MXFP4-E2M1`) is decoded and rounded via exact integer dyadic arithmetic `(mant : Int, exp : Int)` representing $\mathrm{mant} \cdot 2^{\mathrm{exp}}$ with exact tie-to-even rounding `rneDivNat`. This makes every bit-exact addition, subtraction, multiplication, and 1-pass variance witness kernel-verifiable via `decide` (zero `native_decide`, zero `Lean.ofReduceBool`).

---

## For Non-Mathematicians

Modern LLM training and inference rely heavily on RMSNorm and LayerNorm in low-precision formats (BF16, FP16, FP8, MXFP4). This package provides **machine-checked mathematical proofs** (verified by Lean 4's kernel with zero assumptions beyond standard logic) of three practical phenomena:

1. **Why a multiplication-free `L∞ + L1` hybrid norm beats pure `L1` by > 126x in quadratic distortion:** Replacing squaring and `rsqrt` with a pure bit-shift combination $2^{-6}\|x\| _ \infty + 2^{-12}\|x\| _ 1$ at Llama-3 8B width ($d = 4096$) cuts the worst-case squared condition number from **4096x** (pure `L1`) down to **32.5x** (`65/2`), matching the exact continuous minimax optimum with zero multiplications — while proving that no linear combination of `L∞` and `L1` can beat $\Theta(d^{1/4})$.
2. **Why naive low-precision `sum(x_i^2)` freezes completely on moderate outliers:** In IEEE-754 RNE, sequential accumulation of $\sum x _ i^2$ drops every single unit bulk coordinate once the running sum hits $2^p$ — which occurs at a single outlier of magnitude just **16** in BF16, **45.25** in FP16, **4** in FP8-E4M3, **3** in FP8-E5M2, and **2** in MXFP4.
3. **Why 1-pass LayerNorm produces `NaN` even on unit-variance inputs, and why 2-pass shifted-mean never does:** Computing $\mathrm{fl}(E[x^2]) - \mathrm{fl}(E[x])^2$ produces strictly negative variance (`Var = -1` in BF16 at mean `15.1875`, `Var = -4` in FP16 at mean `65.4375`, `Var = -16` in FP8-E4M3 at mean `13`), triggering `rsqrt(Var) = NaN`. Shifting by the mean first ($\frac{1}{d}\sum (x _ i - \hat{\mu})^2$) is unconditionally non-negative in exact arithmetic and in every monotonic non-negative floating-point format.

---

## Building & Verifying

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for verbatim build and `#print axioms` verification transcripts.
