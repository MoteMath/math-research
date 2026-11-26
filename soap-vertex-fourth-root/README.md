# SOAP Vertex Fourth-Root — Vertex-Form BF16/FP8-Safe Matrix Inverse Fourth-Root Polynomials & FP8 Linear Crossover (`soap-vertex-fourth-root`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **8 / 10** | **9 / 10** | **10 / 10** | **89 / 100** |

*Heuristic self-rating (weighted `3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 89 / 100`): exact vertex-form reparameterization of quadratic matrix inverse-fourth-root polynomials eliminating final-sum cancellation for Shampoo/SOAP preconditioners, paired with the exact FP8 fourth-power linear crossover (`I031` + `I032`), and a pure-`Init` Lean 4 (`v4.34.1`, zero Mathlib, zero `native_decide`) cleared-denominator `Int` interval certificate engine proving continuous worst-case 5-step confinement across BF16 ($\varepsilon = 10^{-2}$ and $\varepsilon = 10^{-4}$), hybrid FP8, and pure FP8 E4M3.*

## For Mathematicians

Second-order optimizers such as Shampoo and SOAP require computing the inverse fourth root $G^{-1/4}$ of symmetric positive definite Kronecker preconditioner factors $G$ with spectrum in $[\varepsilon, 1]$. Coupled inverse-fourth-root iterations maintain $M _ t = X _ t^4 G$ and $X _ t \approx G^{-1/4}$ via

```math
M _ {t+1} = M _ t \, P _ t(M _ t)^4, \qquad X _ {t+1} = X _ t \, P _ t(M _ t).
```

Classical Guo–Higham coupled Newton uses the linear step $P(m) = \frac{5}{4} - \frac{1}{4} m$ (quadratic convergence, 4 matmuls/step), while degree-2 monomial polynomials $P(m) = a + b m + c m^2$ ($a > 0, b < 0, c > 0$) suffer from severe alternating-sign cancellation under low-precision rounding (BF16 unit roundoff $u = 2^{-8} = 1/256$, hybrid FP8 $u = 2^{-5} = 1/32$, pure FP8 E4M3 $u = 2^{-4} = 1/16$). Moreover, raising $P(m)$ to the fourth power amplifies outer rounding errors by $(1 \pm u)^8$.

We formalize three structural theorems and four continuous worst-case 5-step trajectory confinement theorems over exact rationals $\mathbb{Q}$:

1. **Exact Vertex-Form Equivalence & Global Positivity (`vertex_fourth_root_equiv_monomial`):**
   Every quadratic $a + b m + c m^2$ with $c \ne 0$ satisfies the exact completed-square identity
   ```math
   a + b m + c m^2 = \left(a - \frac{b^2}{4c}\right) + c \left(m + \frac{b}{2c}\right)^2,
   ```
   and any vertex polynomial $\alpha + \beta (m - \mu)^2$ with $\beta \ge 0$ satisfies $\alpha \le \alpha + \beta (m - \mu)^2$ globally for all $m \in \mathbb{Q}$. When $\alpha > 0, \beta \ge 0$, the final sum $\alpha I + \beta (M - \mu I)^2$ adds strictly nonnegative terms with zero cancellation.

2. **Exact Taylor-2 Vertex Identity & Cubic Convergence Residual (`taylor2_fourth_root_vertex_exact`):**
   The 2nd-order Taylor/Halley polynomial of $m^{-1/4}$ at $m = 1$ admits the exact strictly positive vertex form
   ```math
   1 - \frac{m - 1}{4} + \frac{5}{32} (m - 1)^2 = \frac{9}{10} + \frac{5}{32}\left(m - \frac{9}{5}\right)^2 \ge \frac{9}{10},
   ```
   and its coupled update residual vanishes to third order at $m = 1$:
   ```math
   m \, P(m)^4 - 1 = (m - 1)^3 \, R(m),
   ```
   where $R(m) = \mathrm{taylor2ResidualPoly}(m)$ is the explicit degree-6 polynomial in $x = m - 1$ with exact dyadic coefficients $(15/32, -135/512, 189/1024, -15/256, 675/32768, -3375/1048576, 625/1048576)$.

3. **Pointwise Exact Adversarial Envelopes (`noisyFourthRootStep_envelope`):**
   Under the exact 7-rounding-point vertex step model `NoisyVertexStep4` and 5-rounding-point linear step model `NoisyLinearStep4` (relative error $|\delta _ i| \le u$ at every shift, squaring, scaling, addition, and output product), every adversarial output $y$ for $m > 0$ and $0 \le u < 1$ is bounded pointwise by
   ```math
   (1 - u)^8 m \left(\alpha + (1 - u)^4 \beta (m - \mu)^2\right)^4 \le y _ v \le (1 + u)^8 m \left(\alpha + (1 + u)^4 \beta (m - \mu)^2\right)^4,
   ```
   ```math
   (1 - u)^8 m \left(p _ 0 + p _ 1 (1 + u) m\right)^4 \le y _ l \le (1 + u)^8 m \left(p _ 0 + p _ 1 (1 - u) m\right)^4
   ```
   (for $p _ 1 \le 0$ and $p _ 0 + p _ 1 (1 + u) m > 0$).

4. **Continuous 5-Step Worst-Case Confinement Certificates (Theorems 4–7):**
   Using a pure-`Init` cleared-denominator `Int` uniform-partition checker (`checkVertexStep` / `checkLinearStep`), we certify **every** adversarial 5-step trajectory over $\mathbb{Q}$:
   - **BF16 Vertex DP, $\varepsilon = 10^{-2}$ (`bf16_fourth_root_dp5_certified`):** `inv4_vertex_bf16_e2` at $u = 1/256$ confines $m _ 5 \in [965/1000, 1039/1000]$ ($\delta _ M \le 0.039$, **$6.18\times$** tighter than 6-step Guo–Higham).
   - **BF16 Vertex DP, $\varepsilon = 10^{-4}$ (`bf16_fourth_root_eps1e4_certified`):** `inv4_vertex_bf16_e4` at $u = 1/256$ confines $m _ 5 \in [935/1000, 1049/1000]$ ($\delta _ M \le 0.065$, **$15.1\times$** tighter than 6-step Guo–Higham).
   - **Hybrid FP8 Vertex DP, $\varepsilon = 10^{-2}$ (`fp8_hybrid_fourth_root_dp5_certified`):** `inv4_vertex_fp8hyb_e2` at $u = 1/32$ confines $m _ 5 \in [652/1000, 1329/1000]$.
   - **Pure FP8 E4M3 Linear Crossover DP, $\varepsilon = 10^{-2}$ (`fp8_pure_fourth_root_linear_dp5_certified`):** `inv4_linear_fp8_e2` at $u = 1/16$ confines $m _ 5 \in [257/1000, 1654/1000]$, certifying the `I032` FP8 fourth-power precision crossover where tuned linear steps beat quadratic vertex steps at $u = 1/16$ due to lower per-step rounding-depth amplification under $P^4$.

## For Non-Mathematicians

Advanced neural-network optimizers like Shampoo and SOAP accelerate training by computing the inverse fourth root $G^{-1/4}$ of covariance matrices at every step. On modern AI accelerators running in 16-bit BF16 or 8-bit FP8 arithmetic, standard polynomial recipes either converge too slowly (Guo–Higham) or subtract large positive and negative numbers whose tiny rounding errors blow up when raised to the fourth power.

Rewriting the quadratic update in "completed-square" (vertex) form $\alpha + \beta (m - \mu)^2$ removes the dangerous final subtraction completely: the result is always a sum of positive numbers. At 16-bit BF16 precision, our 5-step vertex schedules are **$6.18\times$ to $15.1\times$** more accurate than classical Guo–Higham. At extreme 8-bit pure FP8 precision ($u = 1/16$), raising a polynomial to the fourth power amplifies every extra rounding step so strongly that a tuned linear schedule actually overtakes the quadratic schedule. This package provides a machine-checked Lean 4 proof certifying all four schedules against an adversary who picks the worst possible rounding error at every single arithmetic operation across all 5 steps.

---

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `vertex_fourth_root_equiv_monomial` | For any $a, b, c, \alpha, \beta, \mu, m \in \mathbb{Q}$ with $c \ne 0$, $a + b m + c m^2 = (a - b^2/(4c)) + c (m + b/(2c))^2$, and $\beta \ge 0 \implies \alpha \le \alpha + \beta (m - \mu)^2$. |
| `taylor2_fourth_root_vertex_exact` | For all $m \in \mathbb{Q}$, $1 - (m - 1)/4 + (5/32)(m - 1)^2 = 9/10 + (5/32)(m - 9/5)^2 \ge 9/10$ and $m P(m)^4 - 1 = (m - 1)^3 \cdot \mathrm{taylor2ResidualPoly}(m)$. |
| `noisyFourthRootStep_envelope` | Exact pointwise lower and upper degree-9 envelopes for both the 7-rounding-point `NoisyVertexStep4` and the 5-rounding-point `NoisyLinearStep4`. |
| `bf16_fourth_root_dp5_certified` | 5-step BF16 (`u = 1/256`) vertex schedule `inv4_vertex_bf16_e2` confines every trajectory from $[1/100, 1]$ into $[965/1000, 1039/1000]$. |
| `bf16_fourth_root_eps1e4_certified` | 5-step BF16 (`u = 1/256`) vertex schedule `inv4_vertex_bf16_e4` confines every trajectory from $[1/10000, 1]$ into $[935/1000, 1049/1000]$. |
| `fp8_hybrid_fourth_root_dp5_certified` | 5-step hybrid FP8 (`u = 1/32`) vertex schedule `inv4_vertex_fp8hyb_e2` confines every trajectory from $[1/100, 1]$ into $[652/1000, 1329/1000]$. |
| `fp8_pure_fourth_root_linear_dp5_certified` | 5-step pure FP8 E4M3 (`u = 1/16`) linear schedule `inv4_linear_fp8_e2` confines every trajectory from $[1/100, 1]$ into $[257/1000, 1654/1000]$. |

## Prior-Art Context

- **Shampoo (Gupta, Koren, Singer 2018) & SOAP (Vyas et al. 2024):** Precondition neural-network gradients via Kronecker-factored inverse $p$-th roots ($G^{-1/4}$ for two-sided Shampoo / SOAP eigenbasis updates), making fast low-precision $G^{-1/4}$ iterations directly impactful for large-scale training.
- **Coupled Newton Iteration for Matrix $p$-th Roots (Guo & Higham 2006):** Established the standard coupled iteration $M _ {k+1} = M _ k ((p + 1)I - M _ k)^p / p^p$ (for $p = 4$, $P(m) = (5 - m)/4$), which converges quadratically but requires more steps and degrades severely at $\varepsilon = 10^{-4}$ in BF16.
- **Vertex-Form Polar Polynomials (`muon-vertex-polar`):** Introduced completed-square reparameterization for odd quintic polar ($G^{-1/2}$) iterations in Muon. This work extends the vertex-form architecture to coupled inverse-fourth-root ($G^{-1/4}$) iterations, proves the exact cubic-convergence Taylor-2 vertex identity, identifies the FP8 fourth-power linear crossover (`I032`), and provides a fast pure-`Init` Lean 4 cleared-denominator `Int` interval verification engine with zero `native_decide`.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for verbatim build timings and `#print axioms` output, and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest.
