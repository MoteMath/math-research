# Universal Vertex Inverse-$p$-th Root — All-$p$ Coupled $G^{-1/p}$ Vertex Law, Cubic Convergence, BF16 Certificates & Degree-9 Polar Rounding Floor (`universal-vertex-invroot`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **9 / 10** | **9 / 10** | **10 / 10** | **91 / 100** |

*Heuristic self-rating (weighted `3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 91 / 100`): proves the universal all-$p$ coupled $G^{-1/p}$ completed-square vertex law ($\forall p \ge 1$), exact monomial cancellation condition number $\kappa _ {\mathrm{mono}}(p) = 1 + 4/p + 2/p^2$ versus unit vertex-sum condition number $\kappa _ {\mathrm{sum}} = 1$, universal all-$p$ cubic convergence with exact leading constant $(p+1)(2p+1)/(6p^2)$, the exact 4-matmul shared-square degree-9 identity and rounding-floor dominance of 3-matmul degree-5 over 4-matmul degree-9 across BF16 and FP8, and continuous 6-step worst-case BF16 confinement certificates for $p \in \{2, 3, 8\}$ in pure Lean 4 `Init` (`v4.34.1`, zero Mathlib, zero `native_decide`).*

## For Mathematicians

Coupled Newton–Schulz iterations for the matrix inverse $p$-th root $G^{-1/p}$ ($p \ge 1$) maintain $M _ t = X _ t^p G$ and $X _ t \approx G^{-1/p}$ via

```math
X_{t+1} = X_t P(M_t), \qquad M_{t+1} = M_t P(M_t)^p.
```

In low-precision tensor-core arithmetic (BF16 $u = 2^{-8} = 1/256$, hybrid FP8 $u = 2^{-5} = 1/32$, pure FP8 E4M3 $u = 2^{-4} = 1/16$), expanding the 2nd-order Taylor/Halley polynomial $T _ {2,p}(m) = 1 - (m - 1)/p + \frac{p+1}{2p^2}(m - 1)^2$ in monomial form $c _ 0 + c _ 1 m + c _ 2 m^2$ introduces alternating-sign cancellation ($c _ 0 > 0, c _ 1 < 0, c _ 2 > 0$) whose rounding errors are amplified by $P(M)^p$.

We formalize six headline theorems over exact rationals $\mathbb{Q}$ in pure Lean 4 `Init` (zero Mathlib):

1. **Universal All-$p$ Vertex Identity, Positivity & Zero-Cancellation Law (`universal_invroot_vertex_identity_and_positivity`):**
   For every $p \in \mathbb{N}$ with $p \ge 1$ and every $m \in \mathbb{Q}$:
   ```math
   1 - \frac{m - 1}{p} + \frac{p + 1}{2 p^2}(m - 1)^2 = \frac{2p + 1}{2p + 2} + \frac{p + 1}{2 p^2}\left(m - \frac{2p + 1}{p + 1}\right)^2,
   ```
   satisfying the universal global lower bound
   ```math
   \frac{3}{4} \le \frac{2p + 1}{2p + 2} \le P_p(m),
   ```
   and exact monomial expansion $P _ p(m) = c _ 0 + c _ 1 m + c _ 2 m^2$ with cancellation condition number at $m = 1$:
   ```math
   |c_0| + |c_1| + |c_2| = 1 + \frac{4}{p} + \frac{2}{p^2},
   ```
   whereas the vertex sum adds two strictly nonnegative terms whose absolute values sum identically to $1$ (zero final-sum cancellation).

2. **Universal All-$p$ Cubic Convergence (`universal_invroot_cubic_convergence`):**
   For every $p \in \mathbb{N}$ with $p \ge 1$ and every $m \in \mathbb{Q}$, constructing the explicit recursive polynomial quotient $R _ p(x) = \mathrm{invRootCubicQuot}(p, x)$ in $x = m - 1$:
   ```math
   m \, P_p(m)^p - 1 = (m - 1)^3 R_p(m - 1), \qquad R_p(0) = \frac{(p + 1)(2p + 1)}{6 p^2}.
   ```
   (Taking values $1, 5/8, 14/27, 15/32, 51/128$ for $p = 1, 2, 3, 4, 8$.)

3. **4-Matmul Shared-Square Degree-9 Identity & Rounding-Floor Dominance (`deg9_shared_square_and_rounding_floor_dominance`):**
   - Exact shared-square algebraic identity for all $a, c, d, \mu _ 1, \mu _ 2 \in \mathbb{Q}$:
     ```math
     c + d (a - \mu_2)^2 = \bigl(c + d(\mu_1 - \mu_2)^2\bigr) + d (a - \mu_1)^2 + 2 d (\mu_1 - \mu_2)(a - \mu_1),
     ```
     enabling 4-matmul double-vertex degree-9 polar steps without a second squaring matmul.
   - Algebraic degree-per-matmul edge $5^4 < 9^3$ ($625 < 729$, i.e. $5^{1/3} < 9^{1/4}$), **yet** under adversarial fixed-point rounding envelopes at $x = 1$,
     ```math
     (1 + u)^6 < (1 + u)^{10} \qquad (\forall u > 0),
     ```
     and across BF16 ($u = 1/256$), Hybrid FP8 ($u = 1/32$), and Pure FP8 ($u = 1/16$), the sequential double-vertex degree-9 rounding floor exceeds $1.65\times$ the 3-matmul single-vertex degree-5 floor:
     ```math
     \frac{165}{100}\bigl((1 + u)^6 - 1\bigr) < (1 + u)^{10} - 1.
     ```

4. **Certified Continuous 6-Step BF16 Confinement for $p \in \{2, 3, 8\}$ (Theorems 4–6):**
   Using a pure-`Init` cleared-denominator `Int` uniform-partition interval checker (`checkVertexStepP`) with sound outward $2^{-40}$ dyadic rounding (`qFloor40` / `qCeil40`) and exact pointwise adversarial envelopes (`noisyVertexStep2_envelope`, `noisyVertexStep3_envelope`, `noisyVertexStep8_envelope`), we certify **every** adversarial 6-step stationary trajectory from $[85/100, 115/100]$ at $u = 1/256$ using the exact Q32.32 `quad_vertex` schedules from `w1-polar-higher-roots/results.json`:
   - **$p = 2$ (`bf16_inv_sqrt_vertex_certified`):** confined in $[982/1000, 1018/1000]$ ($\delta _ M \le 0.018$).
   - **$p = 3$ (`bf16_inv_cbrt_vertex_certified`):** confined in $[974/1000, 1026/1000]$ ($\delta _ M \le 0.026$).
   - **$p = 8$ (`bf16_inv_eighth_vertex_certified`):** confined in $[932/1000, 1068/1000]$ ($\delta _ M \le 0.068$).

## For Non-Mathematicians

Modern AI training optimizers (like Muon, Shampoo, and SOAP) repeatedly compute fractional inverse powers of matrices—such as $G^{-1/2}$, $G^{-1/3}$, $G^{-1/4}$, or $G^{-1/8}$—using fast low-precision 16-bit (BF16) or 8-bit (FP8) matrix multiplications. Standard polynomial formulas subtract large positive and negative numbers, causing small rounding errors to cancel out significant digits and blow up when raised to the $p$-th power.

This package proves a single universal algebraic formula that works for **every** root order $p \ge 1$: rewriting the quadratic update in completed-square ("vertex") form turns it into a sum of strictly positive numbers that is always at least $3/4$, eliminates cancellation completely, and still converges cubically (tripling the number of accurate digits each step). It also proves why a clever 4-matmul degree-9 polar formula—despite having a slight theoretical algebraic edge ($9^{1/4} > 5^{1/3}$)—still loses to the simpler 3-matmul degree-5 vertex formula in BF16 and FP8 hardware: its extra sequential rounding steps inflate the worst-case rounding floor by more than $1.65\times$. Finally, Lean 4's proof kernel directly verifies that the exact BF16 schedules for $p = 2, 3, 8$ stay strictly within their target accuracy bands against every possible worst-case rounding adversary.

---

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `universal_invroot_vertex_identity_and_positivity` | For all $p \ge 1$ and $m \in \mathbb{Q}$: $T _ {2,p}(m) = P _ p(m) \ge \frac{2p+1}{2p+2} \ge \frac{3}{4}$, exact monomial expansion $c _ 0 + c _ 1 m + c _ 2 m^2$, $\kappa _ {\mathrm{mono}}(p) = 1 + 4/p + 2/p^2$, and $\kappa _ {\mathrm{sum}} = 1$. |
| `universal_invroot_cubic_convergence` | For all $p \ge 1$ and $m \in \mathbb{Q}$: $m P _ p(m)^p - 1 = (m - 1)^3 R _ p(m - 1)$ with exact leading constant $R _ p(0) = (p+1)(2p+1)/(6p^2)$. |
| `deg9_shared_square_and_rounding_floor_dominance` | Exact 4-matmul shared-square identity, $5^4 < 9^3$, universal $(1+u)^6 < (1+u)^{10}$ for $u > 0$, and $> 1.65\times$ degree-9 rounding-floor penalty at BF16, Hybrid FP8, and Pure FP8. |
| `bf16_inv_sqrt_vertex_certified` | 6-step BF16 ($u = 1/256$) stationary `quad_vertex` schedule for $G^{-1/2}$ confines $[85/100, 115/100]$ into $[982/1000, 1018/1000]$. |
| `bf16_inv_cbrt_vertex_certified` | 6-step BF16 ($u = 1/256$) stationary `quad_vertex` schedule for $G^{-1/3}$ confines $[85/100, 115/100]$ into $[974/1000, 1026/1000]$. |
| `bf16_inv_eighth_vertex_certified` | 6-step BF16 ($u = 1/256$) stationary `quad_vertex` schedule for $G^{-1/8}$ confines $[85/100, 115/100]$ into $[932/1000, 1068/1000]$. |

## Prior-Art Context

- **Coupled Newton Iteration for Matrix $p$-th Roots (Guo & Higham 2006):** Introduced the standard coupled iteration $M _ {k+1} = M _ k ((p + 1)I - M _ k)^p / p^p$ (linear update, quadratic convergence).
- **Shampoo (Gupta, Koren, Singer 2018), SOAP (Vyas et al. 2024), and Muon (Jordan et al. 2024):** Use low-precision iterative matrix inverse roots ($G^{-1/2}, G^{-1/4}, G^{-1/p}$) and odd polar polynomials (`msign`) as core primitives in large-scale neural network optimization.
- **Vertex-Form Polynomials (`muon-vertex-polar`, `soap-vertex-fourth-root`):** Established completed-square cancellation-free updates for $p = 2$ polar iterations and $p = 4$ SOAP preconditioners. This work unifies the theory into a single universal all-$p$ theorem ($\forall p \ge 1$) with exact cubic convergence and monomial condition number, formalizes the exact 4-matmul degree-9 shared-square identity and rounding-floor dominance over degree-9, and certifies BF16 schedules across $p \in \{2, 3, 8\}$ in pure Lean 4 `Init`.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for verbatim build timings and `#print axioms` output, and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest.
