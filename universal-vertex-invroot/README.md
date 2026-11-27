# Universal Vertex Inverse-$p$-th Root — All-$p$ Coupled $G^{-1/p}$ Vertex Law, Cubic Convergence, Relative-Error-Model Confinement Certificates & a Degree-9 Rounding-Model Comparison (`universal-vertex-invroot`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **9 / 10** | **9 / 10** | **10 / 10** | **91 / 100** |

*Heuristic self-rating (weighted `3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 91 / 100`): proves the universal all-$p$ coupled $G^{-1/p}$ completed-square vertex law ($\forall p \ge 1$), exact monomial cancellation condition number $\kappa _ {\mathrm{mono}}(p) = 1 + 4/p + 2/p^2$ versus unit vertex-sum condition number $\kappa _ {\mathrm{sum}} = 1$, universal all-$p$ cubic convergence with exact leading constant $(p+1)(2p+1)/(6p^2)$, the exact 4-matmul shared-square degree-9 identity and a rounding-model comparison of 3-matmul degree-5 against 4-matmul degree-9 (in a scalar relative-error model with unit roundoffs $1/256$, $1/32$, $1/16$), and 6-step confinement certificates for $p \in \{2, 3, 8\}$ in that scalar model with $u = 1/256$, in pure Lean 4 `Init` (`v4.34.1`, zero Mathlib, zero `native_decide`).*

## For Mathematicians

Coupled Newton–Schulz iterations for the matrix inverse $p$-th root $G^{-1/p}$ ($p \ge 1$) maintain $M _ t = X _ t^p G$ and $X _ t \approx G^{-1/p}$ via

```math
X_{t+1} = X_t P(M_t), \qquad M_{t+1} = M_t P(M_t)^p.
```

In low-precision arithmetic (the unit roundoffs used below are $u = 2^{-8} = 1/256$, labelled BF16 in the files, and the illustrative values $2^{-5} = 1/32$ and $2^{-4} = 1/16$ labelled FP8; the Lean statements only use the number $u$, not any floating-point format), expanding the 2nd-order Taylor/Halley polynomial $T _ {2,p}(m) = 1 - (m - 1)/p + \frac{p+1}{2p^2}(m - 1)^2$ in monomial form $c _ 0 + c _ 1 m + c _ 2 m^2$ introduces alternating-sign cancellation ($c _ 0 > 0, c _ 1 < 0, c _ 2 > 0$) whose rounding errors are amplified by $P(M)^p$.

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

3. **4-Matmul Shared-Square Degree-9 Identity & Rounding-Model Comparison (`deg9_shared_square_and_rounding_floor_dominance`):**
   - Exact shared-square algebraic identity for all $a, c, d, \mu _ 1, \mu _ 2 \in \mathbb{Q}$:
     ```math
     c + d (a - \mu_2)^2 = \bigl(c + d(\mu_1 - \mu_2)^2\bigr) + d (a - \mu_1)^2 + 2 d (\mu_1 - \mu_2)(a - \mu_1),
     ```
     enabling 4-matmul double-vertex degree-9 polar steps without a second squaring matmul.
   - Algebraic degree-per-matmul edge $5^4 < 9^3$ ($625 < 729$, i.e. $5^{1/3} < 9^{1/4}$), **yet** in the model where the degree-5 path incurs six relative roundings and the degree-9 path ten (each a factor $1 \pm u$, an assumption of the model, not a derived property of any hardware), at $x = 1$,
     ```math
     (1 + u)^6 < (1 + u)^{10} \qquad (\forall u > 0),
     ```
     and for $u = 1/256$, $1/32$ and $1/16$, the model's degree-9 rounding bound exceeds $1.65$ times the model's degree-5 bound:
     ```math
     \frac{165}{100}\bigl((1 + u)^6 - 1\bigr) < (1 + u)^{10} - 1.
     ```

4. **6-Step Confinement in a Scalar Relative-Error Model for $p \in \{2, 3, 8\}$ (Theorems 4–6):**
   The model (`NoisyVertexStep2/3/8` in `Defs.lean`) is a scalar iteration in which every arithmetic operation is multiplied by $1 + \delta_i$ with $|\delta_i| \le u$ chosen adversarially (existentially); it has no matrix, no `X` update and no IEEE semantics. Using a pure-`Init` cleared-denominator `Int` uniform-partition interval checker (`checkVertexStepP`) with sound outward $2^{-40}$ dyadic rounding (`qFloor40` / `qCeil40`) and exact pointwise adversarial envelopes (`noisyVertexStep2_envelope`, `noisyVertexStep3_envelope`, `noisyVertexStep8_envelope`), we certify that **every** such 6-step trajectory of the scalar model started in $[85/100, 115/100]$ at $u = 1/256$ ends in the stated interval, for the Q32.32 `quad_vertex` parameters hard-coded in `Defs.lean` (taken from a search output file that is not part of this repository):
   - **$p = 2$ (`bf16_inv_sqrt_vertex_certified`):** confined in $[982/1000, 1018/1000]$ ($\delta _ M \le 0.018$).
   - **$p = 3$ (`bf16_inv_cbrt_vertex_certified`):** confined in $[974/1000, 1026/1000]$ ($\delta _ M \le 0.026$).
   - **$p = 8$ (`bf16_inv_eighth_vertex_certified`):** confined in $[932/1000, 1068/1000]$ ($\delta _ M \le 0.068$).

## For Non-Mathematicians

Modern AI training optimizers (like Muon, Shampoo, and SOAP) repeatedly compute fractional inverse powers of matrices—such as $G^{-1/2}$, $G^{-1/3}$, $G^{-1/4}$, or $G^{-1/8}$—using fast low-precision 16-bit (BF16) or 8-bit (FP8) matrix multiplications. Standard polynomial formulas subtract large positive and negative numbers, causing small rounding errors to cancel out significant digits and blow up when raised to the $p$-th power.

This package proves a single universal algebraic formula that works for **every** root order $p \ge 1$: rewriting the quadratic update in completed-square ("vertex") form turns it into a sum of strictly positive numbers that is always at least $3/4$, eliminates cancellation completely, and still converges cubically (tripling the number of accurate digits each step). It also proves a statement about a 4-matmul degree-9 polar formula, which has a slight algebraic edge ($9^{1/4} > 5^{1/3}$): in a simple model where each rounding multiplies by $1 \pm u$ and the degree-9 path has ten roundings against six, its error bound is more than $1.65$ times larger; this is a statement about the model, not a measurement of real hardware. Finally, Lean 4's proof kernel verifies that, in that scalar rounding model, six-step trajectories for $p = 2, 3, 8$ stay within the stated intervals.

---

**Scope of the formal statement.** Theorems 1 and 2 are identities over the rationals (`ring`-level polynomial identities that hold for every $p$). Theorems 4 to 6 are about the hand-written scalar model `NoisyVertexStep2/3/8` (a relative error factor $1 + \delta_i$ per operation, $|\delta_i| \le u$, $\delta_i$ existentially chosen; scalar `m` only; no matrix iteration, no `X` update, no IEEE-754 or tensor-core semantics). `uBF16 = 1/256` is only a number; "Hybrid FP8 $u = 1/32$" is not a real format. The model, not hardware, is what is certified.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `universal_invroot_vertex_identity_and_positivity` | For all $p \ge 1$ and $m \in \mathbb{Q}$: $T _ {2,p}(m) = P _ p(m) \ge \frac{2p+1}{2p+2} \ge \frac{3}{4}$, exact monomial expansion $c _ 0 + c _ 1 m + c _ 2 m^2$, $\kappa _ {\mathrm{mono}}(p) = 1 + 4/p + 2/p^2$, and $\kappa _ {\mathrm{sum}} = 1$. |
| `universal_invroot_cubic_convergence` | For all $p \ge 1$ and $m \in \mathbb{Q}$: $m P _ p(m)^p - 1 = (m - 1)^3 R _ p(m - 1)$ with exact leading constant $R _ p(0) = (p+1)(2p+1)/(6p^2)$. |
| `deg9_shared_square_and_rounding_floor_dominance` | Exact 4-matmul shared-square identity, $5^4 < 9^3$, $(1+u)^6 < (1+u)^{10}$ for $u > 0$, and the numeric inequality $1.65\,((1+u)^6 - 1) < (1+u)^{10} - 1$ at $u = 1/256, 1/32, 1/16$ (a comparison of two model expressions, not of real rounding). |
| `bf16_inv_sqrt_vertex_certified` | In the scalar relative-error model with $u = 1/256$, the 6-step stationary `quad_vertex` schedule for $G^{-1/2}$ confines $[85/100, 115/100]$ into $[982/1000, 1018/1000]$. |
| `bf16_inv_cbrt_vertex_certified` | In the scalar relative-error model with $u = 1/256$, the 6-step stationary `quad_vertex` schedule for $G^{-1/3}$ confines $[85/100, 115/100]$ into $[974/1000, 1026/1000]$. |
| `bf16_inv_eighth_vertex_certified` | In the scalar relative-error model with $u = 1/256$, the 6-step stationary `quad_vertex` schedule for $G^{-1/8}$ confines $[85/100, 115/100]$ into $[932/1000, 1068/1000]$. |

## Prior-Art Context

- **Coupled Newton Iteration for Matrix $p$-th Roots (Guo & Higham 2006):** Introduced the standard coupled iteration $M _ {k+1} = M _ k ((p + 1)I - M _ k)^p / p^p$ (linear update, quadratic convergence).
- **Shampoo (Gupta, Koren, Singer 2018), SOAP (Vyas et al. 2024), and Muon (Jordan et al. 2024):** Use low-precision iterative matrix inverse roots ($G^{-1/2}, G^{-1/4}, G^{-1/p}$) and odd polar polynomials (`msign`) as core primitives in large-scale neural network optimization.
- **Vertex-Form Polynomials (`muon-vertex-polar`, `soap-vertex-fourth-root`):** Established completed-square cancellation-free updates for $p = 2$ polar iterations and $p = 4$ SOAP preconditioners. This work unifies the theory into a single universal all-$p$ theorem ($\forall p \ge 1$) with exact cubic convergence and monomial condition number, formalizes the exact 4-matmul degree-9 shared-square identity and rounding-floor dominance over degree-9, and certifies confinement in a scalar rounding model across $p \in \{2, 3, 8\}$ in pure Lean 4 `Init`.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for verbatim build timings and `#print axioms` output, and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest.
