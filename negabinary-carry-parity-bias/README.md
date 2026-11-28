# Negabinary vs. Binary Carry-Parity Bias: Exact Spectral Decomposition, the $\pm 1/3$ Classification, and the Asymmetric $(-1/9, +1/3]$ Barrier

> **Hour 7 Discovery — 8-Hour Pure-Silicon GPU Hunt (`alien-silicon-hunt-20261128`, Track C)**
> Zero floating-point ISA instructions on GPU (`gfx1100`); bit-identical CPU verification; 100% machine-checked in pure `Init` Lean 4 (`v4.34.1`) with zero Mathlib dependencies, zero `sorry`, zero `native_decide`, and clean `#print axioms`.

## What This Proves

Choose any fixed integer constant $m \ge 1$ and let $x$ range uniformly over all $2^w$ unsigned $w$-bit integers $\{0, \dots, 2^w - 1\}$. Count the total carries generated when adding $x$ and $m$:
- In **negabinary (base $-2$)**, each bit slice computes $s = x _ i + m _ i + c \in \{-1, 0, 1, 2, 3\}$; $s \ge 2$ emits a positive carry ($c' = -1$), $s < 0$ emits a negative carry ($c' = +1$), and $s \in \{0, 1\}$ emits no carry ($c' = 0$). Let $C _ {-2}(x, m)$ be the total number of positive plus negative carries.
- In **standard binary (base $+2$)**, each bit slice with $s \ge 2$ emits a carry ($c' = +1$). Let $C _ {+2}(x, m)$ be the total number of carries.

Classical intuition might expect the carry-parity sign $(-1)^{C(x, m)}$ to average out near $0$ as $w \to \infty$. Pure-silicon GPU sweeps in Track C (`N = 2^{20}`) instead revealed massive, sharply quantized, exact rational asymptotic biases
```math
\beta_{-2}(m) := \lim_{w \to \infty} \frac{1}{2^w} \sum_{x = 0}^{2^w - 1} (-1)^{C_{-2}(x, m)}, \qquad \beta_{+2}(m) := \lim_{w \to \infty} \frac{1}{2^w} \sum_{x = 0}^{2^w - 1} (-1)^{C_{+2}(x, m)}
```
together with a startling **base-$(+2)$ vs. base-$(-2)$ spectral asymmetry**:

| Property | Negabinary (Base $-2$) | Standard Binary (Base $+2$) |
| :--- | :--- | :--- |
| Exact finite-width sum $3 S _ {L + k}(m, 0)$ | $b _ 0(m) \cdot 2^k + o _ 0(m) \cdot (-1)^k + 3 d _ 0(m)$ | $g _ 0(m) \cdot 2^k + u _ 0(m) \cdot (-1)^k$ |
| Exact asymptotic range ($m \ge 1$) | **Closed symmetric** $\left[-\tfrac{1}{3},\; +\tfrac{1}{3}\right]$ | **Half-open asymmetric** $\left(-\tfrac{1}{9},\; +\tfrac{1}{3}\right]$ |
| All $+1/3$ maximizers ($m \ge 1$) | $m = 2^k$ **only** | $m \in \{2^k,\; 3 \cdot 2^k\}$ **only** |
| Lower extremal boundary | Attained **iff** $m \in \{3 \cdot 2^k,\; 7 \cdot 2^k,\; 13 \cdot 2^k\}$ | **Never attained** ($\beta _ {+2}(m) > -1/9$ strictly); sharp along $m _ r = 3 \cdot 2^{2r + 1} - 1$ with $\beta _ {+2}(m _ r) = -\tfrac{1}{9} + \tfrac{1}{9 \cdot 4^r}$ |
| Zero-bias kernel collapse | $m \in \{5 \cdot 2^r, 9 \cdot 2^r, 15 \cdot 2^r, \dots\}$ collapse to exact period-2 oscillation $\pm 2^r (3 + (-1)^k)$ | $m = 5 \cdot 2^r, 7 \cdot 2^r, \dots$ |

## Headline Theorems (10 Unconditional Lean 4 Theorems)

All 10 theorems are stated in pure integer arithmetic (`Int`/`Nat`) in `Challenge.lean` and proved unconditionally in `Solution.lean`:

1. **`negabinParitySum_step`**: Exact 3-state transfer matrix recurrence ($T _ 0$ for $2q$, $T _ 1$ for $2q + 1$) for $S _ w(m, c)$ across all widths $w$ and addends $q$.
2. **`negabinParitySum_zero`**: Exact zero-addend Jacobsthal law $S _ w(0, 0) = 2^w$, $S _ w(0, +1) = J _ w + 1$, $S _ w(0, -1) = J _ w - 1$, $3 J _ w = 2^w - (-1)^w$, and the constant carry-gap invariant $S _ w(0, +1) - S _ w(0, -1) = 2$.
3. **`negabinParitySum_spectral`**: Universal exact 3-mode spectral decomposition $3 S _ {\mathrm{bitLen}(m) + k}(m, c) = b _ c(m) \cdot 2^k + o _ c(m) \cdot (-1)^k + 3 d _ c(m)$ for all $m, k \in \mathbb{N}$ and $c \in \{0, +1, -1\}$.
4. **`negabinBias_abs_le_one_third`**: Universal $\pm 1/3$ barrier: $|b _ 0(m)| \le 2^{\mathrm{bitLen}(m)}$ for all $m \ge 1$, proved via the strictly invariant cube $[-1/3, 1/3]^3$ for $m \ge 4$.
5. **`negabinBias_eq_pos_one_third_iff`**: Complete classification: $b _ 0(m) = 2^{\mathrm{bitLen}(m)} \iff \exists k,\; m = 2^k$.
6. **`negabinBias_eq_neg_one_third_iff`**: Complete classification: $b _ 0(m) = -2^{\mathrm{bitLen}(m)} \iff \exists k,\; m = 3 \cdot 2^k \lor m = 7 \cdot 2^k \lor m = 13 \cdot 2^k$.
7. **`negabinZeroBias_bounded_family`**: Exact infinite zero-bias families $5 \cdot 2^r$, $9 \cdot 2^r$, and $15 \cdot 2^r$ with $b _ 0(m) = 0$ and exact bounded period-2 oscillation $\pm 2^r (3 + (-1)^k)$ for all $k \ge 0$.
8. **`base2ParitySum_spectral`**: Universal exact 2-mode standard binary spectral decomposition $3 S _ {\mathrm{bitLen}(m) + k}^{+2}(m, c) = g _ c(m) \cdot 2^k + u _ c(m) \cdot (-1)^k$ for all $m, k \in \mathbb{N}$ and $c \in \{0, 1\}$.
9. **`base2Bias_asymmetric_barrier`**: Strict asymmetric barrier $-2^{\mathrm{bitLen}(m)} < 3 g _ 0(m) \le 3 \cdot 2^{\mathrm{bitLen}(m)}$ for all $m \ge 1$ (proved via the strictly invariant 5-inequality polygon $\{g _ 0 > -1/9,\; g _ 0 \le 1/3,\; |g _ 1| \le 1/3,\; g _ 0 - g _ 1 > -2/9,\; g _ 0 + g _ 1 > -4/9\}$), paired with exact sharpness $3 g _ 0(3 \cdot 2^{2r + 1} - 1) = -2^{2r + 3} + 8$.
10. **`base2Bias_eq_pos_one_third_iff`**: Complete classification: $g _ 0(m) = 2^{\mathrm{bitLen}(m)} \iff \exists k,\; m = 2^k \lor m = 3 \cdot 2^k$.

## Verification

```powershell
lake build
lake build Challenge
lake env lean PrintAxioms.lean
```
See `AUDIT.md` for verbatim build and `#print axioms` receipts.
