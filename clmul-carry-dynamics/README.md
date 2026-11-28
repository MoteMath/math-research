# Carryless–Carried Hybrid Hull–Dobell Dynamics, Rotation Kaprekar Sinks, and Exact `m = 3` Twin Laws (`clmul-carry-dynamics`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **89 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): Zero-dependency pure Lean 4 `Init` formalization (zero Mathlib, zero `sorry`, zero `native_decide`, Palomar Comparator + `nanoda` ready) proving three universal pure-silicon binary dynamical and carry-twin laws discovered by GPU scanning on $\mathbb{Z} / 2^w \mathbb{Z}$.*

---

## For Mathematicians

Classical arithmetic treats carry-less multiplication $\mathrm{clmul}(a, x)$ (polynomial multiplication over $\mathbb{F} _ 2[X]$) and ordinary carried addition $+$ (modular arithmetic over $\mathbb{Z} / 2^w \mathbb{Z}$) as incompatible rings. Mixing them produces non-classical pure-silicon dynamical systems that nevertheless obey sharp, universal algebraic laws across all bit-widths $w$:

1. **Carryless–Carried Hybrid Hull–Dobell Theorem (`hybrid_hull_dobell_iff`):**
   Consider the hybrid affine map on $\mathbb{Z} / 2^w \mathbb{Z}$ ($w \ge 2$):
   ```math
   f_{a,b,w}(x) = (\mathrm{clmul}(a, x) + b) \bmod 2^w.
   ```
   For every bit-width $w \ge 2$ and every $a, b \in \mathbb{N}$, $f _ {a,b,w}$ forms a single full cycle of length $2^w$ on $\{0, \dots, 2^w - 1\}$ if and only if
   ```math
   a \equiv 1 \pmod 4 \quad \land \quad b \equiv 1 \pmod 2.
   ```
   The proof lifts from $w = 2$ by an exact 2-adic top-bit cocycle argument: odd $a$ makes $x \mapsto \mathrm{clmul}(a, x) \bmod 2^w$ bijective, pairing $x = 2k$ with $2k + 1$ annihilates the linear XOR-sum of bit $w$ of $\mathrm{clmul}(a, x)$ for all $w \ge 2$, and the carried overflow count across the bijection is exactly $b \bmod 2^w \equiv 1 \pmod 2$, forcing $f _ {a,b,w+1}^{[2^w]}(0) = 2^w$.

2. **Exact $w$-Step Carry-Vector Rotation Kaprekar Sink (`kaprekarStep_add_one_eq`, `kaprekarStep_image_char`, `kaprekarStep_universal_sink`, `kaprekarStep_w2_sharpness`):**
   Consider the bitwise carry-vector + rotation map on `BitVec w`:
   ```math
   g_w(x) = \bigl(((x + 1) \oplus x \oplus 1) + \mathrm{rotl}_w(x, 1) + 1\bigr) \bmod 2^w.
   ```
   - **Exact 1-line algebraic reduction (all $w \ge 1$):**
     ```math
     g_w(x) + 1 = \bigl((x \mid (x + 1)) \ll 1\bigr) \mid \mathrm{msb}(x).
     ```
   - **Exact step-$t$ image characterization (all $w \ge 3$, $1 \le t \le w - 1$):**
     $y \in \mathrm{Im}(g _ w^{[t]})$ if and only if bits $1, \dots, t$ of $y + 1$ are all $1$ (so $|\mathrm{Im}(g _ w^{[t]})| = 2^{w - t}$).
   - **Universal collapse & sharp diameter (all $w \ge 3$):**
     Every $x \in \mathrm{BitVec}\,w$ collapses to the unique fixed point $\lnot 1\#w = 2^w - 2$ in at most $w$ steps, while $g _ w^{[w - 1]}(0\#w) \ne \lnot 1\#w$.
   - **Sharpness at $w = 2$:** At width $w = 2$, $g _ 2$ has two distinct fixed points $1\#2$ and $2\#2$, proving the $w \ge 3$ threshold is exact.

3. **Exact $m = 3$ Carried-vs-Carryless Twin Laws (`carried_eq_clmul3_iff`, `zeroCarry3Count_eq_fib`, `carried_clmul3_parity_sum`):**
   Comparing carried multiplication $3x = x + 2x$ against carry-less multiplication $\mathrm{clmul}(3, x) = x \oplus 2x$ over $0 \le x < 2^w$:
   - **Zero-Carry Fibonacci Law (all $w \in \mathbb{N}$):**
     $3x = \mathrm{clmul}(3, x) \iff x \mathbin{\&} 2x = 0$, and $\#\{x < 2^w : 3x = \mathrm{clmul}(3, x)\} = F _ {w+2}$.
   - **Exact $3^{\lfloor w/2 \rfloor}$ Parity Correlation Law (all $w \ge 1$):**
     ```math
     \sum_{x = 0}^{2^w - 1} (-1)^{\mathrm{popcount}(3x) + \mathrm{popcount}(\mathrm{clmul}(3, x))} =
     \begin{cases}
       4 \cdot 3^{w/2 - 1} & \text{if } w \text{ is even } (w \ge 2), \\
       2 \cdot 3^{(w - 1)/2} & \text{if } w \text{ is odd } (w \ge 1).
     \end{cases}
     ```
     Proved via an exact closed 3-state LSB transducer recurrence $(s _ 0, s _ 1, s _ 2)(w + 1) = (s _ 0 + s _ 1,\; s _ 0 + s _ 2,\; s _ 1 - s _ 2)(w)$.

---

## For Non-Mathematicians

Modern processors have two fundamentally different ways to multiply binary numbers: standard arithmetic with carries, and carry-less polynomial multiplication (`CLMUL`) used in cryptography and error-correcting codes. Normally these two worlds are kept strictly separate. Here we prove three exact laws that emerge when they collide across every bit-width $w$:

1. Replacing standard multiplication with carry-less multiplication inside a linear congruential generator $x \mapsto (\mathrm{clmul}(a, x) + b) \bmod 2^w$ still obeys the exact classical Hull–Dobell full-cycle condition ($a \equiv 1 \bmod 4$, $b$ odd) for every width $w \ge 2$.
2. A non-linear carry-and-bit-rotation map shrinks its state space by an exact factor of $2$ on every step, collapsing all $2^w$ bitstrings to the single number $2^w - 2$ in exactly $w$ steps for every width $w \ge 3$ (and failing sharply at $w = 2$).
3. Comparing carried $3x$ against carry-less $3 \otimes x$ across all $w$-bit integers produces exact Fibonacci counts $F _ {w+2}$ for carry-free agreements and an exact power-of-3 parity correlation law $4 \cdot 3^{w/2 - 1}$ / $2 \cdot 3^{(w-1)/2}$.

---

## Headline Theorems

The trusted theorem statements live in [`Challenge.lean`](Challenge.lean) (with definitions in [`Defs.lean`](Defs.lean)) and are proved unconditionally in [`Solution.lean`](Solution.lean) (namespace `ClmulCarryDynamics`).

| Theorem | Summary |
| :--- | :--- |
| `clmul_xor` | $\mathrm{clmul}(a, x \oplus y) = \mathrm{clmul}(a, x) \oplus \mathrm{clmul}(a, y)$. |
| `clmul_mod_injective_of_odd` | For odd $a$, $x \mapsto \mathrm{clmul}(a, x) \bmod 2^w$ is injective on $\{0, \dots, 2^w - 1\}$. |
| `hybrid_hull_dobell_iff` | For all $w \ge 2$, $x \mapsto (\mathrm{clmul}(a, x) + b) \bmod 2^w$ is a full $2^w$-cycle iff $a \equiv 1 \pmod 4$ and $b \equiv 1 \pmod 2$. |
| `kaprekarStep_add_one_eq` | For all $w \ge 1$, $g _ w(x) + 1 = ((x \mid (x + 1)) \ll 1) \mid \mathrm{msb}(x)$. |
| `kaprekarStep_image_char` | For all $w \ge 3$ and $1 \le t \le w - 1$, $y \in \mathrm{Im}(g _ w^{[t]})$ iff bits $1 \dots t$ of $y + 1$ are all $1$. |
| `kaprekarStep_universal_sink` | For all $w \ge 3$, $g _ w^{[w]}(x) = \lnot 1\#w$ for all $x$, $g _ w^{[w - 1]}(0\#w) \ne \lnot 1\#w$, and $g _ w(\lnot 1\#w) = \lnot 1\#w$. |
| `kaprekarStep_w2_sharpness` | At $w = 2$, $1\#2$ and $2\#2$ are distinct fixed points of $g _ 2$. |
| `carried_eq_clmul3_iff` | $3x = \mathrm{clmul}(3, x) \iff (x \mathbin{\&} 2x) = 0$. |
| `zeroCarry3Count_eq_fib` | For all $w \in \mathbb{N}$, $\#\{x < 2^w : 3x = \mathrm{clmul}(3, x)\} = F _ {w+2}$. |
| `carried_clmul3_parity_sum` | For all $w \ge 1$, $\sum _ {x < 2^w} (-1)^{\mathrm{popcount}(3x) + \mathrm{popcount}(\mathrm{clmul}(3, x))}$ equals $4 \cdot 3^{w/2 - 1}$ (even $w$) or $2 \cdot 3^{\lfloor w/2 \rfloor}$ (odd $w$). |

---

## Build & Verification

Built against `leanprover/lean4:v4.34.1` using pure `Init` only (no Mathlib, no external dependencies):

```bash
lake build
lake build Challenge
lake env lean PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for verbatim build and `#print axioms` receipts, and [`comparator.json`](comparator.json) for the Palomar Comparator + `nanoda` verification manifest.
