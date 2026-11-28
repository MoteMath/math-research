# Pure-Silicon Non-Idempotent Framed-Link Racks and Single-Bit Conjugated Knot Quandles (`silicon-framed-racks-and-bitquandles`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **89 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): Zero-dependency pure Lean 4 `Init` formalization (zero Mathlib, zero `sorry`, zero `native_decide`, Palomar Comparator + `nanoda` ready) proving universal algebraic laws for three non-classical, non-Alexander pure-silicon framed-link rack and knot quandle families over `BitVec w` discovered by GPU algebraic-law mining on $\mathbb{Z} / 2^w \mathbb{Z}$.*

---

## For Mathematicians

In low-dimensional topology, **racks** (left-bijective, left-self-distributive magmas) classify framed links (Reidemeister moves II & III without move I), while **quandles** (idempotent racks) classify unframed knots and links. Classical finite examples over $\mathbb{Z} / 2^w \mathbb{Z}$ are almost exclusively **Alexander** (affine: $x \star y = a x + b y + d \bmod 2^w$). Combining modular addition with bitwise XOR yields three genuinely non-Alexander infinite families across all bit-widths $w$:

1. **Universal Coset-Shift Framed-Link Racks & Single-Bit Carry-XOR Realization (`cosetRack_laws`, `carryXorRack_eq`, `carryXorRack_framed_laws`):**
   - For any $g : \mathrm{BitVec}\,w \to \mathrm{BitVec}\,w$ invariant under $d \mapsto d \pm g(a)$, $x \star _ g y = y + g(y - x)$ is a left-bijective, left-self-distributive rack with framing twist $x \star _ g x = x + g(0)$ (idempotent iff $g(0) = 0$).
   - The GPU-discovered carry-XOR magma $x \star _ k y = x + ((y - x) \oplus 2^k) + 2^k$ reduces identically for all $k < w$ to
     ```math
     x \star_k y = y + \begin{cases} 0 & \text{if } \mathrm{bit}_k(y - x) = 1, \\ 2^{k+1} & \text{if } \mathrm{bit}_k(y - x) = 0, \end{cases}
     ```
     yielding a **strictly one-sided, non-idempotent framed-link rack** for every $w \ge 2$ and $k + 1 < w$.

2. **Involutive Non-Idempotent Zero-Borrow Core-XOR Framed-Link Racks (`coreXorRack_eq`, `coreXorRack_involutive_framed_laws`, `coreXorRack_nonAlexander`):**
   - For $m _ k = 2^k - 1$ (`lowMask w k`), the GPU-discovered magma $x \diamond _ k y = (x \oplus m _ k) + (x - y)$ cancels the lower $k$ bits of $x$ identically:
     ```math
     x \diamond_k y = 2\,(x \mathbin{\&} \lnot m_k) + m_k - y.
     ```
   - Because $m _ k - (y \mathbin{\&} m _ k) \in [0, 2^k - 1]$ creates **zero borrow** across bit $k$, $(x \diamond _ k y) \mathbin{\&} \lnot m _ k = 2(x \mathbin{\&} \lnot m _ k) - (y \mathbin{\&} \lnot m _ k)$, making $\diamond _ k$ an **involutive ($x \diamond _ k (x \diamond _ k y) = y$), left-self-distributive, non-idempotent ($0 \diamond _ k 0 = 2^k - 1 \ne 0$), non-Alexander framed-link rack** for all $1 \le k < w$.

3. **Single-Bit Conjugated Both-Sided Knot Quandles (`conjBitQuandle_eq`, `conjBitQuandle_bothSided_laws`, `conjBitQuandle_nonInvolutive_nonAlexander`):**
   - Conjugating modular translation by a single-bit XOR produces $x \triangleright _ k y = ((x \oplus 2^k) + (y - x)) \oplus 2^k$, which reduces identically for all $k < w$ to:
     ```math
     x \triangleright_k y = \begin{cases}
       y & \text{if } \mathrm{bit}_k(x) = \mathrm{bit}_k(y), \\
       y - 2^{k+1} & \text{if } \mathrm{bit}_k(x) = 1,\; \mathrm{bit}_k(y) = 0, \\
       y + 2^{k+1} & \text{if } \mathrm{bit}_k(x) = 0,\; \mathrm{bit}_k(y) = 1.
     \end{cases}
     ```
   - For every $w \ge 3$ and $k + 1 < w$, $\triangleright _ k$ is a **both-sided (LSD + RSD) knot quandle** that is **non-involutive** (for all $k + 2 < w$ and at $w = 3, k = 0$) and **non-Alexander**.

---

## For Non-Mathematicians

Knot theorists distinguish tangled loops using algebraic systems called **quandles** (for ordinary knots) and **racks** (for framed ribbons that remember twists). On $w$-bit computer integers, almost all known textbook examples are simple linear formulas $a x + b y + d \bmod 2^w$. By searching over millions of CPU-native combinations of addition and bitwise XOR on a GPU, we uncovered three completely non-linear infinite families — two twisted ribbon racks (one strictly one-sided, one self-inverting via zero-borrow bit cancellation) and one two-sided knot quandle — and proved their algebraic laws unconditionally for every bit-width $w$ in Lean 4's kernel with zero external dependencies.

---

## Headline Theorems

The trusted theorem statements live in [`Challenge.lean`](Challenge.lean) (definitions in [`Defs.lean`](Defs.lean)) and are proved unconditionally in [`Solution.lean`](Solution.lean) (namespace `SiliconRacksQuandles`).

| Theorem | Summary |
| :--- | :--- |
| `cosetRack_laws` | Universal coset-shift framed-link rack theorem for `y + g (y - x)`. |
| `carryXorRack_eq` | Exact reduction of `x + ((y - x) ^^^ 2^k) + 2^k` to a bit-`k`-gated `+2^(k+1)` shift. |
| `carryXorRack_framed_laws` | Left-bijectivity, LSD, non-idempotence, and non-RSD for all `k + 1 < w`. |
| `coreXorRack_eq` | Exact lower-`k`-bit cancellation `(x ^^^ (2^k-1)) + (x - y) = 2*(x &&& ~~~mask) + mask - y`. |
| `coreXorRack_involutive_framed_laws` | Involutivity, LSD, and non-idempotence of `coreXorRack k` for all `1 ≤ k < w`. |
| `coreXorRack_nonAlexander` | `coreXorRack 1` on `BitVec 4` is not an Alexander (affine) rack. |
| `conjBitQuandle_eq` | Exact 3-branch carry/borrow reduction of `((x ^^^ 2^k) + (y - x)) ^^^ 2^k`. |
| `conjBitQuandle_bothSided_laws` | Idempotence, left-bijectivity, LSD, and RSD for all `k + 1 < w`. |
| `conjBitQuandle_nonInvolutive_nonAlexander` | Non-involutivity for all `k + 2 < w` plus non-Alexander witness at `w = 3, k = 0`. |

---

## Build & Verification

Built against `leanprover/lean4:v4.34.1` using pure `Init` only (zero Mathlib, zero external packages):

```bash
lake build
lake build Challenge
lake env lean PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for verbatim build and `#print axioms` receipts, and [`comparator.json`](comparator.json) for the Palomar Comparator + `nanoda` verification manifest.
