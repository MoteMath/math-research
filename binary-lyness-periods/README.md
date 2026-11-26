# Binary Lyness & XOR-Feistel Carry-Renormalization Periods (`binary-lyness-periods`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **10 / 10** | **9 / 10** | **7 / 10** | **10 / 10** | **89 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): unrecorded universal period-6 and period-12 Feistel carry-renormalization laws over unbounded $\mathbb{N} \times \mathbb{N}$ (for completely arbitrary odd-input round functions $h, g : \mathbb{N} \to \mathbb{N}$), together with an exact power-of-two `iff` dichotomy for the binary Lyness map $F _ c(x, y) = (y, x \oplus (y + c))$ and its bitwise-OR period-12 twin, formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

Consider the invertible nonlinear XOR-Feistel map $F _ f(x, y) = (y,\; x \oplus f(y))$ on unbounded $\mathbb{N} \times \mathbb{N}$. We prove two general parity-driven periodicity laws for completely arbitrary functions $h, g : \mathbb{N} \to \mathbb{N}$:

1. **Even-carry law (period 6):** Whenever $f(2k) = 2k + 1$ and $f(2k + 1) = 2 h(k)$, the triple iterate $F _ f^3(2a, 2b) = (2(b \oplus h(a \oplus b)),\; 2(a \oplus h(a \oplus b)))$ preserves the XOR sum $a \oplus b$ as an exact invariant, forcing $F _ f^6(x, y) = (x, y)$ on the entire non-odd-odd domain $\{2 \mid x \lor 2 \mid y\}$ — **regardless of how chaotic $h$ is**.
2. **Odd-carry law (period 12):** Whenever $f(2k) = 2k + 1$ and $f(2k + 1) = 2 g(k) + 1$, conjugating $F _ f^4$ on $(2\mathbb{N})^2$ by the involution $(a, b) \mapsto (a \oplus b,\; b \oplus g(a \oplus b))$ linearizes it into the $\mathbb{F} _ 2$-Fibonacci map $(u, v) \mapsto (v, u \oplus v)$ of order $3$, forcing $F _ f^{12}(x, y) = (x, y)$ for **every** $(x, y) \in \mathbb{N} \times \mathbb{N}$.

Specializing to the **Binary Lyness map** $F _ c(x, y) = (y,\; x \oplus (y + c))$ (mixing binary carry-free XOR with carry-propagating addition $+ c$ over unbounded $\mathbb{N}$) yields an exact dichotomy: $F _ c^6 = \mathrm{id}$ on all of $\mathbb{N} \times \mathbb{N}$ **if and only if** $c = 0$ or $c = 2^r$ for some $r \in \mathbb{N}$ (even though $y + 2^r$ propagates carries arbitrarily far!). Conversely, every non-power-of-two $c$ breaks period $6$ via an explicit $(t + 3)$-bit witness $(0, 2^{t+2} - 2)$ for odd $c = 1 + 2^{t+1} + s \cdot 2^{t+2}$. Meanwhile, the **bitwise-OR twin** $H _ {2^r}(x, y) = (y,\; x \oplus (y \mathbin{|} (y + 2^r)))$ triggers the odd-carry law and collapses universally to period $12$ for all $r \in \mathbb{N}$ and all $(x, y) \in \mathbb{N} \times \mathbb{N}$.

## For Non-Mathematicians

Pick **any** two whole numbers $x$ and $y$ — even numbers with a million digits. Now repeat a simple two-step digital-circuit mix: add $1$ (or any power of $2$, like $2, 4, 8, \dots$) to $y$, combine the result with $x$ using bitwise XOR, and slide the pair forward: $(x, y) \to (y,\; x \oplus (y + 2^r))$. Because adding $1$ ripples carries arbitrarily far up the binary digits while XOR ignores carries completely, you would expect the numbers to scramble endlessly or grow without bound. Instead, after **exactly $6$ steps**, every single pair of numbers snaps right back to where it started! Even stranger: this miracle happens **only** when the added constant is $0$ or a power of $2$ (for $c = 3$, it immediately fails). And if you replace $y + 2^r$ with the bitwise OR $y \mathbin{|} (y + 2^r)$, every pair of numbers snaps back in **exactly $12$ steps** — both coming from hidden "carry-canceling" symmetries that work even if you replace the upper-bit carry formula with any wild function you want.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib) formalization of universal XOR-Feistel carry-renormalization periodicity laws and the exact power-of-two period-6 dichotomy for the Binary Lyness recurrence over unbounded $\mathbb{N} \times \mathbb{N}$.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `feistelStep_iter_six_of_even_parity` | If $f(2k) = 2k + 1$ and $f(2k + 1) = 2 h(k)$ for an arbitrary $h : \mathbb{N} \to \mathbb{N}$, then $F _ f^6(x, y) = (x, y)$ whenever $x \% 2 = 0 \lor y \% 2 = 0$. |
| `feistelStep_iter_twelve_of_odd_parity` | If $f(2k) = 2k + 1$ and $f(2k + 1) = 2 g(k) + 1$ for an arbitrary $g : \mathbb{N} \to \mathbb{N}$, then $F _ f^{12}(x, y) = (x, y)$ for all $(x, y) \in \mathbb{N} \times \mathbb{N}$. |
| `lynessStep_pow_two_period_six` | For every $r, x, y \in \mathbb{N}$, $F _ {2^r}^6(x, y) = (x, y)$, where $F _ c(x, y) = (y,\; x \oplus (y + c))$. |
| `lynessStep_period_six_iff` | For every $c \in \mathbb{N}$, $(\forall x, y \in \mathbb{N},\; F _ c^6(x, y) = (x, y)) \iff (c = 0 \lor \exists r,\; c = 2^r)$. |
| `orLynessStep_pow_two_period_twelve` | For every $r, x, y \in \mathbb{N}$, $H _ {2^r}^{12}(x, y) = (x, y)$, where $H _ c(x, y) = (y,\; x \oplus (y \mathbin{|} (y + c)))$. |

## Proof Architecture

1. **Exact $F _ f^3$ Invariant for Even-Carry Functions (`feistelStep_iter_six_of_even_parity`):**
   On an even-even pair $(2a, 2b)$, tracing three steps of $F _ f$ under $f(2k) = 2k + 1$ and $f(2k + 1) = 2 h(k)$ gives
   ```math
   (2a, 2b) \to (2b, 2(a \oplus b) + 1) \to (2(a \oplus b) + 1, 2(b \oplus h(a \oplus b))) \to (2(b \oplus h(a \oplus b)), 2(a \oplus h(a \oplus b))).
   ```
   Since $(b \oplus h(a \oplus b)) \oplus (a \oplus h(a \oplus b)) = a \oplus b$, the XOR sum $a \oplus b$ is strictly invariant under $F _ f^3$, so applying $F _ f^3$ a second time cancels $h(a \oplus b)$ identically and returns $(2a, 2b)$. Because every $(x, y)$ with $2 \mid x \lor 2 \mid y$ lands in $(2\mathbb{N})^2$ within $2$ steps and $F _ f$ is injective, $F _ f^6(x, y) = (x, y)$ holds on all non-odd-odd states.

2. **Conjugacy to $\mathbb{F} _ 2$-Fibonacci for Odd-Carry Functions (`feistelStep_iter_twelve_of_odd_parity`):**
   When $f(2k) = 2k + 1$ and $f(2k + 1) = 2 g(k) + 1$, four steps of $F _ f$ map $(2a, 2b)$ to $(2a', 2b')$ where $a' = b \oplus g(a \oplus b)$ and $b' = a \oplus b \oplus g(a \oplus b) \oplus g(a \oplus g(a \oplus b))$. In coordinates $(u, v) = (a \oplus b,\; b \oplus g(a \oplus b))$ (which is a bijection on $\mathbb{N} \times \mathbb{N}$), $F _ f^4$ acts as the exact linear map $(u, v) \mapsto (v, u \oplus v)$ of order $3$, so $F _ f^{12}(2a, 2b) = (2a, 2b)$. Using the explicit inverse $F _ f^{-1}(x, y) = (y \oplus f(x), x)$, every $(x, y) \in \mathbb{N} \times \mathbb{N}$ (including odd-odd states!) reaches $(2\mathbb{N})^2$ in at most $3$ backward steps, proving $F _ f^{12} = \mathrm{id}$ globally.

3. **Binary Lyness Renormalization & Bit-0 Product Splitting (`lynessStep_pow_two_period_six` & `orLynessStep_pow_two_period_twelve`):**
   At $c = 1$, $y + 1$ satisfies $2k \mapsto 2k + 1$ and $2k + 1 \mapsto 2(k + 1)$, so Theorem 1 closes all non-odd-odd states while odd-odd pairs $(2u + 1, 2v + 1)$ map strictly inside the odd-odd sector as $(2v + 1,\; 2(u \oplus (v + 1)) + 1)$, closing by strong induction on $x + y$. For $c = 2^{r+1}$, `lynessStep_two_mul_split` splits bit $0$ (pure XOR, period $3 \mid 6$) from the upper bits (`lynessStep (2^r)`), inductively proving $F _ {2^r}^6 = \mathrm{id}$. Likewise, $y \mathbin{|} (y + 1)$ satisfies $2k \mapsto 2k + 1$ and $2k + 1 \mapsto 2(k \mathbin{|} (k + 1)) + 1$, giving $H _ 1^{12} = \mathrm{id}$ immediately from Theorem 2 and $H _ {2^r}^{12} = \mathrm{id}$ by bit-0 splitting.

4. **Sharpness Dichotomy (`lynessStep_period_six_iff`):**
   Any even $c > 0$ reduces to $c / 2$ by evaluating $F _ c^6$ on $(2x, 2y)$. Any odd $c \ge 3$ can be written as $c = 1 + H + s \cdot 2H$ with $H = 2^{t+1} \ge 2$; because $F _ c$ is causal modulo $2^{t+3} = 4H$, evaluating $F _ c^6(0, 2H - 2) \bmod 4H$ collapses independently of $s \bmod 2$ to first coordinate $2H \ne 0 \pmod{4H}$, proving $F _ c^6(0, 2H - 2) \ne (0, 2H - 2)$.

## Prior-Art Context

- **Classical Lyness & periodic rational recurrences:** The name echoes the classical rational Lyness map $(x, y) \mapsto (y, (y + 1)/x)$ of period $5$ (Lyness 1942) and its generalizations, though our map operates in mixed carry-free XOR and carry-propagating binary arithmetic over $\mathbb{N}$ rather than a field.
- **Addition outside XOR (opposite order of operations):** The MathOverflow thread *"A Bitwise Xor Problem"* investigates the superficially similar recurrence $a _ i = (a _ {i-1} \oplus a _ {i-2}) + 1$ (addition *outside* XOR), which behaves completely differently and grows with periods scaling as $3 \cdot 2^{m-1}$ modulo $2^m$ rather than collapsing to finite period $6$ on unbounded $\mathbb{N}$.
- **T-functions & 2-adic dynamics:** Invertible triangular maps mixing XOR and addition are studied in Klimov & Shamir (*A New Class of Invertible Mappings*, CHES 2002; *New Cryptographic Primitives Based on Multiword T-Functions*, FSE 2004) and Anashin & Khrennikov (*Applied Algebraic Dynamics*, De Gruyter 2009), primarily targeting maximal single-cycle lengths $2^n$ for stream ciphers. A web, literature, and OEIS search found no prior record of the universal even-carry period-6 and odd-carry period-12 Feistel carry-renormalization laws, the exact power-of-two period-6 dichotomy for $F _ c(x, y) = (y, x \oplus (y + c))$, or the period-12 bitwise-OR twin $H _ {2^r}$.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim `#print axioms` output and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` verification manifest.
