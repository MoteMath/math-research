# Key-Invariant Cycle Spectra of XOR-Keyed ARX Fibonacci Maps (`arx-fibonacci-isospectrality`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **9 / 10** | **8 / 10** | **8 / 10** | **10 / 10** | **84 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): exact finite-level 2-adic perturbation law and closed-form minimal period theorem proving that the XOR-keyed modular ARX Fibonacci map $G _ {c,m}(x, y) = (y \bmod 2^m,\; (x + (y \oplus c)) \bmod 2^m)$ has the exact same cycle spectrum for every $m$-bit key $c$, via the period-preserving involution $(x, y) \mapsto (x \oplus c, y \oplus c)$, formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

For any word size $m \ge 1$ and any key $c \in \mathbb{N}$, define the modular ARX (Add-XOR) Fibonacci map on $\{0, \dots, 2^m - 1\}^2$ by

```math
G_{c,m}(x, y) = \bigl(y \bmod 2^m,\; (x + (y \oplus c)) \bmod 2^m\bigr).
```

Even though $y \mapsto y \oplus c$ is nonlinear over $\mathbb{Z}/2^m\mathbb{Z}$ and mixes non-commuting bitwise XOR with modular addition (producing wildly different trajectories and carry patterns for different keys $c$), we prove that **every key $c$ produces the exact same cycle spectrum** as the unkeyed linear Fibonacci map $G _ {0,m}$:

1. **Exact 2-adic perturbation law (`xor_add_pow_two_mod`):** For every $r, y, c \in \mathbb{N}$,
   ```math
   ((y + 2^r) \oplus c) \equiv (y \oplus c) + \sigma_r \cdot 2^r \pmod{2^{r+2}},
   \qquad \sigma_r = \begin{cases} 3 & \text{if bit } r \text{ of } c \text{ is } 1, \\ 1 & \text{if bit } r \text{ of } c \text{ is } 0. \end{cases}
   ```
2. **Closed-form minimal period (`arxFibStep_exact_minPeriod`):** $(c \bmod 2^m, c \bmod 2^m)$ is the unique fixed point of $G _ {c,m}$, and every non-fixed state $(x, y) \in \{0, \dots, 2^m - 1\}^2$ whose lowest bit differing from $(c, c)$ is $r _ 0 < m$ has **exact minimal period** $3 \cdot 2^{m - 1 - r _ 0}$, independent of the key bits of $c$ above $r _ 0$.
3. **Isospectral involution (`arxFibStep_isospectral_bijection`):** The involution $(x, y) \mapsto (x \oplus (c \bmod 2^m),\; y \oplus (c \bmod 2^m))$ preserves exact minimal periods identically between $G _ {c,m}$ and $G _ {0,m}$ for every $m \ge 1$, every key $c$, and every state $(x, y)$ — **even though it is not a dynamical conjugacy**!
4. **Coefficient sharpness (`arxFibStep3_breaks_isospectrality`):** Replacing $1 \cdot x$ with $3 \cdot x$ shatters key-invariance already at $m = 2$: at $c = 1$ every state satisfies $H _ {1,2}^3(x, y) = (x, y)$ (zero period-6 states), whereas at $c = 0$ the state $(0, 1)$ has exact minimal period $6$.

## For Non-Mathematicians

Take a classic Fibonacci-style counter on $m$-bit computer integers: keep two numbers $(x, y)$, and at each step replace them with $(y, x + y)$ wrapped around modulo $2^m$. Now try to "encrypt" or scramble the counter by picking a secret $m$-bit key $c$ and XORing $y$ with $c$ before every addition: $(x, y) \to (y,\; x + (y \oplus c)) \bmod 2^m$. Because XOR and addition clash on binary carries, you might expect different keys $c$ to break the counter into totally different loop sizes. Remarkably, **the secret key cannot change a single loop length**: for *every* bit-width $m$ and *every* key $c$, the collection of cycle lengths is **identical** to the unkeyed Fibonacci counter (one fixed point, one loop of length $3$, two loops of length $6$, four loops of length $12$, and so on, with every non-fixed state having exact period $3 \cdot 2^{m - 1 - r _ 0}$ determined purely by the lowest bit $r _ 0$ where $(x, y)$ differs from $(c, c)$). Yet this invariance is razor-sharp: changing $x + (y \oplus c)$ to $3x + (y \oplus c)$ destroys it immediately on 2-bit numbers.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib) formalization proving exact key-invariant cycle spectra for modular XOR-keyed ARX Fibonacci maps for all bit-widths $m \ge 1$ and all keys $c \in \mathbb{N}$.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `xor_add_pow_two_mod` | For all $r, y, c \in \mathbb{N}$, $((y + 2^r) \oplus c) \bmod 2^{r+2} = ((y \oplus c) + \sigma _ r \cdot 2^r) \bmod 2^{r+2}$, where $\sigma _ r = 3$ if `c.testBit r` and $1$ otherwise. |
| `arxFibStep_fixed_point_iff` | For $m \ge 1$ and $x, y < 2^m$, $G _ {c,m}(x, y) = (x, y) \iff (x = c \bmod 2^m \land y = c \bmod 2^m)$. |
| `arxFibStep_exact_minPeriod` | For $m \ge 1$, $x, y < 2^m$, and $r _ 0 < m$ the lowest bit where $(x, y)$ differs from $(c, c)$, `IsMinPeriod (arxFibStep c m) (x, y) (3 * 2 ^ (m - 1 - r0))`. |
| `arxFibStep_isospectral_bijection` | For all $m \ge 1$, $c, L \in \mathbb{N}$, and $x, y < 2^m$, `IsMinPeriod (arxFibStep c m) (x, y) L ↔ IsMinPeriod (arxFibStep 0 m) (x ^^^ (c % 2 ^ m), y ^^^ (c % 2 ^ m)) L`. |
| `arxFibStep3_breaks_isospectrality` | For $H _ {c,m}(x, y) = (y \bmod 2^m, (3x + (y \oplus c)) \bmod 2^m)$ at $m = 2$, every state satisfies $H _ {1,2}^3(x, y) = (x, y)$ while $(0, 1)$ has exact minimal period $6$ under $H _ {0,2}$. |

## Proof Architecture

1. **Exact 2-Adic Perturbation of Bitwise XOR (`xor_add_pow_two_mod`):**
   Splitting $y$ and $c$ at bit $r$ (`xor_split_two_pow`) isolates bits $\ge r$ cleanly modulo $2^{r+2} = 4 \cdot 2^r$, reducing the exact two-bit carry interaction to the 16-case identity $((q + 1) \oplus e) \equiv (q \oplus e) + (3 \text{ if } 2 \nmid e \text{ else } 1) \pmod{4}$. Induction on $b$ lifts this to $((y + b \cdot 2^r) \oplus c) \equiv (y \oplus c) + \sigma _ r b \cdot 2^r \pmod{2^{r+2}}$.

2. **Linearized Jacobian Propagation (`arxFibRaw_iter_perturb`):**
   Let $J _ {\sigma}(a, b) = (b,\; a + \sigma b)$ for $\sigma \in \{1, 3\}$. Because the unreduced map `arxFibRaw c` is causal modulo every $2^k$, induction on $n$ shows that for every $r, n, x, y, a, b \in \mathbb{N}$,
   ```math
   G_c^n(x + a \cdot 2^r,\; y + b \cdot 2^r) \equiv G_c^n(x, y) + J_{\sigma_r}^n(a, b) \cdot 2^r \pmod{2^{r+2}}.
   ```
   Crucially, **both** Jacobians $J _ 1$ and $J _ 3$ share the exact same order-$3$ behavior modulo $2$, non-vanishing lift $J _ {\sigma}^3(a, b) - (a, b) \not\equiv 0 \pmod{4}$ whenever $(a, b) \not\equiv (0, 0) \pmod{2}$, non-vanishing doubling $(a, b) + J _ {\sigma}^3(a, b) \equiv 2(\cdot) \not\equiv 0 \pmod{4}$, and order-$6$ identity $J _ {\sigma}^6 \equiv I \pmod{4}$.

3. **Exact 2-Adic Lifting (`arxFibRaw_lift`):**
   Applying `arxFibRaw_iter_perturb` at the fixed point $(c, c)$ yields the base lift ($k = 0$): $G _ c^3(x, y) \equiv (x, y) \pmod{2^{r _ 0 + 1}}$ and $\not\equiv (x, y) \pmod{2^{r _ 0 + 2}}$. Inducting on $k$ via $G _ c^{2L} = G _ c^L \circ G _ c^L$ shows that $G _ c^{3 \cdot 2^k}(x, y)$ agrees with $(x, y)$ modulo $2^{r _ 0 + k + 1}$ and strictly differs modulo $2^{r _ 0 + k + 2}$ for every $k \in \mathbb{N}$.

4. **Exact Minimality via Period-GCD Closure (`arxFibStep_exact_minPeriod`) & Involution (`arxFibStep_isospectral_bijection`):**
   Because the return times $\{n : F^n(p) = p\}$ of *any* map are closed under `Nat.gcd`, any strict divisor $g < 3 \cdot 2^s$ of $3 \cdot 2^s$ either divides $3 \cdot 2^{s-1}$ (contradicting the $(s - 1)$-level non-lift) or is coprime to $3$ and divides $2^s$ (forcing $G _ c^1(x, y) \equiv (x, y) \pmod{2^{r _ 0 + 1}}$ via $\gcd(2^s, 3) = 1$, contradicting `arxFibRaw_step1_ne_mod`). Since $(x \oplus (c \bmod 2^m),\; y \oplus (c \bmod 2^m))$ shares the exact same first differing bit $r _ 0$ relative to $(0, 0)$ as $(x, y)$ does relative to $(c, c)$, it has the exact same minimal period for every $x, y < 2^m$.

## Prior-Art Context

- **2-adic differentiability of bitwise XOR & level-by-level lifting:** Anashin (*Uniformly distributed sequences of p-adic integers, II*, arXiv:math/0209407 (2002)) and Anashin & Khrennikov (*Applied Algebraic Dynamics*, De Gruyter, 2009) develop the 2-adic calculus of compatible (1-Lipschitz) functions, including the 2-adic derivative of $x \mapsto x \oplus c$ and Hensel/Jacobian period lifting modulo $2^m$.
- **T-functions & ARX primitives:** Klimov & Shamir (*A New Class of Invertible Mappings*, CHES 2002; *New Cryptographic Primitives Based on Multiword T-Functions*, FSE 2004) analyze triangular Add-XOR state-update maps modulo $2^m$.
- **Unkeyed Pisano periods modulo $2^m$:** Wall (*Fibonacci Series Modulo $m$*, Amer. Math. Monthly **67** (1960), 525–532) established the unkeyed Fibonacci period $\pi(2^m) = 3 \cdot 2^{m-1}$.
- **Prior-art status:** No prior record was found by the authors; the search was not recorded. The authors know of no prior publication establishing that the nonlinear XOR-keyed ARX Fibonacci map $G _ {c,m}(x, y) = (y, x + (y \oplus c)) \bmod 2^m$ has an exact key-independent cycle spectrum identical to unkeyed linear Fibonacci for all $m \ge 1$ and all keys $c$, paired with the explicit period-preserving involution $(x, y) \mapsto (x \oplus c, y \oplus c)$ (which is not a conjugacy) and the sharp coefficient-$3$ failure witness.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim `#print axioms` output and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` verification manifest.
