# Bit-Reversal Increment Cycles (`bitrev-increment-cycles`)

A complete, sorry-free, **pure-`Init` (zero Mathlib)** Lean 4 formalization of the exact parity dichotomy for the $k$-bit reversal-plus-one permutation

```math
f_k(x) = (\mathrm{bitrev}_k(x) + 1) \bmod 2^k \qquad (x \in \{0, 1, \dots, 2^k - 1\}).
```

## Main Theorems

For every $k \ge 1$, the map $f _ k$ is a bijection on $\{0, \dots, 2^k - 1\}$ (composition of the bit-reversal involution with $+1 \bmod 2^k$, i.e., a binary shift-register/butterfly-increment composition). Its global cycle structure splits cleanly by the parity of $k$:

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `bitrevInc_odd_single_cycle` | For every odd bit-width $k = 2t + 1$, $f _ k$ is a **single full-period Hamiltonian cycle** of length $2^{2t+1}$. |
| `bitrevInc_even_zero_period` | For every even bit-width $k = 2(m+1)$, the orbit of $0$ under $f _ {2(m+1)}$ has **exact minimal period** $2^{m+2} - 1$ (exponentially shorter than $2^{2m+2}$). |
| `bitrevInc_single_cycle_iff_odd` | For every $k \ge 1$, $f _ k$ acts as a single cycle on $\{0, \dots, 2^k - 1\}$ **if and only if** $k$ is odd. |
| `bitrevInc_return_map` | Exact $k \to k + 2$ return-map law on the embedded slice $2m = (0, m, 0)$: returns in $3$ steps from $2^k - 1$ to $0$, in $5$ steps from $f _ k^{-1}(2^k - 1)$ to $2$ (absorbing $(1,0,0)$), and in $4$ steps from every other $m < 2^k$ to $2 f _ k^2(m)$. |

## Proof Architecture (`k -> k + 2` Return-Map Renormalization)

Writing a $(k + 2)$-bit integer as a triple $(a, m, b) = a \cdot 2^{k+1} + 2m + b$ with $a, b \in \{0, 1\}$ and $0 \le m < 2^k$:

```math
\mathrm{bitrev}_{k+2}(a, m, b) = (b, \mathrm{bitrev}_k(m), a),
```

so adding $1 \pmod{2^{k+2}}$ yields the exact transition rules:
- $f _ {k+2}(0, m, b) = (b, \mathrm{bitrev} _ k(m), 1)$,
- $f _ {k+2}(1, m, b) = (b, f _ k(m), 0)$ when $m \ne 2^k - 1$,
- $f _ {k+2}(1, 2^k - 1, b) = (1 - b, 0, 0)$ (carry out of the middle $k$ bits flips $b$).

Tracing the first return to the slice $(0, m, 0) = 2m$ produces an exact 3/4/5-step return map:
- **3-step jump** ($m = 2^k - 1$): $(0, 2^k - 1, 0) \to (0, 2^k - 1, 1) \to (1, 2^k - 1, 1) \to (0, 0, 0)$.
- **5-step jump** ($m \ne 2^k - 1$, $f _ k(m) = 2^k - 1$): $(0, m, 0) \to (0, \mathrm{bitrev} _ k(m), 1) \to (1, m, 1) \to (1, 2^k - 1, 0) \to (1, 0, 0) \to (0, 1, 0)$.
- **4-step advance** (all other $m$): $(0, m, 0) \to (0, \mathrm{bitrev} _ k(m), 1) \to (1, m, 1) \to (1, f _ k(m), 0) \to (0, f _ k^2(m), 0)$.

This single renormalization law explains the entire parity dichotomy:
1. **Odd $k$:** The period $2^k$ of $f _ k$ is **even**, so stepping by $+2$ from $0$ visits all even indices $0, 2, \dots, 2^k - 2$, hits $f _ k^{-1}(2^k - 1)$, takes the **5-step parity-switching jump** to index $1$, visits all odd indices $1, 3, \dots, 2^k - 1$, and closes via the 3-step jump back to $0$ in $4(2^k - 2) + 5 + 3 = 2^{k+2}$ steps — sweeping all $2^{k+2}$ states.
2. **Even $k = 2(m+1)$:** The period $L _ m = 2^{m+2} - 1$ of $0$ is **odd**, so $L _ m - 1$ is even! Stepping by $+2$ from $0$ lands directly on $2^k - 1$ after $(L _ m - 1)/2$ four-step segments and closes via the 3-step jump back to $0$ without ever triggering the 5-step switch, giving exact minimal period $4 \cdot (L _ m - 1)/2 + 3 = 2 L _ m + 1 = 2^{m+3} - 1$.

## Prior-Art Context

The bit-reversal involution is a foundational primitive in radix-2 FFTs, Van der Corput sequences, and permutation networks, and composing an involution with a cyclic shift $+1 \bmod 2^k$ is a classic dihedral-type construction. While the short-cycle behavior of $x \mapsto (\mathrm{bitrev} _ k(x) + 1) \bmod 2^k$ is elementary to state, we found no published proof of this exact odd/even Hamiltonian-cycle dichotomy or its $3/4/5$-step $k \to k + 2$ return-map renormalization law in the literature or OEIS (in particular, the even-width cycle-count sequence $2, 3, 5, 9, 17, \dots$ and maximum cycle length sequence $3, 12, 20, 52, 116, 244, \dots$, $2^{m+2} - 12$ for $m \ge 3$, were verified empirically up to $k = 22$, $2^{22} = 4{,}194{,}304$).

## Build & Verification

Pure `Init` — builds from scratch in under 10 seconds with zero external dependencies:

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim `#print axioms` output and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` verification manifest.
