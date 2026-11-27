# Gray-Basis & Feistel-Carry Orbit Compilers (`gray-basis-feistel-carry-orbits`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **9 / 10** | **8 / 10** | **7 / 10** | **10 / 10** | **82 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): trailing-ones bit-slice renormalization (`phi n γ`) paired with two reusable silicon orbit compilers — Gray-basis parity-fiber reduction (proving universal order-4 collapse of Gray `bitrev + 1` and the exact MSB carry-kick Hamiltonian phase transition) and Feistel-carry fiber-splice reduction (proving universal Jacobsthal giant-cycle isospectrality for every bijection $h$) — formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

The core operator $\Phi _ \gamma(v) = (v \oplus \gamma) + 1 \pmod{2^n}$ renormalizes cleanly along the trailing-ones run $t = \mathrm{trailingOnes}(n, \gamma)$: even $\gamma$ yields a single Hamiltonian cycle of length $2^n$, while odd $\gamma$ splits into a carry-free odd half (periods $1$ or $2$) and a self-similar width-$(n-1)$ even half, with $\sim \gamma$ always the exact predecessor of $0$ in its $2^{n-t}$-cycle. Two compilers lift this engine to broad families of non-T-function maps:

1. **Compiler A (Gray-Basis Parity-Fiber Reduction):** For any parity-preserving, single-coset-equivariant involution $P$ conjugated by the binary Gray code $G$, $F _ {P, \delta}(x) = (G^{-1}(P(G(x))) + 1) \oplus \delta$ collapses in 2 steps on even states to $\Phi _ \gamma$ for a single compiled defect $\gamma$. For **every** bit-permutation involution $\pi \in S _ w$ ($w \ge 2$) with $j = \pi(0)$, $F(x) = G^{-1}(\pi(G(x))) + 1$ has compiled defect $2^j - 1$, zero-orbit length $2^{w - j}$, and every state has minimal period in $\{2, 4, 2^{w - j}\}$. In particular, Gray-basis `bitrev + 1` collapses to **universal bounded order $4$** for all $w \ge 2$, whereas adding a single MSB carry-kick $2^{w-1}$ creates a **single full-period Hamiltonian cycle of length $2^w$** if and only if $\pi(0) \in \{0, w - 2, w - 1\}$ (for all $w \ge 3$).
2. **Compiler B (Feistel-Carry Fiber-Splice Reduction):** For $H _ h(a, b) = ((a \cdot 2^k + (b \oplus h(a))) + 1) \bmod 2^{m+k}$, the unique carry-exit $\sim h(a)$ of each fiber splices all $2^m$ zero-orbits end-to-end into one giant cycle of length $\sum _ a 2^{k - \mathrm{trailingOnes}(h(a))}$, while all other states have period $1$ or $2$. Hence $H _ h$ is a single Hamiltonian cycle iff $h(a)$ is even for all $a$; and when $m = k$ and $h$ is **any bijection** (linear or nonlinear), the giant cycle has universal Jacobsthal length $L _ 0$ with $3 L _ 0 = 2^{2k+1} + 1$, completely independent of $h$.

## For Non-Mathematicians

Mix a bit permutation (like reversing the bits of a number) with binary addition (`+ 1`), and the resulting cycle lengths usually look chaotic. This package discovers that doing the permutation in the binary Gray-code basis — where consecutive numbers differ in only one bit — completely tames the dynamics at every bit width. Reversing bits in Gray basis and adding 1 collapses so completely that every number returns to itself in at most 4 steps, no matter how many bits wide the word is. Yet adding one extra bit at the very top (`+ 2^(w-1) + 1`) shatters that collapse and turns the exact same map into a single giant loop visiting every single w-bit number once! A second compiler analyzes Feistel-carry maps where the top half of a word XORs into the bottom half before adding 1, proving that whenever the mixing function is any bijection at all, the giant cycle has an exact Jacobsthal length independent of which bijection you choose.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib) formalization of trailing-ones bit-slice renormalization, Gray-basis parity-fiber collapse, MSB carry-kick Hamiltonian phase transitions, and universal Feistel-carry Jacobsthal isospectrality.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `phi_singleCycle_iff_even` | Core engine: for $n \ge 1$, $\Phi _ \gamma(v) = (v \oplus \gamma) + 1 \pmod{2^n}$ is a single Hamiltonian cycle if and only if $\gamma$ is even. |
| `grayInvMap_singleCycle_iff` | Compiler A: for any `GrayInvolutionSpec P δ m` at width $n + 1 \ge 2$, `grayInvMap P δ` is single-cycle if and only if `compiledDefect δ m` is even. |
| `grayBitPermInvolution_plusOne_universal` | For every bit-permutation involution $\pi$ on $n + 1 \ge 2$ bits with $j = \pi(0)$, Gray-basis $\pi + 1$ has zero-orbit length $2^{n + 1 - j}$, is single-cycle iff $j = 0$, and every state has period in $\{2, 4, 2^{n + 1 - j}\}$. |
| `grayBitrev_plusOne_order4` | For every width $w \ge 2$, Gray-basis `bitrev + 1` has minimal period $2$ at $0$ and satisfies $F^4(x) = x$ for every $x \in \mathrm{BitVec}\ w$. |
| `grayBitPermInvolution_msbKick_singleCycle_iff` | For every $w \ge 3$ and bit-permutation involution $\pi$, Gray-basis $\pi + (2^{w-1} + 1)$ is a single Hamiltonian cycle if and only if $\pi(0) \in \{0, w - 2, w - 1\}$. |
| `grayBitrev_msbKick_singleCycle` | For every width $w \ge 3$, Gray-basis `bitrev + (2^{w-1} + 1)` is a single full-period Hamiltonian cycle of length $2^w$. |
| `feistelCarry_singleCycle_iff` | Compiler B: for $m, k \ge 1$ and any $h : \mathrm{BitVec}\ m \to \mathrm{BitVec}\ k$, `feistelCarry m k h` is a single Hamiltonian cycle if and only if $h(a)$ is even for all $a$. |
| `feistelCarry_bijection_jacobsthal` | For every $k \ge 1$ and every bijection $h$ on $\mathrm{BitVec}\ k$, `feistelCarry k k h` has giant zero-orbit length $L _ 0$ with $3 L _ 0 = 2^{2k+1} + 1$ (independent of $h$) and all other periods in $\{1, 2\}$. |

## Proof Architecture

1. **Trailing-Ones Core Engine (`phi_zero_orbit`, `phi_complete_pointwise`, `phi_singleCycle_iff_even`):** bit-0 parity splitting renormalizes odd $\gamma$ to width $n - 1$, giving exact pointwise periods and proving that $\sim \gamma$ is the exact final state of the zero-orbit.
2. **Compiler A (`grayInvMap_return_map`, `grayBitPermInvolution_plusOne_universal`, `grayBitPermInvolution_msbKick_singleCycle_iff`):** zero-carry increment on even states cancels $P$ in 2 steps, conjugating the return map to $\Phi _ \gamma$ with explicit compiled defect $\gamma$.
3. **Compiler B (`feistelCarry_zero_orbit`, `feistelCarry_singleCycle_iff`, `feistelCarry_bijection_jacobsthal`):** splices fiber zero-orbits at their exact carry-exit states $\sim h(a)$ and sums $2^{k - \mathrm{trailingOnes}(h(a))}$ over any bijection $h$ to obtain the Jacobsthal number.

## Prior-Art Context

- **Bit-permutation + carry-increment orbits:** Distinct from `bitrev-increment-cycles` (which analyzes standard-basis `bitrev + 1`); here conjugating bit-permutation involutions by the binary Gray code yields exact parity-fiber collapse, universal order-4 collapse for `bitrev + 1`, and the MSB carry-kick Hamiltonian phase transition, while Feistel-carry maps yield universal Jacobsthal isospectrality.
- **Status:** not independently reviewed; no prior-art search is recorded.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

Toolchain: `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib). See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts, [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` verification manifest, and `scripts/explore_and_verify.py` for the exact-integer exploration and verification script (zero floating point).
