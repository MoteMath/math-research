# Pure-Silicon Walsh–Automaton Spectral-Gap Engine (`bitwise-expander-walsh-gaps`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **9 / 10** | **9 / 10** | **10 / 10** | **91 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): **Mechanism Name:** **Exact Integer Walsh–Automaton Spectral-Gap Engine (`WalshAutomatonEngine`)** **Core Silicon Principle:** A $2^k$-vertex explicit bitwise-edge Cayley graph $G _ k(P)$ on $\mathrm{BitVec}\ k$ (edges $x \sim y \iff P(x \oplus y) = \mathrm{true}$, with $P(0) = \mathrm{false}$) has an exponentially large $2^k \times 2^k$ Laplacian $L _ k$. Classical spectral gr*

## For Mathematicians

**Mechanism Name:** **Exact Integer Walsh–Automaton Spectral-Gap Engine (`WalshAutomatonEngine`)** **Core Silicon Principle:** A $2^k$-vertex explicit bitwise-edge Cayley graph $G _ k(P)$ on $\mathrm{BitVec}\ k$ (edges $x \sim y \iff P(x \oplus y) = \mathrm{true}$, with $P(0) = \mathrm{false}$) has an exponentially large $2^k \times 2^k$ Laplacian $L _ k$. Classical spectral graph theory diagonalizes $L _ k$ over $\mathbb{R}$ or $\mathbb{C}$ and estimates eigenvalues numerically. In pure silicon binary math, `WalshAutomatonEngine` compiles the infinite family $\{G _ k(P)\} _ {k \ge 1}$ through a **two-layer exact integer bridge** requiring **zero real numbers, zero complex numbers, zero floating-point arithmetic, and zero divisions**: 1. **Layer 1 — Exact Integer Walsh–Parseval–Rayleigh & Expander Mixing Engine:** Using pure bit-slice recursion (`bvSum` over `BitVec.cons`) and exact $\{-1, +1\}$ bitwise inner-product characters $\chi _

## For Non-Mathematicians

**Mechanism Name:** **Exact Integer Walsh–Automaton Spectral-Gap Engine (`WalshAutomatonEngine`)** **Core Silicon Principle:** A $2^k$-vertex explicit bitwise-edge Cayley graph $G _ k(P)$ on $\mathrm{BitVec}\ k$ (edges $x \sim y \iff P(x \oplus y) = \mathrm{true}$, with $P(0) = \mathrm{false}$) has an exponentially large $2^k \times 2^k$ Laplacian $L _ k$. Classical spectral gr

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `BitwiseExpanderWalshGaps/Theorems.lean`, definitions in `BitwiseExpanderWalshGaps/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `wht_plancherel` | Exact Integer Plancherel Identity over `BitVec k` (zero division, zero floats). |
| `dirichletForm_eq_wht` | Exact Integer Laplacian-Rayleigh Spectral Decomposition. |
| `expander_mixing_lemma_int` | Master Lifting Theorem 4 (Exact Integer Expander Mixing Lemma — zero reals, zero sqrt). |
| `mod3_exact_spectral_gap` | **THEOREM A (Exact Tight Integer Spectral Gap of `G_mod3` ∀ k ≥ 1):** 1. Universal Rayleigh spectral gap: `∀ f, ∑ f = 0 → mod3Gap k * ‖f‖² ≤ ⟨f, L f⟩` 2. Centered variance Poincaré: `∀ f, mod3Gap k * Var(f) ≤ 2^k * ⟨f, L f⟩` 3. Exact tightness witness: `χ_{allOnes k}` is non-zero, zero-sum, and attains exact equality. Note: `mod3Gap k = 0` for `k <= 4` (the graph is disconnected there), so the gap statement is trivially `0` for those `k`; the gap is positive from `k = 5` (`2, 4, 16, 32, 90, 180, ...` for `k = 5, 6, 7, 8, 9, 10, ...`, recomputed by direct Walsh transform). |
| `fib_expander_mixing_lemma` | For every `k >= 3`, the integer expander-mixing inequality `disc^2 <= mu^2 * s(2^k - s) * t(2^k - t)` holds for the Fibbinary graph (`x ~ y` iff `x XOR y` is nonzero with no two adjacent 1-bits), with `mu = Lucas(k-1) - 1`. |
| `witness_fib_k4` | Machine-checked finite instance (`k = 4`): the Fibbinary graph has degree `7`, eigenvalue `3` at `fibWitnessMax 4`, eigenvalue `-3` at `fibWitnessMin 4`, and Dirichlet form `64` on `chi (fibWitnessMax 4)`. |
| `sharpness_mod2_always_disconnected` | For every `k >= 1`, the character `chi_1` is zero-sum, has squared norm `2^k` and Dirichlet form `0` under `mod2Pred`, so the mod-2 graph is disconnected (spectral gap `0`). |
| `witness_mod3_eml_k5` | Machine-checked finite instance (`k = 5`): for `S = {x < 11}` and `T = {x odd}` (so `s = 11`, `t = 16`), the integer expander-mixing inequality holds for the mod-3 graph with `mu = 8`. |

## Prior-Art Context

- - **Distinction from Anti-Duplication Catalog (CHARTER Section 4):** Does not overlap `zero-carry-spanning-trees` (`x & y = 0`), `skew-thue-morse-pfaffian`, `clmul-lift-determinants`, `carry-determinants`, `carry-blocks-determinants`, `bitrev-increment-cycles`, `binary-lyness-periods`, or `arx-fibonacci-isospectrality`. - **Honest Classical Prior-Art Credit & Distinctions:** - **Newman's Sum & Multiples of 3 (`G_mod3`):** The extremal character sum $\sum _ {x < 2^k,\, 3 \mid x} (-1)^{s _ 2(x)}$ evaluated at $\chi _ {\mathrm{allOnes}(k)}$ is the classical **D. J. Newman (1969)** sum (*On the number of binary digits in a multiple of three*, Pro
- Built against `leanprover/lean4:v4.34.1` (pure `Init` stack; `enable_nanoda: true` in `comparator.json`); `scripts/explore_and_verify.py` re-evaluates small instances in exact integer arithmetic (it proves nothing by itself).

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).