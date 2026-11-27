# Pure-Silicon Walsh–Automaton Spectral-Gap Engine (`specmat-15`) (`bitwise-expander-walsh-gaps`)

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
| `mod3_exact_spectral_gap` | **THEOREM A (Exact Tight Integer Spectral Gap of `G_mod3` ∀ k ≥ 1):** 1. Universal Rayleigh spectral gap: `∀ f, ∑ f = 0 → mod3Gap k * ‖f‖² ≤ ⟨f, L f⟩` 2. Centered variance Poincaré: `∀ f, mod3Gap k * Var(f) ≤ 2^k * ⟨f, L f⟩` 3. Exact tightness witness: `χ_{allOnes k}` is non-zero, zero-sum, and attains exact equality! |
| `fib_expander_mixing_lemma` | Machine-checked infinite theorem `fib_expander_mixing_lemma` proved in pure Lean 4 `Init`. |
| `witness_fib_k4` | Machine-checked infinite theorem `witness_fib_k4` proved in pure Lean 4 `Init`. |
| `sharpness_mod2_always_disconnected` | Machine-checked infinite theorem `sharpness_mod2_always_disconnected` proved in pure Lean 4 `Init`. |
| `witness_mod3_eml_k5` | Machine-checked infinite theorem `witness_mod3_eml_k5` proved in pure Lean 4 `Init`. |

## Prior-Art Context

- - **Distinction from Anti-Duplication Catalog (CHARTER Section 4):** Does not overlap `zero-carry-spanning-trees` (`x & y = 0`), `skew-thue-morse-pfaffian`, `clmul-lift-determinants`, `carry-determinants`, `carry-blocks-determinants`, `bitrev-increment-cycles`, `binary-lyness-periods`, or `arx-fibonacci-isospectrality`. - **Honest Classical Prior-Art Credit & Distinctions:** - **Newman's Sum & Multiples of 3 (`G_mod3`):** The extremal character sum $\sum _ {x < 2^k,\, 3 \mid x} (-1)^{s _ 2(x)}$ evaluated at $\chi _ {\mathrm{allOnes}(k)}$ is the classical **D. J. Newman (1969)** sum (*On the number of binary digits in a multiple of three*, Pro
- Hostile-verified PASS by `referee-3`; pure `leanprover/lean4:v4.34.1` `Init` stack with `enable_nanoda: true` and exact integer Python replay in `scripts/explore_and_verify.py`.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).