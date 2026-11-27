# Silicon Walsh–Hadamard & T-Function Bent Proof Engine (`silicon-tfunction-bent-duality`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **10 / 10** | **9 / 10** | **9 / 10** | **10 / 10** | **93 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): **Mechanism Name:** **Silicon Walsh–Hadamard & T-Function Bent Proof Engine (`SiliconBent`)** — combining: 1. **Bit-Sliced Butterfly FWHT & Exact Silicon Wiener–Khinchin Kernel**, 2. **Causal Silicon T-Function Combinator Algebra & Constructive Bit-by-Bit Hensel Inverter (`tInv`)**, 3. **4-Subblock Kronecker–Dual Bent Lifting Engine & Zero-Sum T-Quad Compiler**, 4. **Unconditio*

## For Mathematicians

**Mechanism Name:** **Silicon Walsh–Hadamard & T-Function Bent Proof Engine (`SiliconBent`)** — combining: 1. **Bit-Sliced Butterfly FWHT & Exact Silicon Wiener–Khinchin Kernel**, 2. **Causal Silicon T-Function Combinator Algebra & Constructive Bit-by-Bit Hensel Inverter (`tInv`)**, 3. **4-Subblock Kronecker–Dual Bent Lifting Engine & Zero-Sum T-Quad Compiler**, 4. **Unconditional Causal-Mask Carlet–T Bent Engine**, and 5. **Finite 15-Hyperplane 4-Bit Certificate $\to$ Infinite Non-$\mathcal{M}^\#$ Lifting Engine**. **How the Finite Binary Object Lifts to $\infty$:** - **Finite-to-Infinite Spectral Lifting:** Rather than verifying bentness bit-width by bit-width, any bitwise/arithmetic map $\pi : \mathbb{N} \to \mathbb{N}$ built from our causal silicon combinator algebra (`+`, `*`, `^^^`, `&&&`, `///`, `2 * ·`, odd affine maps) automatically satisfies `TBijection π` (`Causal π` and local MSB `BitFlip π`). A 3-line constructive bit-by-bi

## For Non-Mathematicians

**Mechanism Name:** **Silicon Walsh–Hadamard & T-Function Bent Proof Engine (`SiliconBent`)** — combining: 1. **Bit-Sliced Butterfly FWHT & Exact Silicon Wiener–Khinchin Kernel**, 2. **Causal Silicon T-Function Combinator Algebra & Constructive Bit-by-Bit Hensel Inverter (`tInv`)**, 3. **4-Subblock Kronecker–Dual Bent Lifting Engine & Zero-Sum T-Quad Compiler**, 4. **Unconditio

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `SiliconTfunctionBentDuality/Theorems.lean`, definitions in `SiliconTfunctionBentDuality/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `walsh_walsh` | Hadamard Involution Theorem: `W_n (W_n f) x = 2^n * f x` for all `x < 2^n`. |
| `mm_isBent` | Parametric Maiorana-McFarland Bent Engine: ANY `TBijection π` and ANY `g` yields an exact bent function on `2*k` bits with flat Walsh spectrum `±2^k`, exact dual via `tInv π k`, and vanishing autocorrelation for all `k ≥ 0`. |
| `zeroSum_tQuad_isBent` | Zero-Sum T-Function Quad Compiler: Given ANY two causal maps `φ1, φ2`, the 4 causal T-functions `ψ0(a)=a`, `ψ1(a)=a ^^^ 2φ1(a)`, `ψ2(a)=a ^^^ 2φ2(a)`, `ψ3(a)=a ^^^ 2(φ1(a) ^^^ φ2(a))` satisfy `ψ0 ^^^ ψ1 ^^^ ψ2 ^^^ ψ3 = 0`, so their dual-inverted MM functions lift via `quadCombine` to an infinite bent family on `2*(k+1)` bits with exact flat Walsh spectrum and vanishing autocorrelation for ALL `k ≥ 1`. |
| `mul3_infinite_bent_and_nonMM` | **Infinite Theorem 1 (`piMul3` — Carried Multiplication by 3):** For ALL `k ≥ 1`, `f_k(x, y) = <x, (3*y) mod 2^k> ⊕ [x = 0]` has exact flat Walsh spectrum `±2^k`, exact closed-form dual, and vanishing autocorrelation; and for ALL `k ≥ 4`, `f_k ∉ M#`! |
| `mul7_infinite_bent_and_nonMM` | **Infinite Theorem 4 (`piMul7` — Carried Multiplication by 7):** For ALL `k ≥ 4`, `f_k(x, y) = <x, (7*y) mod 2^k> ⊕ [x = 0]` is bent with exact flat Walsh spectrum `±2^k`, vanishing autocorrelation, and strictly outside `M#`. |
| `counterexample_non_bijective_mul2` | Counterexample 1: Breaking `BitFlip` (`π(y) = 2*y`, even multiplier) destroys Walsh flatness and vanishing autocorrelation immediately at `k = 1` (`W = 4 ≠ ±2`, `Δ(1) = 4 ≠ 0`). |
| `counterexample_non_causal_shift` | Counterexample 3: Breaking `Causal` (`φ(y) = y / 2`, right-shift) causes `π(y) = y ^^^ (2 * (y / 2))` to collide mod 4 at `y = 0` and `y = 2` (not a bijection!). |
| `nonvacuity_carletT_nonzero_pi0` | Non-vacuity witness for Carlet-T with `π(0) ≠ 0` (`π(y) = 3*y + 1`, `r = 2 ≤ k`). |

## Prior-Art Context

- - **Classical prior art (honestly credited):** Maiorana–McFarland bent functions, Carlet's classes $\mathcal{D}$ / $\mathcal{D} _ 0$ (1994), Preneel / Canteaut–Charpin 4-bent concatenation (`d0 d1 d2 d3 = -1`), Dillon's second-order derivative characterization of $\mathcal{M}^\#$, and Klimov–Shamir T-functions (2002) are classical results in Boolean function theory and symmetric cryptography. - **Claimed contribution (not independently reviewed; no literature search is recorded):** 1. **Unified pure-silicon causal T-function + Hensel inverter + unconditional Carlet–T compiler** in standalone Lean 4, proving that causality alone suffices for all prefix cuts $0 \le r \le k$ even when
- Built against `leanprover/lean4:v4.34.1` (pure `Init` stack; `enable_nanoda: true` in `comparator.json`); `scripts/explore_and_verify.py` re-evaluates small instances in exact integer arithmetic (it proves nothing by itself).

## Scope of the formal statement

Maiorana–McFarland bentness (`mm_isBent`) is a classical result; the Lean content is its proof for the hand-written `walsh`, `mmSign` and `TBijection` definitions in `Defs.lean`. The non-$\mathcal{M}^\#$ statements are for the two specific permutations $y \mapsto 3y$ and $y \mapsto 7y$ (mod $2^k$) and hold for $k \ge 4$ only.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).