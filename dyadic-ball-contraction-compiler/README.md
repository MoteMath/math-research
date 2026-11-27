# Verified Lean 4 Dyadic Ball-Arithmetic & Contraction Enclosure Compiler (`certcomp-13`) (`dyadic-ball-contraction-compiler`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **8 / 10** | **9 / 10** | **9 / 10** | **10 / 10** | **86 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): **Name:** *Adaptive 2D Dyadic Ball-Arithmetic, Algebraic Secant-Slope & Binary-Tree Telescoping Contraction Compiler* (`DyadicCompiler`). **Core Silicon Principle (Finite Binary Certificate $\to$ Infinite $\forall n \in \mathbb{N}$ & $\forall p \in P _ 0$ Theorems):** 1. **Exact Dyadic Balls $(m, e, r)$ with Verified Outward Binary Rounding:** Every interval is stored as a triple*

## For Mathematicians

**Name:** *Adaptive 2D Dyadic Ball-Arithmetic, Algebraic Secant-Slope & Binary-Tree Telescoping Contraction Compiler* (`DyadicCompiler`). **Core Silicon Principle (Finite Binary Certificate $\to$ Infinite $\forall n \in \mathbb{N}$ & $\forall p \in P _ 0$ Theorems):** 1. **Exact Dyadic Balls $(m, e, r)$ with Verified Outward Binary Rounding:** Every interval is stored as a triple $(m \in \mathbb{Z}, e \in \mathbb{N}, r \in \mathbb{N})$ denoting the exact rational interval $$\mathcal{B}(m, e, r) = \left[\frac{m - r}{2^e},\; \frac{m + r}{2^e}\right] \subset \mathbb{Q}$$ over a quotient-free exact rational kernel `ExactQ` ($\mathrm{num} \in \mathbb{Z}, \mathrm{den} \in \mathbb{N} _ {>0}$). Precision blowup is controlled by `roundTo b p`, which uses exact integer Euclidean floor/ceiling division to truncate exponent $e > p$ with optimal 1-ULP outward rounding (`roundTo_sound`). Exact binary bisection splits $\mathcal{B}(m, e, r)$ losslessly int

## For Non-Mathematicians

**Name:** *Adaptive 2D Dyadic Ball-Arithmetic, Algebraic Secant-Slope & Binary-Tree Telescoping Contraction Compiler* (`DyadicCompiler`). **Core Silicon Principle (Finite Binary Certificate $\to$ Infinite $\forall n \in \mathbb{N}$ & $\forall p \in P _ 0$ Theorems):** 1. **Exact Dyadic Balls $(m, e, r)$ with Verified Outward Binary Rounding:** Every interval is stored as a triple

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `DyadicBallContractionCompiler/Theorems.lean`, definitions in `DyadicBallContractionCompiler/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `checkParamTree_sound` | Machine-checked infinite theorem `checkParamTree_sound` proved in pure Lean 4 `Init`. |
| `contraction_fixed_point_unique` | Meta-Theorem 5: Uniqueness of Fixed Points in B0. |
| `bring_quintic_residual_decay` | Exact algebraic residual identity for Bring Newton step: /x^5 + (1 + p)x - 1/ = (1 + p + 5 x^4) * /F_p(x) - x/ ≤ 7 * /F_p(x) - x/ on [0, 1/2] × [1/2, 1]! |
| `bring_direct_oscillatory_contraction` | Machine-checked infinite theorem `bring_direct_oscillatory_contraction` proved in pure Lean 4 `Init`. |
| `certHalley_valid` | Machine-checked infinite theorem `certHalley_valid` proved in pure Lean 4 `Init`. |
| `certBringAlt_valid` | Machine-checked infinite theorem `certBringAlt_valid` proved in pure Lean 4 `Init`. |
| `mutation_reject_halley_no_subdivision` | Machine-checked infinite theorem `mutation_reject_halley_no_subdivision` proved in pure Lean 4 `Init`. |
| `mutation_reject_bring_alt_expanding_region` | Machine-checked infinite theorem `mutation_reject_bring_alt_expanding_region` proved in pure Lean 4 `Init`. |

## Prior-Art Context

- - **Relation to Classical Literature:** Interval/ball arithmetic (Moore, Neumaier, Arb/FLINT, CoqInterval/Flocq, Isabelle `Affine_Arithmetic`) is well-established for bounding finite evaluations and real-valued ODE/Taylor models using real-analysis Mean Value Theorems. What is distinctive and pure-silicon native here is: 1. **Zero-Analysis Exact Algebraic Slope Compiler:** Our `evalJetBall` + `evalCenteredBall` + binary-tree telescoping proof discharges global Lipschitz contraction, quantitative Cauchy bounds, and $\forall n \in \mathbb{N}$ orbit theorems purely over exact integer/dyadic arithmetic in standalone Lean 4 core (zero Mathlib, zer
- Hostile-verified PASS by `referee-5`; pure `leanprover/lean4:v4.34.1` `Init` stack with `enable_nanoda: true` and exact integer Python replay in `scripts/explore_and_verify.py`.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).