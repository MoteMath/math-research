# Verified Lean 4 Dyadic Ball-Arithmetic & Contraction Enclosure Compiler (`dyadic-ball-contraction-compiler`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **8 / 10** | **9 / 10** | **9 / 10** | **10 / 10** | **86 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): **Name:** *Adaptive 2D Dyadic Ball-Arithmetic, Algebraic Secant-Slope & Binary-Tree Telescoping Contraction Compiler* (`DyadicCompiler`). **Core Silicon Principle (Finite Binary Certificate $\to$ Infinite $\forall n \in \mathbb{N}$ & $\forall p \in P _ 0$ Theorems):** 1. **Exact Dyadic Balls $(m, e, r)$ with Verified Outward Binary Rounding:** Every interval is stored as a triple*

## For Mathematicians

**Name:** *Adaptive 2D Dyadic Ball-Arithmetic, Algebraic Secant-Slope & Binary-Tree Telescoping Contraction Compiler* (`DyadicCompiler`). **Core Silicon Principle (Finite Binary Certificate $\to$ Infinite $\forall n \in \mathbb{N}$ & $\forall p \in P _ 0$ Theorems):** 1. **Exact Dyadic Balls $(m, e, r)$ with Verified Outward Binary Rounding:** Every interval is stored as a triple $(m \in \mathbb{Z}, e \in \mathbb{N}, r \in \mathbb{N})$ denoting the exact rational interval $$\mathcal{B}(m, e, r) = \left[\frac{m - r}{2^e},\; \frac{m + r}{2^e}\right] \subset \mathbb{Q}$$ over a quotient-free exact rational kernel `ExactQ` ($\mathrm{num} \in \mathbb{Z}, \mathrm{den} \in \mathbb{N} _ {>0}$). Precision blowup is controlled by `roundTo b p`, which uses exact integer Euclidean floor/ceiling division to truncate exponent $e > p$ with 1-ULP outward rounding (soundness is proved; optimality is not) (`roundTo_sound`). Exact binary bisection splits $\mathcal{B}(m, e, r)$ losslessly int

## For Non-Mathematicians

**Name:** *Adaptive 2D Dyadic Ball-Arithmetic, Algebraic Secant-Slope & Binary-Tree Telescoping Contraction Compiler* (`DyadicCompiler`). **Core Silicon Principle (Finite Binary Certificate $\to$ Infinite $\forall n \in \mathbb{N}$ & $\forall p \in P _ 0$ Theorems):** 1. **Exact Dyadic Balls $(m, e, r)$ with Verified Outward Binary Rounding:** Every interval is stored as a triple

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `DyadicBallContractionCompiler/Theorems.lean`, definitions in `DyadicBallContractionCompiler/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Scope of the formal statement

The soundness meta-theorems and the interval-iteration statements are parametric in the exponent and parameter ball; `certHalley_valid`, `certBringAlt_valid` and the two mutation rejections are finite Boolean computations. The maps (the Bring quintic Newton step, the `x -> 1/(1+x^4)` map, a Halley step) are the specific expressions defined in `Defs.lean`.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `checkParamTree_sound` | Soundness meta-theorem: if the Boolean checker `checkParamTree` accepts a certificate tree, then for every parameter `p` in the parameter ball the map is self-mapped and Lipschitz with the stated constant `q` on the ball `B0`. |
| `contraction_fixed_point_unique` | Meta-Theorem 5: Uniqueness of Fixed Points in B0. |
| `bring_quintic_residual_decay` | For every parameter `p` in `certBring.p0` ($[0, 1/2]$), start `x0` in `certBring.b0` ($[1/2, 1]$) and first Newton iterate `x1`, every iterate `xn` satisfies $|x_n^5 + (1+p)x_n - 1| \le 7 \cdot (7/8)^n \cdot |x_1 - x_0|$. |
| `bring_direct_oscillatory_contraction` | For `x0`, `y0` in the box `certBringAlt.b0`, all iterates of `exprBringDirect` (at parameter 0) stay in the box and $|x_n - y_n| \le (63/64)^n |x_0 - y_0|$. |
| `certHalley_valid` | Machine-checked finite instance: the Boolean check `checkParamContraction certHalley` returns `true` (a finite computation). |
| `certBringAlt_valid` | Machine-checked finite instance: the Boolean check `checkParamContraction certBringAlt` returns `true` (a finite computation). |
| `mutation_reject_halley_no_subdivision` | Machine-checked finite instance: the checker rejects `certHalley` with its subdivision tree replaced by a single leaf. |
| `mutation_reject_bring_alt_expanding_region` | Machine-checked finite instance: the checker rejects `certBringAlt` with its box replaced by the expanding region `⟨17, 5, 1⟩`. |

## Prior-Art Context

- - **Relation to Classical Literature:** Interval/ball arithmetic (Moore, Neumaier, Arb/FLINT, CoqInterval/Flocq, Isabelle `Affine_Arithmetic`) is well-established for bounding finite evaluations and real-valued ODE/Taylor models using real-analysis Mean Value Theorems. What is distinctive and pure-silicon native here is: 1. **Zero-Analysis Exact Algebraic Slope Compiler:** Our `evalJetBall` + `evalCenteredBall` + binary-tree telescoping proof discharges global Lipschitz contraction, quantitative Cauchy bounds, and $\forall n \in \mathbb{N}$ orbit theorems purely over exact integer/dyadic arithmetic in standalone Lean 4 core (zero Mathlib, zer
- Built against `leanprover/lean4:v4.34.1` (pure `Init` stack; `enable_nanoda: true` in `comparator.json`); `scripts/explore_and_verify.py` re-evaluates small instances in exact integer arithmetic (it proves nothing by itself).

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).