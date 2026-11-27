# CHKAE: Verified Cayley–Hamilton, Krylov & Perron-Cone Annihilator Engine (`cayley-hamilton-perron-annihilator`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **8 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **84 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): **Mechanism Name:** **CHKAE** (*Verified Cayley–Hamilton, Krylov & Perron-Cone Annihilator Engine*). **Silicon Principle (Finite Binary Matrix/Polynomial Certificate $\to$ Infinite Universal Law $\forall n \in \mathbb{N}$):** In pure silicon binary mathematics, global bit-level sums over $n$-bit words (carried vs. carryless parity correlations, $k$-way binary carry-parity parti*

## For Mathematicians

**Mechanism Name:** **CHKAE** (*Verified Cayley–Hamilton, Krylov & Perron-Cone Annihilator Engine*). **Silicon Principle (Finite Binary Matrix/Polynomial Certificate $\to$ Infinite Universal Law $\forall n \in \mathbb{N}$):** In pure silicon binary mathematics, global bit-level sums over $n$-bit words (carried vs. carryless parity correlations, $k$-way binary carry-parity partition functions, Zeckendorf-constrained multiplier automata) compile via LSB-splitting into integer transfer-matrix observables where $M \in \mathbb{Z}^{d \times d}$ is a finite integer transition matrix and $u, v \in \mathbb{Z}^d$ are exact readout/initial vectors. CHKAE separates **mathematical soundness** (abstract `Fin d -> Int` matrix algebra) from **polynomial-time kernel reflection** (concrete `List (List Int)` certificates checked by Lean 4's kernel `decide`, with zero `Prop` fields in any certificate and zero `native_decide`). CHKAE provides **five composa

## For Non-Mathematicians

**Mechanism Name:** **CHKAE** (*Verified Cayley–Hamilton, Krylov & Perron-Cone Annihilator Engine*). **Silicon Principle (Finite Binary Matrix/Polynomial Certificate $\to$ Infinite Universal Law $\forall n \in \mathbb{N}$):** In pure silicon binary mathematics, global bit-level sums over $n$-bit words (carried vs. carryless parity correlations, $k$-way binary carry-parity parti

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `CayleyHamiltonPerronAnnihilator/Theorems.lean`, definitions in `CayleyHamiltonPerronAnnihilator/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `matAnn_sound` | Machine-checked infinite theorem `matAnn_sound` proved in pure Lean 4 `Init`. |
| `scaledVal_exact_valuation` | Machine-checked infinite theorem `scaledVal_exact_valuation` proved in pure Lean 4 `Init`. |
| `carrySumK_eq_obs` | Exact semantic bridge for ALL `k ≥ 1` and ALL `n : Nat`. |
| `thm_Z5_and_K7_pos` | **THEOREM 2a (Strict Positivity of `Z_5` and `K_7`):** For ALL `n : Nat`, both `Z_corr 5 n > 0` and `K_corr 7 n > 0`. |
| `thm_C3_odd_part_mod4` | Machine-checked infinite theorem `thm_C3_odd_part_mod4` proved in pure Lean 4 `Init`. |
| `thm_C5_pos_for_all_ge_8` | **THEOREM 5b (Eventual Strict Positivity of `C_5` Beyond Descartes' Rule of Signs):** |
| `sharpness_K23_fails` | **Sharpness Witness 1 (Carried-vs-Carryless Positivity Fails at `c = 23`!):** |
| `sharpness_K7_Z5_shift` | **Sharpness Witness 5 (`+3` shift in `K_7(n+3) = 2*Z_5(n)` is sharp):** |

## Prior-Art Context

- - **Classical Literature Distinction:** - Newman (1969) and Coquet (1983) studied $\sum _ {x < N} (-1)^{\mathrm{popcount}(3x)} > 0$ (the unweighted Thue–Morse sum along multiples of $3$), and Drmota–Skałba (1995) studied $\Gamma _ p(n) = \sum _ {x < 2^n} (-1)^{\mathrm{popcount}(px)}$ for prime $p$. By contrast, our **carried-vs-carryless parity correlation** $K _ c(n)$ compares $\mathbb{Z}$-multiplication $c \cdot x$ against $\mathbb{F} _ 2[x]$-multiplication $\mathrm{clmul}(c, x)$, which equals $\Gamma _ c(n)$ when $\mathrm{popcount}(c)$ is even and the signed correlation $\Delta _ c(n)$ when $\mathrm{popcount}(c)$ is odd — revealing both positi
- Hostile-verified PASS by thread referee; pure `leanprover/lean4:v4.34.1` `Init` stack with `enable_nanoda: true` and exact integer Python replay in `scripts/explore_and_verify.py`.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).