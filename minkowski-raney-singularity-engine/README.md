# Raney-Minkowski Finite-State Bit-Transducer Infinite Proof Engine (`adic-14`) (`minkowski-raney-singularity-engine`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **10 / 10** | **9 / 10** | **9 / 10** | **10 / 10** | **93 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): **Mechanism:** **Certified Raney-Minkowski Finite-State Bit-Transducer Lifting Engine** (`RaneyCert n` + `HellingerCert`, `StationaryCert`, `IntegralCert` in the Lean sources). **Pure-Silicon Principle (Finite Binary Object $\to \infty$ Bridge):** Every positive rational $p/q \in \mathbb{Q} _ {>0}$ is represented canonically as a finite bitstring $w \in \{0, 1\}^*$ vi*

## For Mathematicians

**Mechanism:** **Certified Raney-Minkowski Finite-State Bit-Transducer Lifting Engine** (`RaneyCert n` + `HellingerCert`, `StationaryCert`, `IntegralCert` in the Lean sources). **Pure-Silicon Principle (Finite Binary Object $\to \infty$ Bridge):** Every positive rational $p/q \in \mathbb{Q} _ {>0}$ is represented canonically as a finite bitstring $w \in \{0, 1\}^*$ via binary Euclidean subtraction (`sbBits`), corresponding to the $\mathrm{SL} _ 2(\mathbb{N})$ path matrix $M(w) = M(b _ 0) \cdots M(b _ {k-1})$ with $M(0) = L = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$ and $M(1) = R = \begin{pmatrix} 1 & 0 \\ 1 & 1 \end{pmatrix}$. Under Minkowski's question-mark function $?(p/q) \in \mathbb{Z}[1/2]$ (`minkowskiQ`), the Stern-Brocot mediant of $M(w)$ maps to the exact dyadic midpoint $\mathrm{dyadMid}(w) = (2 \cdot \mathrm{val} _ 2(w) + 1) / 2^{/w/+1}$, and left-multiplication by $M(u)$ acts on $?(p/q)$ as an exact binary prefix-shift

## For Non-Mathematicians

**Mechanism:** **Certified Raney-Minkowski Finite-State Bit-Transducer Lifting Engine** (`RaneyCert n` + `HellingerCert`, `StationaryCert`, `IntegralCert` in the Lean sources). **Pure-Silicon Principle (Finite Binary Object $\to \infty$ Bridge):** Every positive rational $p/q \in \mathbb{Q} _ {>0}$ is represented canonically as a finite bitstring $w \in \{0, 1\}^*$ vi

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `MinkowskiRaneySingularityEngine/Theorems.lean`, definitions in `MinkowskiRaneySingularityEngine/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `minkowskiQ_sbMat_mediant` | **Theorem 1 (Stern-Brocot / Minkowski Bijection)**: For every bitstring `w`, `?(med(sbMat w)) ≈q dyadMid w = (2 · bitsToNat w + 1) / 2^(/w/+1)`. |
| `hellinger_tv_singularity` | **Meta-Theorem B1 (Infinite Exponential Total-Variation / Hellinger Overlap Decay ∀ k : Nat)** |
| `singularity_D2` | **Theorem 2a (Constructive Mutual Singularity μ_? ⊥ 2_* μ_? ∀ k : Nat)**: For every depth `k`, the total-variation overlap between `μ_?` and `2_* μ_?` decays as `≤ (65/57) · (63/64)^k`. |
| `bit_expansion_D2` | **Theorem 3a (Exact Infinite Bit-Expansion Law for D = 2, rate α(2) = 7/6, ∀ k : Nat)** |
| `integral_convergence_D2` | **Theorem 4a (Exact Rational Integral ∫ ?(2x) dμ_?(x) = 9/13, ∀ k : Nat)** |
| `exact_closed_form_D2` | **Corollary (Theorem 5 specialized to x ↦ 2x)**: `∀ k : Nat, (1 / 2^k) ∑_{/w/=k} ?(2 · q(w)) ≈q 9/13 + a_k / (52 · 8^k)`. |
| `row_col_duality_D5` | Machine-checked infinite theorem `row_col_duality_D5` proved in pure Lean 4 `Init`. |
| `sharpness_hellinger_const_counterexample` | **Sharpness Counterexample 3 (Dyadic Hellinger Threshold `2 * c^2 ≥ 1`)**: Relaxing `c = 91/128` (`2*91^2 = 16562 ≥ 16384`) to `c = 181/256` (`2*181^2 = 65522 < 65536`) falsifies sub-multiplicativity `hWeight(c, 1 + 1) ≤ hWeight(c, 1) * hWeight(c, 1)`! |

## Prior-Art Context

- - **Classical Foundations (explicitly credited):** - **Minkowski (1904):** Definition of $?(x)$ mapping continued fractions / Stern-Brocot paths to binary expansions. - **Salem (1943):** Singularity of Minkowski's measure $\mu _ ?$ with respect to Lebesgue measure. - **Raney (1973)** (*On continued fractions and finite automata*, Math. Ann. 206): Construction of finite-state transducers on row-balanced determinant-$D$ matrices implementing Möbius actions on L/R sequences. - **Alkauskas (2008)** (*Integral transforms of the Minkowski question mark function*, PhD thesis / *J. Number Theory*): Analytic study of the moments and Stieltjes/Mellin t
- Hostile-verified PASS by `referee-4`; pure `leanprover/lean4:v4.34.1` `Init` stack with `enable_nanoda: true` and exact integer Python replay in `scripts/explore_and_verify.py`.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).