# 2-Adic Bruhat–Tits Lattice-Gauge Automaton Engine for Carry-Bounded Base-2 Representations (`bruhat-tits-carry-gauge-automata`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **8 / 10** | **8 / 10** | **8 / 10** | **10 / 10** | **82 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): **Mechanism:** **2-Adic Bruhat–Tits Lattice-Gauge Automaton Engine (`LatticeGaugeCert`)** paired with the **First-Principles Carry-Bounded Representation Compiler (`carryCount_eq_evalMat`)** and **Modular Quotient Automaton Engine (`ModQuotientCert`)**.*

## For Mathematicians

**Mechanism:** **2-Adic Bruhat–Tits Lattice-Gauge Automaton Engine (`LatticeGaugeCert`)** paired with the **First-Principles Carry-Bounded Representation Compiler (`carryCount_eq_evalMat`)** and **Modular Quotient Automaton Engine (`ModQuotientCert`)**.

## For Non-Mathematicians

**Mechanism:** **2-Adic Bruhat–Tits Lattice-Gauge Automaton Engine (`LatticeGaugeCert`)** paired with the **First-Principles Carry-Bounded Representation Compiler (`carryCount_eq_evalMat`)** and **Modular Quotient Automaton Engine (`ModQuotientCert`)**.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `BruhatTitsCarryGaugeAutomata/Theorems.lean`, definitions in `BruhatTitsCarryGaugeAutomata/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `carryCount_eq_evalMat` | **First-Principles Combinatorial Equivalence Theorem**: For ANY digit weight table `w` with `w 0 = 1`, ANY carry cap `C`, ANY bit-width `width`, and ANY `n < 2 ^ width`, the direct combinatorial weighted count of carry-bounded representations `carryCount w C width n c` equals the `(C + 1)`-dimensional binary matrix product `evalMat (carryMat w C false) (carryMat w C true) (e0Vec C) n c`. |
| `sound` | **Master Engine Theorem 4 (Exact Modular Quotient Soundness, `∀ n : Nat`)**. |
| `thm_2x2_5point_rigidity` | **Infinite Theorem A4 (2×2 5-Point Finite-to-Infinite 2-Adic Rigidity IFF)**: For ANY integer weights `(1, w1, w2, w3)`, matching `ExactVal2 (f2 w1 w2 w3 n) (phi3 n)` on ALL `n : Nat` is equivalent to matching on just the 5 points `{1, 2, 3, 7, 8}`, and equivalent to the exact mod-8 congruence `w1 % 4 = 3 ∧ w2 % 4 = 3 ∧ w3 % 4 = 1 ∧ (w1 + w2 + w3) % 8 = 7`. |
| `thm_2x2_k_equiv_3_mod_8` | **Infinite Theorem A5 (Binomial Specialization for ALL `k = 8*t + 3`, `k`-way 1-Bit-Carry Addition)**. |
| `thm_3x3_exact_v2` | **Infinite Theorem C1 (3×3 Exact Unbounded 2-Adic Valuation Law)**: For ALL `(w1, w2, w3, w4, w5) ∈ ℤ⁵` with `w1 % 8 = 4 ∧ w2 % 4 = 2 ∧ w3 % 8 = 4 ∧ w4 % 2 = 1 ∧ w5 % 16 = 0`, and ALL `n : Nat`, `ExactVal2 (f3 w1 w2 w3 w4 w5 n) (phi4 n)`. |
| `thm_phi4_unbounded` | **Unboundedness Witness for `Φ_4`**: `∀ m, phi4 (2^(m+2) - 1) = m + 2`. |
| `nonvacuous_3x3_k4` | Non-vacuity witness 3: `k = 4, C = 2` inhabits `LatticeGaugeCert` (3×3). |
| `sharpness_3x3_all_five_weights` | **Sharpness Counterexample 7 (All 5 Individual Weight Moduli in 3×3 Family, failing at `n = 1, 2, 3, 4, 5`)**. |

## Prior-Art Context

- - **Distinction from classical literature:** - Unconstrained hyperbinary partitions ($D = \{0,1,2\}$, Stern's diatomic sequence, Reznick 1990), binary partition asymptotics via matrix products (**Protasov 2000**), and unconstrained $k$-way sums ($\binom{n+k-1}{k-1}$, Kummer's theorem) are classical. - Allouche–Shallit $2$-regular sequences and Christol's theorem establish finite-state automaticity for **fixed** modulus $m$, which cannot certify **unbounded** $2$-adic valuations $\nu _ 2(f(n)) \to \infty$ or odd-part congruences $\mathrm{odd} _ 2(f(n)) \bmod 4$. - Existing $p$-adic valuation studies of Stern-type and $k$-regular sequences (e.g
- Hostile-verified PASS by `referee-4`; pure `leanprover/lean4:v4.34.1` `Init` stack with `enable_nanoda: true` and exact integer Python replay in `scripts/explore_and_verify.py`.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).