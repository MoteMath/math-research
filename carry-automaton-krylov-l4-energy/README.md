# Carry-Coupled Binary Automaton Correlation & Dual-Krylov $L^4$-Energy Proof Engine (`carry-automaton-krylov-l4-energy`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **8 / 10** | **8 / 10** | **8 / 10** | **10 / 10** | **82 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): **Name:** *Carry-Coupled Binary Automaton Correlation & Dual-Krylov $L^4$-Energy Proof Engine* (`BinAuto` $\to$ `apCorr` $\to$ `LeftAnnihilator` + `DualKrylovEnergy`).*

## For Mathematicians

**Name:** *Carry-Coupled Binary Automaton Correlation & Dual-Krylov $L^4$-Energy Proof Engine* (`BinAuto` $\to$ `apCorr` $\to$ `LeftAnnihilator` + `DualKrylovEnergy`).

## For Non-Mathematicians

**Name:** *Carry-Coupled Binary Automaton Correlation & Dual-Krylov $L^4$-Energy Proof Engine* (`BinAuto` $\to$ `apCorr` $\to$ `LeftAnnihilator` + `DualKrylovEnergy`).

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `CarryAutomatonKrylovL4Energy/Theorems.lean`, definitions in `CarryAutomatonKrylovL4Energy/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Scope of the formal statement

The statements are about the hand-written binary automata and polynomial families defined in `Defs.lean` (for example `mask6Auto`); `mask6Cert_valid` is a finite certificate check, and the other headline statements are universally quantified over their stated parameters.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `apCorr_even` | **THEOREM 1a (Universal Even-Shift Subdivision Law):** Exact bit-pair lifting at even shift `s = 2t` for every `BinAuto d`. |
| `bijTail_infinite_flat_spectrum` | **THEOREM 1 (Universal Infinite Flat-Spectrum & Pythagorean Theorem for ALL `m` and ALL `ψ`):** For EVERY width `m : Nat`, EVERY nonlinear feedback function `ψ : Fin (2^m) → Bool`, and EVERY block length `k : Nat`: 1. Exact zero total autocorrelation for ALL shifts `s ≥ 1`: `∑_q apCorr q q k s = 0`. 2. Exact pure-integer polynomial flatness for ALL `X : Int`: `∑_q P_{q, k}(X) * P^{rev}_{q, k}(X) = 2^(k + m + 1) * X^(2^k - 1)`. 3. Exact partial-sum Pythagorean law (`X = 1`): `∑_q (∑_{n < 2^k} f_q(n))^2 = 2^(k + m + 1)`. |
| `innerQRZ_dualStep` | **Exact Adjointness Theorem (`innerQRZ_dualStep`):** `⟨dualStep A W, S⟩ = ⟨W, primalStep A S⟩` for EVERY `BinAuto d`, `W`, and `S`. |
| `paperfolding_direct_rec` | Direct recurrence verification: `g(2n) = (-1)^n` and `g(2n+1) = g(n)` for all `n : Nat`. |
| `baumSweet_classical_rec` | Direct verification that `baumSweetAuto.eval 0` satisfies the classical Baum-Sweet recurrence: `b(0)=1`, `b(2n+1)=b(n)`, `b(4n)=b(n)`, `b(4n+2)=0` for ALL `n : Nat`. |
| `mask6Cert_valid` | Machine-checked finite instance: the witnessed dual certificate `mask6Cert` for `mask6Auto` passes the Boolean check `checkWitnessedDualCert` (a finite computation). |
| `mask6_totE4_rec` | **THEOREM 4a (Exact Sparse Degree-5 Recurrence for `totE4 mask6Auto`, ∀ `k : Nat`):** `T(k + 5) = 2 * T(k + 4) + 16 * T(k + 2) + 256 * T(k)`. |
| `rudinShapiro_E4_closed_form` | Machine-checked infinite theorem `rudinShapiro_E4_closed_form` proved in pure Lean 4 `Init`. |

## Prior-Art Context

- - **Classical Prior Art (Explicitly Distinguished):** - *Rudin-Shapiro (Shapiro 1951, Rudin 1959, Littlewood 1968, Brillhart–Morton 1978, Høholdt–Jensen 1988):* corresponds to the single base case $m = 0, \psi \equiv 0$ of our Theorem 1 and our 10-line benchmark corollary `rudinShapiro_E4_closed_form`. - *Golay Complementary Sets & Generalized Boolean Functions (Golay 1961, Davis–Jedwab 1999, Paterson 2000):* construct fixed-length-$2^k$ complementary sets from quadratic/graph Boolean functions on $k$ variables. By contrast, our Theorem 1 constructs a **universal 2-parameter family of infinite 2-automatic sliding-window parity sequences** (`b
- Built against `leanprover/lean4:v4.34.1` (pure `Init` stack; `enable_nanoda: true` in `comparator.json`); `scripts/explore_and_verify.py` re-evaluates small instances in exact integer arithmetic (it proves nothing by itself).

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).