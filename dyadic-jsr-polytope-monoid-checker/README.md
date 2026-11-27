# Exact $\mathbb{Z}[1/2]$ Switched-Polytope & Invariant-Cone Matrix-Monoid Proof Compiler (`certcomp-4`) (`dyadic-jsr-polytope-monoid-checker`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **9 / 10** | **9 / 10** | **10 / 10** | **91 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): **Mechanism Name:** **Exact $\mathbb{Z}[1/2]$ Dual-Lifting Matrix-Monoid Contraction, JSR & Invariant-Cone Proof Compiler** (`DyadicMonoidEngine` in [Proof.lean](file:///c:/Users/devin/Desktop/math/silicon-infinite-mechanisms-20261126/certcomp-4/Proof.lean)). **Pure-Silicon Principle (Finite $\to$ Infinite Bridge):** Given a finite family of exact dyadic matrices $M _ b = 2^{-s*

## For Mathematicians

**Mechanism Name:** **Exact $\mathbb{Z}[1/2]$ Dual-Lifting Matrix-Monoid Contraction, JSR & Invariant-Cone Proof Compiler** (`DyadicMonoidEngine` in [Proof.lean](file:///c:/Users/devin/Desktop/math/silicon-infinite-mechanisms-20261126/certcomp-4/Proof.lean)). **Pure-Silicon Principle (Finite $\to$ Infinite Bridge):** Given a finite family of exact dyadic matrices $M _ b = 2^{-s} A _ b \in \mathrm{Mat} _ {d \times d}(\mathbb{Z}[1/2])$ ($b \in \{0, \dots, m - 1\}$), determining boundedness, exponential decay, or strict positivity across **all** infinite-horizon binary matrix products $M _ {b _ n} \cdots M _ {b _ 1}$ (the Joint Spectral Radius problem) is undecidable in general. Our compiler replaces real analysis and floating-point heuristics with **three pure-data integer/dyadic certificate checkers** verified inside the Lean 4.36.0 kernel by `decide` (zero `native_decide`, zero `Prop` fields in any certificate, zero `Float`): 1. **DFA-S

## For Non-Mathematicians

**Mechanism Name:** **Exact $\mathbb{Z}[1/2]$ Dual-Lifting Matrix-Monoid Contraction, JSR & Invariant-Cone Proof Compiler** (`DyadicMonoidEngine` in [Proof.lean](file:///c:/Users/devin/Desktop/math/silicon-infinite-mechanisms-20261126/certcomp-4/Proof.lean)). **Pure-Silicon Principle (Finite $\to$ Infinite Bridge):** Given a finite family of exact dyadic matrices $M _ b = 2^{-s

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `DyadicJsrPolytopeMonoidChecker/Theorems.lean`, definitions in `DyadicJsrPolytopeMonoidChecker/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `switched_polytope_sound` | **MAIN SOUNDNESS META-THEOREM 1 (DFA-Switched Exact Dyadic Operator-Norm Contraction):** If `checkSwitchedPolytopeCert cert = true`, then for EVERY word `w` of arbitrary length accepted by the DFA (`runDFA cert.step q0 w = some qn`) and EVERY row `p : Fin d`, the exact `Z[1/2]` row `ℓ_1` norm of `dyadicWordProd M w` satisfies: `‖(dyadicWordProd M w)_p‖_1 ≤_{Z[1/2]} C_const * (lamNum / 2^lamShift)^/w/`. |
| `convex_hull_infinite_alphabet_sound` | **MAIN SOUNDNESS META-THEOREM 2 (Infinite-Alphabet Dyadic Convex-Hull Contraction):** One finite polytope certificate checked by `decide` on `m` vertex matrices AUTOMATICALLY certifies uniform exponential contraction for ALL arbitrary-length, time-varying products drawn from the ENTIRE INFINITE dyadic convex hull `conv_{Z[1/2]}(M_0, ..., M_{m-1})`! |
| `periodic_eigen_sound` | **MAIN SOUNDNESS META-THEOREM 4 (Exact Periodic Eigen-Witness JSR Lower Bound):** If `checkPeriodicEigenCert cert = true`, then for EVERY `k : Nat`, the `k`-fold repeated word `w_0^k` (length `/w_0/ * k`) attains exact `ℓ_∞` operator norm at least `(/eig/ / 2^(s * /w_0/))^k`! |
| `thm1_convex_hull_contraction` | **THEOREM 1C (Infinite-Alphabet Dyadic Convex-Hull Contraction):** Every arbitrary-length sequence of time-varying dyadic convex combinations of `M0, M1` contracts at the exact same rate `4 * (15/16)^n`. |
| `thm1_sharpness_unbounded` | Machine-checked infinite theorem `thm1_sharpness_unbounded` proved in pure Lean 4 `Init`. |
| `thm3_signed_cone_subradius` | **THEOREM 3A (Strict Positivity & Exponential Subradius `≥ 5/4` for Signed-Entry Matrices):** |
| `thm4_unconstrained_lower` | Machine-checked infinite theorem `thm4_unconstrained_lower` proved in pure Lean 4 `Init`. |
| `mut8_bad_naf_dfa_rejected` | Machine-checked infinite theorem `mut8_bad_naf_dfa_rejected` proved in pure Lean 4 `Init`. |

## Prior-Art Context

- - **Classical Literature:** Polyhedral Lyapunov norms and invariant-polytope algorithms for the Joint Spectral Radius originate with Barabanov (1988), Protasov (1996), Jungers (2009), Guglielmi–Protasov (2013), and path-dependent multinorms with Protasov–Jungers–Blondel (2010); $C^1$ regularity of Dubuc–Deslauriers 4-point subdivision was analyzed via JSR and polytopic norms by Rioul (1992), Hechler–Mössner–Reif (2009), and Charina–Conti–Guglielmi–Protasov (2014/2016). - **What Is Genuinely Novel Here:** 1. **Zero-Float, Standalone Kernel-Verified Compiler in Core Lean 4:** Rather than floating-point LP/SDP heuristics or external numerical JS
- Hostile-verified PASS by `referee-5`; pure `leanprover/lean4:v4.34.1` `Init` stack with `enable_nanoda: true` and exact integer Python replay in `scripts/explore_and_verify.py`.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).