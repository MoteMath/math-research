# Audit Report — `bitnet-contraction-hierarchy`

## Executive Summary

- **Package:** `bitnet-contraction-hierarchy` (Palomar Comparator pure-`Init` Lean 4 package)
- **Toolchain:** `leanprover/lean4:v4.34.1` (zero Mathlib, zero external dependencies)
- **Synthetic Score:** **91 / 100** (`Nov=9, Sur=9, Gen=10, Use=8, Ver=10`; weighted `3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 91`)
- **Build Status:** `lake build` PASS (**0 errors, 0 warnings**); `lake build Challenge` PASS (**0 errors**)
- **Axiom Audit:** All 6 headline theorems depend **exclusively** on `[propext, Classical.choice, Quot.sound]`, matching `comparator.json` (`"enable_nanoda": true`, zero `sorryAx`, zero `Lean.ofReduceBool`).

---

## Theorem-by-Theorem Audit Matrix

| # | Theorem (`BitnetContractionChallenge.*`) | Quantifier Scope | Proof Method | Axioms |
|---|---|---|---|---|
| 1 | `ternary_nearest_nonneg_contraction` | Universal `∀ d γ x` (`0 ≤ γ`) | Coordinate-wise gain non-negativity + `sumRat_le_sumRat` (both `ternRound` and `ternRoundStrict`) | `propext`, `Classical.choice`, `Quot.sound` |
| 2 | `bitnet_absmean_contraction_exact` | Universal `∀ d ≥ 1`, `∀ x` (`normSq x > 0`) + exact witness `unitE0 d` | Rescaling to `γ = 1`, `k/4` cancellation, factored quadratic `(d - 1/2 - u)((2d - 1)u - d) ≥ 0` | `propext`, `Classical.choice`, `Quot.sound` |
| 3 | `bitnet_absmax_and_half_contraction_exact` | Universal `∀ d ≥ 1`, `∀ M > 0`, `∀ x` (`max |x_i| = M`) + exact witnesses | Point-and-rest sum extraction with factored quadratics `(2v-1)(d+2-2v) ≥ 0` and `(4v-1)(d+12-12v) ≥ 0` | `propext`, `Classical.choice`, `Quot.sound` |
| 4 | `bitnet_rms_contraction_exact_algebraic` | Universal `∀ d ≥ 1`, `∀ x γ` (`γ > 0, d γ^2 = normSq x`) + `d = 8, 16` witnesses | Coordinate bound `z_i^2 ≤ y_i^2 + y_i + 1/4` + `sumRat_sq_le_sq_sumRat` + `rms_witness_exact` | `propext`, `Classical.choice`, `Quot.sound` |
| 5 | `multilevel_shifted_sqrt_dcrit_exact` | Universal `∀ M ≥ 2`, `∀ d : Nat` + concrete `dCrit` & `harmonicConst` | Exact `Nat` identities + `Nat.mul_le_mul` + `omega` / `grind` | `propext`, `Classical.choice`, `Quot.sound` |
| 6 | `two_stage_ternary_greedy_vs_disjoint_crossover` | Exact `d = 3` and `d = 4` crossover witnesses | Kernel-decided `Int × Int` evaluation (`greedyTwoStageNumDen`, `jointDisjointTwoStageNumDen`) + cross-multiplication `rat_div_lt_div_of_int_cross` | `propext`, `Classical.choice`, `Quot.sound` |

---

## Trust-Boundary & Hygiene Checks

1. **Zero `sorry` / `admit` / `axiom` / `native_decide` / `lemma` outside `Challenge.lean`:** Verified by full-tree grep across `BitnetContraction/`, `BitnetContraction.lean`, and `Solution.lean`.
2. **Exact Challenge–Solution Signature Match:** Every theorem name and type in `Solution.lean` matches `Challenge.lean` verbatim under `namespace BitnetContractionChallenge`.
3. **Zero Floating-Point in Proofs or Definitions:** All quantities are exact `Nat`, `Int`, or `Rat`. The irrational `RMS` law $\alpha \ge (\sqrt{3d+1}-1)/d$ and critical dimension threshold $d > 4M^2 + 2 + 4M\sqrt{M^2+1}$ are formalized in exact algebraic squared form over `Rat` and `Nat`.
4. **Empirical GPU Cross-Check (Search Only, Never Trust Base):** Backed by Wave 4B RX 7900 XTX exact 128-bit integer search (245 launches, 38.61B evaluations, 174.3 s, 12,288 CPU spot-replays, 0 mismatches), with all mathematical claims proved independently from Lean 4 `Init` axioms.
5. **No Scratch Files:** Repository contains only the clean Palomar package files listed in `README.md`.

---

## For Mathematicians / Non-Mathematicians / Prior-Art Summary

See [`README.md`](README.md) for the complete **For Mathematicians**, **For Non-Mathematicians**, **Prior-Art Context**, and **Synthetic Score** (`91 / 100`) sections.
