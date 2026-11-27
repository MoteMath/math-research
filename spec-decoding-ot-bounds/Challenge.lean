/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpecDecodingOt.Defs

/-!
# Trusted Challenge Statements (`spec-decoding-ot-bounds`)

Universal and exact pure-`Init` Lean 4 statements. Note: "i.i.d. OT" (`alphaIID`, a minimum over
subsets of the Strassen functional `strassenObj`) and "Cyclic Madow" (`alphaMadow2`, a minimum over
masks of a folded-interval functional) are the definitions in `Defs.lean`; their equality with
the operational i.i.d. and Cyclic Madow drafting schemes is not proved here.
1. `multidraft_corr_vs_iid_exact_gaps`: exact multi-draft speculative decoding correlated-vs-i.i.d.
   optimal transport additive gap `((K - 1) / K)^K` and multiplicative gap `K^K / (K^K - (K - 1)^K)`
   for ALL `K ≥ 1`, ALL `V`, ALL probability distributions `p, q`, and ALL subsets `S`, plus exact
   attainment witness for every `K ≥ 1`.
2. `cyclic_madow_optimality_refutation_exact`: exact rational counterexamples refuting both
   default-order (`1/2 < 3/4 < 1`) and oracle descending-`p/q`-sorted (`17/20 < 91/100 < 1`)
   Cyclic Madow optimality at `K = 2`.
3. `quantized_draft_loss_k1_exact`: exact tight single-draft (`K = 1`) quantized-draft acceptance
   loss bound `(R - 1) / (R + 1)` (= `tanh(ε / 2)`) for ALL `V ≥ 2` and `R ≥ 1`, with exact witness.
4. `quantized_draft_loss_multidraft_exact`: exact tight correlated `K`-draft (`K ≥ 2`) quantized-draft
   acceptance loss bound `(K - 1) * (R^2 - 1) / (1 + (K - 1) * R^2)` for ALL `K ≥ 2`, `V ≥ 2`, `R ≥ 1`,
   with exact witness.
5. `modular_bitvec_reversible_exact_inverse`: unconditional bit-exact invertibility (bijection) of
   `L`-layer modular `BitVec b` reversible Transformer blocks for ALL bit-widths `b`, ALL depths `L`,
   ALL layer maps `F, G`, and ALL states `s`.
6. `symplectic_float_reversible_unimodular`: exact unimodularity `det M(γ) = det (M(γ)^n) = 1`,
   hyperbolic trace `2 + γ^2 > 2` (`γ ≠ 0`), lower bound `(M(γ)^n)_{0,0} ≥ 1 + n * γ^2`, and
   exponential `ℓ_∞` row-sum amplification `(M(γ)^n)_{0,0} + (M(γ)^n)_{0,1} ≥ (1 + γ)^n` (`0 ≤ γ`).
-/

namespace SpecDecodingOtChallenge

open SpecDecodingOt

/-- Theorem 1 (Exact Multi-Draft Correlated vs I.I.D. Optimal Transport Gaps):
    For ALL `K ≥ 1`, ALL `V`, ALL rational probability distributions `p, q : Fin V → Rat`, and
    ALL subsets `S : Fin V → Bool`:
    - Additive gap: `alphaCorr K p q - strassenObj K p q S ≤ ((K - 1) / K)^K`,
    - Multiplicative gap: `(K^K - (K - 1)^K) * alphaCorr K p q ≤ K^K * strassenObj K p q S`,
    and BOTH bounds are attained with exact equality for every `K ≥ 1` on a 2-symbol distribution. -/
theorem multidraft_corr_vs_iid_exact_gaps (K : Nat) (hK : 1 ≤ K) :
    (∀ (V : Nat) (p q : Fin V → Rat), isProbDist p → isProbDist q →
      ∀ (S : Fin V → Bool),
        alphaCorr K p q - strassenObj K p q S ≤ ratPow (((K : Rat) - 1) / (K : Rat)) K ∧
        (((K ^ K : Nat) : Rat) - (((K - 1) ^ K : Nat) : Rat)) * alphaCorr K p q ≤
          ((K ^ K : Nat) : Rat) * strassenObj K p q S) ∧
    (∃ p q : Fin 2 → Rat,
      isProbDist p ∧ isProbDist q ∧
      alphaCorr K p q = 1 ∧
      alphaIID K p q = 1 - ratPow (((K : Rat) - 1) / (K : Rat)) K ∧
      alphaCorr K p q - alphaIID K p q = ratPow (((K : Rat) - 1) / (K : Rat)) K ∧
      (((K ^ K : Nat) : Rat) - (((K - 1) ^ K : Nat) : Rat)) * alphaCorr K p q =
        ((K ^ K : Nat) : Rat) * alphaIID K p q) := by
  sorry

/-- Theorem 2 (Exact Constructive Refutation of Naive & Oracle-Sorted Cyclic Madow Optimality):
    At `K = 2, V = 4`:
    - Default-order Cyclic Madow on `(madowCE1P, madowCE1Q)` yields `1/2 < 3/4 < 1` (strictly
      worse than i.i.d. OT);
    - Even oracle descending-`p/q`-sorted Cyclic Madow on `(madowCE2P, madowCE2Q)` yields
      `17/20 < 91/100 < 1` (strictly worse than both i.i.d. OT and the correlated OT ceiling). -/
theorem cyclic_madow_optimality_refutation_exact :
    (isProbDist madowCE1P ∧ isProbDist madowCE1Q ∧
      alphaMadow2 madowCE1P madowCE1Q = (1 : Rat) / 2 ∧
      alphaIID 2 madowCE1P madowCE1Q = (3 : Rat) / 4 ∧
      alphaCorr 2 madowCE1P madowCE1Q = 1 ∧
      alphaMadow2 madowCE1P madowCE1Q < alphaIID 2 madowCE1P madowCE1Q ∧
      alphaIID 2 madowCE1P madowCE1Q < alphaCorr 2 madowCE1P madowCE1Q) ∧
    (isProbDist madowCE2P ∧ isProbDist madowCE2Q ∧
      (∀ i j : Fin 4, i.val ≤ j.val → madowCE2P j / madowCE2Q j ≤ madowCE2P i / madowCE2Q i) ∧
      alphaMadow2 madowCE2P madowCE2Q = (17 : Rat) / 20 ∧
      alphaIID 2 madowCE2P madowCE2Q = (91 : Rat) / 100 ∧
      alphaCorr 2 madowCE2P madowCE2Q = 1 ∧
      alphaMadow2 madowCE2P madowCE2Q < alphaIID 2 madowCE2P madowCE2Q ∧
      alphaIID 2 madowCE2P madowCE2Q < alphaCorr 2 madowCE2P madowCE2Q) := by
  sorry

/-- Theorem 3 (Exact Single-Draft `K = 1` Quantized-Draft Acceptance Loss Law):
    For ALL `V ≥ 2`, `R ≥ 1`, probability distribution `p`, and positive draft weights `w, w'`
    satisfying `w_i ≤ R * w'_i` and `w'_i ≤ R * w_i`:
    `|alpha1 p (softmaxRat w) - alpha1 p (softmaxRat w')| ≤ (R - 1) / (R + 1)`,
    attained with exact equality for every `V ≥ 2`. -/
theorem quantized_draft_loss_k1_exact (V : Nat) (hV : 2 ≤ V) (R : Rat) (hR : 1 ≤ R) :
    (∀ (p w w' : Fin V → Rat), isProbDist p → (∀ i, 0 < w i) → (∀ i, 0 < w' i) →
      (∀ i, w i ≤ R * w' i ∧ w' i ≤ R * w i) →
      (alpha1 p (softmaxRat w) - alpha1 p (softmaxRat w')).abs ≤ (R - 1) / (R + 1)) ∧
    (∃ (p w w' : Fin V → Rat), isProbDist p ∧ (∀ i, 0 < w i) ∧ (∀ i, 0 < w' i) ∧
      (∀ i, w i ≤ R * w' i ∧ w' i ≤ R * w i) ∧
      alpha1 p (softmaxRat w) - alpha1 p (softmaxRat w') = (R - 1) / (R + 1)) := by
  sorry

/-- Theorem 4 (Exact Correlated Multi-Draft `K ≥ 2` Quantized-Draft Acceptance Loss Law):
    For ALL `K ≥ 2`, `V ≥ 2`, `R ≥ 1`, probability distribution `p`, and positive draft weights
    `w, w'` satisfying `w_i ≤ R * w'_i` and `w'_i ≤ R * w_i`:
    `alphaCorr K p (softmaxRat w) - alphaCorr K p (softmaxRat w') ≤ (K - 1) * (R^2 - 1) / (1 + (K - 1) * R^2)`,
    attained with exact equality for every `K ≥ 2`, `V ≥ 2`, `R ≥ 1`. -/
theorem quantized_draft_loss_multidraft_exact (K : Nat) (hK : 2 ≤ K) (V : Nat) (hV : 2 ≤ V)
    (R : Rat) (hR : 1 ≤ R) :
    (∀ (p w w' : Fin V → Rat), isProbDist p → (∀ i, 0 < w i) → (∀ i, 0 < w' i) →
      (∀ i, w i ≤ R * w' i ∧ w' i ≤ R * w i) →
      alphaCorr K p (softmaxRat w) - alphaCorr K p (softmaxRat w') ≤
        (((K : Rat) - 1) * (R * R - 1)) / (1 + ((K : Rat) - 1) * (R * R))) ∧
    (∃ (p w w' : Fin V → Rat), isProbDist p ∧ (∀ i, 0 < w i) ∧ (∀ i, 0 < w' i) ∧
      (∀ i, w i ≤ R * w' i ∧ w' i ≤ R * w i) ∧
      alphaCorr K p (softmaxRat w) - alphaCorr K p (softmaxRat w') =
        (((K : Rat) - 1) * (R * R - 1)) / (1 + ((K : Rat) - 1) * (R * R))) := by
  sorry

/-- Theorem 5 (Unconditional Bit-Exact Modular `BitVec b` Reversible Transformer Invertibility):
    For ALL bit-widths `b`, ALL depths `L`, ALL layer maps `F, G`, and ALL states `s`:
    `revPass L F G (fwdPass L F G s) = s` and `fwdPass L F G (revPass L F G s) = s`
    bit-for-bit identically through arbitrary `2^b` wrap-arounds. -/
theorem modular_bitvec_reversible_exact_inverse (b L : Nat)
    (F G : Fin L → BitVec b → BitVec b) (s : BitVec b × BitVec b) :
    revPass L F G (fwdPass L F G s) = s ∧ fwdPass L F G (revPass L F G s) = s := by
  sorry

/-- Theorem 6 (Symplectic Unimodularity & Hyperbolic Exponential Drift of the rational `2 × 2` matrix `M(γ)`, the linearised coupling of a reversible block; no floating-point semantics are formalised):
    For ALL `γ : Rat` and ALL `n : Nat`, `M(γ) = [[1 + γ^2, γ], [γ, 1]]` has exact determinant `1`,
    every power `M(γ)^n` has determinant `1`, trace `2 + γ^2 > 2` for `γ ≠ 0`, `(M(γ)^n)_{0,0} ≥ 1 + n * γ^2`,
    and exponential `ℓ_∞` row-sum growth `(M(γ)^n)_{0,0} + (M(γ)^n)_{0,1} ≥ (1 + γ)^n` for `0 ≤ γ`. -/
theorem symplectic_float_reversible_unimodular (γ : Rat) (n : Nat) :
    mat2Det (symplecticM γ) = 1 ∧
    mat2Det (mat2Pow (symplecticM γ) n) = 1 ∧
    mat2Trace (symplecticM γ) = 2 + γ * γ ∧
    (γ ≠ 0 → 2 < mat2Trace (symplecticM γ)) ∧
    1 + (n : Rat) * (γ * γ) ≤ (mat2Pow (symplecticM γ) n).a00 ∧
    (0 ≤ γ → ratPow (1 + γ) n ≤ (mat2Pow (symplecticM γ) n).a00 + (mat2Pow (symplecticM γ) n).a01) := by
  sorry

end SpecDecodingOtChallenge
