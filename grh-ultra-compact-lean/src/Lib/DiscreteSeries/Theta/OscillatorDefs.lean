import Lib.DiscreteSeries.FlenstedJensen.RepresentationDefs
noncomputable section
open Matrix Fintype MvPolynomial Sgn Finset GlModule
variable {R C ι : Type} [Fintype R] [Fintype C] [Fintype ι] (σ : ℤˣ) (ε : R → ℤˣ) (ε' : C → ℤˣ)
omit [Fintype R] in
lemma canonical_commutation η (a b : R) P : raiseOp η a (raiseOp η b P) = raiseOp η b (raiseOp η a P) ∧ lowerOp η a (lowerOp η b P) = lowerOp η b (lowerOp η a P) ∧ lowerOp η a (raiseOp η b P) = raiseOp η b (lowerOp η a P) + ite (a = b) P 0 := by aesop (add simp [raiseOp, lowerOp, _root_.pderiv_comm, mul_left_comm])
def pairSign i := σ * ε (Prod.fst i) * ε' i.2
structure FockDualPair (ε : R → ℤˣ) (ε' : C → ℤˣ) ι where (σ : ℤˣ) (γ γ' : ℤ) (varEquiv : R × C ≃ ι)
abbrev FockDualPair.std γ γ' := (⟨1, γ, γ' + card R, .refl _⟩ : FockDualPair ε ε' _)
variable {ε ε'} (T : FockDualPair ε ε' ι) (l : HCParam ε) (l' : HCParam ε') (Φ : MvPolynomial ι ℂ)
namespace FockDualPair
abbrev swap : FockDualPair ε' ε ι := ⟨-T.σ, T.γ', T.γ, .trans (.prodComm ..) T.varEquiv⟩
omit [Fintype R] [Fintype C] [Fintype ι] in
lemma sw2 : T.swap.swap = T := by simp [swap]; rfl
abbrev varSign := pairSign T.σ ε ε'
@[simp] abbrev η := T.varSign ∘ T.varEquiv.symm
def vacuumWeight s := T.γ - #{c | T.σ * s * ε' c ≠ 1}
abbrev rWt r := l.lowestKType r - T.vacuumWeight (ε r)
@[simp] abbrev centredParam r := l r - 2 * T.γ + card C
attribute [local simp] add_mul mul_add ite_and mul_assoc glOp single_apply
def oscRows : GlModule R (MvPolynomial ι ℂ) := let U a b := ((if ε a = ε b then 1 else T.σ : ℂ) • ∑ c, glOp T.η (T.varEquiv (a, c)) (T.varEquiv (b, c)) + if a = b then ↑T.γ else 0)
 .mk (liftLinear ℂ (.smulRight .id <| U · ·)) (by
  repeat intro; induction ‹_› using Matrix.induction_on' <;> simp_all [add_sub_add_comm]
  simp [liftLinear_apply, mul_apply, mul_comm]
  simp [U, canonical_commutation, apply_ite (raiseOp ..), -ite_smul, DFunLike.ext_iff, -zsmul_eq_mul, ← ite_zero_smul, ite_add_zero, ← smul_sum]
  intro; rw [sum_comm]; match_scalars <;> norm_cast <;> aesop)
def fLap a b := ∑ c with T.varSign (a, c) = -1, glOp T.η (T.varEquiv (a, c)) (T.varEquiv (b, c))
def polR a b s := ∑ c with T.varSign (b, c) = s, X (T.varEquiv (a, c)) * Φ.pderiv (T.varEquiv (b, c))
abbrev IsMatchedPair r c := T.centredParam l r = -T.swap.centredParam l' c ∧
 |(card R - card C : ℤ)| < T.varSign (r, c) * T.centredParam l r
def IsHarmonic := ∀ a b c, ε a ≠ ε b → (Φ.pderiv (T.varEquiv (b, c))).pderiv (T.varEquiv (a, c)) = 0
def IRH := ∀ a b, ε a ≠ ε b → T.fLap a b Φ = 0
def IsPreJointHarmonic := Φ ≠ 0 ∧ T.swap.oscRows.IsCompactPrimitive l' Φ ∧ T.IRH Φ ∧ l.IsKHighest T.oscRows l.lowestKType Φ ∧ T.swap.IRH Φ
def IsJointHighest ν ν' := Φ ≠ 0 ∧ l'.IsKHighest T.swap.oscRows ν' Φ ∧ T.IsHarmonic Φ ∧ l.IsKHighest T.oscRows ν Φ ∧ T.swap.IsHarmonic Φ
omit [Fintype ι] in
lemma swap_oscRows_E a b : T.swap.oscRows.E a b = (ite (ε' a = ε' b) 1 T.σ : ℂ) • -∑ r, lowerOp T.η (T.varEquiv (r, a)) * raiseOp T.η (T.varEquiv (r, b)) + ite (a = b) ↑T.γ' 0 := by simp [oscRows, E, smul_sum, ← sum_neg_distrib, raiseOp, lowerOp, pairSign, mul_right_comm T.σ]; congr; aesop
end FockDualPair
export FockDualPair (vacuumWeight oscRows fLap polR IsMatchedPair IsHarmonic swap_oscRows_E)
structure IsMatch where
 gap : l.HasGap (500 * (card R + card C) ^ 3)
 gap' : l'.HasGap (500 * (card C + card R) ^ 3)
 left r : (∃ c, T.IsMatchedPair l l' r c) ∨ |T.centredParam l r| < card R - card C
 right c : (∃ r, T.IsMatchedPair l l' r c) ∨ |T.swap.centredParam l' c| < card C - card R
structure IsJointHarmonic extends IsMatch T l l' where
 isJointHighest : T.IsJointHighest l l' Φ l.lowestKType l'.lowestKType
