import New.Selmer.FitTwists
import New.Rows.LineCoordinates
variable {E r n} [Field E] [CMType E] [Fintype r] [Fintype n] {O : AuxPair E r n} {w} (hw : _ ≠ w) (hS : w ∉ O.places.conjClosure) {P} (D : Data P) (j : D.LiftIndex) {c : ℕ} [NeZero c] (ϑ : D.MFoldTwist)
lemma LValueData.fitsParams_auxPair (X : LValueData E n) : X.auxPair.FitsParams 0 := by
  refine' .mk (fun w ↦ ⟨X.auxPair.isHCParam_paramV.hasGap .., .mk .., _, fun _ ↦ .inl ((X.auxPair.isHCParam_paramV.exists_decrPosition_eq w X.one_lt_card.le).imp _)⟩) .. <;> simp [AuxPair.paramV, hcParameter, diagramWeight_apply, AuxPair.detExp, IsMatchedPair, pairSign, Function.Injective] <;> grind [X.one_lt_card]
lemma AuxPair.heckePolyOnForms_testValue_eq_zero [WeilData E] {y z} (h : O.Lifts y z) : O.heckePolyOnForms hw hS (O.testValue w) y = 0 := by
  cases Nat.exists_eq_add_of_lt O.rank_lt
  simp [O.heckePolyOnForms_eq_smul _ _ (h w hw hS), testValue, rankDiff, *, Finset.prod_range_succ, add_assoc, field, AutChar.frobValue, HeckeChar.atUnif]
namespace Data
noncomputable abbrev nStar := D.f * (2 * D.t ^ 3)
lemma nStar_bounds : 2 * D.r ≤ D.b ∧ 300 * nStar D + D.t ≤ D.h₂ ∧ 0 < nStar D := ⟨D.le_of_hasLogBound, D.nat_le_of_hasLogBound, D.nat_le_of_hasLogBound⟩
variable {D}
noncomputable def orderW c := ite (D.signsW j c = 1) (-1 - (untwistedAuxPair j).ord c : ℤ) ((untwistedAuxPair j).ord c)
noncomputable abbrev conjHolWeight τ := (toHCParam (D.signsW j) (-D.paramW τ)).lowestKType
noncomputable def kernelWeight τ := staircaseWeight D.SmallIndex (D.signsW j)
  (untwistedAuxPair j).ord (Pi.single (-1) ((untwistedAuxPair j).colsMinus τ)) (-(D.m / 2 - j))
attribute [local grind .] card_rowIndex auxPair orderW signsW rowParameter Fintype.card_fin Fintype.card_sum units_ne_neg_self
attribute [local simp] kernelWeight paramW_lt_iff vacuumWeight staircaseWeight
lemma rank_bounds_card_bigIndex : 6 * D.r ≤ D.n D.m ∧ 100 * D.m + 9 < D.k ∧ D.r + 1 = D.k + D.m ∧ D.t = 5 * D.r ∧ Fintype.card D.RowIndex = D.r ∧ Fintype.card (BigIndex j) = D.r + 9 * D.m + 1 := ⟨D.nat_le_of_hasLogBound, D.nat_lt_of_hasLogBound, by grind⟩
lemma two_mul_card_detIndex_add_le τ : (2 * (Fintype.card (DetIndex j τ) + Fintype.card (BigIndex j) + D.m) : ℕ) ≤ 5 * D.b := by
  grw [(?_ : _ + D.m ≤ D.w j τ)] <;> grind [card_detIndex_add_bigCharExp, w_le_two_mul_b]
@[local simp↓] lemma conjHolWeight_eq_add_kernelWeight τ : conjHolWeight j τ = staircaseWeight
  (BigIndex j) (D.signsW j) (untwistedAuxPair j).ord (Pi.single 1 ((untwistedAuxPair j).colsPlus τ))
  (-(bigCharExp j + -D.w j τ)) + kernelWeight j τ := by
  ext c; erw [conjHolWeight, eq_comm, (D.fitsParams_auxPair .one j).exists_isJointHarmonic.choose_spec.2.2]
  cases Int.units_eq_one_or (D.signsW j c) <;> simp [*, -Fintype.card_sum, auxPair] <;>
    rw [Finset.sum_subset (s₂ := .Ioo ((untwistedAuxPair j).ord c) (6 * D.r))] <;> grind
lemma conjHolWeight_kernelWeight_bounds τ : let s := D.signsW j; let k := conjHolWeight j τ; (∀ i,
      |↑(k i)| ≤ 5 * D.b) ∧ IsKDominant s (orderW j) k ∧ IsKDominant s (orderW j) (kernelWeight j
      τ) ∧ HasHolGap s k (300 * nStar D) ∧ HasHolGap s (kernelWeight j τ) (300 * nStar D) := by
  and_intros <;> repeat intro
  grw [← Int.cast_abs, abs_lowestKType_le (D.hasGap_paramW _ τ).neg (L := 2 * D.w (D.m + 1) τ) (by grind [Pi.neg_apply, paramW]), card_rowIndex]; simp; grind [nStar_bounds, w_le_two_mul_b]
  iterate 2 cases Int.units_eq_one_or (D.signsW j ‹_›) <;> simp_all
    [orderW, -tsub_le_iff_right] <;> gcongr
  all_goals simp [*, -Nat.cast_sum]; grw [← Finset.single_le_sum (f := (untwistedAuxPair j).colsMinus τ) (a := D.m - j)] <;> grind [-Sum, Int.ofNat_le.2 D.nStar_bounds.2.1]
variable {j}
lemma isPosFirstOrder_orderW : IsPosFirstOrder (D.signsW j) (orderW j) := by grind [IsPosFirstOrder, Function.Injective, D.basisNumber.injective]
lemma paramW_lt_of_orderW_lt τ a b : D.signsW j a = D.signsW j b → orderW j a < orderW j b → D.paramW τ a < D.paramW τ b := by simp; grind
instance instFactNeRingOfIntegersEHPowGbOfNat (c) : Fact (D.piGBar ^ c ≠ 0) := ⟨by simp⟩
lemma places_modulus_eq_union ϑ : (D.𝔪 ϑ c).places = {w | D.IsChosen w} ∪ ϑ.Q := by simp [places_levelModulus, levelPlaces, range_chosen]
lemma isTameFor_of_hasWeight {ν γ ψ} (ϑ : D.Twist) (H : ν.HasWeight γ (ψ * ϑ.ψ)) (b : ∀ w, ψ w ≠ 1 ↔ D.IsChosen w) : IsTameFor (D.𝔪 ϑ c) ν γ (Modulus.charOfTamePart _ (ψ * ϑ.ψ)) := ⟨nonempty_modulus_places, _, H, by grind [places_modulus_eq_union, Pi.mul_def, Twist, TameChar, IsChosen, → levelNorm_mem_and_notMem_of_mem_Q], rfl⟩
lemma isTameFor_twistedChi j (ϑ : D.Twist) : IsTameFor (D.𝔪 ϑ c) (twistedChi ϑ j) 0 (Modulus.charOfTamePart _ (D.liftTamePart ϑ j)) := isTameFor_of_hasWeight _ (twistedChi_hasWeight ..) (omega_zpow_ne_one j (by grind))
instance instNeZeroNatB₁ : NeZero D.b₁ := .of_pos D.nat_le_of_hasLogBound
noncomputable abbrev gridLevelGen := D.piGBar ^ D.b₁
noncomputable abbrev gridModulus := D.𝔪 ϑ D.b₁
lemma gridModulus_one_ideal : (gridModulus 1).ideal = .span {D.gridLevelGen} := D.ideal_untwistedModulus_eq_span ▸ by rfl'
noncomputable abbrev triangleModulus z (ϑ : D.MFoldTwist) := D.𝔪 (cond z 1 ϑ :) (cond z D.b₁ 1)
noncomputable abbrev reduceToTriangle z := Ideal.Quotient.factor
    (z.rec (Ideal.mul_mono_left (Ideal.pow_le_pow_right NeZero.one_le)) (Ideal.mul_mono_right (by with_unfolding_all use Ideal.le_of_dvd (one_dvd _))) : (gridModulus ϑ).ideal ≤ (triangleModulus z ϑ).ideal)
lemma piGBar_dvd_gridLevelGen : D.piGBar ∣ gridLevelGen := by simp [NeZero.ne]
