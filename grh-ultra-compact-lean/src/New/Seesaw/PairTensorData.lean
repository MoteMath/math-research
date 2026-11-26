import New.Exchange.SquareLawFourier
import Lib.GLn.Dual.DualWeights
import New.Seesaw.GradingsOfY
import New.Columns.ChainValuation
import New.Exchange.GridModuli
noncomputable section
open Matrix Finset Fintype PolyRep Space Real
variable {E n n'} [Field E] [CMType E] [Fintype n] [Fintype n'] {κ κ' e e'}
attribute [local grind] hcParameter diagramWeight_apply Ioo_eq_empty
lemma exists_branching_pairing [Nonempty n] {l l' s t r} {σ : _ ⊕ Unit ≃ n'} (hσ : (s ⊕ᵥ r) ∘ σ.symm = t) (ht : t = 1) (h : IsHCParam κ e l') (h' : IsHCParam κ' e' (-l)) (hi : ∀ w x, (#{j | x < l' w j} - #{i | x < l w i} : ℤ) ∈ Icc 0 1) : ∃ B : Matrix _ _ ℤ, (∃ N : _ → ℤ, (∀ (S R : Type) [CommRing S] [StarRing S] [Field R] [CharZero R] (f : _ → S →+* R) g u v' v, weylRep κ' e' (g.1.map <| f ·) *ᵥ v' ⬝ᵥ B.map (↑) *ᵥ weylRep κ e ((U.block σ (g, u)).1.map <| f ·) *ᵥ v = (∏ τ, (u.1.map (f τ)).det ^ N τ : Rˣ) * v' ⬝ᵥ B.map (↑) *ᵥ v) ∧ (∀ τ, (N τ).natAbs ≤ boxes κ (card n') + (e τ).natAbs) ∧ ∀ M, boxes κ (card n') ≤ M → ∀ v' v, ‖v' ⬝ᵥ B.map (↑) *ᵥ v‖ ≤ ((M ^ M) ^ 3 :) * √(weylNormSq v') * √(weylNormSq v)) ∧ ∀ g, ∃ c, ∀ (V : Space E n s) [V.IsStd]
  (η : AlgForm n _ e') (φ : AlgForm _ _ e) u K [IsLevel K], ∫ x, ofAlgForm (-l) s η x * ofAlgForm l' t φ (G.reindex σ hσ (.sum (x, 1, u)) * (g, 1)) ∂V.quotMeasure = c / stdLevelIndex K * classIntegral stdRatPoints K fun h ↦ η.1 h ⬝ᵥ B.map (↑) *ᵥ φ.1 (U.block σ (h, u)) := by
  obtain ⟨hn, ⟨⟩, κ₀, e₀, k⟩ := by simpa using card_congr σ.symm, (by simp_all [funext_iff, reindex_equiv σ] : (s, r, t) = 1),
    exists_isHCParam_of_hasGap (by simpa using h'.hasGap · 0 |>.neg)
  let d τ q := (hcParameter κ₀ e₀ (card n) τ q - hcParameter κ e (card n') τ q.succ) / 2
  have J w q (o : q.succ ≤ card n) : d w q ∈ Icc 0 ↑(κ w q.succ) := by
    obtain ⟨⟨i, a⟩, ⟨j, _⟩, _, c⟩ := k.exists_decrPosition_eq w o, h.exists_decrPosition_eq w (.trans o hn.ge), h.exists_decrPosition_eq w (o.trans_lt hn.ge)
    rcases a.2.2 (l' w j), c.2.2 (l w i), hi w (l' w j), hi w (l w i); grind -linarith [decrPosition]
  obtain ⟨⟨A, L, hv, -, hA⟩, b, b1, b2, b3⟩ := exists_dual_pairing_of_isHCParam k h', exists_branching_matrix (fun _ ↦ σ) κ₀ 0 e e₀ (funext₂ fun w q ↦ (κ w q).sub_add_min_cancel
    (d w (q - 1)).toNat) (by grind -linarith) nofun (by grind -linarith [card_pos_iff])
  use A * b, ⟨_, by introv _; rw [map_intCast_mul_mulVec, mulVec_mulVec v, b1 _ (g.1.map <| f ·) (f · |> u.1.map |>.det)] <;> simp [map_intCast_mul_mulVec, ← mulVec_mulVec, Units.smul_def, ← ext_iff, PolyRep.blockScalar, reindex_equiv σ]; tauto, fun τ ↦ ?_, fun M m _ _ ↦ ?_⟩, fun g ↦
    (integral_algFormCoeff_blockEmb (stdSpace ..) (by simp) b3 (_ ∘ₗ conjWeylRep κ e g⁻¹) _).imp
    fun _ H V _ η φ _ _ _ ↦ by simpa [algFormCoeff, map_intCast_mul_mulVec, IsStd.eq_stdSpace] using! H φ _ _ _ _ (isAutomorphic_algFormCoeff η) (hv _ _)
  grw [Int.natAbs_add_le, ← FitsRanks.refl.sum_diagramWeight_eq_boxes, ← single_le_sum _ (mem_univ (τ, ⟨0, by omega⟩))] <;> simp; simp [diagramWeight_apply]; bound
  grw [map_intCast_mul_mulVec, (hA _).choose_spec.2, gramForm_apply, le_sqrt_of_sq_le (posDef_cauchy_schwarz weylGram_posDef ..), ← weylNormSq, ← weylNormSq, (hA _).choose_spec.1, b2] <;> simp [field, sqrt_sq_eq_abs]
  grw [← boxes, ← m, ← FitsRanks.refl.sum_diagramWeight_eq_boxes, ← @FitsRanks.sum_diagramWeight_eq_boxes n, sum_le_sum]
  intro (w, q); grind -linarith [J w _ (Nat.sub_one_lt_of_lt _)]; grind
namespace Data
variable {P} {D : Data P} (ϑ : D.MFoldTwist) {z : Bool} {i j a b} (c : Bool) (l : ℕ) (n : Type) [Fintype n]
def gridSpace : ∀ o z i j, Space D.E _ (D.gridSigns z o i j)
  | 0, true, 0, 0 => ((D.spaceY 0).sum (signedSpace ..)).reindex (.refl _) D.gridSigns_zero.symm
  | 0, false, 0, j => D.spaceY j | _ + 1, _, 0, 0 => (gridSpace ..).neg | _, _, _, _ =>
    signedSpace ..
def gridKernel z i j := kernelPair (D.gridParam z 0 i j) (D.gridSigns z 0 i j)
abbrev GridForm z a b := (gridSpace ..).Form (D.gridKernel z a b true)
def gridChar := D.liftChar (bif c then ϑ.pow (l + 1) else .one) (l + 1) * WeilData.upsilonU1 ^ ((Fintype.card n + (!c).toNat) / 2)
abbrev gridTamePart := D.liftTamePart (bif c then ϑ.pow (l + 1) else .one) (l + 1)
abbrev triangleOrder z ϑ n := Fintype.card (GL (D.GridIndex z 0 n) (D.triangleModulus z ϑ).ResRing)
abbrev Node := Bool × ℕ × ℕ
abbrev NodeIndex (p : Node) := D.GridIndex p.1 p.2.1 p.2.2
def nodeLevel p := if !p.1 ∧ p.2.1 = 0 then ⊥ else (GeneralLinearGroup.map (n := D.NodeIndex p) (reduceToTriangle ϑ true)).ker
abbrev levelIndex z a b := ((nodeLevel ϑ (z, a, b)).index : ℂ)
abbrev gridLevelForms i := levelSpace ((gridSpace ..).formRep (D.gridKernel true 0 i true)) (principalLevel _ D.gridLevelGen)
lemma isConjKernelPair_gridKernel (h : i ≤ D.m ∧ j ≤ D.m) : IsConjKernelPair (D.gridKernel z i j) := isConjKernelPair_kernelPair (d := false) (D.hasGap_gridParam · .. |>.mono
  (by grw [gapThreshold, card_gridIndex_le _ h]; simpa using D.le_of_hasLogBound))
instance gridChar_hasWeight : (gridChar ϑ c l n).HasWeight (D.gridWeight c l n)
  (gridTamePart ϑ c l) := D.hasWeight_liftChar.mul_upsilonU1_pow _
lemma isEdgeFamily_grid {I} (ϑ : I → _) d {c l i' j'} (e : (c, l, i', j') = bif d then (z, i, i + 1, j) else (!z, j, i, j + 1)) (hi : i' ≤ D.m := by omega) (hj : j' ≤ D.m := by omega) : IsEdgeFamily
  (fun x ↦ gridChar (ϑ x) c l) (D.gridKernel z i j) (D.gridKernel z i' j') d (D.gridHarmonic 0 d c l ..) := isEdgeFamily_of_paramsCorrespond _ _ (D.paramsCorrespond_grid _ _ _ _ _ e)
lemma gridSpace_diag h : D.gridSpace 0 _ j j =
  ((gridSpace ..).sum (signedSpace ..)).reindex _ (D.gridDiagEquiv_spec h) := by
  cases j; rfl
  exact signedSpace_eq_reindex _
    (Units.ext ((fromBlocks_diagonal ..).trans (by simp; congr with ⟨⟩ <;> rfl)))
lemma gridSpace_subdiag j : ∃ τ h, D.gridSpace 0 true j (j + 1) =
  (D.gridSpace 0 false (j + 1) j).reindex (.symm τ) h := (exists_equiv_of_card_neg (by cases D.t_odd; simp_all [card_gridIndex]; lia) (by
  grind [card_neg_gridSigns])).imp fun _ ↦ (⟨·, by cases j <;> exact signedSpace_eq_reindex _ rfl⟩)
def pointDescent z b : D.GridForm z 0 (b + 1) →ₗ[ℂ] D.GridForm z 0 b := (triangleOrder z ϑ b : ℂ) •
  modDescent _ _ (gridChar ϑ (!z) b) (D.gridHarmonic 0 false (!z) b z 0 b 0 (b + 1))
  (inclusionDatum (triangleModulus z ϑ).ResRing) ..
def iotaPlus z b : D.GridForm z 0 D.m →ₗ[ℂ] D.GridForm z 0 b := if b < D.m then pointDescent ϑ .. ∘ₗ
  iotaPlus .. else Pi.single (M := (D.GridForm .. →ₗ[ℂ] D.GridForm z 0 ·)) _ .id b
variable {ϑ}
def descentMove (y : Matrix (D.GridIndex z a (b + 1)) (D.GridIndex z a b) (gridModulus ϑ).ResRing) :
  D.GridForm z a (b + 1) →ₗ[ℂ] D.GridForm z a b
  := modDescent _ _ (gridChar ϑ (!z) b) (D.gridHarmonic 0 false (!z) b ..) (Pi.single y 1) ..
def liftMove (y : Matrix (D.GridIndex z (a + 1) b) (D.GridIndex z a b) (gridModulus ϑ).ResRing) :
  D.GridForm z a b →ₗ[ℂ] D.GridForm z (a + 1) b
  := modLift _ _ (gridChar ϑ z a) (D.gridHarmonic 0 true z a ..) (Pi.single y 1) ..
lemma gridChar_det {n'} [Fintype n'] s (k : Kf D.E n') : (gridChar ϑ c l n).1 (G.det (s := s) (1, k.1)) = (gridModulus ϑ).charOfTamePart (gridTamePart ϑ c l) ((gridModulus ϑ).reductionK₀
  k).1.det := (gridChar_hasWeight ..).apply_det_eq_charOfTamePart (by
  cases c <;> simp +contextual [places_modulus_eq_union, liftTamePart, TameChar.pow, ϑ.1.1.5]
  tauto) _
lemma levelIndex_eq_untwisted (h : z ∨ a ≠ 0) : levelIndex ϑ z a b =
  Fintype.card (GL (D.GridIndex z a b) (D.gridModulus 1).ResRing) := by
  rw [levelIndex, nodeLevel, ite_eq_right (by lia), Subgroup.index_ker, MonoidHom.range_eq_top.2 (reductionK₀_surjective.forall.2 fun _ ↦ ⟨_, Units.ext Modulus.factor_reductionK₀⟩)]; simp; rfl
variable {P : _} (D : Data P) (ϑ : D.TameChar)
lemma s22_b6 : Ideal.absNorm (.span {D.piGBar}) =
  D.gProd ^ D.f := by simp [span_piGBar, prod_q_chosenPlace]
lemma s22_g5 w : Valued.v (D.chosenIdele.1 w) = Valued.v ((algebraMap _ (Ô _) D.piGBar).1 w) := (Modulus.valued_generator ..).trans ((v_algebraMap_eq_intValuation _).trans (w.intValuation_eq_exp_neg_multiplicity D.piGBar_ne_zero)).symm
lemma k2 {k hk} w : Valued.v (((D.q6 k hk).c : 𝔸f _) w) =
  Valued.v ((D.ideleA * star D.ideleA.1) w) :=
  have := congr($(@id (D.ideleA.1 * _ = _) (divp_mul_cancel ..) ▸ WeilData.self_dual w) * $(w.intValuation_eq_exp_neg_multiplicity (ne_zero_of_differentIdeal_eq_span Parameters.different_eq_span_varpi)))
  eq_of_inv_mul_eq_one (by simp [q6, ← (congr($D.piGBar_mul_star) : _ = (D.gProd : D.E)), s22_g5, Parameters.different_eq_span_varpi, ← v_algebraMap_eq_intValuation, v_algebraMap_eq_valuation, WithZero.exp_neg, -WithZero.inv_exp] at *; grind)
lemma z4 k hk : (q6 k hk).Q0 D.ideleA D.piIdele
  (D.latticeScale k) := by grind [Grading.Q0, q6, spaceY]
lemma chosenLevel_inf_trivialOn_le {n} [Fintype n] : chosenLevel ⊓ Gf.trivialOn n ϑ.Q ≤ levelOf (D.levelPlaces ϑ).placeAt ⊥ := fun _ ⟨h, k⟩ ↦ mem_levelOf.2 ⟨_, funext (Sum.rec (congrFun (mem_levelOf.1 h).2) (Kf.reduceAt_eq_one_of_atPlace <| Gf.mem_trivialOn.1 k _ ·.2))⟩
end Data
def Data.n3 {P} (D : Data P) t := TensorChain.pure (D.pairTranslates (D.translateDatum t)) (D.ϱ + 1)
