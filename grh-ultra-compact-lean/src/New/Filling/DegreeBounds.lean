import New.Seesaw.BesselGeneric
attribute [-simp] Fintype.card_pi
open Space Fintype Matrix Grading ProbabilityTheory
lemma Data.exists_last_stage_map {P} (D : Data P) {M} e : ∃ R : D.Stage M →ₗ[ℂ] _,(∀ {ϑ Ψ y} {φ : D.Column},liftChainY ϑ M y=R (chainComb ϑ Ψ D.translateDatum M φ) → ι ϑ y=Bμ ϑ Ψ φ)∧∀ t,∃ C,∀ x {ψ} {F : _ → ℂ},(∀ k,F ((D.lastGrading e).inclX k)=algFormCoeff 1 t ψ (.blockEmb (e := .refl _) Sum.elim_one_one.symm (k,1)))→(D.lastGrading e).ratBessel.qms[F * star x.1]=C * inner ℂ x (R ψ):=by
  obtain ⟨rfl,⟨s⟩,w⟩:=e,D.isStd_spaceY,D.isHCParam_Y
  refine ⟨_ ∘ₗ D.restrictToY,(toAlgForm _ w).eq_symm_apply.1,fun t↦(integral_algFormCoeff_blockEmb _ ?_ D.branching.2.2.2 t _).imp' (· * card _ * ∏ τ,_) fun C H x
    ψ F e↦have k:=ofAlgForm_toAlgForm w x ▸
      star_ofAlgForm s;congr(∫ g, $((mul_comm ..).trans (congrArg _ ?_)) ∂$(?_)).trans
      ((H ψ _ 1 _ (Kf ..) x.2.conj.1 k).trans (congr(_ * $(integral_mul_eq_classIntegral w (Kf ..) x.2.conj.1 _ k)).trans (by simp [restrictToY];field_simp [Finset.prod_ne_zero_iff];rfl)).symm)⟩
  any_goals convert e (.reindex D.lastIndexEquiv (s▸rfl) g) <;> [apply (D.spaceY _).isEmbedding_ratCoordMatrix.2;apply G.ext_mat]
  repeat simp [inf_eq_left.2,LE.le,mem_besselGroup_iff,← ext_iff,lastGrading,G.blockEmb,↓ratCoordMatrix_inclX,ratCoordMatrix_eq, *]
