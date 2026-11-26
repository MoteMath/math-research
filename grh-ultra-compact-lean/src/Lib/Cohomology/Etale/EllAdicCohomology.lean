import Lib.PadicComparison.Crystalline.PeriodLifting
noncomputable section
open CategoryTheory AlgebraicGeometry CommRingCat LocallyConstant WittVector Function AddCommGrpCat TensorProduct Pi
variable {ℓ} [ThePrime ℓ] {n : ℕ} (R : CommRingCat) (Ω) [CommRing Ω] [Algebra R Ω] (Γ) [Group Γ] [MulSemiringAction Γ Ω] [SMulCommClass Γ R Ω]
abbrev ellAdicCoeff := moduleCoeff (asModules ((testIncl ⋙ locConstAlg) ⋙ wittFunctor ℤ_[ℓ]))
def ellAdicPull n {M N} := AddMonoidHom.mk' (fun α : M ⟶ N ↦ (H.mapₗ ℤ_[ℓ] ellAdicCoeff α n).baseChange ℚ_[ℓ]) (by aesop (add simp [H.mapₗ, H.map, Abelian.Ext.mk₀_add, tmul_add]))
attribute [local simp] ellAdicPull H.mapₗ H.map_comp
lemma ellAdicPull.comp {M N K} α β x : @ellAdicPull ℓ _ n M N α (@ellAdicPull ℓ _ n N K β x) = ellAdicPull n (α ≫ β) x := by induction x <;> simp_all
def geomPoints : Over (Spec R) ⥤ PointFunctor := .mk (pointsToBase ·.hom |> baseChangeOf <| ofHom (algebraMap R Ω)) fun f ↦ {app _ := ↾fun x ↦ ⟨(⟨x.1.1.1 ≫ f.1⟩, _), .trans congr(⟨Spec.preimage $(by simp)⟩) x.2⟩}
def ellAdicCohom n := (geomPoints R Ω).op ⋙ .mk _ fun u ↦ ModuleCat.ofHom (ellAdicPull n (freeAb.map (mapOnTests u.unop)))
def ellAdicCohom.galoisAction X n : Representation ℚ_[ℓ] Γ (ellAdicCohom R Ω n ⟨X⟩) := .comp ⟨⟨fun g : Ω ≃ₐ[R] Ω ↦ ellAdicPull n (freeAb.map (mapOnTests (baseChangeTransition _ (ofHom g) (by aesop)))), congr($((ellAdicCohom ..).map_id _).1)⟩, by intros; ext; erw [ellAdicPull.comp, ← freeAb.4]; rfl⟩ (MulSemiringAction.toAlgAut ..)
lemma ellAdicCohom.map_galoisAction {X Y} (f : X ⟶ Y) (g : Γ) x : (ellAdicCohom R Ω n).map f.op ((galoisAction ..) g x) = (galoisAction ..) g ((ellAdicCohom ..).map f.op x) := by (repeat erw [ellAdicPull.comp, ← freeAb.4]); rfl
lemma exists_ellAdicCoeff_modShortExact_pow k : ∃ q : ellAdicCoeff ⟶ locConstCoeff ⟨TruncatedWittVector ℓ k (ZMod ℓ)⟩, ModShortExact ↑(ℓ ^ k) q := ⟨_, modShortExact_of_isReductionMod (q := {app _ := ofHom (.mk' _ (LocallyConstant.ext fun a ↦ ((truncate k).comp (map (evalRingHom a))).map_add · ·))}) fun A ↦ (witt_reduction_spec (ZMod ℓ) (locConstAlg _)).2.imp (·.1.pow _) fun v ↦ ⟨(truncate_surjective _ _ _ ·.flip |>.imp fun _ ↦ congrArg unflip), fun x ↦ .trans (by erw [← mem_ker_truncate, ← sub_zero x, map_sub, sub_eq_zero, sub_zero]; exact
  (LeftInverse.injective flip_unflip).eq_iff) (v.2 ..)⟩⟩
lemma ellMod : ∃ q : ellAdicCoeff ⟶ locConstCoeff ⟨ZMod ℓ⟩, ModShortExact ↑ℓ q ∧ ∀ N n, IsDerivedComplete (ℓ : ℤ_[ℓ]) (H N ellAdicCoeff n) := have w A := witt_reduction_spec (ZMod ℓ) (locConstAlg _)
  ⟨_, modShortExact_of_isReductionMod (q := {app _ := ofHom constantCoeff.toAddMonoidHom}) (⟨w · |>.2.1.1, (w _).1⟩), .cohomology (IsCompleteTorsionFree.isDerivedComplete (B := wittFunctor _ _) <| w · |>.2.1)⟩
lemma finite_H_ellAdicCoeff {N} (_ : Finite (H N (locConstCoeff ⟨ZMod ℓ⟩) n)) : Module.Finite ℤ_[ℓ] (H N ellAdicCoeff n) := ellMod.elim fun c ⟨k, d⟩ ↦ let q := H.push N c _; .of_surjective ((basisFun ..).constr ℕ (invFun q))
    ((d ..).exists_eq_of_approx (.of_isAdicComplete (PadicInt.maximalIdeal_eq_span_p.rec {})) _ _ fun x ↦ ⟨(basisFun ..) (q x), (k.exists_smul_eq_of_push_eq_zero _ (q.sub_mem_ker_iff.2 (invFun_eq ⟨x, rfl⟩).symm)).imp (by simp_all [-basisFun_apply])⟩)
lemma IsCohomEquiv.bijective_ellAdicPull {M N α} (h : IsCohomEquiv (locConstCoeff ⟨ZMod ℓ⟩) α) : Bijective (@ellAdicPull ℓ _ n M N α) := ellMod.elim fun _ ⟨e, d⟩ ↦ map_bijective (f := 1) bijective_id ((h.bij.of_mod (β := 𝟙 (𝟭 _ ⋙ _)) e e rfl (by tauto) (d _)).eqv _)
