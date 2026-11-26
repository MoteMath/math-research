import Lib.General.Groups.IrreducibleCharacters
import Lib.General.LinearAlgebra.ValuedMatrix
noncomputable section
open Submodule ComplexConjugate Fint Fintype Function LinearEquiv LinearMap Module MonoidAlgebra Polynomial Quot QuotientAddGroup Ring LinearMap.BilinForm
variable (k) [Field k]
def SimClass := Quot fun a b : Σ n, End k (Fin n → k) ↦ ∃ e : _ ≃ₗ[k] _, e.conj a.2 = b.2
@[implicit_reducible] def Hall := SimClass k → ℂ deriving AddCommGroup, Module ℂ, TopologicalSpace, T2Space, IsTopologicalAddGroup
variable {k} {V} [AddCommGroup V] [Module k V] [Module.Finite k V] (g : Module.End k V) (c : SimClass k)
def simClassOf : SimClass k := .mk _ ⟨_, (finBasis ..).equivFun.conj g⟩
@[simp] lemma q7 : simClassOf c.out.2 = c := (Quot.sound ⟨_, rfl⟩).symm.trans c.out_eq
abbrev StableSubspace := {W : Submodule k V // ∀ x ∈ W, g x ∈ W}
def StableSubspace.q3 {g : End k V} (W : StableSubspace g) : End k W := g.restrict W.2
def StableSubspace.q5 {g : End k V} (W : StableSubspace g) := W.1.mapQ _ g W.2
abbrev SimClass.dim := c.out.1
def SimClass.charpoly : SimClass k → Polynomial k :=
  Quot.lift (·.2.charpoly) fun _ _ ⟨_, h⟩ ↦ by simp [← h]
instance : Mul (Hall k) := ⟨fun f h ↦ (∑ᶠ W : StableSubspace ·.out.2, f (simClassOf W.q3) * h (simClassOf W.q5))⟩
@[simp] def Hall.constOne : Hall k := fun _ ↦ 1
@[simp] def Hall.rankPart (n : ℕ) (F : Hall k) : Hall k := fun c ↦ ite (c.dim = n) (F c) 0
instance : One (Hall k) := ⟨.rankPart 0 .constOne⟩
def Hall.evalGL (F : Hall k) {n} [Fintype n] (g : GL n k) := F (simClassOf g.1.toLin')
variable {k V V' : Type*} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V] [AddCommGroup V'] [Module k V'] [Module.Finite k V'] {g : Module.End k V} {g' : End k V'} (e : V ≃ₗ[k] V') (g₁ : End k V) {f h : Hall k} (c : SimClass k) (p : V →ₗ[k] _) (hp : ∀ x, p (g x) = g' (p x))
lemma s11_v3 : simClassOf g = simClassOf g' ↔ ∃ e : V ≃ₗ[k] _, ∀ x, e (g x) = g' (e x) := by
  delta simClassOf; generalize (finBasis k V).equivFun = a, (finBasis k V').equivFun = b
  refine (Equivalence.quot_mk_eq_iff ⟨fun _ ↦ ⟨1, rfl⟩, .imp' .symm ?_, fun ⟨e, _⟩ ↦ .imp' e.trans
   ?_⟩ ..).trans ⟨.imp' (a ≪≫ₗ · ≪≫ₗ b.symm) ?_, .imp' (a.symm ≪≫ₗ · ≪≫ₗ b) ?_⟩ <;>
  simp_all [DFunLike.ext_iff] <;> grind [symm_apply_eq]
lemma s11_q1 (h : ∀ x, e (g x) = g' (e x) := by aesop) : simClassOf g =
  simClassOf g' := s11_v3.2 ⟨e, h⟩
lemma s11_w5 : ∃ e : _ ≃ₗ[k] V, ∀ x, e ((simClassOf g₁).out.2 x) = g₁ (e x) := s11_v3.1 (q7 _)
@[simp] lemma s11_r3 : (simClassOf g).dim = finrank k V := by simp [← (s11_w5 g).choose.finrank_eq]
@[simp] lemma s11_p7 : (simClassOf g).charpoly = g.charpoly := charpoly_conj ..
@[ext] lemma Hall.ext (H : ∀ n (g : End _ (Fin n → k)), f (simClassOf g) = h (simClassOf g)) : f = h := funext (q7 · ▸ H ..)
lemma Hall.j0 {m n} (F : ∀ c, c.dim < m → f c = 0) (H : ∀ c, c.dim < n → h c = 0) c (e : c.dim < m + n) : (f * h) c = 0 := finsum_eq_zero_of_forall_eq_zero fun W ↦ by grind [W.1.finrank_quotient_add_finrank, q7 c, s11_r3]
@[simp] lemma Hall.add_apply : (f + h) c = f c + h c := rfl
@[simp] lemma Hall.zero_apply : (0 : Hall k) c = 0 := rfl
@[simp] lemma Hall.neg_apply : (-f) c = -f c := rfl
@[simp] lemma Hall.smul_apply a c : (a • f) c = a * f c := rfl
@[simp] lemma Hall.one_apply : (1 : Hall k) c = if c.dim = 0 then 1 else 0 := rfl
abbrev s11_z4 (a : End k V) (b : End k V') x := (b.prod x).coprod (.prod 0 a)
instance fintypeStableSubspace [Finite k] : Fintype (StableSubspace g) := have := @finite_of_finite k V; .ofFinite _
instance fintypeLinearHom [Finite k] : Fintype (V →ₗ[k] V') := @.ofFinite _ (finite_of_finite k)
private lemma z2 (hp : ∀ x, p (g x) = g' (p x)) (W : StableSubspace g) (s : Surjective p) (h : W = p.ker) : simClassOf W.q5 = simClassOf g' := s11_q1 (quotEquivOfEq _ _ h ≪≫ₗ p.quotKerEquivOfSurjective s) (ind hp)
private lemma y8 (hp : ∀ x, p (g x) = g' (p x)) {U : StableSubspace g'} (i : Injective p) (h : p.range = U) : simClassOf U.q3 = simClassOf g := (s11_q1 (LinearEquiv.ofInjective p i ≪≫ₗ ofEq ..)).symm
def StableSubspace.comap (U : StableSubspace g') : StableSubspace g := ⟨.comap p U, by aesop⟩
variable {f h : Hall k} (n) (F : Hall k) (H : Hall k)
@[simp] lemma p1 (i : p.ker = ⊥) (U : StableSubspace g') (h : U ≤ p.range) : simClassOf (StableSubspace.comap p hp U).q3 = simClassOf U.q3 :=
  s11_q1 (comap_equiv_self_of_inj_of_le (ker_eq_bot.1 i) h) (by bound)
variable [Finite k]
lemma StableSubspace.j6 (F : _ → ℂ) : ∑ W with p.ker ≤ W.1, F W = ∑ W with W.1 ≤ p.range, F (comap p hp W) := by apply Finset.sum_nbij' (⟨.map p ·, by aesop⟩) (comap p _) <;>
  simp_all [comap, comap_map_eq, map_comap_eq, map_le_range]
section
attribute [local simp] Finset.mul_sum Finset.sum_filter Finset.sum_mul injective_id range_eq_top finrank_zero_iff mkQ_surjective range_dualMap_mkQ_eq subsingleton_iff_eq_bot Subspace.dualCoannihilator_dualAnnihilator_eq Subtype.coe_eq_iff add_mul mul_add
omit [Finite k] in
@[simp] private lemma r9 (s : p.range = ⊤) U : simClassOf (StableSubspace.comap p hp U).q5 = simClassOf U.q5 := by apply z2 (mkQ _ ∘ₗ p) <;> aesop
@[local simp] lemma Hall.w2 : (f * h) (simClassOf g) = ∑ᶠ W : StableSubspace g, f (simClassOf W.q3) * h (simClassOf W.q5) := by simp [HMul.hMul, Mul.mul, by simpa using StableSubspace.j6 _ (s11_w5 g).choose_spec]
lemma s11_y5 : simClassOf g = simClassOf g.dualMap := let ⟨_, _, _, _, _, ⟨e⟩⟩ :=
   (equiv_directSum_of_isTorsion (AEval.isTorsion_of_finiteDimensional k V g))
  let E := AEval'.of g ≪≫ₗ (e ≪≫ₗ DFinsupp.linearEquivFunOnFintype).restrictScalars k; have := Finite.pi_iff.1 (.equiv E)
  s11_q1
   (E ≪≫ₗ piCongrRight (fun _ ↦ have L := (@exists_ker_toSpanSingleton_eq_annihilator
    _ _ _ _ _ (compHom _ (R := _ᵈᵐᵃ) (.toOpposite (.id k[X]) .all)) _ _)
   toDual ((mul k _).compr₂ L.choose) (.ofSeparatingLeft (ind fun q h ↦ mul_one q ▸
    (forall_dual_apply_eq_zero_iff ..).1 (congr($(L.choose_spec.le (LinearMap.ext h)) · 1))))) ≪≫ₗ
   lsum ..
   ≪≫ₗ E.dualMap) (by simp [toDual, DFunLike.ext_iff, E, ← AEval'.X_smul_of, -map_smul_of_tower])
instance : CommRing (Hall k) := by
  refine' { mul_assoc := _, .. } <;> intros <;> ext _ g
  any_goals solve | simp [z2 (g' := g) 1 _ ⟨⊥, _⟩ surjective_id rfl, y8 (g := g) .id]
  have (W : StableSubspace g) := And.intro (StableSubspace.j6 (g :=
   W.q3) W.1.subtype (congrFun rfl)) (StableSubspace.j6 (g' :=
   W.q5) W.1.mkQ (by aesop)); simp_all [mul_assoc, Finset.sum_comm]
  congr!; apply z2 ((mkQ _).submoduleComap _) (by tauto) _ (by rintro ⟨⟨⟩⟩; tauto); simp [submoduleComap, ker_restrict]; rfl
  nth_rw 2 [s11_y5]; simp; apply Finset.sum_nbij' (⟨dualAnnihilator ·, by aesop⟩)
   (⟨dualCoannihilator ·, by grind [mem_dualCoannihilator, g.dualMap_apply]⟩) <;> simp_intro W
  rw [s11_y5, mul_comm, s11_y5, y8 W.1.mkQ.dualMap, z2 W.1.subtype.dualMap] <;> aesop
lemma Hall.j7 m : ∀ c, c.dim < m → ((1 - constOne : Hall k) ^ m) c = 0 :=
  m.recAux nofun fun _ ↦ (j0 · (by simp_all [sub_eq_add_neg]))
instance : Algebra ℂ (Hall k) := by apply Algebra.ofModule <;> aesop (add 1% (by ring))
lemma Hall.j4 : IsUnit (constOne : Hall k) := ⟨.mkOfMulEqOne _ _ (@Summable.one_sub_mul_tsum_pow (Hall k) _ _ {continuous_mul := continuous_pi (q7
  · ▸ by simp [-q7]; fun_prop)} _ _ (Pi.summable.2 (.comp_nat_add (k := ·.dim + 1)
  (by simp +arith [j7])))), sub_sub_self ..⟩
end
def Hall.q6 (F : Hall k) : SimClass k → Hall k := (finMean fun x ↦ F <| simClassOf <| s11_z4 ·.out.2 ·.out.2 x)
abbrev Hall.moebius : Hall k := constOne⁻¹ʳ
abbrev Hall.mulMu (F : Hall k) : Hall k := fun c ↦ F c * moebius c
def Hall.IsCuspidal (F : Hall k) := ∀ a b, a.dim ≠ 0 → b.dim ≠ 0 → F.q6 a b = 0
def Hall.q0 := @finMean (End k (Fin n → k))ˣ fun g ↦ conj (F (simClassOf g.1)) * H (simClassOf g.1)
def Hall.q4 : Hall k := (F.q0 n <| H.q6 ·)
variable (k) {K} [Field K] [Algebra k K] (η : K → ℂ)
@[simp] def Hall.brauerLift : Hall k := (·.charpoly.aroots K |>.map η |>.sum)
def Hall.greenCuspidal := (brauerLift k η).mulMu * constOne
lemma IsCentralProj.isChar {G} [Group G] [Finite G] {e : ℂ[G]} (h : IsCentralProj e) : IsChar (Nat.card G * e.coeff ·) := isChar_of_mem_virtualChars
  ((irreducible_criteria_of_isClassFunction _ (by simp [h.2])).2.1 fun _ ↦ (·.star.imp' _ fun ρ e ↦
  .trans (by simp [classInner, finMean, ← congrFun e, asAlgebraHom_eq_sum, FDRep.character, Finset.sum_div, mul_rotate']) (h.1.map (Representation.asAlgebraHom ρ.ρ)).isProj_range.trace))
attribute [local simp] Hall.q6 LinearMap.toMatrix_apply SetLike.ext_iff
variable {k V W : Type*} [Field k] [Finite k] [AddCommGroup V] [Module k V] [Module.Finite k V] [AddCommGroup W] [Module k W] [Module.Finite k W] (F : Hall k) (a : End k V) (b : End k W)
lemma Hall.z1 : F.q6 (simClassOf a) (simClassOf b) = finMean (F <| simClassOf <| s11_z4 a b ·) := match s11_w5 a,
  s11_w5 b with | ⟨e, _⟩, ⟨f, _⟩ => (finMean_equiv
  (f.arrowCongr e).symm.toEquiv fun _ ↦ congrArg F (s11_q1 (f.prodCongr e)))
lemma Hall.x1 (H : Hall k) (a : End k V) (b : End k W) : (F * H).q6 (simClassOf a) (simClassOf b) = ∑ A : StableSubspace a, (F.q6 (simClassOf A.q3) * H.q6 (simClassOf A.q5)) (simClassOf b) := by
  let S (P : StableSubspace a × StableSubspace b) := P.2.1.compatibleMaps P.1.1
  let φ : (Σ P, S P × _ ⧸ S P) → Σ x, StableSubspace (s11_z4 a b x) | ⟨⟨A, B⟩, y, s⟩ => ⟨a ∘ₗ s.out - s.out ∘ₗ
     b + y, StableSubspace.comap (LinearEquiv.skewProd 1 1 s.out).1 (g' := s11_z4 a b y) (by simp; grind)
     ⟨.prod B A, by aesop⟩⟩
  have : φ.Bijective := ⟨fun ⟨P, _, s⟩ ⟨Q, _, t⟩ h ↦ ?_, fun ⟨_, U, u⟩ ↦ ?_⟩; simp [w2, ↓z1, finMean, div_mul_div_comm, ← Nat.cast_mul, sum_mul_sum, ← sum_prod_type', ← sum_sigma', ← this.sum_comp]; rw [sum_sigma, Finset.sum_div]; congr with ⟨⟨A⟩, ⟨B⟩⟩
  simp_rw [S, by simpa using (B.compatibleMaps A).card_eq_card_quotient_mul_card, ← card_prod,
   ← finMean_eq]
  refine (congrArg finMean ?_).trans (finMean_comp_surjective (.mk' (fun (⟨y, h⟩, _) ↦
   (y.restrict (id h), B.mapQ A y (id h))) (by clear * -; aesop)) (fun ⟨α, β⟩ ↦ by
   obtain ⟨⟨r, rfl⟩, c, rfl⟩ := projective_lifting_property _ β A.mkQ_surjective, α.exists_extend; use (⟨A.subtype ∘ₗ c + r ∘ₗ B.mkQ, fun _ ↦ ?_⟩, 0); ext
   all_goals simp_all [(Quotient.mk_eq_zero _).2]) _)
  ext; rw [p1, r9, y8 (B.subtype.prodMap A.subtype), z2 (B.mkQ.prodMap A.mkQ)]
   <;> simp [StableSubspace.q3, StableSubspace.q5, ← ker_eq_bot, ← range_eq_top]
  simp [φ, StableSubspace.comap, Sigma.subtype_ext_iff] at h
  cases show P = Q by ext w; simpa using h.2 0 w; rcases h.2 w (-s.out w), h.2 w (-t.out w); aesop
  simp_all [s.out_equiv_out.1 (leftRel_apply.2 fun _ _ ↦ ((h.2 ..).1 (by simpa)).2)]; have ⟨r, R⟩ := projective_lifting_property _ .id ((LinearMap.fst ..).submoduleMap_surjective U); obtain ⟨t, rfl⟩ := r.exists_extend
  let s := (S ⟨StableSubspace.comap (inr ..) (by simp) ⟨U, u⟩,
   U.map (LinearMap.fst ..), by aesop⟩).mkQ (-LinearMap.snd .. ∘ₗ U.subtype ∘ₗ t)
  have e : (φ ⟨_, 0, s⟩).2 = U := SetLike.ext fun z ↦ (and_congr_right fun h ↦ by
   simpa [Prod.sub_def, (congr($R ⟨_, h⟩) : (t z.1).1.1 = _)] using! U.sub_mem_iff_left
    (x := z) (add_mem (t z.1).2 (QuotientAddGroup.eq.1 s.out_eq h))).trans (by tauto)
  exact ⟨⟨_, ⟨_, fun w h ↦ by simpa [sub_add, ← sub_eq_add_neg] using (e.ge (u (w, -_)
   (e.le ⟨h, by simp⟩))).2⟩, s⟩, Sigma.subtype_ext (add_sub_cancel ..) ‹_›⟩
lemma Hall.r7 {o} (h : o.dim = 0) a : F.q6 o a = F a ∧ F.q6 a o = F a := by have := (Fin.cast h).isEmpty; simp [finMean]; rw [s11_q1 .prodUnique, q7, s11_q1 .uniqueProd, q7]; simp
omit [Finite k] in
lemma Hall.v8 (U : StableSubspace a) : U.q3.charpoly * U.q5.charpoly = a.charpoly := by
  erw [← charpoly_fromBlocks_zero₂₁', ← a.charpoly_toMatrix ((Free.chooseBasis k U).sumQuot
   (Free.chooseBasis ..))]; congr with ⟨⟩ ⟨⟩ <;> simp [U.2, (Quotient.mk_eq_zero _).2] <;> congr
  rw [← Basis.sumQuot_inr]; rfl
end
section
open Finset Fint LinearMap Module MulAction Pointwise Submodule GeneralLinearGroup
attribute [local simp] LinearMap.ext_iff
variable {k V} [Field k] [Finite k] [AddCommGroup V] [Module k V] [Module.Finite k V] {F H} (n)
omit [Finite k] in
lemma Hall.p0 {a : End k V} : (∀ x, (simClassOf a).out.2 x = x) ↔ a = 1 :=
  (s11_w5 a).rec (by simp [·.surjective.forall, ← ·])
lemma Hall.z6 : q0 (finrank k V) F H = @classInner (End k V)ˣ (F <| simClassOf ·.1) (H <| simClassOf ·.1) :=
  finMean_equiv (congrLinearEquiv _).1 (by congr! <;> exact (Quot.sound ⟨_, rfl⟩).symm)
lemma Hall.w0 {ι} [Fintype ι] : @classInner (GL ι k) F.evalGL H.evalGL = q0 (Fintype.card ι) F H := by simp_rw [← finrank_pi k, z6, classInner, finMean_equiv Matrix.GeneralLinearGroup.toLin.1]; rfl
lemma Hall.y3 (X A B : Hall k) : q0 n (A * B) X = ∑ p ∈ antidiagonal n, q0 p.1 A (q4 p.2 B X) := by
  let d (U : Submodule k (Fin n → k)) := finrank k U
  have S g {U y} h (H : d y = _) := eq_of_le_of_finrank_eq (map_le_iff_le_comap.2 h)
   (((toLinearEquiv g).finrank_map_eq U).trans H.symm)
  rw [Nat.antidiagonal_eq_map, sum_map, q0, finMean, ← fun M ↦ (sum_comp (M · / (#_ : ℂ))
   d).trans (.symm (sum_congr (f := M) (Subset.antisymm (fun _ _ ↦ mem_image.2 ⟨_, mem_univ _,
   (finrank_range_of_inj (finrank_le_iff_exists_linearMap.1 (by aesop)).choose_spec).trans
   (finrank_fin_fun k)⟩) (by simp [subset_iff, (finrank_le _).trans, d])) (by simp [field])))]
  simp [w2, sum_mul, sum_sigma']
  rw [← Equiv.sum_comp (ι := Σ U, stabilizer _ U) (.mk (⟨_, _, map_le_iff_le_comap.1 ·.2.2.le⟩)
   fun ⟨g, U, h⟩ ↦ ⟨U, g, S _ h rfl⟩), Fintype.sum_sigma, sum_div]; congr with U
  have ⟨Z, h⟩ := U.exists_isCompl; let e := Z.prodEquivOfIsCompl U h.symm
  rw [← card_orbit_mul_card_stabilizer_eq_card_group _ U, Nat.cast_mul, div_mul_eq_div_div_swap, ← finMean_eq, finMean_equiv ⟨fun t ↦ (⟨congrLinearEquiv e (ofLinearEquiv (.skewProd
   t.2.1.toLinearEquiv t.1.toLinearEquiv t.2.2)), S (congrLinearEquiv e _) (Subtype.forall'.2
   (by simp [e])) rfl⟩ : stabilizer _ U), fun ⟨g, H⟩ ↦ (ofLinearEquiv (g.toLinearEquiv.ofSubmodules
   _ _ (id H)), congrLinearEquiv (U.quotientEquivOfIsCompl Z h) (ofLinearEquiv (Quotient.equiv U U
   g.toLinearEquiv (id H))), U.projectionOnto Z h ∘ₗ domRestrict g Z), by aesop_cat, fun _ ↦ by
   ext : 2; simp [e]; grind [projection_add_projection_eq_self]⟩ fun _ ↦ rfl]
  simp [↓Equiv.coe_fn_mk, d, finMean_prod, z6, z1, q4, classInner, mul_assoc, ← finMean_const_mul, by simpa using e.finrank_eq.symm]
  congr! <;> [skip; apply z2 (s :=
   projectionOnto_surjective h.symm); apply s11_q1 e.symm _; use fun ⟨g, h⟩ ↦ h ▸ (toLinearEquiv g).finrank_map_eq U, fun H ↦ (exists_linearEquiv_restrict_eq (.ofFinrankEq _ _ H.symm)).rec fun g e ↦ ⟨_, S (ofLinearEquiv g)
   (by simp [← e ⟨·, ·⟩]) H⟩] <;> simp [e, StableSubspace.q3, restrict_apply, add_comm]
end
section
attribute [local simp] Finset.mul_sum Hall.IsCuspidal Hall.r7 Hall.q0 Hall.q4
variable {k} [Field k] [Finite k] {F H c f : Hall k} {d n} {o : SimClass k} (hc : c.IsCuspidal) (hd : d ≠ 0)
lemma Hall.z7 (hf : ∀ c, c.dim ≠ d → f c = 0) : q0 (d + n) (f * H) F = q0 n H (q4 d f F) := by rw [mul_comm, y3, Finset.sum_eq_single (n, d)] <;> simp +contextual (disch := simp; lia) [*]
omit [Finite k] in
lemma Hall.j2 (h : o.dim = 0) : o = simClassOf (0 : Module.End k (Fin 0 → k)) := q7 o ▸ s11_q1 (h ▸ 1) (by subsingleton)
@[simp] lemma Hall.b5 (h : o.dim = 0) : (F * H) o = F o * H o := by simpa [j2, h] using star_inj.2 (y3 0 1 F H)
include hc hd
lemma Hall.k5 : q0 d c (F * H) = q0 d c F * q0 0 constOne H + q0 0 constOne F * q0 d c H := by
  have := star_inj.2 (y3 d c F H)
  rw [Finset.sum_eq_add (d, 0) (0, d)] at this <;> simp_all [← finMean_conj, mul_comm]
  simp [finMean, Finset.sum_mul, field, mul_assoc]; aesop
lemma Hall.p8 : q4 d f c = q0 d f c • 1 := by aesop
lemma Hall.r5 : q4 d c (F * H) = q4 d c F * H + F * q4 d c H := by ext; simp [w2]; simp [x1, finMean_sum, @id (finMean _ = _) (k5 hc hd)]
omit hc hd
namespace Hall
open Module Finset StableSubspace Submodule LinearMap ComplexConjugate End Polynomial
lemma s11_p5 {L} [Lattice L] [BoundedOrder L] [IsModularLattice L] [Fintype L] {μ : L → ℂ} (M : ∀ X ≠ ⊥, ∑ U with U ≤ X, μ U = 0) (h : μ ⊤ ≠ 0) (W : L) : IsComplemented W :=
  (exists_maximal_of_wellFoundedGT _ ⟨⊥, by simp⟩).imp fun C ⟨d, m⟩ ↦ ⟨d,
  codisjoint_iff_le_sup.2 (by_contra (h ∘ (wellFounded_lt.1 ⊤).rec fun U _ _ _ ↦ by rw [← M U, ← @sum_sdiff L _ {A | A ≤ U ⊓ (W ⊔ C)}, M, sum_eq_single U] <;> grind [Ne.lt_of_le, disjoint_iff, le_sup_left, le_sup_right, le_inf_iff, d.disjoint_sup_right_of_disjoint_sup_left (c := U)]))⟩
variable {k : _} {V K} [Field k] [Finite k] [AddCommGroup V] [Module k V] [Module.Finite k V] {g : End k V} {o : SimClass k} (B : Hall k) [Field K] [Algebra k K] (η : K → ℂ)
lemma s11_j3 : moebius * constOne = (1 : Hall k) := by grind [j4]
lemma s11_y6 : ∑ W : StableSubspace g, moebius (simClassOf W.q3) = (1 : Hall k) (simClassOf g) := by rw [← s11_j3]; simp [w2]
attribute [local simp] w2 sum_filter projection_apply_of_mem_left greenCuspidal aroots_mul charpoly_monic Monic.ne_zero s11_y6
lemma s11_k9 (h : moebius (simClassOf g) ≠ 0) : g.IsSemisimple := isSemisimple_iff'.2
  (@s11_p5 _ _ _ ⟨(sup_inf_le_assoc_of_le ·.1)⟩ fintypeStableSubspace _ (fun X n ↦ by
  simpa +contextual [n, by simpa using j6 (g := q3 X) X.1.subtype (by aesop)] using! s11_y6 (g := q3 X)) (by rwa [s11_q1 topEquiv]))
@[simp] lemma b7 (h : o.dim = 0) : moebius o = 1 := by simpa [*] using congr($s11_j3 o)
@[simp ↓] lemma s11_d0 a b : B.mulMu.q6 a b = moebius a * moebius b * B (simClassOf (b.out.2.prodMap a.out.2)) := by
  erw [← congr($((j4.mul_right_cancel (by
   simp; ext _ b; apply congrFun (j4.mul_right_cancel _) a; ext _ g
   have := x1 moebius constOne g b; simp_all [z1, ite_and]) :
   q6 moebius a = moebius a • moebius)) b * _), q6, mul_comm, ← finMean_const_mul]; congr! 2
  simp [or_iff_not_imp_right]; intro
  obtain ⟨C, c, h⟩ :=
   isSemisimple_iff.1 (s11_k9 ‹_›) (.prod ⊥ ⊤) fun _ ↦ by aesop
  rcases projection_apply_mem h, (isIdempotentElem_projection h).ker_mem_invtSubmodule_iff.1
   (by simpa)
  rw [s11_q1 (.ofInjectiveEndo (.prod (fst ..) (snd .. ∘ₗ projection _ _ h)) _) _] <;> simp_all [injective_iff_map_eq_zero, Prod.ext_iff, ↓mem_prod, DFunLike.ext_iff]
@[simp] lemma d9 : ∀ c : SimClass k, conj (moebius c) = moebius c := congrFun
  (j4.mul_right_cancel (ext (by simp [← map_sum])))
@[simp] lemma s11_r8 : greenCuspidal k η * constOne = -brauerLift k η := by grind [s11_j3, (ext fun _ g ↦ by simp +contextual [← sum_add_distrib, mul_comm (moebius _), ← add_mul, ← Multiset.sum_add, ← mul_sum, ← Multiset.map_add, ← aroots_mul, v8, ← g.charpoly_natDegree] : greenCuspidal k η + moebius * brauerLift k η = 0)]
lemma x6 c : c.dim < 1 → greenCuspidal k η c = 0 := by simp_all [j2]
lemma s11_j9 : (greenCuspidal k η).IsCuspidal := fun a b _ _ ↦
  q7 a ▸ q7 b ▸ (x1 ..).trans (by simp_all
  [q6, -q7, charpoly_prodMap, mul_add, ← mul_sum, ← sum_mul, mul_assoc])
end Hall
end
noncomputable section
open Polynomial Classical Fint Function Real UniqueFactorizationMonoid FiniteField Nat Multiset
variable {k} [Field k] [Finite k] {K} [Field K] [Algebra k K] (T : MulChar K ℂ) {n} [Fintype n] (Q r : ℕ) (P c : k[X]) (χ : MulChar k ℂ)
def monicsOfDegree k [Field k] [Finite k] r := @Set.toFinset k[X] {_c | _} (.ofEquiv _ ((monicEquivDegreeLT r).trans (degreeLTEquiv ..).toEquiv).symm)
def faithfulChar k [Field k] : MulChar (AlgebraicClosure k) ℂ := epsilon (Injective ·)
class IsFaithfulMulChar K [Field K] (T : outParam (MulChar K ℂ)) extends IsAlgClosed K where injective : Injective T
def thetaChar x := T ^ epsilon (T x = .exp (2 * π * .I / (Q - 1 :)) ^ ·)
def greenTau := (-1 : ℂ) ^ P.natDegree • (Hall.greenCuspidal k (thetaChar T (.card k ^ P.natDegree) (epsilon (P.aeval · = 0)))).rankPart P.natDegree
def labelChar : k[X] →* Hall k :=
  ⟨⟨fun c ↦ ite (c = 0) 0 ((normalizedFactors c).map (greenTau T)).prod, by simp⟩, by aesop⟩
def IsLabel := c.Monic ∧ Squarefree c ∧ c.natDegree = r ∧ c.coeff 0 ≠ 0
def detChar : Hall k := fun c ↦ χ ((-1) ^ c.dim * c.charpoly.coeff 0)
def reflectionSum l := groupAlgElem fun h : GL n k ↦ ite (∃ u, h.1 = 1 + .vecMulVec u l) (χ⁻¹ h.1.det) 0
def labelIdem n [Fintype n] (c : k[X]) := let Ξ := (labelChar (faithfulChar k) c).evalGL (n := n)
  ite (IsLabel (Fintype.card n) c) (groupAlgElem fun g ↦
   Ξ 1 / Nat.card (GL n k) * starRingEnd ℂ (Ξ g)) 0
variable {k K : _} [Field k] [Finite k] [Field K] [Algebra k K] {P : k[X]} (hP : Irreducible P) {x : K} (hx : aeval x P = 0)
@[simp] lemma pow_pred_eq_one_iff {Q} (hQ : 2 ≤ Q) : x ^ (Q - 1) = 1 ↔ x ≠ 0 ∧ x ^ Q = x := by grind [pow_sub₀, zero_pow]
@[simp] lemma algebraMap_pow_card_pred_eq_one (a : kˣ) : algebraMap k K a ^ (.card k - 1) = 1 :=
  card_units k ▸ mod_cast by simp
include hP hx
lemma root_pow_card_pow_eq_self_iff {n} : x ^ .card k ^ n = x ↔ P.natDegree ∣ n := by simp [hP.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X, ← hP.dvd_iff_aeval_eq_zero hx]
lemma s11_k3 {a b} : x ^ .card k ^ a = x ^ .card k ^ b ↔ a ≡ b [MOD P.natDegree] := by
  have := @(frobeniusAlgHom k K).injective.eq_iff
  induction a, b using Nat.recDiagAux <;> simp_all [pow_succ, pow_mul, eq_comm, modEq_iff_dvd', ← root_pow_card_pow_eq_self_iff hP hx, modEq_zero_iff_dvd]
lemma aroots_eq_frobenius_orbit : P.aroots K = .map (x ^ .card k ^ ·) (range P.natDegree) := by
  have := (aeval_algHom <| frobeniusAlgHom k K ^ ·)
  apply roots_eq_of_degree_le_card_of_ne_zero (S := ⟨_, (nodup_range _).map_on _⟩) <;> simp_all
   [hP.ne_zero, coe_frobeniusAlgHom, ↓s11_k3 hP, ModEq, mod_eq_of_lt]
lemma aroots_pow_eq_frobenius_orbit {j} : (P ^ j).aroots K = .map (x ^ .card k ^ ·) (range (P ^ j).natDegree) ∧ x ^ .card k ^ (P ^ j).natDegree = x := by induction j <;> simp_all [aroots_eq_frobenius_orbit _ hx, @pow_add ℕ, add_mul, add_smul, range_add, pow_mul, root_pow_card_pow_eq_self_iff hP, -card_eq_fintype_card]
lemma exists_pow_card_pow_eq_of_root {y} : aeval y P = 0 → ∃ i < P.natDegree, x ^ .card k ^ i = y :=
  by simpa [hP.ne_zero] using congr(y ∈ $(aroots_eq_frobenius_orbit hP hx)).mp
end
section
open Hall LinearMap Module Polynomial StableSubspace Submodule
variable {k V} [Field k] [Finite k] [AddCommGroup V] [Module k V] [Module.Finite k V] {g : End k V}
omit [Finite k] in
lemma v9 {P} (hP : Irreducible P) (hm : Monic P) (h : IsNilpotent (aeval g P)) : charpoly g = P ^ (finrank k V / P.natDegree) := by have := charpoly_dvd_charpoly_aeval_comp (Y := g.toMatrixAlgEquiv (finBasis ..)) P; simp_all [↓aeval_algHom_apply, toMatrixAlgEquiv, h.charpoly_eq_X_pow_finrank]; grind [charpoly_natDegree, natDegree_pow, Nat.mul_div_left, dvd_prime_pow hP.prime, eq_of_monic_of_associated, charpoly_monic, Monic.pow]
lemma Hall.IsCuspidal.exists_charpoly_eq_pow {F} (h : IsCuspidal F) (hF : F (simClassOf g) ≠ 0) : ∃ P j, Irreducible P ∧ charpoly g = P ^ j := by_cases (⟨X, 0, irreducible_X, g.charpoly_monic.eq_one_of_isUnit ·⟩) fun u ↦ by
  have ⟨P, m, i, d⟩ := (g.toMatrixAlgEquiv _).charpoly.exists_monic_irreducible_factor u; have ⟨N, I, n⟩ := ((aeval g P).eventually_isCompl_ker_pow_range_pow.and Nat.eventually_pos).exists
  have c Y h := DFunLike.congr_fun (Algebra.commute_of_mem_adjoin_singleton_of_commute
   ((P ^ N).aeval_mem_adjoin_singleton k g) ((Y * g).ext h))
  simp_all [aeval_algHom_apply, i.dvd_iff_not_isCoprime, ← isUnit_aeval_iff_isCoprime.trans isCoprime_comm]; let C : StableSubspace g := ⟨ker (aeval g P ^ N), by simp_all [← c]⟩
  have E : ∀ x, simClassOf (s11_z4 C.q3 C.q5 x) = simClassOf g :=
   (surjective_of_injective (.of_ker (C.q3.compRight k - C.q5.lcomp ..) fun y e ↦
   y.ext ((reindex_equiv (quotientEquivOfIsCompl _ _ I).symm).1.2 fun ⟨_, v, rfl⟩ ↦ Subtype.ext
   ((c (C.1.subtype ∘ₗ y ∘ₗ mkQ _) (congr($(sub_eq_zero.1 e) ⟦·⟧ |>.1).symm) v).trans
   (y _).2)))).forall.2 fun y ↦ s11_q1 (.skewProd (quotKerEquivRange _) 1 y ≪≫ₗ
   prodEquivOfIsCompl _ _ I.symm)
   (by simp [Submodule.Quotient.forall, q3, q5, C]; grind)
  exact ⟨P, i, _, v9 i m
   ⟨N, by simpa [*, C, z1, n.ne', ← isUnit_iff_ker_eq_bot, finrank_zero_iff, ↓finrank_eq_zero] using h (simClassOf C.q3) (simClassOf C.q5)⟩⟩
lemma s11_m8 {K} [Field K] [Algebra k K] η η' {a} (h : ∀ z, g.charpoly.aroots K = .map (z ^ .card k ^ ·) (.range (finrank k V)) ∧ z ^ .card k ^ finrank k V = z → a * η z = η' z) : greenCuspidal k η' (simClassOf g) = a * greenCuspidal k η (simClassOf g) := by_contra (· <| by
  simp [greenCuspidal, w2, mulMu, Finset.mul_sum, ← mul_assoc, ← Multiset.sum_map_mul_left]
  congr! with W _ z; grind +splitImp [s11_j9, → IsCuspidal.exists_charpoly_eq_pow, aroots_pow_eq_frobenius_orbit, mem_aroots, pow_ne_zero, congr(aeval z $(v8 _ W)), charpoly_natDegree])
end
open Module Algebra Finset Fint Hall Lagrange Matrix Polynomial Submodule minpoly
variable {k K F V} [Field k] [Finite k] [Field K] [Algebra k K] [Field F] [Finite F] [Algebra k F] (z : PowerBasis k F) [AddCommGroup V] [Module k V] [Module F V] [IsScalarTower k F V] [Module.Finite k V] [Module.Finite F V]
lemma card_GL_eq_prod {n R} [Fintype n] [Field R] : Nat.card (GL n k) = ∏ i ∈ range (Fintype.card n), (Nat.card k ^ i * (Nat.card k ^ (i + 1) - 1) : R) := by open Calc in
  simp [↓Nat.card_congr (Units.mapEquiv (reindexRingEquiv k (Fintype.equivFin n)).toMulEquiv).1, ↓card_GL_field, Nat.pow_le_pow_right Fintype.card_pos]; induction Fintype.card n <;> simp_all
   [Fin.prod_univ_succ, prod_range_succ, pow_succ, ← sub_mul] <;> ring
attribute [local simp] w2 finrank_zero_iff eval_finsetSum mul_smul add_smul
lemma x9 η : let N : ℂ[X] := nodal (range (finrank F V)) fun x ↦
   ↑(Nat.card F ^ x)
  let g := lsmul k k V z.gen; moebius (simClassOf g) = N.eval 0 ∧ greenCuspidal k η (simClassOf g) =
  -(((minpoly k z.gen).aroots K).map η).sum * N.derivative.eval 1 := by
  intro N g; have := @finite_of_finite k V
  let S (W : StableSubspace g) : Submodule F V := ⟨W.1.1, fun c _ ↦ (z.exists_eq_aeval'
   c).choose_spec ▸ (aeval_apply_smul_mem_of_le_comap' · _ _ W.2)⟩
  rw [← one_mul moebius, (eq_of_degree_sub_lt_of_eval_index_eq _ (Nat.cast_injective.comp
   (Nat.pow_right_injective Finite.one_lt_card)).injOn ((degree_lt_iff_coeff_zero ..).2
   fun n h ↦ ?_) fun j h ↦ (eval_nodal_at_node h).trans ?_ : N = ∑ W, monomial (finrank F (S W))
   (moebius (simClassOf W.q5)))]
  simp [(by grind [s11_j3, s11_r8 η] : greenCuspidal k η = -brauerLift
   k η * moebius), z.finrank, ← finrank_mul_finrank k F, z.dim_pos.ne', zero_pow_eq, mul_sum, derivative_monomial, fun W ↦ show simClassOf W.q3 = simClassOf (lsmul k k (S W) z.gen) from rfl, monic z.isIntegral_gen, v9 (irreducible z.isIntegral_gen), Multiset.map_nsmul, Multiset.sum_nsmul]; ac_rfl
  erw [coeff_sub, ← (isMonicOfDegree_monomial_one _).coeff_eq ⟨by simp, nodal_monic⟩ h, finsetSum_coeff, Fintype.sum_eq_single ⟨⊤, by simp⟩, finrank_top] <;> simp_all
   [coeff_monomial]; intro a b n; bound [(S ⟨a, b⟩).finrank_lt (n <| top_unique ·.ge)]
  simp; simp_rw [pow_right_comm _ j, ← Nat.cast_pow, ← card_eq_pow_finrank, Nat.cast_pow, Fintype.card_subtype, ← sum_boole, Fintype.sum_pow, Fintype.prod_boole, mul_sum, ← SetLike.mem_coe, ← Set.range_subset_iff, ← span_le]; rw [sum_comm, sum_eq_zero]; intro v _; let U : StableSubspace g := ⟨(span F (.range v)).restrictScalars k, by aesop⟩
  simpa [sum_filter, U, mt finrank_le_of_span_eq_top, mem_range.1 h, s11_y6] using!
   ((StableSubspace.j6 U.1.mkQ (g' := U.q5) (by bound) _).trans
   (by simp)).trans congr($(mul_comm constOne moebius) (simClassOf U.q5))
lemma m1 η [Nontrivial V] : (greenCuspidal k η).mulMu (simClassOf (lsmul k k V z.gen)) * (.card V - 1 : ℕ) = (((minpoly k z.gen).aroots K).map η).sum * Nat.card {e : V ≃ₗ[k] V // ∀ x, e (z.gen • x) = z.gen • e x} := by
  simp_rw [mulMu, x9 z η]; rw [@natCard_eq_pow_finrank F V, eq_comm, ← Nat.card_congr ((GeneralLinearGroup.toLin' (finBasis F V)).1.trans ?_), card_GL_eq_prod, ← Nat.sub_add_cancel finrank_pos, nodal, prod_range_succ']; simp [eval_prod, pow_succ, prod_range_succ, ← neg_sub (1 : ℂ), -neg_sub, -Nat.card_eq_fintype_card, prod_neg]; ring
  exact .mk (⟨·.toLinearEquiv.restrictScalars k, by simp⟩) fun ⟨f, _⟩ ↦ .ofLinearEquiv {f with
   map_smul' c := by induction eq_top_iff.1 z.adjoin_gen_eq_top c using adjoin_induction <;> aesop}
