import Lib.General.Geometry.ChartedSchemes
import Lib.Cohomology.Duality.Contraction
import Lib.Cohomology.ProjectiveLine.NormalizationPullback
import Lib.PadicComparison.HodgeTate.GaloisTwist
import Lib.Shimura.Eigenspace.EigenQuotient
import Lib.PadicComparison.HodgeTate.HodgeTateVectors
import Lib.General.Geometry.Lefschetz
section
open Localization CategoryTheory Fin Function Ideal IsLocalizedModule LinearMap MvPolynomial RingHom
  ConcreteCategory CategoryTheory.Functor IsLocalization.Away RingTheory.Sequence
variable {k ι : Type} [CommRing k] {c : HodgeTest k} {n} [Fintype ι] {f : ι → c.baseAlg} {d}
def someUnitLocus (f : ι → c.baseAlg) : Subfunctor (reprBy c) :=
    ⟨fun _ ↦ {y | ∃ i, IsUnit (y.1.1 (f i))}, fun a _ ↦ .imp fun _ ↦ .map a.1.1⟩
lemma depth_vanishing (H : ℕ → _ → ModuleCat k) {I l} (hI : ∀ n M x, I ≤
    (torsionOf k (H n M) x).radical) (hδ : ∀ n (M : ModuleCat k) (r : k), IsSMulRegular M r → (∀ m <
    n, Subsingleton (H m (.of k (QuotSMulTop r M)))) → IsSMulRegular (H n M) r) (hl : ofList l ≤ I)
    (hn : n < l.length) (M : ModuleCat k) (h : IsWeaklyRegular M l) : Subsingleton (H n M) := by
  induction l generalizing M n <;> simp at *
  exact subsingleton_of_forall_eq 0 (hI _ _ · hl.1 |>.elim ((hδ _ _ _ h.1 (by bound)).pow ·
    |>.right_eq_zero_of_smul))
seal exteriorMap in
lemma DepthVanishing.subsingleton_of_isWeaklyRegular l (hl : ofList l ≤ span (.range f)) (hn :
  n < l.length) (h : IsWeaklyRegular c.baseAlg l) :
  Subsingleton (H (relFreeAb (someUnitLocus f)) hodgeCoeff n) := by
  let L {C} [Category C] (φ : C ⥤ _) x s : C ⥤ Comma (𝟭 _) (coyoneda ⟨c⟩) :=
    .mk (⟨x ⟶ ·, _, ↾(s ≫ φ.map ·)⟩) fun a ↦ .mk (↾(· ≫ a)) (φ.map a)
  let ψ := L (𝟭 _) c (𝟙 _); let P := ObjectProperty.ι fun B : CommAlg c.baseAlg ↦
    Module.Flat c.baseAlg B
  let U g : Subfunctor (Comma.fst (𝟭 _) (coyoneda ⟨c⟩) ⋙ uliftFunctor) := ⟨fun X ↦ {t |
    IsUnit ((X.3 t.1).1 g)}, fun a _ ↦ congr(IsUnit (($a.w _).1 g)).mpr ∘ .map a.2.1.1⟩
  have bij B (b : P B) := (@pointMap_bijective_of_existsUnique _ _ B ⟨_, B.2.trans ..⟩) ⟨fun _ ↦
    {x | IsUnit (x.1.1 b)}, fun a _ ↦ .map a.1.1⟩ ⟨⟨⟨B.1.toAway b⟩⟩, algebraMap_isUnit _⟩ fun _ _
    h ↦ ⟨⟨ofHom (liftAlgHom _ h)⟩, by aesop (add simp Algebra.algHom)⟩; let W := ⨆ i, U (f i)
  have ind {Q} (hP : IsClosedClass Q) (h : ∀ g, Q (freeAb (U g).toFunctor)) :=
    (hP.2 _ (relFreeAb.shortExact W).2 (hP.freeAb_iSup
    (.range U) (by simpa [h] using (⟨· * ·, by ext; simp [U]⟩)) (by simp))).1
    ((hP.iff_of_isIso (freeAb.map (Subfunctor.ι ⊤))).1 (by simpa [U] using! h 1))
  let γ : Comparison hodgeCoeff (piAbFunctor fun _ ↦ moduleCoeff (asModules P ⋙ tensorWith c.baseAlg
    _)) := ⟨P ⋙ restrictAlg k _ ⋙ HodgeTest.withIndex c.Index, fun B ↦ (AddEquiv.ulift.trans
    ((Pi.basisFun B.1 c.Index).ExteriorAlgebra.equivFun.toAddEquiv.trans (.piCongrRight fun _ ↦
    .symm (.trans .ulift (TensorProduct.lid ..).toAddEquiv)))).toAddCommGrpIso.hom,
    fun B D a ↦ by ext; congrm (⟨1 ⊗ₜ $(HodgeTest.repr_withIndex_map a.1 _ ·)⟩)⟩
  let ψ' := L γ.φ ⟨.of .., .self⟩ ⟨ofHom ⟨.id _, by tauto⟩, .id⟩
  let η : ψ' ⟶ γ.φ ⋙ ψ := .mk fun B ↦ .mk (ψ' B).3 (𝟙 _)
  refine (by ext; simp [W, Subfunctor.whisker]; rfl : W.whisker ψ = someUnitLocus f) ▸ have :=
      (depth_vanishing (fun n M ↦ .of _ (H (ψ' ⋙ relFreeAb W) (moduleCoeff (asModules P ⋙ tensorWith
      _ M)) n)) (fun n M _ ↦ span_le.2 (fun | _, ⟨i, rfl⟩ => exists_exists_eq_and.1 (mem_ker_iff
      (.powers _) (g := TensorProduct.mk _ (Away (f i)) _ 1).1 ((ind (FP.isClosedClass.comap
      (restrictAlong ψ')) (bij ⟨.of .., _⟩ · |> FP.isClosedClass.of_bijective _ <|
      hasFlatBaseChange_reprFunctor _) _ c.baseAlg ..).1 (((relFreeAb.isCohomEquiv_iff_subsingleton
      (W.whisker _)).1 (IsCohomDense.isCohomEquiv (.mono (U := (U _).whisker ψ') ?_ fun _ ↦ le_iSup
      (U ∘ f) i _)) n).1 ..))))) (fun _ M r h i _ _ ↦ eq_of_tensorPush_eq (exact_lsmul_mkQ_smul_top
      M r) Quot.exists_rep (·.2.rTensor_preserves_injective_linearMap _ h) i) hl hn (.of ..) h)
    ((H.pi_bijective ..).comp (ind (γ.isClosedClass η) (fun g ↦ ((γ.isBijective_congr (pointMap_comp
      _ (whiskerRight η (U g).toFunctor)) (.of_bijective (pointMap_bijective_of_existsUnique
      ((U g).whisker ψ) _ (HodgeTest.existsUnique_lift_away _ g isLocalization.1)))
      (.of_bijective (bij ⟨.of .., .self⟩ g))).2 (γ.isBijective_of_repr (u :=
      pointMap ⟨𝟙 _⟩) ⟨𝟙 _⟩ (pointMap_id_bijective_of_fullyFaithful (𝟭 _) _) (.comp
      (AddEquiv.bijective _) (bijective_of_isIso (hodgeCoeff.map (_ ≫ _))))) :)) n)).1.subsingleton
  rintro B ⟨⟨y⟩⟩; cases show y = structureMap by ext
  exact (Comparison.isBijective_of_repr _ (bij B _) (ULift.map_bijective.2 (congr(Bijective $(show _
    = lTensor .. by ext; simp [TensorProduct.smul_tmul']; rfl)).mp (isBaseChange (.powers (f i)) _
    ((TensorProduct.assoc ..).1 ∘ₗ TensorProduct.map (TensorProduct.mk c.baseAlg _ _ 1)
    (IsScalarTower.toAlgHom _ B.1 (Away (algebraMap _ _ (f i)))).toLinearMap))))).eqv
lemma isCohomEquiv_someUnitLocus (h : span (.range f) = ⊤) : IsCohomEquiv hodgeCoeff
  (freeAb.map (someUnitLocus f).ι) := (relFreeAb.isCohomEquiv_iff_subsingleton _).2 fun n ↦
  DepthVanishing.subsingleton_of_isWeaklyRegular
  (.replicate n.succ 1) (by aesop) (by simp) ⟨by simp⟩
lemma hodge_vanishing_along_diagonal {x : _ → c.baseAlg} (hx : (polyEval x).Etale) (hn : n < d) :
  Subsingleton (H (relFreeAb (someUnitLocus (x ∘ castAdd d - x ∘ natAdd d))) hodgeCoeff n) :=
  DepthVanishing.subsingleton_of_isWeaklyRegular _ (by simp [ofList, Set.range, algebraMap])
  (by simpa) (@.of_flat _ _ _ _ (_) (Flat.comp (.of_bijective (f := (bind₁ (append (X ∘ castAdd d
  - X ∘ natAdd d) (-X ∘ natAdd d))).1) (Involutive.bijective (by apply ·.induction_on <;> simp_all
  [forall_fin_add, -natAdd_eq_addNat]))) (Etale.iff_flat_and_formallyUnramified.1 hx).1)
  (.ofFn (X ∘ castAdd d)) ⟨fun i _ ↦ (isSMulRegular_quotient_iff_mem_of_smul_mem ..).2 fun p h ↦ by
  rw [smul_eq_mul, mul_top, ofList, show {r | r ∈ _} = X '' castAdd d '' {j | j < i} by
    grind [List.mem_take_iff_getElem], mem_ideal_span_X_image] at *
  exact fun m _ ↦ (h (.single ⟨i, by grind⟩ 1 + m) (by simp_all)).imp (by simp; grind)⟩)
lemma hasZariskiDescent_hodgeCoeff : HasZariskiDescent (@HodgeTest.sqZeroExt k _ ⋙ forget₂ _ _)
  hodgeCoeff := fun Y U h X y ↦ ((span_eq_top_iff_finite _).1
  (ne_top_iff_exists_maximal.not_right.2 fun ⟨m, l, e⟩ ↦ (h X y m l).elim fun _ a ↦ a.1
  (e (subset_span a.2)))).elim fun s ⟨l, e⟩ ↦ (IsCohomDense.mono (U := someUnitLocus fun i : s ↦
  X.baseProj _) (fun _ g ↦ isCohomEquiv_someUnitLocus (by erw
  [← Set.image_eq_range (X.baseProj ≫ _), ← Ideal.map_span, e, Ideal.map_top])) fun _ _ ⟨i, u⟩ ↦
  l i.2 _ _ (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 u)).isCohomEquiv
end
section
open Algebra.TensorProduct AddSubmonoid CategoryTheory Comparison CommAlgCat IsCohomEquiv Finset
  Finsupp TotalH TensorProduct CartesianMonoidalCategory MonoidalCategory Module.Basis Abelian.Ext
seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor in
lemma kunneth {k} [Field k] [CharZero k] {X d n} [hX : HasAtlas d X] (z : HodgeH _ n) :
    z ∈ AddSubmonoid.closure {z | ∃ a b e,
  ∃ (x : HodgeH (freeAb.obj X) a) (y : HodgeH (freeAb.obj X) b), z = .map (freeAb.prod X X)
  (_root_.cup (@exteriorAlg k _).mulPairing x y e :)} := hX.exists_isCharting.elim fun V ⟨h, t⟩ ↦ by
  have hU := hasZariskiDescent_hodgeCoeff (h.whisker _)
  have u {P} (hP : IsClosedClass P) (h : ∀ c, P (freeAb _)) : P (freeAb (V.whisker _).toFunctor) :=
    t _ (hP.comap (restrictAlong _)) fun b _ ↦
    hP.of_bijective _ b.exists_univPoint.choose_spec.2 (h _)
  refine (mem_map_iff_mem (((hU.preimage (fst ..)).inf (hU.preimage (snd ..))).isCohomEquiv n).1).1
    ((DirectSum.of_eq_same ..).subst ((((of_isIso (freeAb.map (NatIso.ofComponents fun _ ↦
    (Equiv.Set.prod ..).toIso).1 ≫ freeAb.prod (V.whisker _).toFunctor _)).bijective_totalH.comp
    (u (isClosedClass_lerayHirsch (Φ := abTensor _) (θ := fun i : Σ n,
    ofVectorSpaceIndex k (H _ _ n) ↦ H.push _ exteriorAlg.mulPairing _ (i.2.1.mapExactFunctor
    (abTensor.flip _)))) fun c ↦ ?_)).2.forall (p := (· n ∈ _))).2 (·.induction_linear (by simp)
    (by simp_all [add_mem]) fun ⟨a, x, _⟩ y ↦ ((hU.isCohomEquiv _).2 x).elim fun _ e ↦ ?_) _))
  let b := (ofVectorSpace k _).smulTower c.formBasis
  refine (bijective_iff_of_comm_sq (·.induction_linear (by simp [↓map_zero])
    (by simp_all [↓map_add]) fun _ r ↦ ?_) (curryAddEquiv.trans
    (mapRange.addEquiv (b.repr.symm.toAddEquiv.trans (.trans (.symm .ulift) (sectionEquiv
    hodgeCoeff _))))).bijective (u (isClosedClass_lerayHirsch (Φ := abTensor.flip _) (θ := fun j ↦
    mk₀ ((abTensor _).map ((homReprEquiv c hodgeCoeff).symm ⟨b j⟩) ≫ exteriorAlg.mulPairing)))
    fun c' ↦ ?_)).1 (Finsupp.domLCongr (.prodComm ..) ≪≫ₗ curryLinearEquiv k ≪≫ₗ
    mapRange.linearEquiv (DFinsupp.basis fun _ ↦ ofVectorSpace ..).repr.symm).bijective
  simp [DFinsupp.basis]
  conv_rhs => rw [lerayHirsch_single, TotalH.smul_eq_comp, map_comp_assoc, map_homClass,
    ← homClass_comp]
  conv_lhs => erw [lerayHirsch_single, map_homClass, (mk₀_bijective ..).1 ((push_homReprEquiv_symm
    (CoeffAction.act r).asHom ..).symm.trans (mk₀_comp_mk₀ ..)), toTotalH, ← of_comp_homClass,
    ← map_of, ← TotalH.comp_assoc_of_sq (naturality (abTensor.flip.map _) _), ← homClass_comp]
  congr 2
  exact abTensor_hom_ext fun _ _ _ ↦
    congrArg _ ((mul_smul_comm r ..).trans (smul_mul_assoc ..).symm)
  let z : (reprBy c' ⊗ reprBy c) ⟨c'.baseAlg ⊗ c.baseAlg, _ ⊕ₗ _⟩ :=
    (⟨ofHom includeLeft, semilinearOfBasis _
    ((Pi.single · 1) ∘ .inl)⟩, ⟨ofHom includeRight, semilinearOfBasis _ ((Pi.single · 1) ∘ .inr)⟩)
  let s {c I} g (ε : I → ℤˣ) := ((HodgeTest.formBasis.reindex g).groupSMul
    ε).repr.symm.toAddEquiv.trans (.trans (.symm .ulift) (sectionEquiv (@hodgeCoeff k _) c))
  refine' ((of_isIso (freeAb.map (isoOfAppBijective (pointMap z) fun B ↦ .of_existsUnique _
    fun ⟨⟨f⟩, ⟨g⟩⟩ ↦ (existsUnique_tensor_desc f.1 g.1).elim fun _ ⟨a, b⟩ _ ↦ by
    refine' ⟨⟨_, semilinearOfBasis _ (Sum.rec _ _)⟩, congr((⟨$(HodgeTest.hom_ext a _)⟩,
      ⟨$(HodgeTest.hom_ext b _)⟩)), _⟩ <;> try exact fun _ ↦
      (congrArg _ (semilinearOfBasis_single ..)).trans (semilinearOfBasis_single ..)
    rintro _ ⟨⟩; exact congr(⟨$(HodgeTest.hom_ext (by tauto)
      (by rintro ⟨⟩ <;> exact .symm ((semilinearOfBasis_single ..).trans (congrArg _
      (semilinearOfBasis_single ..)))))⟩)).1 ≫ freeAb.prod ..)).bijective_totalH.of_comp_iff' _).1
    ((bijective_iff_of_comm_sq (curryAddEquiv.surjective.forall.2 (·.induction_linear
    (by simp [↓map_zero]) (by simp_all [↓map_add, -mapRange.addEquiv_apply]) fun ⟨⟨_, _⟩, _⟩ _ ↦ _))
    (mapRange.addEquiv (s 1 1)).bijective (s sumEquiv.1 (Function.uncurry _)).bijective).1
    ((equivFinsuppOfBasisRight b).symm ≪≫ₗ (c.formBasis.repr.restrictScalars _).lTensor _ ≪≫ₗ
    finsuppTensorFinsupp ..).bijective)
  swap; simp [s, b, lerayHirsch_single, groupSMul]
  conv_lhs => erw [map_homClass, homClass_comp_homClass_comp, ← homClass_comp]
  refine congrArg _ ((Equiv.eq_symm_apply _).2 (congr(exteriorAlg.mulPairing _ ($(add_zero _) ⊗ₜ
    $(add_zero _))).trans (congrArg _ (?_ : exteriorMap z.1.1.2 _ * exteriorMap z.2.1.2 _ = _))))
  erw [exteriorMap_smul, exteriorMap_smul, smul_mul_smul, exteriorMap_formBasis _ (.sumLexInl ..)
    (semilinearOfBasis_single _ _), exteriorMap_formBasis _ (.sumLexInr ..)
    (semilinearOfBasis_single _ _), ExteriorAlgebra.basis_mul_of_disjoint (I := Lex _)
    _ ⟨_, rfl⟩ ⟨_, rfl⟩ (disjoint_map_inl_map_inr ..)]; simp [z]; rfl
  apply y.induction_on .. <;> simp_all [add_mem, lerayHirsch_single, comp_of, DirectSum.of_apply,
    dite_mem, (hU.isCohomEquiv _).2.forall]
  exact fun | _, _, rfl => e ▸ ⟨_, subset_closure ⟨a, by tauto⟩, (H.map_comp ..).symm.trans
    ((cup_map (h := freeAb.hom_ext) ..).trans (congrArg _ (comp_assoc_of_third_deg_zero ..)))⟩
end
noncomputable section
open CategoryTheory Function MonoidalCategory TensorProduct Finset Abelian Ext RingHom TrivSqZeroExt
  Matrix exteriorPower Set Ideal Fin ULift witnessed HodgeTest Comparison H TotalH freeAb
set_option backward.isDefEq.respectTransparency false
variable {k} [Field k] {d V} (f : V ⟶ sqZeroExt ⋙ affineSpace k d)
def jouanolouRel : Subfunctor (V ⊗ .mk (·.baseAlg) (·.1) ⋙ affineSpace k d) :=
  ⟨fun c ↦ {(v, l) | l.1 ⬝ᵥ fst ∘ (f.app c v).1 = 1}, fun φ _ h ↦ congr(_ ⬝ᵥ
  _ ∘ $(f.naturality_apply ..).1).trans (by simpa [dotProduct] using! congr(φ.1 $h))⟩
lemma exists_jouanolouRel_of_unimodular c v (h : v ∈ ((@unimodular k _ d).whisker _).obj c) : ∃ l,
  (v, l) ∈ (jouanolouRel (𝟙 _)).obj c :=
  «exists».2 (mem_span_range_iff_exists_fun.1 ((unimodular.map c.baseProj h).ge ⟨⟩))
variable {R} (ω : freeAb.obj V ⟶ hodgeCoeff) (h : R ≤ jouanolouRel f) {c : HodgeTest k}
instance : Module c.baseAlg (hodgeCoeff.obj c) := module' (M := ExteriorAlgebra ..)
@[simp] def detCochain := desc (Y := witnessed R d) (fun c t ↦ det (t.1.2 · |>.1) • ω.app c
  (.of t.1.1)) fun _ _ _ _ ↦ congrArg up (.symm ((exteriorMap_smul ..).trans
  (congrArg₂ _ (map_det ..) congr($(ω.naturality_apply ..).1).symm)))
lemma sum_minor_eq_mul_det (t : Matrix _ _ c.baseAlg) f i (h : ∀ j, t j ⬝ᵥ f = 1) :
    ∑ j : Fin d.succ, (-1) ^ (j.1 + i.1) • (t.submatrix j.succAbove i.succAbove).det =
    f i * t.det := by simpa [det_succ_column' _ i, ← dotProduct.eq_1, dotProduct_comm f, h]
    using (open Calc in t.det_updateCol_sum i f)
def detCocycle := abCoker.desc (α := boundary (jouanolouRel f) d) (detCochain ω) (hom_ext fun c ⟨⟨v,
  l⟩, t⟩ ↦ by simpa [boundary, sum_app_apply, -NatTrans.app_sum, ← smul_assoc,
  sum_smul] using! congr($(sum_minor_eq_mul_det (vecCons
  0 <| l · |>.1) (vecCons 0 _) 0 (by simpa)) • ω.app c (.of v)))
@[simp] lemma pi_comp_detCocycle : abCoker.π _ ≫ detCocycle f ω = detCochain ω := rfl
def volumeForm : freeAb.obj (sqZeroExt ⋙ affineSpace k d) ⟶ hodgeCoeff := desc (fun _ v ↦
  ⟨(ιMulti _ d (snd ∘ v.1)).1⟩) fun _ _ _ _ ↦ congrArg _ (exteriorMap_iotaMulti ..).symm
def symbolClass : HodgeH (_root_.relFreeAb (@unimodular k _ d)) d :=
  cocycleClass exists_jouanolouRel_of_unimodular (detCocycle _ volumeForm)
attribute [-simp] map_smul zsmul_eq_mul
abbrev IsInducedByCoords (v : Fin d → c.baseAlg) (f : Fin d → TrivSqZeroExt c.baseAlg _) (α :
  _root_.relFreeAb (someUnitLocus v) ⟶ _) := ∀ C σ,
  α.app C (relFreeAb.mk _ σ) = relFreeAb.mk (unimodular.whisker _) ⟨sqZeroExt.map σ.1 ∘ f⟩
seal Finset.univ Finset.sum Finset.prod in
seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor in
lemma symbolClass_transformation {v : Fin d → c.baseAlg} {f g α β}
  (hα : IsInducedByCoords v f α) (hβ :
  IsInducedByCoords v g β) (hf : fst ∘ f = v) (M N : Matrix (Fin d) _ _) (a : k)
    (hM : v = M *ᵥ fst ∘ g)
  (hN : ∀ i j, (f i).snd j - ∑ l, N i l * (g l).snd j ∈ span (.range v)) (ha : N.det - algebraMap k
  _ a * M.det ∈ span (.range v)) : H.map _ α d symbolClass = a • H.map _ β d symbolClass := by
  let S : ⋀[c.baseAlg]^d _ →+ _ := (cocycleClass (U := someUnitLocus v) (hf ▸ fun _ _ ⟨i, h⟩ ↦
    ⟨⟨Pi.single i _⟩, (single_dotProduct ..).trans h.val_inv_mul⟩)).comp
    (.mk' (detCocycle (pointMap ⟨f⟩) <| ((homReprEquiv ..).trans
    .ulift).symm ·.1) fun _ _ ↦ (cancel_epi (abCoker.π _)).1 (hom_ext (by simp)))
  have T {g a} M (e : v = M *ᵥ fst ∘ g) {α} (h : IsInducedByCoords v g α) :
    a • H.map _ α d symbolClass = S ((algebraMap k _ a * M.det) • ιMulti _ d (snd ∘ g)) := by
    erw [smul_eq_push, ← pull_id_eq_push, ← map_pull_eq_pull_map rfl, H.map_id]
    refine pull_cocycleClass (R' := jouanolouRel (pointMap ⟨f⟩)) exists_jouanolouRel_of_unimodular _
      _ (pointMap _) ⟨fun C ↦ ↾fun x ↦ ⟨x.2.1 ᵥ* M.map x.1.1.1⟩, by intros; ext; congrm ⟨fun _ ↦
      $(.symm (map_vecMul ..))⟩⟩ (fun _ x ↦ (dotProduct_mulVec x.2.1 ..).symm.trans ∘ congr(_ ⬝ᵥ
      $(congr(_ ∘ $(hf.trans e)).trans (funext (map_mulVec _ _ _)))).symm.trans) ?_ h
    simp [volumeForm]; intros; erw [det_mul, ← map_det]
    exact congrArg up (.trans (by simp [exteriorMap_iotaMulti, mul_smul, ← smul_comm a]; rfl)
      congr(_ • $((add_zero _).trans (exteriorMap_smul ..))).symm)
  have K i (r : c.baseAlg) m := @T (update (inr ∘ m) i (1, r • m i)) 1 (updateCol 1 i v)
    (by ext; simp [mulVec, dotProduct, update, apply_ite]) 0 fun _ φ ↦ .symm (relFreeAb.mk_eq_zero
    (projSpace.span_eq_top_of_isUnit i (by simp [isUnit_iff_isUnit_fst, HodgeTest.sqZeroExt])))
  simp [H.map, ← cramer_apply, smul_smul, ↓comp_update, comp_def, mul_comm] at K
  rw [(one_smul ..).symm.trans (T 1 (by simp [hf]) hα), T M hM hβ, ← sub_eq_zero,
    ← map_sub, ← ((Pi.basisFun ..).exteriorPower d).sum_repr (_ - _)]
  simpa [basis_repr_apply, ιMulti_family] using sum_eq_zero fun s _ ↦
    (mem_span_range_iff_exists_fun.1 (show _ ∈ span (range v) by
    simp_rw [← Ideal.Quotient.eq] at *; simp [← ha, ← det_mul, map_det, Matrix.map,
      hN]; rfl)).elim fun t e ↦ congr(S ($e • _)).symm.trans (by simp [sum_smul, ← K])
variable (k d)
lemma symbolClass_one : ∃ ω : _ ⋙ freeAb.obj unimodular.toFunctor ⟶ hodgeCoeff, (∀ c v, ∃ w,
  (v.1.1 0).fst • w = (v.1.1 0).snd ∧ ω.app c (.of v) = ⟨.ι _ w⟩) ∧ @symbolClass k _ 1 =
  (relFreeAb.shortExact (unimodular.whisker _)).2.extClass.comp (.mk₀ ω) rfl :=
  (exists_map_extClass_comp (relFreeAb.shortExact _).2 shortExact_cokerBoundary.2 (detCocycle _
  volumeForm) (.mk₀ (𝟙 _)) _ (fromRel exists_jouanolouRel_of_unimodular) rfl).imp fun _ ↦
  .imp (fun a c ⟨⟨v⟩, u⟩ ↦ (exists_jouanolouRel_of_unimodular _ _ u).elim fun ⟨l⟩ h ↦ ⟨l 0 • _, by
  simpa [dotProduct, smul_smul, mul_comm] using! congr($h • (v 0).2), .symm (a c _ _ ⟨⟦.of ⟨(_, _),
  fun _ ↦ h⟩⟧, by with_unfolding_all congrm .of ⟨⟨_, $(funext nofun)⟩, _⟩, congrArg up (by
  simp [volumeForm]; rfl)⟩)⟩) (by simp_all [symbolClass, cocycleClass, push])
@[simp] def affineSpace.snoc : affineSpace k d ⊗ affineSpace k 1 ⟶ affineSpace k d.succ :=
  ⟨fun _ ↦ ↾fun v ↦ ⟨Fin.snoc v.1.1 (v.2.1 0)⟩, by aesop_cat (add simp [affineSpace, comp_snoc])⟩
seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor in
lemma symbolClass_succ [CharZero k] : ∃ h, HodgeH.map (relFreeAb.prod ..)
  (_root_.cup exteriorAlg.mulPairing (@symbolClass k _ d) symbolClass (add_comm ..) :) =
  HodgeH.map (relFreeAb.map (affineSpace.snoc ..) h) symbolClass := by
  refine (symbolClass_one k).elim fun ω ⟨hω, e₁⟩ ↦ e₁ ▸ ⟨?h, by
  let G := (@unimodular k _ 1).whisker sqZeroExt
  let f := sqZeroExt.whiskerLeft (affineSpace.snoc k d)
  let Q := jouanolouRel f ⊓ ⟨({(x, l) | x.2 ∈ G.obj · ∨ l.1 (last d) = 0}), fun φ x ↦ .imp (G.map φ
    ·) (by simpa using! congrArg φ.1 ·)⟩
  have T {B : Ab} {c x} {a b : B} (e : x ∉ G.obj c → a = b) : a ⊗ₜ[ℤ] relFreeAb.mk G x =
    b ⊗ₜ relFreeAb.mk _ x := by_cases (by simp [relFreeAb.mk_eq_zero ·]) (e · ▸ rfl)
  refine (map_cocycleClass (R' := Q) (U' := .whisker (_ ⊔ _) _) exists_jouanolouRel_of_unimodular
    (fun c x a ↦ a.elim (exists_jouanolouRel_of_unimodular _ _ · |>.elim fun l a ↦ ⟨⟨snoc _ 0⟩,
    (sum_univ_castSucc _).trans (by simpa [f]), by simp⟩) fun _ ↦ (exists_jouanolouRel_of_unimodular
    _ _ (?h _ a)).imp (by tauto)) (abTensor.flip.obj (_root_.relFreeAb G)) ((-1) ^ d • 𝟙 _)
    (fun m ↦ desc (fun c ⟨⟨⟨v, x⟩, l⟩, t⟩ ↦ (if a : x ∈ G.obj c then 0 else .of ⟨(v,
    (⟨init <| l · |>.1⟩)), fun i ↦ by simpa [f, show (l i).1 _ = 0 from (t i).2.resolve_left a,
    jouanolouRel, dotProduct, sum_univ_castSucc] using! (t i).1⟩) ⊗ₜ relFreeAb.mk G x) fun _ _ φ _ ↦
    T (by have := G.map φ; split_ifs <;> tauto)) (by intros; exact T (by simp [·]; congrm ⟦.of ⟨⟨_,
    $(funext nofun)⟩, _⟩⟧)) (fun _ _ _ ↦ hom_ext fun _ _ ↦ T (by simp [·]; rfl))
    (detCocycle _ volumeForm)).elim fun y H ↦ (congrArg _ (DirectSum.of_injective
    _ ?_).symm).trans ((comp_assoc _ _ _ _ rfl (by simp)).symm.trans (congr($(H.2).comp _ rfl).trans
    ((exists_map_extClass_comp (shortExact_cokerBoundary (R := Q)).2 ((relFreeAb.shortExact
    G).2.map_of_exact (abTensor.obj _)) ((abTensor.obj _).map ω ≫ exteriorAlg.mulPairing) _
    (desc (fun c ⟨⟨⟨v, x⟩, l⟩, _⟩ ↦ ((-1) ^ d • (detCochain (R := ⊤) volumeForm).app c (.of ⟨(v,
    (⟨init <| l · |>.1⟩)), by simp⟩)) ⊗ₜ .of x) fun _ _ _ _ ↦ .symm congr($(((_ : ℤ) • detCochain
    _).naturality_apply ..) ⊗ₜ _).symm) _ (H.1.trans (hom_ext fun _ _ ↦ T (by simp [·])))).elim fun
    z h ↦ .trans (by exact h.2) ((pull_cocycleClass (R' :=
    Q) exists_jouanolouRel_of_unimodular _ (.id _) f {app _ := ↾(·.2)} (fun _ _ ↦
    (·.1)) (fun c ⟨_, t⟩ ↦ h.1 c _ _ ?_) (by tauto)).symm.trans congr($(id_pull _) _ _)))))
  erw [← comp_of, ← of_comp_homClass, ← cup_of, ← comp_of _ (.mk₀ ω), cup_comp_homClass_right,
    TotalH.cup]
  cases neg_one_pow_eq_or ℤ d <;> simpa [*, TotalH.comp_assoc, -Functor.flip_obj_obj, ← comp_of,
    TotalH.homClass, ← homClass_comp] using! congr((-1 :) ^ d • $(comp_assoc_of_eq
    (extClass_sign_comm (abTensor_shortExact (relFreeAb.shortExact G).2) (@symbolClass k _ d)) _))
  conv => enter [1, _, 1, 2, 2]; erw [sum_app_apply]
  simp
  erw [map_sum, sum_congr rfl fun _ _ ↦ map_zsmul ..]
  simp
  rw [show ∑ _, _ = _ by simpa [sum_smul, sum_tmul, pow_add, mul_zsmul]
    using! congr(($(sum_minor_eq_mul_det _ _ (last _) (t · |>.1)) • volumeForm.app c _) ⊗ₜ _)]
  refine if a : _ then (hω c ⟨_, a⟩).elim fun w e ↦ ⟨_ ⊗ₜ .of ⟨_, a⟩, rfl, congrArg up
    ?_⟩ else ⟨0, by
      simpa [det_eq_zero_of_column_eq_zero _ (t · |>.2.resolve_left a)] using map_zero _⟩
  simp [volumeForm, ExteriorAlgebra.ιMulti, ↓List.ofFn_succ', f, smul_smul, ← e.1,
    mul_comm]; erw [e.2]⟩
  rintro _ _ ⟨⟩ <;> apply eq_top_mono (span_mono _) ‹_› <;> simp <;> tauto
end
section
open CategoryTheory Ideal CommAlgCat Algebra TrivSqZeroExt Matrix Set SqZeroExt NatTrans DualNumber
  Module
variable {k E d} [Field k] {W X : CommAlg k ⥤ Type 1} (u c : W ⟶ X) [Field E] [Algebra E k]
abbrev ConstIfCoincident x := c (of k k[ε]) x = u _ x → x = W.map (fst ≫ structureMap) x
def IsCoincidenceSet (s : Finset _) := (∀ x, ConstIfCoincident u c x) ∧ (∀ w ∈ s, c _ w = u _ w) ∧
  ∀ K, IsField K.1 → ∀ x, c K x = u K x → ∃ w ∈ s, x = W.map structureMap w
lemma exists_isCoincidenceSet [IsAlgClosed k] [hX : IsSepFunctor X] (h : ∀ x,
  ConstIfCoincident u c x) {ι} [Finite ι] (a : ι → EtaleChart d W) (ha : ∀ K, IsField K.1 → ∀ x,
  c K x = u K x → ∃ i, x ∈ (a i).locus K) : ∃ s, IsCoincidenceSet u c s := by
  choose J hJ using fun {A} y ↦ by simpa [← naturality_apply] using hX.1 A (c _ y) (u A y)
  choose o j using @nullstellensatz_exists_le_ker k
  use (finite_iUnion fun i ↦ .dependent_image (@finite_minimalPrimes_of_isNoetherianRing _ _
    (FiniteType.isNoetherianRing k _) (J (a i).point)) fun p m ↦ W.2 (ofHom (o m.isPrime.1))
    (a i).point).toFinset, h
  simp
  use fun _ _ _ m ↦ (· ▸ (hJ ..).2 (m.le.trans (j _)))
  peel ha
  obtain ⟨⟨_, ⟨⟩⟩, _⟩ := this, IsField.isDomain ‹_›
  exact (exists_minimalPrimes_le (J := comap ..) ((hJ ..).1 ‹_›)).imp fun p ⟨m, q⟩ ↦
   (exists_mem_colon_of_tangent rfl (j _) fun v _ l
    r ↦ congr(($((a _).eq_comp_of_map_point_eq _ (h _ ((hJ ..).2
   (m.le.trans l)))) r).2)).elim fun _ l ↦ ⟨m, W.map_comp_apply .. ▸ eq_comp_structureMap_of_ker_le
    (l.1 ⟨·, ·, rfl⟩ |> m.isPrime.2 |>.resolve_left (by tauto) |> q) ▸ rfl⟩
def HasJacobianRatio {X} (u c : W ⟶ restrictAlg E k ⋙ X) d (t n : k) w := ∀ A : EtaleChart d X,
  c _ w ∈ A.locus _ → let ξ (γ : _ ⟶ (restrictAlg ..) (.of k k[ε])) i := (γ (A.coordinate i)).snd
      ∃ N, N.det = n ∧ ∀ v α γ, W.map fst v = w → X.map α A.point = u _ v →
        X.map γ A.point = c _ v → t • ξ α - ξ γ = N *ᵥ (ξ α - ξ γ)
lemma EtaleChart.tangent_mem_range_of_jet {X} (A : EtaleChart d X) {T : FGModuleCat k} (hT : finrank
  k T = d) v : let Y := restrictAlg E k ⋙ X; let f φ := Y.map (ofHom (map (Dual.eval k T φ))) v
    Y.map fst v ∈ A.locus _ → f.Injective → (∀ w, Y.map fst w = Y.map fst v → w ∈ range f) ∧ ∃ D :
      T ≃ₗ[k] _, ∀ φ α, X.map α A.point = f φ → (A.coordinate · |> α |>.snd) = D φ := fun hv h ↦ by
  obtain ⟨⟨⟨γ⟩, ⟨⟩⟩, S : IsSquareZero ((restrictAlg E k).map fst)⟩ :=
    (A.isOpenSub.mem_of_isSquareZero _ · _ hv) (fst_surjective_and_kerIdeal_sq (k := k)),
    fst_surjective_and_kerIdeal_sq (k := k) (M := k)
  have U {α β} a b := (A.injective _).eq_iff.2 (A.lift_unique S a (ext congr($a _) <|
    congrFun b ·) : α = β)
  erw [← funext fun _ ↦ X.map_comp_apply ..] at *
  let B := (0 + LinearMap.pi fun i ↦ (γ.1 _).2).linearEquivOfInjective (by tauto) (by simpa)
  use fun w H ↦ ?_, B, fun _ _ ↦ (A.injective _ · ▸ rfl)
  obtain ⟨_, ⟨⟩⟩ := A.isOpenSub.mem_of_isSquareZero _ S w (H ▸ hv)
  refine (B.surjective _).imp fun φ ↦ U (A.injective _ ?_)
  simpa [SqZeroExt.fst, ← fstHom_comp_map (.applyₗ φ), -fstHom_comp_map] using! H.symm
lemma IsTangentPoly.hasJacobianRatio {X} {c u : W ⟶ restrictAlg E k ⋙ X} {w P} (hW :
  IsChartCovered d W) (hP : IsTangentPoly d c u w P) (h₁ : P.eval 1 ≠ 0) : (∀ t, HasJacobianRatio u
  c d t (P.eval t / P.eval 1) w) ∧ ∀ v, W.map fst v = w → ConstIfCoincident u c v := by
  obtain ⟨_, v, T, hT, ⟨⟩, h, hu, p⟩ := hP
  obtain ⟨⟨S, ⟨⟩⟩, V, _⟩ := (⟨(1 - T).equivOfDetNeZero (by grind [one_smul]), by simp⟩ : T ∈ range
    (1 - ·.1)),
    EtaleChart.tangent_mem_range_of_jet _ hT v (hW.1 _ (Field.toIsField k) _).choose_spec h.of_comp
  use fun t A hw ↦ ?_, (V · · |>.elim fun | φ, rfl, e => ((by simpa using h (e.trans (hu φ)).symm)
    ▸ .symm (W.map_comp_apply .. ▸ by congr with _ <;> simp)))
  obtain ⟨_, D, G⟩ :=
    (by simpa only [← naturality_apply] using A.tangent_mem_range_of_jet hT (c _ v) :) hw h
  use (D ∘ₗ ((1 - t • (1 - S.1)) * S.symm.1) ∘ₗ D.symm).toMatrix', by
    simp [S.det_coe_symm]; grind [one_smul, sub_sub_cancel], fun v _ _ ↦ by
    rintro ⟨φ, ⟨⟩⟩ a b; simp [G φ _ b, G _ _ (hu φ ▸ a), ↓map_neg] ∘ V v
end
section
open CategoryTheory Classical Function Ideal TrivSqZeroExt relFreeAb
seal H.map
attribute [local simp] Field.toIsField mem_offPoints_iff isOpenSub_offPoints ComesFromPoints
variable {k} [Field k] {X X' d e R R'} {U : Subfunctor X} {g m} {ξ :
  HodgeH (relFreeAb U) d} (a : EtaleChart e X) {z : X (.of k k)}
lemma EtaleChart.isCohomEquiv_univPoint : ∃ μ : a.R ⟶ HodgeTest.sqZeroExt ⟨_, Fin e⟩,
  LeftInverse fst μ ∧ ∀ {d f S}, S = (@unimodular k _ d).preimage (pointMap ⟨f⟩) →
  ∃ h, IsCohomEquiv hodgeCoeff (map (U' := someUnitLocus (c := ⟨_, _⟩) f) (𝟙 _) h ≫ map (U :=
  S.whisker _) (pointMap ⟨μ⟩) le_rfl) := a.exists_univPoint.imp fun _ ⟨s, j⟩ ↦
  (forall_and.1 j).elim fun j _ ↦ ⟨s, @fun _ f _ e ↦ funext (s ∘' f) ▸ e ▸ ⟨fun _ _ ⟨i, h⟩ ↦
  projSpace.span_eq_top_of_isUnit i (isUnit_iff_isUnit_fst.2 h), Iff.mpr (IsCohomEquiv.comp_iff
  (isCohomEquiv_of_le _ (isCohomEquiv_someUnitLocus <| by apply unimodular.2 ·.baseProj ·.2)))
  (relFreeAb.excision _ .of_top_le (m := mono_of_app_injective j) rfl)⟩⟩
lemma EtaleChart.symbolClass_eq_of_cutsOutLocus {f g : Fin d → a.R} {P x} (D : CutsOutLocus _ P x f)
  (F : CutsOutLocus X' P x g) : symbolClass.map (relFreeAb.map _ D.preimage_fieldLocus_not.le) =
  symbolClass.map (relFreeAb.map _ F.preimage_fieldLocus_not.le) := by
  have hg : _ = span (.range g) := eq_of_forall_ge_iff
    (·.mk_ker ▸ (D _ (CommAlgCat.ofHom (Quotient.mkₐ ..))).trans (F ..).symm)
  choose M hM using fun _ ↦ mem_span_range_iff_exists_fun.1 (hg ▸ mem_span_range_self)
  obtain ⟨⟨μ : _ →ₐ[k] TrivSqZeroExt a.R (_ → a.R)⟩, e : LeftInverse _ μ,
    V⟩ := a.isCohomEquiv_univPoint
  apply ((V D.preimage_fieldLocus_not).2 _).1; erw [← H.map_comp,
    symbolClass_transformation (f := μ ∘ f) (g := μ ∘ g) _ _ _ M M _ (funext
    _).symm, one_smul, H.map_comp] <;>
    first | tauto | (simp [comp_def, e _] <;> assumption) | rw [hg]
  simp [← hM, snd_sum, e _, Ideal.sum_mem, mul_mem_right, mem_span_range_self]
lemma hodge_excision {u : X' ⟶ X} [Mono u] (ho : IsOpenSub (.range u)) (H : ∀ K, IsField K.1 →
  ∀ x ∉ Subfunctor.range u K, ∃ O, IsOpenSub O ∧ x ∈ O K ∧ O ≤ U) {U'} (e : U' = U.preimage u) :
  IsCohomEquiv hodgeCoeff (HodgeTest.sqZeroExt.whiskerLeft (map _ e.le)) := excision (U := U.whisker
  _) ((restrictAlong _).map u) (hasZariskiDescent_hodgeCoeff (isLocallyEverything_of_open_cover
  (byCases (by tauto) <| .imp (by tauto) ∘ H · · ·))) congr(.whisker $e _)
@[local simp ←] lemma HodgeH.map_comp {N N' M} (α : M ⟶ N') β (x : @HodgeH k _ N d) :
    x.map (α ≫ β) = (x.map β).map α := .symm (H.map_comp ..).symm
@[simp] lemma HodgeH.map_zero {N} : ξ.map (N' := N) 0 = 0 := ((H.mapHom ..).flip ξ).map_zero
def IsLocalSymbol ξ y P g (m : k) := ∃ᵉ (D : CutsOutLocus X P y g) (h), HodgeH.map (map (pointMap
  (A := R) y) (U := U) h) ξ = m • .map (map _ D.preimage_fieldLocus_not.le) (@symbolClass k _ d)
lemma IsLocalSymbol.map {y P} (h : IsLocalSymbol ξ y P g m) φ :
    IsLocalSymbol ξ (@X.map R R' φ y) P (φ ∘ g) m := ⟨(by simpa [span_le] using h.1 · <| φ ≫ ·), by
  rw! (transparency := .all) [← pointMap_comp _ (pointMap y)]
  exact ⟨_, by simpa using! congr($(h.2.2).map (relFreeAb.map _ le_rfl))⟩⟩
def IsPointSum (s : Set _) (n : _ → k) (ξ : HodgeH (relFreeAb U) d) := ∀ z ∈ s, ∃ᵉ (a :
  EtaleChart d X) (g), z ∈ a.locus _ ∧ IsLocalSymbol ξ a.point (ComesFromPoints {z}) g (n z)
private lemma π_map {C : Type _} [CategoryTheory.Category C] {V V' : C ⥤ Type 1} {U : Subfunctor V} {U' : Subfunctor V'} {u : V' ⟶ V} {h' : U' ≤ U.preimage u} : relFreeAb.π _ ≫ relFreeAb.map u h' = freeAb.map u ≫ relFreeAb.π U := rfl
noncomputable def pointClass d (z : X _) :=
  HodgeH.map (q := d) (π (offPoints {z})) (epsilon (IsPointSum {z} 1))
lemma exists_isOpenSub_le_offPoints [IsSepFunctor X] (h : z ∈ U _) ⦃K⦄ (hK : IsField K.1) ⦃x⦄ (n :
  x ∉ U K) :
  ∃ O, IsOpenSub O ∧ x ∈ O K ∧ O ≤ offPoints {z} := by have := U.map (V := K) structureMap h; aesop
lemma EtaleChart.exists_isLocalSymbol [IsSepFunctor X] {g} (h : CutsOutLocus X (ComesFromPoints {z})
  a.point g) (w : z ∈ a.locus _) : ∃ ξ : HodgeH (relFreeAb (offPoints {z})) e, IsLocalSymbol ξ
  a.point (ComesFromPoints {z}) g 1 ∧ IsPointSum {z} 1 ξ := ((hodge_excision a.isOpenSub
  (exists_isOpenSub_le_offPoints w) rfl e).2 _).imp fun _ l ↦ (⟨·, by rintro _ ⟨⟩; tauto⟩) ⟨h, _, l⟩
lemma IsPointSum.map_eq_smul_pointClass [IsSepFunctor X] {n ξ} (h : IsPointSum {z} n ξ) :
  .map (π (offPoints {z})) ξ = n z • pointClass d z := by
  have ⟨a, g, hz, h⟩ := h z rfl
  have ⟨b, g₀, e, h'⟩ := epsilon_spec ⟨_, (a.exists_isLocalSymbol h.1 hz).choose_spec.2⟩ _ rfl
  have ⟨c, E⟩ := a.exists_locus_eq_inf b; have ⟨⟨_, e₁⟩, _, e₂⟩ := E ▸ c.point_mem_locus
  obtain ⟨⟨D, _, h⟩, F, _, u⟩ := e₁ ▸ h.map _, e₂ ▸ h'.map _
  rw [c.symbolClass_eq_of_cutsOutLocus D F, ← u.trans (one_smul ..), ← map_smul] at h
  simp [(hodge_excision c.isOpenSub (exists_isOpenSub_le_offPoints (by aesop)) rfl _).1 h,
    pointClass]
lemma IsPointSum.map_eq_sum_pointClass [IsSepFunctor X] {s : Finset _} {n} (h :
  IsPointSum s n ξ) (e : U = offPoints s) : .map (π _) ξ = ∑ z ∈ s, n z • pointClass d z := by
  induction' s using Finset.induction with z s hz ih generalizing U
  simp [(freeAb.hom_ext fun _ _ ↦ mk_eq_zero (e ▸ nofun) : π U = 0)]
  cases show U = offPoints {z} ⊓ offPoints s by aesop (add simp [offPoints, fieldLocus])
  obtain ⟨x, y : HodgeH .., E : y.map (relFreeAb.map _ (by simp)) = _⟩ :=
    ((hodge_excision (u := (offPoints s).ι) (by simp) (exists_isOpenSub_le_offPoints (z :=
    z) (by simpa)) (by ext _ ⟨⟩; apply_rules [and_iff_left]) d).2 (ξ.map (map _
    le_rfl))).imp fun x E ↦ ((LongExactSeq.contravariant
    ((shortExact_triple ..).2.map_of_exact (restrictAlong _)) _).exact_f_g d (ξ - .map (map
    (𝟙 _) (by simp)) x)).1 ((HodgeH.map _).sub_mem_ker_iff.2 (by simpa using! E.symm))
  have O {t A B l l' x y} t' (e : ξ = .map (map (𝟙 X) (U := A) l) x + .map (map (𝟙 X) (U := B)
      l') y) : B = offPoints t' → t = ↑(insert z s) \ t' → IsPointSum t n x := by
    rintro rfl rfl w o; peel 4 h w o.1
    exact ⟨_, by simpa [e, -ComesFromPoints, (hom_ext fun _ _ ↦ mk_eq_zero fun K _ l ↦
      (mem_offPoints_iff l).1 (X.map_comp_apply .. ▸ by_contra (exists_isOpenSub_le_offPoints (z :=
      w) (by aesop) l · |>.elim (by tauto))) : map _ this.1 ≫ map _ l' = 0)] using this.2⟩
  cases add_eq_of_eq_sub' E
  simp [hz, ih (O _ (add_comm ..) rfl _), (O s rfl _ _).map_eq_smul_pointClass, π_map]
end
section
seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor
open CategoryTheory MonoidalCategory Ideal Set EtaleChart
attribute [-simp] Fin.natAdd_eq_addNat IsScalarTower.coe_toAlgHom'
lemma exists_diagonal_class {k} [Field k] {X d} : @HasAtlas k _ d X → ∃ δ : HodgeH
  (relFreeAb (offDiagonal X)) d, ∀ K z, IsField K.1 → ∃ a O, IsOpenSub (X := X ⊗ X) O ∧ (z, z) ∈ O
  K ∧ ∀ᵉ (B) (p ∈ O B), ∃ φ ψ, X.map φ (point a) = p.1 ∧ X.map ψ a.point = p.2 ∧ IsLocalSymbol δ p
  (fun _ x ↦ x.1 = x.2) (fun i ↦ φ (a.coordinate i) - ψ (a.coordinate i)) 1 := fun ⟨_, a, ha⟩ ↦ by
  choose e h using exists_eq_iff_coordinate_eq ∘' a
  let V i := away (.prod ..) (e i)
  let l {i} : _ ⟶ (V i).R := CommAlg.toAway _
  have Q {n W V} (e : locus (d := n) V = W) := hodge_excision (U := (offDiagonal X).preimage W.ι)
    (V.comap W.ι ⟨_, e ▸ V.point_mem_locus⟩ rfl).isOpenSub (e ▸ by rintro _ _ ⟨_, _, ⟨⟩⟩; tauto) rfl
  choose x E using fun i ↦
    ((Q rfl d).2 _).imp (q := (IsLocalSymbol (X := (V i).locus.toFunctor) · ⟨_, point_mem_locus _⟩
    (fun _ x ↦ x.1.1 = x.1.2) _ 1)) fun _ ↦ (⟨fun C α ↦ by simpa [span_le, -map_sub] using! ((h i _
    (l ≫ α)).trans (and_iff_right ((CommAlg.exists_toAway_comp_iff ..).1 ⟨α, rfl⟩))).symm, _, ·⟩)
  have G {i B p χ} h : IsLocalSymbol (R := B) (x i) ⟨p, χ, h⟩ .. := h.rec ((E i).map _)
  have N {K} k z : ∃ i, (z, z) ∈ (V i).locus _ := (ha K k z).imp fun i m ↦
    ((range_pointMap_prod ..).ge _ ⟨m,
    m⟩).elim fun _ E ↦ E.subst ((mem_locus_away ..).2 ((h ..).1 (E ▸ mem_diagonal z :)).1)
  refine (relFreeAb.exists_glued_class _ {A | ∃ i c, (locus c).whisker _ = A ∧ c.locus ≤
    (V i).locus} (fun _ ⟨i, c, e, h⟩ _ ⟨_, b, E, _⟩ ↦ (c.exists_locus_eq_inf b).elim (⟨i, ·, · ▸
    ⟨congr($e ⊓ $E), by order⟩⟩)) (fun _ ⟨i, c, E, h⟩ m n ↦ E ▸ (h _ c.point_mem_locus).elim fun _
    e ↦ ⟨fun _ _ ↦ ((c.isCohomEquiv_univPoint.choose_spec.2 ((G e).1.preimage_fieldLocus_not.trans
    (by simp [EtaleChart.restrict, Pi.sub_def, away, EtaleChart.prod, ← map_sub]
        rfl))).2.comp_iff.2 (Q rfl) _).1 ((hodge_vanishing_along_diagonal (EtaleChart.restrict _ e
    c.injective c.isOpenSub).etale n).1 ..)⟩) _ (⟨·, _, rfl, le_rfl⟩)
    (hasZariskiDescent_hodgeCoeff (isLocallyEverything_of_open_cover fun _ k ⟨z, _⟩ ↦ by_cases
    (· ▸ (N k z).elim (⟨_, isOpenSub <| V ·, ·, le_sup_of_le_left (le_sSup ⟨_, rfl⟩)⟩)) (⟨_,
    isOpenSub_offDiagonal, mem_offDiagonal_of_ne k ·, le_sup_right⟩))) x fun i j ↦
    ((V i).exists_locus_eq_inf (V j)).elim fun c e ↦ (e ▸ c.point_mem_locus
    :).elim fun ⟨_, m⟩ ⟨_, n⟩ ↦ ?_).imp fun δ H K z k ↦ (N k z).elim (⟨a ·, _, isOpenSub _, ·,
    fun | _, _, ⟨⟨χ⟩, rfl⟩ => ⟨tensorInl ≫ l ≫ χ, tensorInr ≫ l ≫ χ, ?_⟩⟩)
  simpa [← map_sub] using ⟨rfl, rfl, by peel 2 G rfl; erw [← H,
    ← δ.map_comp _ (relFreeAb.map _ le_rfl), relFreeAb.map_comp] at this; tauto⟩
  obtain ⟨⟨D, _, u⟩, F, _, v⟩ := G m, G n
  refine (Q e _).1 (.trans ?_ (u.trans (c.symbolClass_eq_of_cutsOutLocus D F ▸ v ▸ ?_))) <;>
    erw [← (x _).map_comp _ (relFreeAb.restrict _ (by simp)), relFreeAb.map_comp] <;> rfl
end
section
open CategoryTheory CommAlgCat Field H HodgeTest Ideal RingHom CartesianMonoidalCategory
  MonoidalCategory
variable {k} [Field k] [CharZero k] {d} {W X : CommAlg k ⥤ Type 1} [HasAtlas d X]
def scaledGraph t (u c : W ⟶ X) :=
  lift (scaleModule t _ ≫ sqZeroExt.whiskerLeft u) (sqZeroExt.whiskerLeft c)
def constMap (z : X (of k k)) : W ⟶ X where app A := ↾fun _ ↦ X.map structureMap z
seal H.map
lemma exists_diagonal_local_terms {d} (hX : HasAtlas d X) : ∃ δ : HodgeH (freeAb.obj (X ⊗ X)) d,
  ∀ {E} [Field E] [CharZero E] [Algebra k E] {W} [IsSepFunctor W] [IsChartCovered d W] (u c :
  W ⟶ _) s t (n : _ → E), IsCoincidenceSet u c s → (∀ w ∈ s, HasJacobianRatio u c d t (n w) w) →
  (∃ ξ : HodgeH (_root_.relFreeAb (offPoints s)) d, IsPointSum s n ξ) ∧ H.map _ (freeAb.map
  (scaledGraph t u c)) d δ.baseChange = ∑ w ∈ s, n w • pointClass d w := (exists_diagonal_class
  hX).imp' (.map (relFreeAb.π _)) fun δ hδ E _ _ _ W _ _ u c s t n ⟨hr, h, hs⟩ hJ ↦ by
  have N {U} (h : IsOpenSub U) : (U.preimage (lift u c)).whisker _ ≤
    (U.whisker _).preimage (scaledGraph t u c) := fun C _ m ↦ h.mem_of_isSquareZero C.baseProj
    fst_surjective_and_kerIdeal_sq _ (congr(($((X.map_comp_apply ..).trans
    (congrArg _ (u.naturality_apply ..).symm)), _) ∈ _).mp (U.map C.baseProj m))
  refine ⟨⟨H.map _ (relFreeAb.map (U' := (offPoints s).whisker _) _ fun C _ _ ↦
    N (@isOpenSub_offDiagonal _ _ X _).whisker_restrictAlg C
    ((isOpenSub_offDiagonal.whisker_restrictAlg.preimage _).fieldLocus_le _ fun _ _ ↦
    (mem_offDiagonal_of_ne (X := X) · (by tauto)))) d _, ?I⟩, IsPointSum.map_eq_sum_pointClass ?I
    rfl ▸ by erw [HodgeH.baseChange_map, ← map_comp, eq_comm, ← map_comp]; rfl⟩
  refine fun w hw ↦ (hδ _ (c _ w) (toIsField E)).elim fun A ⟨O, hO, hw', L⟩ ↦ ?_
  obtain ⟨⟨Q, hQ, hT⟩, a, ⟨⟨ζ : _ ⟶ _⟩, rfl⟩, ha, v⟩ := hJ w hw A (by have := L _ _ hw'; tauto),
    ((hO.whisker_restrictAlg.preimage (lift u c :)).inf (isOpenSub_offPoints (s :=
    s \ {w}))).exists_chart_le (toIsField E)
    ⟨congr(($(h w hw), _)) ▸ hw', by simp [mem_offPoints_iff, toIsField, ComesFromPoints]⟩
  obtain ⟨⟨φ, ψ, hφ, hψ, Z, -⟩, ν, F, V⟩ := L _ _ ha, a.isCohomEquiv_univPoint
  have M {v : W ⟶ restrictAlg k E ⋙ X} {B C φ y} h (α : B ⟶ C) :=
    (X.map_comp_apply φ _ A.point).trans ((congrArg _ h).trans (v.naturality_apply α y).symm)
  let f := (φ ∘ A.coordinate : _ → a.R) - by exact ψ ∘ A.coordinate
  have Z {C} (α : a.R ⟶ C) : span _ ≤ ker α.hom ↔ _ := (Z ..).trans (eq_comm.trans
    ((c.naturality_apply α a.point).congr (u.naturality_apply α a.point) :).symm)
  obtain ⟨b, o, hb⟩ := exists_mem_colon_of_tangent rfl ((Z ζ).2 (by tauto)) fun p _ l r ↦
    congr(($(a.eq_comp_of_map_point_eq _ (hr _ ((Z _).1 l))) r).2)
  have hk := by simpa using (map_eq_top_iff_fields _ (𝟙 _)).2 fun K κ i l ↦ v K κ i ((hs
    K i _ ((Z _).1 (le_colon.trans l))).imp fun z ⟨m, e⟩ ↦ ⟨⟨m, fun q ↦ hb (by
    simpa [a.eq_comp_of_map_point_eq _ (q ▸ e), i.nontrivial] using l o)⟩, e⟩)
  refine ⟨a, f, ⟨_, rfl⟩, ?D, fun C p l K κ hK ⟨z, hz, e⟩ ↦ (offPoints _).map _ v K κ hK
    ⟨z, ⟨hz, (l K κ hK ⟨z, ·, e⟩)⟩, e⟩, ((V (CutsOutLocus.preimage_fieldLocus_not ?D)).2 _).1 ?_⟩
  exact fun C α ↦ ⟨(by simp [ComesFromPoints, eq_comp_structureMap_of_ker_le <| hk.trans ·]; rfl),
    (Z α).2 ∘ by simp_all [ComesFromPoints]⟩
  obtain ⟨_, _, h₁, h₂, Y, _, e'⟩ := L _ _ (N hO.whisker_restrictAlg _ (Subfunctor.map _ ν ha))
  obtain ⟨rfl, rfl, e'⟩ := A.injective _ ((M (M hφ _) _).trans h₁.symm),
    A.injective _ ((M hψ _).trans h₂.symm), by simpa -dsimp using congr(($e').baseChange (k := E))
  have eF i : _ = f i := congr($(F _) - $(F _))
  erw [eq_comm, map_push, ← map_comp, eq_comm, ← map_comp, ← map_comp]
  refine (congrArg (H.map _ · d _) (relFreeAb.hom_ext fun C σ ↦ ?_)).trans ((map_comp ..).trans
    ((congrArg (H.map _ (relFreeAb.map (U' := someUnitLocus _) (U := .whisker (.preimage _
    (pointMap _)) (sqZeroExt ⋙ _)) (pointMap ⟨𝟙 _⟩) fun C σ ⟨i, e⟩ ↦ Y.preimage_fieldLocus_not.ge _
    (projSpace.span_eq_top_of_isUnit i (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (eF i ▸ e :)))) d)
    e').trans ((map_comp ..).symm.trans ((congrArg _ (witnessed.pull_cocycleClass
    exists_jouanolouRel_of_unimodular exists_jouanolouRel_of_unimodular _ (𝟙 _) {app _ := ↾(·.2)} ?_
    ?_ ?_)).trans (symbolClass_transformation (by tauto) ?_ (funext eF)
    (1 : Matrix (Fin d) _ _) (Q.map (algebraMap ..))
    _ (by ext; simp; erw [F]) (fun i j ↦ hk ?_) (hQ ▸ by simp [map_det]))))))
  exact congr(relFreeAb.mk _ $(W.map_comp_apply .. ▸ (scaledGraph ..).naturality_apply ..))
  (iterate 4 tauto); show ζ (t • (ν _).snd j - (ν _).snd j - _) = 0
  let μ := (withIndex _ ⋙ sqZeroExt).map ζ ≫ ofHom (TrivSqZeroExt.map (.proj j))
  have S y : (μ y).2 = ζ _ := zero_add _
  simpa [← S, f] using! congr($(hT _ _ _ (W.map_comp_apply .. ▸
    by congr with _; exact (add_zero _).trans congr(ζ $(F _))) (by tauto) (M hψ (ν ≫ μ))) i)
lemma exists_diagonal_pointClass : ∃ δ, ∀ z, (∃ ξ : HodgeH (_root_.relFreeAb (offPoints {z})) d,
  IsPointSum {z} 1 ξ) ∧ .map (freeAb.map (lift (constMap z) (𝟙 X))) δ = pointClass d z ∧
  ∀ {W} [IsSepFunctor W] [IsChartCovered d W] (u : W ⟶ X) s, IsCoincidenceSet (constMap z) u
  s → .map (freeAb.map u) (pointClass d z) = ∑ w ∈ s, pointClass d w :=
  (exists_diagonal_local_terms ‹_›).imp' _ fun δ h z ↦ by
  have h W [IsSepFunctor W] [IsChartCovered d W] :=
    (h (W := W) (constMap z) · · 1 1 · fun _ _ _ _ ↦ ⟨1, by simp⟩)
  have e :=
    h X (𝟙 _) {z} ⟨fun | _, rfl => (map_map_structureMap ..).symm, by simp [constMap]; tauto⟩
  simp at *
  use Finset.coe_singleton z ▸ e.1, e.2; peel h; erw [← this.2, ← e.2, ← map_comp]
  congr; exact freeAb.hom_ext (Y := _ ⋙ _)
lemma pointClass_eq_of_functions_eq {z z'} (e : ∀ g : X ⟶ affineSpace k 1, (g _ z).1 0 =
  (g _ z').1 0) : pointClass d z = pointClass d z' := by
  repeat rw [← (exists_diagonal_pointClass.choose_spec _).2.1]
  apply AddMonoidHom.eqOn_closureM _ (kunneth _)
  rintro _ ⟨a, n, h, x, y, rfl⟩
  have ⟨_, r⟩ := @projective_and_eval_bijective _ _ (@sqZeroExt k _ ⋙ 𝟙_ _) hodgeCoeff ⟨_, Empty⟩ ⟨⟩
    fun _ ↦ ⟨fun ⟨_⟩ ⟨_⟩ _ ↦ congrArg _ (hom_ext (by ext) nofun), fun _ ↦ ⟨⟨structureMap, 0⟩, rfl⟩⟩
  repeat erw [← map_comp, cup_map _ x y h (freeAb.map (sqZeroExt.whiskerLeft (constMap _))) (𝟙 _)
    (γ' := freeAb.map (λ_ _).inv ≫ freeAb.prod (_ ⋙ 𝟙_ _) (_ ⋙ X)) freeAb.hom_ext]
  congr 2; cases a <;> [rw [← x.mk₀_homEquiv₀_apply]; subsingleton]
  repeat erw [H.map, Abelian.Ext.bilinearComp_apply_apply, Abelian.Ext.mk₀_comp_mk₀]
  exact congrArg _ (r.1 (ULift.down_injective (formBasis.ext_elem fun i ↦
    e (freeAb.homEquiv X _ ((𝟭 _).whiskerRight (H := _ ⋙ sqZeroExt) ⟨fun _ ↦
    ofHom (TrivSqZeroExt.inlAlgHom ..), by intros; ext; exact TrivSqZeroExt.ext rfl (by ext ⟨⟩)⟩
    (freeAb X) ≫ (withIndex _).whiskerLeft (Abelian.Ext.homEquiv₀ x)) ≫ ⟨fun A ↦ ↾(⟨fun _ ↦
    formBasis.repr ·.1 i⟩), by intros; ext; congrm ⟨fun _ ↦ $(repr_withIndex_map ..)⟩⟩))))
end
section
seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Functor relFreeAb Classical
set_option backward.isDefEq.respectTransparency false
lemma IsPointSum.cup_pointClass {k} [Field k] [CharZero k] {d X Y} [HasAtlas d X] [HasAtlas 1 Y]
  z : .map (freeAb.prod X Y) (cup (@exteriorAlg k _).mulPairing (pointClass d z.1)
  (pointClass 1 z.2) (add_comm ..)) = pointClass _ z := by
  have m {R X Y U W T S} s t h l x y := (HodgeH.map_comp (relFreeAb.map (@pointMap _ _ (X ⊗ Y) R (s,
    t)) (sup_le_sup h l)) (relFreeAb.prod U W) _).symm.trans (cup_map (γ' :=
    (@HodgeTest.sqZeroExt k _).whiskerLeft (relFreeAb.map (lift (𝟙 _) (𝟙 _)) le_rfl ≫ relFreeAb.prod
    T S)) (mulPairing _) x y (add_comm 1 d) (whiskerLeft _ (relFreeAb.map (pointMap s) h))
    (whiskerLeft _ (relFreeAb.map (pointMap t) l)) (hom_ext (U := (T ⊔ S).whisker _)))
  obtain ⟨⟨a, g, ez, e⟩, b, g', ew, e'⟩ := epsilon_spec (exists_diagonal_pointClass.choose_spec _).1
    z.1 rfl, epsilon_spec (exists_diagonal_pointClass.choose_spec _).1 z.2 rfl
  have ⟨ξ, L, G⟩ := (a.prod b).exists_isLocalSymbol (g := Fin.snoc (g · ⊗ₜ 1) (1 ⊗ₜ g' 0))
    (fun _ α ↦ .symm (exists_eq_left.trans (Prod.ext_iff.trans (by simpa -dsimp [ComesFromPoints,
    Ideal.span_le, Set.subset_def, and_comm] using! ((e.1 _ (_ ≫ α)).and (e'.1 _ (_ ≫ α))).symm))))
    ((range_pointMap_prod ..).ge _ ⟨ez, ew⟩)
  use have hU := by rintro _ _ (h | h) _ _ l ⟨_, ⟨⟩, e⟩ <;> use h _ _ l ⟨_, rfl, by injections⟩
    (cup_map _ _ _ _ (whiskerLeft _ (π _)) (whiskerLeft _ (π _)) rfl).symm.trans ((HodgeH.map_comp
      (π _) (relFreeAb.prod ..) _).trans ((hodge_excision (a.prod b).isOpenSub (fun _ l _ n ↦ by
    obtain ⟨_, h⟩ | ⟨_, h⟩ := (not_and_or.1 (range_pointMap_prod a b ▸ n)).imp
      (exists_isOpenSub_le_offPoints ez l ·) (exists_isOpenSub_le_offPoints ew
    l ·) <;> exact ⟨_, h.1.preimage _, by tauto⟩) rfl _).1 ((m ..).trans ((congrArg _
    (congrArg₂ (cup _ · · _) (e.map _).2.2 (e'.map _).2.2)).trans (by
    erw [one_smul, one_smul, ← m]
    simpa -dsimp [(symbolClass_succ ..).2, ← HodgeH.map_comp, pointMap_comp] using!
      congr($(L.2.2).map (relFreeAb.map (𝟙 (reprBy _)) fun x _ ↦ (hU x ·))).symm)) : _ = (ξ.map
      (relFreeAb.map (𝟙 _) hU)).map _) ▸ by simp [← HodgeH.map_comp, π_map,
      G.map_eq_smul_pointClass]))
end
section
open thickeningOver CategoryTheory CommAlgCat MvPolynomial NNRat TotalH PadicTest WittVector freeAb
  CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
variable {p k} [Field k] [EmbeddedInQpBar p k]
noncomputable def Gm.ofCoord : freeAb (@unimodular k _ 1).toFunctor ⟶ forget₂ .. ⋙ Gm :=
  desc (fun _ v ↦ ⟨(by
  simpa [unimodular, Set.range_unique] using v.2 : IsUnit (v.1.1 0)).unit⟩) (by simp [ext]; tauto)
noncomputable def thickeningOver.oneSubMu : genericCoeff ⟶ thickeningOver ⋙ forget₂ .. ⋙ Gm :=
  ⟨fun c ↦ AddCommGrpCat.uliftFunctor.map
  (AddCommGrpCat.ofHom (MonoidHom.toAdditiveRight (.toHomUnits ⟨⟨(1 - mulMu c ·.toAdd), by simp⟩, by
    simp [mul_sub, ← mulMu_proj_mul, proj_mulMu, sub_sub]⟩))), fun _ _ _ ↦ AddCommGrpCat.ext fun _ ↦
  Gm.ext.2 ((_root_.map_sub ..).trans (congrArg₂ _ (map_one _) (map_mulMu ..))).symm⟩
lemma thickeningOver.shortExact_oneSubMu : ∃ w,
  ShortComplex.ShortExact ⟨oneSubMu, whiskerRight proj _, w⟩ := by
  choose s i e using exact_mulMu_proj
  exact shortExact_of_app (fun c _ _ h ↦ congr(⟨$(i c (sub_right_inj.1 (Gm.ext.1 h)))⟩)) (fun c
    ⟨u⟩ ↦ .trans (by simpa [Gm.ext,
    sub_eq_zero.trans eq_comm, eq_comm.trans sub_eq_iff_comm] using! e c (1 - _)) ULift.exists.symm)
    fun c ⟨u⟩ ↦ (s ..).elim fun _ h ↦
    ⟨⟨((IsNilpotent.isUnit_quotient_mk_iff ⟨2, c.ker_thickeningProj_sq⟩).1
    (.of_map (RingHom.quotientKerEquivOfSurjective (s c)) _ ⟨u, h.symm⟩)).unit⟩, Gm.ext.2 h⟩
lemma hodgeTateMap_symbolClass : hodgeTateMap 1 symbolClass =
  restrictToPairs (((relFreeAb.shortExact _).2.map_of_exact (restrictAlong _)).extClass.comp
  (H.map _ (genericOver.whiskerLeft Gm.ofCoord) 1 shortExact_oneSubMu.2.extClass) rfl) := by
  choose ω hω eω using symbolClass_one k
  simpa [eω] using!
    (comp_assoc_of_eq (Comparison.pull_comp_restrictAlong ..) _).symm.trans ((congrArg _ (by
    simp [Comparison.pull, H.map, H.push, Abelian.Ext.toTotalH]
    erw [comp_assoc_of_eq (Cocycle.cohomClass_naturality ⟨_,
      _⟩ _ _ (𝟙 _) (by intros; erw [Category.comp_id])).symm, comp_id, ← homClass_comp_of]
    refine Cocycle.cohomClass_comp_eq_extClass _ (shortExact_oneSubMu.2.map_of_exact (restrictAlong
      _)) _ _ (fun _ ↦ Gm.ofCoord _ ≫ Gm.map (CommRingCat.ofHom (.pullbackFst ..))) (fun _ ↦ ?_)
      fun X _ f ↦ AddCommGrpCat.hom_ext (FreeAbelianGroup.lift_ext _ _ fun ⟨⟨v⟩, u⟩ ↦ (hω _ ⟨_,
      unimodular.map (X.toSqZero) u⟩).elim fun m ⟨h, e⟩ ↦ ?_) <;> simp [← Functor.map_comp]
    congr with ⟨⟩; tauto
    erw [e, ← sub_eq_iff_eq_add', desc_of, Gm.ext]
    show _ * (1 - (thickeningOver.mulMu ..) (-(contraction f.2 (.ι _ m)).algebraMapInv)) = _ + _
    erw [mul_one_sub, ← mulMu_proj_mul, proj.naturality_apply, (v 0).2, ← h, map_smulₛₗ]
    simp [contraction]; rfl
    simp [Cocycle.cocycle_comp, ↓NatTrans.naturality_assoc])).trans
    (Comparison.pull_comp_restrictAlong (relFreeAb.shortExact _).2.extClass ..))
lemma thickeningOver.teichmullerLift_epsTilt c : teichmullerLift c (algebraMap _ _ epsTilt) = 1 +
  mulMu c 1 := by simp [map_one c.thickeningProj ▸ mulMu_thickeningProj c 1, mu]; erw
  [MonoidHom.comp_apply, ← map_teichmuller]; rfl
seal genericAlg thickeningOver
lemma projSpace.exists_hodgeTateMap_pointClass_line : ∃ η, hodgeTateMap 1 (pointClass 1
  (@affinePoint k _ 1 _ 0 0)) = restrictToPairs η ∧ ∀ {N n} [HasFlatValues N] (x : H N genericCoeff
  n), _root_.cup (genericAlg ⋙ forget₂ ..).mulPairing x η (add_comm 2 n) = 0 → x = 0 := by
  have D {V U} [s : @IsChartCovered k _ 1 V] o : PairRestrictBijective (relFreeAb U) :=
    (((Comparison.restrict ..).isClosedClass HodgeTatePair.toGeneric).2 _ (relFreeAb.shortExact U).2
    (s.comap U.ι (by simpa)).pairRestrictBijective).1 s.pairRestrictBijective
  obtain ⟨ξ, ⟨hX, h₁, E⟩, G⟩ := (stdChart k 1 0).exists_isLocalSymbol (z := affinePoint 0 0) (g :=
    X) (fun _ _ ↦ by simp [ComesFromPoints]; erw [mk_eq_mk_iff_cross_mul]; simp +contextual
    [Set.range_unique]) ((mk_mem_stdChart_iff _).2 isUnit_one)
  obtain ⟨⟨ξT, hξ⟩, G⟩ :=
    (D isOpenSub_offPoints).exists_hodgeTateMap_eq 1 ξ, G.map_eq_smul_pointClass.symm
  apply_fun hodgeTateMap 1 at E G; simp [hodgeTateMap_map, *, hodgeTateMap_symbolClass,
    ← restrictToPairs_map] at *
  refine ⟨_, G, fun x s ↦
    DirectSum.of_injective _ ((comp_id.trans x.toTotalH.map_id).symm.trans ?_)⟩
  let A : tilt ⋙ reprBy (monoidAlg ℚ≥0) ⟶ _ ⋙ affineSpace k 1 :=
    ⟨(↾fun t ↦ ⟨fun _ ↦ teichmullerLift · (t.1.hom (.single 1 1))⟩),
    by intros; ext; with_unfolding_all exact congr(⟨fun _ ↦ .mk _ $(.symm ((IsLocalization.map_eq
    (powers_le_comap_powers ..) _).trans (congrArg _ (map_teichmuller ..))))⟩)⟩
  let b := A ≫ whiskerRight proj _
  have g c i t : b c ⟨charTwist epsPow (cond i coeHom (-coeHom)) ≫ t.1⟩ = b c t := by
    simp [b, A, affineSpace, charTwist, funext_iff, -AddMonoidAlgebra.coe_algebraMap]
    erw [((proj c).hom.1.1.comp
      ((teichmullerLift ..).comp ((algebraMap ..).1.comp epsPow))).mem_ker.1, one_mul]
    cases i <;> simp [teichmullerLift_epsTilt, proj_mulMu]
  let T : affineSpace k 1 ⟶ reprBy (stdChart k 1 0).R := ⟨fun _ ↦ ↾(⟨ofHom <| aeval ·.1⟩), by
    intros; ext; congrm ⟨ofHom $((comp_aeval ..).symm)⟩⟩
  let φ : twoDiscs ⟶ _ := sigma.desc fun i ↦
    b ≫ whiskerLeft _ (T ≫ pointMap (stdChart k 1 (i.1.rec 1 0)).point)
  have U c t : (A c ⟨discToTorus coeHom ≫ t⟩).1 0 * (A c ⟨discToTorus (-coeHom) ≫ t⟩).1 0 = 1 := by
    simp [A, ← map_mul, ← AddMonoidAlgebra.one_def]
  let W : _ ⟶ _ ⋙ freeAb unimodular.toFunctor := projFirst (B :=
    pointOrTorus) ≫ desc (.of ⟨_, span_eq_top_of_isUnit 0 <| .of_mul_eq_one _
    <| U · ·.1⟩) (by intros; exact .symm congr(.of $(Subtype.ext (A.naturality_apply ..).symm)))
  let ε {X} : freeAb X ⟶ genericCoeff := desc (fun c _ ↦ ⟨(1 : genericAlg c)⟩)
    (by intros; exact congrArg _ (map_one (genericAlg.map _).1).symm)
  obtain ⟨_, _, _, _, _, J, I⟩ := by
    apply toda_squares (oneSub_comp_gluing epsPow) (origin ⟨true⟩) (hom_ext (by simp -dsimp))
      ((relFreeAb.shortExact unimodular).2.map_of_exact (restrictAlong _)) shortExact_oneSubMu.2
      (projFirst ≫ freeAb.map b) (-W ≫ whiskerLeft _ Gm.ofCoord) (projFirst ≫ ε) (whiskerLeft
      _ Gm.ofCoord) (-W ≫ whiskerRight proj _) <;> apply freeAb.hom_ext <;> rintro c
      ⟨⟨⟨⟩⟩⟩ <;> simp [W]
    exacts [rfl, congr(.of $((g _ true _).symm)), sub_eq_of_eq_add (Gm.ext.2 (.symm (show (1 - mulMu
      c _) * _ = _ by
      erw [desc_of, desc_of, desc_of, IsUnit.unit_spec]
      simp [A, charTwist, pointOrTorus, AddEquiv.ulift, -AddMonoidAlgebra.coe_algebraMap,
        -Bool.cond_eq_ite]
      erw [AddMonoidAlgebra.lift_single]
      simp [-AddMonoidAlgebra.coe_algebraMap]
      erw [AlgHom.commutes, teichmullerLift_epsTilt]; rfl)))]
  have m A ψ := @relFreeAb.mk_eq_zero _ _ _ (offPoints {affinePoint 0 0}) A _ ((offPoints _).map ψ
    (a := (stdChart k 1 1).point)
    fun K ψ h ⟨_, rfl, e⟩ ↦ by have := h.nontrivial; simpa using (mk_mem_stdChart_iff ..).1 ⟨_, e⟩)
  obtain ⟨j', hj⟩ := by
    refine J _ _ (freeAb.map φ - origin ⟨false⟩ _ ≫ freeAb.map φ) (whiskerLeft _ (relFreeAb.π _))
      (whiskerLeft _ (relFreeAb.map T (fun _ v l ↦ hX.preimage_fieldLocus_not.ge _
      (.trans (congrArg _ (congrArg _ (funext (aeval_X _)))) l)) ≫ relFreeAb.map _ h₁)) (hom_ext ?_)
      (hom_ext (by simp [-Bool.cond_eq_ite]; simp [freeAb, φ, sigma.desc, g, -Bool.cond_eq_ite]))
        (hom_ext ?_) <;> rintro c ⟨⟨⟨⟩⟩⟩ <;> simp
    exacts [congr(.of $(mk_eq_mk_iff_cross_mul.2 (by
      simp; erw [aeval_X, aeval_X, mul_comm, ← map_mul (proj c).1, U]; simp))),
      (m ..).trans (m ..).symm, sub_eq_self.2 (m ..)]
  have q := congr(pullbackAlong $hj ξT.toTotalH).symm
  erw [← homClass_comp_homClass_comp, homClass_comp_of, whiskerLeft_comp, H.map_comp, (@D _ _
    (.comap _ (EtaleChart.isOpenSub _)) (isOpenSub_offPoints.preimage _)).injective_restrictToPairs
    E, ← H.map_comp, ← whiskerLeft_comp, show _ ≫ _ = 𝟙 _ from relFreeAb.hom_ext fun _ _ ↦
    congrArg (relFreeAb.mk unimodular ⟨·⟩) (funext (aeval_X _)), H.map_id] at q
  erw [map_zero, ← show tensorPoint ε _ ≫ (genericAlg ⋙ forget₂ ..).mulPairing = 𝟙 _ by
    ext _ ⟨⟩; exact congrArg _ ((mul_one_add ..).trans (by simp)), homClass_comp,
    TotalH.comp_assoc_of_sq (naturality ..), (I _ _ _ (subsingleton_coker_gluing
    isCohomEquiv_gluing_generic _)).1 _ (tensorPoint (𝟙 _) _) _ 0, map_zero]
  erw [← map_homClass, ← TotalH.map_comp_assoc, q, ← homClass_comp_homClass_comp, homClass_comp_of,
    TotalH.map_comp_assoc, (comp_assoc_of_eq rfl _).trans (cup_of ..), s] <;> simp +arith
end
section
open CategoryTheory Finset CartesianMonoidalCategory CommAlgCat Fin Polynomial
set_option backward.isDefEq.respectTransparency false
seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor in
lemma projSpace.hodgeTateMap_pointClass_ne_zero {p k} [Field k] [EmbeddedInQpBar p k] {d} z :
  hodgeTateMap d (pointClass (X := projSpace k d) d z) ≠ 0
  := exists_hodgeTateMap_pointClass_line.rec fun η ⟨hη, P⟩ ↦ by
  have c {d} : ∀ z, pointClass d z = pointClass d (@affinePoint k _ d _ 0 0) :=
    Quot.ind fun ⟨⟨u⟩, h⟩ ↦ pointClass_eq_of_functions_eq fun g ↦
    have n {B C z} (ψ : B ⟶ C) x (e : z =
      _ := by erw [mk_eq_mk_iff_cross_mul]; simp [forall_fin_succ] at * <;>
     grind) := congr($((congrArg _ e).trans (g.naturality_apply ψ x)).1 0)
    if hj : _ then (eq_C_of_toLaurent_eq _ _ ((n (ofHom toLaurentAlg) (mk (cons X (C ∘ u ∘ succ))
    (Exists.rec span_eq_top_of_isUnit hj))).symm.trans
      (n (ofHom (LaurentPolynomial.invert.toAlgHom.comp toLaurentAlg)) (affinePoint 0
      (monomial 1 ∘ u ∘ succ)) rfl))).rec fun _ e ↦ (n (ofHom (aeval (u 0))) _).trans ((congr(
    aeval _ $e.1 = aeval _ $e.2).mpr (by simp)).trans (n (ofHom (aeval 0)) _).symm) else n (𝟙 _) _
  have M {d} (z := @affinePoint k _ d _ 0 0) : hodgeTateMap d.succ (.map (freeAb.map (lineProductMap
    k d)) (pointClass d.succ (affinePoint 0 0))) = 0 ↔ hodgeTateMap d (pointClass d z) = 0 := by
    obtain ⟨⟨ξ, hx⟩, δ, h⟩ := IsChartCovered.pairRestrictBijective.exists_hodgeTateMap_eq d
      (pointClass d z), exists_diagonal_local_terms (hasAtlas k _)
    have C : IsCoincidenceSet (𝟙 _) (constMap z) {z} := by simp [IsCoincidenceSet,
      ConstIfCoincident, constMap, @map_map_structureMap k]
    have S t : HodgeH.scale t (.map (freeAb.map (lift (𝟙 _) (constMap z))) δ.baseChange) = _ :=
      (H.map_comp ..).symm.trans (congr(H.map _ $freeAb.hom_ext _ _).trans (h _ _ _ t _ C fun _ _ A
      _ ↦ ⟨.scalar _ t, rfl, fun _ _ γ _ _ c ↦
      A.eq_comp_of_map_point_eq _ (C.1 _ c.symm) ▸ by simp; repeat erw [sub_zero]⟩).2)
    have w l (n : hodgeTateMap l (pointClass d z) ≠ 0) :=
      Nat.pow_right_injective .refl (EmbeddedInQpBar.toCharZero.1
      (by simpa [smul_left_inj n, hodgeTateMap_scale] using
      congr((2 : k) ^ l • hodgeTateMap l $(S 1) = hodgeTateMap l $(S 2))))
    have F {B v u} : lineProductMap k d B (v, u) = (projSpace ..).map structureMap
      (affinePoint 0 0) → ∀ [IsLocalRing B], ∃ j, (v, u) = _ := v.induction_on₂ u fun _ _ e _ ↦
      (exists_eq_single_of_mul_eq_zero _ _ (by simpa using mk_eq_mk_iff_cross_mul.1 e ·.succ 0)).2
    rw [(exists_diagonal_pointClass.choose_spec _).2.2 (lineProductMap ..) _ ⟨fun (_,
      _) e ↦ by rw [(F e).choose_spec, map_map_structureMap], forall_mem_image.2 fun _ _ ↦
      mk_eq_mk_iff_cross_mul.2 (by simp [forall_fin_succ]), fun _ K _ e ↦ let := K.toField
      exists_mem_image.2 ((F e).imp (⟨mem_univ ·, ·⟩))⟩]
    simp_rw [← IsPointSum.cup_pointClass, c, ← c z, map_sum, hodgeTateMap_map, hodgeTateMap_cup]
    rw [sum_eq_single d] <;> simp +contextual [Finset.ext_iff, hx, hη, Not.imp_symm (w _),
      ← Nat.cast_smul_eq_nsmul k, -Nat.cast_add]
    refine ⟨fun _ ↦ P ξ (IsChartCovered.pairRestrictBijective.injective_restrictToPairs.comp
      (IsCohomEquiv.of_isIso ..).1 ((restrictToPairs_map (freeAb.prod ..) _).trans
      ((congrArg _ ((congrArg _ (Comparison.pull_cup abTensor_hom_ext
      ..)).trans (TotalH.cup_of ..).symm)).trans (by simpa)))) ▸ map_zero _, (by simp [·])⟩
  refine mt (M z).2 (d.rec (mt (congrArg (PairH.map (freeAb.map (lift (constMap (affinePoint 0 0))
    (𝟙 _))))) fun e ↦ ?_) fun _ ↦ mt (by simp [hodgeTateMap_map, M.1 ·]))
  erw [← hodgeTateMap_map, ← HodgeH.map_comp, ← freeAb.map_comp, show _ ≫ _ = 𝟙
    _ by ext _ ⟨⟩; erw [mk_eq_mk_iff_cross_mul]; simp, freeAb.map_id, H.map_id, hη, map_zero,
    map_eq_zero_iff _ IsChartCovered.pairRestrictBijective.injective_restrictToPairs] at e
  simpa using PadicTest.eq_zero_of_algebraMap_genericRing ⟨Unit, _, Pi.constRingHom ..⟩ 1
    congr(($(show 𝟙 genericCoeff = 0 by simpa [cup, e] using P (.mk₀ _)).1 _ ⟨_⟩).1)
end
open CategoryTheory Function CommAlgCat CutsOutLocus IsUnimodCoords projSpace MvPolynomial Finset
  RingHom Fin CommAlg IsLocalization Away Field Submodule Algebra Ideal EtaleChart
  CartesianMonoidalCategory MonoidalCategory
attribute [local instance] FractionRing.liftAlgebra FormallyEtale.of_isSeparable
lemma linearIndepOn_hodgeTateMap_pointClass {p k} [Field k] [EmbeddedInQpBar p k] [IsAlgClosed k]
  {R} [Algebra R.1 k] {Y d} [hX : HasAtlas d (algPointsOf k R Y)] (hE : HasProjEmbedding Y.hom) :
  LinearIndepOn k (hodgeTateMap d) (.range (pointClass
  (X := algPointsOf k R Y) d)) := hE.rec @fun _ L _ hL ↦ by
  simp_rw [linearIndepOn_iff_notMem_span, ← Set.image_compl_preimage, Set.image_image,
    mem_span_image_iff_exists_fun]
  rintro _ ⟨z, rfl⟩ ⟨t, ht, n, H⟩
  have := Fact.mk hL
  choose a ζ w₀ ez hw₀ using exists_chart_coords L z (toIsField _)
  obtain ⟨_, _, q, m, hζ⟩ := isReduced_of_etale a.etale, FiniteType.isNoetherianRing k a.R,
    @exists_minimalPrimes_le _ _ (.colon ⊥ {(1 : a.R)}) _ (ker_isPrime ζ.1) (by aesop_cat)
  obtain ⟨_, γ, hψ⟩ := m.1.1, exists_eq_colon_of_mem_minimalPrimes m
  have ⟨ψ, V⟩ : ∃ ψ, ker ψ = q := ⟨algHom k .., q.ker_algebraMap_residueField⟩
  simp [← V, Ideal.ext_iff] at *
  choose n Λ e h using
    exists_isNoetherNormalization (k := k) (ne_iff.2 (hw₀.2.imp fun _ h ↦ (h.map ψ).ne_zero))
  let β := γ * evalForms Λ w₀ 0; let c := a.away β
  obtain ⟨⟨κ, ⟨⟩⟩, w, hw, w₁⟩ := (exists_toAway_comp_iff β (ofHom ψ)).2 (by
    simpa [β, comp_aeval_apply, *, ← sq] using hψ 1), (⟨_, hw₀.map_unit_smul (toAway β)
    (isUnit_of_dvd β (dvd_mul_left ..)).unit⁻¹, by simp [Units.smul_def]; rfl⟩ : ∃ w,
    IsUnimodCoords L _ w ∧ evalForms Λ w 0 = 1)
  obtain ⟨I, hg, u, E⟩ := injective_of_map_algebraMap_zero (M := .powers β) _ κ.1.1 fun r e ↦
    (isUnit_of_dvd β ⟨_, rfl⟩).mul_right_cancel (by simp [← map_mul, (hψ r).1 e]),
    hw.comp κ, (hw.comp κ).exists_unit_smul_eq ((hw₀.comp _).comp κ)
  obtain ⟨_, h, _, m, B⟩ := I.isDomain, eq_inv_smul_iff.2 E ▸ h _,
    hg.exists_mem_open_of_isUnit c.isOpenSub ⟨_, rfl⟩
  let y := aeval (R := k) (evalForms Λ w ∘ succ)
  algebraize [y.1, (κ.hom.comp y).1, κ.1.1, κ.1.1.comp y.1]
  let S := MvPolynomial (Fin n) k
  let M := IntermediateField.mk (.restrictScalars k (.algebraicClosure S q.ResidueField))
    fun _ ↦ .inv
  obtain ⟨⟨_, ⟨⟨φ⟩, ⟨⟩⟩, e⟩, _⟩ := @B (of k M) (⟨_, IsIntegral.isAlgebraic <| h.2 _ (cons 1 X) _
    .refl (funext (by simp [forall_fin_succ, y, *])) ·⟩) (.of_ker M.val 1 (by simp) .refl) (by
    simpa [← M.val.injective.ne_iff]), (faithfulSMul_iff_algebraMap_injective
    ..).2 (.of_ker y fun a _ ↦ by
    choose G c D using exists_homogenization (isHomogeneous_X _ 0) (a.rename succ) .refl
    simpa [D, comp_def, S, bind₁_rename] using h.1.map (aeval (cons (1 : S) X)) c (by
      erw [evalForms_map, ← comp_aeval]; simp [aeval_rename, y, *]))
  have G := IsAlgebraic.mk fun r ↦ (isAlgebraic_algebraMap_iff I).1
    (congr($(c.eq_comp_of_map_point_eq _ ((e.comp (ofHom M.val)).ext hg).symm) r ∈ M).mpr (φ.1 r).2)
  have ⟨δ, hδ, et⟩ := @exists_etale_of_isEtaleAt _ _ _ _ y.1.toAlgebra
    (.of_restrict_scalars_finitePresentation k ..) ⊥ _ (by
    delta IsEtaleAt Localization.AtPrime; rw [primeCompl_bot]; exact .comp _ (FractionRing S) _)
  let U := { c.away δ with coordinate := _, etale := congr($(comp_aeval _ (toAway δ).1).1.Etale).mp
                             (etale_algebraMap.2 et) }
  have e₃ := (c.mem_locus_away δ κ).2 (by simpa using! I.ne hδ)
  have o {A x v} (h : IsUnimodCoords L x v) h' ⦃T⦄ (b : T ⊆ (pointClass d ⁻¹' {pointClass d z})ᶜ) :
    x ∈ offPoints T A := fun K φ I ⟨y, m, e⟩ ↦ let := I.toField
    b m (pointClass_eq_of_functions_eq (hg.exists_function_const · |>.elim fun _ H ↦
      ez ▸ H (hw₀.comp ζ) (.of_ker _ _ hζ (E ▸ .smul
    (.id ..) _ .refl)) ▸ structureMap.1.injective (by simpa [e] using! H (h.comp φ) (.map _ h'))))
  choose b _ _ B T using hg.exists_mem_open_of_isUnit U.isOpenSub e₃
  obtain ⟨_, oU, F, q, r⟩ := e₃.choose.1.1.domain_nontrivial,
    o hw (.of_ker κ.1 1 (by simp [← I.eq_iff]) .refl),
    (G.1 (aeval w b)).exists_nonzero_coeff_and_aeval_eq_zero (by simpa [← I.ne_iff])
  obtain ⟨⟨⟩, ⟨q, m⟩, _, f, D⟩ := equiv_iff_eq.1 ⟨(c.away δ).nonempty_basis_kaehler.some.indexEquiv
    U.nonempty_basis_kaehler.some⟩,
    not_forall.1 (funext.mt q), exists_homogenization (Λ 0).2 (F.eval₂ (bind₁ (Λ ·.succ)).1 b) .refl
  let Q := projSpace.affinePoint (A := of k k) 0 q
  let Γ : Subfunctor (_ ⊗ projSpace k d) := ⟨fun _ x ↦ ∃ v h, IsUnimodCoords L x.1 v ∧ x.2 =
    projSpace.mk (evalForms Λ v) h,
    fun φ _ ⟨v, _, a, e⟩ ↦ ⟨φ ∘ v, evalForms_map Λ φ.1 _ ▸ ⟨_, a.comp φ, congrArg _ e⟩⟩⟩
  let π := Γ.ι ≫ fst ..
  have : Mono π := mono_of_app_injective (by
    rintro _ ⟨⟨⟩, _, _, a, ⟨⟩⟩ ⟨⟨⟩, _, _, a', ⟨⟩⟩ ⟨⟩
    congrm ⟨(_, $(mk_eq_mk_iff_exists_unit.2 ((a.exists_unit_smul_eq a').imp fun _ ↦
      (· ▸ (evalForms_smul _).symm)))), _⟩)
  let O := (offPoints t).preimage π ⊓ fieldLocus fun K x ↦ constMap Q K x = x.1.2 →
    x.1.1 ∈ U.locus K
  let j := O.ι ≫ π
  have hj {A} := injective_of_mono (j A)
  let C := U.comap j ⟨⟨(_, _), _, span_eq_top_of_isUnit 0 (by simp [*]), hw.comp _, rfl⟩,
    (offPoints _).2 _ (oU ht), fun _ _ _ _ ↦ ⟨_, rfl⟩⟩ rfl
  have P {A y} b : y ∈ C.locus A := (U.locus_comap j rfl).ge _
    (U.isOpenSub.fieldLocus_le _ (y.2.2 · · · (map_map_structureMap _ Q ▸ (congrArg _ b).symm)))
  obtain ⟨hV, s, hs⟩ := IsChartCovered.comap _ (h := ⟨fun K hK ↦ let := hK.toField
    by rintro ⟨⟨x⟩, _, H, ⟨a⟩⟩
       obtain ⟨c, κ, w, ⟨⟩, a'⟩ := exists_chart_coords L x hK
       obtain ⟨⟨u, ⟨⟩⟩, j, e⟩ := (a'.comp κ).exists_unit_smul_eq a, exists_isUnit_of_span_eq_top H
       exact ⟨(c.away _).comap π ⟨(_, _), _, span_eq_top_of_isUnit j
         (by simpa using (c.mem_locus_away ..).1 (point_mem_locus _)), a'.comp _, rfl⟩ rfl,
         (locus_comap _ π rfl).ge _ ((c.mem_locus_away ..).2 (by simpa [u.smul_def] using e))⟩⟩)
    (O.range_ι.substr (.inf (isOpenSub_offPoints.preimage _) (isOpenSub_fieldLocus fun _ _ ↦
    (IsSepFunctor.exists_ideal ..).elim fun _ h ↦
    (U.isOpenSub ..).imp' _ fun _ g _ φ f ↦ let := f.toField
    by erw [← map_map_structureMap φ Q, h, g, ← isAtom_top.ne_bot_iff_eq le_top, Ne,
      map_eq_bot_iff_le_ker, sup_le_iff, not_and]))),
    exists_isCoincidenceSet (constMap Q) (O.ι ≫ Γ.ι ≫ snd ..) (fun y b ↦ by
    obtain ⟨⟨ψ : U.R ⟶ _⟩, ⟨⟩⟩ := P b
    erw [← Functor.map_comp_apply, (U.lift_unique (π :=
      SqZeroExt.fst) fst_surjective_and_kerIdeal_sq ?_ fun j ↦ ?_ : _ ≫ _ = ψ)] <;> try rfl
    have := mk_eq_mk_iff_cross_mul (v := ψ ∘ _).1 b j.succ 0
    simp [w₁] at this ⊢; erw [this]; rfl) ![C] fun _ _ _ ↦ (⟨0, P ·⟩)
  have E {X} [HasAtlas d X] x := @(exists_diagonal_pointClass (X := X).choose_spec x).2.2 _
    ⟨fun A a b ↦ (hX.exists_ideal A (j.app A a) (j.app A b)).imp fun _ h B φ ↦
      hj.eq_iff.symm.trans (by erw [j.naturality_apply, j.naturality_apply]; exact h B φ)⟩ hV
  have J x t a := E x j t ⟨fun _ e ↦ hj (by erw [j.naturality_apply, e, map_map_structureMap]; rfl),
    a⟩
  exact (IsChartCovered.pairRestrictBijective.exists_hodgeTateMap_eq ..).elim fun η l ↦
    hodgeTateMap_pointClass_ne_zero Q (l ▸ by simp [(h.pullback_injective
    hg (O := O) (fun V a ↦ ⟨⟨_, _, a, rfl⟩, o a V ht, fun K φ I e ↦ let := I.toField
    (mk_eq_mk_iff_exists_unit.1 e.symm).rec fun u e ↦ ((T ..).ext (a.map_unit_smul φ u) ▸ B (V.smul
      ..) (.mk0 _ fun H ↦ m (by simpa [aeval_bind₁ _, *, congrFun (((evalForms_smul _).trans
      (congrArg _ _)).trans e), ← comp_def, aeval_algebraMap_apply, F.eval₂_eq_sum_range,
      sum_range_succ'] using V.smul φ.hom u f (IsHomogSolution.refl.map _ f
      (by simpa [*, F.aeval_def, F.eval₂_eq_sum_range, aeval_bind₁ w]
      using! r)))) :)⟩) (hV.pairRestrictBijective.injective_restrictToPairs (by
    simp_rw [restrictToPairs_map, ← l, ← hodgeTateMap_map, E _ _ _ hs, map_zero, map_sum]
    exact sum_eq_zero fun y h ↦ (P (hs.2.1 _ h)).elim fun ζ a ↦ by
      rw [← sum_singleton (pointClass d), ← J (j.app _ y) {y} ⟨fun _ h ↦ by
        cases mem_singleton.1 h; simp [constMap]; rfl, fun K _ x e ↦
        ⟨y, mem_singleton_self y, hj (e.trans (j.naturality_apply _ y).symm)⟩⟩,
        not_ne_iff.1
        (oU .rfl _ (_ ≫ ζ.1) (toIsField _) ⟨_, ·, by simp [← a]; rfl⟩)]
      simpa [← hodgeTateMap_map, fun i : t ↦ (J _ ∅ ⟨nofun, fun K hK x e ↦ ((mem_offPoints_iff hK).1
        x.2.1 ⟨_, i.2, e⟩).elim⟩).trans sum_empty] using congr(PairH.map (freeAb.map j) $H).symm)) :
          η = 0)])
open AlgebraicGeometry Polynomial Functor
set_option backward.isDefEq.respectTransparency false
lemma ellAdicCohom.woods_hole {p A E k d h I} [CommRing A] [Field E] [CharZero E] [Algebra A E]
  [Field k] [IsAlgClosed k] [EmbeddedInQpBar p k] [Algebra E k] {R : Subalgebra A E} {W Y :
  Over (Spec (.of R))} [IsProper Y.hom] {u} {b : I →₀ k} (hX : HasAtlas d (algPointsOf E _ Y)) (hW :
  HasAtlas d (algPointsOf k _ W)) (hE : HasProjEmbedding W.hom) (hF : h ≤ d → ∀ q ≤ d, ∀ x :
  HodgeH _ q, (b.linearCombination k fun i ↦ hodgeTateMap h (x.map
  (freeAb.map ((algPoints E _).map (u i : W ⟶ Y)))).baseChange) = 0) : IsNullFamily u b d h := by
  intro c S P hP
  obtain ⟨⟨φ, _⟩, ⟨δ, hδ⟩, ⟨_, a, _⟩, L, e⟩ := Module.exists_dual_forall_apply_eq_one
    (linearIndepOn_hodgeTateMap_pointClass hE), exists_diagonal_local_terms hX, hW.2,
    (LinearMap.pi (@leval k
    _)).dualMap_surjective_of_injective (fun _ _ ↦ funext ∘ congrFun) (Polynomial.lcoeff k h)
  let D u : algPointsOf k _ W ⟶ restrictAlg E k ⋙ algPointsOf E _ Y := (algPoints ..).map u
  let Φ t (i : b.support) : type_of% δ →+ HodgeH (freeAb (algPointsOf ..)) _ :=
    (H.map _ (freeAb.map (scaledGraph t (D (u i)) (D c))) d).comp HodgeH.baseChange
  have T := (hP · · |>.elim (IsTangentPoly.hasJacobianRatio (c := D c) hW.isChartCovered))
  choose s _ B A using fun i : b.support ↦ exists_isCoincidenceSet (D (u i)) _ (hX :=
    isSepFunctor_algPoints) (fun _ e ↦ (T ⟨i, _⟩ (by congrm _ ≫ $e.1)).2 _ rfl e) a (by tauto)
  have hδ i t : Φ t i δ = _ := (hδ _ _ _ _ _ (by tauto) (T ⟨i, ·⟩ congr($(B _ _ ·).1) |>.1 t)).2
  have e := (congr($e <| · * Polynomial.C ·))
  simp [LinearMap.pi] at e
  refine (Set.ext fun _ ↦ ULift.down_inj.trans ⟨(by simpa using A _ _ (Field.toIsField k) _ ·),
    B _ _ ∘ by simp⟩ : S = univ.sigma s) ▸ ⟨finite_toSet _, .trans (by
    simp [*, ↓finsum_mem_coe_finset, ← sum_fn, mul_sum, sum_sigma, division_def, mul_assoc,
    AddMonoidHom.pi]) ((∑ i, b i.1 • L.toAddMonoidHom.comp
    (.pi ((φ ∘ₗ hodgeTateMap d).toAddMonoidHom.comp <| Φ · i))).ker.1.closure_le.2 ?_ (kunneth δ))⟩
  intro δ ⟨q, _, _, x, _, r⟩
  have F t i : Φ t i δ = .map (freeAb.map (CartesianMonoidalCategory.lift (𝟙 _) (𝟙 _)) ≫
    freeAb.prod ..) _ := (congrArg _ (((congrArg _ r).trans (HodgeH.baseChange_map ..)).trans
    (congrArg _ ((@HodgeTest.baseComparison k _ E _ _).pull_cup abTensor_hom_ext x ..)))).trans
    ((H.map_comp ..).symm.trans (cup_map (Functor.mulPairing _) x.baseChange _ _
    (HodgeTest.scaleModule t _ ≫ Functor.whiskerLeft _ (freeAbMap (D _)))
    (Functor.whiskerLeft _ (freeAbMap (D c))) freeAb.hom_ext))
  simpa [F, e, H.map_comp, hodgeTateMap_map (_ ≫ _), hodgeTateMap_cup, hodgeTateMap_scale, ← sum_fn,
    AddMonoidHom.pi,
    -LinearMap.smul_apply, -LinearMap.coe_smul, ← @eval_X_pow k, -Polynomial.eval_pow] using!
    congrArg (φ ∘ₗ PairH.map _ ∘ₗ _) ∘ (sum_attach ..).trans ∘ (hF · q (by omega) x)
seal ellAdicCohom
open Matrix Module ellAdicCohom LinearMap Flat Filter IsEigenQuotient ModuleCat.Algebra Int
attribute [local simp] Model.cosetSum cosetFn smul_sum baseChange_comp
  ValuationSubring.valuation_eq_one_iff
lemma Model.exists_galois_rep {E} [Field E] [CMBase E] {a d₀} [HasQuadSubfield _ E] {𝔑 ν R}
    (X : Model (Fin a) d₀ 𝔑 ν R) {ℓ} [NeZero a] (hN : IsNeat (Fin a) 𝔑) [ThePrime ℓ] [Algebra E Ω] M
    (hM : ∀ w, IsSafe 𝔑 w → M ≤ w.1.primeCompl) [_root_.IsLocalization M R] [PadicIso ℓ] (θ :
  SafePlace 𝔑 → _) J (hJ : ∀ u ∈ J, 0 ≤ u ∧ OccursInWeight a ν θ u.toNat) : ∃ ρ : PadicRep _ ℓ,
  Continuous ρ.rep ∧ ∀ w, SphericalClause ρ.rep
  OccursIn (if algebraMap E ℂ = · then J else 0) w.1.1 (heckePoly w.1.1.q a (ιℓ <| θ w ·)) := by
  rcases X.smooth, X.proper, X.projective, X.reduction,
    IsLocalization.isNoetherianRing M R inferInstance
  have := (X.covering · |>.smoothOfRelativeDimension_baseChange X.d)
  have ⟨_, _, _⟩ : IsCharted X.Z R ∧ IsCharted X.Z Ω ∧ ∀ i, IsCharted (X.W i) Ω := by
    and_intros <;> intros <;> exact ⟨(hasAtlas_algPoints X.d).exists_isCharting⟩
  choose hV V using fun n i ↦ transfer (X.covering i) ℓ n
  choose l p _ using fun w : SafePlace 𝔑 ↦
    (Eventually.all (X.eventually_translate ∅ <| heckeIsogeny_mem_GUPlus w.1 ·)).exists
  choose T hT' ht hW using fun n : Set.Iic (X.d + X.d) ↦ exists_commuting_tau_ops (hV n) (V n) p
  have e n w b := congr((baseChangeHom ℤ_[ℓ] Bcris .. ∘ₗ restrictScalarsₗ ..) $(ht n w b))
  simp [LinearMap.ext_iff, -Subtype.forall, heckeSum] at e ht
  have hT i s (g : Gal(Ω/E)) : Commute (T i s) ((galoisAction ..) g) :=
    LinearMap.ext fun x ↦ hV _ (l s.1) (by simp [ht, map_galoisAction])
  obtain ⟨N, r, F, ⟨h₃, H⟩, hr⟩ := exists_isEigenQuotient (ιℓ ∘ ↿θ) hT (continuous_galoisAction · E)
  use ⟨r⟩, hr, fun w A hA ↦ ?_
  have hR r : algebraMap (CommRingCat.of R) Ω r ∈ A :=
    A.mem_of_valuation_le_one _ ((IsLocalization.surj M r).rec
    fun x e ↦ le_of_mul_le_of_one_le_left (by simpa using! A.valuation_le_one ⟨_, congr(algebraMap
    R Ω $e ∈ A).mpr (algebraMap_ringOfIntegers_mem ..)⟩) (not_lt.1 (hM _ w.2 x.2.2 ∘ (hA _).1)))
  have hcr [PadicPlaceEmbedding E A ℓ] i := (isCrystalline_and_linearFrob_rel E hR i
    (X.m ∘ ![]) 0 1 0 (by simp [CongruenceRelation, Cancels]) nofun).1
  obtain ⟨⟨t, f, -, hp, _, hq⟩, C⟩ := w.1.1.1.exists_prime_and_absNorm_eq_pow,
    X.congruence _ w.2 _ (algebraMap _ Ω ⁻¹' A.nonunits) (hA · |>.2) (p w)
  rw [heckePoly, ← hA, ← @fact_iff t.Prime] at *; norm_cast at *
  refine ⟨⟨fun _ _ _ ↦ Units.ext (toLin'.injective (ext_on_range H.1 fun _ ↦ (h₃ ..).trans (by
    simp [*, galoisAction_eq_one_of_inertia hR _ hp]))), isCrystalline ⟨by tauto, H⟩ (hcr ·)⟩,
    fun he γ s hs u hu z ↦ ?_, fun s hs ↦ ⟨fun h ↦ ?_, @fun he _ k o ↦ ?_⟩⟩
  · simp [apply_ite] at hu
    obtain ⟨⟨h, rfl⟩, hO⟩ := (hJ u hu.2).imp_left le.dest
    let ε := ιℓ.trans s.toRingEquiv
    let : EmbeddedInQpBar ℓ ℂ := {ε.toRingHom.toAlgebra with}
    refine (exists_word_kill_of_jump_eq_zero ⟨by tauto, H⟩ (hcr ·) hs (by tauto) hT' z).rec fun c
      ⟨_, n⟩ ↦ hO _ (ε.symm ∘ c) (ε.injective (by simpa [map_list_prod])) fun b ↦
      X.isNullHecke_of_isNullFamily hN ((c.support.eventually_all.2 fun L _ ↦ .all (hW · ℂ L _
      b.2.1)).mono fun l a m ↦ woods_hole (hasAtlas_algPoints _) (hasAtlas_algPoints _)
      (X.projective l) fun hh q hq x ↦ (exists_hasHodgeTateWeight hR (fun r ↦ congr(ε
      ($(hu.1) r)).trans (by simp [ε])) X.d ε.symm ε.right_inv (x.map (freeAb.map
      ((algPoints ..).map (X.m m))))).rec fun v ⟨Θ, hv, K⟩ ↦ .trans ?_ ((sum_congr rfl fun L hL ↦
      congrArg (ε.symm (c L) • ·) (a L hL ⟨_, add_le_add hq hh⟩ (.mk' (Θ <| ·.restrictScalars _
      |>.baseChange _ v) (by simp)))).trans ?_))
    · simp [← K, HodgeH.map_comp]
    simpa [Finsupp.linearCombination, Finsupp.sum, c.support.sum_comm, smul_comm (ε.symm _)]
      using congr(cosetSum (fun g ↦ Θ (baseChange _ _ $(n ⟨_, _⟩ v hv))) b.1)
  · refine toLinAlgEquiv'.injective (ext_on_range H.1 fun ⟨i, x⟩ ↦ ?_)
    simp [↓Polynomial.C_mul', -cast_mul]
    conv_lhs => enter [2, b]; erw [mul_smul, cast_smul_eq_zsmul, ← map_pow (matrixRep r),
      h₃, ← H.2.1 _ (w, b), ← _root_.map_zsmul]
    rw [← _root_.map_sum, congrArg (F i) (hV _ (l w) ?_), map_zero]
    simpa [ht, sum_filter, sum_comm, (finrank_le _).trans_eq]
      using ellAdicCohom.congruence_relation hR (by simpa) hp (hq.rec hs) _ _ _ (C hq) x
  exact IsEigenQuotient.isKilledBy ⟨by tauto, H⟩ (w, ·) (hcr ·) o fun i y ↦
    lTensor_preserves_injective_linearMap (.restrictScalars ℤ_[ℓ] _) (hV i (l w)) (by
    simpa [← baseChange_eq_lTensor, e, sum_filter, sum_comm, (finrank_le _).trans_eq,
      ↓LinearMap.sum_apply] using! congr($((isCrystalline_and_linearFrob_rel E hR _ _ _ _ _ (C
      (o.eq_pow_of_isFrob (_root_.map_inv he.toGp _ ▸ he.isFrob_iff.2 hs))) fun _ ↦ o.pow _).2) y))
