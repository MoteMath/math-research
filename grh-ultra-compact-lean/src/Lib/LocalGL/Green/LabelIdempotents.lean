import Lib.General.Algebra.FaithfulChar
import Lib.Adelic.Witt.SpaceOperations
section
open Module Matrix Finset Complex Hall Fintype ComplexOrder LinearMap GeneralLinearGroup
variable {k n : Type _} {r : ℕ} (K : Type _) [Field k] [Finite k] [Field K] [Algebra k K] {T : MulChar K ℂ} [IsFaithfulMulChar K T] [Fintype n] {c : Polynomial k}
omit [Finite k] in
@[elab_as_elim] lemma IsLabel.q9 [IsAlgClosed K] {p : ℕ → _ → Prop} (hc : IsLabel r c) (h1 : p 0 1) (h : ∀ P r c (ξ : K), P.Monic → Irreducible P → P.coeff 0 ≠ 0 → P.aeval ξ = 0 → p r c → p (P.natDegree + r) (P * c)) : p r c := by
  induction r using Nat.strongRec generalizing c
  obtain _ | ⟨P, n, i, c, rfl⟩ := not_or_of_imp c.exists_monic_irreducible_factor <;>
   simp_all [IsLabel, hc.1.isUnit_iff, squarefree_mul_iff]
  grind [i.natDegree_pos, n.of_mul_monic_left, n.natDegree_mul, IsAlgClosed.exists_aeval_eq_zero K P i.degree_pos.ne']
lemma IsLabel.map (hc : IsLabel r c) : IsLabel r (c.map (algebraMap k K)) := by simp_all [IsLabel, (PerfectField.separable_iff_squarefree.2 _).map.squarefree]
attribute [local simp] q0 finMean NeZero.ne p0 prod_range_succ
lemma labelChar_degree_bounds (hc : IsLabel (card n) c) : let d := (labelChar T c).evalGL (n := n) 1; 0 ≤ d.re ∧ ((1 -
   card n / Nat.card k) / Nat.card k ^ card n : ℝ) ≤ d / Nat.card (GL n k) * star d := by
  have o := @Finite.one_lt_card k _ _; let z : PowerBasis k k := ⟨1, 1, .singleton .., by simp⟩
  obtain ⟨B, b, e⟩ : ∃ B ≤ Nat.card k ^ card n, q0 (card n) (labelChar T c) (mulMu fun c ↦
   ite (∀ x, c.out.2 x = x) 1 0) * B = (-1) ^ card n := hc.q9 K ⟨1, by
   aesop⟩ fun P r c _ m i _ _ ⟨B, b, e⟩ ↦ ⟨_, Nat.pow_add .. ▸ mul_le_mul' (Nat.pred_le _) b, by
   have := NeZero.of_pos i.natDegree_pos; have h := m1 (K := K) (V := Fin P.natDegree → k) z; simp [minpoly.eq_X_sub_C'] at h; rw [map_mul, gt_v2 T i m, z7 s11_j1, pow_add, ← e, ← star_inj]
   simp [z, q4, greenTau, field, Nat.card_fun, ite_div, ite_and, forall_and, ← Nat.card_congr (generalLinearEquiv ..).1, LinearMap.ext_iff] at *; grind⟩
  rw [← finrank_pi k, z6, classInner, ← star_inj] at e; simp [prod_neg, field, Lagrange.eval_nodal, by simpa [z] using
   (x9 (V := n → k) z T).1, ↓← Nat.card_congr toLin.1] at e
  by_cases B = 0 <;> simp_all [← eq_div_iff, evalGL, End.one_eq_id, ← ofReal_natCast, ← ofReal_pow, ← ofReal_prod, le_def, @eq_comm ℂ 0, prod_eq_zero_iff]
  rify at *; use by positivity
  grw [b, b]; simp [card_GL_eq_prod, field]; induction' card n with m h <;> simp [← mul_assoc]
  grw [← h] <;> simp [field, pow_succ] <;> nlinarith [one_le_pow₀ o.le (n := m)]
end
section
open Finset Function Subgroup ComplexConjugate Fint SemidirectProduct AddMonoidAlgebra ZMod
variable {E E' Γ G G'} [Group E] [Group E'] [Group Γ] [Group G] [Group G'] [Finite E] [Finite E'] [Finite Γ] [Finite G] [Finite G'] (π : E →* Γ) (σ : Γ)
def DescendsOnCoset (j : G → E) (h : E → ℂ) (f : G → ℂ) := ∀ s γ, π s = σ → s ^ orderOf σ = j γ → h s = f γ
private noncomputable def w8 s t := ∑ x, ite (π x = 1 ∧ x * t * x⁻¹ = s) (1 : ℂ) 0
private noncomputable def j5 (ρ : E' →* E) f s := (π.comp ρ).ker.index * classInner (w8 π s ∘ ρ) f
@[local grind] structure Q0 (j : G →* E) (r : G → E) where
  injective : Injective j
  pow_eq γ : π (r γ) = σ ∧ r γ ^ orderOf σ = j γ
  map_conj v γ : r (v * γ * v⁻¹) = j v * r γ * (j v)⁻¹
  mem_range_of_conj x γ δ : π x = 1 → x * r δ * x⁻¹ = r γ → x ∈ j.range
variable {π σ} {j : G →* E} {r ρ h g α Y} (R : Q0 π σ j r)
attribute [local simp] classInner mul_sum sum_mul Fintype.sum_prod_type Semiconj mem_centralizer_iff
omit [Finite Γ] in
private lemma x3 {u y} (e : π u = π y) s t : w8 π (y * s * y⁻¹) (u * t * u⁻¹) = w8 π s t := .symm
  (sum_equiv (.mulLeft y * .mulRight u⁻¹) (by simp) (by simp [e, ← mul_assoc]; simp [mul_assoc]))
private lemma k4 {Z} [CommSemiring Z] [Algebra Z ℂ] (o : Surjective (π.comp ρ)) (v : h ∈ virtualChars Z E') : j5 π ρ h ∈ virtualChars Z E := (irreducible_criteria_of_isClassFunction _ fun s y ↦ (o (π y)).elim fun x _ ↦ congrArg (_ * ·) (finMean_equiv (MulAut.conj x) (by simp_all [x3, isClassFunction_of_mem_virtualChars v]))).2.1 fun χ c ↦ ((c.comp ρ).exists_classInner_eq v).imp fun _ ↦
  .trans (by simpa [apply_ite conj, o.of_comp (f := π), sum_comm, field, card_filter, w8, mul_div, j5, c.isClassFunction, ↓o, ite_and, -sum_boole, finMean, Fintype.card_subtype, mul_left_comm, index_ker] using congr($π.ker.index_mul_card * classInner _ h))
attribute [-simp] mk_eq_inl_mul_inr
private lemma m9 {k k' S} [Field k] [Field k'] [Algebra k k'] [Ring S] [Finite k'] [Algebra k' S] {β : Gal(k'/k) →* MulAut Sˣ} {σ} (τ : S →+* S) (hβ : ∀ u, β σ u = τ u) (hτ : Semiconj (algebraMap k' S) σ τ) {j : G →* _} (i : Injective j) (f : ∀ u, u ∈ j.range ↔ β σ u = u) : ∃ r : _ → _ ⋊[β] _, Q0 rightHom σ (inl.comp j) r ∧ ∀ (B : Subalgebra k' S) γ, ↑(j γ) ∈ B → (r γ).1.1 ∈ B := by
  let C := ZMod (.card G); let s := (mapAlgAut k C σ).toRingHom; let L γ := lift k' S C ⟨⟨(j <| γ ^ ·.toAdd.val), by simp⟩, by simp [C, val_add, pow_add]⟩
  have e γ z : τ (L γ z) = L γ (s z) := by induction z using induction_linear <;>
   simp_all [L, s, Algebra.smul_def, ← hβ, (f _).1, -f]
  have ⟨z, _⟩ := ((isTameAtLevel_gal σ).of_map (θ := s) (algebraMap ..) (by simp [s])
   (by ext <;> simp [s, ← AlgEquiv.coe_pow, ← map_pow, -mapAlgAut_apply])).exists_norm (.inl
   (Module.finite_of_finite k')) ((of ..).toHomUnits (.ofAdd 1)).isUnit (by aesop) (one_dvd _)
  have W γ m : (⟨z.map (L γ), σ⟩ : _ ⋊[β] _) ^ m = ⟨.map (L γ) (∏ i ∈ range m, z.map (s ^ i).1),
   σ ^ m⟩ := by induction m <;> ext <;> simp [pow_succ', prod_range_succ', mul_comm, *]
  have P γ : _ = inl (j γ) := (W γ (orderOf σ)).trans (by
   ext <;> simp_all [L, val_one_eq_one_mod, -map_pow])
  have N {γ} δ u (h : j γ = u * j δ * u⁻¹) : z.map (L γ) = u * z.map (L δ) * u⁻¹ :=
   Units.ext (by simp [L, lift_apply, Finsupp.sum, h, u.conj_pow])
  exact ⟨_, ⟨inl_injective.comp i, (⟨rfl, P ·⟩), fun v γ ↦ by ext <;> simp [(f _).1, N γ (j v)],
   fun | ⟨u, .(1)⟩, γ, δ, rfl, h => ((f u).2
   (by simpa [N _ u (by simpa [P] using congr(($h.symm ^ orderOf σ).1))] using congr($h.1))).imp (by bound)⟩, fun _ _ _ ↦ sum_mem (by aesop)⟩
instance : Finite (G ⋊[α] Γ) := .of_equiv _ equivProd.symm
@[simp] private lemma d5 (u w : G ⋊[α] Γ → ℂ) : finMean (fun x ↦ ite (x.2 = 1) (u x) (w x)) = finMean w + (finMean (u <| inl ·) - finMean (w <| inl ·)) / Nat.card Γ := by simp [↓finMean_equiv equivProd.symm, finMean, ite_sub, ← sub_eq_iff_eq_add', ← sum_sub_distrib, field]; rfl
lemma IsIrrChar.b0 (hY : IsIrrChar Y) (hs : ∀ σ g, Y (α σ g) = Y g) {Φ} (v : Φ ∈ virtualChars ℤ _) (h1 : Nat.card Γ * classInner Φ Φ = classInner (Φ ∘ inl) (Φ ∘ inl) + (Nat.card Γ - 1)) (m : ℤ) (ha : classInner Y (Φ ∘ inl) = 1 + Nat.card Γ * m) : IsIrrChar fun x : G ⋊[α] Γ ↦ ite (x.2 = 1) (Y x.1) (Φ x) := by
  have ⟨A, n, B⟩ := hY
  apply (irreducible_criteria_of_isClassFunction ℤ _).1 (fun x ↦ ite (x.2 = 1) (Y x.1) 0) _ _ _
   (A.rec (by aesop)) fun χ a z r ↦ ((a.comp inl).exists_classInner_eq A.mem_virtualChars).elim
   fun N b ↦ (a.exists_classInner_eq v).imp' (· - N * m) fun M d ↦ ?_
  iterate 4 simp +contextual [A.isClassFunction, isClassFunction_of_mem_virtualChars v, field] at *; grind
  have e g : χ (inl g) = χ 1 / Y 1 * Y g := by
   obtain ⟨r, q⟩ := r (inl g), finMean_equiv (.mulRight g) (congrFun rfl) ▸ congr(conj $(B _
    (a.comp inl).isClassFunction g⁻¹))
   simp [← finMean_conj, ← A.apply_inv, field] at r z q; grind [B Y A.isClassFunction, finMean_eq, sum_eq_zero]
  simp [*, mul_assoc, field] at *; grind
include R
omit [Finite E] [Finite Γ] [Finite G] in
lemma Q0.x2 γ : π (j γ) = 1 := by grind [pow_orderOf_eq_one]
lemma Q0.y4 : (∀ s, π s = σ → ∃ x γ, π x = 1 ∧ x * r γ * x⁻¹ = s) ∧ ∀ {h f g f'}, DescendsOnCoset π σ j h f → DescendsOnCoset π σ j g f' → (∀ s x, π x = 1 → h (x * s * x⁻¹) = h s ∧ g (x * s * x⁻¹) = g s) → π.ker.index * finMean (fun s ↦ ite (π s = σ) (conj (h s) * g s) 0) = classInner f f' := by
  let i := (j.codRestrict π.ker R.x2).range
  obtain ⟨n, o⟩ := (R.pow_eq 1).1 ▸ Nat.card_congr (π.fiberEquivKer _), fun x : π.ker ↦
   π.mem_ker.1 x.2
  have b := @Injective.bijective_of_nat_card_le ((_ ⧸ i) × G) (π ⁻¹' {σ}) _ (fun (x, γ) ↦ ⟨x.out *
   r γ * x.out.1⁻¹, by simp [*, R.pow_eq]⟩) (fun ⟨_, δ⟩ ⟨x, γ⟩ h ↦ by simp_all [ x.out_equiv_out.1 (QuotientGroup.leftRel_apply.2 ((R.mem_range_of_conj _ γ _ (o _)
   (by simpa [mul_assoc] using congr(x.out⁻¹ * $h.1 * x.out))).imp fun _ ↦ Subtype.ext))]; grind)
   (n ▸ i.index_mul_card ▸ Nat.card_prod _ G ▸ mul_le_mul_right (Finite.card_range_le _) _)
  use (by grind [b.2 ⟨·, ·⟩]); intros; erw [finMean, finsum_eq_sum_of_fintype, ← sum_filter, sum_subtype _ mem_filter_univ, ← b.sum_comp, ← π.ker.index_mul_card, ← n]; simp [← Fintype.card_of_bijective b, *, finMean, field]; grind [DescendsOnCoset]
omit [Finite E] [Finite Γ] [Finite G] in
lemma Q0.r1 H {H₀} (c : comap j H = H₀) (m : ∀ γ ∈ H₀, r γ ∈ H) : Q0 (G := H₀) (π.comp H.subtype) σ (j.restrict c.ge) (⟨_, m _ ·.2⟩) := by constructor <;>
  simp [Injective, ← c, ← SetLike.coe_eq_coe, MonoidHom.restrict] <;> grind [j.mem_range]
lemma Q0.m7 (c : ∀ s x, π x = 1 → g (x * s * x⁻¹) = g s) : DescendsOnCoset π σ j g (g ∘ r) := fun s γ q e ↦ by
  obtain ⟨x, δ, u, ⟨⟩⟩ := (R.r1 (centralizer {j γ}) rfl (by simp_all [← map_mul, R.injective.eq_iff, ← R.map_conj, ← mul_inv_eq_iff_eq_mul])).y4.1 ⟨s, by simp [← e, pow_mul_comm']⟩ q
  simp_all [R.pow_eq, mul_inv_eq_iff_eq_mul, x.2 _, R.injective.eq_iff]
lemma DescendsOnCoset.x5 (c : IsClassFunction h) ρ₀ {j' : G' →* E'} (e : ∀ γ, ρ (j' γ) = j (ρ₀ γ)) {f r'} (S : Q0 (π.comp ρ) σ j' r') (l : DescendsOnCoset (π.comp ρ) σ j' h f) {F} (C : IsClassFunction F) (hF : ∀ χ, IsClassFunction χ → classInner F χ = classInner f (χ ∘ ρ₀)) : DescendsOnCoset π σ j (j5 π ρ h) F := fun s γ a b ↦ by
  have q t x (m : π x = π 1) :=
   And.intro (x3 m s t) (x3 m.symm t); simp [forall_and] at q
  refine .trans congr(_ * finMean $(by simp +contextual [funext_iff, w8, ne_of_apply_ne π, *])) ((S.y4.2 (fun _ δ a _ ↦
   R.m7 q.1 _ (ρ₀ δ) a (by grind)) l (by aesop)).trans ?_)
  simpa [fun δ ↦ (R.m7 (g := (w8 π · (r δ))) (by grind) s γ a b).trans (Fintype.sum_of_injective j R.injective (fun v ↦ ite (δ = (MulAut.conj v)⁻¹ • γ) 1 0) _
   (by grind [j.mem_range]) (by
   simp [R.x2, ← R.map_conj, ↓eq_inv_smul_iff]; grind)).symm, finMean, apply_ite conj, -sum_boole, @sum_comm G, ← map_inv, C, -inv_inv] using
   congr(conj $(hF (w8 π s ∘ r) (by grind [R.x2]))).symm
omit R
open Matrix Hall GeneralLinearGroup Fintype Equiv Submodule
variable {k m n ι} [Field k] [Fintype m] [Fintype n] [LinearOrder ι] (b : n → ι) (F : ι → Hall k)
lemma simClassOf_submatrix (e : m ≃ n) (M : Matrix n n k) : simClassOf (M.submatrix e e).toLin' = simClassOf M.toLin' := s11_q1 (.piCongrLeft' _ _ e)
private lemma v5 {Y : GL n k → ℂ} (c : IsClassFunction Y) : ∃ X, Y = Hall.evalGL X :=
  (factorsThrough_iff Y).1 fun _ _ h ↦ by
   cases s11_v3.1 h.symm; convert c _ (toLin.symm (.ofLinearEquiv ‹_›))
   simp_all [← toLin.apply_eq_iff_eq, eq_mul_inv_iff_mul_eq, Units.ext_iff, DFunLike.ext_iff]
lemma m4 [Finite k] {s} (hs : ∀ i, b i ∈ s) Y : IsClassFunction Y → classInner (∏ a ∈ s, (F a).rankPart (Fintype.card {i // b i = a})).evalGL Y = classInner (∏ a ∈ s, (F a).evalGL ∘ blockHom b a) (Y ·.1) := (by
  rintro ⟨X, rfl⟩
  induction' s using induction_on_max with m s hm ih generalizing n X
  simp_all [← isEmpty_iff, classInner, Hall.evalGL, j2]; let e := sumCompl (b · = m)
  have h (g : parabolic (R := k) b) := (Matrix.ext fun _ _ ↦ g.2 (by simp [e]; grind) :
   toBlocks₁₂ (g.1.1.submatrix e e) = 0) ▸ fromBlocks_toBlocks _
  have u g := isUnit_fromBlocks_zero₁₂'.1 ((h g).substr (by simp))
  rw [w0, prod_insert, ← card_congr e, card_sum, z7, ← w0, s.prod_congr rfl fun a h ↦ by rw [← card_congr (subtypeSubtypeEquivSubtype (· ▸ (hm a h).ne))], ih] <;> try grind [rankPart]
  simp [q4, ← w0, classInner, z1, ← finMean_const_mul, ← finMean_prod (Prod.rec _), Hall.evalGL]
  apply finMean_equiv ⟨fun g ↦ (⟨(u g).2.unit, g.2.submatrix⟩, (u g).1.unit,
   (submatrix g.1 e e).toBlocks₂₁.toLin'), fun t ↦ ⟨(by simp : IsUnit (reindex e e (fromBlocks
   t.2.1 0 t.2.2.toMatrix' t.1.1))).unit, blockTriangular_reindex_iff.2 (by
   simp [e, BlockTriangular]; grind [t.1.2 _])⟩, by aesop_cat, by aesop_cat⟩
  simp_intro _ [mul_left_comm, ← mul_assoc, mt (hm m)]; symm; congr!
  exact (simClassOf_submatrix (subtypeSubtypeEquivSubtype (by grind)) _).symm; rw [← simClassOf_submatrix e, ← h, s11_v3]
  use .sumArrowLequivProdArrow .., by simp [fromBlocks_mulVec]; tauto) ∘ v5
variable (k k' Z : Type*) {k₀} {R : _} [Field k] [Field k'] [Field k₀] [Algebra k k'] [Algebra k₀ k'] [Finite k₀] [CommSemiring Z] [Algebra Z ℂ] [CommRing R] [Algebra R ℂ] {F G : Hall k} {F' G' : Hall k'} {σ : Gal(k'/k)} (n : _) [Fintype n]
noncomputable def galActionGL : Gal(k'/k) →* MulAut (GL n k') := .mk' (Units.mapEquiv
  ·.mapMatrix.toMulEquiv) (by tauto)
abbrev GalSemidirect := _ ⋊[galActionGL k k' n] _
variable {k k' n} (Φ : GalSemidirect k k' n → ℂ) (X : Hall k₀)
variable (k₀) in
abbrev HasFixedField (σ : Gal(k'/k)) := .range (algebraMap k₀ _) = fixedPoints σ
def DescendsTo := ∀ σ, HasFixedField k₀ σ → DescendsOnCoset rightHom σ (inl <| ·.map (algebraMap ..)) Φ X.evalGL
variable (F F' n)
def HasCommonLift := ∃ Φ ∈ virtualChars Z (GalSemidirect k k' n), DescendsTo Φ F ∧ DescendsTo Φ F'
def Lift := ∀ m, HasCommonLift Z F F' (Fin m)
variable {Φ Z F F' n}
lemma Lift.exists_descendsTo [Finite k'] (h : Lift Z F F') n [Fintype n] : HasCommonLift Z F F' n := (h _).rec fun _ ⟨v, l⟩ ↦ ⟨_, comp_mem_virtualChars v (SemidirectProduct.map (reindexGL (equivFin n)).toMonoidHom (.id _) (by tauto)), by apply l.imp <;> exact fun l σ s _ γ a b ↦ .trans (l σ s _ (reindexGL _ γ) a (by rw [← map_pow, b]; rfl)) (congrArg _ (simClassOf_submatrix ..))⟩
lemma w3 : IsClassFunction (F.evalGL (n := n)) := fun _ x ↦ congrArg F (s11_q1 x.toLin.toLinearEquiv).symm
lemma v1 [Finite k'] (s : HasFixedField k₀ σ) : ∃ r : GL n k₀ → GalSemidirect .., Q0 rightHom σ (inl.comp (GeneralLinearGroup.map (algebraMap ..))) r ∧ ∀ (B : Subalgebra k' _) γ, (γ.map (algebraMap ..)).1 ∈ B → (r γ).1.1 ∈ B := m9 (.mapMatrix σ) (by tauto)
  (by simp [algebraMap, Semiconj]) (by simp [Injective, GeneralLinearGroup.ext_iff]) fun _ ↦ ⟨(·.rec
  (by bound [s.le])), exists_gl_map_eq_of_fixed (σ := σ.toRingHom) (RingHom.injective _) s.ge⟩
attribute [local simp] DescendsTo DescendsOnCoset Hall.evalGL HasCommonLift
@[simp] lemma DescendsTo.iff_comp_inl_eq_evalGL : DescendsTo Φ F' ↔ (Φ <| inl ·) = F'.evalGL :=
  ⟨by bound, fun h σ s ↦ by simp_all [funext_iff, σ.ext (g := 1) (s.le ⟨·, rfl⟩)]⟩
lemma Lift.m2 [Finite k'] (h : ∀ m, ∃ Φ ∈ virtualChars Z (GalSemidirect k k' (Fin m)), DescendsTo Φ F) : ∃ G : Hall k', Lift Z F G := by
  choose Φ v e using h; choose X x using fun m ↦
   v5 (isClassFunction_of_mem_virtualChars (comp_mem_virtualChars (v m) inl))
  use fun c ↦ X c.dim c, (⟨Φ ·, by simp_all [funext_iff, -DescendsTo]⟩)
lemma s11_x7 [Finite k'] (u : ∀ σ : Gal(k'/k), σ = 1) (h : F'.evalGL ∈ virtualChars Z (GL n k')) (e : ∀ g : GL n k, F'.evalGL (g.map (algebraMap ..)) = F.evalGL g) : HasCommonLift Z F F' n := ⟨_, comp_mem_virtualChars h (.mk' left (by aesop)), by aesop⟩
lemma Lift.rankPart_of_descendsTo {m} (l : HasCommonLift Z F F' (Fin m)) : Lift Z (rankPart m F) (rankPart m F') := (eq_or_ne · m |>.rec (·.symm ▸ by simpa) (⟨0, by simp [·]⟩))
lemma Lift.w7 : Lift Z (@constOne k _) (@constOne k' _) := fun _ ↦ by aesop
@[simp] lemma Lift.one : Lift (k := k) (k' := k') Z 1 1 := rankPart_of_descendsTo (w7 0)
lemma Lift.evalGL_mem_virtualChars [Finite k] (h : Lift Z F G) : F.evalGL ∈ virtualChars Z (GL n k) := have ⟨_, v, e⟩ := h.exists_descendsTo n
  DescendsTo.iff_comp_inl_eq_evalGL.1 e.1 ▸ comp_mem_virtualChars v _
lemma Lift.sub (h : Lift R F F') (h' : Lift R G G') : Lift R (F - G) (F' - G') := fun n ↦
  (h' n).rec fun Ψ _ ↦ (h n).imp' (· - Ψ) (by simp_all [sub_eq_add_neg, add_mem]; grind)
variable [Finite k']
lemma Lift.mul [Finite k] (h : Lift Z F F') (h' : Lift Z G G') : Lift Z (F * G) (F' * G') := fun m ↦ by
  choose Φ v e f using fun i n (_ : Fintype n) ↦
   (i.rec h' h : Lift Z (cond i F G) (cond i F' G')).exists_descendsTo n
  refine ⟨∑ a ≤ m, j5 rightHom (Subgroup.subtype ⟨⟨⟨left ⁻¹' (parabolic (decide <| ·.1 <
  a)).carrier, @fun x ↦ (·.mul <| ·.map x.2)⟩, by simp⟩, @fun x ↦ .map x.2⁻¹ ∘ (parabolic _).2⟩)
  (∏ i, _ ∘ MonoidHom.mk' (fun ⟨s, h⟩ ↦ ⟨blockHom _ i ⟨_, h⟩, s.2⟩) fun x y ↦ congrArg₂ _ ((blockHom
  ..).2 ⟨_, _⟩ ⟨_, y.2.map x.1.2⟩) rfl), sum_mem fun a _ ↦
   k4 (⟨⟨inr ·, (parabolic _).1.2⟩,
  rfl⟩) (prod_mem fun i _ ↦ comp_mem_virtualChars (v i _ _) _), ?_, ?_⟩ <;> intro σ s t γ p w <;>
  rw [Finset.sum_apply, funext fun a ↦ have ⟨_, R, B⟩ := v1 s
   DescendsOnCoset.x5 R (isClassFunction_of_mem_virtualChars (prod_mem fun i _ ↦
    comp_mem_virtualChars (v i _ _) _)) _ (by tauto) (R.r1 _ (by
  ext; simp [parabolic, BlockTriangular]) (B (blockTriangularSubalgebra ..) · ∘ .map _))
    (fun _ _ p w ↦ by simp_rw [Finset.prod_apply]; congr!; apply_rules; rw [← map_pow, w]; rfl)
    w3 (m4
  _ _ (by grind)) t γ p w] <;> simp +contextual [w2, -not_lt, -mul_ite, -Nat.not_lt, sum_comm, card_fin_lt_of_le ∘ mem_Iic.1, finrank_quotient, (finrank_le _).trans]
lemma Lift.mulMu [Finite k] (h : Lift R F F') : Lift R F.mulMu F'.mulMu := fun m ↦ ((by induction m <;> grind
  [Hall.j4, one, sub ‹_› (sub (w7.mul ‹_›) one)] : Lift R (moebius + (1 -
  constOne) ^ m.succ * -moebius) (moebius + (1 - constOne) ^ m.succ * -moebius)) m).rec fun Φ _ ↦
  (h m).imp' (· * Φ) (by simp_all [mul_mem, j0 (n := 0) (j7 _)]; grind)
lemma Lift.y2 [Finite k] {m} (h : Lift R F F') : Lift R ((-1 : ℂ) ^ m • rankPart m (F.mulMu * constOne)) ((-1 : ℂ) ^ m • rankPart m (F'.mulMu * constOne)) := by
  obtain ⟨l, _ | _⟩ := rankPart_of_descendsTo (h.mulMu.mul w7 m),
   m.even_or_odd <;> simp [*]
  simpa using (l.sub l).sub l
seal Finset.univ Finset.sum Finset.prod in
lemma s11_k8 {S} [Monoid S] [Finite S] α (ν : S →* ℂ) : ∃ ϑ, IsChar ϑ ∧ (∀ s : Sˣ ⋊[α] Gal(k'/k), ϑ s = ∏ τ, ν (α τ s.1)) ∧ ∀ σ, HasFixedField k σ → DescendsOnCoset rightHom σ inl ϑ (ν ·.1) :=
  ⟨_, isChar_monoidHom ⟨⟨_, by simp⟩, fun a b ↦ by simp [← Equiv.prod_comp (.mulRight a.2) (ν <| α ·
  b.1)]⟩, fun _ ↦ rfl, fun σ s t _ e p ↦ .trans (by
  simp [pow_injOn_Iio_orderOf, ← IsCyclic.image_range_orderOf fun τ ↦ (IntermediateField.fixingSubgroup_fixedField _).le fun x ↦ (s.ge (x.2 ⟨σ, 1, rfl⟩)).rec (by bound)]; induction orderOf σ <;> cases e <;>
  simp_all [pow_add, prod_range_succ, ↓← map_pow]) (congrArg (ν ·.1) p)⟩
open Module Algebra TensorProduct LinearMap FiniteField
variable (k k' : Type*) {K L} {m : _} [Field k] [Field k'] [Algebra k k'] [Finite k] [Finite k'] [Field K] [Algebra k K] [Algebra k' K] [IsScalarTower k k' K] (θ : MulChar K ℂ) [Field L] [Finite L] [Algebra k L]
omit [Finite k] in
private lemma p3 {m : ℕ} {A} [Ring A] [Algebra k A] [Finite A] (b : Basis (Fin m) k A) t : simClassOf (leftMulMatrix b t).toLin' = simClassOf (mulLeft k t) :=
  (s11_q1 b.equivFun (by simp [leftMulMatrix_mulVec_repr])).symm
attribute [local simp] classInner p3 Hall.evalGL leftMulMatrix_eq_repr_mul DescendsOnCoset add_eq_zero_iff_neg_eq DescendsTo
seal Finset.univ Finset.sum Finset.prod in
lemma s11_k1 (r : finrank k L = m) (φ : k' ⊗[k] L →ₐ[k'] K) : ∃ Φ : GalSemidirect k k' (Fin m) → ℂ, IsChar Φ ∧ DescendsTo Φ (greenCuspidal k θ).mulMu ∧ ∀ X, (∀ B, q0 m X B = finMean fun t : _ˣ ↦ conj (θ (φ (∏ τ : Gal(k'/k), Algebra.TensorProduct.map τ.toAlgHom (.id k L) t.1))) * B (simClassOf (mulLeft k' t.1))) → DescendsTo Φ X := by
  let b := finBasisOfFinrankEq k L r; let B := TensorProduct.basis k' b; have := fintypeOfFintype B; let g (σ : Gal(k'/k)) := congr σ (1 : Gal(L/k))
  have q σ x j : B.repr (g σ x) j = σ (B.repr x j) := by induction x <;> aesop
  let β := MonoidHom.mk' (Units.mapEquiv <| g · |>.toMulEquiv) (by aesop (add simp B.ext_elem_iff)); let ⟨ϑ, a, u, w⟩ := s11_k8 β (θ.comp φ)
  refine ⟨j5 _ (SemidirectProduct.map (Units.map (leftMulMatrix B).1.1) (.id _)
   fun σ ↦ by ext; simp [galActionGL, β, ← q, B, g, Units.mapEquiv]) ϑ, isChar_of_mem_virtualChars
   (k4 rightHom_surjective a.mem_virtualChars), fun σ s ↦ .x5
   (v1 s).choose_spec.1 a.isClassFunction (Units.map (leftMulMatrix b).1.1)
   (fun _ ↦ by ext <;> simp [B]) (m9 (g σ) (by tauto) (by tauto)
   (Units.map_injective includeRight.injective) fun x ↦ ⟨by rintro ⟨_, rfl⟩; ext; simp [β, g],
   fun h ↦ ?_⟩).choose_spec.1 (w σ s · <| ·.map _) w3 fun _ c ↦ (v5
   c).choose_spec ▸ w0.trans ?_, fun X h σ s ↦ .x5 (v1
   s).choose_spec.1 a.isClassFunction (·.map (leftMulMatrix B)) (f := ϑ ∘ inl) ?_ (r' :=
   inl) ⟨inl_injective, ?_, ?_, ?_⟩ ?_ w3 fun _ c ↦
   (v5 c).choose_spec ▸ w0.trans (by aesop)⟩
  · choose c hc using (s.ge <| q σ x · ▸ congr(B.repr $h _)); have : 1 ⊗ₜ ∑ i, c i • b i = x.1 := B.ext_elem (by simpa [B, Finsupp.single_apply]); exact ⟨.mk0 _ (x.ne_zero <| by simp [← this, ·]), Units.ext this⟩
  iterate 5 simp_all [range_inl_eq_ker_rightHom, σ.ext (g := 1) (s.le ⟨·, rfl⟩)]
  simpa [← r, q0.eq_1, mul_right_comm, mul_assoc] using
   y0 θ ((AlgHom.liftEquiv ..).2 φ) _
lemma s11_m5 [IsAlgClosed K] : ∃ B : Hall k', Lift ℤ (brauerLift k θ) B :=
  ⟨_, by simpa using ((Lift.m2 (F := -greenCuspidal k θ) fun m ↦ (m.succ.rec
  ⟨_, _, .w7, nofun⟩ fun _ ⟨_, _, h, e⟩ ↦ ⟨_, _, .mul ((Lift.m2
  (·.casesOn ⟨0, by simp [x6]⟩ fun _ ↦
  (s11_k1 _ _ θ (finrank_extension ..)
  ((AlgHom.liftEquiv ..).1 IsAlgClosed.lift)).imp fun _ ↦ .imp (·.mem_virtualChars)
  (·.1))).choose_spec.sub ((h.mul .w7).sub h).mulMu) .w7,
  add_mul (brauerLift k θ).mulMu .. ▸ j0 (n := 0) (by
  peel j0 e (j7 1); simp_all [sub_eq_add_neg, add_mul, mul_add, mulMu]; grind) nofun⟩
  : ∃ J J', Lift (k' := k') ℤ J J' ∧ ∀ c, c.dim < m.succ → (greenCuspidal k θ + J :) c = 0).elim
  fun _ ⟨_, l⟩ ↦ (l.1 m).imp (by aesop)).choose_spec.mul .w7)⟩
end
section
open Polynomial Hall Classical
variable {k K n r} [Field k] [Finite k] [Field K] [Algebra k K] (T) [IsFaithfulMulChar K T] [Fintype n] {c P : k[X]} (hc : IsLabel r c)
attribute [local simp] r5 p8 isCuspidal_greenTau s11_p9 IsLabel Irreducible.ne_one Monic.def irreducible_X_sub_C
lemma labelChar_X_sub_C χ : labelChar T (Polynomial.X - C (charName T χ).1 : k[X]) = (detChar χ).rankPart 1 := by
  ext _ g
  have (η : K → ℂ) := j0 (x6 η)
   (j7 1) (simClassOf g)
  simp_all [greenTau, epsilon_singleton, detChar, -map_mul, mul_sub, add_eq_zero_iff_eq_neg, ← map_neg, aroots, thetaChar_charName, g.charpoly_natDegree, congr(aroots $(g.charpoly_monic.eq_X_add_C _) K)]
include hc
lemma IsLabel.exists_eq_prod_of_splits (h : ∀ x : K, aeval x c = 0 → x ^ .card k = x) : ∃ χ : Fin r → _, c = ∏ i, (Polynomial.X - C (charName T (χ i)).1) :=
  h |> hc.q9 K (by bound) fun _ _ _ _ m i z e h _ ↦ (h (by aesop)).imp'
  (Fin.append fun _ ↦ (charName T).symm (-.mk0 _ z)) (by simp +contextual [Fin.prod_univ_add, ← m.eq_X_add_C, Nat.dvd_one.1 ((root_pow_card_pow_eq_self_iff i e).1 (by aesop))])
lemma rankPart_labelChar : (labelChar T c).rankPart r = labelChar T c := funext
  (hc.q9 K (by simp) (by
  intro _ _ _ _ _ _ _ _ _ x; simp_all; exact fun _ ↦ .symm (finsum_eq_zero_of_forall_eq_zero
  fun U ↦ by grind [U.1.finrank_quotient_add_finrank, s11_r3, s11_j1, q7 x])))
private lemma k2 {d e} (i : Irreducible P) : IsLabel e P → e = d → ¬P ∣ c → q4 d (greenTau T P) (labelChar T c) = 0 := hc.q9 K (by grind [r5 (F := 1), isCuspidal_greenTau, i.natDegree_pos, IsLabel]) (by aesop (add simp i.prime.dvd_mul))
lemma x8 : c.eval 1 ≠ 0 → ∀ A, q0 r (labelChar T c) (A * constOne) = q0 r (labelChar T c) A := hc.q9 K
  (by simp [q0]) (by simp_all [z7 s11_j1])
lemma s11_y9 : ∀ c', IsLabel r c' → q0 r (labelChar T c) (labelChar T c') = ite (c = c') 1 0 := hc.q9 K
  (by simp_all [q0]) fun P _ _ _ _ i _ _ _ c' ↦ by
  obtain _ | ⟨_, rfl⟩ := em' (P ∣ c') <;> simp_all [z7 s11_j1, k2, squarefree_mul_iff, i.ne_zero, i.isRelPrime_iff_not_dvd, natDegree_mul']
  simp [q0]; tauto
omit hc in
lemma IsLabel.z3 (hc : IsLabel (Fintype.card n) c) : IsIrrChar ((labelChar T c).evalGL (n := n)) := by
  apply (irreducible_criteria_of_isClassFunction ℤ w3).1 (labelChar T c).evalGL w3
   _ _ (labelChar_degree_bounds K hc).1 fun _ a _ _ ↦ a.exists_classInner_eq
   (hc.q9 K ⟨1, by simp⟩ (by
   intros; simp_all; casesm Exists _; exact ⟨_, (s11_m5
   ..).choose_spec.y2.mul ‹_›⟩) : Exists (Lift _ (labelChar T
   c))).choose_spec.evalGL_mem_virtualChars <;> grind [s11_y9, w0]
lemma lift_labelChar_self : Lift ℕ (labelChar T c) (labelChar T c) := rankPart_labelChar T hc ▸ .rankPart_of_descendsTo (s11_x7 (by subsingleton) (IsLabel.z3 _ (by simpa)).1.mem_virtualChars (by simp))
end
open Nat Finite Function Hall Matrix Polynomial
noncomputable def scaleRootsEquiv {k} [Field k] (a : kˣ) : k[X] ≃* k[X] := by
  use! (·.scaleRoots a), (·.scaleRoots a⁻¹) <;>
   simp_intro _ [← scaleRoots_mul, mul_scaleRoots_of_noZeroDivisors]
variable {k K : Type _} {r : ℕ} [Field k] [Finite k] [Field K] {c : k[X]}
omit [Finite k] in
lemma IsLabel.scaleRoots (a : kˣ) (hc : IsLabel r c) : IsLabel r (c.scaleRoots a) := by simp_all [IsLabel, Monic]; use (reindex_equiv _).1.2 fun x h ↦ (hc.2.1 x ((map_dvd_iff (scaleRootsEquiv a)).1 (by simpa))).map _
lemma frobenius_conj_pow_injOn {ξ : K} {e l} a (h3 : 9 ∣ .card k - 1) (h : IsPrimitiveRoot ξ (.card k ^ 3 ^ (e + 1) - 1)) (hl : Nat.Prime l) : (Set.Iio (3 ^ (e + 1))).InjOn ((ξ ^ l ^ a) ^ .card k ^ ·) := by
  obtain ⟨o, u, s, hy⟩ := @one_lt_card k _ _, h.1, h3.trans (sub_one_dvd_pow_sub_one _ (3 ^ e))
  convert @minimalPeriod_eq_prime_pow _ (· ^ Nat.card k) (ξ ^ l ^ a) 3 e _ ?_ ?_ ▸
   iterate_injOn_Iio_minimalPeriod <;> simp_all [IsPeriodicPt, IsFixedPt, succ_le_iff, pow_right_comm ξ (l ^ a), pow_succ, mul_pow, tsub_eq_iff_eq_add_of_le]
  exact ((dvd_prime_pow hl).1 ∘ (h.pow (b := s * (81 * s + 27) + 3) (by simpa)
   (by rw [pow_mul, hy]; lia)).2 _).mt (by rintro ⟨_ | _ | _, _, D⟩ <;>
   grind [one_lt_pow, dvd_prime, prime_three.dvd_of_dvd_pow (.trans (by lia) D.dvd)])
lemma labelChar_mul_det [Algebra k K] {n} [Fintype n] {T} [IsFaithfulMulChar K T] (hc : IsLabel r c) χ (g : GL n k) : (labelChar T c).evalGL g * χ g.1.det = (labelChar T (c.scaleRoots (charName T χ))).evalGL g := by
  erw [← thetaChar_charName T, RingHom.map_det, det_eq_prod_roots_charpoly, charpoly_map, ← charpoly_toLin', ← s11_p7]
  exact ((hc.q9 K (by simp_all [j2]) fun P _ _ x _ i o
   h _ ↦ congrFun (Hall.ext fun _ _ ↦ by
   have := i.map (scaleRootsEquiv (charName T χ)); simp_all [map_mul, scaleRootsEquiv, Monic.def, w2, Finset.sum_mul]; congr with W; simp [*, s11_w4 _ _ (scaleRoots_aeval_eq_zero h), s11_w4 i _ h, aroots_mul, ↓mul_left_comm, ← v8 _ W, (LinearMap.charpoly_monic _).ne_zero, mul_comm, mul_assoc]; split_ifs; swap; rfl; rw [s11_m8 (g := W.q3) (thetaChar T (.card k ^ P.natDegree) x) _ (a := thetaChar T (.card k) (algebraMap k K (charName T χ)) (W.q3.charpoly.aroots K).prod) fun z ↦ by by_cases z = 0 <;> simp_all [r4, root_pow_card_pow_pred_eq_one i o h, ← Finset.range_val, MulChar.map_zero, s11_j8 T one_lt_card _ _ rfl (pow_one _), mul_comm, Finset.prod_pow_eq_pow_sum, root_pow_card_pow_eq_self_iff (irreducible_X_sub_C _)]]; ring) : ∀ x,
   labelChar T (scaleRootsEquiv _ c) x =
   labelChar T c x * thetaChar T _ _ (x.charpoly.aroots K).prod) _).symm
open Finset LinearMap Fint Submodule MonoidAlgebra Representation
variable {n ι : Type _} [Fintype n] [Fintype ι] {k : Type _} [Field k] [Finite k]
attribute [local simp] labelIdem coeff_mul_apply_right Finsupp.sum_fintype finMean_prod Units.smul_def w3 reflectionSum asAlgebraHom_eq_sum LinearMap.ext_ring_iff character q4 detChar Units.ext_iff
private lemma m6 : OrthogonalIdempotents (labelIdem (k := k) n) :=
  .iff_mul_eq.2 fun c d ↦ by
  ext x
  have (h : IsLabel _ d) := (h.z3 (faithfulChar k)).2.2
   (labelChar (faithfulChar k) c).evalGL w3 x⁻¹
  simp only [labelIdem]; split_ifs <;> simp_all [Finsupp.sum_fintype, _root_.finMean, w0, s11_y9, eq_comm, mul_mul_mul_comm _ _ (_ / _), ← mul_sum, ← (IsLabel.z3 _ _).1.apply_inv] <;> grind
lemma reflectionSum_mul_labelIdem {c : Polynomial k} {χ} (hχ : ¬c.IsRoot (charName (faithfulChar k) χ)) {l} (hl : l ≠ 0) : reflectionSum χ l * labelIdem n c = 0 := by
  rw [IsClassFunction.commute (by aesop)]; simp; intro h
  let N : Submonoid (GL n k) := ⟨⟨{g | ∃ u, g.1 = 1 + vecMulVec u l}, by
   simp_all [mul_add, mul_vecMulVec, add_assoc, ← add_vecMulVec]; lia⟩, by simp⟩
  let := @LeftCancelMonoid.groupOfFinite N {}; let e := (dotProductEquiv k n l).equivProdOfSurjectiveOfIsCompl (mkQ _) (by simpa [range_eq_top, surjective_iff_ne_zero]) (by simp) (by simpa using (ker _).exists_isCompl.choose_spec); let E := e ≪≫ₗ .symm (prodEquiv k ≪≫ₗ ringLmapEquivSelf k ..)
  have hd u : (1 + vecMulVec u l).det = (1 + (E u).1).det ∧ simClassOf
   (.id + (vecMulVec u l).toLin') = simClassOf (s11_z4 1 (1 + (E u).1) (E u).2) :=
   ⟨by simp [E, e, vecMulVec_eq Unit, det_one_add_mul_comm],
   s11_q1 e (by simp [E, e, vecMulVec_mulVec, add_comm])⟩
  have := ((h.z3 (faithfulChar k)).1.groupAlgElem_eq_zero (V := ℂ)
   N.subtype · (ρ := .comp .smulOneHom ⟨⟨(χ⁻¹ ·.1.det), by simp⟩, by simp⟩) ?_)
  ext; simp_all [sum_ite, ← sum_subtype_eq_sum_filter, ← (h.z3 _).1.apply_inv, mul_assoc, ← mul_sum]; convert! Or.inr (this _)
  simpa [classInner, mul_comm (labelChar _ c _), hd, ← χ.star_apply', Hall.evalGL, ← z1, ↓z6, ↓LinearMap.det_eq_sign_charpoly_coeff, finMean_equiv (.ofBijective (uncurry fun g x ↦ (⟨.mk'' _
   ((hd _).1 ▸ .map _ (by simp)), E.symm (Units.val g - 1, x), rfl⟩ : N)) ⟨by simp_all [Injective, ↓← sub_eq_zero (a := vecMulVec _ l), ← sub_vecMulVec], fun ⟨g, u, _⟩ ↦ ⟨(g.det • 1, (E u).2), by
   simp_all [E]⟩⟩) (by tauto)] using
   congrFun (Module.finrank_self k ▸ (by simp_all [← labelChar_X_sub_C (faithfulChar k), dvd_iff_isRoot, k2, IsLabel, Monic.def, irreducible_X_sub_C] : q4 1 ((detChar χ).rankPart 1) (labelChar (faithfulChar k) c) = 0) :) _
variable {k : ι → _} [∀ w, Field (k w)] [∀ w, Finite (k w)] (c : ∀ w, Polynomial (k w))
variable (n) in
noncomputable def tupleIdem := piTensorElem (labelIdem n <| c ·)
lemma isCentralProj_tupleIdem : IsCentralProj (tupleIdem n c) :=
  .piTensorElem (⟨m6.1 <| c ·, by aesop⟩)
lemma tupleIdem_orthogonal : OrthogonalIdempotents (tupleIdem (k := k) n) := ⟨(isCentralProj_tupleIdem · |>.1), fun _ _ e ↦ piTensorElem_mul_eq_zero _ (m6.2 (ne_iff.1 e).choose_spec)⟩
lemma isCentralProj_sum_tupleIdem {s} : IsCentralProj (∑ c ∈ s, tupleIdem (k := k) n c) :=
  ⟨tupleIdem_orthogonal.isIdempotentElem_sum, by simp [(isCentralProj_tupleIdem _).2]⟩
