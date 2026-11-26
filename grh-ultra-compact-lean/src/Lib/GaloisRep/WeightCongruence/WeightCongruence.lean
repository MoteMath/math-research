import Lib.Adelic.CuspForms.ClassReps
import Lib.GaloisRep.Main.SplitPlaceCount
noncomputable section
attribute [-instance] Finite.of_subsingleton
open Module Finset IsUltrametricDist Matrix MvPolynomial Submodule Fintype ContinuousMap Classical
variable {X k : Type} [TopologicalSpace X] [CompactSpace X] [Nonempty X] [NormedField k] [IsUltrametricDist k]
attribute [local simp] hom_bind₁ RingHom.map_det Finsupp.weight_eq_sum Finsupp.degree_eq_sum closedBall_openAddSubgroup minor
private lemma k6 (N : Submodule k C(X, k)) φ (h : ∀ a, ∃ d ∈ N, ∀ x, (∀ u ∈ N / N, u x = u a) → φ x = d x) : ∀ ε > 0, ∃ g ∈ N, ‖φ - g‖ ≤ ε := by
 by_contra! ⟨ε, o, n⟩
 let A := (N / N).toSubalgebra (by simp) fun x y a b z h ↦ mul_assoc x y z ▸ a _ (b _ h)
 let B := A.toSubring ⊓ {closedBall_openAddSubgroup _ one_pos, Submonoid.unitClosedBall _ with}
 have b (c : B) := mem_closedBall_zero_iff.1 c.2.2
 have ⟨m, _, I⟩ := Ideal.exists_le_maximal (comap (.toSpanSingleton B _ φ) (⟨N.1, (·.2.1 _)⟩ ⊔ ⟨(closedBall_openAddSubgroup _ o).1.1, fun c _ ↦ by simpa using! norm_mul_le_of_le (b c)⟩)) (by
  simpa [Ideal.eq_top_iff_one, Submodule.mem_sup, ← eq_sub_iff_add_eq'] using n)
 let P := m.primeCompl
 have : Nonempty P := ⟨1⟩
 let Z := {x | 1 ≤ fun f : P ↦ ‖f.1.1 x‖}
 have S g {r} (o : 0 < r) (H : ∀ x ∈ Z, ‖g x‖ ≤ r) : ∃ f : P, ‖f.1.1 * g‖ ≤ r := by
  simpa [norm_le, o.le] using isCompact_univ.elim_directed_cover _ (fun f : P ↦ (isOpen_closedBall
   0 o.ne').preimage (f * g).2) (fun x _ ↦ Set.mem_iUnion.2 (by_contra fun c ↦ c ⟨1, by
   simpa using H _ fun f ↦ not_lt.1 fun l ↦ c ((exists_pow_lt_of_lt_one (by positivity : 0 < r / (‖g x‖ + 1)) l).imp' (f ^ ·) fun _ h ↦ by simp; grw [h]; simp [field])⟩)) fun e f ↦ ⟨e * f, by
   refine ⟨mul_comm f e ▸ ?_, ?_⟩ <;> simp_intro x h <;> grw [norm_coe_le_norm, b] <;> simpa⟩
 choose d D h using h (epsilon Z)
 refine (S (φ - d) o fun x hx ↦ h x (fun u U ↦ ?_) |> (by simp [·, o.le])).elim fun e c ↦ e.2 (I (mem_sup.2 ⟨_, e.1.2.1 _ D, _, by simpa [mul_sub] using! c, add_sub_cancel ..⟩))
 let v := u - .const _ (u (epsilon Z))
 have ⟨y, Y, M⟩ := (isClosed_le (by fun_prop) (by fun_prop)).isCompact.exists_isMaxOn ⟨_, hx⟩
  (f := (‖v ·‖)) (by fun_prop)
 exact eq_of_norm_sub_le_zero ((M hx).trans (not_lt.1 fun p ↦ (S v p M).elim fun f c ↦ (@epsilon_spec _ Z ⟨y, Y⟩ ⟨⟨(v y)⁻¹ • (f * v), A.smul_mem (mul_mem f.1.2.1 (sub_mem U
  (algebraMap_mem ..))) _, by simpa [norm_smul, field]⟩, fun c ↦ (Y ⟨_, f.2 ∘ (m.sub_mem_iff_left c).1⟩).not_gt (by simp [mul_comm, norm_pos_iff.1 p])⟩).not_gt (by aesop)))
private lemma k7 {l N Φ} [Fact l.Prime] [Algebra ℚ_[l] k] [a : IsAlgClosed k] [Fintype Φ] (z : C(X, Φ → GL _ k)) (L : IntermediateField ℚ_[l] k) [Module.Finite ℚ_[l] L] (hL : ∀ γ τ i j, z γ τ i j ∈ L) {φ} (hφ : Continuous φ) (hi : φ.FactorsThrough z) : φ ∈ t7 {ψ | ∃ κ e, ∃ β ξ : WeylIndex (Fin N) κ → k, (∀ τ, FreeInts fun j : Fin N ↦ -∑ h ∈ Ioo ↑j N, (κ τ h + 1)) ∧ ψ = fun γ ↦ β ⬝ᵥ weylRep κ e (z γ) *ᵥ ξ} := by
  have f (y : Fin N → ℕ) (l : ∀ i, ∀ j > i, y j < y i / (N + 1) ^ 2) : FreeInts (-y ·) := fun d o ↦ StrictAntiOn.injOn (α := Lex _) (by
    rintro (α : _ →₀ ℕ) rfl (β : _ →₀ ℕ) (_ : _ = _) (⟨j, H⟩ : α.Lex _ _ β)
    have := sum_mono fun i ↦ show α i * y i + α i + ite (i = j) (y j + 1) 0 ≤ β i * y i + β i + α i * (y j / (N + 1) ^ 2) by
      grind [mt (Nat.mul_le_mul_left (α i) ∘ l j i), mul_le_mul_left H.2 (y j)]
    simp [← sum_mul] at *; grw [o, Nat.mul_div_le] at this; bound)
  have ⟨v, hv⟩ := @exists_linearIndependent_of_le_rank L k _ _ _ N (not_lt.1 fun h ↦ by
    obtain := rank_lt_aleph0_iff.1 (h.trans (by simp)), @Finite.trans ℚ_[l] L k
    grind [finrank_pos, Int.eq_zero_of_abs_lt_dvd ⟨_, by simpa [Algebra.norm_natCast] using congr((Algebra.norm ℚ_[l] $((a.exists_pow_nat_eq l (finrank ℚ_[l] k).succ_pos).choose_spec.symm)).valuation)⟩])
  let y (x : (Σ _ : Φ, Fin N) × ℕ) := ite (x.2 ≤ x.1.2) (v x.1.2) 0
  let κ (d : Φ → ℕ) τ h := (N + 1) ^ (4 * (N - h)) + ite (h = 1) (d τ) 0
  let E F : C(X, k) := ⟨fun γ ↦ (rowSubst (z γ ·|>.1) F).eval y, by simp [rowSubst, eval₂_eq]; fun_prop⟩
  let w := ∏ τ, @tableauPoly _ _ k _ (N + 1) (κ 0 τ) (Sigma.mk τ) fun h _ ↦ Fin.castLE h.is_le
  refine t8.2 fun ε o ↦ (k6 (span k {E F | (d) (F ∈ nabla
    k _ (diagramWeight _ (κ d)))}) ⟨φ, hφ⟩ (fun γ ↦ ⟨_, subset_span ⟨0, _, smul_mem _ (φ γ / w.eval y) (rowSubst_mem_nabla (z γ ·)⁻¹ (prod_tableauPoly_mem_nabla : w ∈ _)), rfl⟩, fun δ h ↦ fun t ↦ by simp +zetaDelta [t, hi t, rowSubst_rowSubst, tableauPoly, prod_eq_zero_iff, BlockTriangular, hv.ne_zero, det_of_isLowerTriangular] (funext fun τ ↦ Units.ext (ext fun a b ↦ congr($(linearIndependent_iffₛ.1 hv (⟨_, hL δ τ a ·⟩) (⟨_, hL γ τ a ·⟩) (h (E (.X (⟨τ, a⟩, 0))) (mapsTo_span (f := .mulLeft ..) ?_) |> (by simpa [E, rowSubst] using! ·)) b).1)))⟩) ε o).imp' _ fun _ ↦ .imp (mapsTo_span (f := coeFnLinearMap _) ?_ ·) (norm_le _ o.le).1 <;> rintro _ ⟨d, F, c, rfl⟩
  · use d + Pi.single τ 1, minor _ ![⟨τ, a⟩] * F, ?_, ext (by simp [E])
    convert SetLike.mul_mem_graded (minor_mem_nabla (Fin.forall_fin_one.2 rfl)) c; ext ⟨⟩
    simp [diagramWeight_apply, κ]; grind [a.2]
  exact (nabla_le_span_nablaBasis_mul_detPow _ (by simpa [diagramWeight, sum_range_succ] using c)).elim fun β h ↦ ⟨_, (κ d · N), β, (eval y <| nablaBasis k _ _ · * detPow k _ (κ d · N)), fun τ ↦ f _ fun i j h ↦ by
    grw [← single_le_sum (a := j.1), add_assoc, ← le_self_add, Nat.pow_div, ← mul_pow_sub_one, sum_le_card_nsmul, smul_eq_mul, mul_lt_mul_iff_left₀]
    any_goals grind [Nat.card_Ioo]
    simp +contextual (disch := grind) [κ, ite_eq_right, pow_lt_pow_right₀], funext (by simp [E, ← h, weylRep, mulVec, dotProduct, mul_sum, Units.smul_def, sum_mul, mul_assoc, linearCombination_apply])⟩
open RingHomClass IntermediateField Polynomial Filter Topology Metric Units
variable {E n : Type} [Field E] [CMType E] [Fintype n] {l} [Fact l.Prime] [PadicIso l] (κ κ' : Weight E)
@[simps! -isSimp toFun] def k8 := (⟨.pi fun v ↦ (GeneralLinearGroup.map
 (exists_placeOfEmb_extension (weightEmbedding (toRingHom ιℓ) v)).choose).comp (Gf.atPlace _), continuous_pi fun _ ↦ (continuous_adeleExtension _).generalLinearGroup_map.continuousOn.domRestrict⟩ : Gf E n →ₜ* _)
def s08_k9 M := (⟨⟨fun f x ↦ (M *ᵥ weylRep κ'.1 κ'.2 (k8 x.1)⁻¹ *ᵥ ιℓ ∘ f x.1)
 x.2, by aesop⟩, by simp [_root_.funext_iff, entrywise, Finset.mul_sum, mul_left_comm]⟩ :
 (Gf E n → _) →ₛₗ[toRingHom ιℓ] _ × WeylIndex n κ.1 → _)
private lemma p3 γ x : ιℓ ∘ (stdSpace E n).weightRep κ.1 κ.2 γ x = weylRep _ κ.2 (k8 (stdEmbFin γ)) *ᵥ ιℓ ∘ x := by
 convert! map_weightRep ιℓ.toRingHom ..
 ext; simpa [k8_toFun, Gf.atPlace] using! adeleExtension_algebraMap ..
lemma p4 {κ f} (hf : f ∈ (stdSpace E n).forms κ) : ∃ L : IntermediateField ℚ_[l] _, Module.Finite ℚ_[l] L ∧ ∀ g i, ιℓ (f g i) ∈ L := by
 have := IsLevel.mk inf_le_left (isOpen_Kf.inter hf.1)
 use adjoin _ ((⋃ v, .range (weightEmbedding (E := E) ιℓ v)) ∪ ⋃ c : StdClasses (Kf .. ⊓ rightStab f), .range (ιℓ ∘ f c.out)), ?_, fun g i ↦ ?_
 rw [adjoin_union, adjoin_iUnion]; apply +allowSynthFailures IntermediateField.finiteDimensional_sup
 simp
 obtain ⟨_, _, k, rfl⟩ := exists_eq_map_mul_rep_mul stdEmbFin (Kf .. ⊓ rightStab f) (·.out_eq) g
 rw [k.2.2, hf.2, stdSpace_weightRep_apply]; apply ((adjoin ..).toSubring.comap ιℓ.toRingHom).sum_mem fun _ _ ↦ mul_mem (weylRep_entry_mem ..) _ <;> simp [mem_intGL, ← map_inv] <;> bound
variable {ℓ} [ThePrime ℓ] {E n : _} {H} [Field E] [EmbeddedNumberField E] [Fintype n] [Group H] [TopologicalSpace H] {P : FinPlace E → _} {j} {ρ : H →* GL n (PadicAlgCl ℓ)}
lemma norm_eq_one_of_continuous [CompactSpace H] {ψ : H →* (PadicAlgCl ℓ)ˣ} (h : Continuous ψ) g : ‖(ψ g).1‖ = 1 := have ⟨a, b⟩ := (continuous_val.comp h).norm.exists_forall_ge (by simp)
 by simpa [field, antisymm_iff] using max_le (b (a * g)) (b (a / g))
lemma norm_coeff_le_of_mul_monic {D R : (PadicAlgCl ℓ)[X]} {η} (hR : R.Monic) (h : ∀ i, ‖(D * R).coeff i‖ ≤ η) i : ‖D.coeff i‖ ≤ η := by simpa [hR] using (mul_le_mul (le_supNorm ..) (R.le_supNorm R.natDegree) (by simp) D.supNorm_nonneg).trans (D.gaussNorm_mul (v := NormedField.toAbsoluteValue _) isNonarchimedean_norm one_pos R ▸ (supNorm_eq_iSup _).trans_le (ciSup_le h))
lemma Attached.tendsto_charpoly_coeff [PadicIso ℓ] (h : Attached P ρ j) x i : Tendsto (ιℓ <| P ·.w |>.coeff i) (mostFrobeniiAt E (j x)) (𝓝 ((ρ x).1.charpoly.coeff i)) := nhds_basis_closedBall.tendsto_right_iff.2 fun η
 p ↦ mem_inf_of_inter (h.2.2.2 η p) (Filter.map_comap_le
 (h.2.2.1.image_mem_nhds ((((MvPolynomial.continuous_eval _).comp (h.rec (by fun_prop))).congr fun x ↦ charpoly.univ_coeff_eval₂Hom n _ (ρ x).1.uncurry i).tendsto x (closedBall_mem_nhds _ p))))
 fun y ⟨b, z, u, v⟩ ↦ closedBall_eq_of_mem u ▸ by simpa [dist_eq_norm'] using! b _ v i
lemma Attached.trace_eq [PadicIso ℓ] {G} [Group G] [TopologicalSpace G] {j'} {σ : G →* GL n _} (h : Attached P ρ j) (h' : Attached P σ j') x {y} (e : j x = j' y) : (ρ x).1.trace = (σ y).1.trace := by simp [Polynomial.ext (tendsto_nhds_unique (h.tendsto_charpoly_coeff ..) <| e ▸ h'.tendsto_charpoly_coeff y ·), trace_eq_sum_roots_charpoly]
open NumberField IsCMField Kronecker Set RingHom
variable {E : Type} [Field E] [CMType E] {N} {l : _} [Fact l.Prime] [PadicIso l] (κ : _) (w : FinPlace E) (hw : _ ≠ w) (g : GL (Fin N) (LocField w))
def p5 v := let u := placeOfEmb (weightEmbedding ιℓ.toRingHom v); u = star w ∨ u = w
lemma p6 σ (h : inducedPrime σ = w) : p5 w (.mk σ) := h ▸ .imp (by erw [placeOfEmb_comp_star, ·])
 (by erw [weightEmbedding, RingHom.comp_assoc, ← isConj_complexConj]; aesop) (Φ_eq_or σ)
lemma p7 {τ} (h : ↑l ∈ w.1 → ¬p5 w τ) : k8 (atSplit hw g) τ = 1 := by
 rw [k8_toFun, atPlace_atSplit_of_ne] <;> aesop (add simp p5)
lemma p5.p8 {v g} (h : p5 w v) (e : k8 (n := Fin N) g v = 1) : g.atPlace w = 1 := have := (map_eq_one_iff _ (Units.map_injective (Matrix.map_injective (RingHom.injective _)))).1 e
 h.rec (Gf.atPlace_star_eq_one_iff.1 <| · ▸ this) (· ▸ this)
lemma p9 j : ∃ a ≠ 0, (↑l ∉ w.1 → a = -1) ∧ ∃ T : _ →ₗ[PadicAlgCl l] _ → _, (∀ φ r, (∀ z, ‖φ z‖ ≤ r) → ∀ z, ‖T φ z‖ ≤ r) ∧ ∀ {κ' f} M P, let F := s08_k9 (n := Fin N) κ κ' M f
 HasHeckePolyAt f w hw P → (∀ g : GL (Fin N) _, let z := k8 (atSplit hw g)
  weylRep κ.1 κ.2 z * M * weylRep κ'.1 κ'.2 z⁻¹ = M) → T F = (a * ιℓ (P.coeff j)) • F := let s U : Gf E (Fin N) := atSplit hw (transposeGL (basicCosetRep U))
 let Y := Option.elim' 1 fun (U, a, b) ↦ weylRep κ.1 κ.2 (k8 (s U)) a b
 have ⟨y, hT⟩ := Finite.exists_max (‖Y ·‖)
 have := (Units.norm_pos 1).trans_le (hT none)
 ⟨-(Y y)⁻¹, by aesop, by cases y <;> aesop (add simp [weylRep, p7]), (_ : ℤ) • -(Y y)⁻¹ • ∑ U ∈ _, .pi fun (g, i) ↦ ∑ b, Y (U, i, b) • .proj (g * s U, b), fun φ r H z ↦ (IsUltrametricDist.norm_zsmul_le ..).trans (by
  simp [field, ← sum_product', (exists_norm_finsetSum_le ..).elim
  fun _ ↦ (·.2.trans (norm_mul_le_of_le (hT _) (H _)))]), fun M P ⟨k, t, p, e⟩ hL ↦ by
  simp [p, _root_.funext_iff, mul_assoc, ← mul_sum, -Int.cast_ite, -mul_eq_mul_left_iff, ← by simpa [heckeSplit, heckeGL_eq_sum ((mem_sphericalAt_iff _).1 k)] using (congr(s08_k9 _ _ M $(e (N - j)) ·))]
  congr!
  simpa [s08_k9, ← mulVec_mulVec] using! congr($(hL _).mulVec ..)⟩
attribute [local fun_prop] Continuous.if_const
attribute [local simp] mulIndicator
lemma g3 {K} (hK : IsLevel (n := Fin N) K) {θ : K →* ℂ} (n : θ =ᶠ[nhds
  1] 1) (T : Set _) (f : (stdSpace E _).forms κ) (t : ∀ d, (∀ τ ∈ T, k8 d.1 τ = 1) → d.1 ∈ rightStab f.1 ∧ θ d = 1) {D} (hD : ∀ ν, ∀ φ ∈ levelSpace ((stdSpace ..).formTranslation ν) K θ, (∀ τ ∉ T, ν.1 τ = κ.1 τ ∧ ν.2 τ = κ.2 τ) → (∀ τ ∈ T, FreeInts fun j : Fin N ↦ -∑ h ∈ .Ioo ↑j N, (ν.1 τ h + 1)) → ∀ M, (∀ z : _ → GL (Fin N) (PadicAlgCl l), (∀ τ ∈ T, z τ = 1) → weylRep κ.1 κ.2 z * M * weylRep ν.1 ν.2 z⁻¹ = M) → s08_k9 κ ν M φ ∈ span (PadicAlgCl l) D) : s08_k9 κ κ 1 f.1 ∈ t7 D := by
 have A := exists_transporter stdRatPoints Fact.out .rfl K
 let s c g := (A c g).choose
 let u c k := (ιℓ (θ k), ιℓ (θ k⁻¹) • ιℓ ∘ f.1 (c * k))
 have hu c : Continuous (u c) := (isLocallyConstant_of_eventually_mul ((n.and (IsOpen.mem_nhds
  (.preimage_val f.2.1) (by simp))).mono (by simp +contextual [u, ← mul_assoc]))).continuous
 let R c k := (u c k).1 • weylRep κ.1 κ.2 (Tᶜ.mulIndicator (k8 (c * k.1)⁻¹))
 let q {c g} (γ : s c g) : K := ⟨_, (((A ..).choose_spec.1 _).1 γ.2).2⟩
 let L c y := LinearMap.pi fun x : _ × _ ↦ dotProductEquiv _ _ ((R c · x.2 y) ∘ q) ∘ₗ .funLeft _ _ (@q c x.1)
 let Φ c k := weylRep _ κ.2 (T.mulIndicator (k8 (c * k.1)⁻¹)) *ᵥ (u c k).2
 have a c g γ : R c (@q c g γ) *ᵥ Φ c (q γ) = (s08_k9 _ κ 1 f ⟨g, ·⟩) := by
  simp +contextual [Φ, R, u, q, s08_k9, mul_assoc, (f.2.2 · g), p3, ← (weylRep ..).map_mul, Pi.mul_def, Pi.inv_def, ((Group.isUnit _).map θ).ne_zero]
 convert sum_mem (t := .univ) fun (c : StdClasses K) _ ↦ (fun c ↦ Submodule.smul_mem _ (s c
  c).card.cast⁻¹ (sum_mem (t := .univ) fun y _ ↦ (?_ : L c y (Φ c · y) ∈ t7 D))) c.out
 simp [L, s, ↓(A ..).choose_spec.2, dotProduct, sum_comm, ← mulVec_apply_eq_sum, *, -mem_classAut, -MonoidHom.coe_range, _root_.funext_iff, HasFiniteType.finite_aut, DoubleCoset.out_eq', Nat.card_pos.ne']
 have : Continuous fun k ↦ ((R c k · y), Φ c k y) := by dsimp [R, Φ, weylRep]; fun_prop
 have ⟨_, p, H⟩ := (isCompact_range this.fst).isBounded.exists_pos_norm_le
 refine t8.2 fun ε o ↦ (t8.1 (k7
  (.mk fun k (τ : T) ↦ k8 (c * k.1)⁻¹ τ) _ (fun _ τ _ _ ↦ mem_of_le_of_mem (le_iSup _ τ) ((exists_placeOfEmb_extension _).choose_spec.2.2.1 _))
  this.snd (mul_left_surjective · |>.forall.2 fun d h ↦ by
  clear * - h t; simp_all +unfoldPartialApp [_root_.funext_iff, Φ, u, ← mul_assoc, (t ..).1 _]))
  _ (div_pos o p)).imp' _ fun _ ↦ .imp ((map_span_le ..).2 ?_ ⟨_, ·, rfl⟩) fun h x ↦ congr(‖$(map_sub (L ..) ..) x‖).ge.trans (norm_sum_le_of_forall_le_of_nonneg o.le fun _ _ ↦ (norm_mul_le_of_le ((norm_le_pi_norm ..).trans (H _ ⟨_, rfl⟩)) (h _)).trans_eq (by field))
 rintro _ ⟨a, b, β, ξ, he, rfl⟩
 let e {α} := Equiv.piEquivPiSubtypeProd (· ∈ T) α
 have H μ {p} (h : e μ = p) : ∃ σ : _ ≃ _, ∀ η (z : type_of% (k8 c)), weylRep μ η z = (weylRep p.1 (e η).1 (z ·) ⊗ₖ weylRep p.2 (e η).2 (z ·)).submatrix σ σ := h ▸ ⟨e, by
  simp [← Matrix.ext_iff, weylRep, @schur_apply_eq_prod (Subtype.{1} _), schur_apply_eq_prod (κ := μ), ← Fintype.prod_subtype_mul_prod_subtype (· ∈ T), mul_smul_mul_comm]; tauto⟩
 obtain ⟨⟨ρ, G⟩, σ, H⟩ := H _ (e.apply_symm_apply (a, (e κ.1).2)), H κ.1 rfl
 let M := (vecMulVec (col 1 (σ y).1) β ⊗ₖ 1).submatrix σ ρ
 convert ← hD (_, e.symm (b, (e κ.2).2)) _ (deltaForm (o := ⟨n⟩) _ _ _ c (ιℓ.symm ∘ ((replicateCol
  _ ξ ⊗ₖ 1).submatrix ρ σ *ᵥ Pi.single y 1))).2 (by simp +contextual [e]) (by simpa +contextual
  [e] using he) M fun z h ↦ by simp [M, *, ← Pi.one_def, ← map_mul, Pi.mul_def]
 ext; refine (map_sum (.proj _ ∘ₛₗ s08_k9 _ (_, _) M ∘ₛₗ .const ∘ₛₗ .applyₗ _) ..).trans
  ((sum_coe_sort ..).symm.trans congr(∑ γ, $((dite_eq_left (q γ).2).symm ▸ ?_)))
 simp [s08_k9, Function.comp_def _ (_ ∘ _), p3 (_, _), ← map_mul, -mulVec_single, ← (weylRep _ _ _).mul_assoc, M.mul_assoc]; simp [M, *, ← Pi.one_def, -mulVec_mulVec, mul_assoc, q, R, vecMulVec_mulVec, ← replicateCol_mulVec]; split <;> ring
