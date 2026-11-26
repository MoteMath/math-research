import Lib.Weil.DualPair.PairReal
noncomputable section
attribute [-instance] Prod.isMulCommutative CommMonoid.toCommSemigroup
open MeasureTheory Space
variable {E n n' : Type} [Field E] [CMType E] [Fintype n] [Fintype n'] {s : n → ℤˣ} {t : n' → ℤˣ}
  {X : Type _} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] {S : Space E n s}
  {T : Space E n' t} {φ : X} {y : G E s → ℂ} {y' : G E t → ℂ} (K : ThetaKernel X S T)
  (hr : y ∈ S.rapidFunctions)
def Space.lift φ (y : _ → ℂ) h := ∫ g, K.θ (K.ω (g, h) φ) * y g ∂S.quotMeasure
variable (S T) in
structure Space.ModerateWeight where
  (weightFn : C(G E s, ℂ)) (groupMap : C(G E s, G E t)) isModerate : S.IsModerate weightFn
  height_le : ∃ C, ∀ g, T.height (groupMap g) ≤ S.height g * C
attribute [local simp] lift mul_pow rep_apply_apply le_of_lt
attribute [local simp ←] integral_const_mul mul_assoc
omit [CompleteSpace X] in
lemma lift_mul_right h k : lift K φ y (h * k) = lift K (K.ω (1, k) φ) y h := by simp
namespace ThetaKernel
@[simps] abbrev swap : ThetaKernel X T S :=
  ⟨K.ω.comp MulEquiv.prodComm.toMonoidHom, K.θ, by simp; fun_prop, by simp_all [K.4]⟩
omit [CompleteSpace X] in
lemma theta_rat_mul {h} : ∀ γ ∈ S.Γ, ∀ g, K.θ (K.ω (γ * g, h) φ) = K.θ (K.ω (g, h) φ) := by
  grind [K.4, one_mul h, one_mem]
omit [CompleteSpace X] in
lemma isAutomorphic (L : OpenSubgroup _) (a : ∀ k ∈ L, K.ω ((1, k), 1) φ = φ) h : S.IsAutomorphic
  (K.θ <| K.ω ⟨·, h⟩ φ) := ⟨by fun_prop, K.theta_rat_mul, L, (by nth_rw 2 [← a · ·]; simp)⟩
lemma moderate_growth : ∃ C A, ∀ g h φ, ‖K.θ (K.ω (g, h) φ)‖ ≤
  C * ‖φ‖ * (S.height g * T.height h) ^ A := by
  choose A a _ _ b using
    ((K.swap.exists_rat_norm_le_height 1).and (K.exists_rat_norm_le_height 1)).exists
  choose _ _ a using a
  exact ⟨_ * (2 * 2) ^ A, _, fun g h φ ↦ by simpa [*, mul_right_comm, K.4] using
    (K.θ.le_opNorm_of_le ((_ ∘L _).le_of_opNorm_le (norm_mul_le_of_le (a g) (b h)) φ))⟩
lemma isModerate φ h : S.IsModerate (K.θ <| K.ω ⟨·, h⟩ φ) :=
  ⟨_, _, (by simpa using K.swap.moderate_growth.choose_spec.choose_spec h · φ)⟩
section
omit [CompleteSpace X]
lemma fixesLeft_lift : T.Γ.FixesLeft (lift K φ y) := fun _ ↦ (by simp [← K.4 (one_mem _) · _ ·])
lemma lift_equivariant (hy : S.IsAutomorphic y) φ k l h : lift K φ y (h * l) =
  lift K (K.ω (k, l) φ) (y <| · * k) h
  := by cases hy; simpa using (integral_comp_mul_right k (by grind [theta_rat_mul])).1.symm
lemma lift_omega_left (hy : S.IsAutomorphic y) k : lift K (K.ω (k, 1) φ) y =
  lift K φ (y <| · * k⁻¹) := funext (by simpa using K.lift_equivariant hy (K.ω (k, 1) φ) k⁻¹ 1)
end
include hr
lemma exists_norm_theta_mul_le : ∃ C A, ∀ φ g h, ‖K.θ (K.ω (g, h) φ) * y g‖ ≤
  T.height h ^ A * |C| * ‖φ‖ := have ⟨C, A, H⟩ := K.moderate_growth; (hr.2 A).elim (⟨|C| * ·, A, by
  introv; grw [norm_mul, H, le_abs_self C, ← le_abs_self, ← ·] <;> simp [field]⟩)
lemma integrable_theta_mul φ h : Integrable (fun g ↦ K.θ (K.ω (g, h) φ) * y g) S.quotMeasure :=
  (hr.2.mul (isModerate ..)).integrable (hr.1.rec (by fun_prop))
def liftBilin : X →ₗ[ℂ] S.rapidFunctions.1 →ₗ[ℂ] G E t → ℂ := by
  refine' .mk₂ ℂ (lift K · ·) .. <;> simp [add_mul, funext_iff, mul_add, integral_add,
    integrable_theta_mul]
  ac_nf; simp
lemma exists_clm_lift : ∃ L : _ → X →L[ℂ] ℂ, ∀ φ h, lift K φ y h = L h φ := ⟨(strongIntegral
  S.quotMeasure fun g ↦ y g • K.θ ∘L K.ω ⟨g, ·⟩), by simp [strongIntegral_apply, mul_comm (y _),
  integrable_theta_mul, *]⟩
lemma integrable_prod_weightFn {m} [Fintype m] {u F} {U : Space E m u} (w : U.ModerateWeight T) (r :
  F ∈ U.rapidFunctions) φ : Integrable (fun p ↦ (⇑w.weightFn * F) p.1 *
  (K.θ ((K.ω (p.2, w.groupMap p.1)) φ) * y p.2)) (U.quotMeasure.prod S.quotMeasure) := .of_bound
  (hr.1.rec (r.1.rec (by fun_prop))) _ (.of_forall (by
  grw [norm_mul, (K.exists_norm_theta_mul_le hr).choose_spec.choose_spec, w.4.choose_spec ·.1,
    le_abs_self (_ ^ _)] <;> simp [-Pi.mul_apply, abs_of_pos]; grw [(r.2.mul w.3 _).choose_spec]))
lemma integral_lift_eq_integral_descent (hr' : y' ∈ T.rapidFunctions) :
    ∫ h, y' h * lift K φ y h ∂T.quotMeasure = ∫ g, y g * lift K.swap φ y' g ∂S.quotMeasure := by
  simp; rw [integral_integral_swap]; ac_rfl
  simpa using! K.integrable_prod_weightFn hr ⟨1, .id _, ⟨1, 0, by simp⟩, 1, by simp⟩ hr' φ
end ThetaKernel
end
def DescentsVanish {E n m} [Field E] [CMType E] [WeilData E] [Fintype n] [Fintype m] {s t} (W :
  Space E n s) (V : Space E m t) a S Y := ∀ f, Space.projOn _ S f = f →
  Space.lift (pairThetaKer W V a 1).swap f Y = 0
section
open MeasureTheory Matrix Kronecker WeilData Space Prod G IsDualFamily Heisenberg ENNReal MatMul
variable {E : Type} [Field E] [CMType E] {n n' p q : Type} [Fintype n] [Fintype n'] {s s'}
  (S : Space E n s) (T : Space E n' s') (a b) (g : G E s) (c : Matrix n q E)
noncomputable def Space.coordMatrix := g⁻¹.mat * (S.x⁻¹.1 * c.map toAdele)
variable {g c R} [CommRing R] [Nontrivial R] {φ : 𝔸f E →+* R} [Fintype p]
lemma Space.mul_coordMatrix_ne_zero (hc : c ≠ 0) (X : GL p (𝔸 E)) {M : Matrix p n _} :
  HasLeftInv (M.map φ) →
  (X.1.map snd)ᴴ * (M * (S.coordMatrix g c).map snd) ≠ 0 := fun ⟨_, h⟩ e ↦ let ψ := φ.comp (.snd ..)
  hc (map_injective (ψ.comp _).injective (mul_right_injective_of_inv _ _ ((S.x * g.toUnitary).map
    ψ).3 (mul_right_injective_of_inv _ _ h (mul_right_injective_of_inv _ _ ((star X).map ψ).4 (by
         simpa [coordMatrix, ← RingHom.coe_snd, -coe_units_inv] using! congr(($e).map φ))))))
lemma Space.coordMatrix_mul_ne_zero (hc : c ≠ 0) (X : GL p (𝔸 E)) {M : Matrix n p _} (h :
  HasLeftInv (M.map φ)ᵀ) :
  ((S.coordMatrix g c).map snd)ᴴ * (M * X.1.map snd) ≠ 0 := fun e ↦ S.mul_coordMatrix_ne_zero (φ :=
  φ.comp starRingAut.toRingHom) hc X (M := Mᴴ) (by convert h; aesop) (by simpa using congr($eᴴ))
lemma Space.exists_short_isotropic (h : 2 < S.height g) : ∃ x ≠ 0, xᴴ * S.J * x = 0 ∧ ∀ j : Unit,
  x.col j ∈ (S.move g).latticeBall (2 / S.height g) := by
  have := (S.move g).firstMinimum_pos; simp [height, field] at *
  obtain ⟨x, hx, _,
    e⟩ := by simpa [h.le] using le_firstMinimum_iff.2.mt (lt_two_mul_self this).not_ge
  use replicateCol _ x, by simpa, funext₂ fun _ _ ↦ (form_eq_zero_of_norm_mul_lt_one hx hx (by
    simp [← sq, e.trans h]) :), by bound
variable [WeilData E] [Fintype q] {P} (hP' : Set.IsConjDisjoint P) {Ψ} [hΨ :
  IsSchwartzBruhat (E := E) (n := n' × n) P Ψ] {S T}
@[simp] lemma apply_vecAtPoint (f : 𝒮 S) γ : f (S.vecAtPoint γ) =
  f 0 := by simp [← S.apply_vecAtPoint_add f γ 0]
include hP' hΨ
lemma name_eq_zero_of_invariant (X : Matrix _ p (𝔸 E)) (Y : Matrix n q (𝔸 E)) {ℓ : _ →L[ℂ] ℂ} (h :
  ∀ z f, ℓ ((S.hom T).ϱ (X ⊗ₖ (Yᴴ * stdForm E s)ᵀ *ᵥ z) f) = ℓ f) (hK : ∀ y, Ψ y ≠ 0 → (X.map snd)ᴴ
  * (vecToMat y * Y.map snd) ≠ 0) f : ℓ (name _ P Ψ f) = 0 := hΨ.mem_of_cosets ((ℓ ∘L .apply ℂ _
  f).ker.comap _) fun y hy ↦ (hK y hy).imp_symm fun N ↦ ext fun i j ↦ let K x := (X x.1 i *
  star (Y x.2 j)).2; .trans (by
    simp [K, entrywise, Fintype.sum_prod_type, vecToMat, Finset.mul_sum]; ac_rfl)
    (eq_zero_of_forall_mul_integral (a := star K ⬝ᵥ y) fun u ↦
    (stdLattice.forall_psi₀_mul_eq_one_iff _).1 fun v _ ↦ by_contra (N ⟨_, .symm ⟨fun _ _ _ e ↦
    eq_zero_of_mul_eq_self_left · (.trans (by erw [ϱ_name hP', IsSchwartzBruhat.schrodingerAct_star
    hP' (star (u * v) • K), mul_right_comm, funext fun x ↦ mul_eq_mul_right_iff.2
    (or_not.imp (e x) (ite_eq_right ·)), LinearMap.map_smul]; simp; rfl) (congr(ℓ (ϱ _ $(by
    ext <;> simp [finVec, stdForm]; ring) _)).trans (h (Pi.single (i, j) (0, α.1 * idem _ * star
    (_ * u * v))) _))), (isLocallyConstant_psi₀.comp_continuous (by fun_prop)).eventually_eq _⟩⟩))
lemma exists_norm_name_le {f₀} (hf : f₀ ∈ finitePart _) N A Y Z : ∃ C, ∀ v g h (ℓ : _ →L[ℂ] ℂ) ρ H,
  let L := ℓ ∘L pairWeil S T a b (g, h); weightedNorm (N + A) v ≠ ⊤ → 1 ≤ ρ → 0 < H → (∀ f, ‖L f‖ ≤
    Y * ‖f‖ * (ρ * H) ^ A) → (2 < H → ∃ d c x y, (∀ i : p, d.col i ∈ (T.move h).latticeBall x) ∧
    (∀ j : q, c.col j ∈ (S.move g).latticeBall y) ∧ x * y ≤ Z * ρ * (2 / H) ∧ (dᴴ * T.J * d = 0 ∨
    cᴴ * S.J * c = 0) ∧ (∀ (z : Matrix _ q E) f, ℓ (ϱ _ (matToVec (T.ratMap S (z * cᴴ * S.J))) f) =
    ℓ f) ∧ ((∀ y, Ψ y ≠ 0 → ((T.coordMatrix h d).map snd)ᴴ * (vecToMat y * (S.coordMatrix g c).map
    snd) ≠ 0) ∨ ∀ f B, (∀ z, ‖L (f - ϱ _ (T.coordMatrix h d ⊗ₖ ((S.coordMatrix g c)ᴴ *
  stdForm E s)ᵀ *ᵥ z) f)‖ ≤ B) → ‖L f‖ ≤ B)) → ‖L (integrated _ v (name _ P Ψ f₀))‖ * H ^ N ≤
    C * (weightedNorm (N + A) v).toReal * ρ ^ (N + 2 * A) := by
  obtain ⟨⟨C, hC⟩, ⟨M, hM, hL⟩, R, _, -, _, hb, -, -, hA⟩ :=
    @exists_enorm_le_mul_weightedNorm_of_sub .., exists_natCast_smul_mem_of_isCompact E
    (stdLattice.isCompact_stdLattice.smul (α (E := E))⁻¹.1) ((isLocallyConstant_rho_finVec
    (name_mem_finitePart P Ψ hf)).eventually_eq 0), exists_hasFundDomain_toAdele (E := E)
  use ?_
  intro v g h ℓ ρ t L hv hρ _ hY H; grw [le_abs_self Y, (mul_right_comm ..).le] at hY
  grw (transparency := .default) [← toReal_enorm, toReal_mono (mul_ne_top ofReal_ne_top hv) (hC
    (max 2 _ * ρ / t) (L ∘L (integrated _).flip _) (by positivity) fun l v B o ↦ ?_),
    toReal_ofReal_mul, L.opNorm_comp_le, L.opNorm_le_bound (by positivity) hY]
  simp [field, mul_pow, pow_add, div_pow, two_mul]; rw [mul_comm]; congr!; positivity
  obtain ⟨d, c, _, _, h₀, h₁, h₅, h₂, h₃, h₄⟩ := H (by grw [hρ] at l; field_simp at l; grind)
  set K := T.coordMatrix h d ⊗ₖ _
  have mul x y f : ϱ _ (K *ᵥ x) (ϱ _ (K *ᵥ y) f) = (S.hom T).ϱ (K *ᵥ (x + y)) f := by
    simp [adelicHeis, star_mulVec, dotProduct_mulVec, K, -Matrix.mul_assoc]
    cases h₂ <;> simp only [coordMatrix, gram_mul (mat _), mat_preserves_stdForm,
      gram_at_point_eq_map, *] <;> simp
  have hp f : IsContPeriodic (_root_.ratVectors ..) fun d ↦ L (ϱ _ (K *ᵥ d) f) := ⟨by fun_prop, by
    rintro _ ⟨ξ, ⟨⟩⟩ _; simpa [↓← mul, K, L, ↓kronecker_mulVec_eq_matToVec, pairWeil, ω_ϱ, -Rep.mul,
      coordMatrix, Space.ratMap, ← h.mat.mul_assoc, ← mat_mul, S.map_J,
      g⁻¹.mat_preserves_stdForm] using! h₃ (d * vecToMat ξ) _⟩
  clear_value L
  have e := by simpa using strongIntegral_apply _ (fun _ ↦ L ∘L _) (hp · |>.integrable_out)
  refine h₄.elim (fun h₄ k ↦ ?_) (· _ B)
    (((by simpa : (M : E) ≠ 0).isUnit.map toAdele).smul_bijective.2.forall.2 fun d ↦ ?_)
  simpa [quotMean, integral_sub, (hp _).integrable_out, ← e, integrated_name,
    name_eq_zero_of_invariant hP' _ _
    (fun z f ↦ (e _).trans (by simpa [e, ↓← mul] using! quotMean_translate (hp f) z))
    h₄] using norm_quotMean_le (_root_.ratVectors ..) k
  choose a hc _ using hA ∘' d
  have b i := hb (hc i)
  simp [-mulVec_add, -mulVec_smul, IsContPeriodic, finVec.eq_unfold, Set.mem_smul_set, baseLattice,
    archCoords, move_vecAtPoint,
    forall_and, Nat.cast_smul_eq_nsmul, -nsmul_eq_mul] at hL hp h₀ h₁ b ⊢
  erw [← hp.2 _ _ ⟨_, map_nsmul _ M a⟩, ← smul_add, mulVec_smul, rho_integrated_realCoord, hL,
    Rep.rho_zero_apply]
  refine o _ ((pi_norm_le_iff_of_nonneg (by positivity)).2 ?_)
  all_goals simp_intro .. [↓mulVec_eq_sum, fst_sum, snd_sum, K, stdForm, realCoord]
  grw [norm_sum_le, division_def, ← norm_inv, ← Pi.inv_apply, norm_le_pi_norm _⁻¹]
  simp; grw (transparency := .default) [(norm_le_pi_norm ..).trans (b.1 ..), (norm_mul ..).ge,
    norm_mul_le_of_le ((PiLp.norm_apply_le _ (_, _)).trans (h₀.2 _)) ((PiLp.norm_apply_le _
    (_, _)).trans (h₁.2 _)), h₅]
  exact .trans (b := (M * ∑ _ : p × q, Z * 2 * R) * ‖(scaleIdele E).1.1⁻¹‖ * ρ / t)
    (le_of_eq (by simp; ring)) (by gcongr; exact le_max_right ..)
  intro; apply sum_mem; intros; apply_rules [mul_mem, star_mem_Ô, b.2, h₀.1, h₁.1]
variable (S T φ hΨ)
lemma pairTheta_decay_of_onto (h : ∀ y, Ψ y ≠ 0 → HasLeftInv ((vecToMat y).map φ)ᵀ) N : ∃ B M C,
  ∀ v g h, weightedNorm M v ≠ ⊤ → ‖pairTheta S T a b (integrated _ v (name _ P Ψ (vacElem _))) (g,
  h)‖ * T.height h ^ N ≤ C * (weightedNorm M v).toReal * S.height g ^
  B := (pairThetaKer ..).moderate_growth.elim fun _ ⟨_, H⟩ ↦ ⟨_, _,
  (exists_norm_name_le a b hP' vacElem_mem_finitePart ..).imp fun _ D v g k ↦ (D v g k (θ _) _
  _ · (one_le_height g) (height_pos k) (H g k) (T.exists_short_isotropic · |>.imp fun x ⟨o, i, e⟩ ↦
  (S.exists_short_basis_matrix.choose_spec g).rec fun Y u ↦ ⟨_, _, _, e, u, (mul_comm ..).le, .inl
  i, by simp [← vecAtPoint_hom], .inl (T.coordMatrix_mul_ne_zero o (_ * (_ * Y.map _)) ∘ h · :)⟩))⟩
end
section
open Matrix Norms.L2Operator Function IsLocalRing Space
variable {n m : Type _} [Fintype n] [Fintype m] {ε : n → _} {ε' : m → _}
@[simp] lemma norm_fromBlocks x b : ‖@fromBlocks n m n m ℂ x 0 0 b‖ = ‖x‖ ⊔ ‖b‖ := by
  apply NonUnitalStarAlgHom.norm_map ({toFun := (fromBlocks · 0 0).uncurry, ..} :
    _ →⋆ₙₐ[ℂ] _) _ (x, b) <;> aesop_cat
@[fun_prop] lemma isProperMap_inl : IsProperMap (U.inl ε ε') := isProperMap_of_comp_of_t2 (g :=
  (·.1.1.onFun .inl)) (by simp [continuous_U_iff_matrix]; fun_prop) (by fun_prop)
  isClosedEmbedding_U.isProperMap
section
variable {E n n' : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {𝔪 : Modulus E}
noncomputable def modulusResidue (𝔪 : Modulus E) {w} (h : w ∈ 𝔪.places) :
    𝔪.ResRing →+* ResField w := Ideal.Quotient.lift _ _ (algebraMap_ResField_eq_zero.2 ∘ @h ·)
@[simp] lemma modulusResidue_reduction (𝔪 : Modulus E) {w} h x :
  modulusResidue 𝔪 h (𝔪.reduction x) = reduceAt w x := 𝔪.apply_reduction_eq_of_algebraMap x
end
variable {E n n' : Type} [Field E] [CMType E] {𝔪 : Modulus E} [Fintype n] [Fintype n'] {s : n → ℤˣ}
  {s' : n' → ℤˣ} (S : Space E n s) (T : Space E n' s')
lemma isPrimitiveMatrix_of_liftFn_ne_zero {ι Ψ} (e : Matrix n' n ι) (l : ∀ y, Ψ y ≠ 0 →
  HasLeftInv (e.map y)) ⦃w x⦄ (o : w ∈ 𝔪.places) (h : 𝔪.liftFn Ψ x ≠ 0) :
  IsPrimitiveMatrix (LocInt w).1 ((e.map x).map (evalAt w)) := ((dite_ne_right_iff.1 h).imp
  fun _ ↦ l _).elim fun i ⟨L, l⟩ ↦ ⟨by solve_by_elim [idem_mul_mem_Ô.1], _, .symm
  ⟨by simpa [o] using! Matrix.map_mul.symm.trans congr(Matrix.map $((Matrix.mul_assoc ..).trans
        (isUnit_of_mapMatrix (residue _) (M :=
  L.map (surjInv residue_surjective ∘ modulusResidue _ o) * e.map
  fun j ↦ ⟨_, mem_Ô.1 (i j) w⟩) (by simpa [comp_def, surjInv_eq] using! congr(IsUnit (Matrix.map $l
  (modulusResidue _ o))))).val_inv_mul) (LocInt w).subtype), by simp [IsIntMatrix]⟩⟩
lemma Space.height_sum_le g h : (S.sum T).height (.sum (g, h)) ≤ S.height g * T.height h := by
  simp [height, field, firstMinimum_pos, inf_le_firstMinimum_sum.trans']
lemma modDatum_eq_sum [WeilData E] Ψ v : modDatum S T 𝔪 Ψ v = ∑ x,
  Ψ x • modDatum S T 𝔪 (Pi.single x 1) v := by nth_rw 1 [pi_eq_sum_univ' Ψ]; simp [-Pi.single_apply,
  modDatum, comp_def, ← Finset.sum_fn, ← Pi.smul_def, -smul_eq_mul]
lemma pairTheta_modDatum_decay [WeilData E] a b {Ψ} (o : Nonempty 𝔪.places) (h :
  support Ψ ⊆ {y | HasLeftInv y}) M : ∃ B N C, ∀ v h g, weightedNorm N v ≠ ⊤ → ‖pairTheta S T a b
  (modDatum S T 𝔪 Ψ v) (g, h)‖ * S.height g ^ M ≤ C * (weightedNorm N v).toReal * T.height h ^
  B := let ⟨_, _, H⟩ := (pairThetaKer ..).swap.moderate_growth; ⟨_, _, (exists_norm_name_le a b
    𝔪.disjoint_places_star vacElem_mem_finitePart ..).imp fun _ D v k g ↦ (D v g k (θ _) _
    _ · (one_le_height k) (height_pos g) (H k g) fun l ↦ (T.exists_short_basis_matrix.choose_spec
    k).rec fun Y u ↦ ⟨_, (S.exists_short_isotropic l).imp fun x ⟨h0, i, e⟩ ↦ ⟨_, _, u, e, le_rfl,
    .inr i, by simp [← vecAtPoint_hom], .inl fun y c ↦ (S.mul_coordMatrix_ne_zero h0 (_ * (_ * Y.map
    _)) ((isPrimitiveMatrix_of_liftFn_ne_zero _ (by tauto) o.some.2 c).2.imp (by tauto)) :)⟩⟩)⟩
end
