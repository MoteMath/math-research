import Lib.GaloisRep.BaseChange.OrbitClassSum
import Lib.Adelic.Witt.SpaceOperations
section
lemma eq_zero_of_norm_Φ {E} [Field E] [NumberField E] [PlaceEmbedding E] {x : E} (h : IsIntegral ℤ x) : (∀ v, ‖Φ v x‖ < 1) → x = 0 := Not.imp_symm (NumberField.one_le_house_of_isIntegral h) ∘ by
 simp_all [NumberField.house, pi_norm_lt_iff, ← NumberField.InfinitePlace.apply]
open Set ENNReal Fintype Matrix MeasureTheory Metric NumberField Measure Classical
variable {E : Type _} [Field E] [CMType E] {n : Type _} [Fintype n] (y : GL n (𝔸 E))
lemma lintegral_encard_rat_points {S} (hS : MeasurableSet S) : .ofReal (ideleAbs y.det) * volume S = ∫⁻ x, {ξ | y⁻¹.1 *ᵥ (toAdele ∘ ξ + x) ∈ S}.encard ∂(ratVectors E n).qms := .trans (by simp)
 (((MeasurePreserving.comp ⟨by fun_prop, volume_map_mulVec_adele _⟩
 measurePreserving_addOrbitMeasure).measure_preimage (by aesop)).symm.trans (.trans (prod_apply (by
 measurability)) (lintegral_congr fun _ ↦ (count_apply .of_discrete).trans (mod_cast encard_congr
 (Equiv.ofInjective _ (@toAdele E ..).injective.comp_left).subtypeEquivOfSubtype.symm))))
lemma minkowski_first : ENNReal.ofReal (ideleAbs y.det) ≤ .ofReal (((2 * rootDiscr E) ^ numInfPlaces E) ^ card n) * {ξ | ∀ i, (y⁻¹.1 *ᵥ toAdele ∘ ξ) i ∈ ball 0 1 ×ˢ Ô E}.encard := by
 have := rootDiscr_pos E
 grw [← (lintegral_encard_rat_points y (.univ_pi fun _ ↦ ((@isOpen_ball _ _ 0 2⁻¹).prod isOpen_Ô).measurableSet)).trans_le (lintegral_le_const (.of_forall fun x ↦ ENat.toENNReal_mono
   (encard_le_encard_of_injOn (fun b h ↦ by simpa [mulVec_sub, ← two_mul] using (fun i
   ↦ sub_mem_sub (h i ⟨⟩) (epsilon_spec_aux ⟨0⟩ _ ⟨b, h⟩ i ⟨⟩))) sub_left_injective.injOn))),
   mul_left_comm, ofReal_le_of_le_toReal]
 simp (disch := bound) [volÔ_eq, volume_pi, volume_eq_prod, pi_ball, ← inv_pow, ← mul_pow]
 grind [Real.two_le_pi, one_le_pow₀]
lemma exists_ne_zero_inv_mulVec_mem (h : ((2 * rootDiscr E) ^ numInfPlaces E) ^ card n < ideleAbs y.det) : ∃ ξ, (∀ i, (y⁻¹.1 *ᵥ toAdele ∘ ξ) i ∈ ball 0 1 ×ˢ Ô E) ∧ ξ ≠ 0 := exists_ne_of_one_lt_encard (mod_cast one_lt_of_lt_mul_right (α := ℝ≥0∞) ((minkowski_first y).trans_lt' (by simpa))) 0
variable {n : Type _} [Fintype n] {E : Type _} [Field E] [CMType E] {s : n → ℤˣ} (V : Space E n s) (F : _ → ℂ)
noncomputable def dilationGroup {R : Type*} [CommRing R] [StarRing R] {m : Type*} (A : Matrix n m R) {J} := Subgroup.ofDiv {g : U J × Rˣ | g.1.1.1 * A = g.2 • A ∧ ∀ v w : Matrix n n R, Aᴴ * (J * v) = 0 → Aᴴ * (J * w) = 0 → wᴴ * (J * (g.1.1.1 * v)) = wᴴ * (J * v)} ⟨1, by simp⟩ fun _ g k h ↦ by
 constructor <;> intros <;> [rw [← smul_left_cancel_iff k.2, ← Matrix.mul_smul, ← h.1];
   erw [mul_assoc, g.2, ← h.2]] <;> simp_all [↓← Matrix.mul_assoc, smul_smul,
   ← U.gram_invariant k.1 _ _⁻¹]
noncomputable def Space.archCoords := AddMonoidHom.mk' (G := EuclideanSpace ℂ (_ × n)) (.toLp 2 fun p ↦ V.vecAtPoint · p.2 |>.1 p.1) (by aesop)
abbrev Space.latticeBall r := {y ∈ V.baseLattice | ‖V.archCoords y‖ ≤ r}
noncomputable def Space.firstMinimum := sInf (insert 1 ((‖V.archCoords ·‖) '' {y ∈ V.baseLattice | y ≠ 0}))
noncomputable def Space.height g := (V.move g).firstMinimum⁻¹
def Space.IsModerate := ∃ C B, ∀ g, ‖F g‖ ≤ C * V.height g ^ B
def Space.IsRapid := ∀ B, ∃ C, ∀ g, ‖F g‖ * V.height g ^ B ≤ C
variable {E : Type _} [Field E] [NumberField E] [NumberField.IsCMField E] {n : Type _} [Fintype n] {s : n → _}
lemma G.isClosedEmbedding_mat : Topology.IsClosedEmbedding (mat : G E s → _) := have e := U.isClosedEmbedding_mat (by simp); e.comp
   (toUnitary.1.3.isClosedEmbedding (.prodMk (continuous_pi (U.continuous_map <| continuous_apply · |>.fst')) (U.continuous_map continuous_snd)) (e.continuous_iff.2 continuous_mat))
lemma G.ext_mat {g g' : G E s} : g.mat = g'.mat → g = g' := (isClosedEmbedding_mat.1.2 ·)
lemma G.continuous_iff {X} [TopologicalSpace X] {f : X → G E s} : Continuous f ↔ Continuous (f · |>.mat) := isClosedEmbedding_mat.continuous_iff
instance {E : Type _} [Field E] [CMType E] (W : Space E n 1) : DiscreteTopology W.Γf := continuous_subtype_val.discrete_of_tendsto_cofinite_cocompact (.mono_left (by
 simpa [← Filter.coprod_cocompact] using!
   W.ratEmbed.tendsto_coe_cofinite_of_isDiscrete W.ratEmbed_injective
   ⟨W.discreteTopology_Gamma⟩) Set.rangeFactorization_surjective.le_map_cofinite)
open Complex Int _root_.Matrix Finset Function
variable {E : Type _} [Field E] [CMType E] {n : Type _} [Fintype n] (x : n → ℤ)
variable {E : Type _} [Field E] [NumberField E] in variable (E) in
noncomputable def twoAtInfinity : (𝔸 E)ˣ := .map ⟨⟨(fun _ ↦ ·, 1), rfl⟩, by aesop⟩ (.mk0 2 (by simp))
attribute [local simp low] diagonal_apply mulVec_apply Prod.fst_prod Prod.fst_sum Prod.snd_prod Prod.snd_sum Units.smul_def dotProduct mul_assoc twoAtInfinity zpow_nonneg
attribute [local simp ←] map_inv map_zpow
lemma sum_norm_sq_mulVec_of_isometry {m} [Fintype m] {Q : Matrix m n ℂ} (h : Qᴴ * Q = 1) v : ∑ i, ‖(Q *ᵥ v) i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
 simpa [← ofReal_inj, ← conj_mul', star_mulVec, h] using Q.dotProduct_mulVec (star (Q *ᵥ v)) v
lemma ideleAbs_det_mkAdelicGL a (b : GL n (𝔸f E)) : ideleAbs (mkAdelicGL (a, b)).det = (∏ w, ‖(a w).1.det‖ ^ 2) * finIdeleAbs b.det := by simp [finIdeleAbs, ideleAbs, det_apply]
noncomputable def dyadicDiag {E : Type _} [Field E] [NumberField E] {n : Type _} [Fintype n] (x : n → ℤ) := diagGL (twoAtInfinity E ^ x ·)
def profileBases (M : Set _) x y := {Y : GL n E | y⁻¹ * Y.map toAdele * (dyadicDiag x)⁻¹ ∈ M}
lemma isCompact_closedBall_prod_integral (r := 1) : @IsCompact (𝔸 E) _ (closedBall 0 r ×ˢ Ô E) := (isCompact_closedBall ..).prod isCompact_Ô
lemma ideleAbs_det_dyadicDiag : @ideleAbs E _ _ (dyadicDiag x).det = (2 ^ (2 * numInfPlaces E)) ^ ∑ i, x i := by simp [dyadicDiag, ideleAbs, ← zpow_sum_of_ne_zero]; group
lemma ideleAbs_det_dyadicDiag_natCast (x : n → ℕ) : @ideleAbs E _ _ (dyadicDiag (x ·)).det = ((2 ^ numInfPlaces E) ^ ∑ i, x i) ^ 2 := (ideleAbs_det_dyadicDiag _).trans (mod_cast by ring)
lemma dyadicDiag_inv_mem (x : n → ℕ) : (dyadicDiag (x ·))⁻¹.1 ∈ Set.matrix (closedBall 0 1 ×ˢ Ô E) := by simp [dyadicDiag, diagonal_mem_matrix_iff, Pi.pow_def]; bound
@[simp↓] lemma ideleAbs_det_map_toAdele (Y : GL n E) : ideleAbs (Y.map toAdele).det = 1 := Y.map_det toAdele ▸ ideleAbs_toAdele _
lemma minkowski_second (y : GL n _) : ∃ᵉ (Y) (x : n → ℤ), (det Y ≠ 0 ∧ ∀ j, let v := y⁻¹.1 *ᵥ toAdele ∘ Y j; (∀ i, (v i).2 ∈ Ô E) ∧ ‖WithLp.toLp 2 fun p : _ × _ ↦ (v p.2).1 p.1‖ ≤ 2 ^ x j) ∧ ideleAbs y.det * (2 ^ (2 * numInfPlaces E)) ^ ∑ i, x i ≤ (8 * (numInfPlaces E * card n) * NumberField.rootDiscr E) ^ (numInfPlaces E * card n) := by
 cases isEmpty_or_nonempty n; simp [univ_eq_empty, ideleAbs]; by_contra! H
 choose N o h using exists_forall_mul_mem_Ô (Prod.snd ∘ y.2.uncurry)
 obtain ⟨_, ⟨Y, x, hY, ⟨⟩⟩, hm⟩ :=
   @exists_least_of_bdd (∃ Y x, _ ∧ Finset.univ.sum x = ·) ⟨_, fun _ ⟨Y, x, h, e⟩ ↦
   e ▸ (le_zpow_iff_clog_le (by simp) (by simp [rootDiscr_pos, zero_lt_iff])).1 (@cast_pow .. ▸
   (div_le_iff₀' ideleAbs_pos).2 (H Y x h).le)⟩ ⟨_, Matrix.diagonal N, _, ⟨by simpa, fun j ↦
   ⟨by simpa [apply_ite, mul_comm] using! (h ⟨·, j⟩), self_le_zpow_clog _root_.one_lt_two _⟩⟩, rfl⟩
 let g := .map toAdele (.mk'' Yᵀ (by simp [*]))⁻¹ * y
 let A w := g.map (evalInf w); let B := g.map (.snd ..)
 choose b t u using fun w ↦
   exists_orthonormal_mul x ⟨_, (Units.mk0 (2 * √(numInfPlaces E * card n)) (by simp) • (A w)⁻¹).4⟩
 choose c hc _ using exists_ne_zero_inv_mulVec_mem (mkAdelicGL (b, B) * dyadicDiag x) (by
   contrapose! H; use Y, x, hY
   have e w := by simpa [field, (A _).det_ne_zero] using congr(‖$(u w).det‖).symm
   have : ideleAbs g.det = _ := ideleAbs_det_mkAdelicGL A B
   simp_all [g, ideleAbs_det_dyadicDiag, ideleAbs_det_mkAdelicGL]
   grw [H]; ring; norm_num [pow_mul', mul_comm])
 choose j hj hj' using c.support.exists_max_image x Subtype.finite (by simpa)
 refine (hm _ ⟨_, x - Pi.single j 1, ⟨(Y.det_updateRow_sum j c).trans_ne (by simp_all),
   (and_forall_ne j).1 ⟨?_, fun i k ↦ by simpa [k] using hY.2 i⟩⟩, rfl⟩).not_gt (by simp)
 simp [← mulVec_mulVec, dyadicDiag, -coe_units_inv, field, forall_and, pi_norm_lt_iff] at hc
 simpa [← vecMul_eq_sum, comp_def, RingHom.map_vecMul, mulVec_vecMul, zpow_sub₀, sum_prod_type, PiLp.norm_eq_of_L2, mul_pow, @mul_comm ℝ, field, ← mul_sum, -coe_units_inv, Real.sqrt_le_iff]
   using! (hc.symm.imp_right fun h ↦ sum_mono fun w ↦ (sum_norm_sq_mulVec_of_isometry (u w)
   ((b w).2 *ᵥ _)).trans_le (sum_le_card_nsmul _ _ ((2 ^ x j) ^ 2) fun l _ ↦ by
     gcongr; by_contra! k; have := by simpa using k.trans (h ..)
     simp +contextual [Finset.sum_eq_zero, or_iff_not_imp_right, not_lt.2, blockTriangular_inv_of_blockTriangular (t w) (this.trans_le' (hj' ..))] at k) :)
lemma tsum_prod_le_prod_tsum {α} (f : α → ℝ≥0∞) : ∑' x : n → α, ∏ i, f (x i) ≤ ∏ _ : n, tsum f := tsum_le_of_sum_le' bot_le fun s ↦ by grw [(by grind : s ⊆ piFinset (s.image ∘ eval)),
 ← prod_univ_sum, ENNReal.sum_le_tsum]
lemma encard_le_of_dyadic_box {α B} (hB : IsCompact B) : ∃ C ≠ ∞, ∀ (x : n → ℤ) {S} (f : α → n → E), Set.InjOn f S → (∀ a ∈ S, (fun i ↦ (twoAtInfinity E ^ (-x i)).1 * f a i) ∈ B) → S.encard ≤ C * .ofReal (((2 ^ numInfPlaces E) ^ ∑ i, (x i).toNat) ^ 2) := by
 choose _ hF _ a s using IsCovolOneLattice.exists_compact_cover (ratVectors E n)
 have hS := isCompact_univ_pi (fun _ ↦ isCompact_closedBall_prod_integral) |> fun p ↦
   (p.mul hB).add (p.mul hF)
 exists volume _, hS.measure_ne_top; introv u k
 grw [← ideleAbs_det_dyadicDiag_natCast, mul_comm, lintegral_encard_rat_points _ hS.measurableSet, ← iInf_le_lintegral]
 use le_iInf fun v ↦ mod_cast Set.encard_le_encard_of_injOn (fun ξ h ↦ ⟨_, ⟨(twoAtInfinity E ^
   (-x⁺ + x) · |>.1), ?_, _, k ξ h, rfl⟩, _, ⟨_, ?_, _, (a v).choose_spec ▸ s v, rfl⟩, by
   ext1; simp [dyadicDiag, -map_zpow, _root_.zpow_add]; ring!⟩)
   ((add_left_injective _).comp_injOn u) <;> simp [field, posPart]
end
open Matrix Topology
variable {E : Type*} [Field E] [NumberField E] [NumberField.IsCMField E] {n m : Type _} [Fintype n] [Fintype m] {s : n → _} {t : m → _}
attribute [local simp] blockGL U.sum Function.comp_def
lemma U.mem_range_sum {R} [CommRing R] [StarRing R] {J J' J''} (h : @fromBlocks n m n m R J 0 0 J' = J'') {g} : (IsUnit J' → ((∃ a, sum h (a, 1) = g) ↔ g.1.1.toCols₂ = fromRows 0 1)) ∧ (IsUnit J → ((∃ a, sum h (1, a) = g) ↔ g.1.1.toCols₁ = fromRows 1 0)) := by
 obtain ⟨e, k, u, ⟨⟩⟩ := g.1.1.fromBlocks_toBlocks, mem_U.1 g.2, g.1.isUnit, h
 rw [← e] at k u ⊢
 simp [← fromCols_fromRows_eq_fromBlocks, fromRows_ext_iff]
 constructor <;> rintro ⟨_, ⟨⟩⟩ <;> use (by aesop) <;> intro <;> simp_all [-e, Matrix.mul_left_eq_iff_eq_invOf_mul] <;> use u.unit <;> aesop
@[fun_prop] lemma G.isClosedEmbedding_sum : IsClosedEmbedding (sum : _ → G E (s ⊕ᵥ t)) := by
 simp [← isClosedEmbedding_mat.of_comp_iff]
 apply ((by tauto : (fromBlocks · 0 0 ·).uncurry.RightInverse fun M ↦ (M.onFun .inl, M.onFun .inr)
   ).isClosedEmbedding ..).comp (isClosedEmbedding_mat.prodMap isClosedEmbedding_mat) <;> fun_prop
@[fun_prop] lemma G.continuous_reindex e h : Continuous (reindex e h : G E s → G E t) := by
 simp [continuous_iff]; fun_prop
@[fun_prop] lemma G.continuous_neg : Continuous (neg : G E s → _) := continuous_iff.2 continuous_mat
namespace Space
variable {E : Type*} [Field E] [CMType E] (V : Space E n s) (W : Space E m t)
attribute [local simp] fromBlocks_mulVec sum vecAtPoint mat_ratEmbed mul_assoc RingHom.map_mulVec map_J
@[ext] lemma ext {V V' : Space E n s} (h : V.x = V'.x) : V = V' := by
 simp_all [mk.injEq _, ← (map_injective (@toAdele E ..).injective).eq_iff]
@[local simp] lemma mem_Γ_iff_range {g} : g ∈ V.Γ ↔ ∀ i j, (V.x * g.mat * V.x⁻¹) i j ∈ toAdele.range := ⟨.rec (by aesop), fun h ↦
 .imp (fun _ ↦ V.toRatCoords.symm_apply_eq.2 ∘ And.right)
 (U.mem_range_map _ (RingHom.injective _) (by simp) rfl (mem_ratMatrices.2 h).choose_spec)⟩
protected lemma witt {X Y : Matrix n m E} : HasLeftInv X → HasLeftInv Y → Xᴴ * V.J * X = Yᴴ * V.J * Y → ∃ g : U V.J, g.1.1 * X = Y := witt exists_isUnit_sub_star V.conjTranspose_J (by simp)
lemma ratEmbed_mulVec_vecAtPoint γ y : (V.ratEmbed γ).mat *ᵥ V.vecAtPoint y = V.vecAtPoint (γ *ᵥ y) := by simp
lemma stdForm_vecAtPoint y z : star (V.vecAtPoint y) ⬝ᵥ stdForm E s *ᵥ V.vecAtPoint z = star y ⬝ᵥ V.J *ᵥ z := by simp [star_mulVec_dotProduct]; simp [dotProduct]
lemma vecAtPoint_injective : (⇑V.vecAtPoint).Injective := (MulAction.injective V.x⁻¹).comp (@toAdele E ..).injective.comp_left
lemma sum_ratEmbed γ : (V.sum W).ratEmbed (U.sum rfl γ) = G.sum (V.ratEmbed γ.1, W.ratEmbed γ.2) := G.ext_mat (by erw [mat_ratEmbed]; simp)
lemma sum_vecAtPoint y z : (V.sum W).vecAtPoint (y ⊕ᵥ z) = V.vecAtPoint y ⊕ᵥ W.vecAtPoint z := by simp
lemma sum_mem_Γ {g} : G.sum g ∈ (V.sum W).Γ ↔ g.1 ∈ V.Γ ∧ g.2 ∈ W.Γ := by simp
lemma signedSpace_eq_reindex [StablyUnram E] {e h} (hV : V.x = (signedSpace E s).x) : signedSpace _ t = V.reindex e h := h ▸ by ext : 2; simp_all [signedSpace, reindex]
lemma mem_move_Γ a {g} : g ∈ (V.move a).Γ ↔ a * g * a⁻¹ ∈ V.Γ := by simp [move, G.mat]
