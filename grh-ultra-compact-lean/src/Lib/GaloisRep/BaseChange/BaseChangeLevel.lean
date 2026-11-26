import Lib.LocalGL.Iwahori.SortedExponents
import Lib.Adelic.CuspForms.FormRepresentation
import Lib.GaloisRep.BaseChange.BaseChangePlaces
section
variable {E n : Type} [Field E] [CMType E] [Fintype n] {V : Space E n 1} {κ : Weight E} {w : FinPlace E} (hw : _ ≠ w)
lemma exists_inf_trivialOn_le {H} (hH : H.IsOpen) : ∃ S : Finset _, (∀ w, maxCompactAt n w ≤ H → w ∉ S ∧ star w ∉ S) ∧ Kf E n ⊓ Gf.trivialOn n S ≤ H := (exists_minimal_of_wellFoundedLT _ ((isCompact_Kf.diff
 hH).elim_finite_subcover _ (isOpen_ne_fun continuous_one <| Gf.continuous_atPlace ·) fun g h ↦ by
  simpa using mt Gf.ext (H.one_mem.ne_of_notMem h.2))).imp fun S ⟨_, m⟩ ↦ by
 simp_all [Set.subset_def]
 use fun w _ ↦ (?_ ∘ @m (S \ {w, star w}) (Gf.exists_supportedOn_mul_trivialOn
  {w} · |>.rec ?_)) ?_ <;> grind [Gf.mem_trivialOn, Gf.mem_supportedOn, Gf.atPlace_star_eq_one_iff, star_star, Subgroup.mem_inf, mul_mem, IsConcreteLE.le_iff]
lemma hasHeckePolyAt_iff {f w} hw {P} : HasHeckePolyAt f.1 w hw P ↔ f ∈ sphericalAt (V.formTranslation κ) w ∧ ∃ t, P = heckePoly w.q (Fintype.card n) t ∧ ∀ j, heckeSplit (V.formTranslation κ) hw j f = t j • f := by
 simp [HasHeckePolyAt, Subtype.ext_iff]
 congr!; exact .symm (map_heckeSplit _ _ (V.forms κ).subtype)
noncomputable def s08_v8 (H : OpenSubgroup (Gf E n)) := H.comap
  (.mk' (fun g ↦ g * (atSplit hw (g.atPlace w))⁻¹) (by simp [(Gf.commute_supportedOn_trivialOn (atSplit_mem_supportedOn _ _) _).inv_left.eq, mul_assoc])) (by simp; fun_prop)
lemma le_span_isSphericalOff {S : Finset _} M (h : M ≤ levelSpace (V.formTranslation κ) (Kf .. ⊓ Gf.trivialOn n S)) [Module.Finite ℂ M] (T : ∀ w hw, w ∉ S → star w ∉ S → ∀ j, ∀ f ∈ M, heckeSplit (V.formTranslation κ) (w := w) hw j f ∈ M) : M ≤ .span ℂ {f ∈ M | ∃ P, IsSphericalOff S f.1 P} := ((V.exists_isUnitary_formTranslation κ).choose_spec.le_span_hecke_eigenvectors (by grind
 [star_star]) (fun w (o : w.IsSplit ∧ _) ↦ h.trans (And.elim levelSpace_le_sphericalAt o.2)) (by
 tauto)).trans (Submodule.span_le.2 fun _ ⟨m, c, _⟩ ↦ by_cases (by aesop) (Submodule.subset_span ⟨m, _, ·, by simpa [Subtype.ext_iff] using h m, fun w _ a b ↦ (hasHeckePolyAt_iff _).2
 ⟨levelSpace_le_sphericalAt a b (h m), dite _ (c ⟨⟨w, ·⟩, ·⟩) default, rfl, by aesop⟩⟩))
variable {E n : _} [Field E] [CMType E] [Fintype n] (V : Space E n 1) (κ : Weight E) {w : FinPlace E} (hw : _ ≠ w)
noncomputable abbrev embedAtSplit {E : _} {n : _} [Field E] [NumberField E] [NumberField.IsCMField E] [Fintype n] {w : FinPlace E} (hw : _ ≠ w) := (atSplit hw).comp (reindexGL (Fintype.equivFin n)).symm.toMonoidHom
noncomputable abbrev localFormRep := Rep.of ((V.formTranslation κ).comp (embedAtSplit hw))
open Set Fintype Submodule Module End Gf
attribute [local simp] atPlace_atSplit_of_ne mem_intGL
variable {V} {κ} {hw} {x : ↑(localFormRep V κ hw)}
instance : IsSmoothRep (localFormRep V κ hw).ρ := ⟨fun x ↦ .mono ((((continuous_atSplit hw).comp
 (.units_map _ (by simp; fun_prop))).1 _ x.2.1).mem_nhds (by simp)) fun _ ↦ Subtype.ext ∘ funext⟩
instance : Module.Finite ℂ ((cyclicSpan (localFormRep V κ hw).ρ x).submoduleOf (levelSpace (localFormRep V κ hw).ρ proIwahori)) := .of_fg (fg_of_fg_map _ (by simp) ((Finite.iff_fg.1 (V.finite_formTranslation_levelSpace κ (s08_v8 hw ⟨_, x.2.1⟩ ⊓ .comap _ (continuous_atPlace w) (.comap (reindexGL (equivFin n)).toMonoidHom (.units_map _ (by simp; fun_prop)) ⟨_, isOpen_proIwahori⟩)).2)).of_le (image_subset_iff.2 fun z h ⟨_, a, b⟩ ↦ (LinearMap.eqOn_span (eqOn_range.2 (by ext : 3; exact .trans (by simp [(commute_supportedOn_trivialOn (atSplit_mem_supportedOn _ _) _).right_comm, ← mul_assoc]) (a _))) h).trans (z.2 ⟨_, b⟩))))
lemma isUnitary_localFormRep : IsUnitary (localFormRep V κ hw).ρ (V.exists_isUnitary_formTranslation κ).choose := (V.exists_isUnitary_formTranslation κ).choose_spec.imp id (by tauto)
lemma IsEigenform.v9 {y P} (h : IsEigenform x.1 P) (hy : y ∈ cyclicSpan (localFormRep V κ hw).ρ x) (_ : y ≠ 0) : IsEigenform y.1 P := ⟨by simpa, h.2.mp (.mono ((toFinite {w}).star.insert w).compl_mem_cofinite fun _ _ ↦ (by
 peel ·; rw [hasHeckePolyAt_iff, mem_span] at *; use hy _ (by simp [-mem_supportedOn]; intros; rw [← mul_apply, ← map_mul, commute_supportedOn_trivialOn ‹_›] <;> aesop)
 peel this.2; simpa using hy (eigenspace ..) (by simp_all [← heckeSplit_comm_of_trivialOn])))⟩
lemma hasHeckePolyAt_iff_localFormRep {P} : HasHeckePolyAt x.1 w hw P ↔ x ∈ levelSpace (localFormRep V κ hw).ρ (Kw ..) ∧ ∃ t, P = heckePoly w.q (card n) t ∧ ∀ j, heckeGL (localFormRep V κ hw).ρ j x = t j • x := by
 rw [hasHeckePolyAt_iff, mem_sphericalAt_iff, and_congr_left', and_congr_right]
 congr! 5
 apply heckeFun_comp (reindexGL (equivFin n)).toMonoidHom _ ‹_›
 all_goals clear * -; simp_all [reindex_equiv (reindexGL (equivFin _)), indicator, basicDoubleCoset, Function.Surjective, reindex_equiv (equivFin n).symm, ↓isBiInvariant_basicDoubleCoset]
end
section
open Finset HasFiniteType DoubleCoset Gf LinearMap Set Subgroup
variable {E E' n W A} [Field E] [CMType E] [Field E'] [CMType E'] [Algebra E E'] [Fintype n] [AddCommGroup W] [Module ℂ W] {π : Representation ℂ (Gf E n) W} {S T : Set (FinPlace E)} (H : ∀ w ∈ T, w ∉ S ∧ star w ∉ S) [Group A] (a : A →* Gf E n) (r : Gf E n →* A)
def IsLocalRetraction S := (∀ g, a g ∈ supportedOn n S) ∧ (∀ g, r (a g) = g) ∧ r.ker = trivialOn n S
section
attribute [local simp] supportedOn localLevel SetLike.ext_iff placesAbove funext_iff heckeFun_sum s08_r8
lemma exists_commuting_hecke_family L {L₀ B C} (hK : L ≤ Kf ..) {J X} {F : J → _} (hF : ∀ j, IsBiInvariant L₀ (F j)) {u : X → _} (hu : ∀ x, (u x).IsSplit) (hX : ∀ x, u x ∉ S.conjClosure ∧ maxCompactAt n (u x) ≤ L) : let ρ := π.comp a
  let V := levelSpace ρ L₀; let D j := heckeFun ρ L₀ (F j); let W := levelSpace π (trivialOn n S ⊓ L)
      let T := Sum.elim D fun x ↦ heckeSplit π (hu (Prod.fst x)) x.2; IsLocalRetraction a r S → L = .comap r L₀ ⊓ (B ⊓ C) → (∀ g, a g ∈ B ⊓ C) → (∀ i j, EqOn (D i * D j) (D j * D i) V) → levelSpace π L = V ⊓ W ∧ (∀ g, (∀ v ∈ W, ρ g v ∈ W) ∧ ∀ x, Commute (T (.inr x)) (ρ g)) ∧ ∃ s : ∀ _, _, let A i := (T i).restrict (s i); (∀ i j, Commute (A i) (A j)) ∧ ∃ R : J → _ → _ → _, ∀ k, R k (A (.inl k)) (indicator B 1) ∧ ∀ {t φ}, R k t φ → IsOperatorOf π L t (F k ∘ r * (φ * indicator C 1)) ∧ (∀ {i j}, EqOn (D i * D k) (D j) V → R j (A (.inl i) * t) φ) ∧ ∀ x, supportedOn n {u x.1} ≤ C → R k (A (.inr x) * t) (heckeSplit s08_r8 (hu x.1) x.2 φ) := by
  rintro ρ V D W T ⟨p, q, o⟩ rfl hN c; simp at hN
  refine (fun E w ↦ ⟨E, w, Sum.rec (E ▸ fun j v h ↦ ⟨(hF j).heckeFun_mem h.1, by simp [T, D, hF, sum_mem, W.smul_mem, (w _).1 _ h.2]⟩) fun _ _ h ↦ heckeSplit_mem_levelSpace _ _ (levelSpace_anti (hX _).2 h) hK h, ?_⟩) ?_ fun g ↦ ⟨fun _ h ↦ map_mem_levelSpace_of_commute h (commute_supportedOn_trivialOn (p g) ·.2.1
    |>.symm.map _), fun x ↦ LinearMap.ext (by simp_all [T, ρ, heckeSplit_comm_of_trivialOn])⟩
  simp +contextual +zetaDelta [iff_def, ← o, q, hN]; intro _ _ h k _ _ _
  simpa [*, mul_mem, -map_inv] using h (k * a (r k)⁻¹)
  intro Z; refine ⟨?m, fun k t φ ↦ ∃ T, t = Z _ * T ∧ ∀ i, IsOperatorOf π _ (Z (.inl i) * T)
    (F i ∘ r * (φ * _)), fun k ↦ ⟨⟨1, rfl, fun i ↦ .t3 (hF i).1 ?_ ⟨1, rfl, by simp⟩⟩, @fun | _, _, ⟨T, rfl, h⟩ => ⟨h k, fun H ↦ ⟨T, by ext; exact H (E.le (by simp)).1, h⟩, fun x H ↦ ⟨_, (?m _ _).left_comm _, fun i ↦ (?m _ _).left_comm _ ▸ (h i).t3 (isBiInvariant_basicDoubleCoset _).1 (map_heckeSplit _ _ (mulLeft ℂ (F i ∘ r) * mulRight ..) fun g e ↦ by simp [r9, H e, r.mem_ker.1 (o ▸ supportedOn_compl.le (supportedOn_mono (by grind) e))])⟩⟩⟩⟩
  rintro ⟨⟩ ⟨⟩ <;> ext ⟨_, v⟩ <;> solve_by_elim [heckeSplit_comm, symm, (E.le v).1, map_heckeFun _
    (hF _).1 fun g ↦ congr($((w g).2 _) _), levelSpace_anti (hX _).2]
  choose _ _ using QuotientGroup.mk_out_eq_mul L₀
  simp [cosetFn, Finsupp.single_apply, QuotientGroup.eq, *, indicator, mul_mem_cancel_left, ite_and, ← @QuotientGroup.eq A]; lia
lemma isLocalRetraction_atSplit n [Fintype n] {w u} (h : ∀ v, .below E v = w ↔ v = u) hu hw : IsLocalRetraction (n := n) (atSplit hw) (atPlace w) {w} ∧ IsLocalRetraction (n := n) (atSplit hu) (atPlace u) (placesAbove E' {w}) ∧ localLevel n (placesAbove _ {w}) = .comap (atPlace u) (intGL n Valued.v.integer) := by simp_all [IsLocalRetraction, ← below_star, star_eq_iff_star_eq, atPlace_star_eq_one_iff, atPlace_atSplit_of_ne]; tauto
lemma Gf.supportedOn_le_trivialOn (H : ∀ w ∈ T, w ∉ S ∧ star w ∉ S) : supportedOn n S ≤ trivialOn n T := biInf_mono H
lemma exists_remaining_places (H : ∀ w ∈ T, w ∉ S ∧ star w ∉ S) {K} (h : ∀ x : T, ∀ u ∈ placesAbove _ {x.1}, K u = Kw ..) : ∃ Y, idem (placesAbove _ T) * idem (placesAbove E' Y) = 0 ∧ supportedOn n (placesAbove _ T) ≤ localLevel n (placesAbove _ Y) K ∧ placesAbove _ (T ∪ Y) = (placesAbove E' S)ᶜ ∧ idem (placesAbove _ T) + idem (placesAbove _ Y) = 1 - idem (placesAbove E' S) ∧ localLevel n (placesAbove _ S)ᶜ K = localLevel n (placesAbove _ T) ⊓ localLevel n (placesAbove E' Y) K := ⟨(S ∪ T).conjClosureᶜ, by
 simp_all [LE.le, Set.ext_iff, DFunLike.ext_iff, idem_apply, below_star]
 grind [star_star, one_mem]⟩
end
lemma Space.isSampleTotal_twisted_trace {E n} [Field E] [CMType E] [Fintype n] (V : Space E _ 1) κ {K L} (σ : _ ≃* _) (cσ : Continuous σ.symm) (hK : K ≤ Kf E n) (hL : L ≤ K) (oL : L.IsOpen) (hσ : L.comap σ = L) (τ : _ ≃* _) : let j := V.embFin; let ρ := V.weightRep _ κ.2; (∀ γ, j (τ γ) = σ (j γ)) → ∀ s, (∀ γ, s * ρ γ = ρ (τ γ) * s) → ∃ c ≠ 0, ∃ h h', ∀ {φ T}, IsOperatorOf (V.formTranslation κ) L T φ → IsSampleTotal (fun p q : _ × _ ↦ {g | q.1⁻¹ * j g * p.1 ∈ K ∧ g⁻¹ * q.2 * τ g = p.2}) (fun y ↦ φ (y.1⁻¹ * j y.2 * σ y.1) * (ρ y.2 * s).trace ℂ _)
      c ((T * ((s.compLeft _ ∘ₗ funLeft ℂ _ σ.symm).restrict h).restrict h').trace ℂ _) := by
  intro j ρ hτ s hs
  have := V.hasFiniteType_of_isLevel.of_le hK (isOpen_mono hL oL)
  refine ⟨_, Nat.cast_ne_zero.2 (this.4.relIndex_ne_zero oL), fun _ h ↦ ⟨(comap σ.symm.toMonoidHom
    _).isOpen_mono (by aesop_cat) (cσ.1 _ h.1), (reindex_equiv τ).1.2 (by simp_all [j, ρ, forms, SmoothForm, DFunLike.ext_iff])⟩, fun _ h k ↦ ?_, fun ⟨a, e, C⟩ ↦ e.substr ?_⟩
  ext; simpa [LinearMap.restrict] using congr(s ($(h ⟨σ.symm k, hσ.le (by simp)⟩).1 _) _)
  have := this.of_le hL oL
  choose S hS cS using exists_transporter V.Γf Fact.out .rfl
  have N {J} [HasFiniteType V.Γf J] h x := classSum_eq_relIndex_smul (L := L) (f := fun y ↦ (#(S J x
    y) : ℂ)) h 1 (by simp; rfl) fun y ↦ (by rw [cS, cS, out_eq', mul_one] : _ = (#(S J x y) : ℂ))
  simp_rw [classSum, finsum_eq_sum_of_fintype, Rat.smul_def] at N
  conv at N in _ * ∑ _, _ => simp [cS, out_eq', ↓card_classAut_out x, -mem_classAut, -MonoidHom.coe_range]
  have f x : (fun γ ↦ cosetFn L a (x⁻¹ * j γ * σ x) * (ρ γ * s).trace ℂ _).HasFiniteSupport := .mul_left ((cosetFn L a).hasFiniteSupport.preimage' fun q _ ↦ .ofFinset (S L (x * q.out) (σ x))
    (by simp [j, *, mul_assoc, ← QuotientGroup.eq, eq_comm])) _
  exact ⟨∑ i, ∑ γ ∈ _, .single (_, γ) _, (trace_eq_weighted_sum (·.out) _ (LinearMap.domRestrict
    (Submodule.subtype _) _) (le_antisymm (fun _ ⟨φ, e⟩ ↦ e ▸ ⟨⟨φ.1.2.2, by simp⟩, (congr($(φ.2
    ·).1))⟩) fun F h ↦ ⟨⟨⟨F, mem_smoothFunctions_of_eigen _ oL h.2, h.1.1⟩, (Subtype.ext <| h.2 ·)⟩, rfl⟩) σ _ (by simp [*, mul_assoc]) (D := ∅) ((ite_eq_left id).mpr <| N le_rfl · |>.trans (by simp))
    (fun _ ↦ by simpa [-map_mul, asAlgebraHom_eq_sum_support] using! congr($(C _).1)) hσ).2.trans
    (by simp [j, ρ, ← hτ, hs, (finsum_comp _ τ.bijective).trans (finsum_eq_sum _ (f _)), mul_sum, -MonoidHom.coe_range]; rfl), fun y h ↦ by simpa [*, mul_sum, ← ncard_coe_finset, ↓card_eq_sum_card_fiberwise fun g a ↦ (f _).mem_toFinset.2 (h (_, g⁻¹ * y.2 * τ g) g ⟨((hS ..).1 a).2, rfl⟩)] using! N hL y.1⟩
end
section
open Set Matrix RingHom Polynomial Gf Module
variable {E E' n W} [Field E] [CMType E] [Field E'] [CMType E'] [Algebra E E'] [Fintype n] {σ : Gal(E'/E)} [AddCommGroup W] [Module ℂ W] {π : Representation ℂ (Gf E' n) W} {u : FinPlace E'}
attribute [local simp] map_aeval_matrix map_smul' adeleMap_apply star_idem Matrix.map_add atPlace_baseChangeGf twistedNorm_map_eq_prod adeleMap_gal_pow r9 idem_apply Polynomial.map_prod cutGL Set.ext_iff below_star atPlace_atSplit_of_ne placesAbove mul_mem_cancel_left mul_mem_cancel_right s08_r8 funext_iff
attribute [-simp] evalAt_apply in
omit [CMType E'] in
lemma IsStep.isNormRoot_of_one_side {μ} (hμ : IsStep E' μ) {B T} (e : B = placesAbove E' T) (hD : ∀ w ∈ T, ∀ x, μ (locIdele w x) = 1) (s : ∀ w ∈ T, star w ∉ T) {p P z} [NeZero p] (hz : ∀ u, .below E u ∉ T → z.map (evalAt u) = 1) (N : ∀ u, .below E u ∈ T → P.map (evalAt u) ∣ (twistedNorm (.map (adeleMap σ)) p z).map (evalAt u) - X) : IsNormRoot n (adeleMap σ) p (idem B) (normKer _ μ) P z ∧ ∀ γ a : Gf E' n, IsRootQuotient γ (idem B • z) a → ∀ u, .below E u ∈ T → a.atPlace u = aeval (γ.atPlace u).1 (z.map (evalAt u)) := have I (u : FinPlace E') S := (evalAt_apply ..).trans (idem_apply S u)
 ⟨⟨by ext : 2; simp_all [← evalAt_apply, ← coeff_map]; grind, by
 rintro g rfl
 have N : (twistedNorm (.map (adeleMap σ)) p z).aeval g.1.1 = cutGL (idem_mul_self (.below E ⁻¹'
  T)) g.1 := matrix_ext_evalAt fun u ↦ if a : _ then (N u a).elim (by simp_all [sub_eq_iff_eq_add, aeval_self_charpoly, ← charpoly_map]) else by simp [*, (map_map (adeleMap _) (evalAt u) z).trans (map_map (evalAt _) (locMap _ rfl) _).symm]
 choose _ _ h using (twistedNorm_map_eq_prod p z ▸ isUnit_aeval_iff_isCoprime.1 ⟨_, N.symm⟩).of_prod_right 0 (by grind [NeZero])
 use fun k M _ ↦ (isUnit_det_of_left_inverse (by simpa [*, one_def] using congr(aeval M $h))).imp
  fun d c ↦ ⟨mem_of_locIdele_mem hμ.y5.1 fun u ↦ if a :
  u.below E ∈ T then by simp [adeleNorm_locIdele, *] else by simp [show ideleAt u d = 1 by ext; simp_all [ideleAt, map_det]], c⟩, matrix_ext_evalAt fun u ↦ by simp_all [← U.inv_val_eq_conjTranspose, Matrix.map_sub]; aesop⟩, fun _ _ a u _ ↦ by simpa [*, fun M ↦ (id rfl : Mᴴ.map (evalAt u) = (M.map (evalAt _))ᵀ.map (conjLoc (star_star u)))] using! congr(map $a (evalAt u))⟩
lemma heckeSplit_comp_baseChangeGf hu hw (s : (⇑(locMap _ (.refl (u.below E)))).Surjective) {j x} (hx : x ∈ sphericalAt π u) (h : ∀ k ∈ supportedOn n (.below E ⁻¹' {u.below E} \ {u}), π k x = x) : heckeSplit (π.comp baseChangeGf) (w := u.below E) hw j x = heckeSplit π (w := u) hu j x := heckeFun_comp _ (by simp)
 ((mem_sphericalAt_iff _).1 hx) (by simp) (GL_map_surjective _ s) (by apply y3) (fun _ ↦ by erw [← π.inv_apply_eq_iff, ← End.mul_apply, ← map_mul, h _ (mem_supportedOn.2 fun v _ _ ↦ ?_)]; by_cases star v = u <;> [rw [← atPlace_star_eq_one_iff]; by_cases v = u] <;> aesop)
 (by simp [basicDoubleCoset, indicator_apply, ← map_inv, -coe_units_inv, ← map_det, ← mapMatrix_apply, v_locMap_eq_of_isUnit_log _ rfl ((s (uniformizer u)).imp (by simp_all))])
attribute [local grind =] star_star below_star below_comap atPlace_star_mem_iff InjOn
lemma exists_hecke_stable_matching {μ} (hσ : σ ≠ 1) [hμ : IsStep E' μ] {S} (h : ∀ w ∈ S, w.IsSplit ∧ IsMatched E' μ w) : let B := localLevel n (placesAbove _ S); ∃ St : Set _, (indicator B 1 ∘ baseChangeGf (E' := E'), indicator B 1) ∈ St ∧ (∀ x ∈ St, IsMatchingPairAbove σ μ S B x.1 x.2) ∧ ∀ w : S, ∃ u, .below E u = w.1 ∧ ∀ x ∈ St, ∀ hw hu j, (heckeSplit
 s08_r8 (w := w) hw j x.1, heckeSplit s08_r8 (w := u) hu j x.2) ∈ St := by
 intro B
 obtain ⟨V, hV, -, b, c⟩ := exists_subset_bijOn (.below E ⁻¹' S) fun u : FinPlace E' ↦ s(u.below E, (star u).below E)
 let A := FinPlace.below E ⁻¹' .below E '' V \ V
 have s : placesAbove E' S = placesAbove _ (.below E '' V) := by simp [SurjOn] at c ⊢; grind [=_ below_star]
 have l {g} : g ∈ B ↔ g ∈ localLevel n V ∧ g ∈ localLevel n A := by grind [mem_localLevel, placesAbove, =_ atPlace_star_mem_iff]
 use {(F ∘ baseChangeGf, indicator (localLevel n A) 1 * F) | (F) (_ : ∀ k ∈ localLevel n V, s08_r8 k F = F ∧ ∀ g, F (g * k) = F g)}, ⟨indicator (localLevel n V) 1, by simp +contextual [indicator], by
  ext <;> simp [indicator, l, ite_and, mem_localLevel, A]; congr! with H; erw [ite_eq_left fun _ _ a e _ ↦ (y3 (w := .below E _) _).2 (e ▸ (y3 _).1 (H _ a))]⟩, ?_, fun ⟨w, m⟩ ↦ ?_
 rintro _ ⟨F, hF, rfl⟩; have ⟨β, η⟩ := bijective_pow_gal hσ
 have key {u : FinPlace E'} {g d : Gal(E'/E)} (a : u.comap g ∈ V) : u.comap d ∈ V ↔ d = g := (mul_left_surjective g d).rec fun d e ↦ e ▸ ⟨(mul_eq_left.2 <| (((h _ (hV a)).2.2 _ rfl).2
  _).mtr <| b · a (by grind)), by grind⟩
 have t i {u} : ∀ ⦃k⦄, atPlace (.comap ↑(σ ^ i) u) k ∈ Kw n _ → ((galoisGf σ)^[i] k).atPlace u ∈ Kw .. := i.rec (by tauto) fun _ a _ ↦ @a _ ∘ (y3 _).2
 use fun k hk ↦ ?_, fun P _ _ ↦ ⟨1 + idem V • (X - 1), (hμ.isNormRoot_of_one_side s (forall_mem_image.2 fun _
  a ↦ (h _ (hV a)).2.1) (by grind) (by simp; tauto) fun u ⟨v, a, e⟩ ↦ ?_).imp_right fun H γ a _ d
  ↦ ?_⟩; simp_all [indicator, (@l (galoisGf σ k)).1 fun u a ↦ t 1 (hk _ (by simpa))]
 obtain ⟨i, rfl⟩ := η.exists.1 (FinPlace.exists_gal_comap_eq e.symm)
 simp [Finset.prod_range, add_ite, key a, β.eq_iff]
 have ⟨_, a₂⟩ : a ∈ localLevel n A ∧ γ⁻¹ * a ∈ localLevel n V := .imp (trivialOn_le_localLevel ·) (trivialOn_le_localLevel ·) (by
  simp +contextual [↓mem_trivialOn, Units.ext_iff, H _ _ d, ↓mem_image_of_mem, A])
 rw [← Nat.succ_pred_prime hμ.out] at *; simp +contextual [← (hF _ a₂).2 γ, *]
 rintro δ _ rfl h _; simpa [twistedNorm, mul_div_assoc] using div_mem (inv_mem a₂) (list_prod_mem
  (List.forall_mem_map.2 fun i m u a ↦ t _ (h _ ⟨⟨u, by simpa⟩, β.ne
  (Fin.succ_ne_zero ⟨i, List.mem_range.1 m⟩) ∘ (@key u 1 _ a).1⟩)))
 obtain ⟨u, rfl, e⟩ : ∃ u, .below E u = w ∧ u ∈ V.conjClosure := by
  simp at s; grind [w.comap_surjective (algebraMap E E')]
 use u, rfl; rintro _ ⟨F, hF, rfl⟩ hw hu j
 have o a : atSplit hu a ∈ localLevel n A := trivialOn_le_localLevel (supportedOn_le_trivialOn (by grind) (atSplit_mem_supportedOn hu a))
 use heckeSplit s08_r8 hu j F, fun k hk ↦ ⟨(heckeSplit_comm_of_atPlace_mem hu j ?_ (by
  grind [mem_localLevel])).symm.trans (congrArg _ ?_), ?_⟩, Prod.ext (heckeSplit_comp_baseChangeGf
  hu hw (fun y ↦ ⟨_, congr(evalAt u $(finAdeleIncl_adeleNorm E _ (1 + singleAdele u
  (y - 1)))).trans (by erw [map_prod, Fintype.prod_eq_single 1, adeleMap_id] <;> simp +contextual
  [(h _ m).2.2])⟩) ?_ (fun k a ↦ (hF _ (trivialOn_le_localLevel (supportedOn_le_trivialOn (by grind) a))).1) ▸ map_heckeSplit _ _
  (LinearMap.funLeft ℂ ℂ baseChangeGf) ?_) ?_ <;> simp +contextual [heckeSplit, *, by simpa using hF, heckeGL, heckeFun_sum, ← mul_assoc, mem_localLevel, mem_Kf_iff, Finset.mul_sum]
open NumberField ComplexEmbedding ComplexConjugate Finset Fin Equiv Function
attribute [local implicit_reducible] stdSpace
variable {E E' n : _} [Field E] [Field E'] [Algebra E E'] [IsGalois E E'] [Fintype n] {σ : Gal(E'/E)}
noncomputable def Weight.baseChange (κ : Weight E) : Weight E' := ((κ.1 <| ·.comap (algebraMap ..)), (κ.2 <| ·.comap (algebraMap ..)))
lemma exists_twisted_weightRep_trace (hσ : σ ≠ 1) [hp : Fact (finrank E E').Prime] [CMType E] [c : CMOver E E'] (κ : Weight E) : let j := U.map (J := 1) (algebraMap E E') (map_star_CM _)
 let ω := U.mapEnd (map_star_CM σ)
 let ρ := (stdSpace _ n).weightRep κ.baseChange.1 κ.baseChange.2
 ∃ s, (∀ δ, s * ρ δ = ρ (ω δ) * s) ∧ ∀ δ γ, twistedNorm ω (finrank E E') δ = j γ → (s * ρ δ).trace ℂ _ = ((stdSpace ..).weightRep κ.1 κ.2 γ).trace ℂ _ := (Nat.exists_eq_add_one.2 hp.1.pos).elim (by
 intro k hE j ω ρ
 choose i hi using fun u ↦ (AlgEquiv.symm_bijective.comp (hE ▸ bijective_pow_gal hσ)).2.exists.1
  (exists_comp_symm_eq_of_comp_eq (lift _ ((Φ (u.comap (algebraMap E _))).comp conj)) ((Φ u).comp
  conj) (RingHom.ext (by simp [@starRingEnd_apply E, @starRingEnd_apply E', by
  simpa [RingHom.ext_iff] using c.2 (Φ u)])))
 let e := ofBijective _ ((Nat.bijective_iff_injective_and_card fun u ↦ (⟨i u, u.comap (algebraMap E
  _)⟩ : Σ _, _)).2 ⟨fun _ ↦ by grind [mk_Φ, cancel_right, surjective], by simp [mul_comm, *, (⟨by
  simp [InfinitePlace.IsUnramified]⟩ : IsUnramifiedAtInfinitePlaces E E').card_infinitePlace]⟩)
 let A : WeylIndex n κ.baseChange.1 ≃ (_ → WeylIndex ..) := .trans (.symm (e.symm.piCongrLeft' _)) (piCurry _)
 let G l := (weylRep κ.1 κ.2).comp (.pi fun v ↦ GeneralLinearGroup.map (n := n)
  ((lift _ ((Φ v).comp conj)).comp (σ ^ l).toRingHom))
 use (submatrix 1 (A.trans ((finRotate _).piCongrLeft' _)) A).toLin'
 simp_rw [fun δ ↦ ((LinearMap.ext (stdSpace_weightRep_apply δ)).trans (congrArg _ (Matrix.ext
  (by simp [reindex_equiv A.symm, ← hi, G, weylRep, @schur_apply_eq_prod (InfinitePlace _), prod_smul, ← Fintype.prod_sigma', reindex_equiv e]; tauto))) : ρ δ = (of fun a b ↦ ∏ l, G l.1 δ (A a l) (A b l)).toLin'), End.mul_eq_comp, ← toLin'_mul, mul_submatrix_one, one_submatrix_mul]
 use fun δ ↦ congrArg _ (Matrix.ext fun i _ ↦ .trans (.symm (Equiv.prod_comp (finRotate _) _)) (by
  simp [G, val_add, ← hE, ← IsGalois.card_aut_eq_finrank]; rfl)), fun δ γ h ↦ .symm ?_
 simp [trace, reindex_equiv A.symm, prod_univ_succ, ← cycleRange_last]
 trans (G 0 (j γ)).trace
 simp [LinearMap.ext (g := toLin' _) (stdSpace_weightRep_apply γ), G, j, U.map, weylRep, Units.smul_def, comp_def]
 simp [*, twistedNorm, ← h]
 refine k.rec ?_ ?_ δ (G 0 δ) <;> intros <;> simp [reindex_equiv (consEquiv _), ← mul_assoc, mul_apply, sum_mul, Fintype.sum_prod_type_right, prod_univ_succ, *, univ_eq_empty] <;> rfl)
end
section
open NumberField Matrix Set Valued Module Ideal Subtype
variable {E E' n : Type} [Field E] [CMType E] [Field E'] [NumberField E'] [CMType E'] [Algebra E E'] [Fintype n] {σ : Gal(E'/E)} (hσ : σ ≠ 1) {μ} [hμ : IsStep (E := E) E' μ] {f : E →+* E}
attribute [local simp] ite_mem y4 adeleMap_gal_pow Algebra.algebraMap_ofSubring idem_mul_self
variable (E' μ) in
def IsStepUnramifiedAt w := ∀ u : FinPlace E', u.below E = w → (∃ σ, σ ∉ u.1.inertia Gal(E'/E)) ∧ ∀ x, v x.1 = 1 → μ (locIdele _ (localNorm E u x)) = 1
noncomputable def intAdeleMap (f : E →+* E') := (adeleMap f).restrict _ _ fun _ ↦ (adeleMap_mem_Ohat f).2
@[simp] private lemma z6 i : ∀ x, (intAdeleMap f)^[i] x = (adeleMap f ^ i) x := by induction i <;> tauto
omit [CMType E] [NumberField E'] [CMType E'] in
lemma notMem_inertia_of_comap_ne {u : FinPlace E'} (h : u.comap σ ≠ u) : σ ∉ u.1.inertia _ := fun a ↦ h (by ext x; simpa using! u.1.add_mem_iff_right (b := x) (a x))
include hσ hμ
lemma exists_isTameAtLevel_intAdeleMap : ∃ C ≠ 0, ∀ m : Ô E', intAdeleMap σ m = m → (∀ u, C.cast ∈ u.1 → (∀ g, g ∈ u.1.inertia Gal(E'/E)) → reduceAt u m = 0) → IsTameAtLevel (intAdeleMap σ) (finrank E E') m := by
  obtain ⟨⟨e, _⟩, b, x, _⟩ := hμ.exists_trace_eq_one, bijective_pow_gal hσ, not_forall.1 (hσ ∘ IsGaloisGroup.faithful (𝓞 E) (B := 𝓞 E').1)
  refine ⟨(span {σ • x - x}).absNorm, by simpa, fun m a h ↦ ⟨a, ⟨algebraMap _ _ e, 0, val_injective (by simp [b.sum_comp (· e), *, Finset.sum_range, ← map_sum, ← trace_eq_sum_automorphisms, -AlgEquiv.coe_pow])⟩, by ext; simp [↓adeleMap_pow_finrank_eq_one], finrank_pos, fun i l P _ hP ↦ ?_⟩⟩
  have H : ∀ g, g ∈ (P.under (𝓞 E')).inertia _ := (bijective_pow_gal ((@b.1 ⟨i, l.2⟩ 0).mt (by
    grind))).2.forall.2 (pow_mem (fun _ ↦ by simp; convert hP _; simp [← coe_inj, algebraMap.smul'])
      ·)
  exact map_le_of_le_comap (fun _ ↦ algebraMap_ResField_eq_zero.1) ((map_under_Ô (by simpa) (I := RingHom.ker (reduceAt ⟨_, inferInstance, by simpa ∘ (·.le (H ..))⟩))
    (algebraMap_ResField_eq_zero.2
    (H ..))).ge (h _ ((span_singleton_le_iff_mem _).2 (H ..) (absNorm_mem _)) H))
lemma exists_baseChange_level {H} (hH : H.IsOpen) : ∃ K, (∀ u, K u ≤ Kw n u) ∧ (∀ S L, L = localLevel n (placesAbove _ S) K → L.IsOpen ∧ (∀ k, galoisGf σ k ∈ L ↔ k ∈ L) ∧ CocyclesSplit (finrank E E') (idem (placesAbove _ S)) L (galoisGf σ) ∧ IsMatchingPairAbove σ μ S L (indicator L 1 ∘ baseChangeGf (E' := E')) (indicator L 1)) ∧ (localLevel n univ
  K).comap baseChangeGf ≤ H ∧ ∀ w, IsStepUnramifiedAt E' μ w → maxCompactAt n w ≤ H → ∀ u ∈ placesAbove _ {w}, K u = Kw n u := by
  obtain ⟨⟨C, C₀, t⟩, S₀, hS, hS'⟩ := exists_isTameAtLevel_intAdeleMap hσ, exists_inf_trivialOn_le hH
  let A := placesAbove E' {w | IsStepUnramifiedAt E' μ w ∧ w ∉ conjClosure S₀}
  have un {u} (h : u ∈ A) := h.elim (·.1 u rfl) (·.1 _ (below_star u) |>.imp (by
    simpa using fun σ x b ↦ ⟨σ, _, by convert b; ext; apply map_star_CM σ.toRingHom⟩) fun b y _ ↦ by
    simpa [↓star_mul, ↓← units_map_adeleNorm_star, adeleNorm_locIdele, star_locIdele, *] using (hμ.apply_norm_eq_one_iff _).2 ⟨1, locIdele u y, rfl⟩)
  let F x := x + idem A * (1 - x)
  obtain ⟨N, N₀, U⟩ := mem_nhds_zero_finAdele_iff.1 (((isCompact_Ô.prod
    (isCompact_idelesUnitOff_empty.diff hμ.y5.2)).eventually_forall_mem (fun x p ↦ p.2.1 - F x * p.1) {1}ᶜ fun z ⟨_, a, b⟩ ↦ isOpen_ne.mem_nhds fun e ↦ b (mem_of_locIdele_mem hμ.y5.1 fun u ↦ congr(μ $(adeleNorm_locIdele
    ..)).trans (by_cases (un · |>.2 _ (mem_idelesUnitOff.1 a u id)) fun c ↦ by simp [(Units.ext (by
    simpa [F, c, ideleAt] using congr($e u)) : ideleAt u _ = 1)]))).and ((isCompact_Ô.matrix.prod
    (isCompact_Kf.diff hH)).eventually_forall_mem (fun x p ↦ p.2.1.1.map (finAdeleIncl _ E') - F x • p.1) {1}ᶜ fun z ⟨_, a, b⟩ ↦ isOpen_ne.mem_nhds fun e ↦ b (hS' ⟨a, Gf.mem_trivialOn.2 ((FinPlace.comap_surjective
    _).forall.2 fun u c ↦ Units.ext (ext fun i j ↦ RingHom.injective _ (congr($(eq_add_of_sub_eq e)
    i j u).trans (by simp +contextual [F, A, apply_ite, placesAbove, mod_cast c]))))⟩)))
  specialize U C (by simp); let m : Ô _ := N * C + ⟨_, idem_mem_Ô A⟩ * (1 - N * C)
  let k := F ((N * C)⁻¹ : E')
  have hk : m * k = 1 := by dsimp [m]; grind [idem_mul_self, map_natCast, congr(($(@mul_inv_cancel₀ E' _ (N * C) (by positivity)) : 𝔸f E'))]
  have hK {u g} : g ∈ congruenceGL ((v.leSubmodule 1).comap (.mulLeft _ (k u))) id ↔ g ∈ Kw n u ∧ ∀ i j, _ * _ ∈ LocInt u := .rfl
  refine ⟨_, fun _ _ ↦ (hK.1 · |>.1), fun S L hL ↦ ?_, fun g h ↦ by
    simp [localLevel, s08_z8, forall_and, *, -Matrix.sub_apply, ← mem_Kf_iff, baseChangeGf_mem_Kf] at h
    exact by_contra (U.2 (k • _, g) ⟨fun _ _ ↦ mem_Ô.2 (h.2 · ..), h.1, ·⟩
      (by erw [smul_smul, hk, one_smul, sub_sub_self]; rfl)), fun w b c u hu ↦ by
    ext; simp +contextual [↓hK, k, F, mem_intGL, sub_mem, show u ∈ A by grind [placesAbove]]⟩
  have hL' g : g ∈ L ↔ ∀ a b, idem (placesAbove _ S) * k * (g.1.1 - 1) a b ∈ Ô _ := by
    simp only [*, mem_localLevel, mul_assoc, idem_mul_mem_Ô, finAdele_mul_apply, ← s08_z8, forall_and, mem_intGL]; rw [and_iff_right_of_imp fun H ↦ ?_]; tauto
    have a := (mul_mem (mem_Ô.1 m.2 _) <| H · · · ·)
    simp [← mul_assoc, ← finAdele_mul_apply, hk, sub_eq_add_neg, add_mem_cancel_right] at a
    exact ⟨a, fun w h i j ↦ (v_locMap_le_one ..).1 (g.atPlace_star rfl ▸ a _ (by simpa) ..)⟩
  refine have a g := ?_; ⟨(ext hL').symm.subst isOpen_Ô.matrix.preimage_of_continuous, a, s08_y6 ⟨_, idem_mem_Ô _⟩ isProfiniteRing_intAdeles (t 0 ?_ ?_) ?_
      (((map_sub ..).trans (congrArg _ ?_)).subst (exists_isUnit_sub_star_Ohat.choose_spec.map
      (intAdeleMap (algebraMap E _)))) ?_ (t (_ * m) ?_ fun u c b ↦ by
    simp [m, by simpa using algebraMap_ResField_eq_zero.2 c, un.mt, b]) ?_
    ⟨(star_mul' ·.1)⟩ (Subring.isIntegrallyClosedIn_iff.2 fun _ h ↦ mem_Ô.2 fun u ↦ ((Valuation.integer.integers (v.comap (evalAt u))).mem_of_integral (h.map_of_comp_eq
    (Subring.inclusion (iInf_le ..)) 1 rfl) :)) _ rfl ?_ ?_ ((mul_mul_mul_comm ..).trans (by
    simp [*])) ?_ (hL' · |>.trans ⟨fun h ↦ ⟨(⟨_, h · ·⟩), rfl⟩, (congrFun₂ ·.choose_spec · ·
    |>.subst (prop _))⟩) fun y z _ ↦ by_contra (U.1 (_, _) ⟨y.2, by simp [coe_idelesUnitOff_empty, mul_mem, add_mem, Submonoid.mem_units_iff], ·⟩ (add_sub_cancel_right ..))⟩
  simp +zetaDelta [hL', ↓← adeleMap_mem_Ohat σ.toRingHom (x := _ * (g.1.1 - 1) _ _)]; rfl
  all_goals simp +zetaDelta [a, intAdeleMap, ← coe_inj, star_idem, preimage, adeleMap_star, mem_range_finAdeleIncl_iff.1, ← mul_assoc]
end
