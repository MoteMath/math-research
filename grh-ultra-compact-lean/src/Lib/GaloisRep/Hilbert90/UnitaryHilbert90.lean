import Lib.GaloisRep.Hilbert90.TameDescent
open Polynomial AdjoinRoot Ideal Matrix U
attribute [-simp] smul_X
attribute [local simp ←] mk_C mk_X Algebra.smul_def
attribute [local simp] Finset.prod_range_succ Matrix.map_add Matrix.map_sub star Subtype.ext_iff add_assoc mul_assoc starRingEnd_apply sub_eq_iff_eq_add'
variable {O n : Type*} [CommRing O] [Fintype n] [StarRing O] {τ p} (hO : IsProfiniteRing O) {m c : O} (he : IsTameAtLevel τ p 0) (hc : τ c = c) (uc : IsUnit (c - star c)) (hτ : ∀ x, τ (star x) = star (τ x)) {Y : Matrix n n O}
include hO he hc uc hτ
lemma j9 (sM : star m = m) (t : τ m = m) {Q} (hQ : Y.charpoly = Q) (h : Q.map τ = Q) {k} (hk : k ≤ 1) (hr : Yᴴ * (1 + m • Y) ^ k = (-1) ^ k * Y) (hY : IsUnit (1 + m • Y)) : ∃ y z z', ∀ ⦃A : Type max u_1 u_2⦄ [Ring A] [StarRing A] [Algebra O A] [StarModule O A] ⦃B : A⦄, Q.aeval B = 0 → (y.map τ).aeval B = aeval B y ∧ let T := (1 + m • (X ^ (1 - k) * y)).aeval B
  (IsTameAtLevel τ p m → aeval B ((1 + m • z') * (1 + m • z)) = 1 ∧ aeval B (twistedNorm (.map τ) p (1 + m • z)) = T) ∧ (star B * (1 + m • B) ^ k = (-1) ^ k * B → T ^ (1 - k) * (1 + m • B) * star T = T ^ k) := by
  choose a w hw using hQ ▸ isUnit_aeval_iff_isCoprime (z := 1 + m • X).1 (by simpa)
  have K {A} [Ring A] [Algebra O A] {B C : A} (h : Q.aeval B = 0) (e : C * (1 + m • B) ^ k = (-1) ^ k * B) : (X * (-w) ^ k).aeval B = C := have := congr(C * aeval B $hw)
    by clear * - hk h e this; cases hk <;> simp_all [← mul_assoc, mul_comm w]
  have L g s h : ∃ θ : _ →+* _, ∀ q, θ (mk Q q) = mk Q ((q.map g).comp s) := ⟨quotientMap _ (s.compRingHom.comp (mapRingHom g)) (by simpa [mem_span_singleton]), by tauto⟩
  obtain ⟨⟨θ, h₁⟩, ρ, hρ⟩ := L τ X (by simp [*]), L _ _ (by simpa [hQ] using (Yᵀ.charpoly_map (starRingEnd O) ▸ K (hQ ▸ Y.aeval_self_charpoly) hr ▸ charpoly_dvd_charpoly_aeval_comp _ :))
  obtain ⟨θC, θX, hw⟩ := h₁ ∘' C, h₁ X, congr(mk Q $hw)
  simp [smul_eq_C_mul] at θC θX hw h₁
  obtain ⟨E, D⟩ : Commute θ ρ ∧ ρ ^ 2 = 1 := have := congr((ρ $hw, θ $hw))
    by clear * - hk h₁ hρ hw t sM hτ this
       cases hk <;> constructor <;> ext <;> simp_all [↓map_mul] <;> grind
  have hθ i : ∀ q, θ^[i] (mk Q q) = mk Q (q.map (τ ^ i)) := by
    induction i <;> simp [*, Polynomial.map_map, pow_succ, RingHom.mul_def, RingHom.one_def]
  let F := θ.eqLocus 1
  set r := ρ.restrict F F (congr($E ·).trans ∘ congrArg _) with R
  let N j : F := ⟨_, t ▸ θC m⟩ * ⟨_, θX⟩ ^ (1 - j)
  have T m (t : IsTameAtLevel τ p m) := t.of_map (of Q) (θC · |>.symm) (by ext <;> simp [*, t.2])
  have h := hO.j5 (powerBasisAux' (hQ ▸ Y.charpoly_monic)).equivFun.toAddEquiv
  have t₁ := @IsTameAtLevel.of_skew F _ r (N k) ⟨_, hc ▸ θC c⟩ (RingHom.ext (congr(⟨$D ·, _⟩)))
    (.of_map F.subtype _ (by simp [*, IsUnit.map, ← map_sub])) (by interval_cases k <;> simp [N, *])
  have H := h.eqLocus (by simpa using T 0 he)
  have u := IsUnit.of_map F.subtype (1 + N 0) (.of_mul_eq_one_right _ (by simpa [N]))
  obtain ⟨g, ⟨⟨⟨y⟩, hy⟩, d⟩, e⟩ : ∃ g : Fˣ, N k ∣ g - 1 ∧ g ^ (1 - k) * (1 + N 0) * r g = g ^ k := by
    interval_cases k
    · choose _ _ c e using t₁.exists_norm (.inr H) u (by simp [N, *]) (by simp)
      exact ⟨_, c, by simp [← e, ← map_mul]⟩
    simpa using t₁.j8 (.inr H) u (by simp [N]) (by simp [N, *]; grind)
  have d : g = mk Q (1 + m • (X ^ (1 - k) * y)) := by simpa [N, smul_eq_C_mul] using! d
  choose! z b c b' c' e' using fun t ↦ by simpa [dvd_def, mk_surjective.exists, ← map_mul, C_mul', ← exists_and_right] using ((T m t).exists_norm (.inr h) (g.isUnit.map F.subtype) g.1.2 (by simp [d, ← C_mul']))
  use y, b, b', fun A _ _ _ _ B hB ↦ let f : AdjoinRoot Q →ₐ[O] A := Quotient.liftₐ _ (aeval B) (by simp [mem_span_singleton', *])
    have hf q : f (mk Q q) = q.aeval B := rfl
    ⟨congr(f $((h₁ y).symm.trans hy)), fun t ↦ by simp [← hf, ← d ▸ e', twistedNorm_map_eq_prod, *, c t ▸ c' t ▸ z.inv_mul], fun _ ↦ by simpa [*, N, aeval_comp, ↓K hB ‹_›, ↓star_aeval] using congr(f $e)⟩
lemma exists_fixed_orthonormal_frame (u : IsUnit Y) (h₁ : Yᴴ = Y) (h₂ : Y.map τ = Y) : ∃ g W, g = 1 + W * (Y - 1) ∧ g.map τ = g ∧ gᴴ * Y * g = 1 := (j9 hO he hc uc hτ
  (by simp) τ.map_one rfl (by simp_all [← charpoly_map]) bot_le (by simpa)
 (by simpa)).elim fun y ⟨_, _, c⟩ ↦ have := c (Y - 1).aeval_self_charpoly
 ⟨_, (y.aeval (Y - 1))ᴴ, rfl, by simp_all [conjTranspose_map _ hτ, map_aeval_matrix]⟩
lemma uh_v2 (s : U 1) (sM : star m = m) (t : IsTameAtLevel τ p m) (hs : s.1.1 = 1 + m • Y) (hN : (twistedNorm (mapEnd hτ) p s).1.1 = 1) : ∃ g W, s * mapEnd hτ g = g ∧ g.1.1 = 1 + m • W := by
 choose k _ H _ using t.j7 (.inr hO) _ hs (by ext1; erw [← map_twistedNorm (U 1).subtype] <;> tauto)
 choose g _ _ a b using exists_fixed_orthonormal_frame hO he hc uc hτ (star k * k).isUnit (by simp)
  (by simpa [conjTranspose_map _ hτ, ← inv_val_eq_conjTranspose] using congr($Hᴴ * $H))
 use of isUnit_one (k * g) (by simpa using b)
 simp [Units.ext_iff, U.map, ← mul_assoc, H, a]; simp [*, mul_add, ← smul_add]
