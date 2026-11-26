import Lib.CM.Genus.QuadraticZeta
open Filter Finset IntermediateField Module Real AdjoinSimple
abbrev PrimePadicIso := Σ l : Nat.Primes, ℂ ≃+* PadicAlgCl l
def HeightLe c (y : _ → ℂ):=∃ᵉ (H) (α) (e : ℕ → ℝ),H≠0∧(∀ σ : ℂ ≃+* ℂ,‖σ H‖ ≤ α.exp)∧(∀ ι : PrimePadicIso,‖ι.2 (H * y ι)‖ ≤ (e ι.1).exp)∧∀ᶠ M in atTop, α + ∑ l∈range M with l.Prime,e l≤c
variable {c c' : ℝ} {y y' : PrimePadicIso → ℂ}
lemma HeightLe.mono (h : HeightLe c y) (hc : c≤c') (hy : ∀ ι :
  PrimePadicIso,‖ι.2 (y' ι)‖ ≤ ‖ι.2 (y ι)‖) : HeightLe c' y':=h.imp fun _↦by gcongr;aesop
lemma HeightLe.of_le {e : ℕ → ℝ} (he : ∀ T,(∀ l∈T,l.Prime)→∑ l∈T,e l≤c) (h : ∀ ι : PrimePadicIso,‖ι.2 (y ι)‖ ≤ exp (e ι.1)) : HeightLe c y:=⟨1,0,e,by aesop⟩
lemma HeightLe.mul : HeightLe c y→HeightLe c' y'→HeightLe (c + c') (y * y'):=fun ⟨H, α,e,a⟩ ⟨K, β,f,b⟩↦⟨H * K, α + β,e + f,by simp_all [exp_add,mul_le_mul,exp_nonneg,mul_mul_mul_comm H K];use a.2.2.2.choose + b.2.2.2.choose;grind⟩
lemma HeightLe.prod {ι s} {c y : ι → _} (h : ∀ i∈s,HeightLe (c i) (y i)) : HeightLe (∑ i∈s,
  c i) (∏ i∈s,y i):=by induction s using cons_induction <;> simp_all [mul, @of_le _ _ 0]
lemma HeightLe.pow (h : HeightLe c y) (n : ℕ) : HeightLe (n * c) (y ^ n):=by simpa using prod (s:=Iio n) fun _ _↦h
lemma HeightLe.nonneg (h : HeightLe c 1) : 0≤c:=by
  choose H _ _ d _ f _ g using by simpa [HeightLe] using h
  have := @NumberField.mk _ _ _ (adjoin.finiteDimensional (isAlgebraic_of_padic (by simpa using f ⟨default,·⟩)).isIntegral)
  have k {F c} [NormedField F] [CharZero F] [IsAlgClosed F] (e : _=_) (h : ∀ ι : _ ≃+* F,‖ι H‖ ≤ exp c):=show ‖algebraMap ℚ F (Algebra.norm ℚ (gen ℚ H))‖.log / finrank ℚ ℚ⟮H⟯ ≤ c by grw [Algebra.norm_eq_prod_embeddings,norm_prod,prod_le_prod₀ _ fun σ _↦(exists_ringEquiv_extend e ℚ⟮H⟯.val σ.1).choose_spec ⟨H,_⟩▸h _] <;> simp_all [finrank_pos.ne',prod_pos,Subtype.ext_iff]
  grw [← g _ le_self_add,← k rfl d,← sum_le_sum fun l h↦@Padic.eq_padicNorm l .. ▸ @PadicAlgCl.norm_extends .. ▸ k (@mk_complex_eq_mk_padicAlgCl ..) (f ⟨⟨l,(mem_filter.1 h).2⟩,·⟩)];simp [← sum_div,field]
  rw [(show ∀ {M} {q : ℚ},q.num.natAbs ⊔ q.den < M→log q + ∑ p∈range M with p.Prime,
    log (padicNorm p q)=0 from fun {M q} _↦have:=(congr(log $(Nat.prod_pow_prime_padicValNat
    · · M ·)));by by_cases q=0 <;> simp_all [log_prod,padicValRat,padicValInt,sub_mul,q.cast_def,log_div]) (Nat.le_add_left ..),zero_div]
