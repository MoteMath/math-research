import Lib.General.Analysis.OstrowskiTaussky
section
open PadicInt Filter Subgroup ZMod Nat Units
lemma exists_procyclic_generator {ℓ Γ} [Fact (Prime ℓ)] [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] [ContinuousMul Γ] (κ : Γ →* ℤ_[ℓ]ˣ) (hκ : Continuous κ) (h₂ : ∀ g, 4 ∣ (κ g).1 - 1) : ∃ γ, ∀ S ≥ κ.ker, S.IsOpen → γ ∈ S → ∀ g, g ∈ S := by
  obtain ⟨μ, C, c, E⟩ : ∃ μ, (∀ k, IsCyclic ((Units.map (toZModPow (k + 2)).1).comp μ).range) ∧
    Continuous μ ∧ μ.ker ≤ κ.ker := by
   obtain h | rfl := (em' _).imp (isCyclic_units_of_prime_pow ℓ Fact.out) id; use κ, inferInstance
   use κ ^ 2, fun k ↦ isCyclic_of_le (H' := zpowers (unitOfCoprime 5 (by bound))) (by
    simpa [LE.le] using fun _ ↦ sq_mem_of_index_two (Nat.mul_left_cancel card_pos ((card_mul_index
     _).trans (by norm_num [↓card_zpowers, ← orderOf_units, orderOf_five, ↓totient_prime_pow, pow_succ]))) _), hκ.pow 2, fun g h ↦ val_eq_one.1 (by
    grind [@pow_p_dvd_int_iff 2 _ 2 (-2), sq_eq_one_iff.1 congr($h.1)])
  choose γ _ h using (Set.exists_subtype_range_iff.1 <| C · |>.exists_monoid_generator)
  exact (isCompact_univ (by simp : atTop.map γ ≤ _)).imp fun δ d S s o a g ↦ comap_map_eq_self
   (E.trans s) ▸ (c.isClosedMap _ (S.isClosed_of_isOpen o)).mem_of_frequently_of_tendsto (.mono
   (d.2.frequently (o.mem_nhds a)) fun k ↦ (⟨_, pow_mem · _, rfl⟩))
   (isOpenEmbedding_val.tendsto_nhds_iff.2 (tendsto_sub_nhds_zero_iff.1 (squeeze_zero_norm (fun k ↦
   (norm_le_pow_iff_mem_span_pow _ (k + 2)).2 (by simpa [← ker_toZModPow] using! congr($(h k ⟨_, g,
   rfl⟩).1.1))) (by simp [↓← norm_p_pow, -norm_p, tendsto_add_atTop_iff_nat]))))
end
open NumberField Ideal Module Set Real Nat
lemma classNumber_le F [Field F] [NumberField F] : classNumber F ≤ (2 ^ finrank ℚ F * (discr F).natAbs) ^ (finrank ℚ F + 1) := by
  have {B} (n : Ioc 0 B) := (span {(n : 𝓞 F)}).absNorm_ne_zero_iff.1 (by aesop)
  grw [classNumber, ← card_eq_fintype_card, (card_le_card_of_surjective (fun x ↦ .mk0
   ⟨span {↑x.1, x.2.out}, by simp; grind⟩) fun C ↦ ?_).trans_eq (@card_sigma _ _ _ this), Finset.sum_le_sum fun n _ ↦ (absNorm_span_natCast n.1).trans_le (by grw [n.2.2])]
  simpa [RingOfIntegers.rank] using pow_succ'.ge; obtain ⟨I, rfl, hI⟩ := exists_ideal_in_class_of_norm_le C; have := absNorm_pos_of_nonZeroDivisors I
  cases IsDedekindDomain.exists_sup_span_eq I.1.span_singleton_absNorm_le (by aesop)
  use ⟨⟨_, this, ?_⟩, ‹𝓞 F›⟩; simp_all [← comap_map_quotientMk, span_insert]; rify; grw [hI, factorial_le_pow, ← two_le_pi, sqrt_le_self_iff.2 (mod_cast by grind)]; ring; bound [InfinitePlace.card_add_two_mul_card_eq_rank F]
