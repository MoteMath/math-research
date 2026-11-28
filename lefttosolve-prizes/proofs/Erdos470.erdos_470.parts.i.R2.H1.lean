import OMAReductions.R_Erdos470_erdos_470_parts_i_R2

-- Proof of Erdos470.erdos_470.parts.i.R2.H1 (General Core-Gap Bridge theorem)
-- Credit: @DevinWatson
-- Ready to submit as proofs/Erdos470.erdos_470.parts.i.R2.H1.lean once R2 merges.

open Finset
open scoped BigOperators

private lemma sum_divisors_mul_of_coprime {m t : ℕ} (hcop : Nat.Coprime m t) :
    ∑ d ∈ (m * t).divisors, d = (∑ d ∈ m.divisors, d) * (∑ d ∈ t.divisors, d) := by
  have hmul : (m * t).divisors = (m.divisors ×ˢ t.divisors).image (fun p => p.1 * p.2) := by
    ext d
    simp only [Nat.mem_divisors, Finset.mem_image, Finset.mem_product, Prod.exists]
    constructor
    · rintro ⟨hd, hmt0⟩
      have hm0 : m ≠ 0 := left_ne_zero_of_mul hmt0
      have ht0 : t ≠ 0 := right_ne_zero_of_mul hmt0
      refine ⟨Nat.gcd d m, Nat.gcd d t, ⟨⟨Nat.gcd_dvd_right d m, hm0⟩, ⟨Nat.gcd_dvd_right d t, ht0⟩⟩, ?_⟩
      have hcop_g : Nat.Coprime (Nat.gcd d m) (Nat.gcd d t) :=
        (hcop.coprime_dvd_left (Nat.gcd_dvd_right d m)).coprime_dvd_right (Nat.gcd_dvd_right d t)
      have h1 : Nat.gcd d m * Nat.gcd d t ∣ d :=
        hcop_g.mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_left d m) (Nat.gcd_dvd_left d t)
      have hg_pos : 0 < Nat.gcd d m := Nat.gcd_pos_of_pos_right d (Nat.pos_of_ne_zero hm0)
      have hcop_div : Nat.Coprime (d / Nat.gcd d m) (m / Nat.gcd d m) :=
        Nat.coprime_div_gcd_div_gcd hg_pos
      have hdiv_dvd_mt : d / Nat.gcd d m ∣ (m / Nat.gcd d m) * t := by
        have hmul_eq : Nat.gcd d m * (d / Nat.gcd d m) ∣ Nat.gcd d m * ((m / Nat.gcd d m) * t) := by
          rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left d m), ← mul_assoc,
              Nat.mul_div_cancel' (Nat.gcd_dvd_right d m)]
          exact hd
        exact (mul_dvd_mul_iff_left (Nat.ne_of_gt hg_pos)).1 hmul_eq
      have hdiv_dvd_t : d / Nat.gcd d m ∣ t := hcop_div.dvd_of_dvd_mul_left hdiv_dvd_mt
      have hdiv_dvd_g : d / Nat.gcd d m ∣ Nat.gcd d t :=
        Nat.dvd_gcd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left d m)) hdiv_dvd_t
      have h2 : d ∣ Nat.gcd d m * Nat.gcd d t := by
        have hmul_g := mul_dvd_mul_left (Nat.gcd d m) hdiv_dvd_g
        rwa [Nat.mul_div_cancel' (Nat.gcd_dvd_left d m)] at hmul_g
      exact Nat.dvd_antisymm h1 h2
    · rintro ⟨a, b, ⟨⟨ha, hm0⟩, ⟨hb, ht0⟩⟩, rfl⟩
      exact ⟨mul_dvd_mul ha hb, mul_ne_zero hm0 ht0⟩
  rw [hmul, Finset.sum_image]
  · rw [Finset.sum_product, ← Finset.sum_mul_sum]
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_product, Nat.mem_divisors] at hx hy
    dsimp only at hxy
    have hcop_xy1 : Nat.Coprime x.1 y.2 :=
      (hcop.coprime_dvd_left hx.1.1).coprime_dvd_right hy.2.1
    have hcop_yx1 : Nat.Coprime y.1 x.2 :=
      (hcop.coprime_dvd_left hy.1.1).coprime_dvd_right hx.2.1
    have h1 : x.1 ∣ y.1 := hcop_xy1.dvd_of_dvd_mul_right (hxy ▸ dvd_mul_right x.1 x.2)
    have h2 : y.1 ∣ x.1 := hcop_yx1.dvd_of_dvd_mul_right (hxy.symm ▸ dvd_mul_right y.1 y.2)
    have hfst : x.1 = y.1 := Nat.dvd_antisymm h1 h2
    have hx1_pos : 0 < x.1 := Nat.pos_of_dvd_of_pos hx.1.1 (Nat.pos_of_ne_zero hx.1.2)
    have hsnd : x.2 = y.2 := Nat.eq_of_mul_eq_mul_left hx1_pos (hfst ▸ hxy)
    exact Prod.ext hfst hsnd

theorem OMA.solution : OMA.R_Erdos470_erdos_470_parts_i_R2.H1 := by
  intro m t E hm ht hcop hE hsig hp hgap
  have hm_pos : 0 < m := hm.pos
  have ht_pos : 0 < t := ht.pos
  have hmt_pos : 0 < m * t := Nat.mul_pos hm_pos ht_pos
  have hmt_ne : m * t ≠ 0 := Nat.ne_of_gt hmt_pos
  have hsig_mt : ∑ d ∈ (m * t).divisors, d = 2 * m * t + E := by
    rw [sum_divisors_mul_of_coprime hcop, hsig]
  have hprop_sum : ∑ d ∈ (m * t).properDivisors, d = m * t + E := by
    have hsplit : ∑ d ∈ (m * t).divisors, d = (∑ d ∈ (m * t).properDivisors, d) + m * t := by
      rw [← Nat.cons_self_properDivisors hmt_ne, Finset.sum_cons, add_comm]
    have h2mt : 2 * m * t = m * t + m * t := by ring
    omega
  refine ⟨⟨?_, ?_⟩, hm.mul ht⟩
  · unfold Nat.Abundant
    omega
  · rintro ⟨_, s, hs_sub, hs_sum⟩
    let c := (m * t).properDivisors \ s
    have hc_sum : ∑ d ∈ c, d = E := by
      have hadd := Finset.sum_sdiff hs_sub (f := fun d : ℕ => d)
      change (∑ d ∈ c, d) + (∑ d ∈ s, d) = ∑ d ∈ (m * t).properDivisors, d at hadd
      omega
    have hc_sub_m : c ⊆ m.divisors := by
      intro d hd
      have hd_prop : d ∈ (m * t).properDivisors := (Finset.mem_sdiff.1 hd).1
      have hd_dvd : d ∣ m * t := (Nat.mem_properDivisors.1 hd_prop).1
      have hd_le_E : d ≤ E := by
        rw [← hc_sum]
        exact Finset.single_le_sum (f := fun x : ℕ => x) (fun _ _ => Nat.zero_le _) hd
      have hd_dvd_m : d ∣ m := by
        by_contra hndvd
        have hgt : 1 < d / Nat.gcd d m := by
          have hg_dvd : Nat.gcd d m ∣ d := Nat.gcd_dvd_left d m
          have hg_pos : 0 < Nat.gcd d m := Nat.gcd_pos_of_pos_right d hm_pos
          have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd_dvd hmt_pos
          have hq_pos : 0 < d / Nat.gcd d m := Nat.div_pos (Nat.le_of_dvd hd_pos hg_dvd) hg_pos
          by_contra hle
          have hq1 : d / Nat.gcd d m = 1 := by omega
          have hdm : d = Nat.gcd d m := by
            have := Nat.div_mul_cancel hg_dvd
            rw [hq1, one_mul] at this
            exact this.symm
          exact hndvd (hdm ▸ Nat.gcd_dvd_right d m)
        obtain ⟨q, hq_prime, hq_dvd_q⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt hgt)
        have hq_dvd_d : q ∣ d := dvd_trans hq_dvd_q (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left d m))
        have hq_dvd_t : q ∣ t := by
          have hcop_q : Nat.Coprime (d / Nat.gcd d m) (m / Nat.gcd d m) :=
            Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right d hm_pos)
          have hdiv_dvd : d / Nat.gcd d m ∣ (m / Nat.gcd d m) * t := by
            have hg_pos : 0 < Nat.gcd d m := Nat.gcd_pos_of_pos_right d hm_pos
            have hmul_eq : Nat.gcd d m * (d / Nat.gcd d m) ∣ Nat.gcd d m * ((m / Nat.gcd d m) * t) := by
              rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left d m), ← mul_assoc,
                  Nat.mul_div_cancel' (Nat.gcd_dvd_right d m)]
              exact hd_dvd
            exact (mul_dvd_mul_iff_left (Nat.ne_of_gt hg_pos)).1 hmul_eq
          exact dvd_trans hq_dvd_q (hcop_q.dvd_of_dvd_mul_left hdiv_dvd)
        have hq_mem : q ∈ t.primeFactors := Nat.mem_primeFactors.2 ⟨hq_prime, hq_dvd_t, Nat.ne_of_gt ht_pos⟩
        have hE_lt_q : E < q := hp q hq_mem
        have hq_le_d : q ≤ d := Nat.le_of_dvd (Nat.pos_of_dvd_of_pos hd_dvd hmt_pos) hq_dvd_d
        omega
      exact Nat.mem_divisors.2 ⟨hd_dvd_m, Nat.ne_of_gt hm_pos⟩
    exact hgap c hc_sub_m hc_sum
