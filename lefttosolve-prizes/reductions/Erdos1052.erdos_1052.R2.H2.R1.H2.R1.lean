import OMAReductions.R_Erdos1052_erdos_1052_R2_H2_R1

-- Reduction Erdos1052.erdos_1052.R2.H2.R1.H2.R1
-- Unconditionally eliminates all single-prime-power cores c = q^k (k >= 2, c != 9)
-- where either:
--   (1) some odd prime square r^2 divides 1 + c (e.g. 7^2, 5^3, 11^3, 17^3, ...), or
--   (2) a 1-step prime-chain collision occurs: some odd prime r1 | 1 + c and odd prime r2 not
--       dividing c satisfy r2^2 | 1 + r1 or (r2 | 1 + c and r2 | 1 + r1)
--       (e.g. 13^2, 17^2, 23^2, ...).
-- Splits the surviving single-prime-power cores by parity of the exponent k (even vs odd).

namespace OMA.R_Erdos1052_erdos_1052_R2_H2_R1_H2_R1

-- Surviving single-prime-power cores c = q^k with EVEN exponent k >= 2 (c != 9),
-- no odd prime square dividing 1 + c, and no 1-step prime-chain collision outside c.
def H1 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    c.primeFactors.card = 1 → c ≠ 9 →
    (∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ^ 2 ∣ 1 + c) →
    (∀ r₁ r₂ : ℕ, r₁.Prime → r₁ ≠ 2 → r₁ ∣ 1 + c →
      r₂.Prime → r₂ ≠ 2 → ¬ r₂ ∣ c →
      ¬ r₂ ^ 2 ∣ 1 + r₁ ∧ ¬ (r₂ ∣ 1 + c ∧ r₂ ∣ 1 + r₁)) →
    (∀ p ∈ c.primeFactors, Even (c.factorization p)) →
    {a : ℕ | let b := 2 ^ a * c
             let u := ∏ q ∈ b.primeFactors, (1 + q ^ b.factorization q)
             5 ≤ a ∧ ∃ S : Finset ℕ, 4 ≤ S.card ∧ S ⊆ Finset.Icc 3 u ∧
               (∀ p ∈ S, p.Prime ∧ ¬ p ∣ b) ∧
               u * (∏ p ∈ S, (1 + p)) = (2 * b) * ∏ p ∈ S, p}.Finite

-- Surviving single-prime-power cores c = q^k with ODD exponent k >= 3,
-- no odd prime square dividing 1 + c, and no 1-step prime-chain collision outside c.
def H2 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    c.primeFactors.card = 1 → c ≠ 9 →
    (∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ^ 2 ∣ 1 + c) →
    (∀ r₁ r₂ : ℕ, r₁.Prime → r₁ ≠ 2 → r₁ ∣ 1 + c →
      r₂.Prime → r₂ ≠ 2 → ¬ r₂ ∣ c →
      ¬ r₂ ^ 2 ∣ 1 + r₁ ∧ ¬ (r₂ ∣ 1 + c ∧ r₂ ∣ 1 + r₁)) →
    (∀ p ∈ c.primeFactors, Odd (c.factorization p)) →
    {a : ℕ | let b := 2 ^ a * c
             let u := ∏ q ∈ b.primeFactors, (1 + q ^ b.factorization q)
             5 ≤ a ∧ ∃ S : Finset ℕ, 4 ≤ S.card ∧ S ⊆ Finset.Icc 3 u ∧
               (∀ p ∈ S, p.Prime ∧ ¬ p ∣ b) ∧
               u * (∏ p ∈ S, (1 + p)) = (2 * b) * ∏ p ∈ S, p}.Finite

namespace SingleCoreElim

-- A product of distinct primes is never divisible by the square of a prime.
theorem not_sq_dvd_prod_primes {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    {r : ℕ} (hr : r.Prime) : ¬ r ^ 2 ∣ ∏ p ∈ S, p := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    intro hd
    have hle := Nat.le_of_dvd (by decide) hd
    have hr2 : 2 ≤ r := hr.two_le
    nlinarith
  | @insert p s hp ih =>
    rw [Finset.prod_insert hp]
    intro hd
    have hpp : p.Prime := hS p (Finset.mem_insert_self p s)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    by_cases hrp : r = p
    · subst hrp
      have hd' : r * r ∣ r * ∏ q ∈ s, q := by simpa [sq] using hd
      have hdiv : r ∣ ∏ q ∈ s, q := (Nat.mul_dvd_mul_iff_left hr.pos).mp hd'
      obtain ⟨q, hqs, hrq⟩ := (hr.prime.dvd_finsetProd_iff (fun x : ℕ => x)).mp hdiv
      have heq : r = q := (((hs q hqs).dvd_iff_eq hr.ne_one).mp hrq).symm
      exact hp (heq ▸ hqs)
    · have hcop : (r ^ 2).Coprime p :=
        ((hr.coprime_iff_not_dvd.mpr fun h =>
          hrp ((hpp.dvd_iff_eq hr.ne_one).mp h).symm)).pow_left 2
      exact ih hs (hcop.dvd_of_dvd_mul_left hd)

-- A prime dividing a product of distinct primes must belong to the set.
theorem prime_mem_of_dvd_prod {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    {r : ℕ} (hr : r.Prime) (hd : r ∣ ∏ p ∈ S, p) : r ∈ S := by
  obtain ⟨q, hq, hrq⟩ := (hr.prime.dvd_finsetProd_iff (fun x : ℕ => x)).mp hd
  have heq : r = q := (((hS q hq).dvd_iff_eq hr.ne_one).mp hrq).symm
  exact heq ▸ hq

-- Decompose an odd single-prime-power core c as q^k with q odd prime, k >= 2.
theorem single_core_decomp {c : ℕ} (hc : Odd c)
    (hpow : ∀ p ∈ c.primeFactors, 2 ≤ c.factorization p)
    (hcard : c.primeFactors.card = 1) :
    ∃ q k : ℕ, q.Prime ∧ q ≠ 2 ∧ 2 ≤ k ∧ c = q ^ k ∧ c.primeFactors = {q} := by
  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hcard
  have hqmem : q ∈ c.primeFactors := hq ▸ Finset.mem_singleton_self q
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hqmem
  have hqdvd : q ∣ c := Nat.dvd_of_mem_primeFactors hqmem
  have hq2 : q ≠ 2 := by
    rintro rfl
    obtain ⟨m, hm⟩ := hc
    obtain ⟨t, ht⟩ := hqdvd
    omega
  have hk2 : 2 ≤ c.factorization q := hpow q hqmem
  have hceq : c = q ^ c.factorization q := by
    have hprod := Nat.factorization_prod_pow_eq_self hc.pos.ne'
    rw [Finsupp.prod, Nat.support_factorization, hq, Finset.prod_singleton] at hprod
    exact hprod.symm
  exact ⟨q, c.factorization q, hqp, hq2, hk2, hceq, hq⟩

-- For b = 2^a * q^k (a > 0, q odd prime, k > 0), sigma*(b) = (1 + 2^a) * (1 + q^k).
theorem sigma_star_two_pow_mul_prime_pow {a q k : ℕ} (ha : 0 < a) (hq : q.Prime)
    (hq2 : q ≠ 2) (hk : 0 < k) :
    ∏ p ∈ (2 ^ a * q ^ k).primeFactors, (1 + p ^ (2 ^ a * q ^ k).factorization p) =
      (1 + 2 ^ a) * (1 + q ^ k) := by
  have h2a : (2 : ℕ) ^ a ≠ 0 := (Nat.two_pow_pos a).ne'
  have hqk : q ^ k ≠ 0 := pow_ne_zero k hq.ne_zero
  have hpf : (2 ^ a * q ^ k).primeFactors = {2, q} := by
    rw [Nat.primeFactors_mul h2a hqk,
      Nat.primeFactors_prime_pow ha.ne' Nat.prime_two,
      Nat.primeFactors_prime_pow hk.ne' hq]
    rfl
  have hf2 : (2 ^ a * q ^ k).factorization 2 = a := by
    rw [Nat.factorization_mul h2a hqk, Finsupp.add_apply,
      Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
      hq.factorization_pow, Finsupp.single_eq_of_ne hq2.symm, add_zero]
  have hfq : (2 ^ a * q ^ k).factorization q = k := by
    rw [Nat.factorization_mul h2a hqk, Finsupp.add_apply,
      Nat.prime_two.factorization_pow, Finsupp.single_eq_of_ne hq2,
      hq.factorization_pow, Finsupp.single_eq_same, zero_add]
  rw [hpf, Finset.prod_pair hq2.symm, hf2, hfq]

-- Any odd prime dividing 1 + q^k cannot divide q^k.
theorem not_dvd_pow_of_dvd_one_add {r q k : ℕ} (hr : r.Prime) (hq : q.Prime)
    (hd : r ∣ 1 + q ^ k) : ¬ r ∣ q ^ k := by
  intro hqkd
  have h1 : r ∣ 1 := (Nat.dvd_add_left hqkd).mp hd
  exact hr.not_dvd_one h1

-- Coprimality of an odd prime r not dividing c with 2 * (2^a * c).
theorem coprime_two_mul_b {r a c : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrc : ¬ r ∣ c) :
    r.Coprime (2 * (2 ^ a * c)) := by
  have hc2 : r.Coprime 2 := hr.coprime_iff_not_dvd.mpr fun h =>
    hr2 ((Nat.prime_two.dvd_iff_eq hr.ne_one).mp h).symm
  have hcc : r.Coprime c := hr.coprime_iff_not_dvd.mpr hrc
  exact hc2.mul_right ((hc2.pow_right a).mul_right hcc)

-- Unconditional exclusion: if either admissibility clause fails, no a >= 5 has a completion S.
theorem empty_of_not_admissible {c : ℕ} (hc : Odd c)
    (hpow : ∀ p ∈ c.primeFactors, 2 ≤ c.factorization p)
    (hcard : c.primeFactors.card = 1)
    (hnadm : ¬ ((∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ^ 2 ∣ 1 + c) ∧
      (∀ r₁ r₂ : ℕ, r₁.Prime → r₁ ≠ 2 → r₁ ∣ 1 + c →
        r₂.Prime → r₂ ≠ 2 → ¬ r₂ ∣ c →
        ¬ r₂ ^ 2 ∣ 1 + r₁ ∧ ¬ (r₂ ∣ 1 + c ∧ r₂ ∣ 1 + r₁)))) :
    {a : ℕ | let b := 2 ^ a * c
             let u := ∏ q ∈ b.primeFactors, (1 + q ^ b.factorization q)
             5 ≤ a ∧ ∃ S : Finset ℕ, 4 ≤ S.card ∧ S ⊆ Finset.Icc 3 u ∧
               (∀ p ∈ S, p.Prime ∧ ¬ p ∣ b) ∧
               u * (∏ p ∈ S, (1 + p)) = (2 * b) * ∏ p ∈ S, p} = ∅ := by
  obtain ⟨q, k, hqp, hq2, hk2, hceq, _⟩ := single_core_decomp hc hpow hcard
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨ha5, S, _, _, hS, hbal⟩
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => (hS p hp).1
  have hu : ∏ p ∈ (2 ^ a * c).primeFactors, (1 + p ^ (2 ^ a * c).factorization p) =
      (1 + 2 ^ a) * (1 + c) := by
    rw [hceq]
    exact sigma_star_two_pow_mul_prime_pow (by omega) hqp hq2 (by omega)
  rw [hu] at hbal
  by_cases h1 : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ^ 2 ∣ 1 + c
  · have h2 : ¬ (∀ r₁ r₂ : ℕ, r₁.Prime → r₁ ≠ 2 → r₁ ∣ 1 + c →
        r₂.Prime → r₂ ≠ 2 → ¬ r₂ ∣ c →
        ¬ r₂ ^ 2 ∣ 1 + r₁ ∧ ¬ (r₂ ∣ 1 + c ∧ r₂ ∣ 1 + r₁)) := fun h2 => hnadm ⟨h1, h2⟩
    push_neg at h2
    obtain ⟨r₁, r₂, hr₁, hr₁2, hr₁d, hr₂, hr₂2, hr₂c, hcol⟩ := h2
    have hr₁c : ¬ r₁ ∣ c := by rw [hceq]; exact not_dvd_pow_of_dvd_one_add hr₁ hqp (hceq ▸ hr₁d)
    have hcop₁ : r₁.Coprime (2 * (2 ^ a * c)) := coprime_two_mul_b hr₁ hr₁2 hr₁c
    have hdiv₁ : r₁ ∣ (2 * (2 ^ a * c)) * ∏ p ∈ S, p := by
      rw [← hbal]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hr₁d _) _
    have hr₁S : r₁ ∈ S := prime_mem_of_dvd_prod hSp hr₁ (hcop₁.dvd_of_dvd_mul_left hdiv₁)
    have hprod_split : (1 + r₁) ∣ ∏ p ∈ S, (1 + p) := Finset.dvd_prod_of_mem (fun p => 1 + p) hr₁S
    have hboth : (1 + c) * (1 + r₁) ∣ (2 * (2 ^ a * c)) * ∏ p ∈ S, p := by
      rw [← hbal]
      rw [mul_assoc]
      exact dvd_mul_of_dvd_right (Nat.mul_dvd_mul_left (1 + c) hprod_split) (1 + 2 ^ a)
    have hr₂sq : r₂ ^ 2 ∣ (1 + c) * (1 + r₁) := by
      by_cases hsq : r₂ ^ 2 ∣ 1 + r₁
      · exact dvd_mul_of_dvd_right hsq (1 + c)
      · obtain ⟨hd1, hd2⟩ := hcol hsq
        rw [sq]
        exact Nat.mul_dvd_mul hd1 hd2
    have hcop₂ : (r₂ ^ 2).Coprime (2 * (2 ^ a * c)) := (coprime_two_mul_b hr₂ hr₂2 hr₂c).pow_left 2
    exact not_sq_dvd_prod_primes hSp hr₂ (hcop₂.dvd_of_dvd_mul_left (hr₂sq.trans hboth))
  · push_neg at h1
    obtain ⟨r, hr, hr2, hr2d⟩ := h1
    have hrd : r ∣ 1 + c := (dvd_pow_self r (by decide : 2 ≠ 0)).trans hr2d
    have hrc : ¬ r ∣ c := by rw [hceq]; exact not_dvd_pow_of_dvd_one_add hr hqp (hceq ▸ hrd)
    have hcop : (r ^ 2).Coprime (2 * (2 ^ a * c)) := (coprime_two_mul_b hr hr2 hrc).pow_left 2
    have hdiv : r ^ 2 ∣ (2 * (2 ^ a * c)) * ∏ p ∈ S, p := by
      rw [← hbal]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hr2d _) _
    exact not_sq_dvd_prod_primes hSp hr (hcop.dvd_of_dvd_mul_left hdiv)

end SingleCoreElim

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R2_H2_R1.H2 := by
  intro h1 h2 c hc hpow hcard hne9
  by_cases hadm : (∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ^ 2 ∣ 1 + c) ∧
      (∀ r₁ r₂ : ℕ, r₁.Prime → r₁ ≠ 2 → r₁ ∣ 1 + c →
        r₂.Prime → r₂ ≠ 2 → ¬ r₂ ∣ c →
        ¬ r₂ ^ 2 ∣ 1 + r₁ ∧ ¬ (r₂ ∣ 1 + c ∧ r₂ ∣ 1 + r₁))
  · obtain ⟨q, k, _, _, _, _, hqpf⟩ := SingleCoreElim.single_core_decomp hc hpow hcard
    rcases Nat.even_or_odd (c.factorization q) with hev | hodd
    · apply h1 c hc hpow hcard hne9 hadm.1 hadm.2
      intro p hp
      rw [hqpf, Finset.mem_singleton] at hp
      exact hp ▸ hev
    · apply h2 c hc hpow hcard hne9 hadm.1 hadm.2
      intro p hp
      rw [hqpf, Finset.mem_singleton] at hp
      exact hp ▸ hodd
  · rw [SingleCoreElim.empty_of_not_admissible hc hpow hcard hadm]
    exact Set.finite_empty

end OMA.R_Erdos1052_erdos_1052_R2_H2_R1_H2_R1
