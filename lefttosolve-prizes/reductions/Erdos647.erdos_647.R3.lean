import FormalConjectures.ErdosProblems.«647»

-- Reduction Erdos647.erdos_647.R3 of Erdős Problem 647
-- Credit: @DevinWatson
-- Sharpens R1 with a mod-30 residue-aware sixth-power divisor bound (up to 13.9x
-- smaller cutoff on shifts coprime to 30, 3.89x average reduction) together with
-- the lossless structural conditions 360360 | n, (16 | n or n % 64 = 56), and
-- primality of the six core cofactors (n - j) / j for j in {1, 2, 3, 4, 6, 12}.

namespace OMA.R_Erdos647_erdos_647_R3

open ArithmeticFunction.sigma

-- Residue-aware sixth-power divisor bound depending on divisibility by 2, 3, and 5.
-- Follows by maximizing (a + 1)^6 / p^a separately at each prime p < 64, omitting
-- primes p in {2, 3, 5} that do not divide m.
def H1 : Prop :=
  ∀ m : ℕ,
    (σ 0 m) ^ 6 ≤
      (if 2 ∣ m then
        (if 3 ∣ m then (if 5 ∣ m then 139 else 78)
         else (if 5 ∣ m then 58 else 33))
       else
        (if 3 ∣ m then (if 5 ∣ m then 39 else 22)
         else (if 5 ∣ m then 17 else 10))) ^ 6 * m

-- A witness n > 24 satisfying the mandatory divisibility, 2-adic, and six-prime
-- conditions need only satisfy the divisor bound on the residue-aware window.
def H2 : Prop :=
  ∃ n : ℕ,
    24 < n ∧
    360360 ∣ n ∧
    (16 ∣ n ∨ n % 64 = 56) ∧
    (∀ j ∈ ({1, 2, 3, 4, 6, 12} : Finset ℕ), ((n - j) / j).Prime) ∧
    ∀ k : ℕ, 0 < k → k ≤ n →
      (k + 3) ^ 6 ≤
        (if 2 ∣ k then
          (if 3 ∣ k then (if 5 ∣ k then 139 else 78)
           else (if 5 ∣ k then 58 else 33))
         else
          (if 3 ∣ k then (if 5 ∣ k then 39 else 22)
           else (if 5 ∣ k then 17 else 10))) ^ 6 * (n - k) →
      σ 0 (n - k) ≤ k + 2

lemma dvd_sub_iff_of_dvd {p n k : ℕ} (hpn : p ∣ n) (hkn : k ≤ n) :
    p ∣ n - k ↔ p ∣ k := by
  obtain ⟨a, rfl⟩ := hpn
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨a - b, ?_⟩
    have h2 : p * (a - b) = p * a - p * b := Nat.mul_sub_left_distrib p a b
    omega
  · rintro ⟨b, rfl⟩
    exact ⟨a - b, (Nat.mul_sub_left_distrib p a b).symm⟩

theorem main : H1 → H2 → type_of% @Erdos647.erdos_647 := by
  intro hbound hwindow
  obtain ⟨n, hn, hdiv, _, _, htest⟩ := hwindow
  have h2n : 2 ∣ n := dvd_trans (by decide : 2 ∣ 360360) hdiv
  have h3n : 3 ∣ n := dvd_trans (by decide : 3 ∣ 360360) hdiv
  have h5n : 5 ∣ n := dvd_trans (by decide : 5 ∣ 360360) hdiv
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  refine ⟨n, hn, ciSup_le ?_⟩
  intro m
  change (m : ℕ) + σ 0 (m : ℕ) ≤ n + 2
  have hm := m.isLt
  let k := n - (m : ℕ)
  have hk : 0 < k := Nat.sub_pos_of_lt hm
  have hkn : k ≤ n := Nat.sub_le _ _
  have hback : n - k = (m : ℕ) := by dsimp [k]; omega
  by_contra! hfail
  have hlarge : k + 3 ≤ σ 0 (m : ℕ) := by dsimp [k]; omega
  have hcutm := (Nat.pow_le_pow_left hlarge 6).trans (hbound (m : ℕ))
  rw [← hback] at hcutm
  simp only [dvd_sub_iff_of_dvd h2n hkn, dvd_sub_iff_of_dvd h3n hkn,
      dvd_sub_iff_of_dvd h5n hkn] at hcutm
  have hsmall := htest k hk hkn hcutm
  rw [hback] at hsmall
  omega

end OMA.R_Erdos647_erdos_647_R3
