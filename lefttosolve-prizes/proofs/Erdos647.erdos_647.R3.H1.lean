import OMAReductions.R_Erdos647_erdos_647_R3

/-!
# Residue-aware sixth-power divisor bound for Erdos647.erdos_647.R3.H1

Maximizing (a + 1)^6 / p^a separately at each prime p < 64 while omitting
primes p in {2, 3, 5} that do not divide m gives sharp mod-30 sixth-power
divisor constants C in {10, 17, 22, 33, 39, 58, 78, 139}.
-/

open scoped BigOperators
open ArithmeticFunction.sigma

namespace OMA.Erdos647R3H1

private def peak (p : ℕ) : ℕ :=
  if p < 64 then
    match p with
    | 2 => 8
    | 3 => 4
    | 5 => 3
    | 7 | 11 => 2
    | _ => 1
  else 0

private def activePeak (b2 b3 b5 : Bool) (p : ℕ) : ℕ :=
  if (p = 2 ∧ b2 = false) ∨ (p = 3 ∧ b3 = false) ∨ (p = 5 ∧ b5 = false) then 0 else peak p

def coeff (b2 b3 b5 : Bool) : ℕ :=
  match b2, b3, b5 with
  | true,  true,  true  => 139
  | true,  true,  false => 78
  | true,  false, true  => 58
  | true,  false, false => 33
  | false, true,  true  => 39
  | false, true,  false => 22
  | false, false, true  => 17
  | false, false, false => 10

private def smallPrimes : Finset ℕ := (Finset.range 64).filter Nat.Prime

private theorem smallExponents :
    ∀ p : Fin 64, p.val.Prime → ∀ a : Fin 9,
      (a.val + 1) ^ 6 * p.val ^ peak p.val ≤
        (peak p.val + 1) ^ 6 * p.val ^ a.val := by
  decide

private theorem tailStep (a : ℕ) (ha : 8 ≤ a) :
    (a + 2) ^ 6 ≤ (a + 1) ^ 6 * 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ha
  ring_nf
  omega

private theorem localBound {p : ℕ} (hp : p.Prime) (a : ℕ) :
    (a + 1) ^ 6 * p ^ peak p ≤ (peak p + 1) ^ 6 * p ^ a := by
  by_cases hsmall : p < 64
  · induction a with
    | zero => exact smallExponents ⟨p, hsmall⟩ hp 0
    | succ a ih =>
      by_cases ha : a < 8
      · exact smallExponents ⟨p, hsmall⟩ hp ⟨a + 1, by omega⟩
      · calc
          (a + 2) ^ 6 * p ^ peak p
              ≤ ((a + 1) ^ 6 * 2) * p ^ peak p :=
                Nat.mul_le_mul_right _ (tailStep a (by omega))
          _ = ((a + 1) ^ 6 * p ^ peak p) * 2 := mul_right_comm _ _ _
          _ ≤ ((a + 1) ^ 6 * p ^ peak p) * p := Nat.mul_le_mul_left _ hp.two_le
          _ ≤ _ := by simpa only [pow_succ, mul_assoc] using Nat.mul_le_mul_right p ih
  · have hlarge : 2 ^ 6 ≤ p := by omega
    simp only [peak, if_neg hsmall, pow_zero, zero_add, one_pow, one_mul, mul_one]
    calc
      (a + 1) ^ 6 ≤ (2 ^ a) ^ 6 := Nat.pow_le_pow_left a.lt_two_pow_self 6
      _ = (2 ^ 6) ^ a := by rw [← pow_mul, Nat.mul_comm, pow_mul]
      _ ≤ p ^ a := Nat.pow_le_pow_left hlarge a

private theorem extendProduct {s t : Finset ℕ} (hst : s ⊆ t) {e : ℕ → ℕ}
    (he : ∀ p ∈ t, p ∉ s → e p = 0) (g : ℕ → ℕ → ℕ) (hg : ∀ p, g p 0 = 1) :
    (∏ p ∈ t, g p (e p)) = ∏ p ∈ s, g p (e p) :=
  (Finset.prod_subset hst (fun p hp hps => by rw [he p hp hps, hg])).symm

private theorem coeffCheck :
    ∀ b2 b3 b5 : Bool,
      (∏ p ∈ smallPrimes, (activePeak b2 b3 b5 p + 1)) ^ 6 ≤
        (coeff b2 b3 b5) ^ 6 * (∏ p ∈ smallPrimes, p ^ activePeak b2 b3 b5 p) := by
  decide

private theorem denPos (b2 b3 b5 : Bool) :
    0 < ∏ p ∈ smallPrimes, p ^ activePeak b2 b3 b5 p := by
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (Finset.mem_filter.mp hp).2.pos _

theorem residueBound (m : ℕ) :
    (σ 0 m) ^ 6 ≤ (coeff (decide (2 ∣ m)) (decide (3 ∣ m)) (decide (5 ∣ m))) ^ 6 * m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  let b2 := decide (2 ∣ m)
  let b3 := decide (3 ∣ m)
  let b5 := decide (5 ∣ m)
  let s := m.primeFactors ∪ smallPrimes
  have hs {p : ℕ} (hp : p ∈ s) : p.Prime := by
    rcases Finset.mem_union.mp hp with h | h
    · exact Nat.prime_of_mem_primeFactors h
    · exact (Finset.mem_filter.mp h).2
  have hfactor {p : ℕ} (_ : p ∈ s) (hp : p ∉ m.primeFactors) : m.factorization p = 0 :=
    Finsupp.notMem_support_iff.mp hp
  have hpeak {p : ℕ} (hp : p ∈ s) (hn : p ∉ smallPrimes) : activePeak b2 b3 b5 p = 0 := by
    have h64 : ¬ p < 64 := fun h => hn (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h, hs hp⟩)
    simp [activePeak, peak, h64]
  have hloc (p : ℕ) (hp : p ∈ s) :
      (m.factorization p + 1) ^ 6 * p ^ activePeak b2 b3 b5 p ≤
        (activePeak b2 b3 b5 p + 1) ^ 6 * p ^ m.factorization p := by
    by_cases hskip : (p = 2 ∧ b2 = false) ∨ (p = 3 ∧ b3 = false) ∨ (p = 5 ∧ b5 = false)
    · have hzero : m.factorization p = 0 := by
        rcases hskip with ⟨rfl, hb⟩ | ⟨rfl, hb⟩ | ⟨rfl, hb⟩
        · exact Nat.factorization_eq_zero_of_not_dvd (of_decide_eq_false hb)
        · exact Nat.factorization_eq_zero_of_not_dvd (of_decide_eq_false hb)
        · exact Nat.factorization_eq_zero_of_not_dvd (of_decide_eq_false hb)
      simp [activePeak, hskip, hzero]
    · simp only [activePeak, if_neg hskip]
      exact localBound (hs hp) (m.factorization p)
  have em := extendProduct (e := m.factorization) (t := s) Finset.subset_union_left
    (fun _ => hfactor)
  have ep := extendProduct (e := activePeak b2 b3 b5) (t := s) Finset.subset_union_right
    (fun _ => hpeak)
  have h := Finset.prod_le_prod' (s := s) hloc
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow] at h
  rw [em (fun _ a => a + 1) (fun _ => rfl), ep (· ^ ·) (fun _ => pow_zero _),
    ep (fun _ a => a + 1) (fun _ => rfl), em (· ^ ·) (fun _ => pow_zero _)] at h
  have hsharp :
      (σ 0 m) ^ 6 * (∏ p ∈ smallPrimes, p ^ activePeak b2 b3 b5 p) ≤
        (∏ p ∈ smallPrimes, (activePeak b2 b3 b5 p + 1)) ^ 6 * m := by
    simpa only [← Nat.card_divisors hm, ← ArithmeticFunction.sigma_zero_apply,
      ← Nat.prod_primeFactors_pow_factorization hm] using h
  apply le_of_mul_le_mul_right _ (denPos b2 b3 b5)
  exact hsharp.trans (by
    simpa only [mul_right_comm] using Nat.mul_le_mul_right m (coeffCheck b2 b3 b5))

end OMA.Erdos647R3H1

theorem OMA.solution : OMA.R_Erdos647_erdos_647_R3.H1 := by
  intro m
  have h := OMA.Erdos647R3H1.residueBound m
  by_cases h2 : 2 ∣ m <;> by_cases h3 : 3 ∣ m <;> by_cases h5 : 5 ∣ m <;>
    simpa [OMA.Erdos647R3H1.coeff, h2, h3, h5] using h
