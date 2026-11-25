import CarryDeterminants.Defs
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Mixed-Radix Arithmetic, Carry Bits, Kummer's Theorem, and Binary Carry Words

This module establishes the foundational pure-arithmetic identities for mixed-radix
expansions and ripple-carry addition:
- `place b r`: the `r`-th place value `∏_{j < r} b j`
- `mdigit b n r`: the `r`-th mixed-radix digit `(n / place b r) % b r`
- `carryIn b i j r` / `carryBit b i j r`: carry into and out of digit position `r`
- The exact digit-carry equation `d_r(i) + d_r(j) + c_in = d_r(i+j) + b_r * c_out`
- The generalized Legendre-Kummer digit-sum / carry identity
- Kummer's theorem connecting `padicValNat p ((i + j).choose i)` to `∑ carryBit`
- The binary carry-word identity `(i + j) ^^^ i ^^^ j = ∑ 2^(r+1) * carryBit`
-/

namespace NovelCarry

lemma place_zero (b : ℕ → ℕ) : place b 0 = 1 := rfl

lemma place_succ (b : ℕ → ℕ) (r : ℕ) : place b (r + 1) = place b r * b r := rfl

lemma place_const (B r : ℕ) : place (fun _ => B) r = B ^ r := by
  induction r with
  | zero => rfl
  | succ r ih => simp [place, ih, pow_succ]

lemma place_pos (b : ℕ → ℕ) (hb : ∀ r, 0 < b r) (r : ℕ) : 0 < place b r := by
  induction r with
  | zero => simp [place]
  | succ r ih => exact Nat.mul_pos ih (hb r)

lemma place_dvd_of_le (b : ℕ → ℕ) {r k : ℕ} (h : r ≤ k) : place b r ∣ place b k := by
  induction h with
  | refl => exact dvd_refl _
  | @step m _ ih => exact dvd_mul_of_dvd_left ih (b m)

lemma place_mono (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r) {r k : ℕ} (h : r ≤ k) :
    place b r ≤ place b k := by
  induction h with
  | refl => exact le_refl _
  | @step m _ ih =>
    calc place b r ≤ place b m := ih
      _ = place b m * 1 := (Nat.mul_one _).symm
      _ ≤ place b m * b m := Nat.mul_le_mul_left _ (hb m)

lemma mdigit_lt (b : ℕ → ℕ) (hb : ∀ r, 0 < b r) (n r : ℕ) : mdigit b n r < b r :=
  Nat.mod_lt _ (hb r)

lemma mdigit_zero (b : ℕ → ℕ) (r : ℕ) : mdigit b 0 r = 0 := by
  simp [mdigit]

lemma mdigit_of_lt_place (b : ℕ → ℕ) {n r : ℕ} (h : n < place b r) : mdigit b n r = 0 := by
  simp [mdigit, Nat.div_eq_of_lt h]

lemma carryIn_zero (b : ℕ → ℕ) (i j : ℕ) : carryIn b i j 0 = 0 := by
  simp [carryIn, place, Nat.mod_one]

lemma carryIn_le_one (b : ℕ → ℕ) (hb : ∀ r, 0 < b r) (i j r : ℕ) : carryIn b i j r ≤ 1 := by
  unfold carryIn
  have hP := place_pos b hb r
  have h1 : i % place b r < place b r := Nat.mod_lt _ hP
  have h2 : j % place b r < place b r := Nat.mod_lt _ hP
  have := Nat.div_lt_of_lt_mul (by linarith : i % place b r + j % place b r < place b r * 2)
  omega

lemma carryBit_le_one (b : ℕ → ℕ) (hb : ∀ r, 0 < b r) (i j r : ℕ) : carryBit b i j r ≤ 1 :=
  carryIn_le_one b hb i j (r + 1)

lemma carryBit_zero_left (b : ℕ → ℕ) (hb : ∀ r, 0 < b r) (j r : ℕ) : carryBit b 0 j r = 0 := by
  unfold carryBit carryIn
  simp only [Nat.zero_mod, zero_add]
  exact Nat.div_eq_of_lt (Nat.mod_lt _ (place_pos b hb (r + 1)))

lemma carryBit_zero_right (b : ℕ → ℕ) (hb : ∀ r, 0 < b r) (i r : ℕ) : carryBit b i 0 r = 0 := by
  unfold carryBit carryIn
  simp only [Nat.zero_mod, add_zero]
  exact Nat.div_eq_of_lt (Nat.mod_lt _ (place_pos b hb (r + 1)))

lemma carryBit_comm (b : ℕ → ℕ) (i j r : ℕ) : carryBit b i j r = carryBit b j i r := by
  simp [carryBit, carryIn, add_comm]

lemma div_add_eq (P i j : ℕ) (hP : 0 < P) :
    (i + j) / P = i / P + j / P + (i % P + j % P) / P := by
  have hi : i = P * (i / P) + i % P := (Nat.div_add_mod i P).symm
  have hj : j = P * (j / P) + j % P := (Nat.div_add_mod j P).symm
  have hsum : i + j = (i % P + j % P) + P * (i / P + j / P) := by
    calc i + j = (P * (i / P) + i % P) + (P * (j / P) + j % P) := by rw [← hi, ← hj]
      _ = (i % P + j % P) + P * (i / P + j / P) := by ring
  rw [hsum, Nat.add_mul_div_left _ _ hP]
  omega

lemma add_div_place (b : ℕ → ℕ) (hb : ∀ r, 0 < b r) (i j r : ℕ) :
    (i + j) / place b r = i / place b r + j / place b r + carryIn b i j r :=
  div_add_eq (place b r) i j (place_pos b hb r)

lemma carryBit_eq_sub (b : ℕ → ℕ) (hb : ∀ r, 0 < b r) (i j r : ℕ) :
    carryBit b i j r = (i + j) / place b (r + 1) - i / place b (r + 1) - j / place b (r + 1) := by
  have h := add_div_place b hb i j (r + 1)
  unfold carryBit
  omega

/-- Fundamental ripple-carry equation at digit position `r`. -/
lemma digit_carry_eq (b : ℕ → ℕ) (hb : ∀ r, 0 < b r) (i j r : ℕ) :
    mdigit b i r + mdigit b j r + carryIn b i j r =
      mdigit b (i + j) r + b r * carryBit b i j r := by
  have h1 : (i + j) / place b r = i / place b r + j / place b r + carryIn b i j r :=
    add_div_place b hb i j r
  have h2 : (i + j) / place b (r + 1) =
      i / place b (r + 1) + j / place b (r + 1) + carryBit b i j r :=
    add_div_place b hb i j (r + 1)
  have hdiv : ∀ n, n / place b (r + 1) = (n / place b r) / b r := fun n => by
    rw [place_succ, Nat.div_div_eq_div_mul]
  have hmod : ∀ n, n / place b r = b r * (n / place b (r + 1)) + mdigit b n r := fun n => by
    unfold mdigit
    rw [hdiv n]
    exact (Nat.div_add_mod (n / place b r) (b r)).symm
  rw [hmod (i + j), hmod i, hmod j, h2] at h1
  have hdist : b r * (i / place b (r + 1) + j / place b (r + 1) + carryBit b i j r) =
      b r * (i / place b (r + 1)) + b r * (j / place b (r + 1)) + b r * carryBit b i j r := by
    ring
  rw [hdist] at h1
  omega

/-- Mixed-radix expansion of `n % place b k`. -/
lemma mod_place_eq_sum (b : ℕ → ℕ) (k n : ℕ) :
    n % place b k = ∑ r ∈ Finset.range k, mdigit b n r * place b r := by
  induction k with
  | zero => simp [place, Nat.mod_one]
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih, place_succ, Nat.mod_mul, mdigit, mul_comm (place b k)]

/-- Mixed-radix expansion of `n < place b k`. -/
lemma eq_sum_mdigit (b : ℕ → ℕ) {k n : ℕ} (hn : n < place b k) :
    n = ∑ r ∈ Finset.range k, mdigit b n r * place b r := by
  calc n = n % place b k := (Nat.mod_eq_of_lt hn).symm
    _ = ∑ r ∈ Finset.range k, mdigit b n r * place b r := mod_place_eq_sum b k n

/-- Exact telescoping identity connecting mixed-radix digit sums and carry bits. -/
lemma digit_sum_add_carry_eq (b : ℕ → ℕ) (hb : ∀ r, 0 < b r) (k i j : ℕ)
    (hi : i < place b k) (hj : j < place b k) :
    mdigitSum b k i + mdigitSum b k j =
      mdigitSum b k (i + j) + (i + j) / place b k +
        ∑ r ∈ Finset.range k, (b r - 1) * carryBit b i j r := by
  have h0 : ∀ m,
      ∑ r ∈ Finset.range m, (mdigit b i r + mdigit b j r) + carryIn b i j 0 =
        ∑ r ∈ Finset.range m, mdigit b (i + j) r + carryIn b i j m +
          ∑ r ∈ Finset.range m, (b r - 1) * carryBit b i j r := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
      have hd := digit_carry_eq b hb i j m
      have hbm : 1 ≤ b m := hb m
      have hcb : b m * carryBit b i j m = (b m - 1) * carryBit b i j m + carryBit b i j m := by
        have := Nat.sub_add_cancel hbm
        calc b m * carryBit b i j m = (b m - 1 + 1) * carryBit b i j m := by rw [this]
          _ = (b m - 1) * carryBit b i j m + carryBit b i j m := by ring
      have hci : carryIn b i j (m + 1) = carryBit b i j m := rfl
      linarith
  have hk := h0 k
  rw [carryIn_zero, add_zero] at hk
  have hci_k : carryIn b i j k = (i + j) / place b k := by
    have h := add_div_place b hb i j k
    rw [Nat.div_eq_of_lt hi, Nat.div_eq_of_lt hj] at h
    omega
  rw [hci_k] at hk
  unfold mdigitSum
  rw [Finset.sum_add_distrib] at hk
  linarith

/-- Uniform base-`B` digit sum identity (for `i, j < B^k`). -/
lemma base_digitSum_carryCount (B k i j : ℕ) (hB : 2 ≤ B)
    (hi : i < B ^ k) (hj : j < B ^ k) :
    mdigitSum (fun _ => B) k i + mdigitSum (fun _ => B) k j =
      mdigitSum (fun _ => B) (k + 1) (i + j) + (B - 1) * carryCount (fun _ => B) k i j := by
  have hb : ∀ _r : ℕ, 0 < B := fun _ => by omega
  have h1 := digit_sum_add_carry_eq (fun _ => B) hb k i j
    (by rwa [place_const]) (by rwa [place_const])
  rw [place_const] at h1
  have hdiv : mdigit (fun _ => B) (i + j) k = (i + j) / B ^ k := by
    unfold mdigit
    rw [place_const]
    apply Nat.mod_eq_of_lt
    have hlt : i + j < B ^ k * B := by
      have : i + j < 2 * B ^ k := by omega
      have : 2 * B ^ k ≤ B * B ^ k := Nat.mul_le_mul_right _ hB
      linarith
    exact Nat.div_lt_of_lt_mul (by linarith)
  have hsum : mdigitSum (fun _ => B) (k + 1) (i + j) =
      mdigitSum (fun _ => B) k (i + j) + (i + j) / B ^ k := by
    unfold mdigitSum
    rw [Finset.sum_range_succ, hdiv]
  have hmul : ∑ r ∈ Finset.range k, (B - 1) * carryBit (fun _ => B) i j r =
      (B - 1) * carryCount (fun _ => B) k i j := by
    unfold carryCount
    rw [Finset.mul_sum]
  linarith

private lemma sum_Ico_one_succ (m : ℕ) (f : ℕ → ℕ) :
    ∑ r ∈ Finset.Ico 1 (m + 1), f r = ∑ r ∈ Finset.range m, f (r + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Ico_succ_top (by omega), Finset.sum_range_succ, ih]

/-- Kummer's Theorem: `v_p(C(i+j, i)) = carryCount (fun _ => p) k i j` for `i, j < p^k`. -/
theorem kummer_padicValNat_choose (p k i j : ℕ) [hp : Fact p.Prime]
    (hi : i < p ^ k) (hj : j < p ^ k) :
    padicValNat p ((i + j).choose i) = carryCount (fun _ => p) k i j := by
  have hp_gt1 : 1 < p := hp.out.one_lt
  have hb : ∀ _r : ℕ, 0 < p := fun _ => by omega
  have hchoose_mul : (i + j).choose i * (i.factorial * j.factorial) = (i + j).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right i j)
    rw [Nat.add_sub_cancel_left] at this
    linarith
  have hpos_c : (i + j).choose i ≠ 0 := Nat.ne_of_gt (Nat.choose_pos (Nat.le_add_right i j))
  have hpos_i : i.factorial ≠ 0 := Nat.factorial_ne_zero i
  have hpos_j : j.factorial ≠ 0 := Nat.factorial_ne_zero j
  have hval : padicValNat p ((i + j).choose i) + padicValNat p i.factorial + padicValNat p j.factorial =
      padicValNat p (i + j).factorial := by
    have h1 := padicValNat.mul (p := p) hpos_c (mul_ne_zero hpos_i hpos_j)
    have h2 := padicValNat.mul (p := p) hpos_i hpos_j
    rw [hchoose_mul] at h1
    omega
  have hlog_ij : Nat.log p (i + j) < k + 1 := by
    by_cases hij : i + j = 0
    · simp [hij]
    · exact Nat.log_lt_of_lt_pow hij (by
        have h1 : i + j < 2 * p ^ k := by omega
        have h2 : 2 * p ^ k ≤ p * p ^ k := Nat.mul_le_mul_right _ hp_gt1
        rw [pow_succ']
        linarith)
  have hlog_i : Nat.log p i < k + 1 := by
    by_cases hi0 : i = 0
    · simp [hi0]
    · exact Nat.log_lt_of_lt_pow hi0 (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by omega) (Nat.le_succ k)))
  have hlog_j : Nat.log p j < k + 1 := by
    by_cases hj0 : j = 0
    · simp [hj0]
    · exact Nat.log_lt_of_lt_pow hj0 (lt_of_lt_of_le hj (Nat.pow_le_pow_right (by omega) (Nat.le_succ k)))
  rw [padicValNat_factorial hlog_ij, padicValNat_factorial hlog_i, padicValNat_factorial hlog_j] at hval
  rw [sum_Ico_one_succ, sum_Ico_one_succ, sum_Ico_one_succ] at hval
  have hstep : ∀ r ∈ Finset.range k,
      (i + j) / p ^ (r + 1) = i / p ^ (r + 1) + j / p ^ (r + 1) + carryBit (fun _ => p) i j r := by
    intro r _
    have := add_div_place (fun _ => p) hb i j (r + 1)
    rw [place_const] at this
    exact this
  have hsum_eq : ∑ r ∈ Finset.range k, (i + j) / p ^ (r + 1) =
      ∑ r ∈ Finset.range k, i / p ^ (r + 1) +
      ∑ r ∈ Finset.range k, j / p ^ (r + 1) +
      carryCount (fun _ => p) k i j := by
    unfold carryCount
    calc ∑ r ∈ Finset.range k, (i + j) / p ^ (r + 1)
        = ∑ r ∈ Finset.range k, (i / p ^ (r + 1) + j / p ^ (r + 1) + carryBit (fun _ => p) i j r) :=
          Finset.sum_congr rfl hstep
      _ = ∑ r ∈ Finset.range k, i / p ^ (r + 1) +
          ∑ r ∈ Finset.range k, j / p ^ (r + 1) +
          ∑ r ∈ Finset.range k, carryBit (fun _ => p) i j r := by
          simp [Finset.sum_add_distrib]
  omega

private lemma geom_sum_two_succ (m : ℕ) : ∑ r ∈ Finset.range m, 2 ^ (r + 1) + 2 = 2 ^ (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, pow_succ 2 (m + 1)]
    omega

/-- Binary carry-word identity: `(i + j) ^^^ i ^^^ j = ∑_{r < k} 2^(r+1) * carryBit_2(i, j, r)`
    for all `i, j < 2^k`. -/
theorem binary_carry_word_eq (k i j : ℕ) (hi : i < 2 ^ k) (hj : j < 2 ^ k) :
    (i + j) ^^^ i ^^^ j = ∑ r ∈ Finset.range k, 2 ^ (r + 1) * carryBit (fun _ => 2) i j r := by
  have hb : ∀ _r : ℕ, 0 < 2 := fun _ => by omega
  apply Nat.eq_of_testBit_eq
  intro t
  have hsum_tb : ∀ m,
      (∑ r ∈ Finset.range m, 2 ^ (r + 1) * carryBit (fun _ => 2) i j r).testBit t =
        (if 1 ≤ t ∧ t ≤ m then carryBit (fun _ => 2) i j (t - 1) == 1 else false) := by
    intro m
    induction m with
    | zero =>
      simp
      omega
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have hlt : ∑ r ∈ Finset.range m, 2 ^ (r + 1) * carryBit (fun _ => 2) i j r < 2 ^ (m + 1) := by
        have hle : ∑ r ∈ Finset.range m, 2 ^ (r + 1) * carryBit (fun _ => 2) i j r ≤
            ∑ r ∈ Finset.range m, 2 ^ (r + 1) := by
          apply Finset.sum_le_sum
          intro r _
          have h1 := carryBit_le_one (fun _ => 2) hb i j r
          simpa using Nat.mul_le_mul_left (2 ^ (r + 1)) h1
        have hgeom := geom_sum_two_succ m
        omega
      rw [Nat.testBit_eq_decide_div_mod_eq]
      have hcb := carryBit_le_one (fun _ => 2) hb i j m
      by_cases htm : t = m + 1
      · subst htm
        have hdiv : (∑ r ∈ Finset.range m, 2 ^ (r + 1) * carryBit (fun _ => 2) i j r +
            2 ^ (m + 1) * carryBit (fun _ => 2) i j m) / 2 ^ (m + 1) =
            carryBit (fun _ => 2) i j m := by
          rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlt, zero_add]
        rw [hdiv]
        have hmod : carryBit (fun _ => 2) i j m % 2 = carryBit (fun _ => 2) i j m :=
          Nat.mod_eq_of_lt (by omega)
        rw [hmod]
        simp only [le_add_iff_nonneg_left, zero_le, le_refl, and_self, ↓reduceIte,
          Nat.add_sub_cancel]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcb with h | h <;> simp [h]
      · by_cases hlt_t : t < m + 1
        · have hpow : 2 ^ (m + 1) = 2 ^ t * (2 * 2 ^ (m - t)) := by
            rw [← pow_succ', ← pow_add]
            congr 1; omega
          have hdiv : (∑ r ∈ Finset.range m, 2 ^ (r + 1) * carryBit (fun _ => 2) i j r +
              2 ^ (m + 1) * carryBit (fun _ => 2) i j m) / 2 ^ t =
              (∑ r ∈ Finset.range m, 2 ^ (r + 1) * carryBit (fun _ => 2) i j r) / 2 ^ t +
              2 * (2 ^ (m - t) * carryBit (fun _ => 2) i j m) := by
            rw [hpow, show 2 ^ t * (2 * 2 ^ (m - t)) * carryBit (fun _ => 2) i j m =
              2 ^ t * (2 * (2 ^ (m - t) * carryBit (fun _ => 2) i j m)) by ring,
              Nat.add_mul_div_left _ _ (by positivity)]
          rw [hdiv, Nat.add_mul_mod_self_left, ← Nat.testBit_eq_decide_div_mod_eq, ih]
          have hiff : (1 ≤ t ∧ t ≤ m + 1) ↔ (1 ≤ t ∧ t ≤ m) := by omega
          simp [hiff]
        · have hsum_lt : ∑ r ∈ Finset.range m, 2 ^ (r + 1) * carryBit (fun _ => 2) i j r +
              2 ^ (m + 1) * carryBit (fun _ => 2) i j m < 2 ^ t := by
            have h1 : 2 ^ (m + 1) * carryBit (fun _ => 2) i j m ≤ 2 ^ (m + 1) := by
              simpa using Nat.mul_le_mul_left (2 ^ (m + 1)) hcb
            have h2 : 2 * 2 ^ (m + 1) ≤ 2 ^ t := by
              rw [← pow_succ']
              exact Nat.pow_le_pow_right (by omega) (by omega)
            omega
          rw [Nat.div_eq_of_lt hsum_lt]
          have hcond : ¬ (1 ≤ t ∧ t ≤ m + 1) := by omega
          simp [hcond]
  rw [hsum_tb k]
  rw [Nat.testBit_xor, Nat.testBit_xor]
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
      Nat.testBit_eq_decide_div_mod_eq]
  cases t with
  | zero =>
    simp only [pow_zero, Nat.div_one, nonpos_iff_eq_zero, one_ne_zero, false_and, ↓reduceIte]
    have h1 : i % 2 = 0 ∨ i % 2 = 1 := by omega
    have h2 : j % 2 = 0 ∨ j % 2 = 1 := by omega
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp [Nat.add_mod, h1, h2]
  | succ t =>
    have hadd := add_div_place (fun _ => 2) hb i j (t + 1)
    rw [place_const] at hadd
    have hcb_le := carryBit_le_one (fun _ => 2) hb i j t
    change (i + j) / 2 ^ (t + 1) = i / 2 ^ (t + 1) + j / 2 ^ (t + 1) +
      carryBit (fun _ => 2) i j t at hadd
    by_cases htk : t + 1 ≤ k
    · simp only [Nat.succ_le_succ_iff, zero_le, htk, and_self, ↓reduceIte, Nat.add_sub_cancel]
      rw [hadd]
      have ha : (i / 2 ^ (t + 1)) % 2 = 0 ∨ (i / 2 ^ (t + 1)) % 2 = 1 := by omega
      have hb' : (j / 2 ^ (t + 1)) % 2 = 0 ∨ (j / 2 ^ (t + 1)) % 2 = 1 := by omega
      rcases ha with ha | ha <;> rcases hb' with hb' | hb' <;>
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcb_le with hc | hc <;>
        simp [Nat.add_mod, ha, hb', hc]
    · have hi_lt : i < 2 ^ (t + 1) :=
        lt_of_lt_of_le hi (Nat.pow_le_pow_right (by omega) (by omega))
      have hj_lt : j < 2 ^ (t + 1) :=
        lt_of_lt_of_le hj (Nat.pow_le_pow_right (by omega) (by omega))
      have hij_lt : i + j < 2 ^ (t + 1) := by
        have h1 : i + j < 2 * 2 ^ k := by omega
        have h2 : 2 * 2 ^ k ≤ 2 ^ (t + 1) := by
          rw [← pow_succ']
          exact Nat.pow_le_pow_right (by omega) (by omega)
        omega
      simp [Nat.div_eq_of_lt hi_lt, Nat.div_eq_of_lt hj_lt, Nat.div_eq_of_lt hij_lt, htk]

end NovelCarry
