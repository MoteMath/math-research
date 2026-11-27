/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions (`ModularCarryResidueDuality`)

Carry-Automaton Divisibility & Modular-Residue Dual Engine
Standalone Lean 4 proof (zero Mathlib, complete kernel-checked proofs, standard axioms only).

Architecture:
  Layer 1: Pure-silicon binary primitives (bitAt, popcount, v2, carriesAdd, sumNat, sumInt).
  Layer 2: Reusable Infinite Proof Mechanism — Bidirectional BitTransducer,
           CoboundaryCert (1-bit local certificate), and Dual Coupling Lifting Engine.
  Layer 3: General Odd-Modulus Dual Carry-Residue Automaton (MSB Euclidean remainder
           automaton coupled with LSB 2-adic division carry transducer), proving:
           - Master Dual Carry-Residue Conservation Law (∀ odd m, ∀ L, ∀ n < 2^L)
           - Synchronized-Trace Divisibility Equivalence
           - Exact Carry-Complementarity Law (κ_add + W = L - 1 - v2(r))
           - Universal 2-adic Reciprocal Popcount Law
  Layer 4: Infinite Mersenne Family m = 2^k - 1 (exact popcount-of-residue extraction,
           sharp divisibility threshold t ≥ 3, 2-adic inverse popcount law).
  Layer 5: Infinite Negacyclic Family m ∣ (2^d + 1) & Fermat Family m = 2^k + 1
           (residue-blind constant collapse 2 - t*d, exact exception set t*d = 2,
           residue-blind 2-adic inverse popcount law).
  Layer 6: Kernel-checked non-vacuity witnesses, infinite & concrete sharpness
           counterexamples, and `#print axioms` audit.
-/

namespace ModularCarryResidueDuality

/-! ## Layer 1: Pure-Silicon Binary Primitives -/

def boolNat (b : Bool) : Nat := if b then 1 else 0
def boolInt (b : Bool) : Int := if b then 1 else 0

def bitAt (n i : Nat) : Bool := ((n / 2 ^ i) % 2) == 1

theorem boolNat_bitAt (n i : Nat) : boolNat (bitAt n i) = (n / 2 ^ i) % 2 := by
  unfold boolNat bitAt
  have h : (n / 2 ^ i) % 2 = 0 ∨ (n / 2 ^ i) % 2 = 1 := by omega
  rcases h with h | h <;> simp [h]

theorem boolInt_eq_ofNat_boolNat (b : Bool) : boolInt b = (boolNat b : Int) := by
  cases b <;> rfl

theorem bitAt_zero (n : Nat) : bitAt n 0 = ((n % 2) == 1) := by
  simp [bitAt]

theorem bitAt_succ (n i : Nat) : bitAt n (i + 1) = bitAt (n / 2) i := by
  unfold bitAt
  rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]

theorem mod_mul_split (n a b : Nat) : n % (a * b) = n % a + (n / a % b) * a := by
  cases ha : a with
  | zero => simp
  | succ a' =>
    cases hb : b with
    | zero =>
      simp only [Nat.mul_zero, Nat.mod_zero]
      have := Nat.div_add_mod n (a' + 1)
      rw [Nat.mul_comm (n / (a' + 1)) (a' + 1)]
      omega
    | succ b' =>
      have ha_pos : 0 < a' + 1 := by omega
      have hb_pos : 0 < b' + 1 := by omega
      have hdiv : n = (a' + 1) * (n / (a' + 1)) + n % (a' + 1) := (Nat.div_add_mod n (a' + 1)).symm
      have hdiv2 : n / (a' + 1) = (b' + 1) * (n / (a' + 1) / (b' + 1)) + n / (a' + 1) % (b' + 1) :=
        (Nat.div_add_mod (n / (a' + 1)) (b' + 1)).symm
      have h1 : n = (a' + 1) * (b' + 1) * (n / (a' + 1) / (b' + 1)) +
          (n % (a' + 1) + (n / (a' + 1) % (b' + 1)) * (a' + 1)) := by
        conv => lhs; rw [hdiv, hdiv2]
        rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm (a' + 1) (n / (a' + 1) % (b' + 1))]
        omega
      have hlt : n % (a' + 1) + (n / (a' + 1) % (b' + 1)) * (a' + 1) < (a' + 1) * (b' + 1) := by
        have hlt1 : n % (a' + 1) < a' + 1 := Nat.mod_lt n ha_pos
        have hlt2 : n / (a' + 1) % (b' + 1) + 1 ≤ b' + 1 := Nat.mod_lt _ hb_pos
        have hmul : (n / (a' + 1) % (b' + 1) + 1) * (a' + 1) ≤ (b' + 1) * (a' + 1) :=
          Nat.mul_le_mul_right (a' + 1) hlt2
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (b' + 1)] at hmul
        omega
      conv => lhs; rw [h1]
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

theorem mod_pow2_succ (n i : Nat) :
    n % 2 ^ (i + 1) = n % 2 ^ i + (n / 2 ^ i % 2) * 2 ^ i := by
  rw [Nat.pow_succ, mod_mul_split]

theorem mod_two_mul_pow2 (n k : Nat) :
    n % (2 * 2 ^ k) = n % 2 + 2 * (n / 2 % 2 ^ k) := by
  rw [mod_mul_split, Nat.mul_comm (n / 2 % 2 ^ k) 2]

def sumNat : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | L + 1, f => sumNat L f + f L

def sumInt : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | L + 1, f => sumInt L f + f L

theorem sumNat_congr {L : Nat} {f g : Nat → Nat} (h : ∀ i, i < L → f i = g i) :
    sumNat L f = sumNat L g := by
  induction L with
  | zero => rfl
  | succ L ih =>
    simp only [sumNat]
    rw [ih (fun i hi => h i (by omega)), h L (by omega)]

theorem sumInt_congr {L : Nat} {f g : Nat → Int} (h : ∀ i, i < L → f i = g i) :
    sumInt L f = sumInt L g := by
  induction L with
  | zero => rfl
  | succ L ih =>
    simp only [sumInt]
    rw [ih (fun i hi => h i (by omega)), h L (by omega)]

theorem sumNat_shift (L : Nat) (f : Nat → Nat) :
    sumNat (L + 1) f = f 0 + sumNat L (fun i => f (i + 1)) := by
  induction L with
  | zero => simp [sumNat]
  | succ L ih =>
    simp only [sumNat] at ih ⊢
    omega

theorem sumInt_shift (L : Nat) (f : Nat → Int) :
    sumInt (L + 1) f = f 0 + sumInt L (fun i => f (i + 1)) := by
  induction L with
  | zero => simp [sumInt]
  | succ L ih =>
    simp only [sumInt] at ih ⊢
    omega

theorem sumInt_add (L : Nat) (f g : Nat → Int) :
    sumInt L (fun i => f i + g i) = sumInt L f + sumInt L g := by
  induction L with
  | zero => rfl
  | succ L ih =>
    simp only [sumInt, ih]
    omega

theorem sumInt_sub (L : Nat) (f g : Nat → Int) :
    sumInt L (fun i => f i - g i) = sumInt L f - sumInt L g := by
  induction L with
  | zero => rfl
  | succ L ih =>
    simp only [sumInt, ih]
    omega

theorem sumInt_const_mul (L : Nat) (c : Int) (f : Nat → Int) :
    sumInt L (fun i => c * f i) = c * sumInt L f := by
  induction L with
  | zero => simp [sumInt]
  | succ L ih =>
    simp only [sumInt, ih, Int.mul_add]

theorem sumInt_ofNat (L : Nat) (f : Nat → Nat) :
    sumInt L (fun i => (f i : Int)) = (sumNat L f : Int) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    simp only [sumInt, sumNat, ih, Int.natCast_add]

theorem sumNat_add (L : Nat) (f g : Nat → Nat) :
    sumNat L (fun i => f i + g i) = sumNat L f + sumNat L g := by
  induction L with
  | zero => rfl
  | succ L ih =>
    simp only [sumNat, ih]
    omega

theorem sumNat_const (L c : Nat) : sumNat L (fun _ => c) = L * c := by
  induction L with
  | zero => simp [sumNat]
  | succ L ih =>
    simp only [sumNat, ih, Nat.succ_mul]

theorem sumNat_mul_left (L c : Nat) (f : Nat → Nat) :
    sumNat L (fun i => c * f i) = c * sumNat L f := by
  induction L with
  | zero => simp [sumNat]
  | succ L ih =>
    simp only [sumNat, ih, Nat.mul_add]

theorem sumNat_split (a b : Nat) (f : Nat → Nat) :
    sumNat (a + b) f = sumNat a f + sumNat b (fun i => f (a + i)) := by
  induction b with
  | zero => simp [sumNat]
  | succ b ih =>
    rw [← Nat.add_assoc, sumNat, ih, sumNat]
    omega

theorem sumNat_eq_zero_iff {L : Nat} {f : Nat → Nat} :
    sumNat L f = 0 ↔ ∀ i, i < L → f i = 0 := by
  induction L with
  | zero => simp [sumNat]
  | succ L ih =>
    simp only [sumNat, Nat.add_eq_zero_iff, ih]
    constructor
    · intro ⟨h1, h2⟩ i hi
      by_cases h : i = L
      · subst h; exact h2
      · exact h1 i (by omega)
    · intro h
      exact ⟨fun i hi => h i (by omega), h L (by omega)⟩

theorem sumInt_telescope (L : Nat) (p : Nat → Int) :
    sumInt L (fun i => p (i + 1) - p i) = p L - p 0 := by
  induction L with
  | zero => simp [sumInt]
  | succ L ih =>
    simp only [sumInt, ih]
    omega

theorem sumInt_telescope_rev (L : Nat) (p : Nat → Int) :
    sumInt L (fun i => p i - p (i + 1)) = p 0 - p L := by
  induction L with
  | zero => simp [sumInt]
  | succ L ih =>
    simp only [sumInt, ih]
    omega

def popcount (n : Nat) : Nat :=
  if n = 0 then 0 else (n % 2) + popcount (n / 2)
termination_by n

theorem popcount_zero : popcount 0 = 0 := by
  unfold popcount; simp

theorem popcount_step (n : Nat) : popcount n = n % 2 + popcount (n / 2) := by
  conv => lhs; unfold popcount
  by_cases h : n = 0
  · subst h; simp [popcount_zero]
  · simp [h]

theorem popcount_two_mul_add (q b : Nat) (hb : b < 2) :
    popcount (2 * q + b) = popcount q + b := by
  rw [popcount_step]
  have h1 : (2 * q + b) % 2 = b := by omega
  have h2 : (2 * q + b) / 2 = q := by omega
  rw [h1, h2]
  omega

theorem popcount_eq_sum_bits (L n : Nat) (hn : n < 2 ^ L) :
    popcount n = sumNat L (fun i => boolNat (bitAt n i)) := by
  induction L generalizing n with
  | zero =>
    have h0 : n = 0 := by simp at hn; omega
    subst h0; simp [popcount_zero, sumNat]
  | succ L ih =>
    rw [sumNat_shift, popcount_step, boolNat_bitAt]
    simp only [Nat.pow_zero, Nat.div_one]
    have hdiv : n / 2 < 2 ^ L := by
      rw [Nat.pow_succ] at hn; omega
    rw [ih (n / 2) hdiv]
    congr 1
    apply sumNat_congr
    intro i _
    rw [bitAt_succ]

theorem sum_bits_val (L n : Nat) (hn : n < 2 ^ L) :
    sumNat L (fun i => boolNat (bitAt n i) * 2 ^ i) = n := by
  induction L generalizing n with
  | zero =>
    have h0 : n = 0 := by simp at hn; omega
    subst h0; simp [sumNat]
  | succ L ih =>
    rw [sumNat_shift]
    have h0 : boolNat (bitAt n 0) * 2 ^ 0 = n % 2 := by
      rw [boolNat_bitAt]; simp
    rw [h0]
    have hdiv : n / 2 < 2 ^ L := by
      rw [Nat.pow_succ] at hn; omega
    have htail : sumNat L (fun i => boolNat (bitAt n (i + 1)) * 2 ^ (i + 1)) =
        2 * sumNat L (fun i => boolNat (bitAt (n / 2) i) * 2 ^ i) := by
      rw [← sumNat_mul_left]
      apply sumNat_congr
      intro i _
      rw [bitAt_succ, Nat.pow_succ, Nat.mul_comm (2 ^ i) 2, ← Nat.mul_assoc,
          Nat.mul_comm _ 2, Nat.mul_assoc]
    rw [htail, ih (n / 2) hdiv]
    omega

theorem sum_bool_val_lt (L : Nat) (f : Nat → Bool) :
    sumNat L (fun i => boolNat (f i) * 2 ^ i) < 2 ^ L := by
  induction L with
  | zero => simp [sumNat]
  | succ L ih =>
    simp only [sumNat, Nat.pow_succ]
    have hb : boolNat (f L) ≤ 1 := by cases f L <;> decide
    have hmul : boolNat (f L) * 2 ^ L ≤ 2 ^ L := by
      calc boolNat (f L) * 2 ^ L ≤ 1 * 2 ^ L := Nat.mul_le_mul_right _ hb
      _ = 2 ^ L := Nat.one_mul _
    omega

theorem popcount_sum_bool_val (L : Nat) (f : Nat → Bool) :
    popcount (sumNat L (fun i => boolNat (f i) * 2 ^ i)) =
      sumNat L (fun i => boolNat (f i)) := by
  induction L generalizing f with
  | zero => simp [sumNat, popcount_zero]
  | succ L ih =>
    rw [sumNat_shift, sumNat_shift]
    have htail : sumNat L (fun i => boolNat (f (i + 1)) * 2 ^ (i + 1)) =
        2 * sumNat L (fun i => boolNat (f (i + 1)) * 2 ^ i) := by
      rw [← sumNat_mul_left]
      apply sumNat_congr
      intro i _
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ i) 2, ← Nat.mul_assoc,
          Nat.mul_comm _ 2, Nat.mul_assoc]
    rw [htail, Nat.pow_zero, Nat.mul_one, Nat.add_comm]
    have hb : boolNat (f 0) < 2 := by cases f 0 <;> decide
    rw [popcount_two_mul_add _ _ hb, ih (fun i => f (i + 1))]
    omega

def v2 (n : Nat) : Nat :=
  if n = 0 then 0 else if n % 2 = 1 then 0 else 1 + v2 (n / 2)
termination_by n

theorem v2_zero : v2 0 = 0 := by unfold v2; simp

theorem v2_odd {n : Nat} (h : n % 2 = 1) : v2 n = 0 := by
  unfold v2
  have hne : n ≠ 0 := by omega
  simp [hne, h]

theorem v2_even {n : Nat} (hne : n ≠ 0) (he : n % 2 = 0) : v2 n = 1 + v2 (n / 2) := by
  conv => lhs; unfold v2
  have h1 : ¬ (n % 2 = 1) := by omega
  simp [hne, h1]

theorem pow2_dvd_iff_le_v2 {n i : Nat} (hn : 0 < n) :
    2 ^ i ∣ n ↔ i ≤ v2 n := by
  induction i generalizing n with
  | zero => simp
  | succ i ih =>
    by_cases he : n % 2 = 0
    · rw [v2_even (by omega) he]
      have hdiv : 0 < n / 2 := by omega
      have hdvd : 2 ^ (i + 1) ∣ n ↔ 2 ^ i ∣ (n / 2) := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ i) 2]
        constructor
        · rintro ⟨k, hk⟩
          refine ⟨k, ?_⟩
          rw [Nat.mul_assoc] at hk
          omega
        · rintro ⟨k, hk⟩
          refine ⟨k, ?_⟩
          rw [Nat.mul_assoc, ← hk]
          omega
      rw [hdvd, ih hdiv]
      omega
    · have hodd : n % 2 = 1 := by omega
      rw [v2_odd hodd]
      constructor
      · rintro ⟨k, hk⟩
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ i) 2, Nat.mul_assoc] at hk
        omega
      · intro h; omega

theorem v2_lt_of_lt_pow2 {n L : Nat} (hpos : 0 < n) (hlt : n < 2 ^ L) : v2 n < L := by
  apply Nat.lt_of_not_le
  intro hle
  have hdvd : 2 ^ L ∣ n := (pow2_dvd_iff_le_v2 hpos).mpr hle
  have hle2 : 2 ^ L ≤ n := Nat.le_of_dvd hpos hdvd
  omega

def carriesAddAux (a b c : Nat) : Nat :=
  if a = 0 ∧ b = 0 then 0
  else
    let c' := (a % 2 + b % 2 + c) / 2
    c' + carriesAddAux (a / 2) (b / 2) c'
termination_by a + b

def carriesAdd (a b : Nat) : Nat := carriesAddAux a b 0

theorem kummer_carriesAddAux (a b c : Nat) (hc : c ≤ 1) :
    popcount (a + b + c) + carriesAddAux a b c = popcount a + popcount b + c := by
  have hstrong : ∀ s a b c, a + b ≤ s → c ≤ 1 →
      popcount (a + b + c) + carriesAddAux a b c = popcount a + popcount b + c := by
    intro s
    induction s with
    | zero =>
      intro a b c hab hc
      have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst ha; subst hb
      unfold carriesAddAux
      simp only [and_self, ↓reduceIte, popcount_zero, Nat.zero_add, Nat.add_zero]
      have h01 : c = 0 ∨ c = 1 := by omega
      rcases h01 with rfl | rfl
      · simp [popcount_zero]
      · rw [popcount_step]; simp [popcount_zero]
    | succ s ih =>
      intro a b c hab hc
      by_cases h0 : a = 0 ∧ b = 0
      · rcases h0 with ⟨rfl, rfl⟩
        unfold carriesAddAux
        simp only [and_self, ↓reduceIte, popcount_zero, Nat.zero_add, Nat.add_zero]
        have h01 : c = 0 ∨ c = 1 := by omega
        rcases h01 with rfl | rfl
        · simp [popcount_zero]
        · rw [popcount_step]; simp [popcount_zero]
      · conv => lhs; rw [show carriesAddAux a b c =
            (a % 2 + b % 2 + c) / 2 + carriesAddAux (a / 2) (b / 2) ((a % 2 + b % 2 + c) / 2) by
              conv => lhs; unfold carriesAddAux
              simp [h0]]
        have hstep := ih (a / 2) (b / 2) ((a % 2 + b % 2 + c) / 2) (by omega) (by omega)
        have hdecomp : a + b + c =
            2 * (a / 2 + b / 2 + (a % 2 + b % 2 + c) / 2) + (a % 2 + b % 2 + c) % 2 := by omega
        rw [hdecomp, popcount_two_mul_add _ _ (by omega), popcount_step a, popcount_step b]
        omega
  exact hstrong (a + b) a b c (Nat.le_refl _) hc

theorem kummer_carriesAdd (a b : Nat) :
    popcount (a + b) + carriesAdd a b = popcount a + popcount b := by
  have h := kummer_carriesAddAux a b 0 (by omega)
  simpa [carriesAdd] using h

def carryIn (a b i : Nat) : Nat :=
  ((a % 2 ^ i) + (b % 2 ^ i)) / 2 ^ i

theorem carryIn_zero (a b : Nat) : carryIn a b 0 = 0 := by
  simp [carryIn, Nat.mod_one]

theorem carryIn_le_one (a b i : Nat) : carryIn a b i ≤ 1 := by
  unfold carryIn
  have h1 : a % 2 ^ i < 2 ^ i := Nat.mod_lt _ (Nat.two_pow_pos i)
  have h2 : b % 2 ^ i < 2 ^ i := Nat.mod_lt _ (Nat.two_pow_pos i)
  have h3 : a % 2 ^ i + b % 2 ^ i < 2 * 2 ^ i := by omega
  have hpos : 0 < 2 ^ i := Nat.two_pow_pos i
  exact Nat.le_of_lt_succ (by
    rw [Nat.div_lt_iff_lt_mul hpos]
    omega)

theorem carryIn_eq_zero_of_sum_lt {a b i : Nat} (h : a + b < 2 ^ i) :
    carryIn a b i = 0 := by
  unfold carryIn
  have ha : a % 2 ^ i = a := Nat.mod_eq_of_lt (by omega)
  have hb : b % 2 ^ i = b := Nat.mod_eq_of_lt (by omega)
  rw [ha, hb]
  exact Nat.div_eq_of_lt h

theorem carriesAddAux_eq_sum_carryIn_general (L a b c : Nat)
    (hc : c ≤ 1) (hsum : a + b + c < 2 ^ L) :
    carriesAddAux a b c =
      sumNat L (fun i => ((a % 2 ^ (i + 1)) + (b % 2 ^ (i + 1)) + c) / 2 ^ (i + 1)) := by
  induction L generalizing a b c with
  | zero =>
    simp at hsum
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha; subst hb
    unfold carriesAddAux; simp [sumNat]
  | succ L ih =>
    rw [sumNat_shift]
    have h0 : (a % 2 ^ 1 + b % 2 ^ 1 + c) / 2 ^ 1 = (a % 2 + b % 2 + c) / 2 := by simp
    rw [h0]
    let c' := (a % 2 + b % 2 + c) / 2
    have hc' : c' ≤ 1 := by omega
    have hdivsum : a / 2 + b / 2 + c' < 2 ^ L := by
      rw [Nat.pow_succ] at hsum; omega
    by_cases hab : a = 0 ∧ b = 0
    · rcases hab with ⟨rfl, rfl⟩
      unfold carriesAddAux
      simp only [and_self, ↓reduceIte]
      have hc0 : (0 % 2 + 0 % 2 + c) / 2 = 0 := by omega
      rw [hc0, Nat.zero_add]
      symm
      rw [sumNat_eq_zero_iff]
      intro i _
      have hlt : c < 2 ^ (i + 2) := by
        have : 2 ≤ 2 ^ (i + 2) := by
          calc 2 = 2 ^ 1 := by decide
          _ ≤ 2 ^ (i + 2) := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      simpa using Nat.div_eq_of_lt hlt
    · conv => lhs; unfold carriesAddAux
      simp only [hab, ↓reduceIte]
      rw [ih (a / 2) (b / 2) c' hc' hdivsum]
      congr 1
      apply sumNat_congr
      intro i _
      have hpow : 2 ^ (i + 2) = 2 * 2 ^ (i + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
      have ha : a % 2 ^ (i + 2) = a % 2 + 2 * (a / 2 % 2 ^ (i + 1)) := by
        rw [hpow, mod_two_mul_pow2]
      have hb : b % 2 ^ (i + 2) = b % 2 + 2 * (b / 2 % 2 ^ (i + 1)) := by
        rw [hpow, mod_two_mul_pow2]
      rw [ha, hb, hpow, ← Nat.div_div_eq_div_mul]
      have hstep :
          (a % 2 + 2 * (a / 2 % 2 ^ (i + 1)) + (b % 2 + 2 * (b / 2 % 2 ^ (i + 1))) + c) / 2 =
            a / 2 % 2 ^ (i + 1) + b / 2 % 2 ^ (i + 1) + c' := by
        omega
      rw [hstep]

theorem carriesAdd_eq_sum_carryIn (L a b : Nat) (hsum : a + b < 2 ^ L) :
    carriesAdd a b = sumNat L (fun i => carryIn a b i) := by
  cases L with
  | zero =>
    simp at hsum
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha; subst hb
    simp [carriesAdd, carriesAddAux, sumNat]
  | succ L =>
    have h1 := carriesAddAux_eq_sum_carryIn_general (L + 1) a b 0 (by omega) (by omega)
    unfold carriesAdd
    rw [h1]
    have hlast : (a % 2 ^ (L + 1) + b % 2 ^ (L + 1) + 0) / 2 ^ (L + 1) = 0 := by
      have := carryIn_eq_zero_of_sum_lt hsum
      simpa [carryIn] using this
    rw [sumNat, hlast, Nat.add_zero]
    rw [sumNat_shift, carryIn_zero, Nat.zero_add]
    apply sumNat_congr
    intro i _
    simp [carryIn]

/-! ## Layer 2: Reusable Infinite Proof Mechanism — Bidirectional Transducer Coboundary & Coupling Engine -/

structure BitTransducer (S : Type) where
  step : S → Bool → S × Bool

def stateLSB {S : Type} (T : BitTransducer S) (s0 : S) (n : Nat) : Nat → S
  | 0 => s0
  | i + 1 => (T.step (stateLSB T s0 n i) (bitAt n i)).1

def outBitLSB {S : Type} (T : BitTransducer S) (s0 : S) (n : Nat) (i : Nat) : Bool :=
  (T.step (stateLSB T s0 n i) (bitAt n i)).2

def outValLSB {S : Type} (T : BitTransducer S) (s0 : S) (L n : Nat) : Nat :=
  sumNat L (fun i => boolNat (outBitLSB T s0 n i) * 2 ^ i)

def stateMSBAux {S : Type} (T : BitTransducer S) (s0 : S) (n : Nat) : Nat → Nat → S
  | 0, _ => s0
  | k + 1, lo => (T.step (stateMSBAux T s0 n k (lo + 1)) (bitAt n lo)).1

def stateMSB {S : Type} (T : BitTransducer S) (s0 : S) (L n i : Nat) : S :=
  stateMSBAux T s0 n (L - i) i

def outBitMSB {S : Type} (T : BitTransducer S) (s0 : S) (L n i : Nat) : Bool :=
  (T.step (stateMSB T s0 L n (i + 1)) (bitAt n i)).2

def outValMSB {S : Type} (T : BitTransducer S) (s0 : S) (L n : Nat) : Nat :=
  sumNat L (fun i => boolNat (outBitMSB T s0 L n i) * 2 ^ i)

theorem stateMSB_top {S : Type} (T : BitTransducer S) (s0 : S) (L n : Nat) :
    stateMSB T s0 L n L = s0 := by
  simp [stateMSB, stateMSBAux]

theorem stateMSB_step {S : Type} (T : BitTransducer S) (s0 : S) (L n i : Nat) (hi : i < L) :
    stateMSB T s0 L n i = (T.step (stateMSB T s0 L n (i + 1)) (bitAt n i)).1 := by
  unfold stateMSB
  have hsub : L - i = (L - (i + 1)) + 1 := by omega
  rw [hsub]
  rfl

theorem stateMSBAux_shift {S : Type} (T : BitTransducer S) (s0 : S) (n k lo : Nat) :
    stateMSBAux T s0 n k (lo + 1) = stateMSBAux T s0 (n / 2) k lo := by
  induction k generalizing lo with
  | zero => rfl
  | succ k ih =>
    simp only [stateMSBAux, ih (lo + 1), bitAt_succ]

theorem stateMSB_succ_shift {S : Type} (T : BitTransducer S) (s0 : S) (L n i : Nat) :
    stateMSB T s0 (L + 1) n (i + 1) = stateMSB T s0 L (n / 2) i := by
  unfold stateMSB
  have hsub : L + 1 - (i + 1) = L - i := by omega
  rw [hsub, stateMSBAux_shift]

theorem outBitMSB_succ_shift {S : Type} (T : BitTransducer S) (s0 : S) (L n i : Nat) :
    outBitMSB T s0 (L + 1) n (i + 1) = outBitMSB T s0 L (n / 2) i := by
  unfold outBitMSB
  rw [stateMSB_succ_shift, bitAt_succ]

theorem outValMSB_succ {S : Type} (T : BitTransducer S) (s0 : S) (L n : Nat) :
    outValMSB T s0 (L + 1) n =
      boolNat (outBitMSB T s0 (L + 1) n 0) + 2 * outValMSB T s0 L (n / 2) := by
  unfold outValMSB
  rw [sumNat_shift, Nat.pow_zero, Nat.mul_one]
  congr 1
  rw [← sumNat_mul_left]
  apply sumNat_congr
  intro i _
  rw [outBitMSB_succ_shift, Nat.pow_succ, Nat.mul_comm (2 ^ i) 2, ← Nat.mul_assoc,
      Nat.mul_comm _ 2, Nat.mul_assoc]

/-- Finite 1-bit coboundary certificate for an LSB-first transducer.
    Checking this single local transition equation lifts automatically to ∀ L, ∀ n < 2^L. -/
structure LSBCoboundaryCert {S : Type} (T : BitTransducer S) where
  weight : S → Int
  pot : S → Int
  α : Int
  β : Int
  local_law : ∀ (s : S) (b : Bool),
    let p := T.step s b
    weight s + (pot p.1 - pot s) = α * boolInt p.2 - β * boolInt b

/-- Finite 1-bit coboundary certificate for an MSB-first transducer.
    Checking this single local transition equation lifts automatically to ∀ L, ∀ n < 2^L. -/
structure MSBCoboundaryCert {S : Type} (T : BitTransducer S) where
  weight : S → Int
  pot : S → Int
  α : Int
  β : Int
  local_law : ∀ (s : S) (b : Bool),
    let p := T.step s b
    weight p.1 + (pot p.1 - pot s) = α * boolInt p.2 - β * boolInt b

/-- ENGINE THEOREM 1A (Finite → Infinite LSB Lifting):
    Any 1-bit LSB coboundary certificate automatically lifts to a global conservation law
    for ALL bit-widths L and ALL n < 2^L. -/
theorem coboundary_lift_LSB {S : Type} {T : BitTransducer S}
    (cert : LSBCoboundaryCert T) (s0 : S) (L n : Nat) (hn : n < 2 ^ L) :
    sumInt L (fun i => cert.weight (stateLSB T s0 n i)) +
      (cert.pot (stateLSB T s0 n L) - cert.pot s0) =
      cert.α * (popcount (outValLSB T s0 L n) : Int) - cert.β * (popcount n : Int) := by
  have hpoint :
      sumInt L (fun i =>
        cert.weight (stateLSB T s0 n i) +
          (cert.pot (stateLSB T s0 n (i + 1)) - cert.pot (stateLSB T s0 n i))) =
      sumInt L (fun i =>
        cert.α * boolInt (outBitLSB T s0 n i) - cert.β * boolInt (bitAt n i)) := by
    apply sumInt_congr
    intro i _
    exact cert.local_law (stateLSB T s0 n i) (bitAt n i)
  have htel : sumInt L (fun i => cert.pot (stateLSB T s0 n (i + 1)) - cert.pot (stateLSB T s0 n i)) =
      cert.pot (stateLSB T s0 n L) - cert.pot (stateLSB T s0 n 0) :=
    sumInt_telescope L (fun i => cert.pot (stateLSB T s0 n i))
  rw [sumInt_add, htel, sumInt_sub, sumInt_const_mul, sumInt_const_mul] at hpoint
  have hstate0 : stateLSB T s0 n 0 = s0 := rfl
  rw [hstate0] at hpoint
  have hout : sumInt L (fun i => boolInt (outBitLSB T s0 n i)) =
      (popcount (outValLSB T s0 L n) : Int) := by
    rw [outValLSB, popcount_sum_bool_val, ← sumInt_ofNat]
    apply sumInt_congr
    intro i _
    exact boolInt_eq_ofNat_boolNat _
  have hin : sumInt L (fun i => boolInt (bitAt n i)) = (popcount n : Int) := by
    rw [popcount_eq_sum_bits L n hn, ← sumInt_ofNat]
    apply sumInt_congr
    intro i _
    exact boolInt_eq_ofNat_boolNat _
  rw [hout, hin] at hpoint
  exact hpoint

/-- ENGINE THEOREM 1B (Finite → Infinite MSB Lifting):
    Any 1-bit MSB coboundary certificate automatically lifts to a global conservation law
    for ALL bit-widths L and ALL n < 2^L. -/
theorem coboundary_lift_MSB {S : Type} {T : BitTransducer S}
    (cert : MSBCoboundaryCert T) (s0 : S) (L n : Nat) (hn : n < 2 ^ L) :
    sumInt L (fun i => cert.weight (stateMSB T s0 L n i)) +
      (cert.pot (stateMSB T s0 L n 0) - cert.pot s0) =
      cert.α * (popcount (outValMSB T s0 L n) : Int) - cert.β * (popcount n : Int) := by
  have hpoint :
      sumInt L (fun i =>
        cert.weight (stateMSB T s0 L n i) +
          (cert.pot (stateMSB T s0 L n i) - cert.pot (stateMSB T s0 L n (i + 1)))) =
      sumInt L (fun i =>
        cert.α * boolInt (outBitMSB T s0 L n i) - cert.β * boolInt (bitAt n i)) := by
    apply sumInt_congr
    intro i hi
    have hlaw := cert.local_law (stateMSB T s0 L n (i + 1)) (bitAt n i)
    have hst := stateMSB_step T s0 L n i hi
    simpa [hst, outBitMSB] using hlaw
  have htel : sumInt L (fun i => cert.pot (stateMSB T s0 L n i) - cert.pot (stateMSB T s0 L n (i + 1))) =
      cert.pot (stateMSB T s0 L n 0) - cert.pot (stateMSB T s0 L n L) :=
    sumInt_telescope_rev L (fun i => cert.pot (stateMSB T s0 L n i))
  rw [sumInt_add, htel, sumInt_sub, sumInt_const_mul, sumInt_const_mul] at hpoint
  rw [stateMSB_top] at hpoint
  have hout : sumInt L (fun i => boolInt (outBitMSB T s0 L n i)) =
      (popcount (outValMSB T s0 L n) : Int) := by
    rw [outValMSB, popcount_sum_bool_val, ← sumInt_ofNat]
    apply sumInt_congr
    intro i _
    exact boolInt_eq_ofNat_boolNat _
  have hin : sumInt L (fun i => boolInt (bitAt n i)) = (popcount n : Int) := by
    rw [popcount_eq_sum_bits L n hn, ← sumInt_ofNat]
    apply sumInt_congr
    intro i _
    exact boolInt_eq_ofNat_boolNat _
  rw [hout, hin] at hpoint
  exact hpoint

/-- ENGINE THEOREM 2 (Universal Dual Coupling Elimination Law):
    Given an MSB transducer and an LSB transducer with matched output scale α and input scale β,
    coupled pointwise by `weight_R(r_i) - weight_C(c_i) = ρ_i - α * w_i`,
    the input bit-weight `popcount n` cancels identically, leaving an exact infinite law
    relating output bit-weights, coupling wrap count, boundary potentials, and the orbit sum! -/
theorem dual_coupling_lift
    {SR SC : Type} {TR : BitTransducer SR} {TC : BitTransducer SC}
    (certR : MSBCoboundaryCert TR) (certC : LSBCoboundaryCert TC)
    (hα : certR.α = certC.α) (hβ : certR.β = certC.β)
    (rTop : SR) (cBot : SC) (L n : Nat) (hn : n < 2 ^ L)
    (ρ w : Nat → Int)
    (hcouple : ∀ i, i < L →
      certR.weight (stateMSB TR rTop L n i) - certC.weight (stateLSB TC cBot n i) =
        ρ i - certC.α * w i) :
    certC.α * ((popcount (outValLSB TC cBot L n) : Int) -
               (popcount (outValMSB TR rTop L n) : Int) -
               sumInt L w) =
      (certC.pot (stateLSB TC cBot n L) - certC.pot cBot) -
      (certR.pot (stateMSB TR rTop L n 0) - certR.pot rTop) -
      sumInt L ρ := by
  have hMSB := coboundary_lift_MSB certR rTop L n hn
  have hLSB := coboundary_lift_LSB certC cBot L n hn
  rw [hα, hβ] at hMSB
  have hdiff :
      sumInt L (fun i => certR.weight (stateMSB TR rTop L n i) -
                         certC.weight (stateLSB TC cBot n i)) =
      sumInt L ρ - certC.α * sumInt L w := by
    rw [← sumInt_const_mul, ← sumInt_sub]
    exact sumInt_congr hcouple
  rw [sumInt_sub] at hdiff
  have hmul :
      certC.α * ((popcount (outValLSB TC cBot L n) : Int) -
                 (popcount (outValMSB TR rTop L n) : Int) -
                 sumInt L w) =
      certC.α * (popcount (outValLSB TC cBot L n) : Int) -
      certC.α * (popcount (outValMSB TR rTop L n) : Int) -
      certC.α * sumInt L w := by
    rw [Int.mul_sub, Int.mul_sub]
  rw [hmul]
  omega

/-! ## Layer 3: General Odd-Modulus Dual Carry-Residue Automaton -/

/-- MSB-first Euclidean division automaton for modulus `m`:
    `2 * r_in + b = m * e + r_out`, `0 ≤ r_out < m`. -/
def msbDivTransducer (m : Nat) : BitTransducer Nat where
  step r b :=
    let v := 2 * r + boolNat b
    (v % m, decide (v / m ≥ 1))

/-- LSB-first 2-adic division carry transducer for odd modulus `m`:
    `q = b XOR (c mod 2)`, `c + m * q = b + 2 * c_next`, `0 ≤ c_next < m`. -/
def lsbCarryTransducer (m : Nat) : BitTransducer Nat where
  step c b :=
    let q : Bool := xor b ((c % 2) == 1)
    let cNext := (c + m * boolNat q - boolNat b) / 2
    (cNext, q)

/-- Exact state-bounded transition arithmetic for `msbDivTransducer`. -/
theorem msbDiv_step_eq {m r : Nat} (hm : 0 < m) (hr : r < m) (b : Bool) :
    let p := (msbDivTransducer m).step r b
    2 * r + boolNat b = m * boolNat p.2 + p.1 ∧ p.1 < m := by
  simp only [msbDivTransducer]
  have hb : boolNat b ≤ 1 := by cases b <;> decide
  have hlt : 2 * r + boolNat b < 2 * m := by omega
  have hq : (2 * r + boolNat b) / m < 2 := by
    rw [Nat.div_lt_iff_lt_mul hm]; omega
  have hdiv : 2 * r + boolNat b = m * ((2 * r + boolNat b) / m) + (2 * r + boolNat b) % m := by
    have := Nat.div_add_mod (2 * r + boolNat b) m
    omega
  have hbool : boolNat (decide ((2 * r + boolNat b) / m ≥ 1)) = (2 * r + boolNat b) / m := by
    match h : (2 * r + boolNat b) / m with
    | 0 => decide
    | 1 => decide
    | k + 2 => rw [h] at hq; omega
  refine ⟨?_, Nat.mod_lt _ hm⟩
  rw [hbool]
  exact hdiv

/-- Exact state-bounded transition arithmetic for `lsbCarryTransducer` (odd `m`). -/
theorem lsbCarry_step_eq {m c : Nat} (hodd : m % 2 = 1) (hc : c < m) (b : Bool) :
    let p := (lsbCarryTransducer m).step c b
    c + m * boolNat p.2 = boolNat b + 2 * p.1 ∧ p.1 < m := by
  simp only [lsbCarryTransducer]
  have hparity : (c + m * boolNat (xor b (c % 2 == 1))) % 2 = boolNat b := by
    have h01 : c % 2 = 0 ∨ c % 2 = 1 := by omega
    cases b <;> rcases h01 with h | h <;> simp [boolNat, h] <;> omega
  have hge : boolNat b ≤ c + m * boolNat (xor b (c % 2 == 1)) := by
    cases b
    · simp [boolNat]
    · by_cases h : c % 2 = 0
      · simp [boolNat, h]; omega
      · have h1 : c % 2 = 1 := by omega
        simp [boolNat, h1]; omega
  have hqle : boolNat (xor b (c % 2 == 1)) ≤ 1 := by cases xor b (c % 2 == 1) <;> decide
  have hmul : m * boolNat (xor b (c % 2 == 1)) ≤ m := by
    calc m * boolNat (xor b (c % 2 == 1)) ≤ m * 1 := Nat.mul_le_mul_left _ hqle
    _ = m := Nat.mul_one _
  constructor <;> omega

/-- Exact MSB transducer restricted to `Fin m` so the 1-bit coboundary cert needs zero side hypotheses! -/
def msbDivFin (m : Nat) (hm : 0 < m) : BitTransducer (Fin m) where
  step r b :=
    let p := (msbDivTransducer m).step r.val b
    (⟨p.1, (msbDiv_step_eq hm r.isLt b).2⟩, p.2)

/-- Exact LSB carry transducer restricted to `Fin m` so the 1-bit coboundary cert is total on `Fin m`! -/
def lsbCarryFin (m : Nat) (hodd : m % 2 = 1) : BitTransducer (Fin m) where
  step c b :=
    let p := (lsbCarryTransducer m).step c.val b
    (⟨p.1, (lsbCarry_step_eq hodd c.isLt b).2⟩, p.2)

/-- 1-bit MSB coboundary certificate for Euclidean division mod `m`:
    `weight(r) = r`, `pot(r) = -2*r`, `α = m`, `β = 1`. -/
def msbDivCert (m : Nat) (hm : 0 < m) : MSBCoboundaryCert (msbDivFin m hm) where
  weight r := (r.val : Int)
  pot r := -2 * (r.val : Int)
  α := (m : Int)
  β := 1
  local_law r b := by
    have h := (msbDiv_step_eq hm r.isLt b).1
    simp only [msbDivFin, boolInt_eq_ofNat_boolNat]
    omega

/-- 1-bit LSB coboundary certificate for 2-adic division carries mod odd `m`:
    `weight(c) = c`, `pot(c) = +2*c`, `α = m`, `β = 1`. -/
def lsbCarryCert (m : Nat) (hodd : m % 2 = 1) : LSBCoboundaryCert (lsbCarryFin m hodd) where
  weight c := (c.val : Int)
  pot c := 2 * (c.val : Int)
  α := (m : Int)
  β := 1
  local_law c b := by
    have h := (lsbCarry_step_eq hodd c.isLt b).1
    simp only [lsbCarryFin, boolInt_eq_ofNat_boolNat]
    omega

/-- Convenient named accessors for our dual automaton on odd `m`. -/
def zeroFin {m : Nat} (hm : 0 < m) : Fin m := ⟨0, hm⟩

def remAt (m : Nat) (hm : 0 < m) (L n i : Nat) : Nat :=
  (stateMSB (msbDivFin m hm) (zeroFin hm) L n i).val

def eucQuot (m : Nat) (hm : 0 < m) (L n : Nat) : Nat :=
  outValMSB (msbDivFin m hm) (zeroFin hm) L n

def carryAt (m : Nat) (hodd : m % 2 = 1) (n i : Nat) : Nat :=
  (stateLSB (lsbCarryFin m hodd) (zeroFin (by omega)) n i).val

def twoAdicQuot (m : Nat) (hodd : m % 2 = 1) (L n : Nat) : Nat :=
  outValLSB (lsbCarryFin m hodd) (zeroFin (by omega)) L n

def carryDomCount (m : Nat) (hodd : m % 2 = 1) (L n : Nat) : Nat :=
  sumNat L (fun i => if remAt m (by omega) L n i < carryAt m hodd n i then 1 else 0)

def dualInvariant (m : Nat) (hodd : m % 2 = 1) (L n : Nat) : Int :=
  (popcount (twoAdicQuot m hodd L n) : Int) -
  (popcount (eucQuot m (by omega) L n) : Int) -
  (carryDomCount m hodd L n : Int)

/-- Halving operator modulo odd `m`: `2 * halveStep m x ≡ x (mod m)`. -/
def halveStep (m x : Nat) : Nat :=
  if x % 2 = 0 then x / 2 else (x + m) / 2

def halveIter (m : Nat) : Nat → Nat → Nat
  | 0, x => x
  | i + 1, x => halveStep m (halveIter m i x)

def halvingOrbitSum (m r L : Nat) : Nat :=
  sumNat L (fun i => halveIter m i (r % m))

theorem mersenne_odd {k : Nat} (hk : 1 ≤ k) : (2 ^ k - 1) % 2 = 1 := by
  have hk1 : k = (k - 1) + 1 := by omega
  rw [hk1, Nat.pow_succ]
  have hpos : 1 ≤ 2 ^ (k - 1) := Nat.two_pow_pos (k - 1)
  omega

theorem fermat_odd {k : Nat} (hk : 1 ≤ k) : (2 ^ k + 1) % 2 = 1 := by
  have hk1 : k = (k - 1) + 1 := by omega
  rw [hk1, Nat.pow_succ]
  omega

end ModularCarryResidueDuality
