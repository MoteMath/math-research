/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CarrylessCarriedResonanceCurve.Defs

/-!
# Proofs (`carryless-carried-resonance-curve`)

Carry-less polynomial powers over F_2[x] against integer powers, Hensel lift of scaled isometries, four-regime valuation law and resonance curve.
-/

/-
  Task 12 (adic-12):
  Carryless (F_2[x]) vs. Carried (Z) 2-Adic Polynomial-Bridge Hensel-Isometry Engine

  Standalone core Lean 4.36.0 formalization (zero Mathlib, zero sorry, zero custom axioms).
  Proves:
    1. Reusable Finite-to-Infinite Mechanism (`HenselBridge`):
       Any function F : Nat -> Int satisfying an exact 2-adic scaled-isometry law at scale L
       with a single base divisibility witness (2^L | F 0) constructively lifts via bit-by-bit
       silicon Hensel iteration (`henselLift`) to a unique coherent 2-adic root in Z_2,
       exact divisibility classification ∀ n t, exact valuation law ∀ n t j,
       non-naturality (unbounded 1-bit support) whenever ∀ n, F n ≠ 0,
       exact odd-scaling root invariance, and exact bit-0 root-shift law.
    2. Complete 4-Regime Global Valuation Law comparing carried powers a^k and carryless
       powers clpow(a, k) for all odd a > 1 and all even k >= 2:
         - Regime I   (a ≡ 1 mod 4): carried-dominated, v_2 = v_2(a - 1) + v_2(k)
         - Regime II  (a ≡ 3 mod 4, 2^e < s + e): carryless-dominated, v_2 = 2^e
         - Regime III (a ≡ 3 mod 4, 2^e > s + e): carried-dominated, v_2 = s + e
         - Regime IV  (Exact Resonance Curve: s = 2^e - e, e >= 2):
           For EVERY odd multiplier B : Nat, the perturbed bridge
             F_bridge a e B n = B * a^(2^e*(2n+1)) - clmul(B, clpow(a, 2^e*(2n+1)))
           is an exact scaled isometry at scale L = 2^e + 1 with a unique non-natural
           2-adic root in Z_2 \ N, exact root invariance for all odd B < 2^(2^e),
           and the exact Bit-(2^e) Carry-Coupling Root-Shift Law for all odd B.
    3. Infinite Non-Vacuity Witnesses (Mersenne & arithmetic progression families)
       and Kernel-Checked Sharpness Counterexamples.
-/

set_option autoImplicit false

namespace SiliconPolyBridge


theorem two_pow_int_pos (k : Nat) : (0 : Int) < ((2 ^ k : Nat) : Int) := by
  have h : 0 < 2 ^ k := Nat.two_pow_pos k
  omega

theorem two_pow_int_succ (k : Nat) :
    ((2 ^ (k + 1) : Nat) : Int) = ((2 ^ k : Nat) : Int) * 2 := by
  rw [Nat.pow_succ]
  push_cast
  rfl

theorem two_pow_int_add (a b : Nat) :
    ((2 ^ (a + b) : Nat) : Int) = ((2 ^ a : Nat) : Int) * ((2 ^ b : Nat) : Int) := by
  rw [Nat.pow_add]
  push_cast
  rfl

theorem two_pow_dvd_of_le {a b : Nat} (h : a ≤ b) :
    ((2 ^ a : Nat) : Int) ∣ ((2 ^ b : Nat) : Int) := by
  have hb : b = a + (b - a) := (Nat.add_sub_of_le h).symm
  rw [hb, two_pow_int_add]
  exact ⟨((2 ^ (b - a) : Nat) : Int), rfl⟩

theorem dvd_two_pow_of_le {a b : Nat} {z : Int} (h : a ≤ b)
    (hd : ((2 ^ b : Nat) : Int) ∣ z) : ((2 ^ a : Nat) : Int) ∣ z :=
  Int.dvd_trans (two_pow_dvd_of_le h) hd

theorem exactPow2_iff_odd_mul {k : Nat} {z : Int} :
    exactPow2 k z ↔ ∃ q : Int, z = ((2 ^ k : Nat) : Int) * q ∧ q % 2 ≠ 0 := by
  constructor
  · rintro ⟨⟨q, hq⟩, hnd⟩
    refine ⟨q, hq, ?_⟩
    intro hmod
    apply hnd
    have h2 : (2 : Int) ∣ q := Int.dvd_of_emod_eq_zero hmod
    rcases h2 with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    rw [hq, hr, two_pow_int_succ, Int.mul_assoc]
  · rintro ⟨q, rfl, hodd⟩
    refine ⟨⟨q, rfl⟩, ?_⟩
    rintro ⟨r, hr⟩
    rw [two_pow_int_succ, Int.mul_assoc] at hr
    have hpos : ((2 ^ k : Nat) : Int) ≠ 0 := Int.ne_of_gt (two_pow_int_pos k)
    have hq : q = 2 * r := Int.eq_of_mul_eq_mul_left hpos hr
    omega

theorem exactPow2_neg {k : Nat} {z : Int} (h : exactPow2 k z) : exactPow2 k (-z) := by
  rw [exactPow2_iff_odd_mul] at h ⊢
  rcases h with ⟨q, rfl, hodd⟩
  exact ⟨-q, by rw [Int.mul_neg], by omega⟩

theorem exactPow2_mul_odd {k : Nat} {c z : Int} (hc : c % 2 ≠ 0) (hz : exactPow2 k z) :
    exactPow2 k (c * z) := by
  rw [exactPow2_iff_odd_mul] at hz ⊢
  rcases hz with ⟨q, rfl, hq⟩
  refine ⟨c * q, ?_, ?_⟩
  · rw [← Int.mul_assoc, Int.mul_comm c ((2 ^ k : Nat) : Int), Int.mul_assoc]
  · have hc1 : c % 2 = 1 := by omega
    have hq1 : q % 2 = 1 := by omega
    rw [Int.mul_emod, hc1, hq1]
    decide

theorem exactPow2_mul {k m : Nat} {x y : Int} (hx : exactPow2 k x) (hy : exactPow2 m y) :
    exactPow2 (k + m) (x * y) := by
  rw [exactPow2_iff_odd_mul] at hx hy ⊢
  rcases hx with ⟨qx, rfl, hqx⟩
  rcases hy with ⟨qy, rfl, hqy⟩
  refine ⟨qx * qy, ?_, ?_⟩
  · rw [two_pow_int_add]
    rw [Int.mul_assoc, ← Int.mul_assoc qx, Int.mul_comm qx ((2 ^ m : Nat) : Int),
        Int.mul_assoc, Int.mul_assoc]
  · have hx1 : qx % 2 = 1 := by omega
    have hy1 : qy % 2 = 1 := by omega
    rw [Int.mul_emod, hx1, hy1]
    decide

theorem exactPow2_add_of_lt {k m : Nat} {x y : Int} (hkm : k < m)
    (hx : exactPow2 k x) (hy : ((2 ^ m : Nat) : Int) ∣ y) :
    exactPow2 k (x + y) := by
  have h1 : ((2 ^ (k + 1) : Nat) : Int) ∣ y := dvd_two_pow_of_le hkm hy
  have h0 : ((2 ^ k : Nat) : Int) ∣ y := dvd_two_pow_of_le (Nat.le_of_lt hkm) hy
  refine ⟨Int.dvd_add hx.1 h0, ?_⟩
  intro hsum
  have hx1 : ((2 ^ (k + 1) : Nat) : Int) ∣ x := by
    have : x = (x + y) - y := by omega
    rw [this]
    exact Int.dvd_sub hsum h1
  exact hx.2 hx1

theorem exactPow2_sub_of_lt {k m : Nat} {x y : Int} (hkm : k < m)
    (hx : exactPow2 k x) (hy : ((2 ^ m : Nat) : Int) ∣ y) :
    exactPow2 k (x - y) := by
  have : x - y = x + (-y) := by omega
  rw [this]
  exact exactPow2_add_of_lt hkm hx (Int.dvd_neg.mpr hy)

theorem exactPow2_sub_of_gt {k m : Nat} {x y : Int} (hkm : k < m)
    (hx : ((2 ^ m : Nat) : Int) ∣ x) (hy : exactPow2 k y) :
    exactPow2 k (x - y) := by
  have : x - y = -(y - x) := by omega
  rw [this]
  exact exactPow2_neg (exactPow2_sub_of_lt hkm hy hx)

theorem dvd_succ_add_of_exactPow2_eq {k : Nat} {x y : Int}
    (hx : exactPow2 k x) (hy : exactPow2 k y) :
    ((2 ^ (k + 1) : Nat) : Int) ∣ (x + y) := by
  rw [exactPow2_iff_odd_mul] at hx hy
  rcases hx with ⟨qx, rfl, hqx⟩
  rcases hy with ⟨qy, rfl, hqy⟩
  have heven : (qx + qy) % 2 = 0 := by omega
  rcases Int.dvd_of_emod_eq_zero heven with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  rw [← Int.mul_add, hr, two_pow_int_succ, Int.mul_assoc]

theorem dvd_succ_sub_of_exactPow2_eq {k : Nat} {x y : Int}
    (hx : exactPow2 k x) (hy : exactPow2 k y) :
    ((2 ^ (k + 1) : Nat) : Int) ∣ (x - y) := by
  have : x - y = x + (-y) := by omega
  rw [this]
  exact dvd_succ_add_of_exactPow2_eq hx (exactPow2_neg hy)

theorem exists_exactPow2_lt_of_not_dvd {t : Nat} {z : Int}
    (hnd : ¬ (((2 ^ t : Nat) : Int) ∣ z)) :
    ∃ j : Nat, j < t ∧ exactPow2 j z := by
  induction t with
  | zero =>
    exfalso
    exact hnd (Int.one_dvd z)
  | succ t ih =>
    by_cases h : ((2 ^ t : Nat) : Int) ∣ z
    · exact ⟨t, Nat.lt_succ_self t, h, hnd⟩
    · rcases ih h with ⟨j, hjt, hj⟩
      exact ⟨j, Nat.lt_succ_of_lt hjt, hj⟩

theorem exactPow2_two_pow (k : Nat) : exactPow2 k ((2 ^ k : Nat) : Int) := by
  rw [exactPow2_iff_odd_mul]
  exact ⟨1, (Int.mul_one _).symm, by decide⟩

theorem int_dvd_two_pow_sub_iff_mod_eq {t a b : Nat} :
    ((2 ^ t : Nat) : Int) ∣ ((a : Int) - (b : Int)) ↔ a % 2 ^ t = b % 2 ^ t := by
  constructor
  · intro hd
    have ha : (a : Int) % ((2 ^ t : Nat) : Int) = ((a % 2 ^ t : Nat) : Int) :=
      (Int.natCast_emod a (2 ^ t)).symm
    have hb : (b : Int) % ((2 ^ t : Nat) : Int) = ((b % 2 ^ t : Nat) : Int) :=
      (Int.natCast_emod b (2 ^ t)).symm
    have heq : (a : Int) % ((2 ^ t : Nat) : Int) = (b : Int) % ((2 ^ t : Nat) : Int) := by
      rcases hd with ⟨q, hq⟩
      have : (a : Int) = (b : Int) + ((2 ^ t : Nat) : Int) * q := by omega
      rw [this, Int.add_mul_emod_self_left]
    omega
  · intro hmod
    have hqa : (a : Int) = ((2 ^ t : Nat) : Int) * ((a / 2 ^ t : Nat) : Int) + ((a % 2 ^ t : Nat) : Int) := by
      have := Nat.div_add_mod a (2 ^ t)
      omega
    have hqb : (b : Int) = ((2 ^ t : Nat) : Int) * ((b / 2 ^ t : Nat) : Int) + ((b % 2 ^ t : Nat) : Int) := by
      have := Nat.div_add_mod b (2 ^ t)
      omega
    refine ⟨((a / 2 ^ t : Nat) : Int) - ((b / 2 ^ t : Nat) : Int), ?_⟩
    rw [Int.mul_sub]
    omega

theorem henselLift_lt (F : Nat → Int) (L t : Nat) :
    henselLift F L t < 2 ^ t := by
  induction t with
  | zero => simp [henselLift]
  | succ t ih =>
    simp only [henselLift]
    split
    · exact Nat.lt_trans ih (by rw [Nat.pow_succ]; omega)
    · rw [Nat.pow_succ]; omega

theorem henselLift_compat (F : Nat → Int) (L t : Nat) :
    henselLift F L (t + 1) % 2 ^ t = henselLift F L t := by
  have hlt := henselLift_lt F L t
  simp only [henselLift]
  split
  · exact Nat.mod_eq_of_lt hlt
  · rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt]

/-- Engine Soundness Theorem 1: Arbitrarily high 2-adic divisibility ∀ t : Nat. -/
theorem henselLift_dvd {F : Nat → Int} {L : Nat} (hF : ScaledIsometry F L) (t : Nat) :
    ((2 ^ (L + t) : Nat) : Int) ∣ F (henselLift F L t) := by
  induction t with
  | zero =>
    simpa [henselLift] using hF.base_dvd
  | succ t ih =>
    simp only [henselLift]
    by_cases hmod : (F (henselLift F L t) % ((2 ^ (L + t + 1) : Nat) : Int) == 0) = true
    · simp only [hmod]
      have h0 : F (henselLift F L t) % ((2 ^ (L + t + 1) : Nat) : Int) = 0 := by
        simpa using hmod
      exact Int.dvd_of_emod_eq_zero h0
    · simp only [hmod, Bool.false_eq_true, ↓reduceIte]
      have hne : F (henselLift F L t) % ((2 ^ (L + t + 1) : Nat) : Int) ≠ 0 := by
        intro h0; exact hmod (by simpa using h0)
      have hnd : ¬ (((2 ^ (L + t + 1) : Nat) : Int) ∣ F (henselLift F L t)) := by
        intro hd; exact hne (Int.emod_eq_zero_of_dvd hd)
      have hexF : exactPow2 (L + t) (F (henselLift F L t)) := ⟨ih, hnd⟩
      have hdiff_in : exactPow2 t (((henselLift F L t + 2 ^ t : Nat) : Int) - (henselLift F L t : Int)) := by
        have : ((henselLift F L t + 2 ^ t : Nat) : Int) - (henselLift F L t : Int) = ((2 ^ t : Nat) : Int) := by
          omega
        rw [this]
        exact exactPow2_two_pow t
      have hexDiff : exactPow2 (L + t) (F (henselLift F L t + 2 ^ t) - F (henselLift F L t)) :=
        hF.lip_exact _ _ t hdiff_in
      have hsum := dvd_succ_add_of_exactPow2_eq hexF hexDiff
      have heq : F (henselLift F L t) + (F (henselLift F L t + 2 ^ t) - F (henselLift F L t)) =
          F (henselLift F L t + 2 ^ t) := by omega
      rw [heq] at hsum
      exact hsum

/-- Engine Soundness Theorem 2: Exact 2-adic valuation law outside precision `t`. -/
theorem henselLift_exact_val {F : Nat → Int} {L : Nat} (hF : ScaledIsometry F L)
    (n t j : Nat) (hjt : j < t)
    (hex : exactPow2 j ((n : Int) - (henselLift F L t : Int))) :
    exactPow2 (L + j) (F n) := by
  have hdiff : exactPow2 (L + j) (F n - F (henselLift F L t)) :=
    hF.lip_exact n (henselLift F L t) j hex
  have hd : ((2 ^ (L + t) : Nat) : Int) ∣ F (henselLift F L t) := henselLift_dvd hF t
  have hlt : L + j < L + t := Nat.add_lt_add_left hjt L
  have hadd := exactPow2_add_of_lt hlt hdiff hd
  have heq : F n - F (henselLift F L t) + F (henselLift F L t) = F n := by omega
  rw [heq] at hadd
  exact hadd

/-- Engine Soundness Theorem 3: Exact global divisibility characterization ∀ n t : Nat. -/
theorem henselLift_iff_dvd {F : Nat → Int} {L : Nat} (hF : ScaledIsometry F L)
    (n t : Nat) :
    ((2 ^ (L + t) : Nat) : Int) ∣ F n ↔ n % 2 ^ t = henselLift F L t := by
  have hlt := henselLift_lt F L t
  constructor
  · intro hdn
    by_cases heq : n % 2 ^ t = henselLift F L t
    · exact heq
    · exfalso
      have hnd : ¬ (((2 ^ t : Nat) : Int) ∣ ((n : Int) - (henselLift F L t : Int))) := by
        intro hd
        have hm := int_dvd_two_pow_sub_iff_mod_eq.mp hd
        rw [Nat.mod_eq_of_lt hlt] at hm
        exact heq hm
      rcases exists_exactPow2_lt_of_not_dvd hnd with ⟨j, hjt, hexj⟩
      have hexFn := henselLift_exact_val hF n t j hjt hexj
      have hle : L + j + 1 ≤ L + t := by omega
      exact hexFn.2 (dvd_two_pow_of_le hle hdn)
  · intro hmod
    have hsub : ((2 ^ t : Nat) : Int) ∣ ((n : Int) - (henselLift F L t : Int)) := by
      rw [int_dvd_two_pow_sub_iff_mod_eq, Nat.mod_eq_of_lt hlt]
      exact hmod
    have hdiff := hF.lip_dvd n (henselLift F L t) t hsub
    have hroot := henselLift_dvd hF t
    have heq : F n = (F n - F (henselLift F L t)) + F (henselLift F L t) := by omega
    rw [heq]
    exact Int.dvd_add hdiff hroot

theorem nat_lt_two_pow (n : Nat) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    omega

theorem not_dvd_two_pow_of_ne_zero {z : Int} (hz : z ≠ 0) (k : Nat)
    (hk : z.natAbs < 2 ^ k) : ¬ (((2 ^ k : Nat) : Int) ∣ z) := by
  rintro ⟨q, hq⟩
  have hq0 : q ≠ 0 := by
    intro h0; rw [h0, Int.mul_zero] at hq; exact hz hq
  have h1 : 1 ≤ q.natAbs := by omega
  have habs : z.natAbs = 2 ^ k * q.natAbs := by
    rw [hq, Int.natAbs_mul]
    simp
  have hge : 2 ^ k ≤ z.natAbs := by
    rw [habs]
    exact Nat.le_mul_of_pos_right (2 ^ k) h1
  omega

/-- Engine Soundness Theorem 4: Non-Naturality (Unbounded 2-Adic Root Support)
    Whenever `F` has no natural root (`∀ n, F n ≠ 0`), its coherent 2-adic root
    cannot stabilize at any finite natural number: `∀ N, ∃ t, N < henselLift F L t`. -/
theorem henselLift_unbounded_of_ne_zero {F : Nat → Int} {L : Nat}
    (hF : ScaledIsometry F L) (hne : ∀ n : Nat, F n ≠ 0) :
    ∀ N : Nat, ∃ t : Nat, N < henselLift F L t := by
  have hex_bound : ∀ N : Nat, ∃ t : Nat, ∀ k ≤ N, ¬ (((2 ^ (L + t) : Nat) : Int) ∣ F k) := by
    intro N
    induction N with
    | zero =>
      refine ⟨(F 0).natAbs, ?_⟩
      intro k hk
      have hk0 : k = 0 := by omega
      subst hk0
      apply not_dvd_two_pow_of_ne_zero (hne 0)
      have h1 : (F 0).natAbs < 2 ^ (F 0).natAbs := nat_lt_two_pow _
      have h2 : 2 ^ (F 0).natAbs ≤ 2 ^ (L + (F 0).natAbs) :=
        Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_add_left _ _)
      omega
    | succ N ih =>
      rcases ih with ⟨t1, ht1⟩
      let t2 := (F (N + 1)).natAbs
      refine ⟨max t1 t2, ?_⟩
      intro k hk
      by_cases hle : k ≤ N
      · intro hd
        exact ht1 k hle (dvd_two_pow_of_le (Nat.add_le_add_left (Nat.le_max_left t1 t2) L) hd)
      · have hkN : k = N + 1 := by omega
        subst hkN
        apply not_dvd_two_pow_of_ne_zero (hne (N + 1))
        have h1 : t2 < 2 ^ t2 := nat_lt_two_pow t2
        have h2 : 2 ^ t2 ≤ 2 ^ (L + max t1 t2) :=
          Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
        omega
  intro N
  rcases hex_bound N with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  by_cases hlt : N < henselLift F L t
  · exact hlt
  · exfalso
    have hle' : henselLift F L t ≤ N := by omega
    exact ht (henselLift F L t) hle' (henselLift_dvd hF t)

/-- Engine Combinator 1: Odd-Scaling Root Invariance across all precisions `t : Nat`. -/
theorem henselLift_odd_scale_invariant {F G : Nat → Int} {L : Nat} {c : Int}
    (hF : ScaledIsometry F L) (hG : ScaledIsometry G L)
    (hFG : ∀ n, G n = c * F n) :
    ∀ t : Nat, henselLift G L t = henselLift F L t := by
  intro t
  have hdG : ((2 ^ (L + t) : Nat) : Int) ∣ G (henselLift F L t) := by
    rw [hFG]
    exact Int.dvd_mul_of_dvd_right (henselLift_dvd hF t)
  have hm := (henselLift_iff_dvd hG (henselLift F L t) t).mp hdG
  rw [Nat.mod_eq_of_lt (henselLift_lt F L t)] at hm
  exact hm.symm

/-- Engine Combinator 2: Exact Bit-0 Root-Shift Law from a single base congruence mod `2^(L+1)`. -/
theorem henselLift_bit0_shift {F G : Nat → Int} {L : Nat} {b : Bool}
    (hF : ScaledIsometry F L)
    (hcong : ((2 ^ (L + 1) : Nat) : Int) ∣
      (G 0 - F 0 - (if b then ((2 ^ L : Nat) : Int) else 0))) :
    henselLift G L 1 = (henselLift F L 1) ^^^ (if b then 1 else 0) := by
  have hF0 : ((2 ^ L : Nat) : Int) ∣ F 0 := hF.base_dvd
  have hF1 : henselLift F L 1 = if F 0 % ((2 ^ (L + 1) : Nat) : Int) == 0 then 0 else 1 := by
    simp [henselLift]
  have hG1 : henselLift G L 1 = if G 0 % ((2 ^ (L + 1) : Nat) : Int) == 0 then 0 else 1 := by
    simp [henselLift]
  rw [hF1, hG1]
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Int.sub_zero] at hcong ⊢
    by_cases hFm : (F 0 % ((2 ^ (L + 1) : Nat) : Int) == 0) = true
    · have hFd : ((2 ^ (L + 1) : Nat) : Int) ∣ F 0 :=
        Int.dvd_of_emod_eq_zero (by simpa using hFm)
      have hGd : ((2 ^ (L + 1) : Nat) : Int) ∣ G 0 := by
        have : G 0 = (G 0 - F 0) + F 0 := by omega
        rw [this]; exact Int.dvd_add hcong hFd
      have hGm : (G 0 % ((2 ^ (L + 1) : Nat) : Int) == 0) = true := by
        simpa using Int.emod_eq_zero_of_dvd hGd
      simp only [hFm, hGm]; decide
    · have hFnd : ¬ (((2 ^ (L + 1) : Nat) : Int) ∣ F 0) := by
        intro hd; exact hFm (by simpa using Int.emod_eq_zero_of_dvd hd)
      have hGnd : ¬ (((2 ^ (L + 1) : Nat) : Int) ∣ G 0) := by
        intro hGd
        have : F 0 = G 0 - (G 0 - F 0) := by omega
        rw [this] at hFnd
        exact hFnd (Int.dvd_sub hGd hcong)
      have hGm : (G 0 % ((2 ^ (L + 1) : Nat) : Int) == 0) ≠ true := by
        intro hm; exact hGnd (Int.dvd_of_emod_eq_zero (by simpa using hm))
      simp only [hFm, hGm]; decide
  | true =>
    simp only [↓reduceIte] at hcong ⊢
    by_cases hFm : (F 0 % ((2 ^ (L + 1) : Nat) : Int) == 0) = true
    · have hFd : ((2 ^ (L + 1) : Nat) : Int) ∣ F 0 :=
        Int.dvd_of_emod_eq_zero (by simpa using hFm)
      have hGnd : ¬ (((2 ^ (L + 1) : Nat) : Int) ∣ G 0) := by
        intro hGd
        have h2L : ((2 ^ (L + 1) : Nat) : Int) ∣ ((2 ^ L : Nat) : Int) := by
          have : ((2 ^ L : Nat) : Int) = (G 0 - F 0) - (G 0 - F 0 - ((2 ^ L : Nat) : Int)) := by omega
          rw [this]
          exact Int.dvd_sub (Int.dvd_sub hGd hFd) hcong
        exact (exactPow2_two_pow L).2 h2L
      have hGm : (G 0 % ((2 ^ (L + 1) : Nat) : Int) == 0) ≠ true := by
        intro hm; exact hGnd (Int.dvd_of_emod_eq_zero (by simpa using hm))
      simp only [hFm, hGm]; decide
    · have hFnd : ¬ (((2 ^ (L + 1) : Nat) : Int) ∣ F 0) := by
        intro hd; exact hFm (by simpa using Int.emod_eq_zero_of_dvd hd)
      have hexF : exactPow2 L (F 0) := ⟨hF0, hFnd⟩
      have hsum : ((2 ^ (L + 1) : Nat) : Int) ∣ (F 0 + ((2 ^ L : Nat) : Int)) :=
        dvd_succ_add_of_exactPow2_eq hexF (exactPow2_two_pow L)
      have hGd : ((2 ^ (L + 1) : Nat) : Int) ∣ G 0 := by
        have : G 0 = (G 0 - F 0 - ((2 ^ L : Nat) : Int)) + (F 0 + ((2 ^ L : Nat) : Int)) := by omega
        rw [this]
        exact Int.dvd_add hcong hsum
      have hGm : (G 0 % ((2 ^ (L + 1) : Nat) : Int) == 0) = true := by
        simpa using Int.emod_eq_zero_of_dvd hGd
      simp only [hFm, hGm]; decide

/-- Structurally recursive fuel-bounded bit-spreading operator `S_r(n)`. -/
def spreadAux : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, r, n =>
    if n = 0 then 0
    else (n % 2) + 2 ^ r * spreadAux fuel r (n / 2)

/-- Bit-spreading (Frobenius dilation) operator `S_r(n) = ∑_i bit(n, i) * 2^(r*i)`. -/
def spread (r n : Nat) : Nat := spreadAux n r n

theorem clmulAux_eq_of_le {f1 f2 a b : Nat} (h1 : b ≤ f1) (h2 : b ≤ f2) :
    clmulAux f1 a b = clmulAux f2 a b := by
  induction f1 generalizing f2 b with
  | zero =>
    have hb : b = 0 := by omega
    subst hb
    cases f2 <;> rfl
  | succ f1 ih =>
    cases f2 with
    | zero =>
      have hb : b = 0 := by omega
      subst hb; rfl
    | succ f2 =>
      simp only [clmulAux]
      by_cases hb : b = 0
      · simp [hb]
      · simp only [hb, ↓reduceIte]
        have hlt1 : b / 2 ≤ f1 := by omega
        have hlt2 : b / 2 ≤ f2 := by omega
        rw [ih hlt1 hlt2]

theorem spreadAux_eq_of_le {f1 f2 r n : Nat} (h1 : n ≤ f1) (h2 : n ≤ f2) :
    spreadAux f1 r n = spreadAux f2 r n := by
  induction f1 generalizing f2 n with
  | zero =>
    have hn : n = 0 := by omega
    subst hn
    cases f2 <;> rfl
  | succ f1 ih =>
    cases f2 with
    | zero =>
      have hn : n = 0 := by omega
      subst hn; rfl
    | succ f2 =>
      simp only [spreadAux]
      by_cases hn : n = 0
      · simp [hn]
      · simp only [hn, ↓reduceIte]
        have hlt1 : n / 2 ≤ f1 := by omega
        have hlt2 : n / 2 ≤ f2 := by omega
        rw [ih hlt1 hlt2]

theorem clmul_unfold {a b : Nat} (hb : b ≠ 0) :
    clmul a b = if b % 2 = 1 then a ^^^ (2 * clmul a (b / 2)) else 2 * clmul a (b / 2) := by
  unfold clmul
  have hb' : b = (b - 1) + 1 := (Nat.sub_add_cancel (Nat.pos_of_ne_zero hb)).symm
  rw [clmulAux_eq_of_le (f2 := (b - 1) + 1) (Nat.le_refl b) (by omega)]
  simp only [clmulAux, hb, ↓reduceIte]
  rw [clmulAux_eq_of_le (f2 := b / 2) (by omega) (Nat.le_refl _)]

theorem spread_unfold {r n : Nat} (hn : n ≠ 0) :
    spread r n = (n % 2) + 2 ^ r * spread r (n / 2) := by
  unfold spread
  rw [spreadAux_eq_of_le (f2 := (n - 1) + 1) (Nat.le_refl n) (by omega)]
  simp only [spreadAux, hn, ↓reduceIte]
  rw [spreadAux_eq_of_le (f2 := n / 2) (by omega) (Nat.le_refl _)]

-- Basic bitwise helper lemmas for Nat
theorem two_mul_testBit_succ (x i : Nat) :
    (2 * x).testBit (i + 1) = x.testBit i := by
  have h : 2 * x = x <<< 1 := by rw [Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm]
  rw [h, Nat.testBit_shiftLeft]
  simp

theorem two_mul_xor_two_mul (x y : Nat) :
    (2 * x) ^^^ (2 * y) = 2 * (x ^^^ y) := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ i =>
    simp only [Nat.testBit_xor, two_mul_testBit_succ]

theorem xor_mod_two_pow (x y w : Nat) :
    (x ^^^ y) % 2 ^ w = (x % 2 ^ w) ^^^ (y % 2 ^ w) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor]
  by_cases h : i < w <;> simp [h]

theorem add_eq_xor_of_lt_pow2 {a b r : Nat} (ha : a < 2 ^ r) :
    a + 2 ^ r * b = a ^^^ (2 ^ r * b) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor]
  have hshift : (2 ^ r * b).testBit i = (decide (r ≤ i) && b.testBit (i - r)) := by
    rw [Nat.mul_comm, ← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]
  have hadd : (a + 2 ^ r * b).testBit i =
      if i < r then a.testBit i else b.testBit (i - r) := by
    by_cases hi : i < r
    · simp only [hi, ↓reduceIte]
      have hmod : (a + 2 ^ r * b) % 2 ^ r = a := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
      have h1 := congrArg (fun z => z.testBit i) hmod
      rw [Nat.testBit_mod_two_pow] at h1
      simpa [hi] using h1
    · simp only [hi, ↓reduceIte]
      have hge : r ≤ i := Nat.le_of_not_lt hi
      have hdiv : (a + 2 ^ r * b) / 2 ^ r = b := by
        rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos r), Nat.div_eq_of_lt ha, Nat.zero_add]
      have h1 := congrArg (fun z => z.testBit (i - r)) hdiv
      rw [Nat.testBit_div_two_pow] at h1
      have : i - r + r = i := Nat.sub_add_cancel hge
      rw [this] at h1
      exact h1
  rw [hadd, hshift]
  by_cases hi : i < r
  · have hge : ¬ (r ≤ i) := by omega
    simp [hi, hge]
  · have hge : r ≤ i := Nat.le_of_not_lt hi
    have ha0 : a.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide : 0 < 2) hge))
    simp [hi, hge, ha0]

theorem add_eq_xor_add_two_and (x y : Nat) :
    x + y = (x ^^^ y) + 2 * (x &&& y) := by
  induction x using Nat.strongRecOn generalizing y with
  | ind x ih =>
    by_cases hx : x = 0
    · subst hx; simp
    · have hlt : x / 2 < x := Nat.div_lt_self (Nat.pos_of_ne_zero hx) (by decide)
      have hrec := ih (x / 2) hlt (y / 2)
      have hx0 : x = 2 * (x / 2) + x % 2 := (Nat.div_add_mod x 2).symm
      have hy0 : y = 2 * (y / 2) + y % 2 := (Nat.div_add_mod y 2).symm
      have hdiv2_tb : ∀ z i : Nat, (z / 2).testBit i = z.testBit (i + 1) := by
        intro z i
        rw [← Nat.pow_one 2, Nat.testBit_div_two_pow]
      have hxor_div : (x ^^^ y) / 2 = (x / 2) ^^^ (y / 2) := by
        apply Nat.eq_of_testBit_eq; intro i
        rw [hdiv2_tb, Nat.testBit_xor, Nat.testBit_xor, hdiv2_tb, hdiv2_tb]
      have hxor_mod : (x ^^^ y) % 2 = (x % 2) ^^^ (y % 2) := by
        simpa [Nat.pow_one] using xor_mod_two_pow x y 1
      have hand_div : (x &&& y) / 2 = (x / 2) &&& (y / 2) := by
        apply Nat.eq_of_testBit_eq; intro i
        rw [hdiv2_tb, Nat.testBit_and, Nat.testBit_and, hdiv2_tb, hdiv2_tb]
      have hand_mod : (x &&& y) % 2 = (x % 2) &&& (y % 2) := by
        apply Nat.eq_of_testBit_eq; intro i
        cases i with
        | zero => simp [Nat.testBit_zero]
        | succ i =>
          have h1 : ((x &&& y) % 2).testBit (i + 1) = false :=
            Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide))
              (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ i + 1)))
          have h2 : ((x % 2) &&& (y % 2)).testBit (i + 1) = false := by
            rw [Nat.testBit_and]
            have : (x % 2).testBit (i + 1) = false :=
              Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide))
                (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ i + 1)))
            simp [this]
          rw [h1, h2]
      have hxor0 := Nat.div_add_mod (x ^^^ y) 2
      have hand0 := Nat.div_add_mod (x &&& y) 2
      have hbit : x % 2 + y % 2 = ((x % 2) ^^^ (y % 2)) + 2 * ((x % 2) &&& (y % 2)) := by
        have hx2 : x % 2 < 2 := Nat.mod_lt x (by decide)
        have hy2 : y % 2 < 2 := Nat.mod_lt y (by decide)
        rcases Nat.lt_succ_iff_lt_or_eq.mp hx2 with hx0' | hx1' <;>
        rcases Nat.lt_succ_iff_lt_or_eq.mp hy2 with hy0' | hy1'
        · have hx0'' : x % 2 = 0 := by omega
          have hy0'' : y % 2 = 0 := by omega
          rw [hx0'', hy0'']; decide
        · have hx0'' : x % 2 = 0 := by omega
          rw [hx0'', hy1']; decide
        · have hy0'' : y % 2 = 0 := by omega
          rw [hx1', hy0'']; decide
        · rw [hx1', hy1']; decide
      omega

theorem xor_le_add (x y : Nat) : x ^^^ y ≤ x + y := by
  have := add_eq_xor_add_two_and x y
  omega

-- Algebraic properties of clmul
theorem clmul_zero_right (a : Nat) : clmul a 0 = 0 := rfl

theorem clmul_one_right (a : Nat) : clmul a 1 = a := by
  simp [clmul, clmulAux]

theorem clmul_zero_left (b : Nat) : clmul 0 b = 0 := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    by_cases hb : b = 0
    · subst hb; rfl
    · rw [clmul_unfold hb, ih (b / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hb) (by decide))]
      split <;> simp

theorem clmul_one_left (b : Nat) : clmul 1 b = b := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    by_cases hb : b = 0
    · subst hb; rfl
    · rw [clmul_unfold hb, ih (b / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hb) (by decide))]
      have hdiv := Nat.div_add_mod b 2
      split
      · have h1 : 1 < 2 ^ 1 := by decide
        have := add_eq_xor_of_lt_pow2 (b := b / 2) h1
        simp only [Nat.pow_one] at this
        omega
      · omega

theorem clmul_two_mul_right (a b : Nat) : clmul a (2 * b) = 2 * clmul a b := by
  by_cases hb : b = 0
  · subst hb; simp [clmul_zero_right]
  · rw [clmul_unfold (by omega : 2 * b ≠ 0)]
    have hdiv : (2 * b) / 2 = b := by omega
    have hmod : (2 * b) % 2 = 0 := by omega
    rw [hdiv, hmod]
    simp

theorem clmul_two_mul_add_one_right (a b : Nat) :
    clmul a (2 * b + 1) = a ^^^ (2 * clmul a b) := by
  rw [clmul_unfold (by omega : 2 * b + 1 ≠ 0)]
  have hdiv : (2 * b + 1) / 2 = b := by omega
  have hmod : (2 * b + 1) % 2 = 1 := by omega
  rw [hdiv, hmod]
  simp

theorem clmul_expand (a x : Nat) :
    clmul a x = (if x % 2 = 1 then a else 0) ^^^ (2 * clmul a (x / 2)) := by
  by_cases hx0 : x = 0
  · subst hx0; simp [clmul_zero_right]
  · rw [clmul_unfold hx0]
    by_cases hx1 : x % 2 = 1
    · simp [hx1]
    · simp [hx1]

theorem clmul_two_mul_left (a b : Nat) : clmul (2 * a) b = 2 * clmul a b := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    by_cases hb : b = 0
    · subst hb; simp [clmul_zero_right]
    · have hlt : b / 2 < b := Nat.div_lt_self (Nat.pos_of_ne_zero hb) (by decide)
      have hstep := ih (b / 2) hlt
      rw [clmul_expand (2 * a) b, clmul_expand a b, hstep]
      by_cases hodd : b % 2 = 1
      · simp only [hodd, ↓reduceIte, two_mul_xor_two_mul]
      · simp only [hodd, ↓reduceIte, Nat.zero_xor]

theorem clmul_pow2_mul_right (a r b : Nat) :
    clmul a (2 ^ r * b) = 2 ^ r * clmul a b := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ r) 2, Nat.mul_assoc, Nat.mul_assoc,
        clmul_two_mul_right, ih]

theorem clmul_xor_right (a b c : Nat) :
    clmul a (b ^^^ c) = clmul a b ^^^ clmul a c := by
  induction b using Nat.strongRecOn generalizing c with
  | ind b ih =>
    by_cases hbc : b = 0
    · subst hbc; simp [clmul_zero_right]
    · have hlt : b / 2 < b := Nat.div_lt_self (Nat.pos_of_ne_zero hbc) (by decide)
      have hrec := ih (b / 2) hlt (c / 2)
      have hdiv2_tb : ∀ z i : Nat, (z / 2).testBit i = z.testBit (i + 1) := by
        intro z i
        rw [← Nat.pow_one 2, Nat.testBit_div_two_pow]
      have hxd : (b ^^^ c) / 2 = (b / 2) ^^^ (c / 2) := by
        apply Nat.eq_of_testBit_eq; intro i
        rw [hdiv2_tb, Nat.testBit_xor, Nat.testBit_xor, hdiv2_tb, hdiv2_tb]
      have hxm : (b ^^^ c) % 2 = (b % 2) ^^^ (c % 2) := by
        simpa [Nat.pow_one] using xor_mod_two_pow b c 1
      rw [clmul_expand a (b ^^^ c), clmul_expand a b, clmul_expand a c,
          hxd, hxm, hrec, ← two_mul_xor_two_mul]
      have hb2 : b % 2 < 2 := Nat.mod_lt b (by decide)
      have hc2 : c % 2 < 2 := Nat.mod_lt c (by decide)
      have hpar : (if (b % 2) ^^^ (c % 2) = 1 then a else 0) =
          (if b % 2 = 1 then a else 0) ^^^ (if c % 2 = 1 then a else 0) := by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hb2 with hb0 | hb1 <;>
        rcases Nat.lt_succ_iff_lt_or_eq.mp hc2 with hc0 | hc1
        · have hb0' : b % 2 = 0 := by omega
          have hc0' : c % 2 = 0 := by omega
          rw [hb0', hc0']; simp
        · have hb0' : b % 2 = 0 := by omega
          rw [hb0', hc1]; simp
        · have hc0' : c % 2 = 0 := by omega
          rw [hb1, hc0']; simp
        · rw [hb1, hc1]; simp
      rw [hpar]
      apply Nat.eq_of_testBit_eq; intro i
      simp only [Nat.testBit_xor]
      cases (if b % 2 = 1 then a else 0).testBit i <;>
      cases (if c % 2 = 1 then a else 0).testBit i <;>
      cases (2 * clmul a (b / 2)).testBit i <;>
      cases (2 * clmul a (c / 2)).testBit i <;> rfl

theorem clmul_xor_left (a b c : Nat) :
    clmul (a ^^^ b) c = clmul a c ^^^ clmul b c := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
    by_cases hc : c = 0
    · subst hc; simp [clmul_zero_right]
    · have hlt : c / 2 < c := Nat.div_lt_self (Nat.pos_of_ne_zero hc) (by decide)
      have hrec := ih (c / 2) hlt
      rw [clmul_expand (a ^^^ b) c, clmul_expand a c, clmul_expand b c, hrec, ← two_mul_xor_two_mul]
      by_cases hodd : c % 2 = 1
      · simp only [hodd, ↓reduceIte]
        apply Nat.eq_of_testBit_eq; intro i
        simp only [Nat.testBit_xor]
        cases a.testBit i <;> cases b.testBit i <;>
        cases (2 * clmul a (c / 2)).testBit i <;> cases (2 * clmul b (c / 2)).testBit i <;> rfl
      · simp only [hodd, ↓reduceIte, Nat.zero_xor]

theorem clmul_comm (a b : Nat) : clmul a b = clmul b a := by
  induction a using Nat.strongRecOn with
  | ind a ih =>
    by_cases ha : a = 0
    · subst ha; rw [clmul_zero_left, clmul_zero_right]
    · have hlt : a / 2 < a := Nat.div_lt_self (Nat.pos_of_ne_zero ha) (by decide)
      have hrec := ih (a / 2) hlt
      by_cases hodd : a % 2 = 1
      · have ha_xor : a = 1 ^^^ (2 * (a / 2)) := by
          have := add_eq_xor_of_lt_pow2 (a := 1) (b := a / 2) (r := 1) (by decide)
          simp only [Nat.pow_one] at this
          omega
        have ha2 : a = 2 * (a / 2) + 1 := by omega
        calc clmul a b
            = clmul (1 ^^^ (2 * (a / 2))) b := by rw [← ha_xor]
          _ = clmul 1 b ^^^ clmul (2 * (a / 2)) b := clmul_xor_left _ _ _
          _ = b ^^^ (2 * clmul (a / 2) b) := by rw [clmul_one_left, clmul_two_mul_left]
          _ = b ^^^ (2 * clmul b (a / 2)) := by rw [hrec]
          _ = clmul b (2 * (a / 2) + 1) := (clmul_two_mul_add_one_right b (a / 2)).symm
          _ = clmul b a := by rw [← ha2]
      · have ha2 : a = 2 * (a / 2) := by omega
        calc clmul a b
            = clmul (2 * (a / 2)) b := by rw [← ha2]
          _ = 2 * clmul (a / 2) b := clmul_two_mul_left _ _
          _ = 2 * clmul b (a / 2) := by rw [hrec]
          _ = clmul b (2 * (a / 2)) := (clmul_two_mul_right b (a / 2)).symm
          _ = clmul b a := by rw [← ha2]

theorem clmul_assoc (a b c : Nat) : clmul (clmul a b) c = clmul a (clmul b c) := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
    by_cases hc : c = 0
    · subst hc; simp [clmul_zero_right]
    · have hlt : c / 2 < c := Nat.div_lt_self (Nat.pos_of_ne_zero hc) (by decide)
      have hrec := ih (c / 2) hlt
      rw [clmul_expand (clmul a b) c, clmul_expand b c, clmul_xor_right, clmul_two_mul_right, hrec]
      by_cases hodd : c % 2 = 1
      · simp [hodd]
      · simp [hodd, clmul_zero_right]

theorem clmul_mod_two_pow_right {a b1 b2 w : Nat} (h : b1 % 2 ^ w = b2 % 2 ^ w) :
    clmul a b1 % 2 ^ w = clmul a b2 % 2 ^ w := by
  induction w generalizing b1 b2 with
  | zero => simp [Nat.pow_zero, Nat.mod_one]
  | succ w ih =>
    have hm2 : b1 % 2 = b2 % 2 := by
      have h1 : (b1 % 2 ^ (w + 1)) % 2 = b1 % 2 := by
        rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul_right_mod]
      have h2 : (b2 % 2 ^ (w + 1)) % 2 = b2 % 2 := by
        rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul_right_mod]
      rw [← h1, ← h2, h]
    have hd : (b1 / 2) % 2 ^ w = (b2 / 2) % 2 ^ w := by
      have h1 : (b1 % 2 ^ (w + 1)) / 2 = (b1 / 2) % 2 ^ w := by
        rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul_right_div_self]
      have h2 : (b2 % 2 ^ (w + 1)) / 2 = (b2 / 2) % 2 ^ w := by
        rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul_right_div_self]
      rw [← h1, ← h2, h]
    have hrec := ih hd
    have h2rec : (2 * clmul a (b1 / 2)) % 2 ^ (w + 1) = (2 * clmul a (b2 / 2)) % 2 ^ (w + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ w) 2, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, hrec]
    rw [clmul_expand a b1, clmul_expand a b2, xor_mod_two_pow, xor_mod_two_pow, hm2, h2rec]

theorem clmul_mod_two_pow_left {a1 a2 b w : Nat} (h : a1 % 2 ^ w = a2 % 2 ^ w) :
    clmul a1 b % 2 ^ w = clmul a2 b % 2 ^ w := by
  rw [clmul_comm a1 b, clmul_comm a2 b]
  exact clmul_mod_two_pow_right h

theorem clmul_mod_two (a b : Nat) : clmul a b % 2 = (a % 2) * (b % 2) := by
  have h1 : clmul a b % 2 ^ 1 = clmul (a % 2) (b % 2) % 2 ^ 1 := by
    rw [clmul_mod_two_pow_left (a2 := a % 2) (by simp),
        clmul_mod_two_pow_right (b2 := b % 2) (by simp)]
  simp only [Nat.pow_one] at h1
  rw [h1]
  have ha : a % 2 < 2 := Nat.mod_lt a (by decide)
  have hb : b % 2 < 2 := Nat.mod_lt b (by decide)
  rcases Nat.lt_succ_iff_lt_or_eq.mp ha with ha0 | ha1 <;>
  rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hb0 | hb1
  · have ha0' : a % 2 = 0 := by omega
    have hb0' : b % 2 = 0 := by omega
    rw [ha0', hb0']; decide
  · have ha0' : a % 2 = 0 := by omega
    rw [ha0', hb1]; decide
  · have hb0' : b % 2 = 0 := by omega
    rw [ha1, hb0']; decide
  · rw [ha1, hb1]; decide

-- Properties of spread and Frobenius identity
theorem spread_zero (r : Nat) : spread r 0 = 0 := rfl

theorem spread_one (r : Nat) : spread r 1 = 1 := by
  simp [spread, spreadAux]

theorem spread_two_mul (r n : Nat) : spread r (2 * n) = 2 ^ r * spread r n := by
  by_cases hn : n = 0
  · subst hn; simp [spread_zero]
  · rw [spread_unfold (by omega : 2 * n ≠ 0)]
    have h1 : (2 * n) % 2 = 0 := by omega
    have h2 : (2 * n) / 2 = n := by omega
    rw [h1, h2, Nat.zero_add]

theorem spread_two_mul_add_one (r n : Nat) :
    spread r (2 * n + 1) = 1 + 2 ^ r * spread r n := by
  rw [spread_unfold (by omega : 2 * n + 1 ≠ 0)]
  have h1 : (2 * n + 1) % 2 = 1 := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  rw [h1, h2]

theorem spread_mod_two_pow {r n : Nat} (hr : 1 ≤ r) :
    spread r n % 2 ^ r = n % 2 := by
  by_cases hn : n = 0
  · subst hn; simp [spread_zero]
  · rw [spread_unfold hn, Nat.add_mul_mod_self_left]
    have hlt : n % 2 < 2 ^ r := by
      have h2 : 2 ≤ 2 ^ r := Nat.pow_le_pow_right (by decide : 0 < 2) hr
      have hm : n % 2 < 2 := Nat.mod_lt n (by decide)
      omega
    exact Nat.mod_eq_of_lt hlt

/-- Silicon Frobenius Law: `clmul a a = spread 2 a` for all `a : Nat`. -/
theorem clmul_self (a : Nat) : clmul a a = spread 2 a := by
  induction a using Nat.strongRecOn with
  | ind a ih =>
    by_cases ha : a = 0
    · subst ha; rw [clmul_zero_right, spread_zero]
    · have hlt : a / 2 < a := Nat.div_lt_self (Nat.pos_of_ne_zero ha) (by decide)
      have hrec := ih (a / 2) hlt
      by_cases hodd : a % 2 = 1
      · have ha_xor : a = 1 ^^^ (2 * (a / 2)) := by
          have := add_eq_xor_of_lt_pow2 (a := 1) (b := a / 2) (r := 1) (by decide)
          simp only [Nat.pow_one] at this
          omega
        have ha2 : a = 2 * (a / 2) + 1 := by omega
        calc clmul a a
            = clmul (1 ^^^ 2 * (a / 2)) (1 ^^^ 2 * (a / 2)) := by rw [← ha_xor]
          _ = (clmul 1 1 ^^^ clmul 1 (2 * (a / 2))) ^^^
              (clmul (2 * (a / 2)) 1 ^^^ clmul (2 * (a / 2)) (2 * (a / 2))) := by
              rw [clmul_xor_left, clmul_xor_right, clmul_xor_right]
          _ = 1 ^^^ (4 * clmul (a / 2) (a / 2)) := by
              rw [clmul_one_left, clmul_one_right, clmul_two_mul_left, clmul_two_mul_right,
                  clmul_one_left, clmul_two_mul_right]
              have h4 : 2 * (2 * clmul (a / 2) (a / 2)) = 4 * clmul (a / 2) (a / 2) := by omega
              rw [h4]
              apply Nat.eq_of_testBit_eq; intro i
              simp only [Nat.testBit_xor]
              cases (1 : Nat).testBit i <;>
              cases (2 * (a / 2)).testBit i <;>
              cases (4 * clmul (a / 2) (a / 2)).testBit i <;> rfl
          _ = 1 + 4 * spread 2 (a / 2) := by
              rw [hrec]
              exact (add_eq_xor_of_lt_pow2 (a := 1) (b := spread 2 (a / 2)) (r := 2) (by decide)).symm
          _ = spread 2 (2 * (a / 2) + 1) := (spread_two_mul_add_one 2 (a / 2)).symm
          _ = spread 2 a := by rw [← ha2]
      · have ha2 : a = 2 * (a / 2) := by omega
        calc clmul a a
            = clmul (2 * (a / 2)) (2 * (a / 2)) := by rw [← ha2]
          _ = 2 * (2 * clmul (a / 2) (a / 2)) := by rw [clmul_two_mul_left, clmul_two_mul_right]
          _ = 4 * spread 2 (a / 2) := by rw [hrec]; omega
          _ = spread 2 (2 * (a / 2)) := (spread_two_mul 2 (a / 2)).symm
          _ = spread 2 a := by rw [← ha2]

theorem spread_comp (r s n : Nat) (_hr : 1 ≤ r) (hs : 1 ≤ s) :
    spread r (spread s n) = spread (r * s) n := by
  -- Helper: spread r (2^t * m) = 2^(r*t) * spread r m
  have hpow : ∀ t m : Nat, spread r (2 ^ t * m) = 2 ^ (r * t) * spread r m := by
    intro t
    induction t with
    | zero => intro m; simp
    | succ t iht =>
      intro m
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ t) 2, Nat.mul_assoc,
          spread_two_mul, iht, ← Nat.mul_assoc, ← Nat.pow_add]
      have : r + r * t = r * (t + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      rw [this]
  -- Helper: spread r (1 + 2^s * m) = 1 + 2^(r*s) * spread r m for s >= 1
  have hpow1 : ∀ m : Nat, spread r (1 + 2 ^ s * m) = 1 + 2 ^ (r * s) * spread r m := by
    intro m
    have hs' : s = (s - 1) + 1 := (Nat.sub_add_cancel hs).symm
    have h2s : 2 ^ s = 2 * 2 ^ (s - 1) := by
      have h1 : 2 ^ s = 2 ^ ((s - 1) + 1) := congrArg (2 ^ ·) hs'
      rw [h1, Nat.pow_succ, Nat.mul_comm]
    rw [spread_unfold (by omega : 1 + 2 ^ s * m ≠ 0)]
    have hm1 : (1 + 2 ^ s * m) % 2 = 1 := by rw [h2s, Nat.mul_assoc]; omega
    have hd1 : (1 + 2 ^ s * m) / 2 = 2 ^ (s - 1) * m := by
      rw [h2s, Nat.mul_assoc, Nat.add_comm 1, Nat.mul_add_div (by decide : 0 < 2)]
      simp
    rw [hm1, hd1, hpow (s - 1) m, ← Nat.mul_assoc, ← Nat.pow_add]
    have : r + r * (s - 1) = r * s := by
      have hs1 : 1 + (s - 1) = s := by omega
      calc r + r * (s - 1) = r * (1 + (s - 1)) := by rw [Nat.mul_add, Nat.mul_one]
        _ = r * s := by rw [hs1]
    rw [this]
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n = 0
    · subst hn; simp [spread_zero]
    · have hlt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)
      have hrec := ih (n / 2) hlt
      by_cases hodd : n % 2 = 1
      · have hn' : n = 2 * (n / 2) + 1 := by omega
        calc spread r (spread s n)
            = spread r (spread s (2 * (n / 2) + 1)) := by rw [← hn']
          _ = spread r (1 + 2 ^ s * spread s (n / 2)) := by rw [spread_two_mul_add_one]
          _ = 1 + 2 ^ (r * s) * spread r (spread s (n / 2)) := hpow1 _
          _ = 1 + 2 ^ (r * s) * spread (r * s) (n / 2) := by rw [hrec]
          _ = spread (r * s) (2 * (n / 2) + 1) := (spread_two_mul_add_one _ _).symm
          _ = spread (r * s) n := by rw [← hn']
      · have hn' : n = 2 * (n / 2) := by omega
        calc spread r (spread s n)
            = spread r (spread s (2 * (n / 2))) := by rw [← hn']
          _ = spread r (2 ^ s * spread s (n / 2)) := by rw [spread_two_mul]
          _ = 2 ^ (r * s) * spread r (spread s (n / 2)) := hpow s _
          _ = 2 ^ (r * s) * spread (r * s) (n / 2) := by rw [hrec]
          _ = spread (r * s) (2 * (n / 2)) := (spread_two_mul _ _).symm
          _ = spread (r * s) n := by rw [← hn']

-- Properties of clpow
theorem clpow_zero (a : Nat) : clpow a 0 = 1 := rfl

theorem clpow_one (a : Nat) : clpow a 1 = a := by
  simp [clpow, clmul_one_left]

theorem clpow_succ_left (a k : Nat) : clpow a (k + 1) = clmul a (clpow a k) := by
  rw [clpow, clmul_comm]

theorem clpow_add (a m n : Nat) :
    clpow a (m + n) = clmul (clpow a m) (clpow a n) := by
  induction n with
  | zero => simp [clpow, clmul_one_right]
  | succ n ih =>
    rw [Nat.add_succ, clpow, clpow, ih, clmul_assoc]

theorem clpow_two_mul (a k : Nat) :
    clpow a (2 * k) = spread 2 (clpow a k) := by
  have : 2 * k = k + k := by omega
  rw [this, clpow_add, clmul_self]

theorem clpow_two_pow_mul (a e m : Nat) :
    clpow a (2 ^ e * m) = spread (2 ^ e) (clpow a m) := by
  induction e with
  | zero =>
    simp only [Nat.pow_zero, Nat.one_mul]
    have hsp1 : ∀ x : Nat, spread 1 x = x := by
      intro x
      induction x using Nat.strongRecOn with
      | ind x ih =>
        by_cases hx : x = 0
        · subst hx; exact spread_zero 1
        · rw [spread_unfold hx, ih (x / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hx) (by decide))]
          simp only [Nat.pow_one]
          omega
    exact (hsp1 _).symm
  | succ e ih =>
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ e) 2, Nat.mul_assoc, clpow_two_mul, ih,
        spread_comp 2 (2 ^ e) _ (by decide) (Nat.two_pow_pos e), Nat.mul_comm 2 (2 ^ e)]

theorem clpow_odd_of_odd {a : Nat} (ha : a % 2 = 1) (k : Nat) :
    clpow a k % 2 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [clpow, clmul_mod_two, ih, ha]

-- Dominance inequality clmul <= mul and strict inequality clpow < pow
theorem clmul_le_mul (a b : Nat) : clmul a b ≤ a * b := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    by_cases hb : b = 0
    · subst hb; simp [clmul_zero_right]
    · have hlt : b / 2 < b := Nat.div_lt_self (Nat.pos_of_ne_zero hb) (by decide)
      have hrec := ih (b / 2) hlt
      rw [clmul_expand a b]
      have h1 := xor_le_add (if b % 2 = 1 then a else 0) (2 * clmul a (b / 2))
      by_cases hodd : b % 2 = 1
      · simp only [hodd, ↓reduceIte] at h1 ⊢
        have hb' : b = 2 * (b / 2) + 1 := by omega
        have h2 : a * b = a + 2 * (a * (b / 2)) := by
          calc a * b = a * (2 * (b / 2) + 1) := by rw [← hb']
            _ = a * (2 * (b / 2)) + a := by rw [Nat.mul_add, Nat.mul_one]
            _ = a + 2 * (a * (b / 2)) := by
                rw [← Nat.mul_assoc, Nat.mul_comm a 2, Nat.mul_assoc, Nat.add_comm]
        omega
      · simp only [hodd, ↓reduceIte, Nat.zero_xor]
        have hb' : b = 2 * (b / 2) := by omega
        have h2 : a * b = 2 * (a * (b / 2)) := by
          calc a * b = a * (2 * (b / 2)) := by rw [← hb']
            _ = 2 * (a * (b / 2)) := by rw [← Nat.mul_assoc, Nat.mul_comm a 2, Nat.mul_assoc]
        omega

theorem clpow_le_pow (a k : Nat) : clpow a k ≤ a ^ k := by
  induction k with
  | zero => simp [clpow]
  | succ k ih =>
    rw [clpow, Nat.pow_succ]
    exact Nat.le_trans (clmul_le_mul (clpow a k) a) (Nat.mul_le_mul_right a ih)

theorem clpow_two_lt_sq {a : Nat} (ha_odd : a % 2 = 1) (ha3 : 3 ≤ a) :
    clpow a 2 < a ^ 2 := by
  have h2 : clpow a 2 = spread 2 a := by
    have := clpow_two_mul a 1
    rw [Nat.mul_one, clpow_one] at this
    exact this
  rw [h2]
  have ha' : a = 2 * (a / 2) + 1 := by omega
  have hq : 1 ≤ a / 2 := by omega
  have hsp : spread 2 a = 1 + 4 * spread 2 (a / 2) := by
    calc spread 2 a = spread 2 (2 * (a / 2) + 1) := by rw [← ha']
      _ = 1 + 4 * spread 2 (a / 2) := spread_two_mul_add_one 2 (a / 2)
  rw [hsp, ← clmul_self (a / 2)]
  have hle : clmul (a / 2) (a / 2) ≤ (a / 2) * (a / 2) := clmul_le_mul _ _
  have hsq : a ^ 2 = 4 * ((a / 2) * (a / 2)) + 4 * (a / 2) + 1 := by
    rw [Nat.pow_two]
    have h4 : (2 * (a / 2)) * (2 * (a / 2)) = 4 * ((a / 2) * (a / 2)) := by
      calc (2 * (a / 2)) * (2 * (a / 2))
          = 2 * ((a / 2) * (2 * (a / 2))) := Nat.mul_assoc _ _ _
        _ = 2 * ((2 * (a / 2)) * (a / 2)) := by rw [← Nat.mul_assoc (a / 2), Nat.mul_comm (a / 2) 2]
        _ = 2 * (2 * ((a / 2) * (a / 2))) := by rw [Nat.mul_assoc]
        _ = 4 * ((a / 2) * (a / 2)) := by rw [← Nat.mul_assoc]
    calc a * a = (2 * (a / 2) + 1) * (2 * (a / 2) + 1) := by rw [← ha']
      _ = 4 * ((a / 2) * (a / 2)) + 4 * (a / 2) + 1 := by
          rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, h4]; omega
  omega

theorem clpow_lt_pow {a k : Nat} (ha_odd : a % 2 = 1) (ha3 : 3 ≤ a) (hk : 2 ≤ k) :
    clpow a k < a ^ k := by
  have hk' : k = 2 + (k - 2) := (Nat.add_sub_of_le hk).symm
  rw [hk', clpow_add, Nat.pow_add]
  have hpos : 0 < clpow a (k - 2) := by
    have := clpow_odd_of_odd ha_odd (k - 2); omega
  have h1 : clmul (clpow a 2) (clpow a (k - 2)) ≤ clpow a 2 * clpow a (k - 2) := clmul_le_mul _ _
  have h2 : clpow a 2 * clpow a (k - 2) < a ^ 2 * clpow a (k - 2) :=
    Nat.mul_lt_mul_of_pos_right (clpow_two_lt_sq ha_odd ha3) hpos
  have h3 : a ^ 2 * clpow a (k - 2) ≤ a ^ 2 * a ^ (k - 2) :=
    Nat.mul_le_mul_left (a ^ 2) (clpow_le_pow a (k - 2))
  omega

/-- Zero-Carry Theorem: multiplying a `spread r y` by any `B < 2^r` produces zero carries. -/
theorem clmul_spread_eq_mul {B r : Nat} (hB : B < 2 ^ r) (y : Nat) :
    clmul B (spread r y) = B * spread r y := by
  by_cases hB0 : B = 0
  · subst hB0; simp [clmul_zero_left]
  induction y using Nat.strongRecOn with
  | ind y ih =>
    by_cases hy : y = 0
    · subst hy; simp [spread_zero, clmul_zero_right]
    · have hlt : y / 2 < y := Nat.div_lt_self (Nat.pos_of_ne_zero hy) (by decide)
      have hrec := ih (y / 2) hlt
      by_cases hodd : y % 2 = 1
      · have hy' : y = 2 * (y / 2) + 1 := by omega
        have h1lt : 1 < 2 ^ r := by omega
        calc clmul B (spread r y)
            = clmul B (spread r (2 * (y / 2) + 1)) := by rw [← hy']
          _ = clmul B (1 + 2 ^ r * spread r (y / 2)) := by rw [spread_two_mul_add_one]
          _ = clmul B (1 ^^^ (2 ^ r * spread r (y / 2))) := by rw [add_eq_xor_of_lt_pow2 h1lt]
          _ = B ^^^ (2 ^ r * clmul B (spread r (y / 2))) := by
              rw [clmul_xor_right, clmul_one_right, clmul_pow2_mul_right]
          _ = B ^^^ (2 ^ r * (B * spread r (y / 2))) := by rw [hrec]
          _ = B + 2 ^ r * (B * spread r (y / 2)) := (add_eq_xor_of_lt_pow2 hB).symm
          _ = B * (1 + 2 ^ r * spread r (y / 2)) := by
              rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ r) B, Nat.mul_assoc, Nat.mul_add, Nat.mul_one]
          _ = B * spread r (2 * (y / 2) + 1) := by rw [← spread_two_mul_add_one]
          _ = B * spread r y := by rw [← hy']
      · have hy' : y = 2 * (y / 2) := by omega
        calc clmul B (spread r y)
            = clmul B (spread r (2 * (y / 2))) := by rw [← hy']
          _ = clmul B (2 ^ r * spread r (y / 2)) := by rw [spread_two_mul]
          _ = 2 ^ r * clmul B (spread r (y / 2)) := clmul_pow2_mul_right _ _ _
          _ = 2 ^ r * (B * spread r (y / 2)) := by rw [hrec]
          _ = B * (2 ^ r * spread r (y / 2)) := by
              rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ r) B, Nat.mul_assoc]
          _ = B * spread r (2 * (y / 2)) := by rw [← spread_two_mul]
          _ = B * spread r y := by rw [← hy']

-- Carryless Lifting-The-Exponent (Exponential 2-Adic Valuation Law)
theorem spread_mod_two_pow_shift {R k u : Nat} (hR : 1 ≤ R)
    (hu : u % 2 ^ (k + 1) = 2 ^ k) :
    spread R u % 2 ^ (R * k + 1) = 2 ^ (R * k) := by
  induction k generalizing u with
  | zero =>
    have hum : u % 2 = 1 := by simpa using hu
    have h1 := spread_mod_two_pow (r := R) (n := u) hR
    have h2 : (spread R u % 2 ^ R) % 2 = spread R u % 2 := by
      have hR' : R = (R - 1) + 1 := (Nat.sub_add_cancel hR).symm
      have hpow : 2 ^ R = 2 * 2 ^ (R - 1) := by
        have := congrArg (2 ^ ·) hR'; rw [this, Nat.pow_succ, Nat.mul_comm]
      rw [hpow, Nat.mod_mul_right_mod]
    rw [Nat.mul_zero, Nat.zero_add, Nat.pow_one, Nat.pow_zero, ← h2, h1, hum]
  | succ k ihk =>
    have hum : u % 2 = 0 := by
      have h1 : (u % 2 ^ (k + 2)) % 2 = u % 2 := by
        rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul_right_mod]
      rw [← h1, hu, Nat.pow_succ]
      omega
    have hud : (u / 2) % 2 ^ (k + 1) = 2 ^ k := by
      have h1 : (u % 2 ^ (k + 2)) / 2 = (u / 2) % 2 ^ (k + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul_right_div_self]
      rw [← h1, hu, Nat.pow_succ]
      omega
    have hrec := ihk hud
    have hu' : u = 2 * (u / 2) := by omega
    have hsp : spread R u = 2 ^ R * spread R (u / 2) := by
      calc spread R u = spread R (2 * (u / 2)) := by rw [← hu']
        _ = 2 ^ R * spread R (u / 2) := spread_two_mul R (u / 2)
    rw [hsp]
    have hpow1 : R * (k + 1) + 1 = R + (R * k + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
    have hpow2 : R * (k + 1) = R + R * k := by rw [Nat.mul_add, Nat.mul_one]; omega
    rw [hpow1, hpow2, Nat.pow_add 2 R (R * k + 1), Nat.pow_add 2 R (R * k), Nat.mul_mod_mul_left, hrec]

theorem spread_mod_two_pow_exact {R r z : Nat} (hR : 1 ≤ R) (hr : 1 ≤ r)
    (hz : z % 2 ^ (r + 1) = 1 + 2 ^ r) :
    spread R z % 2 ^ (R * r + 1) = 1 + 2 ^ (R * r) := by
  have hr' : r = (r - 1) + 1 := (Nat.sub_add_cancel hr).symm
  let r' := r - 1
  have hz' : z % 2 ^ (r' + 2) = 1 + 2 ^ (r' + 1) := by
    have : r + 1 = r' + 2 := by omega
    rw [← this, ← hr']; exact hz
  have hzm : z % 2 = 1 := by
    have h1 : (z % 2 ^ (r' + 2)) % 2 = z % 2 := by
      rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul_right_mod]
    rw [← h1, hz', Nat.pow_succ]
    omega
  have hzne : z ≠ 0 := by omega
  have hzd : (z / 2) % 2 ^ (r' + 1) = 2 ^ r' := by
    have h1 : (z % 2 ^ (r' + 2)) / 2 = (z / 2) % 2 ^ (r' + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul_right_div_self]
    rw [← h1, hz', Nat.pow_succ]
    omega
  have hsp := spread_mod_two_pow_shift hR hzd
  rw [spread_unfold hzne, hzm]
  have hpow1 : R * r + 1 = R + (R * r' + 1) := by
    have : R * r = R * (r' + 1) := congrArg (R * ·) hr'
    rw [this, Nat.mul_add, Nat.mul_one]; omega
  have hpow2 : R * r = R + R * r' := by
    have : R * r = R * (r' + 1) := congrArg (R * ·) hr'
    rw [this, Nat.mul_add, Nat.mul_one]; omega
  rw [hpow1, hpow2, Nat.pow_add 2 R (R * r' + 1), Nat.pow_add 2 R (R * r')]
  have hdiv_mod := Nat.div_add_mod (spread R (z / 2)) (2 ^ (R * r' + 1))
  have heq : 1 + 2 ^ R * spread R (z / 2) =
      (1 + 2 ^ R * 2 ^ (R * r')) +
      (2 ^ R * 2 ^ (R * r' + 1)) * (spread R (z / 2) / 2 ^ (R * r' + 1)) := by
    have h1 : spread R (z / 2) =
        2 ^ (R * r' + 1) * (spread R (z / 2) / 2 ^ (R * r' + 1)) + 2 ^ (R * r') := by
      rw [← hsp]; exact hdiv_mod.symm
    calc 1 + 2 ^ R * spread R (z / 2)
        = 1 + 2 ^ R * (2 ^ (R * r' + 1) * (spread R (z / 2) / 2 ^ (R * r' + 1)) + 2 ^ (R * r')) := by rw [← h1]
      _ = (1 + 2 ^ R * 2 ^ (R * r')) +
          (2 ^ R * 2 ^ (R * r' + 1)) * (spread R (z / 2) / 2 ^ (R * r' + 1)) := by
          rw [Nat.mul_add, ← Nat.mul_assoc]; omega
  have hlt : 1 + 2 ^ R * 2 ^ (R * r') < 2 ^ R * 2 ^ (R * r' + 1) := by
    rw [Nat.pow_succ]
    have hposR : 2 ≤ 2 ^ R := Nat.pow_le_pow_right (by decide : 0 < 2) hR
    have hposK : 1 ≤ 2 ^ (R * r') := Nat.two_pow_pos _
    have hmul : 2 ^ R * (2 ^ (R * r') * 2) = 2 ^ R * 2 ^ (R * r') + 2 ^ R * 2 ^ (R * r') := by
      rw [Nat.mul_two, Nat.mul_add]
    have hge : 2 ≤ 2 ^ R * 2 ^ (R * r') := Nat.le_trans hposR (Nat.le_mul_of_pos_right _ hposK)
    omega
  rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

theorem clpow_mod_odd {a r : Nat} (hr : 1 ≤ r)
    (ha : a % 2 ^ (r + 1) = 1 + 2 ^ r) (m : Nat) :
    clpow a m % 2 ^ (r + 1) = if m % 2 = 1 then 1 + 2 ^ r else 1 := by
  have hlt_1r : 1 + 2 ^ r < 2 ^ (r + 1) := by rw [Nat.pow_succ]; omega
  have hlt_1 : 1 < 2 ^ (r + 1) := by
    have : 2 ≤ 2 ^ (r + 1) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ r + 1)
    omega
  induction m with
  | zero =>
    simp [clpow_zero, Nat.mod_eq_of_lt hlt_1]
  | succ m ih =>
    rw [clpow_succ_left]
    have ha' : a % 2 ^ (r + 1) = (1 + 2 ^ r) % 2 ^ (r + 1) := by
      rw [ha, Nat.mod_eq_of_lt hlt_1r]
    have hih' : clpow a m % 2 ^ (r + 1) =
        (if m % 2 = 1 then 1 + 2 ^ r else 1) % 2 ^ (r + 1) := by
      rw [ih]
      by_cases hm : m % 2 = 1
      · simp [hm, Nat.mod_eq_of_lt hlt_1r]
      · simp [hm, Nat.mod_eq_of_lt hlt_1]
    have hstep : clmul a (clpow a m) % 2 ^ (r + 1) =
        clmul (1 + 2 ^ r) (if m % 2 = 1 then 1 + 2 ^ r else 1) % 2 ^ (r + 1) := by
      rw [clmul_mod_two_pow_left ha', clmul_mod_two_pow_right hih']
    rw [hstep]
    have h1lt : 1 < 2 ^ r := by
      have : 2 ≤ 2 ^ r := Nat.pow_le_pow_right (by decide : 0 < 2) hr
      omega
    by_cases hm : m % 2 = 1
    · have hm1 : ¬ ((m + 1) % 2 = 1) := by omega
      simp only [hm, hm1, ↓reduceIte]
      have hsq : clmul (1 + 2 ^ r) (1 + 2 ^ r) = 1 + 2 ^ (2 * r) := by
        have hxor1 : 1 + 2 ^ r = 1 ^^^ 2 ^ r := by
          simpa using add_eq_xor_of_lt_pow2 (a := 1) (b := 1) (r := r) h1lt
        rw [hxor1, clmul_xor_left, clmul_xor_right, clmul_xor_right,
            clmul_one_left, clmul_one_right, clmul_one_left]
        have h2r : clmul (2 ^ r) (2 ^ r) = 2 ^ (2 * r) := by
          have : clmul (2 ^ r) (2 ^ r * 1) = 2 ^ r * clmul (2 ^ r) 1 := clmul_pow2_mul_right _ _ _
          rw [Nat.mul_one, clmul_one_right, ← Nat.pow_add] at this
          have h2r' : r + r = 2 * r := by omega
          rw [h2r'] at this
          exact this
        rw [h2r]
        have hcancel : (1 ^^^ 2 ^ r) ^^^ (2 ^ r ^^^ 2 ^ (2 * r)) = 1 ^^^ 2 ^ (2 * r) := by
          apply Nat.eq_of_testBit_eq; intro i
          simp only [Nat.testBit_xor]
          cases (1 : Nat).testBit i <;> cases (2 ^ r).testBit i <;>
          cases (2 ^ (2 * r)).testBit i <;> rfl
        rw [hcancel]
        have h1lt2 : 1 < 2 ^ (2 * r) := by
          have : 2 ≤ 2 ^ (2 * r) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ 2 * r)
          omega
        simpa using (add_eq_xor_of_lt_pow2 (a := 1) (b := 1) (r := 2 * r) h1lt2).symm
      rw [hsq]
      have hge : r + 1 ≤ 2 * r := by omega
      have hdvd : 2 ^ (r + 1) ∣ 2 ^ (2 * r) := by
        have heq : 2 * r = (r + 1) + (2 * r - (r + 1)) := (Nat.add_sub_of_le hge).symm
        exact ⟨2 ^ (2 * r - (r + 1)), by rw [← Nat.pow_add, ← heq]⟩
      rcases hdvd with ⟨q, hq⟩
      rw [hq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt_1]
    · have hm1 : (m + 1) % 2 = 1 := by omega
      simp only [hm, hm1, ↓reduceIte, clmul_one_right, Nat.mod_eq_of_lt hlt_1r]

theorem exactPow2_sub_one_iff_mod {k n : Nat} (hk : 1 ≤ k) :
    exactPow2 k ((n : Int) - 1) ↔ n % 2 ^ (k + 1) = 1 + 2 ^ k := by
  constructor
  · intro hex
    rw [exactPow2_iff_odd_mul] at hex
    rcases hex with ⟨q, hq, hodd⟩
    have h2k : 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
    have hn_ge : 1 ≤ n := by
      cases n with
      | zero =>
        exfalso
        have habs : ((-1 : Int)).natAbs = 2 ^ k * q.natAbs := by
          have := congrArg Int.natAbs hq
          rw [Int.natAbs_mul] at this
          simpa using this
        have hq0 : q.natAbs ≠ 0 := by intro h; rw [h] at habs; simp at habs
        have hge : 2 ≤ 2 ^ k * q.natAbs :=
          Nat.le_trans h2k (Nat.le_mul_of_pos_right (2 ^ k) (by omega))
        simp at habs
        omega
      | succ _ => omega
    have hq_nonneg : 0 ≤ q := by
      have hpos := two_pow_int_pos k
      by_cases h0 : 0 ≤ q
      · exact h0
      · exfalso
        have hqle : q ≤ -1 := by omega
        have hmul := Int.mul_le_mul_of_nonneg_left hqle (Int.le_of_lt hpos)
        simp only [Int.mul_neg, Int.mul_one] at hmul
        omega
    let qn := q.toNat
    have hqn : (qn : Int) = q := Int.toNat_of_nonneg hq_nonneg
    have hqn_odd : qn % 2 = 1 := by omega
    have hn_eq : n = 1 + 2 ^ k * qn := by
      have h1 : ((n : Int) - 1) = ((2 ^ k * qn : Nat) : Int) := by
        rw [hq, ← hqn]; push_cast; rfl
      omega
    rw [hn_eq, Nat.pow_succ]
    have hq2 : qn = 2 * (qn / 2) + 1 := by omega
    have hlt : 1 + 2 ^ k < 2 ^ k * 2 := by omega
    have heq : 1 + 2 ^ k * qn = (1 + 2 ^ k) + (2 ^ k * 2) * (qn / 2) := by
      calc 1 + 2 ^ k * qn
          = 1 + 2 ^ k * (2 * (qn / 2) + 1) := by rw [← hq2]
        _ = 1 + (2 ^ k * (2 * (qn / 2)) + 2 ^ k) := by rw [Nat.mul_add, Nat.mul_one]
        _ = (1 + 2 ^ k) + (2 ^ k * 2) * (qn / 2) := by rw [← Nat.mul_assoc]; omega
    rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · intro hmod
    let qn := n / 2 ^ (k + 1)
    have hdiv : 2 ^ (k + 1) * qn + n % 2 ^ (k + 1) = n := Nat.div_add_mod n (2 ^ (k + 1))
    rw [exactPow2_iff_odd_mul]
    refine ⟨(2 * (qn : Int) + 1), ?_, by omega⟩
    have hn : n = 2 ^ (k + 1) * qn + (1 + 2 ^ k) := by
      rw [← hmod]; exact hdiv.symm
    have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
    have h1 : (n : Int) - 1 = ((2 ^ k : Nat) : Int) * (2 * (qn : Int) + 1) := by
      rw [hn, hpow]
      push_cast
      rw [Int.mul_add, Int.mul_one, ← Int.mul_assoc]
      omega
    exact h1

/-- Carryless Lifting-The-Exponent (Exact Exponential 2-Adic Valuation Law):
    For odd `a > 1` with `2^r ‖ (a - 1)` (`r ≥ 1`), and `k = 2^e * m` (`m` odd),
    `2^(2^e * r) ‖ (clpow a k - 1)`. -/
theorem carryless_lte {a r e m : Nat} (hr : 1 ≤ r)
    (ha : exactPow2 r ((a : Int) - 1)) (hm : m % 2 = 1) :
    exactPow2 (2 ^ e * r) ((clpow a (2 ^ e * m) : Int) - 1) := by
  have hamod : a % 2 ^ (r + 1) = 1 + 2 ^ r := (exactPow2_sub_one_iff_mod hr).mp ha
  have hcm : clpow a m % 2 ^ (r + 1) = 1 + 2 ^ r := by
    rw [clpow_mod_odd hr hamod m]; simp [hm]
  rw [clpow_two_pow_mul]
  have hsp : spread (2 ^ e) (clpow a m) % 2 ^ (2 ^ e * r + 1) = 1 + 2 ^ (2 ^ e * r) :=
    spread_mod_two_pow_exact (Nat.two_pow_pos e) hr hcm
  have hpos : 1 ≤ 2 ^ e * r := Nat.mul_pos (Nat.two_pow_pos e) hr
  exact (exactPow2_sub_one_iff_mod hpos).mpr hsp

/-- Super-Exponential Carryless 2-Adic Congruence:
    If `a` is odd and `2^j ∣ (m1 - m2)`, then `2^(2^(e+j)) ∣ (clpow a (2^e*m1) - clpow a (2^e*m2))`. -/
theorem clpow_diff_dvd {a e j m1 m2 : Nat} (ha : a % 2 = 1)
    (hdiv : ((2 ^ j : Nat) : Int) ∣ ((m1 : Int) - (m2 : Int))) :
    ((2 ^ (2 ^ (e + j)) : Nat) : Int) ∣
      ((clpow a (2 ^ e * m1) : Int) - (clpow a (2 ^ e * m2) : Int)) := by
  suffices hle : ∀ x y : Nat, y ≤ x → ((2 ^ j : Nat) : Int) ∣ ((x : Int) - (y : Int)) →
      ((2 ^ (2 ^ (e + j)) : Nat) : Int) ∣
        ((clpow a (2 ^ e * x) : Int) - (clpow a (2 ^ e * y) : Int)) by
    by_cases h : m2 ≤ m1
    · exact hle m1 m2 h hdiv
    · have h' : m1 ≤ m2 := Nat.le_of_not_le h
      have hdiv' : ((2 ^ j : Nat) : Int) ∣ ((m2 : Int) - (m1 : Int)) := by
        have : (m2 : Int) - (m1 : Int) = -((m1 : Int) - (m2 : Int)) := by omega
        rw [this]; exact Int.dvd_neg.mpr hdiv
      have res := hle m2 m1 h' hdiv'
      have : (clpow a (2 ^ e * m1) : Int) - (clpow a (2 ^ e * m2) : Int) =
          -((clpow a (2 ^ e * m2) : Int) - (clpow a (2 ^ e * m1) : Int)) := by omega
      rw [this]; exact Int.dvd_neg.mpr res
  intro x y hyx hd
  rw [int_dvd_two_pow_sub_iff_mod_eq] at hd
  have hx_eq : x = y + 2 ^ j * ((x - y) / 2 ^ j) := by
    have hmod0 : (x - y) % 2 ^ j = 0 := by
      have h1 := Nat.div_add_mod x (2 ^ j)
      have h2 := Nat.div_add_mod y (2 ^ j)
      have hsub : x - y = 2 ^ j * (x / 2 ^ j - y / 2 ^ j) := by
        rw [Nat.mul_sub]; omega
      rw [hsub, Nat.mul_mod_right]
    have hdiv_xy := Nat.div_add_mod (x - y) (2 ^ j)
    omega
  let q := (x - y) / 2 ^ j
  have hmul : 2 ^ e * x = 2 ^ e * y + 2 ^ (e + j) * q := by
    calc 2 ^ e * x = 2 ^ e * (y + 2 ^ j * q) := by rw [← hx_eq]
      _ = 2 ^ e * y + 2 ^ e * (2 ^ j * q) := Nat.mul_add _ _ _
      _ = 2 ^ e * y + 2 ^ (e + j) * q := by rw [← Nat.mul_assoc, ← Nat.pow_add]
  rw [int_dvd_two_pow_sub_iff_mod_eq, hmul, clpow_add, clpow_two_pow_mul a (e + j) q]
  have hsp1 : spread (2 ^ (e + j)) (clpow a q) % 2 ^ (2 ^ (e + j)) =
      1 % 2 ^ (2 ^ (e + j)) := by
    have h1lt : 1 < 2 ^ (2 ^ (e + j)) := by
      have : 2 ≤ 2 ^ (2 ^ (e + j)) := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.two_pow_pos _)
      omega
    rw [spread_mod_two_pow (Nat.two_pow_pos (e + j)), clpow_odd_of_odd ha q, Nat.mod_eq_of_lt h1lt]
  rw [clmul_mod_two_pow_right hsp1, clmul_one_right]

/-! ============================================================================
    SECTION 4: Carried 2-Adic Lifting-The-Exponent (LTE) in Core Lean 4
    ============================================================================ -/

theorem pow_odd_of_odd {a : Nat} (ha : a % 2 = 1) (k : Nat) : (a ^ k) % 2 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Nat.pow_succ, Nat.mul_mod, ih, ha]

theorem geom_sum_odd (a m : Nat) (ha : a % 2 = 1) (hm : m % 2 = 1) :
    ∃ s : Int, ((a ^ m : Nat) : Int) - 1 = ((a : Int) - 1) * s ∧ s % 2 ≠ 0 := by
  suffices h : ∀ k : Nat, ∃ s : Int,
      ((a ^ k : Nat) : Int) - 1 = ((a : Int) - 1) * s ∧ s % 2 = ((k % 2 : Nat) : Int) by
    rcases h m with ⟨s, hs, hmod⟩
    exact ⟨s, hs, by omega⟩
  intro k
  induction k with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ k ih =>
    rcases ih with ⟨s, hs, hmod⟩
    refine ⟨s + ((a ^ k : Nat) : Int), ?_, ?_⟩
    · rw [Nat.pow_succ]
      have h1 : (((a ^ k * a : Nat) : Int) - 1) =
          (((a ^ k : Nat) : Int) - 1) + ((a : Int) - 1) * ((a ^ k : Nat) : Int) := by
        push_cast; rw [Int.sub_mul, Int.one_mul, Int.mul_comm (a : Int) (a ^ k : Int)]; omega
      rw [h1, hs, ← Int.mul_add]
    · have ha_pow_odd : (a ^ k) % 2 = 1 := pow_odd_of_odd ha k
      have h1 : (((a ^ k : Nat) : Int) % 2) = 1 := by
        have := Int.natCast_emod (a ^ k) 2
        omega
      omega

theorem carried_lte_odd {a r m : Nat} (ha_odd : a % 2 = 1)
    (ha : exactPow2 r ((a : Int) - 1)) (hm : m % 2 = 1) :
    exactPow2 r (((a ^ m : Nat) : Int) - 1) := by
  rcases geom_sum_odd a m ha_odd hm with ⟨s, hs, hsodd⟩
  rw [hs, Int.mul_comm]
  exact exactPow2_mul_odd hsodd ha

theorem carried_lte_two_pow_ge2 {a r : Nat} (hr : 2 ≤ r)
    (ha : exactPow2 r ((a : Int) - 1)) (e : Nat) :
    exactPow2 (r + e) (((a ^ (2 ^ e) : Nat) : Int) - 1) := by
  induction e with
  | zero => simpa using ha
  | succ e ih =>
    have hpow : a ^ (2 ^ (e + 1)) = (a ^ (2 ^ e)) * (a ^ (2 ^ e)) := by
      rw [Nat.pow_succ, Nat.mul_two, Nat.pow_add]
    have hfac : (((a ^ (2 ^ (e + 1)) : Nat) : Int) - 1) =
        (((a ^ (2 ^ e) : Nat) : Int) - 1) * (((a ^ (2 ^ e) : Nat) : Int) + 1) := by
      rw [hpow]; push_cast
      rw [Int.sub_mul, Int.mul_add, Int.mul_one, Int.one_mul]; omega
    have h4 : ((2 ^ 2 : Nat) : Int) ∣ (((a ^ (2 ^ e) : Nat) : Int) - 1) :=
      dvd_two_pow_of_le (by omega : 2 ≤ r + e) ih.1
    have hplus : exactPow2 1 (((a ^ (2 ^ e) : Nat) : Int) + 1) := by
      have : (((a ^ (2 ^ e) : Nat) : Int) + 1) = 2 + (((a ^ (2 ^ e) : Nat) : Int) - 1) := by omega
      rw [this]
      exact exactPow2_add_of_lt (by decide : 1 < 2) (exactPow2_two_pow 1) h4
    rw [hfac]
    have hmul := exactPow2_mul ih hplus
    have : r + e + 1 = r + (e + 1) := by omega
    rw [this] at hmul
    exact hmul

/-- Carried 2-Adic LTE (Regime `a ≡ 1 mod 4`, `r ≥ 2`). -/
theorem carried_lte_mod4_eq1 {a r e m : Nat} (hr : 2 ≤ r)
    (ha : exactPow2 r ((a : Int) - 1)) (hm : m % 2 = 1) :
    exactPow2 (r + e) (((a ^ (2 ^ e * m) : Nat) : Int) - 1) := by
  have ha_odd : a % 2 = 1 := by
    have h2 : ((2 ^ 1 : Nat) : Int) ∣ ((a : Int) - 1) := dvd_two_pow_of_le (by omega) ha.1
    rcases h2 with ⟨q, hq⟩; omega
  have hae_odd : (a ^ (2 ^ e)) % 2 = 1 := pow_odd_of_odd ha_odd (2 ^ e)
  rw [Nat.pow_mul]
  exact carried_lte_odd hae_odd (carried_lte_two_pow_ge2 hr ha e) hm

/-- Carried 2-Adic LTE (Regime `a ≡ 3 mod 4`, `s = v_2(a+1) ≥ 2`, `e ≥ 1`). -/
theorem carried_lte_mod4_eq3 {a s e m : Nat} (hs : 2 ≤ s)
    (ha : exactPow2 s ((a : Int) + 1)) (he : 1 ≤ e) (hm : m % 2 = 1) :
    exactPow2 (s + e) (((a ^ (2 ^ e * m) : Nat) : Int) - 1) := by
  have h4 : ((2 ^ 2 : Nat) : Int) ∣ ((a : Int) + 1) := dvd_two_pow_of_le hs ha.1
  have ha_minus : exactPow2 1 ((a : Int) - 1) := by
    have : ((a : Int) - 1) = ((a : Int) + 1) - 2 := by omega
    rw [this]
    exact exactPow2_sub_of_gt (by decide : 1 < 2) h4 (exactPow2_two_pow 1)
  have hsq : exactPow2 (s + 1) (((a ^ 2 : Nat) : Int) - 1) := by
    have hfac : (((a ^ 2 : Nat) : Int) - 1) = ((a : Int) + 1) * ((a : Int) - 1) := by
      rw [Nat.pow_two]; push_cast
      rw [Int.add_mul, Int.mul_sub, Int.mul_one, Int.one_mul]; omega
    rw [hfac]
    exact exactPow2_mul ha ha_minus
  have he' : e = (e - 1) + 1 := (Nat.sub_add_cancel he).symm
  have hpow : a ^ (2 ^ e * m) = (a ^ 2) ^ (2 ^ (e - 1) * m) := by
    rw [← Nat.pow_mul]
    congr 1
    calc 2 ^ e * m = 2 ^ ((e - 1) + 1) * m := by rw [← he']
      _ = (2 * 2 ^ (e - 1)) * m := by rw [Nat.pow_succ, Nat.mul_comm (2 ^ (e - 1)) 2]
      _ = 2 * (2 ^ (e - 1) * m) := Nat.mul_assoc _ _ _
  rw [hpow]
  have hres := carried_lte_mod4_eq1 (a := a ^ 2) (r := s + 1) (e := e - 1) (m := m)
    (by omega) hsq hm
  have hidx : s + 1 + (e - 1) = s + e := by omega
  rw [hidx] at hres
  exact hres

/-! ============================================================================
    SECTION 5: Main Infinite Bridge Theorems (4-Regime Law + Resonant Hensel Bridge)
    ============================================================================ -/

theorem two_pow_gt_add_of_ge2 {r e : Nat} (hr : 2 ≤ r) (he : 1 ≤ e) :
    r + e < 2 ^ e * r := by
  have hge : e + 1 ≤ 2 ^ e := by
    induction e with
    | zero => decide
    | succ e ih =>
      rw [Nat.pow_succ]
      have := Nat.two_pow_pos e
      omega
  have h1 : 1 ≤ 2 ^ e - 1 := by
    have : 2 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide : 0 < 2) he
    omega
  have h2 : (2 ^ e - 1) * 2 ≤ (2 ^ e - 1) * r := Nat.mul_le_mul_left _ hr
  have h3 : 2 ^ e * r = r + (2 ^ e - 1) * r := by
    have : 1 ≤ 2 ^ e := Nat.two_pow_pos e
    calc 2 ^ e * r = (1 + (2 ^ e - 1)) * r := by rw [Nat.add_sub_of_le this]
      _ = r + (2 ^ e - 1) * r := by rw [Nat.add_mul, Nat.one_mul]
  omega

/-- MAIN THEOREM 1 — Regime I (Zero Resonance for `a ≡ 1 mod 4`):
    For EVERY `a` with `2^r ‖ (a - 1)` (`r ≥ 2`) and EVERY even `k = 2^e * m` (`e ≥ 1, m` odd),
    the carried term strictly dominates and `2^(r + e) ‖ (a^k - clpow(a, k))`. -/
theorem regime_I_carried_dominated {a r e m : Nat} (hr : 2 ≤ r) (he : 1 ≤ e)
    (ha : exactPow2 r ((a : Int) - 1)) (hm : m % 2 = 1) :
    exactPow2 (r + e) (((a ^ (2 ^ e * m) : Nat) : Int) - (clpow a (2 ^ e * m) : Int)) := by
  have hcar := carried_lte_mod4_eq1 (e := e) hr ha hm
  have hcl := carryless_lte (e := e) (by omega : 1 ≤ r) ha hm
  have hlt := two_pow_gt_add_of_ge2 hr he
  have heq : (((a ^ (2 ^ e * m) : Nat) : Int) - (clpow a (2 ^ e * m) : Int)) =
      (((a ^ (2 ^ e * m) : Nat) : Int) - 1) - ((clpow a (2 ^ e * m) : Int) - 1) := by omega
  rw [heq]
  exact exactPow2_sub_of_lt hlt hcar hcl.1

/-- MAIN THEOREM 1 — Regime II (Carryless-Dominated below the Resonance Curve):
    For `a ≡ 3 mod 4` with `2^s ‖ (a + 1)` (`s ≥ 2`), `e ≥ 1`, `m` odd, and `2^e < s + e`,
    `2^(2^e) ‖ (a^k - clpow(a, k))`. -/
theorem regime_II_carryless_dominated {a s e m : Nat} (hs : 2 ≤ s) (he : 1 ≤ e)
    (ha : exactPow2 s ((a : Int) + 1)) (hm : m % 2 = 1) (hlt : 2 ^ e < s + e) :
    exactPow2 (2 ^ e) (((a ^ (2 ^ e * m) : Nat) : Int) - (clpow a (2 ^ e * m) : Int)) := by
  have h4 : ((2 ^ 2 : Nat) : Int) ∣ ((a : Int) + 1) := dvd_two_pow_of_le hs ha.1
  have ha1 : exactPow2 1 ((a : Int) - 1) := by
    have : ((a : Int) - 1) = ((a : Int) + 1) - 2 := by omega
    rw [this]; exact exactPow2_sub_of_gt (by decide : 1 < 2) h4 (exactPow2_two_pow 1)
  have hcar := carried_lte_mod4_eq3 hs ha he hm
  have hcl := carryless_lte (e := e) (by decide : 1 ≤ 1) ha1 hm
  rw [Nat.mul_one] at hcl
  have heq : (((a ^ (2 ^ e * m) : Nat) : Int) - (clpow a (2 ^ e * m) : Int)) =
      (((a ^ (2 ^ e * m) : Nat) : Int) - 1) - ((clpow a (2 ^ e * m) : Int) - 1) := by omega
  rw [heq]
  exact exactPow2_sub_of_gt hlt hcar.1 hcl

/-- MAIN THEOREM 1 — Regime III (Carried-Dominated above the Resonance Curve):
    For `a ≡ 3 mod 4` with `2^s ‖ (a + 1)` (`s ≥ 2`), `e ≥ 1`, `m` odd, and `s + e < 2^e`,
    `2^(s + e) ‖ (a^k - clpow(a, k))`. -/
theorem regime_III_carried_dominated {a s e m : Nat} (hs : 2 ≤ s) (he : 1 ≤ e)
    (ha : exactPow2 s ((a : Int) + 1)) (hm : m % 2 = 1) (hlt : s + e < 2 ^ e) :
    exactPow2 (s + e) (((a ^ (2 ^ e * m) : Nat) : Int) - (clpow a (2 ^ e * m) : Int)) := by
  have h4 : ((2 ^ 2 : Nat) : Int) ∣ ((a : Int) + 1) := dvd_two_pow_of_le hs ha.1
  have ha1 : exactPow2 1 ((a : Int) - 1) := by
    have : ((a : Int) - 1) = ((a : Int) + 1) - 2 := by omega
    rw [this]; exact exactPow2_sub_of_gt (by decide : 1 < 2) h4 (exactPow2_two_pow 1)
  have hcar := carried_lte_mod4_eq3 hs ha he hm
  have hcl := carryless_lte (e := e) (by decide : 1 ≤ 1) ha1 hm
  rw [Nat.mul_one] at hcl
  have heq : (((a ^ (2 ^ e * m) : Nat) : Int) - (clpow a (2 ^ e * m) : Int)) =
      (((a ^ (2 ^ e * m) : Nat) : Int) - 1) - ((clpow a (2 ^ e * m) : Int) - 1) := by omega
  rw [heq]
  exact exactPow2_sub_of_lt hlt hcar hcl.1

theorem resonant_s_ge2 {e : Nat} (he : 2 ≤ e) : 2 ≤ 2 ^ e - e ∧ e ≤ 2 ^ e := by
  have h : e + 2 ≤ 2 ^ e := by
    induction e with
    | zero => omega
    | succ e ih =>
      by_cases h2 : e = 1
      · subst h2; decide
      · have he2 : 2 ≤ e := by omega
        have hrec := ih he2
        rw [Nat.pow_succ]; omega
  omega

theorem two_pow_superlinear {e j : Nat} (he : 2 ≤ e) :
    2 ^ e + 1 + j < 2 ^ (e + 1 + j) := by
  have hE : 4 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide : 0 < 2) he
  induction j with
  | zero =>
    rw [Nat.add_zero, Nat.add_zero, Nat.pow_succ]
    omega
  | succ j ih =>
    have hidx : e + 1 + (j + 1) = (e + 1 + j) + 1 := by omega
    rw [hidx, Nat.pow_succ]
    omega

/-- Exact Carry-Coupling Decomposition mod `2^(2^e + 2)` for `B * spread(2^e, a) - clmul(B, spread(2^e, a))`. -/
theorem mul_defect_mod_resonance {a e B : Nat} (he : 2 ≤ e)
    (ha_mod4 : a % 4 = 3) (hB_odd : B % 2 = 1) :
    ((2 ^ (2 ^ e + 2) : Nat) : Int) ∣
      (((B * clpow a (2 ^ e) : Nat) : Int) - ((clmul B (clpow a (2 ^ e)) : Nat) : Int) -
       (if B.testBit (2 ^ e) then ((2 ^ (2 ^ e + 1) : Nat) : Int) else 0)) := by
  have hE4 : 4 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide : 0 < 2) he
  have hcl_eq : clpow a (2 ^ e) = spread (2 ^ e) a := by
    have := clpow_two_pow_mul a e 1
    rw [Nat.mul_one, clpow_one] at this
    exact this
  have hcl_mod : clpow a (2 ^ e) % 2 ^ (2 ^ e + 2) = 1 + 2 ^ (2 ^ e) := by
    rw [hcl_eq]
    have ha_ne : a ≠ 0 := by omega
    rw [spread_unfold ha_ne]
    have ha0 : a % 2 = 1 := by omega
    have ha1_ne : a / 2 ≠ 0 := by omega
    have ha1_mod : (a / 2) % 2 = 1 := by omega
    rw [ha0, spread_unfold ha1_ne, ha1_mod, Nat.mul_add, Nat.mul_one,
        ← Nat.mul_assoc, ← Nat.pow_add]
    have hdvd : 2 ^ (2 ^ e + 2) ∣ 2 ^ (2 ^ e + 2 ^ e) := by
      have heq : 2 ^ e + 2 ^ e = (2 ^ e + 2) + (2 ^ e - 2) := by omega
      exact ⟨2 ^ (2 ^ e - 2), by rw [← Nat.pow_add, ← heq]⟩
    rcases hdvd with ⟨q, hq⟩
    have hlt : 1 + 2 ^ (2 ^ e) < 2 ^ (2 ^ e + 2) := by
      rw [Nat.pow_add 2 (2 ^ e) 2]
      have h2 : 2 ^ 2 = 4 := rfl
      have hposE : 1 ≤ 2 ^ (2 ^ e) := Nat.two_pow_pos _
      rw [h2]; omega
    rw [hq, Nat.mul_assoc, ← Nat.add_assoc, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  let W := 2 ^ e + 2
  let E := 2 ^ e
  have hlt_1E : 1 + 2 ^ E < 2 ^ W := by
    change 1 + 2 ^ E < 2 ^ (E + 2)
    rw [Nat.pow_add 2 E 2]
    have h2 : 2 ^ 2 = 4 := rfl
    have hposE : 1 ≤ 2 ^ E := Nat.two_pow_pos _
    rw [h2]; omega
  have hmul_mod : ((2 ^ W : Nat) : Int) ∣
      (((B * clpow a E : Nat) : Int) - ((B * (1 + 2 ^ E) : Nat) : Int)) := by
    rw [int_dvd_two_pow_sub_iff_mod_eq, Nat.mul_mod, Nat.mul_mod B (1 + 2 ^ E), hcl_mod,
        Nat.mod_eq_of_lt hlt_1E]
  have hclm_mod : ((2 ^ W : Nat) : Int) ∣
      (((clmul B (clpow a E) : Nat) : Int) - ((clmul B (1 + 2 ^ E) : Nat) : Int)) := by
    rw [int_dvd_two_pow_sub_iff_mod_eq]
    exact clmul_mod_two_pow_right (by rw [hcl_mod, Nat.mod_eq_of_lt hlt_1E])
  have h1lt : 1 < 2 ^ E := by
    have : 2 ≤ 2 ^ E := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ E)
    omega
  have hclm_eval : clmul B (1 + 2 ^ E) = B ^^^ (2 ^ E * B) := by
    have h1 : 1 + 2 ^ E = 1 ^^^ (2 ^ E * 1) := by
      simpa using add_eq_xor_of_lt_pow2 (a := 1) (b := 1) (r := E) h1lt
    rw [h1, clmul_xor_right, clmul_one_right, clmul_pow2_mul_right, clmul_one_right]
  have hdiff_nat : B * (1 + 2 ^ E) = clmul B (1 + 2 ^ E) + 2 * (B &&& (2 ^ E * B)) := by
    rw [hclm_eval, Nat.mul_add, Nat.mul_one, Nat.mul_comm B (2 ^ E)]
    exact add_eq_xor_add_two_and B (2 ^ E * B)
  have hand_mod : (B &&& (2 ^ E * B)) % 2 ^ (E + 1) = if B.testBit E then 2 ^ E else 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_and]
    have hsh : (2 ^ E * B).testBit i = (decide (E ≤ i) && B.testBit (i - E)) := by
      rw [Nat.mul_comm, ← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]
    rw [hsh]
    by_cases hi : i < E + 1
    · by_cases hie : i = E
      · subst hie
        have hB0 : B.testBit 0 = true := by simp [Nat.testBit_zero, hB_odd]
        cases hBE : B.testBit E
        · simp [hB0]
        · simp [hB0]
      · have hlt : ¬ (E ≤ i) := by omega
        have hne : E ≠ i := by omega
        cases hBE : B.testBit E
        · simp [hi, hlt]
        · simp [hi, hlt, hne]
    · have hne : E ≠ i := by omega
      cases hBE : B.testBit E
      · simp [hi]
      · simp [hi, hne]
  have h2and_mod : ((2 ^ W : Nat) : Int) ∣
      (((2 * (B &&& (2 ^ E * B)) : Nat) : Int) -
       (if B.testBit E then ((2 ^ (E + 1) : Nat) : Int) else 0)) := by
    have hgoal : (2 * (B &&& (2 ^ E * B))) % 2 ^ W =
        (if B.testBit E then 2 ^ (E + 1) else 0) % 2 ^ W := by
      have hW : 2 ^ W = 2 * 2 ^ (E + 1) := by
        change 2 ^ (E + 2) = 2 * 2 ^ (E + 1)
        rw [Nat.pow_succ, Nat.mul_comm]
      rw [hW, Nat.mul_mod_mul_left, hand_mod]
      cases B.testBit E
      · simp
      · simp only [↓reduceIte]
        have h1 : 2 * 2 ^ E = 2 ^ (E + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
        rw [h1, Nat.mod_eq_of_lt (by omega : 2 ^ (E + 1) < 2 * 2 ^ (E + 1))]
    cases hBE : B.testBit E
    · rw [hBE] at hgoal
      simp only [Bool.false_eq_true, ↓reduceIte] at hgoal ⊢
      exact int_dvd_two_pow_sub_iff_mod_eq.mpr hgoal
    · rw [hBE] at hgoal
      simp only [↓reduceIte] at hgoal ⊢
      exact int_dvd_two_pow_sub_iff_mod_eq.mpr hgoal
  have hcombine :
      (((B * clpow a E : Nat) : Int) - ((clmul B (clpow a E) : Nat) : Int) -
       (if B.testBit E then ((2 ^ (E + 1) : Nat) : Int) else 0)) =
      (((B * clpow a E : Nat) : Int) - ((B * (1 + 2 ^ E) : Nat) : Int)) -
      (((clmul B (clpow a E) : Nat) : Int) - ((clmul B (1 + 2 ^ E) : Nat) : Int)) +
      (((2 * (B &&& (2 ^ E * B)) : Nat) : Int) -
       (if B.testBit E then ((2 ^ (E + 1) : Nat) : Int) else 0)) := by
    omega
  rw [hcombine]
  exact Int.dvd_add (Int.dvd_sub hmul_mod hclm_mod) h2and_mod

/-- MAIN THEOREM 2 (Engine Instantiation — Resonance Curve Isometry):
    For EVERY `e ≥ 2`, EVERY `a` on the Resonance Curve `2^(2^e - e) ‖ (a + 1)`,
    and EVERY odd multiplier `B : Nat`, the perturbed carryless-vs-carried polynomial bridge
    `F_bridge a e B` satisfies the `ScaledIsometry` contract of `HenselBridge` at scale `2^e + 1`! -/
theorem resonant_is_scaledIsometry {a e B : Nat} (he : 2 ≤ e)
    (ha : exactPow2 (2 ^ e - e) ((a : Int) + 1)) (hB : B % 2 = 1) :
    ScaledIsometry (F_bridge a e B) (2 ^ e + 1) := by
  have ⟨hs2, hle⟩ := resonant_s_ge2 he
  have hse : (2 ^ e - e) + e = 2 ^ e := Nat.sub_add_cancel hle
  have h4 : ((2 ^ 2 : Nat) : Int) ∣ ((a : Int) + 1) := dvd_two_pow_of_le hs2 ha.1
  have ha_mod4 : a % 4 = 3 := by
    rcases h4 with ⟨q, hq⟩; omega
  have ha_odd : a % 2 = 1 := by omega
  have ha1 : exactPow2 1 ((a : Int) - 1) := by
    have : ((a : Int) - 1) = ((a : Int) + 1) - 2 := by omega
    rw [this]; exact exactPow2_sub_of_gt (by decide : 1 < 2) h4 (exactPow2_two_pow 1)
  have hcar_exact : ∀ x y j : Nat, exactPow2 j ((x : Int) - (y : Int)) →
      exactPow2 (2 ^ e + 1 + j)
        (((B * a ^ (2 ^ e * (2 * x + 1)) : Nat) : Int) -
         ((B * a ^ (2 ^ e * (2 * y + 1)) : Nat) : Int)) := by
    suffices hle_xy : ∀ x y j : Nat, y ≤ x → exactPow2 j ((x : Int) - (y : Int)) →
        exactPow2 (2 ^ e + 1 + j)
          (((B * a ^ (2 ^ e * (2 * x + 1)) : Nat) : Int) -
           ((B * a ^ (2 ^ e * (2 * y + 1)) : Nat) : Int)) by
      intro x y j hex
      by_cases h : y ≤ x
      · exact hle_xy x y j h hex
      · have h' : x ≤ y := Nat.le_of_not_le h
        have hex' : exactPow2 j ((y : Int) - (x : Int)) := by
          have : (y : Int) - (x : Int) = -((x : Int) - (y : Int)) := by omega
          rw [this]; exact exactPow2_neg hex
        have res := hle_xy y x j h' hex'
        have : (((B * a ^ (2 ^ e * (2 * x + 1)) : Nat) : Int) -
                ((B * a ^ (2 ^ e * (2 * y + 1)) : Nat) : Int)) =
               -(((B * a ^ (2 ^ e * (2 * y + 1)) : Nat) : Int) -
                 ((B * a ^ (2 ^ e * (2 * x + 1)) : Nat) : Int)) := by omega
        rw [this]; exact exactPow2_neg res
    intro x y j hyx hex
    rw [exactPow2_iff_odd_mul] at hex
    rcases hex with ⟨q, hq, hqodd⟩
    have hq_nonneg : 0 ≤ q := by
      have hpos := two_pow_int_pos j
      by_cases h0 : 0 ≤ q
      · exact h0
      · exfalso
        have hqle : q ≤ -1 := by omega
        have hmul := Int.mul_le_mul_of_nonneg_left hqle (Int.le_of_lt hpos)
        simp only [Int.mul_neg, Int.mul_one] at hmul
        omega
    let qn := q.toNat
    have hqn : (qn : Int) = q := Int.toNat_of_nonneg hq_nonneg
    have hqn_eq : x = y + 2 ^ j * qn := by
      have h1 : ((x : Int) - (y : Int)) = ((2 ^ j * qn : Nat) : Int) := by
        rw [hq, ← hqn]; push_cast; rfl
      omega
    have hqn_odd : qn % 2 = 1 := by omega
    have hexp : 2 ^ e * (2 * x + 1) = 2 ^ e * (2 * y + 1) + 2 ^ (e + 1 + j) * qn := by
      rw [hqn_eq]
      have h1 : 2 * (y + 2 ^ j * qn) + 1 = (2 * y + 1) + 2 * (2 ^ j * qn) := by omega
      rw [h1, Nat.mul_add, Nat.pow_add, Nat.pow_add, Nat.pow_one]
      have : 2 ^ e * (2 * (2 ^ j * qn)) = (2 ^ e * 2) * 2 ^ j * qn := by
        rw [Nat.mul_assoc, Nat.mul_assoc]
      exact congrArg (2 ^ e * (2 * y + 1) + ·) this
    have hfac : (((B * a ^ (2 ^ e * (2 * x + 1)) : Nat) : Int) -
                 ((B * a ^ (2 ^ e * (2 * y + 1)) : Nat) : Int)) =
        (((B * a ^ (2 ^ e * (2 * y + 1)) : Nat) : Int)) *
        (((a ^ (2 ^ (e + 1 + j) * qn) : Nat) : Int) - 1) := by
      rw [hexp, Nat.pow_add]
      push_cast
      rw [Int.mul_sub, Int.mul_one, Int.mul_assoc]
    rw [hfac]
    have hlte := carried_lte_mod4_eq3 hs2 ha (by omega : 1 ≤ e + 1 + j) hqn_odd
    have hidx : (2 ^ e - e) + (e + 1 + j) = 2 ^ e + 1 + j := by omega
    rw [hidx] at hlte
    have hcoef_odd : ((B * a ^ (2 ^ e * (2 * y + 1)) : Nat) : Int) % 2 ≠ 0 := by
      have : (B * a ^ (2 ^ e * (2 * y + 1))) % 2 = 1 := by
        rw [Nat.mul_mod, hB, pow_odd_of_odd ha_odd]
      omega
    exact exactPow2_mul_odd hcoef_odd hlte
  have hcl_dvd : ∀ x y j : Nat, ((2 ^ j : Nat) : Int) ∣ ((x : Int) - (y : Int)) →
      ((2 ^ (2 ^ (e + 1 + j)) : Nat) : Int) ∣
        (((clmul B (clpow a (2 ^ e * (2 * x + 1))) : Nat) : Int) -
         ((clmul B (clpow a (2 ^ e * (2 * y + 1))) : Nat) : Int)) := by
    intro x y j hdiv
    have h2 : ((2 ^ (j + 1) : Nat) : Int) ∣ (((2 * x + 1 : Nat) : Int) - ((2 * y + 1 : Nat) : Int)) := by
      rcases hdiv with ⟨q, hq⟩
      refine ⟨q, ?_⟩
      rw [two_pow_int_succ]
      have : ((2 * x + 1 : Nat) : Int) - ((2 * y + 1 : Nat) : Int) = 2 * ((x : Int) - (y : Int)) := by omega
      rw [this, hq, Int.mul_comm ((2 ^ j : Nat) : Int) 2, Int.mul_assoc]
    have hcp := clpow_diff_dvd (a := a) (e := e) (j := j + 1) (m1 := 2 * x + 1) (m2 := 2 * y + 1) ha_odd h2
    have hidx : e + (j + 1) = e + 1 + j := by omega
    rw [hidx] at hcp
    rw [int_dvd_two_pow_sub_iff_mod_eq] at hcp ⊢
    exact clmul_mod_two_pow_right hcp
  refine ⟨?_, ?_, ?_⟩
  · -- base_dvd: 2^(2^e + 1) ∣ F_bridge a e B 0
    have hcar0 := carried_lte_mod4_eq3 hs2 ha (by omega : 1 ≤ e) (by decide : 1 % 2 = 1)
    rw [hse, Nat.mul_one] at hcar0
    have hcl0 := carryless_lte (e := e) (by decide : 1 ≤ 1) ha1 (by decide : 1 % 2 = 1)
    rw [Nat.mul_one] at hcl0
    have hphi0 : ((2 ^ (2 ^ e + 1) : Nat) : Int) ∣
        (((a ^ (2 ^ e) : Nat) : Int) - ((clpow a (2 ^ e) : Nat) : Int)) := by
      have : (((a ^ (2 ^ e) : Nat) : Int) - ((clpow a (2 ^ e) : Nat) : Int)) =
          (((a ^ (2 ^ e) : Nat) : Int) - 1) - ((clpow a (2 ^ e) : Int) - 1) := by omega
      rw [this]
      exact dvd_succ_sub_of_exactPow2_eq hcar0 hcl0
    have hdef0 := mul_defect_mod_resonance he ha_mod4 hB
    have hdef_dvd : ((2 ^ (2 ^ e + 1) : Nat) : Int) ∣
        (((B * clpow a (2 ^ e) : Nat) : Int) - ((clmul B (clpow a (2 ^ e)) : Nat) : Int)) := by
      have hsub := dvd_two_pow_of_le (by omega : 2 ^ e + 1 ≤ 2 ^ e + 2) hdef0
      have hterm : ((2 ^ (2 ^ e + 1) : Nat) : Int) ∣
          (if B.testBit (2 ^ e) then ((2 ^ (2 ^ e + 1) : Nat) : Int) else 0) := by
        cases B.testBit (2 ^ e) <;> simp
      have heq : (((B * clpow a (2 ^ e) : Nat) : Int) - ((clmul B (clpow a (2 ^ e)) : Nat) : Int)) =
          ((((B * clpow a (2 ^ e) : Nat) : Int) - ((clmul B (clpow a (2 ^ e)) : Nat) : Int)) -
           (if B.testBit (2 ^ e) then ((2 ^ (2 ^ e + 1) : Nat) : Int) else 0)) +
          (if B.testBit (2 ^ e) then ((2 ^ (2 ^ e + 1) : Nat) : Int) else 0) := by omega
      rw [heq]
      exact Int.dvd_add hsub hterm
    show ((2 ^ (2 ^ e + 1) : Nat) : Int) ∣ F_bridge a e B 0
    unfold F_bridge
    simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one]
    have hdecomp : (((B * a ^ (2 ^ e) : Nat) : Int) - ((clmul B (clpow a (2 ^ e)) : Nat) : Int)) =
        (B : Int) * (((a ^ (2 ^ e) : Nat) : Int) - ((clpow a (2 ^ e) : Nat) : Int)) +
        (((B * clpow a (2 ^ e) : Nat) : Int) - ((clmul B (clpow a (2 ^ e)) : Nat) : Int)) := by
      push_cast; rw [Int.mul_sub]; omega
    rw [hdecomp]
    exact Int.dvd_add (Int.dvd_mul_of_dvd_right hphi0) hdef_dvd
  · -- lip_dvd
    intro x y j hdiv
    by_cases hxy : x = y
    · subst hxy; simp
    · have hne : (x : Int) - (y : Int) ≠ 0 := by omega
      have hbound : ∃ k : Nat, j ≤ k ∧ exactPow2 k ((x : Int) - (y : Int)) := by
        have hnot : ¬ (((2 ^ (((x : Int) - (y : Int)).natAbs) : Nat) : Int) ∣ ((x : Int) - (y : Int))) :=
          not_dvd_two_pow_of_ne_zero hne _ (nat_lt_two_pow _)
        rcases exists_exactPow2_lt_of_not_dvd hnot with ⟨k, _, hexk⟩
        have hjk : j ≤ k := by
          by_cases hle' : j ≤ k
          · exact hle'
          · exfalso
            have h1 : k + 1 ≤ j := by omega
            exact hexk.2 (dvd_two_pow_of_le h1 hdiv)
        exact ⟨k, hjk, hexk⟩
      rcases hbound with ⟨k, hjk, hexk⟩
      have hcar := hcar_exact x y k hexk
      have hcl := hcl_dvd x y k hexk.1
      have hlt := two_pow_superlinear (e := e) (j := k) he
      have heq : F_bridge a e B x - F_bridge a e B y =
          (((B * a ^ (2 ^ e * (2 * x + 1)) : Nat) : Int) -
           ((B * a ^ (2 ^ e * (2 * y + 1)) : Nat) : Int)) -
          (((clmul B (clpow a (2 ^ e * (2 * x + 1))) : Nat) : Int) -
           ((clmul B (clpow a (2 ^ e * (2 * y + 1))) : Nat) : Int)) := by
        unfold F_bridge; omega
      rw [heq]
      have hex_sub := exactPow2_sub_of_lt hlt hcar hcl
      exact dvd_two_pow_of_le (by omega : 2 ^ e + 1 + j ≤ 2 ^ e + 1 + k) hex_sub.1
  · -- lip_exact
    intro x y j hex
    have hcar := hcar_exact x y j hex
    have hcl := hcl_dvd x y j hex.1
    have hlt := two_pow_superlinear (e := e) (j := j) he
    have heq : F_bridge a e B x - F_bridge a e B y =
        (((B * a ^ (2 ^ e * (2 * x + 1)) : Nat) : Int) -
         ((B * a ^ (2 ^ e * (2 * y + 1)) : Nat) : Int)) -
        (((clmul B (clpow a (2 ^ e * (2 * x + 1))) : Nat) : Int) -
         ((clmul B (clpow a (2 ^ e * (2 * y + 1))) : Nat) : Int)) := by
      unfold F_bridge; omega
    rw [heq]
    exact exactPow2_sub_of_lt hlt hcar hcl

/-- Strict positivity of `F_bridge a e B n` for all resonant `(a, e)`, odd `B`, and `n : Nat`. -/
theorem resonant_F_bridge_pos {a e B n : Nat} (he : 2 ≤ e)
    (ha : exactPow2 (2 ^ e - e) ((a : Int) + 1)) (hB : B % 2 = 1) :
    0 < F_bridge a e B n := by
  have ⟨hs2, _⟩ := resonant_s_ge2 he
  have h4 : ((2 ^ 2 : Nat) : Int) ∣ ((a : Int) + 1) := dvd_two_pow_of_le hs2 ha.1
  have ha_odd : a % 2 = 1 := by rcases h4 with ⟨q, hq⟩; omega
  have ha3 : 3 ≤ a := by rcases h4 with ⟨q, hq⟩; omega
  have hk2 : 2 ≤ 2 ^ e * (2 * n + 1) := by
    have : 4 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide : 0 < 2) he
    have := Nat.mul_le_mul (by omega : 4 ≤ 2 ^ e) (by omega : 1 ≤ 2 * n + 1)
    omega
  have hlt := clpow_lt_pow ha_odd ha3 hk2
  have hBpos : 0 < B := by omega
  have h1 : clmul B (clpow a (2 ^ e * (2 * n + 1))) ≤ B * clpow a (2 ^ e * (2 * n + 1)) :=
    clmul_le_mul _ _
  have h2 : B * clpow a (2 ^ e * (2 * n + 1)) < B * a ^ (2 ^ e * (2 * n + 1)) :=
    Nat.mul_lt_mul_of_pos_left hlt hBpos
  unfold F_bridge; omega

/-- MAIN THEOREM 3 (Infinite Lifting, Exact Classification, & Non-Naturality on the Resonance Curve):
    Discharged directly by feeding `resonant_is_scaledIsometry` into `HenselBridge`! -/
theorem resonant_bridge_master {a e B : Nat} (he : 2 ≤ e)
    (ha : exactPow2 (2 ^ e - e) ((a : Int) + 1)) (hB : B % 2 = 1) :
    (∀ t : Nat, henselLift (F_bridge a e B) (2 ^ e + 1) t < 2 ^ t ∧
      ((2 ^ (2 ^ e + 1 + t) : Nat) : Int) ∣
        F_bridge a e B (henselLift (F_bridge a e B) (2 ^ e + 1) t)) ∧
    (∀ n t : Nat, ((2 ^ (2 ^ e + 1 + t) : Nat) : Int) ∣ F_bridge a e B n ↔
      n % 2 ^ t = henselLift (F_bridge a e B) (2 ^ e + 1) t) ∧
    (∀ N : Nat, ∃ t : Nat, N < henselLift (F_bridge a e B) (2 ^ e + 1) t) := by
  have hiso := resonant_is_scaledIsometry he ha hB
  have hne : ∀ n, F_bridge a e B n ≠ 0 := fun n =>
    Int.ne_of_gt (resonant_F_bridge_pos he ha hB)
  refine ⟨?_, ?_, ?_⟩
  · intro t
    exact ⟨henselLift_lt _ _ t, henselLift_dvd hiso t⟩
  · intro n t
    exact henselLift_iff_dvd hiso n t
  · exact henselLift_unbounded_of_ne_zero hiso hne

/-- MAIN THEOREM 4 (Exact 2-Adic Root Invariance Below the Zero-Carry Threshold `B < 2^(2^e)`):
    For ALL resonant `(a, e)`, ALL odd `B < 2^(2^e)`, and ALL precision depths `t : Nat`,
    the perturbed 2-adic root agrees identically with the unperturbed root! -/
theorem resonant_root_invariance_below_threshold {a e B : Nat} (he : 2 ≤ e)
    (ha : exactPow2 (2 ^ e - e) ((a : Int) + 1)) (hB : B % 2 = 1) (hBlt : B < 2 ^ (2 ^ e)) :
    ∀ t : Nat, henselLift (F_bridge a e B) (2 ^ e + 1) t =
               henselLift (F_bridge a e 1) (2 ^ e + 1) t := by
  have hiso1 := resonant_is_scaledIsometry he ha (by decide : 1 % 2 = 1)
  have hisoB := resonant_is_scaledIsometry he ha hB
  apply henselLift_odd_scale_invariant hiso1 hisoB (c := (B : Int))
  intro n
  unfold F_bridge
  rw [clpow_two_pow_mul, clmul_spread_eq_mul hBlt, clmul_one_left, Nat.one_mul]
  push_cast
  rw [Int.mul_sub]

/-- MAIN THEOREM 5 (Exact Bit-`(2^e)` Carry-Coupling Root-Shift Law):
    For ALL resonant `(a, e)` and ALL odd multipliers `B : Nat`, bit `0` of the
    2-adic root shifts relative to `B = 1` by EXACTLY `B.testBit (2^e)`! -/
theorem resonant_bit_root_shift_law {a e B : Nat} (he : 2 ≤ e)
    (ha : exactPow2 (2 ^ e - e) ((a : Int) + 1)) (hB : B % 2 = 1) :
    henselLift (F_bridge a e B) (2 ^ e + 1) 1 =
      (henselLift (F_bridge a e 1) (2 ^ e + 1) 1) ^^^ (if B.testBit (2 ^ e) then 1 else 0) := by
  have hiso1 := resonant_is_scaledIsometry he ha (by decide : 1 % 2 = 1)
  have ⟨hs2, _⟩ := resonant_s_ge2 he
  have h4 : ((2 ^ 2 : Nat) : Int) ∣ ((a : Int) + 1) := dvd_two_pow_of_le hs2 ha.1
  have ha_mod4 : a % 4 = 3 := by rcases h4 with ⟨q, hq⟩; omega
  apply henselLift_bit0_shift (b := B.testBit (2 ^ e)) hiso1
  have hF1_0 : ((2 ^ (2 ^ e + 1) : Nat) : Int) ∣ F_bridge a e 1 0 := hiso1.base_dvd
  have hBsub1 : (2 : Int) ∣ ((B : Int) - 1) := by
    refine ⟨((B / 2 : Nat) : Int), ?_⟩; omega
  have hmul_even : ((2 ^ (2 ^ e + 2) : Nat) : Int) ∣ (((B : Int) - 1) * F_bridge a e 1 0) := by
    rcases hBsub1 with ⟨q1, hq1⟩
    rcases hF1_0 with ⟨q2, hq2⟩
    refine ⟨q1 * q2, ?_⟩
    rw [hq1, hq2, two_pow_int_succ]
    calc (2 * q1) * (((2 ^ (2 ^ e + 1) : Nat) : Int) * q2)
        = 2 * (q1 * (((2 ^ (2 ^ e + 1) : Nat) : Int) * q2)) := Int.mul_assoc _ _ _
      _ = 2 * ((((2 ^ (2 ^ e + 1) : Nat) : Int) * q1) * q2) := by
          rw [← Int.mul_assoc q1, Int.mul_comm q1 ((2 ^ (2 ^ e + 1) : Nat) : Int)]
      _ = 2 * (((2 ^ (2 ^ e + 1) : Nat) : Int) * (q1 * q2)) := by rw [Int.mul_assoc]
      _ = (2 * ((2 ^ (2 ^ e + 1) : Nat) : Int)) * (q1 * q2) := (Int.mul_assoc _ _ _).symm
      _ = (((2 ^ (2 ^ e + 1) : Nat) : Int) * 2) * (q1 * q2) := by rw [Int.mul_comm 2]
  have hdef := mul_defect_mod_resonance he ha_mod4 hB
  have hdecomp : F_bridge a e B 0 - F_bridge a e 1 0 -
      (if B.testBit (2 ^ e) then ((2 ^ (2 ^ e + 1) : Nat) : Int) else 0) =
      (((B : Int) - 1) * F_bridge a e 1 0) +
      (((B * clpow a (2 ^ e) : Nat) : Int) - ((clmul B (clpow a (2 ^ e)) : Nat) : Int) -
       (if B.testBit (2 ^ e) then ((2 ^ (2 ^ e + 1) : Nat) : Int) else 0)) := by
    unfold F_bridge
    simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one, Nat.one_mul, clmul_one_left]
    push_cast
    rw [Int.sub_mul, Int.mul_sub, Int.one_mul]
    omega
  rw [hdecomp]
  exact Int.dvd_add hmul_even hdef

/-! ============================================================================
    SECTION 6: Infinite Non-Vacuity Witnesses & Kernel-Checked Sharpness Proofs
    ============================================================================ -/

/-- INFINITE NON-VACUITY WITNESS (2-Parameter Infinite Family on the Resonance Curve):
    For EVERY `e ≥ 2` and EVERY `q : Nat`, the odd integer `a = (2*q + 1) * 2^(2^e - e) - 1`
    (including the Mersenne family `2^(2^e - e) - 1` at `q = 0`: 3, 31, 4095, ...)
    inhabits the Resonance Curve `exactPow2 (2^e - e) (a + 1)`. -/
theorem resonance_curve_infinitely_inhabited (e q : Nat) :
    exactPow2 (2 ^ e - e) ((((2 * q + 1) * 2 ^ (2 ^ e - e) - 1 : Nat) : Int) + 1) := by
  have hpos : 1 ≤ (2 * q + 1) * 2 ^ (2 ^ e - e) :=
    Nat.mul_pos (by omega) (Nat.two_pow_pos _)
  have heq : ((((2 * q + 1) * 2 ^ (2 ^ e - e) - 1 : Nat) : Int) + 1) =
      ((2 ^ (2 ^ e - e) : Nat) : Int) * ((2 * q + 1 : Nat) : Int) := by
    have hnat : ((2 * q + 1) * 2 ^ (2 ^ e - e) - 1) + 1 = 2 ^ (2 ^ e - e) * (2 * q + 1) := by
      rw [Nat.sub_add_cancel hpos, Nat.mul_comm]
    have hcast := congrArg (fun n : Nat => (n : Int)) hnat
    push_cast at hcast
    exact hcast
  rw [heq, exactPow2_iff_odd_mul]
  exact ⟨((2 * q + 1 : Nat) : Int), rfl, by omega⟩

-- Concrete kernel-checked non-vacuity evaluations of our constructive silicon lifter:
theorem witness_lift_3_2_B1 : henselLift (F_bridge 3 2 1) 5 3 = 6 := by decide
theorem witness_lift_3_2_B15 : henselLift (F_bridge 3 2 15) 5 3 = 6 := by decide
theorem witness_lift_3_2_B17 : henselLift (F_bridge 3 2 17) 5 3 = 1 := by decide
theorem witness_lift_11_2_B1 : henselLift (F_bridge 11 2 1) 5 3 = 5 := by decide
theorem witness_lift_31_3_B1 : henselLift (F_bridge 31 3 1) 9 1 = 1 := by decide

-- Concrete kernel-checked sharpness / falsification counterexamples:

/-- Sharpness C1: `a = 5 ≡ 1 (mod 4)` never resonates (`v_2(5^4 - clpow(5, 4)) = 4`, exact). -/
theorem sharpness_C1_mod4_eq1 :
    exactPow2 4 (((5 ^ 4 : Nat) : Int) - (clpow 5 4 : Int)) := by
  have : ((5 ^ 4 : Nat) : Int) - (clpow 5 4 : Int) = 368 := by decide
  rw [this, exactPow2_iff_odd_mul]
  exact ⟨23, by decide, by decide⟩

/-- Sharpness C2: `a = 7` (`s = 3 ∉ {2^e - e}`) has zero resonance across all `e ≥ 1`. -/
theorem sharpness_C2_off_curve_7 (e m : Nat) (he : 1 ≤ e) (hm : m % 2 = 1) :
    exactPow2 (min (2 ^ e) (3 + e))
      (((7 ^ (2 ^ e * m) : Nat) : Int) - (clpow 7 (2 ^ e * m) : Int)) := by
  have ha7 : exactPow2 3 ((7 : Int) + 1) := by
    rw [exactPow2_iff_odd_mul]; exact ⟨1, by decide, by decide⟩
  by_cases h1 : e = 1
  · subst h1
    simpa using regime_II_carryless_dominated (a := 7) (s := 3) (e := 1) (m := m)
      (by decide) (by decide) ha7 hm (by decide)
  · by_cases h2 : e = 2
    · subst h2
      simpa using regime_II_carryless_dominated (a := 7) (s := 3) (e := 2) (m := m)
        (by decide) (by decide) ha7 hm (by decide)
    · have h3 : 3 ≤ e := by omega
      have hgt : 3 + e < 2 ^ e := by
        induction e with
        | zero => omega
        | succ e ih =>
          by_cases he3 : e = 2
          · subst he3; decide
          · have := ih (by omega) (by omega) (by omega) (by omega)
            rw [Nat.pow_succ]; omega
      have hmin : min (2 ^ e) (3 + e) = 3 + e := Nat.min_eq_right (Nat.le_of_lt hgt)
      rw [hmin]
      exact regime_III_carried_dominated (a := 7) (s := 3) (e := e) (m := m)
        (by decide) he ha7 hm hgt

/-- Sharpness C3: Threshold `B < 2^(2^e)` for root invariance is sharp at `a = 3, e = 2` (`2^4 = 16`):
    `B = 15` preserves the root (`6`), while `B = 17` flips bit 0 (`1 ≠ 0`). -/
theorem sharpness_C3_threshold_16 :
    henselLift (F_bridge 3 2 15) 5 3 = henselLift (F_bridge 3 2 1) 5 3 ∧
    henselLift (F_bridge 3 2 17) 5 1 ≠ henselLift (F_bridge 3 2 1) 5 1 := by
  decide

/-- Sharpness C4: Naive parity-invariance `v_2(a^(2m+1) - clpow) = v_2(a^(2m) - clpow)` fails
    at the exact bit-4 threshold `a = 19 = 16 + 3, k = 4 vs 5`: `2^8 ‖ (19^4 - clpow)` vs `2^5 ‖ (19^5 - clpow)`. -/
theorem sharpness_C4_odd_parity_break :
    exactPow2 8 (((19 ^ 4 : Nat) : Int) - (clpow 19 4 : Int)) ∧
    exactPow2 5 (((19 ^ 5 : Nat) : Int) - (clpow 19 5 : Int)) := by
  have h4 : ((19 ^ 4 : Nat) : Int) - (clpow 19 4 : Int) = 64768 := by decide
  have h5 : ((19 ^ 5 : Nat) : Int) - (clpow 19 5 : Int) = 1230624 := by decide
  rw [h4, h5, exactPow2_iff_odd_mul, exactPow2_iff_odd_mul]
  exact ⟨⟨253, by decide, by decide⟩, ⟨38457, by decide, by decide⟩⟩

/-- Sharpness C5: Exponent shift `c = 2` breaks base divisibility at `a = 3, e = 2` (`2^2 ‖ (3^6 - clpow(3,6))`). -/
theorem sharpness_C5_shift_c2 :
    exactPow2 2 (((3 ^ 6 : Nat) : Int) - (clpow 3 6 : Int)) := by
  have : ((3 ^ 6 : Nat) : Int) - (clpow 3 6 : Int) = 644 := by decide
  rw [this, exactPow2_iff_odd_mul]
  exact ⟨161, by decide, by decide⟩

/-- Sharpness C6: Even multiplier `B = 2` breaks the scale-`5` isometry (`2^6 ∣ (F(1) - F(0))`). -/
theorem sharpness_C6_even_B_breaks_scale :
    ¬ exactPow2 5 (F_bridge 3 2 2 1 - F_bridge 3 2 2 0) := by
  have hval : F_bridge 3 2 2 1 - F_bridge 3 2 2 0 = 1054016 := by decide
  rw [hval]
  intro h
  exact h.2 ⟨16469, by decide⟩

end SiliconPolyBridge
