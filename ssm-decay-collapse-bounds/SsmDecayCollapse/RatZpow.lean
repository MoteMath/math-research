/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SsmDecayCollapse.Defs

/-!
# Pure-`Init` Rational Powers of Two, Exact Binades, and RNE Rounding Algebra

Establishes the foundational algebraic lemmas for `zpow2`, `binadeOf`, `rneInt`,
`floatVal`, and `ieeeRne` using only Lean 4 `Init`.
-/

namespace SsmDecayCollapse

/-! ### Basic `Rat` order and arithmetic helpers -/

theorem rat_mul_nonneg {a b : Rat} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  have h := Rat.mul_le_mul_of_nonneg_left hb ha
  simpa using h

theorem rat_mul_pos {a b : Rat} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  have h := Rat.mul_lt_mul_of_pos_left hb ha
  simpa using h

theorem rat_mul_le_mul_of_nonneg_right {a b c : Rat} (hab : a ≤ b) (hc : 0 ≤ c) :
    a * c ≤ b * c := by
  rw [Rat.mul_comm a c, Rat.mul_comm b c]
  exact Rat.mul_le_mul_of_nonneg_left hab hc

theorem rat_mul_lt_mul_of_pos_right {a b c : Rat} (hab : a < b) (hc : 0 < c) :
    a * c < b * c := by
  rw [Rat.mul_comm a c, Rat.mul_comm b c]
  exact Rat.mul_lt_mul_of_pos_left hab hc

theorem rat_inv_pos {a : Rat} (ha : 0 < a) : 0 < a⁻¹ := by
  have hne : a ≠ 0 := by grind
  have hmul : a * a⁻¹ = 1 := Rat.mul_inv_cancel a hne
  rcases @Rat.le_total a⁻¹ 0 with hle | hge
  · have h1 : a * a⁻¹ ≤ a * 0 := Rat.mul_le_mul_of_nonneg_left hle (by grind)
    grind
  · have hne' : a⁻¹ ≠ 0 := by
      intro h0
      rw [h0] at hmul
      grind
    grind

theorem rat_div_pos {a b : Rat} (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  rw [Rat.div_def]
  exact rat_mul_pos ha (rat_inv_pos hb)

theorem rat_div_le_iff {a b c : Rat} (hc : 0 < c) : a / c ≤ b ↔ a ≤ b * c := by
  have hne : c ≠ 0 := by grind
  constructor
  · intro h
    have h1 := rat_mul_le_mul_of_nonneg_right h (by grind : (0 : Rat) ≤ c)
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel c hne] at h1
    simpa using h1
  · intro h
    have hinv : 0 < c⁻¹ := rat_inv_pos hc
    have h1 := rat_mul_le_mul_of_nonneg_right h (by grind : (0 : Rat) ≤ c⁻¹)
    rw [Rat.mul_assoc, Rat.mul_inv_cancel c hne] at h1
    rw [Rat.div_def]
    simpa using h1

theorem rat_le_div_iff {a b c : Rat} (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b := by
  have hne : c ≠ 0 := by grind
  constructor
  · intro h
    have h1 := rat_mul_le_mul_of_nonneg_right h (by grind : (0 : Rat) ≤ c)
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel c hne] at h1
    simpa using h1
  · intro h
    have hinv : 0 < c⁻¹ := rat_inv_pos hc
    have h1 := rat_mul_le_mul_of_nonneg_right h (by grind : (0 : Rat) ≤ c⁻¹)
    rw [Rat.mul_assoc, Rat.mul_inv_cancel c hne] at h1
    rw [Rat.div_def]
    simpa using h1

theorem rat_div_lt_iff {a b c : Rat} (hc : 0 < c) : a / c < b ↔ a < b * c := by
  have hne : c ≠ 0 := by grind
  constructor
  · intro h
    have h1 := rat_mul_lt_mul_of_pos_right h hc
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel c hne] at h1
    simpa using h1
  · intro h
    have hinv : 0 < c⁻¹ := rat_inv_pos hc
    have h1 := rat_mul_lt_mul_of_pos_right h hinv
    rw [Rat.mul_assoc, Rat.mul_inv_cancel c hne] at h1
    rw [Rat.div_def]
    simpa using h1

theorem rat_lt_div_iff {a b c : Rat} (hc : 0 < c) : a < b / c ↔ a * c < b := by
  have hne : c ≠ 0 := by grind
  constructor
  · intro h
    have h1 := rat_mul_lt_mul_of_pos_right h hc
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel c hne] at h1
    simpa using h1
  · intro h
    have hinv : 0 < c⁻¹ := rat_inv_pos hc
    have h1 := rat_mul_lt_mul_of_pos_right h hinv
    rw [Rat.mul_assoc, Rat.mul_inv_cancel c hne] at h1
    rw [Rat.div_def]
    simpa using h1

theorem rat_natCast_pos {n : Nat} (hn : 0 < n) : (0 : Rat) < (n : Rat) := by
  exact Rat.natCast_lt_natCast.mpr hn

theorem rat_intCast_lt_iff {a b : Int} : (a : Rat) < (b : Rat) ↔ a < b :=
  Rat.intCast_lt_intCast

theorem rat_intCast_le_iff {a b : Int} : (a : Rat) ≤ (b : Rat) ↔ a ≤ b :=
  Rat.intCast_le_intCast

theorem rat_eq_num_div_den (q : Rat) : q = (q.num : Rat) / ((q.den : Int) : Rat) :=
  calc
    q = mkRat q.num q.den := (Rat.mkRat_self q).symm
    _ = Rat.divInt q.num (q.den : Int) := rfl
    _ = (q.num : Rat) / ((q.den : Int) : Rat) := Rat.divInt_eq_div q.num (q.den : Int)

theorem int_lt_of_mul_lt_mul_right {a b d : Int} (hd : 0 < d) (h : a * d < b * d) : a < b := by
  by_cases hlt : a < b
  · exact hlt
  · have hge : b ≤ a := by omega
    have hle : b * d ≤ a * d := Int.mul_le_mul_of_nonneg_right hge (by omega)
    omega

theorem ratAbs_of_nonneg {x : Rat} (hx : 0 ≤ x) : ratAbs x = x := by
  unfold ratAbs
  simp [hx]

theorem rat_mul_inv_eq {a b : Rat} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  have hne : a * b ≠ 0 := by
    intro h0
    have h1 : a⁻¹ * (a * b) = 0 := by rw [h0]; simp
    rw [← Rat.mul_assoc, Rat.inv_mul_cancel a ha, Rat.one_mul] at h1
    exact hb h1
  have hmul : (a * b) * (b⁻¹ * a⁻¹) = 1 := by
    rw [Rat.mul_assoc, ← Rat.mul_assoc b b⁻¹, Rat.mul_inv_cancel b hb, Rat.one_mul,
      Rat.mul_inv_cancel a ha]
  have h1 : (a * b)⁻¹ * ((a * b) * (b⁻¹ * a⁻¹)) = (a * b)⁻¹ := by
    rw [hmul, Rat.mul_one]
  rw [← Rat.mul_assoc, Rat.inv_mul_cancel (a * b) hne, Rat.one_mul] at h1
  exact h1.symm

/-! ### `zpow2` algebra -/

theorem nat_two_pow_pos (n : Nat) : 0 < 2 ^ n :=
  Nat.pow_pos (by decide : 0 < 2)

theorem rat_two_pow_pos (n : Nat) : (0 : Rat) < ((2 ^ n : Nat) : Rat) :=
  rat_natCast_pos (nat_two_pow_pos n)

theorem rat_two_pow_ne_zero (n : Nat) : ((2 ^ n : Nat) : Rat) ≠ 0 := by
  have := rat_two_pow_pos n
  grind

theorem zpow2_ofNat (n : Nat) : zpow2 (n : Int) = ((2 ^ n : Nat) : Rat) := by
  unfold zpow2
  have h : (0 : Int) ≤ (n : Int) := Int.natCast_nonneg n
  simp [h]

theorem zpow2_neg_ofNat (n : Nat) : zpow2 (-(n : Int)) = (1 : Rat) / ((2 ^ n : Nat) : Rat) := by
  cases n with
  | zero =>
    unfold zpow2
    simp
    grind
  | succ k =>
    unfold zpow2
    have h : ¬ ((0 : Int) ≤ -((k + 1 : Nat) : Int)) := by omega
    simp only [h, ↓reduceIte]
    have hto : (- -((k + 1 : Nat) : Int)).toNat = k + 1 := by omega
    rw [hto]

theorem zpow2_zero : zpow2 0 = 1 := by
  unfold zpow2
  decide

theorem zpow2_pos (k : Int) : 0 < zpow2 k := by
  unfold zpow2
  split
  · exact rat_two_pow_pos k.toNat
  · exact rat_div_pos (by decide) (rat_two_pow_pos (-k).toNat)

theorem zpow2_ne_zero (k : Int) : zpow2 k ≠ 0 := by
  have := zpow2_pos k
  grind

theorem zpow2_neg (k : Int) : zpow2 (-k) = (zpow2 k)⁻¹ := by
  by_cases hk : 0 ≤ k
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [zpow2_ofNat, zpow2_neg_ofNat, Rat.div_def]
    simp
  · have hnk : 0 ≤ -k := by omega
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hnk
    have hk' : k = -(n : Int) := by omega
    rw [hk', Int.neg_neg, zpow2_ofNat, zpow2_neg_ofNat, Rat.div_def]
    simp [Rat.inv_inv]

theorem zpow2_add_one (k : Int) : zpow2 (k + 1) = zpow2 k * 2 := by
  by_cases hk : 0 ≤ k
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    have h1 : ((n : Int) + 1) = ((n + 1 : Nat) : Int) := by omega
    rw [h1, zpow2_ofNat, zpow2_ofNat, Nat.pow_succ, Rat.natCast_mul]
    simp
  · have hnk : 0 < -k := by omega
    obtain ⟨m, hm⟩ : ∃ m : Nat, k = -((m + 1 : Nat) : Int) := by
      refine ⟨(-k - 1).toNat, ?_⟩
      omega
    rw [hm]
    have h1 : -((m + 1 : Nat) : Int) + 1 = -(m : Int) := by omega
    rw [h1, zpow2_neg_ofNat, zpow2_neg_ofNat]
    have hne1 : ((2 ^ m : Nat) : Rat) ≠ 0 := rat_two_pow_ne_zero m
    have hpow : ((2 ^ (m + 1) : Nat) : Rat) = ((2 ^ m : Nat) : Rat) * 2 := by
      rw [Nat.pow_succ, Rat.natCast_mul]
      simp
    rw [Rat.div_def, Rat.div_def, hpow, Rat.one_mul, Rat.one_mul]
    rw [rat_mul_inv_eq hne1 (by decide : (2 : Rat) ≠ 0)]
    rw [Rat.mul_comm (2 : Rat)⁻¹ _, Rat.mul_assoc, Rat.inv_mul_cancel (2 : Rat) (by decide),
      Rat.mul_one]

theorem zpow2_sub_one (k : Int) : zpow2 (k - 1) = zpow2 k / 2 := by
  have h := zpow2_add_one (k - 1)
  have heq : k - 1 + 1 = k := by omega
  rw [heq] at h
  rw [h, Rat.div_def, Rat.mul_assoc, Rat.mul_inv_cancel (2 : Rat) (by decide)]
  simp

theorem zpow2_add_ofNat (a : Int) (n : Nat) : zpow2 (a + (n : Int)) = zpow2 a * zpow2 (n : Int) := by
  induction n with
  | zero =>
    simp [zpow2_zero]
  | succ k ih =>
    have h1 : a + ((k + 1 : Nat) : Int) = (a + (k : Int)) + 1 := by omega
    have h2 : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
    rw [h1, zpow2_add_one, ih, h2, zpow2_add_one, Rat.mul_assoc]

theorem zpow2_add_negOfNat (a : Int) (n : Nat) :
    zpow2 (a + -(n : Int)) = zpow2 a * zpow2 (-(n : Int)) := by
  induction n with
  | zero =>
    simp [zpow2_zero]
  | succ k ih =>
    have h1 : a + -((k + 1 : Nat) : Int) = (a + -(k : Int)) - 1 := by omega
    have h2 : -((k + 1 : Nat) : Int) = -(k : Int) - 1 := by omega
    rw [h1, zpow2_sub_one, ih, h2, zpow2_sub_one]
    rw [Rat.div_def, Rat.div_def, Rat.mul_assoc]

theorem zpow2_add (a b : Int) : zpow2 (a + b) = zpow2 a * zpow2 b := by
  by_cases hb : 0 ≤ b
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hb
    exact zpow2_add_ofNat a n
  · have hnb : 0 ≤ -b := by omega
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hnb
    have hb' : b = -(n : Int) := by omega
    rw [hb']
    exact zpow2_add_negOfNat a n

theorem zpow2_sub (a b : Int) : zpow2 (a - b) = zpow2 a / zpow2 b := by
  have h : a - b = a + (-b) := by omega
  rw [h, zpow2_add, zpow2_neg, Rat.div_def]

theorem zpow2_mul_cancel (a : Int) : zpow2 a * zpow2 (-a) = 1 := by
  rw [← zpow2_add]
  have h : a + -a = 0 := by omega
  rw [h, zpow2_zero]

theorem zpow2_lt_zpow2 {a b : Int} (h : a < b) : zpow2 a < zpow2 b := by
  obtain ⟨n, hn⟩ : ∃ n : Nat, b - a = ((n + 1 : Nat) : Int) := by
    refine ⟨(b - a - 1).toNat, ?_⟩
    omega
  have hb : b = a + ((n + 1 : Nat) : Int) := by omega
  rw [hb, zpow2_add, zpow2_ofNat]
  have h2 : (1 : Rat) < ((2 ^ (n + 1) : Nat) : Rat) := by
    have hnat : 1 < 2 ^ (n + 1) := by
      have hp : 1 ≤ 2 ^ n := nat_two_pow_pos n
      rw [Nat.pow_succ]
      omega
    exact Rat.natCast_lt_natCast.mpr hnat
  have hmul := Rat.mul_lt_mul_of_pos_left h2 (zpow2_pos a)
  simpa using hmul

theorem zpow2_le_zpow2 {a b : Int} (h : a ≤ b) : zpow2 a ≤ zpow2 b := by
  rcases Int.lt_or_eq_of_le h with hlt | rfl
  · exact Rat.le_of_lt (zpow2_lt_zpow2 hlt)
  · exact Rat.le_refl

/-! ### Exactness and uniqueness of `binadeOf` -/

theorem nat_pow_log2_le {n : Nat} (hn : 0 < n) : 2 ^ Nat.log2 n ≤ n :=
  (Nat.le_log2 (Nat.ne_of_gt hn)).mp (Nat.le_refl _)

theorem nat_lt_pow_log2_succ (n : Nat) : n < 2 ^ (Nat.log2 n + 1) :=
  Nat.lt_log2_self

theorem binadeOf_spec {x : Rat} (hx : 0 < x) :
    zpow2 (binadeOf x) ≤ x ∧ x < zpow2 (binadeOf x + 1) := by
  have hden_pos : (0 : Rat) < (x.den : Rat) := rat_natCast_pos (Nat.pos_of_ne_zero x.den_nz)
  have hnum_pos : 0 < x.num := by
    have hx' : (0 : Rat) < (x.num : Rat) / (x.den : Rat) := by
      rw [rat_eq_num_div_den x, Rat.intCast_natCast] at hx
      exact hx
    have h1 := (rat_lt_div_iff hden_pos).mp hx'
    simp at h1
    exact rat_intCast_lt_iff.mp h1
  have hna_pos : 0 < x.num.toNat := by omega
  have hnb_pos : 0 < x.den := Nat.pos_of_ne_zero x.den_nz
  have hnum_eq : (x.num : Rat) = ((x.num.toNat : Nat) : Rat) := by
    have : x.num = (x.num.toNat : Int) := by omega
    rw [this]
    rfl
  have ha_lo : ((2 ^ Nat.log2 x.num.toNat : Nat) : Rat) ≤ (x.num : Rat) := by
    rw [hnum_eq]
    exact Rat.natCast_le_natCast.mpr (nat_pow_log2_le hna_pos)
  have ha_hi : (x.num : Rat) < ((2 ^ (Nat.log2 x.num.toNat + 1) : Nat) : Rat) := by
    rw [hnum_eq]
    exact Rat.natCast_lt_natCast.mpr (nat_lt_pow_log2_succ x.num.toNat)
  have hb_lo : ((2 ^ Nat.log2 x.den : Nat) : Rat) ≤ (x.den : Rat) :=
    Rat.natCast_le_natCast.mpr (nat_pow_log2_le hnb_pos)
  have hb_hi : (x.den : Rat) < ((2 ^ (Nat.log2 x.den + 1) : Nat) : Rat) :=
    Rat.natCast_lt_natCast.mpr (nat_lt_pow_log2_succ x.den)
  let k0 : Int := (Nat.log2 x.num.toNat : Int) - (Nat.log2 x.den : Int)
  have hlo : zpow2 (k0 - 1) < x := by
    rw [rat_eq_num_div_den x, Rat.intCast_natCast, rat_lt_div_iff hden_pos]
    have heq : k0 - 1 = (Nat.log2 x.num.toNat : Int) - ((Nat.log2 x.den + 1 : Nat) : Int) := by
      dsimp only [k0]; omega
    rw [heq, zpow2_sub, zpow2_ofNat, zpow2_ofNat]
    have hpos := rat_div_pos (rat_two_pow_pos (Nat.log2 x.num.toNat)) (rat_two_pow_pos (Nat.log2 x.den + 1))
    have hmul := Rat.mul_lt_mul_of_pos_left hb_hi hpos
    have hcancel :
        ((2 ^ Nat.log2 x.num.toNat : Nat) : Rat) / ((2 ^ (Nat.log2 x.den + 1) : Nat) : Rat) *
          ((2 ^ (Nat.log2 x.den + 1) : Nat) : Rat) =
        ((2 ^ Nat.log2 x.num.toNat : Nat) : Rat) := by
      rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ (rat_two_pow_ne_zero _)]
      simp
    rw [hcancel] at hmul
    grind
  have hhi : x < zpow2 (k0 + 1) := by
    rw [rat_eq_num_div_den x, Rat.intCast_natCast, rat_div_lt_iff hden_pos]
    have heq : k0 + 1 = ((Nat.log2 x.num.toNat + 1 : Nat) : Int) - (Nat.log2 x.den : Int) := by
      dsimp only [k0]; omega
    rw [heq, zpow2_sub, zpow2_ofNat, zpow2_ofNat]
    have hpos := rat_div_pos (rat_two_pow_pos (Nat.log2 x.num.toNat + 1)) (rat_two_pow_pos (Nat.log2 x.den))
    have hmul := Rat.mul_le_mul_of_nonneg_left hb_lo (Rat.le_of_lt hpos)
    have hcancel :
        ((2 ^ (Nat.log2 x.num.toNat + 1) : Nat) : Rat) / ((2 ^ Nat.log2 x.den : Nat) : Rat) *
          ((2 ^ Nat.log2 x.den : Nat) : Rat) =
        ((2 ^ (Nat.log2 x.num.toNat + 1) : Nat) : Rat) := by
      rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ (rat_two_pow_ne_zero _)]
      simp
    rw [hcancel] at hmul
    grind
  unfold binadeOf
  change zpow2 (if x < zpow2 k0 then k0 - 1 else k0) ≤ x ∧
    x < zpow2 ((if x < zpow2 k0 then k0 - 1 else k0) + 1)
  by_cases hlt : x < zpow2 k0
  · simp only [hlt, ↓reduceIte]
    have hk : k0 - 1 + 1 = k0 := by omega
    rw [hk]
    exact ⟨Rat.le_of_lt hlo, hlt⟩
  · simp only [hlt, ↓reduceIte]
    have hle : zpow2 k0 ≤ x := by grind
    exact ⟨hle, hhi⟩

theorem binadeOf_eq_of_bounds {x : Rat} {k : Int} (hlo : zpow2 k ≤ x) (hhi : x < zpow2 (k + 1)) :
    binadeOf x = k := by
  have hzk : 0 < zpow2 k := zpow2_pos k
  have hx : 0 < x := by grind
  have ⟨hblo, hbhi⟩ := binadeOf_spec hx
  let b := binadeOf x
  change b = k
  by_cases hlt : b < k
  · have hle : b + 1 ≤ k := by omega
    have h1 : zpow2 (b + 1) ≤ zpow2 k := zpow2_le_zpow2 hle
    grind
  · by_cases hgt : k < b
    · have hle : k + 1 ≤ b := by omega
      have h1 : zpow2 (k + 1) ≤ zpow2 b := zpow2_le_zpow2 hle
      grind
    · omega

/-! ### Exact characterization of `rneInt` -/

theorem rneInt_floor_spec (q : Rat) :
    let d : Int := (q.den : Int)
    let fl : Int := q.num.ediv d
    let rem : Int := q.num.emod d
    0 < d ∧ 0 ≤ rem ∧ rem < d ∧ q.num = d * fl + rem := by
  dsimp only
  have hd_pos : (0 : Int) < (q.den : Int) := by
    have := Nat.pos_of_ne_zero q.den_nz
    omega
  refine ⟨hd_pos, Int.emod_nonneg q.num (by omega), Int.emod_lt_of_pos q.num hd_pos, ?_⟩
  exact (Int.mul_ediv_add_emod q.num (q.den : Int)).symm

theorem rneInt_eq_of_bounds {q : Rat} {n : Int}
    (hlo : (n : Rat) - 1 / 2 < q) (hhi : q < (n : Rat) + 1 / 2) :
    rneInt q = n := by
  have ⟨hd_pos, hrem_lo, hrem_hi, hdiv⟩ := rneInt_floor_spec q
  let d : Int := (q.den : Int)
  let fl : Int := q.num.ediv d
  let rem : Int := q.num.emod d
  have hden_rat_pos : (0 : Rat) < (d : Rat) := rat_intCast_lt_iff.mpr hd_pos
  have hq : q = (q.num : Rat) / (d : Rat) := rat_eq_num_div_den q
  rw [hq] at hlo hhi
  have hlo' : ((n : Rat) - 1 / 2) * (d : Rat) < (q.num : Rat) := (rat_lt_div_iff hden_rat_pos).mp hlo
  have hhi' : (q.num : Rat) < ((n : Rat) + 1 / 2) * (d : Rat) := (rat_div_lt_iff hden_rat_pos).mp hhi
  have hlo2 : (2 * n - 1 : Int) * d < 2 * q.num := by
    have h2 : (((2 * n - 1 : Int) * d : Int) : Rat) < ((2 * q.num : Int) : Rat) := by
      push_cast
      grind
    exact rat_intCast_lt_iff.mp h2
  have hhi2 : 2 * q.num < (2 * n + 1 : Int) * d := by
    have h2 : ((2 * q.num : Int) : Rat) < (((2 * n + 1 : Int) * d : Int) : Rat) := by
      push_cast
      grind
    exact rat_intCast_lt_iff.mp h2
  have hdiv' : q.num = d * fl + rem := hdiv
  have hrem_lo' : 0 ≤ rem := hrem_lo
  have hrem_hi' : rem < d := hrem_hi
  rw [hdiv'] at hlo2 hhi2
  unfold rneInt
  change (if 2 * rem < d then fl else if d < 2 * rem then fl + 1 else if fl % 2 == 0 then fl else fl + 1) = n
  by_cases h1 : 2 * rem < d
  · simp only [h1, ↓reduceIte]
    have ha : (2 * n - 1) * d < (2 * fl + 1) * d := by
      have hm : (2 * fl + 1) * d = 2 * (d * fl) + d := by grind
      omega
    have hb : (2 * fl) * d < (2 * n + 1) * d := by
      have hm : (2 * fl) * d = 2 * (d * fl) := by grind
      omega
    have h1' := int_lt_of_mul_lt_mul_right hd_pos ha
    have h2' := int_lt_of_mul_lt_mul_right hd_pos hb
    omega
  · by_cases h2 : d < 2 * rem
    · simp only [h1, h2, ↓reduceIte]
      have ha : (2 * n - 1) * d < (2 * (fl + 1)) * d := by
        have hm : (2 * (fl + 1)) * d = 2 * (d * fl) + 2 * d := by grind
        omega
      have hb : (2 * fl + 1) * d < (2 * n + 1) * d := by
        have hm : (2 * fl + 1) * d = 2 * (d * fl) + d := by grind
        omega
      have h1' := int_lt_of_mul_lt_mul_right hd_pos ha
      have h2' := int_lt_of_mul_lt_mul_right hd_pos hb
      omega
    · exfalso
      have heq : 2 * rem = d := by omega
      have hmul : 2 * (d * fl + rem) = (2 * fl + 1) * d := by grind
      rw [hmul] at hlo2 hhi2
      have h1' := int_lt_of_mul_lt_mul_right hd_pos hlo2
      have h2' := int_lt_of_mul_lt_mul_right hd_pos hhi2
      omega

theorem rneInt_of_int (n : Int) : rneInt (n : Rat) = n :=
  rneInt_eq_of_bounds (by grind) (by grind)

theorem rneInt_midpoint (n : Int) :
    rneInt ((n : Rat) + 1 / 2) = if n % 2 == 0 then n else n + 1 := by
  let q : Rat := (n : Rat) + 1 / 2
  have ⟨hd_pos, hrem_lo, hrem_hi, hdiv⟩ := rneInt_floor_spec q
  let d : Int := (q.den : Int)
  let fl : Int := q.num.ediv d
  let rem : Int := q.num.emod d
  have hq : (q.num : Rat) / (d : Rat) = (n : Rat) + 1 / 2 := (rat_eq_num_div_den q).symm
  have hmul : (q.num : Rat) = ((n : Rat) + 1 / 2) * (d : Rat) := by
    have hden_rat_pos : (0 : Rat) < (d : Rat) := rat_intCast_lt_iff.mpr hd_pos
    have hne : (d : Rat) ≠ 0 := by grind
    rw [← hq, Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ hne]
    simp
  have h2eq : 2 * q.num = (2 * n + 1) * d := by
    have hrat : ((2 * q.num : Int) : Rat) = (((2 * n + 1) * d : Int) : Rat) := by
      push_cast
      rw [hmul]
      grind
    exact Rat.intCast_inj.mp hrat
  have hdiv' : q.num = d * fl + rem := hdiv
  have hrem_lo' : 0 ≤ rem := hrem_lo
  have hrem_hi' : rem < d := hrem_hi
  rw [hdiv'] at h2eq
  have hfl : fl = n := by
    have ha : (2 * fl) * d < (2 * n + 2) * d := by
      have hm1 : (2 * fl) * d = 2 * (d * fl) := by grind
      have hm2 : (2 * n + 2) * d = (2 * n + 1) * d + d := by grind
      omega
    have hb : (2 * n) * d < (2 * fl + 2) * d := by
      have hm1 : (2 * fl + 2) * d = 2 * (d * fl) + 2 * d := by grind
      have hm2 : (2 * n + 1) * d = (2 * n) * d + d := by grind
      omega
    have h1' := int_lt_of_mul_lt_mul_right hd_pos ha
    have h2' := int_lt_of_mul_lt_mul_right hd_pos hb
    omega
  have hrem : 2 * rem = d := by
    rw [hfl] at h2eq
    have hm : (2 * n + 1) * d = 2 * (d * n) + d := by grind
    omega
  unfold rneInt
  change (if 2 * rem < d then fl else if d < 2 * rem then fl + 1 else if fl % 2 == 0 then fl else fl + 1) =
    if n % 2 == 0 then n else n + 1
  have h1 : ¬ (2 * rem < d) := by omega
  have h2 : ¬ (d < 2 * rem) := by omega
  simp [h1, h2, hfl]

/-! ### `ieeeRne` and `floatVal` helpers -/

theorem floatVal_pos (p : Nat) (k : Int) (m : Nat) : 0 < floatVal p k m := by
  unfold floatVal
  have h1 : 0 < 2 ^ p + m := Nat.lt_of_lt_of_le (nat_two_pow_pos p) (Nat.le_add_right _ _)
  exact rat_mul_pos (rat_natCast_pos h1) (zpow2_pos _)

theorem floatVal_bounds (p : Nat) (k : Int) (m : Nat) (hm : m < 2 ^ p) :
    zpow2 k ≤ floatVal p k m ∧ floatVal p k m < zpow2 (k + 1) := by
  unfold floatVal
  have hsub : zpow2 k = ((2 ^ p : Nat) : Rat) * zpow2 (k - (p : Int)) := by
    have heq : k = (p : Int) + (k - (p : Int)) := by omega
    rw [heq, zpow2_add, zpow2_ofNat]
    have heq2 : (p : Int) + (k - (p : Int)) - (p : Int) = k - (p : Int) := by omega
    rw [heq2]
  have hsub1 : zpow2 (k + 1) = ((2 ^ (p + 1) : Nat) : Rat) * zpow2 (k - (p : Int)) := by
    have heq : k + 1 = ((p + 1 : Nat) : Int) + (k - (p : Int)) := by omega
    rw [heq, zpow2_add, zpow2_ofNat]
  constructor
  · rw [hsub]
    have hle : ((2 ^ p : Nat) : Rat) ≤ ((2 ^ p + m : Nat) : Rat) :=
      Rat.natCast_le_natCast.mpr (Nat.le_add_right _ _)
    exact rat_mul_le_mul_of_nonneg_right hle (Rat.le_of_lt (zpow2_pos _))
  · rw [hsub1]
    have hlt : ((2 ^ p + m : Nat) : Rat) < ((2 ^ (p + 1) : Nat) : Rat) := by
      apply Rat.natCast_lt_natCast.mpr
      rw [Nat.pow_succ]
      omega
    exact rat_mul_lt_mul_of_pos_right hlt (zpow2_pos _)

theorem binadeOf_floatVal (p : Nat) (k : Int) (m : Nat) (hm : m < 2 ^ p) :
    binadeOf (floatVal p k m) = k :=
  binadeOf_eq_of_bounds (floatVal_bounds p k m hm).1 (floatVal_bounds p k m hm).2

theorem ieeeRne_eq_of_binade (p : Nat) {x : Rat} {k : Int}
    (hlo : zpow2 k ≤ x) (hhi : x < zpow2 (k + 1)) :
    ieeeRne p x = (rneInt (x * zpow2 ((p : Int) - k)) : Rat) * zpow2 (k - (p : Int)) := by
  have hzk : 0 < zpow2 k := zpow2_pos k
  have hx : 0 < x := by grind
  have hb : binadeOf x = k := binadeOf_eq_of_bounds hlo hhi
  unfold ieeeRne
  simp [hx, hb]

theorem ieeeRne_floatVal (p : Nat) (k : Int) (m : Nat) (hm : m < 2 ^ p) :
    ieeeRne p (floatVal p k m) = floatVal p k m := by
  have hb := floatVal_bounds p k m hm
  rw [ieeeRne_eq_of_binade p hb.1 hb.2]
  unfold floatVal
  rw [Rat.mul_assoc]
  have hcancel : zpow2 (k - (p : Int)) * zpow2 ((p : Int) - k) = 1 := by
    rw [← zpow2_add]
    have h0 : k - (p : Int) + ((p : Int) - k) = 0 := by omega
    rw [h0, zpow2_zero]
  rw [hcancel, Rat.mul_one]
  have hcast : (((2 ^ p + m : Nat) : Rat)) = (((2 ^ p + m : Nat) : Int) : Rat) := by rfl
  rw [hcast, rneInt_of_int]

theorem floatVal_zero (p : Nat) (k : Int) : floatVal p k 0 = zpow2 k := by
  unfold floatVal
  simp only [Nat.add_zero]
  rw [← zpow2_ofNat p, ← zpow2_add]
  have h : (p : Int) + (k - (p : Int)) = k := by omega
  rw [h]

theorem ieeeRne_zpow2 (p : Nat) (k : Int) : ieeeRne p (zpow2 k) = zpow2 k := by
  rw [← floatVal_zero p k]
  exact ieeeRne_floatVal p k 0 (nat_two_pow_pos p)

theorem ieeeRne_one (p : Nat) : ieeeRne p 1 = 1 := by
  simpa [zpow2_zero] using ieeeRne_zpow2 p 0

end SsmDecayCollapse
