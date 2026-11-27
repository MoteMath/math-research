import DyadicBallContractionCompiler.Defs

namespace DyadicCompiler
namespace ExactQ
theorem den_int_pos (a : ExactQ) : (0 : Int) < (a.den : Int) := by
  have := a.den_pos; omega

theorem den_int_ne_zero (a : ExactQ) : (a.den : Int) ≠ 0 := by
  have := den_int_pos a; omega

theorem equiv_refl (a : ExactQ) : equiv a a := rfl
theorem equiv_symm {a b : ExactQ} (h : equiv a b) : equiv b a := h.symm

theorem equiv_trans {a b c : ExactQ} (hab : equiv a b) (hbc : equiv b c) : equiv a c := by
  unfold equiv at *
  have h1 : a.num * (c.den : Int) * (b.den : Int) = c.num * (a.den : Int) * (b.den : Int) := by grind
  exact Int.eq_of_mul_eq_mul_right (den_int_ne_zero b) h1

theorem le_refl (a : ExactQ) : le a a := Int.le_refl _

theorem le_trans {a b c : ExactQ} (hab : le a b) (hbc : le b c) : le a c := by
  unfold le at *
  have hb := den_int_pos b
  have ha := Int.le_of_lt (den_int_pos a)
  have hc := Int.le_of_lt (den_int_pos c)
  have h1 := Int.mul_le_mul_of_nonneg_right hab hc
  have h2 := Int.mul_le_mul_of_nonneg_right hbc ha
  have h3 : a.num * (c.den : Int) * (b.den : Int) ≤ c.num * (a.den : Int) * (b.den : Int) := by grind
  exact Int.le_of_mul_le_mul_right h3 hb

theorem le_of_equiv {a b : ExactQ} (h : equiv a b) : le a b := by
  unfold le; rw [h]; exact Int.le_refl _

theorem equiv_of_le_antisymm {a b : ExactQ} (h1 : le a b) (h2 : le b a) : equiv a b := by
  unfold equiv le at *; omega

theorem le_congr_left {a a' b : ExactQ} (heq : equiv a a') (h : le a b) : le a' b :=
  le_trans (le_of_equiv (equiv_symm heq)) h

theorem le_congr_right {a b b' : ExactQ} (heq : equiv b b') (h : le a b) : le a b' :=
  le_trans h (le_of_equiv heq)

theorem add_le_add {a b c d : ExactQ} (h1 : le a b) (h2 : le c d) : le (add a c) (add b d) := by
  unfold le add at *
  simp only [Int.natCast_mul]
  have ha := Int.le_of_lt (den_int_pos a)
  have hb := Int.le_of_lt (den_int_pos b)
  have hc := Int.le_of_lt (den_int_pos c)
  have hd := Int.le_of_lt (den_int_pos d)
  have h1' := Int.mul_le_mul_of_nonneg_right h1 (Int.mul_nonneg hc hd)
  have h2' := Int.mul_le_mul_of_nonneg_right h2 (Int.mul_nonneg ha hb)
  have hsum := Int.add_le_add h1' h2'
  grind

theorem mul_le_mul_of_nonneg_left {a b c : ExactQ} (hc : 0 ≤ c.num) (h : le a b) :
    le (mul c a) (mul c b) := by
  unfold le mul at *
  simp only [Int.natCast_mul]
  have h1 := Int.mul_le_mul_of_nonneg_left h (Int.mul_nonneg hc (Int.le_of_lt (den_int_pos c)))
  grind

theorem mul_le_mul_of_nonneg_right {a b c : ExactQ} (hc : 0 ≤ c.num) (h : le a b) :
    le (mul a c) (mul b c) := by
  unfold le mul at *
  simp only [Int.natCast_mul]
  have h1 := Int.mul_le_mul_of_nonneg_left h (Int.mul_nonneg hc (Int.le_of_lt (den_int_pos c)))
  grind

theorem mul_le_mul_nonneg {a b c d : ExactQ} (ha : 0 ≤ a.num) (hd : 0 ≤ d.num)
    (h1 : le a b) (h2 : le c d) : le (mul a c) (mul b d) :=
  le_trans (mul_le_mul_of_nonneg_left ha h2) (mul_le_mul_of_nonneg_right hd h1)

theorem abs_nonneg (a : ExactQ) : 0 ≤ (abs a).num := Int.natCast_nonneg _

theorem pow_nonneg {a : ExactQ} (ha : 0 ≤ a.num) : ∀ n, 0 ≤ (pow a n).num
  | 0 => by unfold pow ofInt; dsimp only; omega
  | n + 1 => by unfold pow mul; dsimp only; exact Int.mul_nonneg ha (pow_nonneg ha n)

theorem abs_mul_equiv (a b : ExactQ) : equiv (abs (mul a b)) (mul (abs a) (abs b)) := by
  unfold equiv abs mul
  simp only [Int.natAbs_mul, Int.natCast_mul]

theorem abs_add_le (a b : ExactQ) : le (abs (add a b)) (add (abs a) (abs b)) := by
  unfold le abs add
  simp only [Int.natCast_mul]
  have ha := Int.le_of_lt (den_int_pos a)
  have hb := Int.le_of_lt (den_int_pos b)
  have htri : ((a.num * (b.den : Int) + b.num * (a.den : Int)).natAbs : Int) ≤
              (a.num.natAbs : Int) * (b.den : Int) + (b.num.natAbs : Int) * (a.den : Int) := by
    have h1 : ((a.num * (b.den : Int)).natAbs : Int) = (a.num.natAbs : Int) * (b.den : Int) := by
      rw [Int.natAbs_mul, Int.natCast_mul, Int.natAbs_natCast]
    have h2 : ((b.num * (a.den : Int)).natAbs : Int) = (b.num.natAbs : Int) * (a.den : Int) := by
      rw [Int.natAbs_mul, Int.natCast_mul, Int.natAbs_natCast]
    have h3 := Int.natAbs_add_le (a.num * (b.den : Int)) (b.num * (a.den : Int))
    omega
  exact Int.mul_le_mul_of_nonneg_right htri (Int.mul_nonneg ha hb)

theorem dist_symm (a b : ExactQ) : equiv (dist a b) (dist b a) := by
  unfold equiv dist abs sub; dsimp only
  have hneg : (a.num * (b.den : Int) - b.num * (a.den : Int)).natAbs =
              (b.num * (a.den : Int) - a.num * (b.den : Int)).natAbs := by
    have : a.num * (b.den : Int) - b.num * (a.den : Int) = -(b.num * (a.den : Int) - a.num * (b.den : Int)) := by omega
    rw [this, Int.natAbs_neg]
  rw [hneg, Nat.mul_comm b.den a.den]

theorem abs_congr {a b : ExactQ} (h : equiv a b) : equiv (abs a) (abs b) := by
  unfold equiv abs at *
  have hnat : (a.num * (b.den : Int)).natAbs = (b.num * (a.den : Int)).natAbs := by rw [h]
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at hnat
  have hcast : ((a.num.natAbs * b.den : Nat) : Int) = ((b.num.natAbs * a.den : Nat) : Int) := by
    exact congrArg (fun n : Nat => (n : Int)) hnat
  simpa only [Int.natCast_mul] using hcast

theorem dist_triangle (a b c : ExactQ) : le (dist a c) (add (dist a b) (dist b c)) := by
  have hsub : equiv (sub a c) (add (sub a b) (sub b c)) := by
    unfold equiv sub add
    simp only [Int.natCast_mul]
    grind
  exact le_trans (le_of_equiv (abs_congr hsub)) (abs_add_le (sub a b) (sub b c))

theorem dist_eq_sub_of_le {a b : ExactQ} (h : le a b) : equiv (dist a b) (sub b a) := by
  unfold equiv dist abs sub le at *; dsimp only
  have h2 : ((a.num * (b.den : Int) - b.num * (a.den : Int)).natAbs : Int) =
            b.num * (a.den : Int) - a.num * (b.den : Int) := by omega
  rw [h2, Nat.mul_comm b.den a.den]

theorem equiv_of_dist_le_zero {a b : ExactQ} (h : le (dist a b) (ofInt 0)) : equiv a b := by
  unfold le dist abs sub ofInt equiv at *
  simp at h
  omega

theorem dist_congr {a a' b b' : ExactQ} (ha : equiv a a') (hb : equiv b b') :
    equiv (dist a b) (dist a' b') := by
  apply abs_congr
  unfold equiv sub at *
  simp only [Int.natCast_mul]
  grind

theorem mul_add_left_equiv (q a b : ExactQ) : equiv (add (mul q a) (mul q b)) (mul q (add a b)) := by
  unfold equiv add mul
  simp only [Int.natCast_mul]
  grind

theorem mul_assoc_equiv (a b c : ExactQ) : equiv (mul (mul a b) c) (mul a (mul b c)) := by
  unfold equiv mul; simp only [Int.natCast_mul]; grind

theorem mul_comm_equiv (a b : ExactQ) : equiv (mul a b) (mul b a) := by
  unfold equiv mul; simp only [Int.natCast_mul]; grind

theorem mul_congr {a a' b b' : ExactQ} (ha : equiv a a') (hb : equiv b b') :
    equiv (mul a b) (mul a' b') := by
  unfold equiv mul at *; simp only [Int.natCast_mul]; grind

theorem mul_one_left_equiv (a : ExactQ) : equiv (mul (ofInt 1) a) a := by
  unfold equiv mul ofInt; simp only [Int.natCast_mul]; grind

theorem mul_one_right_equiv (a : ExactQ) : equiv (mul a (ofInt 1)) a := by
  unfold equiv mul ofInt; simp only [Int.natCast_mul]; grind

theorem add_sub_equiv (a b c : ExactQ) (h : equiv (sub a b) c) : equiv a (add b c) := by
  unfold equiv sub add at *
  simp only [Int.natCast_mul] at *
  have h1 : a.num * ((b.den : Int) * (c.den : Int)) * (b.den : Int) =
            (b.num * (c.den : Int) + c.num * (b.den : Int)) * (a.den : Int) * (b.den : Int) := by grind
  exact Int.eq_of_mul_eq_mul_right (den_int_ne_zero b) h1

end ExactQ
namespace DyadicBall
theorem pow2_int_pos (k : Nat) : (0 : Int) < ((2 ^ k : Nat) : Int) := by
  have h : 0 < 2 ^ k := Nat.pow_pos (by omega)
  omega

theorem contains_congr {b : DyadicBall} {q1 q2 : ExactQ} (heq : q1.equiv q2) (h : b.contains q1) :
    b.contains q2 := by
  unfold contains ExactQ.equiv at *
  have hd1 := ExactQ.den_int_pos q1
  have hd2 := Int.le_of_lt (ExactQ.den_int_pos q2)
  constructor
  · have hmul := Int.mul_le_mul_of_nonneg_right h.1 hd2
    have hstep : (b.m - (b.r : Int)) * (q2.den : Int) * (q1.den : Int) ≤
                 q2.num * ((2 ^ b.e : Nat) : Int) * (q1.den : Int) := by grind
    exact Int.le_of_mul_le_mul_right hstep hd1
  · have hmul := Int.mul_le_mul_of_nonneg_right h.2 hd2
    have hstep : q2.num * ((2 ^ b.e : Nat) : Int) * (q1.den : Int) ≤
                 (b.m + (b.r : Int)) * (q2.den : Int) * (q1.den : Int) := by grind
    exact Int.le_of_mul_le_mul_right hstep hd1

theorem fromInterval_sound {lo hi : Int} {e : Nat} {q : ExactQ}
    (hlo : lo * (q.den : Int) ≤ q.num * ((2 ^ e : Nat) : Int))
    (hhi : q.num * ((2 ^ e : Nat) : Int) ≤ hi * (q.den : Int)) :
    (fromInterval lo hi e).contains q := by
  unfold fromInterval contains
  dsimp only
  have hle : lo ≤ hi := Int.le_of_mul_le_mul_right (Int.le_trans hlo hhi) (ExactQ.den_int_pos q)
  have hdiv : 2 * ((lo + hi) / 2) ≤ lo + hi ∧ lo + hi ≤ 2 * ((lo + hi) / 2) + 1 := by
    have hmod := Int.emod_nonneg (lo + hi) (by omega : (2 : Int) ≠ 0)
    have hmod2 := Int.emod_lt_of_pos (lo + hi) (by omega : (0 : Int) < 2)
    have hdecomp := Int.ediv_mul_add_emod (lo + hi) 2
    omega
  have hr_eq : ((hi - (lo + hi) / 2).toNat : Int) = hi - (lo + hi) / 2 := by omega
  rw [hr_eq]
  constructor
  · exact Int.le_trans (Int.mul_le_mul_of_nonneg_right (by omega) (Int.le_of_lt (ExactQ.den_int_pos q))) hlo
  · have h2 : (lo + hi) / 2 + (hi - (lo + hi) / 2) = hi := by omega
    rw [h2]; exact hhi

theorem roundTo_sound (b : DyadicBall) (p : Nat) (q : ExactQ) (hq : b.contains q) :
    (b.roundTo p).contains q := by
  unfold roundTo
  split
  · rename_i hle
    unfold contains at *
    have hpow : (2 ^ p : Nat) = 2 ^ b.e * 2 ^ (p - b.e) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' hle]
    have hs := Int.le_of_lt (pow2_int_pos (p - b.e))
    rw [hpow, Int.natCast_mul, Int.natCast_mul]
    have h1 := Int.mul_le_mul_of_nonneg_right hq.1 hs
    have h2 := Int.mul_le_mul_of_nonneg_right hq.2 hs
    constructor <;> grind
  · rename_i hgt
    have hlt : p < b.e := Nat.lt_of_not_ge hgt
    let s : Int := ((2 ^ (b.e - p) : Nat) : Int)
    have hs : 0 < s := pow2_int_pos (b.e - p)
    have hpow : ((2 ^ b.e : Nat) : Int) = ((2 ^ p : Nat) : Int) * s := by
      have : (2 ^ b.e : Nat) = 2 ^ p * 2 ^ (b.e - p) := by
        rw [← Nat.pow_add, Nat.add_sub_cancel' (Nat.le_of_lt hlt)]
      rw [this, Int.natCast_mul]
    have hlo_div : ((b.m - (b.r : Int)) / s) * s ≤ b.m - (b.r : Int) := by
      have hmod := Int.emod_nonneg (b.m - (b.r : Int)) (by omega : s ≠ 0)
      have hd := Int.ediv_mul_add_emod (b.m - (b.r : Int)) s
      omega
    have hhi_div : b.m + (b.r : Int) ≤ ((b.m + (b.r : Int) + s - 1) / s) * s := by
      have hmod := Int.emod_lt_of_pos (b.m + (b.r : Int) + s - 1) hs
      have hd := Int.ediv_mul_add_emod (b.m + (b.r : Int) + s - 1) s
      omega
    apply fromInterval_sound
    · have hmul := Int.mul_le_mul_of_nonneg_right hlo_div (Int.le_of_lt (ExactQ.den_int_pos q))
      have h1 : ((b.m - (b.r : Int)) / s) * (q.den : Int) * s ≤ q.num * ((2 ^ p : Nat) : Int) * s := by
        have := hq.1; grind
      exact Int.le_of_mul_le_mul_right h1 hs
    · have hmul := Int.mul_le_mul_of_nonneg_right hhi_div (Int.le_of_lt (ExactQ.den_int_pos q))
      have h2 : q.num * ((2 ^ p : Nat) : Int) * s ≤ ((b.m + (b.r : Int) + s - 1) / s) * (q.den : Int) * s := by
        have := hq.2; grind
      exact Int.le_of_mul_le_mul_right h2 hs

theorem midpoint_mem_left (b : DyadicBall) : b.bisectLeft.contains b.midpoint := by
  unfold bisectLeft midpoint ExactQ.ofDyadic contains
  rw [Nat.pow_succ, Int.natCast_mul]
  have h2 := Int.le_of_lt (pow2_int_pos b.e)
  have hle := Int.mul_le_mul_of_nonneg_right (by omega : 2 * b.m - (b.r : Int) - (b.r : Int) ≤ b.m * 2) h2
  constructor <;> grind

theorem midpoint_mem_right (b : DyadicBall) : b.bisectRight.contains b.midpoint := by
  unfold bisectRight midpoint ExactQ.ofDyadic contains
  rw [Nat.pow_succ, Int.natCast_mul]
  have h2 := Int.le_of_lt (pow2_int_pos b.e)
  have hle := Int.mul_le_mul_of_nonneg_right (by omega : b.m * 2 ≤ 2 * b.m + (b.r : Int) + (b.r : Int)) h2
  constructor <;> grind

theorem bisect_cover {b : DyadicBall} {q : ExactQ} (hq : b.contains q) :
    (b.bisectLeft.contains q ∧ q.le b.midpoint) ∨ (b.bisectRight.contains q ∧ b.midpoint.le q) := by
  unfold bisectLeft bisectRight midpoint ExactQ.ofDyadic ExactQ.le contains at *; dsimp only
  rw [Nat.pow_succ, Int.natCast_mul]
  by_cases hcmp : q.num * ((2 ^ b.e : Nat) : Int) ≤ b.m * (q.den : Int)
  · left; refine ⟨⟨by grind, by grind⟩, hcmp⟩
  · right; refine ⟨⟨by grind, by grind⟩, by omega⟩

theorem midpointBall_contains (b : DyadicBall) : b.midpointBall.contains b.midpoint := by
  unfold midpointBall midpoint ExactQ.ofDyadic contains; simp

theorem midpoint_mem (b : DyadicBall) : b.contains b.midpoint := by
  unfold midpoint ExactQ.ofDyadic contains; dsimp only
  have h2 := Int.le_of_lt (pow2_int_pos b.e)
  exact ⟨Int.mul_le_mul_of_nonneg_right (by omega) h2, Int.mul_le_mul_of_nonneg_right (by omega) h2⟩

theorem sub_midpoint_mem_radius {b : DyadicBall} {q : ExactQ} (hq : b.contains q) :
    b.radiusBall.contains (q.sub b.midpoint) := by
  unfold radiusBall midpoint ExactQ.ofDyadic ExactQ.sub contains at *
  simp only [Int.natCast_mul]
  have h2 := Int.le_of_lt (pow2_int_pos b.e)
  have h1 : -(b.r : Int) * (q.den : Int) ≤ q.num * ((2 ^ b.e : Nat) : Int) - b.m * (q.den : Int) := by grind
  have h2' : q.num * ((2 ^ b.e : Nat) : Int) - b.m * (q.den : Int) ≤ (b.r : Int) * (q.den : Int) := by grind
  have m1 := Int.mul_le_mul_of_nonneg_right h1 h2
  have m2 := Int.mul_le_mul_of_nonneg_right h2' h2
  constructor <;> grind

theorem subset_sound {a b : DyadicBall} (h : a.subset b = true) {q : ExactQ} (hq : a.contains q) :
    b.contains q := by
  unfold subset at h
  unfold contains at *
  have hqd := Int.le_of_lt (ExactQ.den_int_pos q)
  split at h
  · rename_i hle
    simp only [decide_eq_true_eq] at h
    let s : Int := ((2 ^ (b.e - a.e) : Nat) : Int)
    have hs := Int.le_of_lt (pow2_int_pos (b.e - a.e))
    have hpow : ((2 ^ b.e : Nat) : Int) = ((2 ^ a.e : Nat) : Int) * s := by
      have : (2 ^ b.e : Nat) = 2 ^ a.e * 2 ^ (b.e - a.e) := by
        rw [← Nat.pow_add, Nat.add_sub_cancel' hle]
      rw [this, Int.natCast_mul]
    rw [hpow]
    have h1 := Int.mul_le_mul_of_nonneg_right h.1 hqd
    have h2 := Int.mul_le_mul_of_nonneg_right h.2 hqd
    have hq1 := Int.mul_le_mul_of_nonneg_right hq.1 hs
    have hq2 := Int.mul_le_mul_of_nonneg_right hq.2 hs
    constructor
    · calc (b.m - (b.r : Int)) * (q.den : Int)
          ≤ ((a.m - (a.r : Int)) * s) * (q.den : Int) := h1
        _ = (a.m - (a.r : Int)) * (q.den : Int) * s := by grind
        _ ≤ q.num * ((2 ^ a.e : Nat) : Int) * s := hq1
        _ = q.num * (((2 ^ a.e : Nat) : Int) * s) := by grind
    · calc q.num * (((2 ^ a.e : Nat) : Int) * s)
          = q.num * ((2 ^ a.e : Nat) : Int) * s := by grind
        _ ≤ (a.m + (a.r : Int)) * (q.den : Int) * s := hq2
        _ = ((a.m + (a.r : Int)) * s) * (q.den : Int) := by grind
        _ ≤ (b.m + (b.r : Int)) * (q.den : Int) := h2
  · rename_i hgt
    simp only [decide_eq_true_eq] at h
    have hlt : b.e < a.e := Nat.lt_of_not_ge hgt
    let s : Int := ((2 ^ (a.e - b.e) : Nat) : Int)
    have hs : 0 < s := pow2_int_pos (a.e - b.e)
    have hpow : ((2 ^ a.e : Nat) : Int) = ((2 ^ b.e : Nat) : Int) * s := by
      have : (2 ^ a.e : Nat) = 2 ^ b.e * 2 ^ (a.e - b.e) := by
        rw [← Nat.pow_add, Nat.add_sub_cancel' (Nat.le_of_lt hlt)]
      rw [this, Int.natCast_mul]
    rw [hpow] at hq
    have h1 := Int.mul_le_mul_of_nonneg_right h.1 hqd
    have h2 := Int.mul_le_mul_of_nonneg_right h.2 hqd
    constructor
    · apply Int.le_of_mul_le_mul_right _ hs
      calc (b.m - (b.r : Int)) * (q.den : Int) * s
          = ((b.m - (b.r : Int)) * s) * (q.den : Int) := by grind
        _ ≤ (a.m - (a.r : Int)) * (q.den : Int) := h1
        _ ≤ q.num * (((2 ^ b.e : Nat) : Int) * s) := hq.1
        _ = q.num * ((2 ^ b.e : Nat) : Int) * s := by grind
    · apply Int.le_of_mul_le_mul_right _ hs
      calc q.num * ((2 ^ b.e : Nat) : Int) * s
          = q.num * (((2 ^ b.e : Nat) : Int) * s) := by grind
        _ ≤ (a.m + (a.r : Int)) * (q.den : Int) := hq.2
        _ ≤ ((b.m + (b.r : Int)) * s) * (q.den : Int) := h2
        _ = (b.m + (b.r : Int)) * (q.den : Int) * s := by grind

theorem maxAbsLE_sound {b : DyadicBall} {qNum qExp : Nat}
    (h : b.maxAbsLE qNum qExp = true) {x : ExactQ} (hx : b.contains x) :
    x.abs.le (ExactQ.ofDyadic (qNum : Int) qExp) := by
  unfold maxAbsLE at h
  unfold contains ExactQ.abs ExactQ.le ExactQ.ofDyadic at *
  have hqd := Int.le_of_lt (ExactQ.den_int_pos x)
  have hbound : (x.num.natAbs : Int) * ((2 ^ b.e : Nat) : Int) ≤
                ((b.m.natAbs + b.r : Nat) : Int) * (x.den : Int) := by
    have hlo := Int.le_trans (Int.mul_le_mul_of_nonneg_right (by omega : -((b.m.natAbs + b.r : Nat) : Int) ≤ b.m - (b.r : Int)) hqd) hx.1
    have hhi := Int.le_trans hx.2 (Int.mul_le_mul_of_nonneg_right (by omega : b.m + (b.r : Int) ≤ ((b.m.natAbs + b.r : Nat) : Int)) hqd)
    have habs : (x.num.natAbs : Int) * ((2 ^ b.e : Nat) : Int) =
                ((x.num * ((2 ^ b.e : Nat) : Int)).natAbs : Int) := by
      rw [Int.natAbs_mul, Int.natCast_mul, Int.natAbs_natCast]
    rw [habs]
    rw [Int.neg_mul] at hlo
    omega
  split at h
  · rename_i hle
    simp only [decide_eq_true_eq] at h
    have hint : ((b.m.natAbs + b.r : Nat) : Int) * ((2 ^ (qExp - b.e) : Nat) : Int) ≤ (qNum : Int) := by
      have : (((b.m.natAbs + b.r) * 2 ^ (qExp - b.e) : Nat) : Int) ≤ (qNum : Int) := Int.ofNat_le.mpr h
      simpa only [Int.natCast_mul] using this
    let s : Int := ((2 ^ (qExp - b.e) : Nat) : Int)
    have hs := Int.le_of_lt (pow2_int_pos (qExp - b.e))
    have hpow : ((2 ^ qExp : Nat) : Int) = ((2 ^ b.e : Nat) : Int) * s := by
      have : (2 ^ qExp : Nat) = 2 ^ b.e * 2 ^ (qExp - b.e) := by
        rw [← Nat.pow_add, Nat.add_sub_cancel' hle]
      rw [this, Int.natCast_mul]
    dsimp only
    rw [hpow]
    have h1 := Int.mul_le_mul_of_nonneg_right hbound hs
    have h2 := Int.mul_le_mul_of_nonneg_right hint hqd
    calc (x.num.natAbs : Int) * (((2 ^ b.e : Nat) : Int) * s)
        = (x.num.natAbs : Int) * ((2 ^ b.e : Nat) : Int) * s := by grind
      _ ≤ ((b.m.natAbs + b.r : Nat) : Int) * (x.den : Int) * s := h1
      _ = ((b.m.natAbs + b.r : Nat) : Int) * s * (x.den : Int) := by grind
      _ ≤ (qNum : Int) * (x.den : Int) := h2
  · rename_i hgt
    simp only [decide_eq_true_eq] at h
    have hlt : qExp < b.e := Nat.lt_of_not_ge hgt
    have hint : ((b.m.natAbs + b.r : Nat) : Int) ≤ (qNum : Int) * ((2 ^ (b.e - qExp) : Nat) : Int) := by
      have : ((b.m.natAbs + b.r : Nat) : Int) ≤ ((qNum * 2 ^ (b.e - qExp) : Nat) : Int) := Int.ofNat_le.mpr h
      simpa only [Int.natCast_mul] using this
    let s : Int := ((2 ^ (b.e - qExp) : Nat) : Int)
    have hs : 0 < s := pow2_int_pos (b.e - qExp)
    have hpow : ((2 ^ b.e : Nat) : Int) = ((2 ^ qExp : Nat) : Int) * s := by
      have : (2 ^ b.e : Nat) = 2 ^ qExp * 2 ^ (b.e - qExp) := by
        rw [← Nat.pow_add, Nat.add_sub_cancel' (Nat.le_of_lt hlt)]
      rw [this, Int.natCast_mul]
    dsimp only
    rw [hpow] at hbound
    have h2 := Int.mul_le_mul_of_nonneg_right hint hqd
    apply Int.le_of_mul_le_mul_right _ hs
    calc (x.num.natAbs : Int) * ((2 ^ qExp : Nat) : Int) * s
        = (x.num.natAbs : Int) * (((2 ^ qExp : Nat) : Int) * s) := by grind
      _ ≤ ((b.m.natAbs + b.r : Nat) : Int) * (x.den : Int) := hbound
      _ ≤ ((qNum : Int) * s) * (x.den : Int) := h2
      _ = (qNum : Int) * (x.den : Int) * s := by grind

-- Ball Operations + Exact Enclosure Soundness
theorem constInt_sound (z : Int) : (constInt z).contains (ExactQ.ofInt z) := by
  unfold constInt ExactQ.ofInt contains; simp

theorem constDyadic_sound (m : Int) (e : Nat) : (constDyadic m e).contains (ExactQ.ofDyadic m e) := by
  unfold constDyadic ExactQ.ofDyadic contains; simp

theorem neg_sound {a : DyadicBall} {x : ExactQ} (hx : a.contains x) :
    a.neg.contains x.neg := by
  unfold neg ExactQ.neg contains at *; constructor <;> grind

theorem add_sound {a b : DyadicBall} {x y : ExactQ} (prec : Nat)
    (hx : a.contains x) (hy : b.contains y) :
    (add a b prec).contains (x.add y) := by
  unfold add
  apply roundTo_sound
  unfold contains ExactQ.add at *
  simp only [Int.natCast_mul]
  have hxd := Int.le_of_lt (ExactQ.den_int_pos x)
  have hyd := Int.le_of_lt (ExactQ.den_int_pos y)
  split
  · rename_i hle
    let s : Nat := 2 ^ (b.e - a.e)
    have hs : (0 : Int) ≤ (s : Int) := Int.natCast_nonneg s
    have hpow : ((2 ^ b.e : Nat) : Int) = ((2 ^ a.e : Nat) : Int) * (s : Int) := by
      have : (2 ^ b.e : Nat) = 2 ^ a.e * s := by rw [← Nat.pow_add, Nat.add_sub_cancel' hle]
      rw [this, Int.natCast_mul]
    dsimp only
    simp only [Int.natCast_add, Int.natCast_mul]
    have h1 := Int.mul_le_mul_of_nonneg_right (Int.mul_le_mul_of_nonneg_right hx.1 hs) hyd
    have h2 := Int.mul_le_mul_of_nonneg_right hy.1 hxd
    have h3 := Int.mul_le_mul_of_nonneg_right (Int.mul_le_mul_of_nonneg_right hx.2 hs) hyd
    have h4 := Int.mul_le_mul_of_nonneg_right hy.2 hxd
    have hsum1 := Int.add_le_add h1 h2
    have hsum2 := Int.add_le_add h3 h4
    constructor
    · calc (a.m * (s : Int) + b.m - ((a.r : Int) * (s : Int) + (b.r : Int))) * ((x.den : Int) * (y.den : Int))
          = (a.m - (a.r : Int)) * (x.den : Int) * (s : Int) * (y.den : Int) + (b.m - (b.r : Int)) * (y.den : Int) * (x.den : Int) := by grind
        _ ≤ x.num * ((2 ^ a.e : Nat) : Int) * (s : Int) * (y.den : Int) + y.num * ((2 ^ b.e : Nat) : Int) * (x.den : Int) := hsum1
        _ = (x.num * (y.den : Int) + y.num * (x.den : Int)) * ((2 ^ b.e : Nat) : Int) := by rw [hpow]; grind
    · calc (x.num * (y.den : Int) + y.num * (x.den : Int)) * ((2 ^ b.e : Nat) : Int)
          = x.num * ((2 ^ a.e : Nat) : Int) * (s : Int) * (y.den : Int) + y.num * ((2 ^ b.e : Nat) : Int) * (x.den : Int) := by rw [hpow]; grind
        _ ≤ (a.m + (a.r : Int)) * (x.den : Int) * (s : Int) * (y.den : Int) + (b.m + (b.r : Int)) * (y.den : Int) * (x.den : Int) := hsum2
        _ = (a.m * (s : Int) + b.m + ((a.r : Int) * (s : Int) + (b.r : Int))) * ((x.den : Int) * (y.den : Int)) := by grind
  · rename_i hgt
    have hlt : b.e < a.e := Nat.lt_of_not_ge hgt
    let s : Nat := 2 ^ (a.e - b.e)
    have hs : (0 : Int) ≤ (s : Int) := Int.natCast_nonneg s
    have hpow : ((2 ^ a.e : Nat) : Int) = ((2 ^ b.e : Nat) : Int) * (s : Int) := by
      have : (2 ^ a.e : Nat) = 2 ^ b.e * s := by rw [← Nat.pow_add, Nat.add_sub_cancel' (Nat.le_of_lt hlt)]
      rw [this, Int.natCast_mul]
    dsimp only
    simp only [Int.natCast_add, Int.natCast_mul]
    have h1 := Int.mul_le_mul_of_nonneg_right hx.1 hyd
    have h2 := Int.mul_le_mul_of_nonneg_right (Int.mul_le_mul_of_nonneg_right hy.1 hs) hxd
    have h3 := Int.mul_le_mul_of_nonneg_right hx.2 hyd
    have h4 := Int.mul_le_mul_of_nonneg_right (Int.mul_le_mul_of_nonneg_right hy.2 hs) hxd
    have hsum1 := Int.add_le_add h1 h2
    have hsum2 := Int.add_le_add h3 h4
    constructor
    · calc (a.m + b.m * (s : Int) - ((a.r : Int) + (b.r : Int) * (s : Int))) * ((x.den : Int) * (y.den : Int))
          = (a.m - (a.r : Int)) * (x.den : Int) * (y.den : Int) + (b.m - (b.r : Int)) * (y.den : Int) * (s : Int) * (x.den : Int) := by grind
        _ ≤ x.num * ((2 ^ a.e : Nat) : Int) * (y.den : Int) + y.num * ((2 ^ b.e : Nat) : Int) * (s : Int) * (x.den : Int) := hsum1
        _ = (x.num * (y.den : Int) + y.num * (x.den : Int)) * ((2 ^ a.e : Nat) : Int) := by rw [hpow]; grind
    · calc (x.num * (y.den : Int) + y.num * (x.den : Int)) * ((2 ^ a.e : Nat) : Int)
          = x.num * ((2 ^ a.e : Nat) : Int) * (y.den : Int) + y.num * ((2 ^ b.e : Nat) : Int) * (s : Int) * (x.den : Int) := by rw [hpow]; grind
        _ ≤ (a.m + (a.r : Int)) * (x.den : Int) * (y.den : Int) + (b.m + (b.r : Int)) * (y.den : Int) * (s : Int) * (x.den : Int) := hsum2
        _ = (a.m + b.m * (s : Int) + ((a.r : Int) + (b.r : Int) * (s : Int))) * ((x.den : Int) * (y.den : Int)) := by grind

theorem sub_sound {a b : DyadicBall} {x y : ExactQ} (prec : Nat)
    (hx : a.contains x) (hy : b.contains y) :
    (sub a b prec).contains (x.sub y) := by
  have heq : (x.add y.neg).equiv (x.sub y) := by
    unfold ExactQ.equiv ExactQ.add ExactQ.neg ExactQ.sub; grind
  exact contains_congr heq (add_sound prec hx (neg_sound hy))

theorem mul_sound {a b : DyadicBall} {x y : ExactQ} (prec : Nat)
    (hx : a.contains x) (hy : b.contains y) :
    (mul a b prec).contains (x.mul y) := by
  unfold mul
  apply roundTo_sound
  unfold contains ExactQ.mul at *
  simp only [Int.natCast_add, Int.natCast_mul, Nat.pow_add]
  let dx : Int := x.num * ((2 ^ a.e : Nat) : Int) - a.m * (x.den : Int)
  let dy : Int := y.num * ((2 ^ b.e : Nat) : Int) - b.m * (y.den : Int)
  have hdx_abs : (dx.natAbs : Int) ≤ (a.r : Int) * (x.den : Int) := by grind
  have hdy_abs : (dy.natAbs : Int) ≤ (b.r : Int) * (y.den : Int) := by grind
  have hdiff : x.num * y.num * (((2 ^ a.e : Nat) : Int) * ((2 ^ b.e : Nat) : Int)) -
               a.m * b.m * ((x.den : Int) * (y.den : Int)) =
               a.m * (x.den : Int) * dy + b.m * (y.den : Int) * dx + dx * dy := by grind
  have hxd := Int.le_of_lt (ExactQ.den_int_pos x)
  have hyd := Int.le_of_lt (ExactQ.den_int_pos y)
  have ht1 : ((a.m * (x.den : Int) * dy).natAbs : Int) ≤
             (a.m.natAbs : Int) * (b.r : Int) * ((x.den : Int) * (y.den : Int)) := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natCast_mul, Int.natCast_mul, Int.natAbs_natCast]
    have h1 := Int.mul_le_mul_of_nonneg_left hdy_abs (Int.mul_nonneg (Int.natCast_nonneg a.m.natAbs) hxd)
    grind
  have ht2 : ((b.m * (y.den : Int) * dx).natAbs : Int) ≤
             (b.m.natAbs : Int) * (a.r : Int) * ((x.den : Int) * (y.den : Int)) := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natCast_mul, Int.natCast_mul, Int.natAbs_natCast]
    have h1 := Int.mul_le_mul_of_nonneg_left hdx_abs (Int.mul_nonneg (Int.natCast_nonneg b.m.natAbs) hyd)
    grind
  have ht3 : ((dx * dy).natAbs : Int) ≤
             (a.r : Int) * (b.r : Int) * ((x.den : Int) * (y.den : Int)) := by
    rw [Int.natAbs_mul, Int.natCast_mul]
    have h1 := Int.le_trans
      (Int.mul_le_mul_of_nonneg_right hdx_abs (Int.natCast_nonneg dy.natAbs))
      (Int.mul_le_mul_of_nonneg_left hdy_abs (Int.mul_nonneg (Int.natCast_nonneg a.r) hxd))
    grind
  have htri1 := Int.natAbs_add_le (a.m * (x.den : Int) * dy + b.m * (y.den : Int) * dx) (dx * dy)
  have htri2 := Int.natAbs_add_le (a.m * (x.den : Int) * dy) (b.m * (y.den : Int) * dx)
  constructor <;> grind

theorem sqr_sound {a : DyadicBall} {x : ExactQ} (prec : Nat) (hx : a.contains x) :
    (sqr a prec).contains x.sqr := by
  unfold sqr
  apply roundTo_sound
  unfold contains ExactQ.sqr at *
  have hxd := Int.le_of_lt (ExactQ.den_int_pos x)
  have hpow : ((2 ^ (2 * a.e) : Nat) : Int) = ((2 ^ a.e : Nat) : Int) * ((2 ^ a.e : Nat) : Int) := by
    have : 2 * a.e = a.e + a.e := by omega
    rw [this, Nat.pow_add, Int.natCast_mul]
  let u : Int := x.num * ((2 ^ a.e : Nat) : Int)
  let lo : Int := a.m - (a.r : Int)
  let hi : Int := a.m + (a.r : Int)
  have hu_sq : x.num * x.num * ((2 ^ (2 * a.e) : Nat) : Int) = u * u := by grind
  have hlo_sq : (lo * lo) * ((x.den * x.den : Nat) : Int) = (lo * (x.den : Int)) * (lo * (x.den : Int)) := by
    rw [Int.natCast_mul]; grind
  have hhi_sq : (hi * hi) * ((x.den * x.den : Nat) : Int) = (hi * (x.den : Int)) * (hi * (x.den : Int)) := by
    rw [Int.natCast_mul]; grind
  have h1 : lo * (x.den : Int) ≤ u := hx.1
  have h2 : u ≤ hi * (x.den : Int) := hx.2
  split
  · rename_i hlo_nn
    apply fromInterval_sound
    · rw [hu_sq, hlo_sq]
      have hlo_d := Int.mul_nonneg hlo_nn hxd
      exact Int.le_trans (Int.mul_le_mul_of_nonneg_right h1 hlo_d)
                         (Int.mul_le_mul_of_nonneg_left h1 (Int.le_trans hlo_d h1))
    · rw [hu_sq, hhi_sq]
      have hu_nn := Int.le_trans (Int.mul_nonneg hlo_nn hxd) h1
      exact Int.le_trans (Int.mul_le_mul_of_nonneg_right h2 hu_nn)
                         (Int.mul_le_mul_of_nonneg_left h2 (Int.le_trans hu_nn h2))
  · split
    · rename_i hhi_np
      apply fromInterval_sound
      · rw [hu_sq, hhi_sq]
        have hhi_d : hi * (x.den : Int) ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg hhi_np hxd
        have hu_np : u ≤ 0 := Int.le_trans h2 hhi_d
        have hneg1 : 0 ≤ -(hi * (x.den : Int)) := by omega
        have hneg2 : -(hi * (x.den : Int)) ≤ -u := by omega
        have hsq := Int.le_trans (Int.mul_le_mul_of_nonneg_right hneg2 hneg1)
                                 (Int.mul_le_mul_of_nonneg_left hneg2 (Int.le_trans hneg1 hneg2))
        grind
      · rw [hu_sq, hlo_sq]
        have hhi_d : hi * (x.den : Int) ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg hhi_np hxd
        have hu_np : u ≤ 0 := Int.le_trans h2 hhi_d
        have hneg1 : 0 ≤ -u := by omega
        have hneg2 : -u ≤ -(lo * (x.den : Int)) := by omega
        have hsq := Int.le_trans (Int.mul_le_mul_of_nonneg_right hneg2 hneg1)
                                 (Int.mul_le_mul_of_nonneg_left hneg2 (Int.le_trans hneg1 hneg2))
        grind
    · apply fromInterval_sound
      · rw [hu_sq, Int.zero_mul]
        by_cases hu_s : 0 ≤ u
        · exact Int.mul_nonneg hu_s hu_s
        · have : 0 ≤ -u := by omega
          have := Int.mul_nonneg this this
          grind
      · rw [hu_sq]
        have hdd : 0 ≤ ((x.den * x.den : Nat) : Int) := Int.natCast_nonneg _
        by_cases hu_s : 0 ≤ u
        · have hu_le : u * u ≤ (hi * (x.den : Int)) * (hi * (x.den : Int)) :=
            Int.le_trans (Int.mul_le_mul_of_nonneg_right h2 hu_s)
                         (Int.mul_le_mul_of_nonneg_left h2 (Int.le_trans hu_s h2))
          rw [← hhi_sq] at hu_le
          exact Int.le_trans hu_le (Int.mul_le_mul_of_nonneg_right (Int.le_max_right _ _) hdd)
        · have hneg1 : 0 ≤ -u := by omega
          have hneg2 : -u ≤ -(lo * (x.den : Int)) := by omega
          have hsq := Int.le_trans (Int.mul_le_mul_of_nonneg_right hneg2 hneg1)
                                   (Int.mul_le_mul_of_nonneg_left hneg2 (Int.le_trans hneg1 hneg2))
          have hu_le : u * u ≤ (lo * (x.den : Int)) * (lo * (x.den : Int)) := by grind
          rw [← hlo_sq] at hu_le
          exact Int.le_trans hu_le (Int.mul_le_mul_of_nonneg_right (Int.le_max_left _ _) hdd)

theorem invPos_sound {a b : DyadicBall} {prec : Nat}
    (hinv : invPos a prec = some b) {x : ExactQ} (hx : a.contains x) :
    ∃ (hpos : 0 < x.num), b.contains (x.invPos hpos) := by
  unfold invPos at hinv
  split at hinv
  · cases hinv
  · rename_i hnotle
    have hlo_pos : 0 < a.m - (a.r : Int) := by omega
    have hhi_pos : 0 < a.m + (a.r : Int) := by omega
    injection hinv with hb
    subst hb
    have hx_pos : 0 < x.num := by
      have h1 : 0 < (a.m - (a.r : Int)) * (x.den : Int) := Int.mul_pos hlo_pos (ExactQ.den_int_pos x)
      have h2 : 0 < x.num * ((2 ^ a.e : Nat) : Int) := Int.lt_of_lt_of_le h1 hx.1
      have h2p := pow2_int_pos a.e
      by_cases hxle : x.num ≤ 0
      · have : x.num * ((2 ^ a.e : Nat) : Int) ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg hxle (Int.le_of_lt h2p)
        omega
      · omega
    refine ⟨hx_pos, ?_⟩
    apply fromInterval_sound
    · unfold ExactQ.invPos
      dsimp only
      have hx_toNat : (x.num.toNat : Int) = x.num := by omega
      rw [hx_toNat]
      let hi := a.m + (a.r : Int)
      let num : Int := ((2 ^ (a.e + prec) : Nat) : Int)
      have hdiv_lo : (num / hi) * hi ≤ num := by
        have hmod := Int.emod_nonneg num (by omega : hi ≠ 0)
        have hd := Int.ediv_mul_add_emod num hi
        omega
      have hpow : num = ((2 ^ a.e : Nat) : Int) * ((2 ^ prec : Nat) : Int) := by
        dsimp only [num]; rw [Nat.pow_add, Int.natCast_mul]
      have hmul_pos : 0 < hi * ((2 ^ a.e : Nat) : Int) := Int.mul_pos hhi_pos (pow2_int_pos a.e)
      have h1 := Int.mul_le_mul_of_nonneg_right hdiv_lo (Int.mul_nonneg (Int.le_of_lt hx_pos) (Int.le_of_lt (pow2_int_pos a.e)))
      have h2 := Int.mul_le_mul_of_nonneg_left hx.2 (Int.le_of_lt (pow2_int_pos (a.e + prec)))
      apply Int.le_of_mul_le_mul_right _ hmul_pos
      calc (num / hi) * x.num * (hi * ((2 ^ a.e : Nat) : Int))
          = ((num / hi) * hi) * (x.num * ((2 ^ a.e : Nat) : Int)) := by grind
        _ ≤ num * (x.num * ((2 ^ a.e : Nat) : Int)) := h1
        _ ≤ num * (hi * (x.den : Int)) := h2
        _ = (x.den : Int) * ((2 ^ prec : Nat) : Int) * (hi * ((2 ^ a.e : Nat) : Int)) := by rw [hpow]; grind
    · unfold ExactQ.invPos
      dsimp only
      have hx_toNat : (x.num.toNat : Int) = x.num := by omega
      rw [hx_toNat]
      let lo := a.m - (a.r : Int)
      let num : Int := ((2 ^ (a.e + prec) : Nat) : Int)
      have hdiv_hi : num ≤ ((num + lo - 1) / lo) * lo := by
        have hlo' : 0 < lo := hlo_pos
        have hmod := Int.emod_lt_of_pos (num + lo - 1) hlo'
        have hd := Int.ediv_mul_add_emod (num + lo - 1) lo
        omega
      have hpow : num = ((2 ^ a.e : Nat) : Int) * ((2 ^ prec : Nat) : Int) := by
        dsimp only [num]; rw [Nat.pow_add, Int.natCast_mul]
      have hmul_pos : 0 < lo * ((2 ^ a.e : Nat) : Int) := Int.mul_pos hlo_pos (pow2_int_pos a.e)
      have h1 := Int.mul_le_mul_of_nonneg_left hx.1 (Int.le_of_lt (pow2_int_pos (a.e + prec)))
      have h2 := Int.mul_le_mul_of_nonneg_right hdiv_hi (Int.mul_nonneg (Int.le_of_lt hx_pos) (Int.le_of_lt (pow2_int_pos a.e)))
      apply Int.le_of_mul_le_mul_right _ hmul_pos
      calc (x.den : Int) * ((2 ^ prec : Nat) : Int) * (lo * ((2 ^ a.e : Nat) : Int))
          = num * (lo * (x.den : Int)) := by rw [hpow]; grind
        _ ≤ num * (x.num * ((2 ^ a.e : Nat) : Int)) := h1
        _ ≤ (((num + lo - 1) / lo) * lo) * (x.num * ((2 ^ a.e : Nat) : Int)) := h2
        _ = ((num + lo - 1) / lo) * x.num * (lo * ((2 ^ a.e : Nat) : Int)) := by grind

end DyadicBall
namespace SlopeIdentities
theorem var_slope (x y : ExactQ) :
    (x.sub y).equiv ((ExactQ.ofInt 1).mul (x.sub y)) := by
  exact ExactQ.equiv_symm (ExactQ.mul_one_left_equiv _)

theorem const_slope (c x y : ExactQ) :
    (c.sub c).equiv ((ExactQ.ofInt 0).mul (x.sub y)) := by
  unfold ExactQ.equiv ExactQ.sub ExactQ.mul ExactQ.ofInt; dsimp only
  simp only [Int.natCast_mul]; grind

theorem neg_slope {fx fy s x y : ExactQ}
    (h : (fx.sub fy).equiv (s.mul (x.sub y))) :
    (fx.neg.sub fy.neg).equiv (s.neg.mul (x.sub y)) := by
  unfold ExactQ.equiv ExactQ.neg ExactQ.sub ExactQ.mul at *; dsimp only at *
  simp only [Int.natCast_mul] at *; grind

theorem add_slope {ax ay sa bx by_ sb x y : ExactQ}
    (ha : (ax.sub ay).equiv (sa.mul (x.sub y)))
    (hb : (bx.sub by_).equiv (sb.mul (x.sub y))) :
    ((ax.add bx).sub (ay.add by_)).equiv ((sa.add sb).mul (x.sub y)) := by
  unfold ExactQ.equiv ExactQ.add ExactQ.sub ExactQ.mul at *; dsimp only at *
  simp only [Int.natCast_mul] at *
  have h1 : (((ax.num * (bx.den : Int) + bx.num * (ax.den : Int)) * ((ay.den : Int) * (by_.den : Int)) -
              (ay.num * (by_.den : Int) + by_.num * (ay.den : Int)) * ((ax.den : Int) * (bx.den : Int))) *
             ((sa.den : Int) * (sb.den : Int) * ((x.den : Int) * (y.den : Int)))) =
            (((sa.num * (sb.den : Int) + sb.num * (sa.den : Int)) * (x.num * (y.den : Int) - y.num * (x.den : Int))) *
             ((ax.den : Int) * (bx.den : Int) * ((ay.den : Int) * (by_.den : Int)))) := by
    have t1 : (ax.num * (ay.den : Int) - ay.num * (ax.den : Int)) * ((sa.den : Int) * ((x.den : Int) * (y.den : Int))) =
              sa.num * (x.num * (y.den : Int) - y.num * (x.den : Int)) * ((ax.den : Int) * (ay.den : Int)) := ha
    have t2 : (bx.num * (by_.den : Int) - by_.num * (bx.den : Int)) * ((sb.den : Int) * ((x.den : Int) * (y.den : Int))) =
              sb.num * (x.num * (y.den : Int) - y.num * (x.den : Int)) * ((bx.den : Int) * (by_.den : Int)) := hb
    grind
  exact h1

theorem sub_slope {ax ay sa bx by_ sb x y : ExactQ}
    (ha : (ax.sub ay).equiv (sa.mul (x.sub y)))
    (hb : (bx.sub by_).equiv (sb.mul (x.sub y))) :
    ((ax.sub bx).sub (ay.sub by_)).equiv ((sa.sub sb).mul (x.sub y)) := by
  unfold ExactQ.equiv ExactQ.sub ExactQ.mul at *; dsimp only at *
  simp only [Int.natCast_mul] at *
  grind

theorem mul_slope {ax ay sa bx by_ sb x y : ExactQ}
    (ha : (ax.sub ay).equiv (sa.mul (x.sub y)))
    (hb : (bx.sub by_).equiv (sb.mul (x.sub y))) :
    ((ax.mul bx).sub (ay.mul by_)).equiv (((sa.mul bx).add (ay.mul sb)).mul (x.sub y)) := by
  unfold ExactQ.equiv ExactQ.add ExactQ.sub ExactQ.mul at *; dsimp only at *
  simp only [Int.natCast_mul] at *
  grind

theorem sqr_slope {ax ay sa x y : ExactQ}
    (ha : (ax.sub ay).equiv (sa.mul (x.sub y))) :
    (ax.sqr.sub ay.sqr).equiv (((ax.add ay).mul sa).mul (x.sub y)) := by
  unfold ExactQ.equiv ExactQ.sqr ExactQ.add ExactQ.sub ExactQ.mul at *; dsimp only at *
  simp only [Int.natCast_mul] at *
  grind

theorem invPos_slope {ax ay sa x y : ExactQ}
    (hx : 0 < ax.num) (hy : 0 < ay.num)
    (ha : (ax.sub ay).equiv (sa.mul (x.sub y))) :
    ((ax.invPos hx).sub (ay.invPos hy)).equiv
      ((sa.mul ((ax.invPos hx).mul (ay.invPos hy))).neg.mul (x.sub y)) := by
  unfold ExactQ.equiv ExactQ.invPos ExactQ.neg ExactQ.sub ExactQ.mul at *; dsimp only at *
  simp only [Int.natCast_mul] at *
  have hxn : (ax.num.toNat : Int) = ax.num := by omega
  have hyn : (ay.num.toNat : Int) = ay.num := by omega
  rw [hxn, hyn]
  grind

end SlopeIdentities
theorem evalBall_sound (prec : Nat) (e : Expr) (P X B : DyadicBall)
    (heval : evalBall prec e P X = some B)
    (p x : ExactQ) (hp : P.contains p) (hx : X.contains x) :
    ∃ y, evalQ e p x = some y ∧ B.contains y := by
  induction e generalizing B with
  | var =>
    simp only [evalBall, Option.some.injEq] at heval; subst heval
    exact ⟨x, rfl, DyadicBall.roundTo_sound X prec x hx⟩
  | param =>
    simp only [evalBall, Option.some.injEq] at heval; subst heval
    exact ⟨p, rfl, DyadicBall.roundTo_sound P prec p hp⟩
  | constInt z =>
    simp only [evalBall, Option.some.injEq] at heval; subst heval
    exact ⟨ExactQ.ofInt z, rfl, DyadicBall.constInt_sound z⟩
  | constDyadic m ex =>
    simp only [evalBall, Option.some.injEq] at heval; subst heval
    exact ⟨ExactQ.ofDyadic m ex, rfl, DyadicBall.constDyadic_sound m ex⟩
  | neg a ih =>
    simp only [evalBall, Option.map_eq_some_iff] at heval
    rcases heval with ⟨va, hva, rfl⟩
    rcases ih va hva with ⟨ya, hya, hmem⟩
    exact ⟨ya.neg, by simp [evalQ, hya], DyadicBall.neg_sound hmem⟩
  | add a b iha ihb =>
    simp only [evalBall, Option.bind_eq_some_iff, Option.some.injEq] at heval
    rcases heval with ⟨va, hva, vb, hvb, rfl⟩
    rcases iha va hva with ⟨ya, hya, hma⟩
    rcases ihb vb hvb with ⟨yb, hyb, hmb⟩
    exact ⟨ya.add yb, by simp [evalQ, hya, hyb], DyadicBall.add_sound prec hma hmb⟩
  | sub a b iha ihb =>
    simp only [evalBall, Option.bind_eq_some_iff, Option.some.injEq] at heval
    rcases heval with ⟨va, hva, vb, hvb, rfl⟩
    rcases iha va hva with ⟨ya, hya, hma⟩
    rcases ihb vb hvb with ⟨yb, hyb, hmb⟩
    exact ⟨ya.sub yb, by simp [evalQ, hya, hyb], DyadicBall.sub_sound prec hma hmb⟩
  | mul a b iha ihb =>
    simp only [evalBall, Option.bind_eq_some_iff, Option.some.injEq] at heval
    rcases heval with ⟨va, hva, vb, hvb, rfl⟩
    rcases iha va hva with ⟨ya, hya, hma⟩
    rcases ihb vb hvb with ⟨yb, hyb, hmb⟩
    exact ⟨ya.mul yb, by simp [evalQ, hya, hyb], DyadicBall.mul_sound prec hma hmb⟩
  | sqr a ih =>
    simp only [evalBall, Option.bind_eq_some_iff, Option.some.injEq] at heval
    rcases heval with ⟨va, hva, rfl⟩
    rcases ih va hva with ⟨ya, hya, hma⟩
    exact ⟨ya.sqr, by simp [evalQ, hya], DyadicBall.sqr_sound prec hma⟩
  | inv a ih =>
    simp only [evalBall, Option.bind_eq_some_iff] at heval
    rcases heval with ⟨va, hva, hinv⟩
    rcases ih va hva with ⟨ya, hya, hma⟩
    rcases DyadicBall.invPos_sound hinv hma with ⟨hpos, hmb⟩
    exact ⟨ya.invPos hpos, by simp [evalQ, hya, hpos], hmb⟩

-- Soundness of evalJetBall: Simultaneous Value Enclosure + Exact Algebraic Secant Slope Enclosure!
theorem evalJetBall_sound (prec : Nat) (e : Expr) (P X V S : DyadicBall)
    (heval : evalJetBall prec e P X = some (V, S))
    (p x y : ExactQ) (hp : P.contains p) (hx : X.contains x) (hy : X.contains y) :
    ∃ fx fy s,
      evalQ e p x = some fx ∧
      evalQ e p y = some fy ∧
      V.contains fx ∧
      V.contains fy ∧
      S.contains s ∧
      (fx.sub fy).equiv (s.mul (x.sub y)) := by
  induction e generalizing V S with
  | var =>
    simp only [evalJetBall, Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    exact ⟨x, y, ExactQ.ofInt 1, rfl, rfl,
      DyadicBall.roundTo_sound X prec x hx, DyadicBall.roundTo_sound X prec y hy,
      DyadicBall.constInt_sound 1, SlopeIdentities.var_slope x y⟩
  | param =>
    simp only [evalJetBall, Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    exact ⟨p, p, ExactQ.ofInt 0, rfl, rfl,
      DyadicBall.roundTo_sound P prec p hp, DyadicBall.roundTo_sound P prec p hp,
      DyadicBall.constInt_sound 0, SlopeIdentities.const_slope p x y⟩
  | constInt z =>
    simp only [evalJetBall, Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    exact ⟨ExactQ.ofInt z, ExactQ.ofInt z, ExactQ.ofInt 0, rfl, rfl,
      DyadicBall.constInt_sound z, DyadicBall.constInt_sound z,
      DyadicBall.constInt_sound 0, SlopeIdentities.const_slope _ x y⟩
  | constDyadic m ex =>
    simp only [evalJetBall, Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    exact ⟨ExactQ.ofDyadic m ex, ExactQ.ofDyadic m ex, ExactQ.ofInt 0, rfl, rfl,
      DyadicBall.constDyadic_sound m ex, DyadicBall.constDyadic_sound m ex,
      DyadicBall.constInt_sound 0, SlopeIdentities.const_slope _ x y⟩
  | neg a ih =>
    simp only [evalJetBall, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨⟨va, sa⟩, hva, rfl, rfl⟩
    rcases ih va sa hva with ⟨ax, ay, s, hax, hay, hvx, hvy, hs, hsl⟩
    exact ⟨ax.neg, ay.neg, s.neg, by simp [evalQ, hax], by simp [evalQ, hay],
      DyadicBall.neg_sound hvx, DyadicBall.neg_sound hvy, DyadicBall.neg_sound hs,
      SlopeIdentities.neg_slope hsl⟩
  | add a b iha ihb =>
    simp only [evalJetBall, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨⟨va, sa⟩, hva, ⟨vb, sb⟩, hvb, rfl, rfl⟩
    rcases iha va sa hva with ⟨ax, ay, s1, hax, hay, hvax, hvay, hs1, hsl1⟩
    rcases ihb vb sb hvb with ⟨bx, by_, s2, hbx, hby, hvbx, hvby, hs2, hsl2⟩
    exact ⟨ax.add bx, ay.add by_, s1.add s2,
      by simp [evalQ, hax, hbx], by simp [evalQ, hay, hby],
      DyadicBall.add_sound prec hvax hvbx, DyadicBall.add_sound prec hvay hvby,
      DyadicBall.add_sound prec hs1 hs2, SlopeIdentities.add_slope hsl1 hsl2⟩
  | sub a b iha ihb =>
    simp only [evalJetBall, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨⟨va, sa⟩, hva, ⟨vb, sb⟩, hvb, rfl, rfl⟩
    rcases iha va sa hva with ⟨ax, ay, s1, hax, hay, hvax, hvay, hs1, hsl1⟩
    rcases ihb vb sb hvb with ⟨bx, by_, s2, hbx, hby, hvbx, hvby, hs2, hsl2⟩
    exact ⟨ax.sub bx, ay.sub by_, s1.sub s2,
      by simp [evalQ, hax, hbx], by simp [evalQ, hay, hby],
      DyadicBall.sub_sound prec hvax hvbx, DyadicBall.sub_sound prec hvay hvby,
      DyadicBall.sub_sound prec hs1 hs2, SlopeIdentities.sub_slope hsl1 hsl2⟩
  | mul a b iha ihb =>
    simp only [evalJetBall, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨⟨va, sa⟩, hva, ⟨vb, sb⟩, hvb, rfl, rfl⟩
    rcases iha va sa hva with ⟨ax, ay, s1, hax, hay, hvax, hvay, hs1, hsl1⟩
    rcases ihb vb sb hvb with ⟨bx, by_, s2, hbx, hby, hvbx, hvby, hs2, hsl2⟩
    exact ⟨ax.mul bx, ay.mul by_, (s1.mul bx).add (ay.mul s2),
      by simp [evalQ, hax, hbx], by simp [evalQ, hay, hby],
      DyadicBall.mul_sound prec hvax hvbx, DyadicBall.mul_sound prec hvay hvby,
      DyadicBall.add_sound prec (DyadicBall.mul_sound prec hs1 hvbx) (DyadicBall.mul_sound prec hvay hs2),
      SlopeIdentities.mul_slope hsl1 hsl2⟩
  | sqr a ih =>
    simp only [evalJetBall, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨⟨va, sa⟩, hva, rfl, rfl⟩
    rcases ih va sa hva with ⟨ax, ay, s1, hax, hay, hvax, hvay, hs1, hsl1⟩
    have hsum_mem : (DyadicBall.mul (DyadicBall.constInt 2) va prec).contains (ax.add ay) := by
      -- Since ax, ay ∈ va, ax + ay ∈ [2(m-r)/2^e, 2(m+r)/2^e] = (2 * va)
      unfold DyadicBall.mul DyadicBall.constInt
      apply DyadicBall.roundTo_sound
      unfold DyadicBall.contains ExactQ.add at *
      have h2abs : ((2 : Int).natAbs : Nat) = 2 := rfl
      rw [h2abs]
      simp only [Nat.zero_add, Nat.zero_mul, Nat.add_zero, Int.natCast_mul]
      have hxd := Int.le_of_lt (ExactQ.den_int_pos ax)
      have hyd := Int.le_of_lt (ExactQ.den_int_pos ay)
      have h1 := Int.mul_le_mul_of_nonneg_right hvax.1 hyd
      have h2 := Int.mul_le_mul_of_nonneg_right hvay.1 hxd
      have h3 := Int.mul_le_mul_of_nonneg_right hvax.2 hyd
      have h4 := Int.mul_le_mul_of_nonneg_right hvay.2 hxd
      have hs1' := Int.add_le_add h1 h2
      have hs2' := Int.add_le_add h3 h4
      constructor <;> grind
    exact ⟨ax.sqr, ay.sqr, (ax.add ay).mul s1,
      by simp [evalQ, hax], by simp [evalQ, hay],
      DyadicBall.sqr_sound prec hvax, DyadicBall.sqr_sound prec hvay,
      DyadicBall.mul_sound prec hsum_mem hs1, SlopeIdentities.sqr_slope hsl1⟩
  | inv a ih =>
    simp only [evalJetBall, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨⟨va, sa⟩, hva, invV, hinv, rfl, rfl⟩
    rcases ih va sa hva with ⟨ax, ay, s1, hax, hay, hvax, hvay, hs1, hsl1⟩
    rcases DyadicBall.invPos_sound hinv hvax with ⟨hpx, hix⟩
    rcases DyadicBall.invPos_sound hinv hvay with ⟨hpy, hiy⟩
    exact ⟨ax.invPos hpx, ay.invPos hpy, (s1.mul ((ax.invPos hpx).mul (ay.invPos hpy))).neg,
      by simp [evalQ, hax, hpx], by simp [evalQ, hay, hpy],
      hix, hiy,
      DyadicBall.neg_sound (DyadicBall.mul_sound prec hs1 (DyadicBall.mul_sound prec hix hiy)),
      SlopeIdentities.invPos_slope hpx hpy hsl1⟩

-- Soundness of Centered-Form Enclosure (eliminates linear interval dependency!)
theorem evalCenteredBall_sound (prec : Nat) (e : Expr) (P X V S : DyadicBall)
    (heval : evalCenteredBall prec e P X = some (V, S))
    (p x y : ExactQ) (hp : P.contains p) (hx : X.contains x) (hy : X.contains y) :
    ∃ fx fy s,
      evalQ e p x = some fx ∧
      evalQ e p y = some fy ∧
      V.contains fx ∧
      V.contains fy ∧
      S.contains s ∧
      (fx.sub fy).equiv (s.mul (x.sub y)) := by
  unfold evalCenteredBall at heval
  simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at heval
  rcases heval with ⟨⟨vDirect, sJet⟩, hjet, vMid, hmid, rfl, rfl⟩
  -- Slope & well-definedness for (x, y)
  rcases evalJetBall_sound prec e P X vDirect sJet hjet p x y hp hx hy with
    ⟨fx, fy, sxy, hfx, hfy, _, _, hsxy, hslxy⟩
  -- Midpoint value enclosure
  rcases evalBall_sound prec e P X.midpointBall vMid hmid p X.midpoint hp (DyadicBall.midpointBall_contains X) with
    ⟨fmid, hfmid, hvmid⟩
  -- Centered enclosure for x via (x, midpoint)
  rcases evalJetBall_sound prec e P X vDirect sJet hjet p x X.midpoint hp hx (DyadicBall.midpoint_mem X) with
    ⟨fx', fmid', sxm, hfx', hfmid', _, _, hsxm, hslxm⟩
  rw [hfx] at hfx'; injection hfx' with hfx_eq; subst hfx_eq
  rw [hfmid] at hfmid'; injection hfmid' with hfmid_eq; subst hfmid_eq
  have hmem_x : (DyadicBall.add vMid (DyadicBall.mul sJet X.radiusBall prec) prec).contains fx := by
    have heq_x : (fmid.add (sxm.mul (x.sub X.midpoint))).equiv fx :=
      ExactQ.equiv_symm (ExactQ.add_sub_equiv fx fmid _ hslxm)
    exact DyadicBall.contains_congr heq_x
      (DyadicBall.add_sound prec hvmid (DyadicBall.mul_sound prec hsxm (DyadicBall.sub_midpoint_mem_radius hx)))
  -- Centered enclosure for y via (y, midpoint)
  rcases evalJetBall_sound prec e P X vDirect sJet hjet p y X.midpoint hp hy (DyadicBall.midpoint_mem X) with
    ⟨fy', fmid'', sym, hfy', hfmid'', _, _, hsym, hslym⟩
  rw [hfy] at hfy'; injection hfy' with hfy_eq; subst hfy_eq
  rw [hfmid] at hfmid''; injection hfmid'' with hfmid_eq2; subst hfmid_eq2
  have hmem_y : (DyadicBall.add vMid (DyadicBall.mul sJet X.radiusBall prec) prec).contains fy := by
    have heq_y : (fmid.add (sym.mul (y.sub X.midpoint))).equiv fy :=
      ExactQ.equiv_symm (ExactQ.add_sub_equiv fy fmid _ hslym)
    exact DyadicBall.contains_congr heq_y
      (DyadicBall.add_sound prec hvmid (DyadicBall.mul_sound prec hsym (DyadicBall.sub_midpoint_mem_radius hy)))
  exact ⟨fx, fy, sxy, hfx, hfy, hmem_x, hmem_y, hsxy, hslxy⟩

-- ============================================================================
-- PART 4: Adaptive 2D Subdivision + Contraction Compiler & Infinite Lifting
-- ============================================================================

theorem checkStateTree_sound (e : Expr) (P B0 B : DyadicBall) (qNum qExp : Nat) (t : StateTree)
    (hchk : checkStateTree e P B0 B qNum qExp t = true)
    (p : ExactQ) (hp : P.contains p) :
    IsSelfMappedLipschitz e p B0 B (ExactQ.ofDyadic (qNum : Int) qExp) := by
  let q := ExactQ.ofDyadic (qNum : Int) qExp
  have hq_nn : 0 ≤ q.num := by dsimp [q, ExactQ.ofDyadic]; exact Int.natCast_nonneg qNum
  induction t generalizing B with
  | leaf prec uc =>
    unfold checkStateTree checkStateLeaf at hchk
    dsimp only at hchk
    split at hchk
    · cases hchk
    · rename_i V S heq
      simp only [Bool.and_eq_true] at hchk
      rcases hchk with ⟨hsub, hmax⟩
      have hsound : ∀ x y, B.contains x → B.contains y →
          ∃ fx fy s, evalQ e p x = some fx ∧ evalQ e p y = some fy ∧
            V.contains fx ∧ V.contains fy ∧ S.contains s ∧ (fx.sub fy).equiv (s.mul (x.sub y)) := by
        intro x y hx hy
        by_cases huc : uc = true
        · rw [huc] at heq; simp only [ite_true] at heq
          exact evalCenteredBall_sound prec e P B V S heq p x y hp hx hy
        · have huc' : uc = false := by cases uc <;> simp_all
          rw [huc'] at heq; simp only [Bool.false_eq_true, ite_false] at heq
          exact evalJetBall_sound prec e P B V S heq p x y hp hx hy
      constructor
      · intro x hx
        rcases hsound x x hx hx with ⟨fx, _, _, hfx, _, hvx, _, _, _⟩
        exact ⟨fx, hfx, DyadicBall.subset_sound hsub hvx⟩
      · intro x y fx fy hx hy hfx hfy
        rcases hsound x y hx hy with ⟨fx', fy', s, hfx', hfy', _, _, hs, hsl⟩
        rw [hfx] at hfx'; injection hfx' with e1; subst e1
        rw [hfy] at hfy'; injection hfy' with e2; subst e2
        have habs_le : s.abs.le q := DyadicBall.maxAbsLE_sound hmax hs
        have hdist_eq : (fx.dist fy).equiv (s.abs.mul (x.dist y)) := by
          unfold ExactQ.dist
          exact ExactQ.equiv_trans (ExactQ.abs_congr hsl) (ExactQ.abs_mul_equiv s (x.sub y))
        exact ExactQ.le_trans (ExactQ.le_of_equiv hdist_eq)
          (ExactQ.mul_le_mul_of_nonneg_right (ExactQ.abs_nonneg _) habs_le)
  | split l r ihl ihr =>
    unfold checkStateTree at hchk
    simp only [Bool.and_eq_true] at hchk
    rcases ihl B.bisectLeft hchk.1 with ⟨hinvL, hlipL⟩
    rcases ihr B.bisectRight hchk.2 with ⟨hinvR, hlipR⟩
    constructor
    · intro x hx
      rcases DyadicBall.bisect_cover hx with ⟨hxL, _⟩ | ⟨hxR, _⟩
      · exact hinvL x hxL
      · exact hinvR x hxR
    · intro x y fx fy hx hy hfx hfy
      rcases DyadicBall.bisect_cover hx with ⟨hxL, hx_le⟩ | ⟨hxR, hx_ge⟩ <;>
      rcases DyadicBall.bisect_cover hy with ⟨hyL, hy_le⟩ | ⟨hyR, hy_ge⟩
      · exact hlipL x y fx fy hxL hyL hfx hfy
      · -- Binary-tree telescoping across midpoint: x ≤ mid ≤ y!
        rcases hinvL B.midpoint (DyadicBall.midpoint_mem_left B) with ⟨fm, hfm, _⟩
        have h1 := hlipL x B.midpoint fx fm hxL (DyadicBall.midpoint_mem_left B) hfx hfm
        have h2 := hlipR B.midpoint y fm fy (DyadicBall.midpoint_mem_right B) hyR hfm hfy
        have htri := ExactQ.dist_triangle fx fm fy
        have hadd := ExactQ.add_le_add h1 h2
        have hsum_dist : (ExactQ.add (x.dist B.midpoint) (B.midpoint.dist y)).equiv (x.dist y) := by
          have d1 := ExactQ.dist_eq_sub_of_le hx_le
          have d2 := ExactQ.dist_eq_sub_of_le hy_ge
          have d3 := ExactQ.dist_eq_sub_of_le (ExactQ.le_trans hx_le hy_ge)
          -- (mid - x) + (y - mid) ≈ y - x
          have hsub_add : (ExactQ.add (B.midpoint.sub x) (y.sub B.midpoint)).equiv (y.sub x) := by
            unfold ExactQ.equiv ExactQ.add ExactQ.sub; dsimp only
            simp only [Int.natCast_mul]; grind
          have hcongr : (ExactQ.add (x.dist B.midpoint) (B.midpoint.dist y)).equiv
                        (ExactQ.add (B.midpoint.sub x) (y.sub B.midpoint)) := by
            unfold ExactQ.equiv ExactQ.add at *; dsimp only at *
            simp only [Int.natCast_mul] at *; grind
          exact ExactQ.equiv_trans (ExactQ.equiv_trans hcongr hsub_add) (ExactQ.equiv_symm d3)
        have hq_dist : (ExactQ.add (q.mul (x.dist B.midpoint)) (q.mul (B.midpoint.dist y))).equiv
                       (q.mul (x.dist y)) := by
          have hmul_congr : (q.mul (ExactQ.add (x.dist B.midpoint) (B.midpoint.dist y))).equiv
                            (q.mul (x.dist y)) := by
            unfold ExactQ.equiv ExactQ.mul at *; dsimp only at *
            simp only [Int.natCast_mul] at *; grind
          exact ExactQ.equiv_trans (ExactQ.mul_add_left_equiv q _ _) hmul_congr
        exact ExactQ.le_trans htri (ExactQ.le_congr_right hq_dist hadd)
      · -- Symmetric telescoping: y ≤ mid ≤ x!
        rcases hinvL B.midpoint (DyadicBall.midpoint_mem_left B) with ⟨fm, hfm, _⟩
        have h1 := hlipR x B.midpoint fx fm hxR (DyadicBall.midpoint_mem_right B) hfx hfm
        have h2 := hlipL B.midpoint y fm fy (DyadicBall.midpoint_mem_left B) hyL hfm hfy
        have htri := ExactQ.dist_triangle fx fm fy
        have hadd := ExactQ.add_le_add h1 h2
        have hsum_dist : (ExactQ.add (x.dist B.midpoint) (B.midpoint.dist y)).equiv (x.dist y) := by
          have d1 := ExactQ.equiv_trans (ExactQ.dist_symm x B.midpoint) (ExactQ.dist_eq_sub_of_le hx_ge)
          have d2 := ExactQ.equiv_trans (ExactQ.dist_symm B.midpoint y) (ExactQ.dist_eq_sub_of_le hy_le)
          have d3 := ExactQ.equiv_trans (ExactQ.dist_symm x y) (ExactQ.dist_eq_sub_of_le (ExactQ.le_trans hy_le hx_ge))
          have hsub_add : (ExactQ.add (x.sub B.midpoint) (B.midpoint.sub y)).equiv (x.sub y) := by
            unfold ExactQ.equiv ExactQ.add ExactQ.sub; dsimp only
            simp only [Int.natCast_mul]; grind
          have hcongr : (ExactQ.add (x.dist B.midpoint) (B.midpoint.dist y)).equiv
                        (ExactQ.add (x.sub B.midpoint) (B.midpoint.sub y)) := by
            unfold ExactQ.equiv ExactQ.add at *; dsimp only at *
            simp only [Int.natCast_mul] at *; grind
          exact ExactQ.equiv_trans (ExactQ.equiv_trans hcongr hsub_add) (ExactQ.equiv_symm d3)
        have hq_dist : (ExactQ.add (q.mul (x.dist B.midpoint)) (q.mul (B.midpoint.dist y))).equiv
                       (q.mul (x.dist y)) := by
          have hmul_congr : (q.mul (ExactQ.add (x.dist B.midpoint) (B.midpoint.dist y))).equiv
                            (q.mul (x.dist y)) := by
            unfold ExactQ.equiv ExactQ.mul at *; dsimp only at *
            simp only [Int.natCast_mul] at *; grind
          exact ExactQ.equiv_trans (ExactQ.mul_add_left_equiv q _ _) hmul_congr
        exact ExactQ.le_trans htri (ExactQ.le_congr_right hq_dist hadd)
      · exact hlipR x y fx fy hxR hyR hfx hfy

-- 2D Parameter-State Subdivision Soundness Meta-Theorem
theorem checkParamTree_sound (e : Expr) (P B0 : DyadicBall) (qNum qExp : Nat) (t : ParamTree)
    (hchk : checkParamTree e P B0 qNum qExp t = true)
    (p : ExactQ) (hp : P.contains p) :
    IsSelfMappedLipschitz e p B0 B0 (ExactQ.ofDyadic (qNum : Int) qExp) := by
  induction t generalizing P with
  | pleaf st =>
    unfold checkParamTree at hchk
    exact checkStateTree_sound e P B0 B0 qNum qExp st hchk p hp
  | psplit l r ihl ihr =>
    unfold checkParamTree at hchk
    simp only [Bool.and_eq_true] at hchk
    rcases DyadicBall.bisect_cover hp with ⟨hpL, _⟩ | ⟨hpR, _⟩
    · exact ihl P.bisectLeft hchk.1 hpL
    · exact ihr P.bisectRight hchk.2 hpR

-- ============================================================================
-- GENERAL INFINITE (∀ n : Nat) LIFTING META-THEOREMS
-- ============================================================================

theorem contraction_certified_properties (cert : ParamContractionCert)
    (hchk : checkParamContraction cert = true)
    (p : ExactQ) (hp : cert.p0.contains p) :
    cert.qNum < 2 ^ cert.qExp ∧
    IsSelfMappedLipschitz cert.expr p cert.b0 cert.b0 (ExactQ.ofDyadic (cert.qNum : Int) cert.qExp) := by
  unfold checkParamContraction at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
  exact ⟨hchk.1, checkParamTree_sound cert.expr cert.p0 cert.b0 cert.qNum cert.qExp cert.tree hchk.2 p hp⟩

/-- Meta-Theorem 1: Global Orbit Well-Definedness & Invariance (∀ n : Nat). -/
theorem contraction_orbit_invariant (cert : ParamContractionCert)
    (hchk : checkParamContraction cert = true)
    (p : ExactQ) (hp : cert.p0.contains p)
    (x0 : ExactQ) (hx0 : cert.b0.contains x0) :
    ∀ n : Nat, ∃ xn, iterQ cert.expr p n x0 = some xn ∧ cert.b0.contains xn := by
  have ⟨_, hinv, _⟩ := contraction_certified_properties cert hchk p hp
  intro n
  induction n with
  | zero => exact ⟨x0, rfl, hx0⟩
  | succ k ih =>
    rcases ih with ⟨xk, hxk, hmem⟩
    rcases hinv xk hmem with ⟨xk1, hstep, hmem1⟩
    exact ⟨xk1, by simp [iterQ, hxk, hstep], hmem1⟩

/-- Meta-Theorem 2: Global Exponential Orbit Contraction (∀ n : Nat). -/
theorem contraction_orbit_decay (cert : ParamContractionCert)
    (hchk : checkParamContraction cert = true)
    (p : ExactQ) (hp : cert.p0.contains p)
    (x0 y0 : ExactQ) (hx0 : cert.b0.contains x0) (hy0 : cert.b0.contains y0) :
    ∀ n : Nat, ∀ xn yn,
      iterQ cert.expr p n x0 = some xn →
      iterQ cert.expr p n y0 = some yn →
      (xn.dist yn).le (((ExactQ.ofDyadic (cert.qNum : Int) cert.qExp).pow n).mul (x0.dist y0)) := by
  have ⟨_, hinv, hlip⟩ := contraction_certified_properties cert hchk p hp
  let q := ExactQ.ofDyadic (cert.qNum : Int) cert.qExp
  have hq_nn : 0 ≤ q.num := by dsimp [q, ExactQ.ofDyadic]; exact Int.natCast_nonneg cert.qNum
  intro n
  induction n with
  | zero =>
    intro xn yn hxn hyn
    simp only [iterQ, Option.some.injEq] at hxn hyn
    subst hxn; subst hyn
    exact ExactQ.le_of_equiv (ExactQ.equiv_symm (ExactQ.mul_one_left_equiv (x0.dist y0)))
  | succ k ih =>
    intro xn1 yn1 hxn1 hyn1
    simp only [iterQ, Option.bind_eq_some_iff] at hxn1 hyn1
    rcases hxn1 with ⟨xk, hxk, hstepx⟩
    rcases hyn1 with ⟨yk, hyk, hstepy⟩
    rcases contraction_orbit_invariant cert hchk p hp x0 hx0 k with ⟨xk', hxk', hmemx⟩
    rcases contraction_orbit_invariant cert hchk p hp y0 hy0 k with ⟨yk', hyk', hmemy⟩
    rw [hxk] at hxk'; injection hxk' with ex; subst ex
    rw [hyk] at hyk'; injection hyk' with ey; subst ey
    have hstep := hlip xk yk xn1 yn1 hmemx hmemy hstepx hstepy
    have hik := ih xk yk hxk hyk
    have hmul := ExactQ.mul_le_mul_of_nonneg_left hq_nn hik
    have hassoc := ExactQ.equiv_symm (ExactQ.mul_assoc_equiv q (q.pow k) (x0.dist y0))
    exact ExactQ.le_trans hstep (ExactQ.le_congr_right hassoc hmul)

/-- Meta-Theorem 3: Exponential Step/Residual Decay |x_{n+1} - x_n| ≤ q^n |x_1 - x_0| (∀ n : Nat). -/
theorem contraction_residual_decay (cert : ParamContractionCert)
    (hchk : checkParamContraction cert = true)
    (p : ExactQ) (hp : cert.p0.contains p)
    (x0 x1 : ExactQ) (hx0 : cert.b0.contains x0) (hx1 : evalQ cert.expr p x0 = some x1) :
    ∀ n : Nat, ∀ xn xn1,
      iterQ cert.expr p n x0 = some xn →
      evalQ cert.expr p xn = some xn1 →
      (xn1.dist xn).le (((ExactQ.ofDyadic (cert.qNum : Int) cert.qExp).pow n).mul (x1.dist x0)) := by
  have ⟨_, hinv, _⟩ := contraction_certified_properties cert hchk p hp
  have hx1_mem : cert.b0.contains x1 := by
    rcases hinv x0 hx0 with ⟨x1', hx1', hmem⟩
    rw [hx1] at hx1'; injection hx1' with e; subst e; exact hmem
  have hshift : ∀ k : Nat, ∀ z, iterQ cert.expr p k x1 = some z ↔ iterQ cert.expr p (k + 1) x0 = some z := by
    intro k
    induction k with
    | zero =>
      intro z
      simp [iterQ, hx1]
    | succ m ihm =>
      intro z
      change (Option.bind (iterQ cert.expr p m x1) (fun xn => evalQ cert.expr p xn) = some z) ↔
             (Option.bind (iterQ cert.expr p (m + 1) x0) (fun xn => evalQ cert.expr p xn) = some z)
      simp only [Option.bind_eq_some_iff]
      constructor
      · rintro ⟨w, hw, hst⟩; exact ⟨w, (ihm w).mp hw, hst⟩
      · rintro ⟨w, hw, hst⟩; exact ⟨w, (ihm w).mpr hw, hst⟩
  intro n xn xn1 hxn hstep
  have hxn1 : iterQ cert.expr p n x1 = some xn1 := (hshift n xn1).mpr (by simp [iterQ, hxn, hstep])
  exact contraction_orbit_decay cert hchk p hp x1 x0 hx1_mem hx0 n xn1 xn hxn1 hxn

private theorem cauchy_step_rearrange (oneMinusQ q qk d0 d_tail : ExactQ)
    (h1pq : (oneMinusQ.add q).equiv (ExactQ.ofInt 1)) :
    ((ExactQ.add (oneMinusQ.mul (qk.mul d0)) d_tail).add ((q.mul qk).mul d0)).equiv
    (d_tail.add (qk.mul d0)) := by
  unfold ExactQ.equiv ExactQ.add ExactQ.mul ExactQ.ofInt at *; dsimp only at *
  simp only [Int.natCast_mul] at *
  grind

private theorem cauchy_zero_add (a b z : ExactQ) (hz : z.equiv (ExactQ.ofInt 0)) :
    ((a.mul z).add b).equiv b := by
  unfold ExactQ.equiv ExactQ.add ExactQ.mul ExactQ.ofInt at *; dsimp only at *
  simp only [Int.natCast_mul] at *
  grind

private theorem cauchy_drop_nonneg (a b : ExactQ) (hb : 0 ≤ b.num) :
    a.le (a.add b) := by
  unfold ExactQ.le ExactQ.add; dsimp only
  simp only [Int.natCast_mul]
  have hd1 := Int.le_of_lt (ExactQ.den_int_pos a)
  have hprod := Int.mul_nonneg (Int.mul_nonneg hb hd1) hd1
  grind

/-- Meta-Theorem 4: Quantitative Cauchy Convergence (∀ n m : Nat):
    (1 - q) * |x_{n+m} - x_n| ≤ q^n * |x_1 - x_0|. -/
theorem contraction_cauchy_bound (cert : ParamContractionCert)
    (hchk : checkParamContraction cert = true)
    (p : ExactQ) (hp : cert.p0.contains p)
    (x0 x1 : ExactQ) (hx0 : cert.b0.contains x0) (hx1 : evalQ cert.expr p x0 = some x1) :
    let q := ExactQ.ofDyadic (cert.qNum : Int) cert.qExp
    let oneMinusQ := ExactQ.ofDyadic ((2 ^ cert.qExp : Int) - (cert.qNum : Int)) cert.qExp
    ∀ n m : Nat, ∀ xn xnm,
      iterQ cert.expr p n x0 = some xn →
      iterQ cert.expr p (n + m) x0 = some xnm →
      (oneMinusQ.mul (xnm.dist xn)).le ((q.pow n).mul (x1.dist x0)) := by
  intro q oneMinusQ n m
  have ⟨hq_lt, _, _⟩ := contraction_certified_properties cert hchk p hp
  have hq_nn : 0 ≤ q.num := by dsimp [q, ExactQ.ofDyadic]; exact Int.natCast_nonneg cert.qNum
  have h1mq_pos : 0 < oneMinusQ.num := by
    dsimp [oneMinusQ, ExactQ.ofDyadic]
    have : (cert.qNum : Int) < ((2 ^ cert.qExp : Nat) : Int) := Int.ofNat_lt.mpr hq_lt
    have hpow : ((2 ^ cert.qExp : Nat) : Int) = (2 : Int) ^ cert.qExp := by simp [Int.natCast_pow]
    omega
  have h1mq_nn : 0 ≤ oneMinusQ.num := Int.le_of_lt h1mq_pos
  have h1pq : (oneMinusQ.add q).equiv (ExactQ.ofInt 1) := by
    unfold ExactQ.equiv ExactQ.add ExactQ.ofInt
    dsimp only [oneMinusQ, q, ExactQ.ofDyadic]
    simp only [Int.natCast_mul]
    have hpow : ((2 ^ cert.qExp : Nat) : Int) = (2 : Int) ^ cert.qExp := by simp [Int.natCast_pow]
    rw [← hpow, Int.natCast_one]
    rw [Int.sub_mul, Int.sub_add_cancel, Int.mul_one, Int.one_mul]
  have hstrong : ∀ k : Nat, ∀ xn xnk,
      iterQ cert.expr p n x0 = some xn →
      iterQ cert.expr p (n + k) x0 = some xnk →
      ((oneMinusQ.mul (xnk.dist xn)).add ((q.pow (n + k)).mul (x1.dist x0))).le
      ((q.pow n).mul (x1.dist x0)) := by
    intro k
    induction k with
    | zero =>
      intro xn xnk hxn hxnk
      simp only [Nat.add_zero] at hxnk
      rw [hxn] at hxnk; injection hxnk with e; subst e
      have hd0 : (xn.dist xn).equiv (ExactQ.ofInt 0) := by
        unfold ExactQ.equiv ExactQ.dist ExactQ.abs ExactQ.sub ExactQ.ofInt; dsimp only; omega
      exact ExactQ.le_of_equiv (cauchy_zero_add oneMinusQ ((q.pow n).mul (x1.dist x0)) (xn.dist xn) hd0)
    | succ j ih =>
      intro xn xnj1 hxn hxnj1
      have hsucc : n + (j + 1) = (n + j) + 1 := by omega
      rw [hsucc] at hxnj1
      simp only [iterQ, Option.bind_eq_some_iff] at hxnj1
      rcases hxnj1 with ⟨xnj, hxnj, hstep⟩
      have hih := ih xn xnj hxn hxnj
      have hres := contraction_residual_decay cert hchk p hp x0 x1 hx0 hx1 (n + j) xnj xnj1 hxnj hstep
      have htri := ExactQ.dist_triangle xnj1 xnj xn
      have hmul_tri := ExactQ.mul_le_mul_of_nonneg_left h1mq_nn htri
      have hmul_res := ExactQ.mul_le_mul_of_nonneg_left h1mq_nn hres
      rw [hsucc]
      have hstep1 : ((oneMinusQ.mul (xnj1.dist xn)).add ((q.pow (n + j + 1)).mul (x1.dist x0))).le
          ((ExactQ.add (oneMinusQ.mul (xnj1.dist xnj)) (oneMinusQ.mul (xnj.dist xn))).add ((q.pow (n + j + 1)).mul (x1.dist x0))) := by
        apply ExactQ.add_le_add _ (ExactQ.le_refl _)
        exact ExactQ.le_congr_right (ExactQ.equiv_symm (ExactQ.mul_add_left_equiv oneMinusQ _ _)) hmul_tri
      have hstep2 : ((ExactQ.add (oneMinusQ.mul (xnj1.dist xnj)) (oneMinusQ.mul (xnj.dist xn))).add ((q.pow (n + j + 1)).mul (x1.dist x0))).le
          ((ExactQ.add (oneMinusQ.mul ((q.pow (n + j)).mul (x1.dist x0))) (oneMinusQ.mul (xnj.dist xn))).add ((q.pow (n + j + 1)).mul (x1.dist x0))) := by
        apply ExactQ.add_le_add _ (ExactQ.le_refl _)
        exact ExactQ.add_le_add hmul_res (ExactQ.le_refl _)
      have hrearr := cauchy_step_rearrange oneMinusQ q (q.pow (n + j)) (x1.dist x0) (oneMinusQ.mul (xnj.dist xn)) h1pq
      exact ExactQ.le_trans hstep1 (ExactQ.le_trans hstep2 (ExactQ.le_congr_left (ExactQ.equiv_symm hrearr) hih))
  intro xn xnm hxn hxnm
  have hst := hstrong m xn xnm hxn hxnm
  have hnn : 0 ≤ ((q.pow (n + m)).mul (x1.dist x0)).num := by
    unfold ExactQ.mul; dsimp only
    exact Int.mul_nonneg (ExactQ.pow_nonneg hq_nn (n + m)) (ExactQ.abs_nonneg _)
  exact ExactQ.le_trans (cauchy_drop_nonneg _ _ hnn) hst

/-- Meta-Theorem 5: Uniqueness of Fixed Points in B0. -/
theorem contraction_fixed_point_unique (cert : ParamContractionCert)
    (hchk : checkParamContraction cert = true)
    (p : ExactQ) (hp : cert.p0.contains p)
    (xs ys fxs fys : ExactQ) (hxs : cert.b0.contains xs) (hys : cert.b0.contains ys)
    (hfx : evalQ cert.expr p xs = some fxs) (heqx : fxs.equiv xs)
    (hfy : evalQ cert.expr p ys = some fys) (heqy : fys.equiv ys) :
    xs.equiv ys := by
  have ⟨hq_lt, _, hlip⟩ := contraction_certified_properties cert hchk p hp
  have h1 := hlip xs ys fxs fys hxs hys hfx hfy
  have h2 : (xs.dist ys).le ((ExactQ.ofDyadic (cert.qNum : Int) cert.qExp).mul (xs.dist ys)) :=
    ExactQ.le_congr_left (ExactQ.dist_congr heqx heqy) h1
  unfold ExactQ.le ExactQ.mul ExactQ.ofDyadic at h2; dsimp only at h2
  simp only [Int.natCast_mul] at h2
  have hpow_gt : (cert.qNum : Int) < ((2 ^ cert.qExp : Nat) : Int) := Int.ofNat_lt.mpr hq_lt
  have hdd := ExactQ.den_int_pos (xs.dist ys)
  have hd_nn := ExactQ.abs_nonneg (xs.sub ys)
  -- (xs.dist ys).num * (2^qExp * d) ≤ qNum * (xs.dist ys).num * d, with qNum < 2^qExp and d > 0 ⇒ num = 0!
  have hnum0 : (xs.dist ys).num ≤ 0 := by
    by_cases hpos : 0 < (xs.dist ys).num
    · have hlt1 : (cert.qNum : Int) * (xs.dist ys).num < ((2 ^ cert.qExp : Nat) : Int) * (xs.dist ys).num :=
        Int.mul_lt_mul_of_pos_right hpow_gt hpos
      have hlt2 : (cert.qNum : Int) * (xs.dist ys).num * ((xs.dist ys).den : Int) <
                  ((2 ^ cert.qExp : Nat) : Int) * (xs.dist ys).num * ((xs.dist ys).den : Int) :=
        Int.mul_lt_mul_of_pos_right hlt1 hdd
      grind
    · omega
  exact ExactQ.equiv_of_dist_le_zero (by unfold ExactQ.le ExactQ.ofInt; dsimp only; omega)

/-- Meta-Theorem 6: Exact Exponential Convergence Rate to Any Fixed Point x* ∈ B0 (∀ n : Nat). -/
theorem contraction_fixed_point_distance (cert : ParamContractionCert)
    (hchk : checkParamContraction cert = true)
    (p : ExactQ) (hp : cert.p0.contains p)
    (x0 xs fxs : ExactQ) (hx0 : cert.b0.contains x0) (hxs : cert.b0.contains xs)
    (hfxs : evalQ cert.expr p xs = some fxs) (heqxs : fxs.equiv xs) :
    ∀ n : Nat, ∀ xn,
      iterQ cert.expr p n x0 = some xn →
      (xn.dist xs).le (((ExactQ.ofDyadic (cert.qNum : Int) cert.qExp).pow n).mul (x0.dist xs)) := by
  have ⟨_, _, hlip⟩ := contraction_certified_properties cert hchk p hp
  let q := ExactQ.ofDyadic (cert.qNum : Int) cert.qExp
  have hq_nn : 0 ≤ q.num := by dsimp [q, ExactQ.ofDyadic]; exact Int.natCast_nonneg cert.qNum
  intro n
  induction n with
  | zero =>
    intro xn hxn
    simp only [iterQ, Option.some.injEq] at hxn; subst hxn
    exact ExactQ.le_of_equiv (ExactQ.equiv_symm (ExactQ.mul_one_left_equiv _))
  | succ k ih =>
    intro xn1 hxn1
    simp only [iterQ, Option.bind_eq_some_iff] at hxn1
    rcases hxn1 with ⟨xk, hxk, hstep⟩
    rcases contraction_orbit_invariant cert hchk p hp x0 hx0 k with ⟨xk', hxk', hmemx⟩
    rw [hxk] at hxk'; injection hxk' with ex; subst ex
    have h1 := hlip xk xs xn1 fxs hmemx hxs hstep hfxs
    have h2 : (xn1.dist xs).le (q.mul (xk.dist xs)) :=
      ExactQ.le_congr_left (ExactQ.dist_congr (ExactQ.equiv_refl xn1) heqxs) h1
    have h3 := ExactQ.mul_le_mul_of_nonneg_left hq_nn (ih xk hxk)
    have hassoc := ExactQ.equiv_symm (ExactQ.mul_assoc_equiv q (q.pow k) (x0.dist xs))
    exact ExactQ.le_trans h2 (ExactQ.le_congr_right hassoc h3)

-- ============================================================================
-- PART 5: Finite Binary Certificates, Discharged Infinite Theorems,
--         Binary-Scaling Lift, Sharpness Witnesses, Mutation Tests & Axioms
-- ============================================================================

-- 5.1 Synthesized Finite Binary Certificates (Exported from explore_and_verify.py)

theorem certHalley_valid : checkParamContraction certHalley = true := by decide
theorem certBring_valid : checkParamContraction certBring = true := by decide
theorem certBringTight_valid : checkParamContraction certBringTight = true := by decide
theorem certLogistic_valid : checkParamContraction certLogistic = true := by decide
theorem certBringAlt_valid : checkParamContraction certBringAlt = true := by decide

-- 5.2 Discharged Infinite Theorem 1: Universal Binary-Scaled Halley Square Root
--     (∀ A ∈ ExactQ_{>0}, ∀ n : Nat)

/-- Compact Halley Square-Root Contraction on [1, 4] × [15/16, 17/8] (discharged by certHalley). -/
theorem halley_compact_contraction (a : ExactQ) (ha : certHalley.p0.contains a)
    (x0 y0 : ExactQ) (hx0 : certHalley.b0.contains x0) (hy0 : certHalley.b0.contains y0) :
    (∀ n : Nat, ∃ xn, iterQ exprHalley a n x0 = some xn ∧ certHalley.b0.contains xn) ∧
    (∀ n : Nat, ∀ xn yn, iterQ exprHalley a n x0 = some xn → iterQ exprHalley a n y0 = some yn →
      (xn.dist yn).le (((ExactQ.ofDyadic 7 3).pow n).mul (x0.dist y0))) :=
  ⟨contraction_orbit_invariant certHalley certHalley_valid a ha x0 hx0,
   contraction_orbit_decay certHalley certHalley_valid a ha x0 y0 hx0 hy0⟩

theorem pow2Q_pos (k : Int) : 0 < (pow2Q k).num := by
  cases k with
  | ofNat n =>
    unfold pow2Q ExactQ.ofInt; dsimp only
    have : 0 < 2 ^ n := Nat.pow_pos (by omega); omega
  | negSucc n =>
    unfold pow2Q ExactQ.ofDyadic; dsimp only; omega

theorem pow2Q_mul_neg_equiv (k : Int) : ((pow2Q k).mul (pow2Q (-k))).equiv (ExactQ.ofInt 1) := by
  cases k with
  | ofNat n =>
    cases n with
    | zero =>
      unfold pow2Q ExactQ.equiv ExactQ.mul ExactQ.ofInt; dsimp only; rfl
    | succ m =>
      have hneg : -(Int.ofNat (m + 1)) = Int.negSucc m := rfl
      rw [hneg]
      unfold pow2Q ExactQ.equiv ExactQ.mul ExactQ.ofInt ExactQ.ofDyadic; dsimp only
      simp only [Int.natCast_mul]; grind
  | negSucc n =>
    have hneg : -(Int.negSucc n) = Int.ofNat (n + 1) := rfl
    rw [hneg]
    unfold pow2Q ExactQ.equiv ExactQ.mul ExactQ.ofInt ExactQ.ofDyadic; dsimp only
    simp only [Int.natCast_mul]; grind

/-- Helper: For any positive naturals q ≤ p, ∃ m, q * 4^m ≤ p < q * 4^(m+1). -/
private theorem nat_pow4_bracket (q : Nat) (hq : 0 < q) :
    ∀ p : Nat, q ≤ p → ∃ m : Nat, q * 4 ^ m ≤ p ∧ p < q * 4 ^ (m + 1) := by
  intro p
  induction p with
  | zero => intro h; omega
  | succ n ih =>
    intro hle
    by_cases heq : q = n + 1
    · refine ⟨0, by simp [heq], ?_⟩
      simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
      omega
    · rcases ih (by omega) with ⟨m, hm1, hm2⟩
      by_cases hlt : n + 1 < q * 4 ^ (m + 1)
      · exact ⟨m, by omega, hlt⟩
      · refine ⟨m + 1, by omega, ?_⟩
        have hpos : 0 < q * 4 ^ (m + 1) := Nat.mul_pos hq (Nat.pow_pos (by omega))
        have hpow : q * 4 ^ (m + 1 + 1) = q * 4 ^ (m + 1) * 4 := by
          rw [Nat.pow_succ, Nat.mul_assoc]
        omega

/-- Exact binary normalization of ANY positive rational A > 0 into [1, 4] via 4^k = (2^k)^2! -/
theorem exists_binary_norm_4 (A : ExactQ) (hA : 0 < A.num) :
    ∃ k : Int, certHalley.p0.contains (A.mul ((pow2Q (-k)).sqr)) := by
  have hp_pos : 0 < A.num.toNat := by omega
  have hq_pos : 0 < A.den := A.den_pos
  have hAn : (A.num.toNat : Int) = A.num := by omega
  by_cases hge : A.den ≤ A.num.toNat
  · rcases nat_pow4_bracket A.den hq_pos A.num.toNat hge with ⟨m, hm1, hm2⟩
    refine ⟨Int.ofNat m, ?_⟩
    cases m with
    | zero =>
      have h0 : -(Int.ofNat 0) = Int.ofNat 0 := rfl
      rw [h0]
      unfold certHalley pow2Q ExactQ.mul ExactQ.sqr ExactQ.ofInt DyadicBall.contains; dsimp only
      simp only [Nat.pow_zero, Nat.mul_one, Nat.pow_one] at hm1 hm2 ⊢
      omega
    | succ r =>
      have hneg : -(Int.ofNat (r + 1)) = Int.negSucc r := rfl
      rw [hneg]
      unfold certHalley pow2Q ExactQ.mul ExactQ.sqr ExactQ.ofDyadic DyadicBall.contains; dsimp only
      have h4 : (2 ^ (r + 1) * 2 ^ (r + 1) : Nat) = 4 ^ (r + 1) := by rw [← Nat.mul_pow]
      have h4' : A.den * 4 ^ (r + 1 + 1) = 4 * (A.den * 4 ^ (r + 1)) := by
        rw [Nat.pow_succ, Nat.mul_comm (4 ^ (r + 1)) 4, ← Nat.mul_assoc, Nat.mul_comm A.den 4, Nat.mul_assoc]
      rw [h4]
      rw [h4'] at hm2
      simp only [Int.natCast_mul]
      omega
  · rcases nat_pow4_bracket A.num.toNat hp_pos A.den (by omega) with ⟨m, hm1, hm2⟩
    refine ⟨Int.negSucc m, ?_⟩
    have hneg : -(Int.negSucc m) = Int.ofNat (m + 1) := rfl
    rw [hneg]
    unfold certHalley pow2Q ExactQ.mul ExactQ.sqr ExactQ.ofInt DyadicBall.contains; dsimp only
    have h4 : (2 ^ (m + 1) * 2 ^ (m + 1) : Nat) = 4 ^ (m + 1) := by rw [← Nat.mul_pow]
    have h4' : A.num.toNat * 4 ^ (m + 1) = 4 * (A.num.toNat * 4 ^ m) := by
      rw [Nat.pow_succ, Nat.mul_comm (4 ^ m) 4, ← Nat.mul_assoc, Nat.mul_comm A.num.toNat 4, Nat.mul_assoc]
    have h4int : ((2 ^ (m + 1) : Nat) : Int) * ((2 ^ (m + 1) : Nat) : Int) = ((4 ^ (m + 1) : Nat) : Int) := by
      rw [← Int.natCast_mul, h4]
    rw [h4int]
    have h1 : A.den ≤ A.num.toNat * 4 ^ (m + 1) := by omega
    have h2 : A.num.toNat * 4 ^ (m + 1) ≤ 4 * A.den := by rw [h4']; omega
    have h1i : (A.den : Int) ≤ A.num * ((4 ^ (m + 1) : Nat) : Int) := by
      have : (A.den : Int) ≤ ((A.num.toNat * 4 ^ (m + 1) : Nat) : Int) := Int.ofNat_le.mpr h1
      rw [Int.natCast_mul, hAn] at this; exact this
    have h2i : A.num * ((4 ^ (m + 1) : Nat) : Int) ≤ 4 * (A.den : Int) := by
      have : ((A.num.toNat * 4 ^ (m + 1) : Nat) : Int) ≤ ((4 * A.den : Nat) : Int) := Int.ofNat_le.mpr h2
      rw [Int.natCast_mul, Int.natCast_mul, hAn] at this; exact this
    omega

/-- Closed-form evaluation helper for exprHalley. -/
theorem evalQ_halley_iff (a x y : ExactQ) :
    evalQ exprHalley a x = some y ↔
      ∃ (hden : 0 < (((ExactQ.ofInt 3).mul x.sqr).add a).num),
        y = x.sub (((ExactQ.ofInt 2).mul (x.mul (x.sqr.sub a))).mul
                   ((((ExactQ.ofInt 3).mul x.sqr).add a).invPos hden)) := by
  simp only [exprHalley, evalQ, Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.some.injEq]
  constructor
  · rintro ⟨_, rfl, _, ⟨_, ⟨_, rfl, _, ⟨_, rfl, _, ⟨_, ⟨_, rfl, rfl⟩, _, rfl, rfl⟩, rfl⟩, rfl⟩,
      _, ⟨_, ⟨_, ⟨_, rfl, _, ⟨_, rfl, rfl⟩, rfl⟩, _, rfl, rfl⟩, hinv⟩, rfl⟩, rfl⟩
    split at hinv
    · rename_i hpos; injection hinv with hyeq; subst hyeq; exact ⟨hpos, rfl⟩
    · cases hinv
  · rintro ⟨hpos, rfl⟩
    refine ⟨x, rfl, _, ⟨_, ⟨ExactQ.ofInt 2, rfl, _, ⟨x, rfl, _, ⟨_, ⟨x, rfl, rfl⟩, a, rfl, rfl⟩, rfl⟩, rfl⟩,
      _, ⟨_, ⟨_, ⟨ExactQ.ofInt 3, rfl, _, ⟨x, rfl, rfl⟩, rfl⟩, a, rfl, rfl⟩, ?_⟩, rfl⟩, rfl⟩
    simp [hpos]

/-- Exact Scale-Equivariance of Halley's Map: H_{s^2 * a}(s * x) ≈ s * H_a(x) for any s > 0! -/
theorem halley_step_equivariant (a x s fx : ExactQ) (hs : 0 < s.num)
    (hfx : evalQ exprHalley a x = some fx) :
    ∃ fxs, evalQ exprHalley (a.mul s.sqr) (x.mul s) = some fxs ∧ fxs.equiv (fx.mul s) := by
  rcases (evalQ_halley_iff a x fx).mp hfx with ⟨hden_pos, rfl⟩
  have hscaled_pos : 0 < (((ExactQ.ofInt 3).mul (x.mul s).sqr).add (a.mul s.sqr)).num := by
    unfold ExactQ.add ExactQ.mul ExactQ.sqr ExactQ.ofInt at hden_pos ⊢; dsimp only at hden_pos ⊢
    simp only [Int.natCast_mul, Int.natCast_one] at hden_pos ⊢
    have hs2 : 0 < s.num * s.num := Int.mul_pos hs hs
    have hsd2 : 0 < (s.den : Int) * (s.den : Int) := Int.mul_pos (ExactQ.den_int_pos s) (ExactQ.den_int_pos s)
    have hprod : 0 < ((3 * (x.num * x.num) * (a.den : Int) + a.num * (1 * ((x.den : Int) * (x.den : Int)))) *
                      (s.num * s.num) * ((s.den : Int) * (s.den : Int))) :=
      Int.mul_pos (Int.mul_pos hden_pos hs2) hsd2
    have hident : (((3 * (x.num * s.num * (x.num * s.num)) * ((a.den : Int) * ((s.den : Int) * (s.den : Int))) +
                     a.num * (s.num * s.num) * (1 * ((x.den : Int) * (s.den : Int) * ((x.den : Int) * (s.den : Int)))))) =
                   ((3 * (x.num * x.num) * (a.den : Int) + a.num * (1 * ((x.den : Int) * (x.den : Int)))) *
                    (s.num * s.num) * ((s.den : Int) * (s.den : Int)))) := by grind
    omega
  refine ⟨_, (evalQ_halley_iff (a.mul s.sqr) (x.mul s) _).mpr ⟨hscaled_pos, rfl⟩, ?_⟩
  unfold ExactQ.equiv ExactQ.sub ExactQ.add ExactQ.mul ExactQ.sqr ExactQ.invPos ExactQ.ofInt; dsimp only
  have htn1 : ((((ExactQ.ofInt 3).mul x.sqr).add a).num.toNat : Int) =
              (((ExactQ.ofInt 3).mul x.sqr).add a).num := by omega
  have htn2 : ((((ExactQ.ofInt 3).mul (x.mul s).sqr).add (a.mul s.sqr)).num.toNat : Int) =
              (((ExactQ.ofInt 3).mul (x.mul s).sqr).add (a.mul s.sqr)).num := by omega
  simp only [ExactQ.add, ExactQ.mul, ExactQ.sqr, ExactQ.ofInt, Int.natCast_mul, Int.natCast_one] at htn1 htn2 ⊢
  rw [htn1, htn2]
  grind

/-- Helper: evalQ respectfulness under ExactQ.equiv for Halley's map. -/
theorem evalQ_equiv_congr (e : Expr) {p1 p2 x1 x2 y1 : ExactQ}
    (hp : p1.equiv p2) (hx : x1.equiv x2) (hy1 : evalQ e p1 x1 = some y1) :
    ∃ y2, evalQ e p2 x2 = some y2 ∧ y1.equiv y2 := by
  induction e generalizing y1 with
  | var =>
    simp only [evalQ, Option.some.injEq] at hy1; subst hy1
    exact ⟨x2, rfl, hx⟩
  | param =>
    simp only [evalQ, Option.some.injEq] at hy1; subst hy1
    exact ⟨p2, rfl, hp⟩
  | constInt z =>
    simp only [evalQ, Option.some.injEq] at hy1; subst hy1
    exact ⟨ExactQ.ofInt z, rfl, ExactQ.equiv_refl _⟩
  | constDyadic m ex =>
    simp only [evalQ, Option.some.injEq] at hy1; subst hy1
    exact ⟨ExactQ.ofDyadic m ex, rfl, ExactQ.equiv_refl _⟩
  | neg a ih =>
    simp only [evalQ, Option.map_eq_some_iff] at hy1
    rcases hy1 with ⟨ya, hya, rfl⟩
    rcases ih hya with ⟨yb, hyb, heq⟩
    refine ⟨yb.neg, by simp [evalQ, hyb], ?_⟩
    unfold ExactQ.equiv ExactQ.neg at *; dsimp only; grind
  | add a b iha ihb =>
    simp only [evalQ, Option.bind_eq_some_iff, Option.some.injEq] at hy1
    rcases hy1 with ⟨ya, hya, yb, hyb, rfl⟩
    rcases iha hya with ⟨ya', hya', heqa⟩
    rcases ihb hyb with ⟨yb', hyb', heqb⟩
    refine ⟨ya'.add yb', by simp [evalQ, hya', hyb'], ?_⟩
    unfold ExactQ.equiv ExactQ.add at *; dsimp only; simp only [Int.natCast_mul]; grind
  | sub a b iha ihb =>
    simp only [evalQ, Option.bind_eq_some_iff, Option.some.injEq] at hy1
    rcases hy1 with ⟨ya, hya, yb, hyb, rfl⟩
    rcases iha hya with ⟨ya', hya', heqa⟩
    rcases ihb hyb with ⟨yb', hyb', heqb⟩
    refine ⟨ya'.sub yb', by simp [evalQ, hya', hyb'], ?_⟩
    unfold ExactQ.equiv ExactQ.sub at *; dsimp only; simp only [Int.natCast_mul]; grind
  | mul a b iha ihb =>
    simp only [evalQ, Option.bind_eq_some_iff, Option.some.injEq] at hy1
    rcases hy1 with ⟨ya, hya, yb, hyb, rfl⟩
    rcases iha hya with ⟨ya', hya', heqa⟩
    rcases ihb hyb with ⟨yb', hyb', heqb⟩
    refine ⟨ya'.mul yb', by simp [evalQ, hya', hyb'], ?_⟩
    unfold ExactQ.equiv ExactQ.mul at *; dsimp only; simp only [Int.natCast_mul]; grind
  | sqr a ih =>
    simp only [evalQ, Option.map_eq_some_iff] at hy1
    rcases hy1 with ⟨ya, hya, rfl⟩
    rcases ih hya with ⟨yb, hyb, heq⟩
    refine ⟨yb.sqr, by simp [evalQ, hyb], ?_⟩
    unfold ExactQ.equiv ExactQ.sqr at *; dsimp only; simp only [Int.natCast_mul]; grind
  | inv a ih =>
    simp only [evalQ, Option.bind_eq_some_iff] at hy1
    rcases hy1 with ⟨ya, hya, hinv⟩
    rcases ih hya with ⟨yb, hyb, heq⟩
    split at hinv
    · rename_i hpa
      injection hinv with hyeq; subst hyeq
      have hpb : 0 < yb.num := by
        unfold ExactQ.equiv at heq
        have h1 : 0 < ya.num * (yb.den : Int) := Int.mul_pos hpa (ExactQ.den_int_pos yb)
        have h2 : 0 < yb.num * (ya.den : Int) := by omega
        have hda := ExactQ.den_int_pos ya
        by_cases hle : yb.num ≤ 0
        · have := Int.mul_nonpos_of_nonpos_of_nonneg hle (Int.le_of_lt hda); omega
        · omega
      refine ⟨yb.invPos hpb, by simp [evalQ, hyb, hpb], ?_⟩
      unfold ExactQ.equiv ExactQ.invPos at *; dsimp only
      have ha' : (ya.num.toNat : Int) = ya.num := by omega
      have hb' : (yb.num.toNat : Int) = yb.num := by omega
      rw [ha', hb']; grind
    · cases hinv

/-- Iterated Scale-Equivariance of Halley's Map (∀ n : Nat). -/
theorem halley_iter_equivariant (a s x0 : ExactQ) (hs : 0 < s.num) :
    ∀ n : Nat, ∀ un, iterQ exprHalley a n x0 = some un →
      ∃ xn, iterQ exprHalley (a.mul s.sqr) n (x0.mul s) = some xn ∧ xn.equiv (un.mul s) := by
  intro n
  induction n with
  | zero =>
    intro u0 hu0
    simp only [iterQ, Option.some.injEq] at hu0; subst hu0
    exact ⟨x0.mul s, rfl, ExactQ.equiv_refl _⟩
  | succ k ih =>
    intro uk1 huk1
    simp only [iterQ, Option.bind_eq_some_iff] at huk1
    rcases huk1 with ⟨uk, huk, hstep⟩
    rcases ih uk huk with ⟨xk, hxk, heqk⟩
    rcases halley_step_equivariant a uk s uk1 hs hstep with ⟨xks, hxks, heqs⟩
    rcases evalQ_equiv_congr exprHalley (ExactQ.equiv_refl _) (ExactQ.equiv_symm heqk) hxks with ⟨xk1, hxk1, heq1⟩
    exact ⟨xk1, by simp [iterQ, hxk, hxk1], ExactQ.equiv_trans (ExactQ.equiv_symm heq1) heqs⟩

/-- DISCHARGED INFINITE THEOREM 1 (Universal Binary-Scaled Halley Square Root):
    From ONE 59-leaf finite binary certificate on [1, 4] × [15/16, 17/8],
    for EVERY positive rational A ∈ ExactQ_{>0}, there is an exact signed binary shift k : Int
    such that for ALL starting guesses x0, y0 in the bit-length bracket [2^k, 2^(k+1)]
    (and even [15/16 * 2^k, 17/8 * 2^k]) and ALL n : Nat:
      1. H_A^n(x0) is well-defined (no zero denominators)
      2. |H_A^n(x0) - H_A^n(y0)| ≤ (7/8)^n * |x0 - y0|! -/
theorem halley_universal_pos_rational (A : ExactQ) (hA : 0 < A.num) :
    ∃ k : Int,
      ∀ x0 y0 : ExactQ,
        certHalley.b0.contains (x0.mul (pow2Q (-k))) →
        certHalley.b0.contains (y0.mul (pow2Q (-k))) →
        (∀ n : Nat, ∃ xn, iterQ exprHalley A n x0 = some xn) ∧
        (∀ n : Nat, ∀ xn yn,
          iterQ exprHalley A n x0 = some xn →
          iterQ exprHalley A n y0 = some yn →
          (xn.dist yn).le (((ExactQ.ofDyadic 7 3).pow n).mul (x0.dist y0))) := by
  rcases exists_binary_norm_4 A hA with ⟨k, ha_mem⟩
  refine ⟨k, fun x0 y0 hx0 hy0 => ?_⟩
  let s := pow2Q k
  let sInv := pow2Q (-k)
  let a := A.mul sInv.sqr
  let u0 := x0.mul sInv
  let v0 := y0.mul sInv
  have hs_pos : 0 < s.num := pow2Q_pos k
  have h1 : (s.mul sInv).equiv (ExactQ.ofInt 1) := pow2Q_mul_neg_equiv k
  have ha_eq : (a.mul s.sqr).equiv A := by
    simp only [a, ExactQ.equiv, ExactQ.mul, ExactQ.sqr, ExactQ.ofInt, Int.natCast_mul] at h1 ⊢; grind
  have hx0_eq : (u0.mul s).equiv x0 := by
    simp only [u0, ExactQ.equiv, ExactQ.mul, ExactQ.ofInt, Int.natCast_mul] at h1 ⊢; grind
  have hy0_eq : (v0.mul s).equiv y0 := by
    simp only [v0, ExactQ.equiv, ExactQ.mul, ExactQ.ofInt, Int.natCast_mul] at h1 ⊢; grind
  have hiter_congr : ∀ {p1 p2 z1 z2 w1 : ExactQ} {n : Nat},
      p1.equiv p2 → z1.equiv z2 → iterQ exprHalley p1 n z1 = some w1 →
      ∃ w2, iterQ exprHalley p2 n z2 = some w2 ∧ w1.equiv w2 := by
    intro p1 p2 z1 z2 w1 n hp hz hw1
    induction n generalizing w1 with
    | zero =>
      simp only [iterQ, Option.some.injEq] at hw1; subst hw1
      exact ⟨z2, rfl, hz⟩
    | succ m ihm =>
      simp only [iterQ, Option.bind_eq_some_iff] at hw1
      rcases hw1 with ⟨wm, hwm, hst⟩
      rcases ihm hwm with ⟨wm2, hwm2, heqm⟩
      rcases evalQ_equiv_congr exprHalley hp heqm hst with ⟨w2, hw2, heq2⟩
      exact ⟨w2, by simp [iterQ, hwm2, hw2], heq2⟩
  constructor
  · intro n
    rcases contraction_orbit_invariant certHalley certHalley_valid a ha_mem u0 hx0 n with ⟨un, hun, _⟩
    rcases halley_iter_equivariant a s u0 hs_pos n un hun with ⟨xn_sc, hxn_sc, _⟩
    rcases hiter_congr ha_eq hx0_eq hxn_sc with ⟨xn, hxn, _⟩
    exact ⟨xn, hxn⟩
  · intro n xn yn hxn hyn
    rcases contraction_orbit_invariant certHalley certHalley_valid a ha_mem u0 hx0 n with ⟨un, hun, _⟩
    rcases contraction_orbit_invariant certHalley certHalley_valid a ha_mem v0 hy0 n with ⟨vn, hvn, _⟩
    have hdec := contraction_orbit_decay certHalley certHalley_valid a ha_mem u0 v0 hx0 hy0 n un vn hun hvn
    rcases halley_iter_equivariant a s u0 hs_pos n un hun with ⟨xn_sc, hxn_sc, heq_xsc⟩
    rcases halley_iter_equivariant a s v0 hs_pos n vn hvn with ⟨yn_sc, hyn_sc, heq_ysc⟩
    rcases hiter_congr ha_eq hx0_eq hxn_sc with ⟨xn', hxn', heq_x'⟩
    rcases hiter_congr ha_eq hy0_eq hyn_sc with ⟨yn', hyn', heq_y'⟩
    rw [hxn] at hxn'; injection hxn' with ex; subst ex
    rw [hyn] at hyn'; injection hyn' with ey; subst ey
    have hxn_eq : xn.equiv (un.mul s) := ExactQ.equiv_trans (ExactQ.equiv_symm heq_x') heq_xsc
    have hyn_eq : yn.equiv (vn.mul s) := ExactQ.equiv_trans (ExactQ.equiv_symm heq_y') heq_ysc
    -- dist(xn, yn) ≈ s * dist(un, vn) ≤ s * q^n * dist(u0, v0) ≈ q^n * dist(x0, y0)!
    have hdist_scale : ∀ c d : ExactQ, ((c.mul s).dist (d.mul s)).equiv ((c.dist d).mul s) := by
      intro c d
      have hsub : ((c.mul s).sub (d.mul s)).equiv ((c.sub d).mul s) := by
        unfold ExactQ.equiv ExactQ.sub ExactQ.mul; dsimp only; simp only [Int.natCast_mul]; grind
      have habs_s : s.abs.equiv s := by
        unfold ExactQ.equiv ExactQ.abs; dsimp only
        have : (s.num.natAbs : Int) = s.num := by omega
        rw [this]
      unfold ExactQ.dist
      have h1' := ExactQ.equiv_trans (ExactQ.abs_congr hsub) (ExactQ.abs_mul_equiv (c.sub d) s)
      exact ExactQ.equiv_trans h1' (ExactQ.mul_congr (ExactQ.equiv_refl _) habs_s)
    have hlhs : (xn.dist yn).equiv ((un.dist vn).mul s) :=
      ExactQ.equiv_trans (ExactQ.dist_congr hxn_eq hyn_eq) (hdist_scale un vn)
    have hrhs1 : (((ExactQ.ofDyadic 7 3).pow n).mul (u0.dist v0)).mul s |>.equiv
                 (((ExactQ.ofDyadic 7 3).pow n).mul (x0.dist y0)) := by
      have hd0 : ((u0.dist v0).mul s).equiv (x0.dist y0) :=
        ExactQ.equiv_trans (ExactQ.equiv_symm (hdist_scale u0 v0)) (ExactQ.dist_congr hx0_eq hy0_eq)
      unfold ExactQ.equiv ExactQ.mul at hd0 ⊢; dsimp only at hd0 ⊢
      simp only [Int.natCast_mul] at hd0 ⊢; grind
    have hmul := ExactQ.mul_le_mul_of_nonneg_right (Int.le_of_lt hs_pos) hdec
    exact ExactQ.le_congr_left (ExactQ.equiv_symm hlhs) (ExactQ.le_congr_right hrhs1 hmul)

-- 5.3 Discharged Infinite Theorem 2: Parametric Bring Radical Quintic Family
--     x^5 + (1 + p)x - 1 = 0  (unsolvable by radicals at p = 0!)

private theorem newton_residual_identity (x P D : ExactQ) (hD : 0 < D.num) :
    P.equiv (D.mul (x.sub (x.sub (P.mul (D.invPos hD))))) := by
  unfold ExactQ.equiv ExactQ.sub ExactQ.mul ExactQ.invPos; dsimp only
  have htn : (D.num.toNat : Int) = D.num := by omega
  simp only [Int.natCast_mul]
  rw [htn]
  grind

/-- Exact algebraic residual identity for Bring Newton step:
    |x^5 + (1 + p)x - 1| = (1 + p + 5 x^4) * |F_p(x) - x| ≤ 7 * |F_p(x) - x| on [0, 1/2] × [1/2, 1]! -/
theorem bring_quintic_residual_decay (p : ExactQ) (hp : certBring.p0.contains p)
    (x0 x1 : ExactQ) (hx0 : certBring.b0.contains x0) (hx1 : evalQ exprBringNewton p x0 = some x1) :
    ∀ n : Nat, ∀ xn,
      iterQ exprBringNewton p n x0 = some xn →
      (bringPoly p xn).abs.le ((ExactQ.ofInt 7).mul (((ExactQ.ofDyadic 7 3).pow n).mul (x1.dist x0))) := by
  intro n xn hxn
  rcases contraction_orbit_invariant certBring certBring_valid p hp x0 hx0 n with ⟨xn', hxn', hmem⟩
  change iterQ exprBringNewton p n x0 = some xn' at hxn'
  rw [hxn] at hxn'; injection hxn' with e; subst e
  rcases (contraction_certified_properties certBring certBring_valid p hp).2.1 xn hmem with ⟨xn1, hstep, _⟩
  change evalQ exprBringNewton p xn = some xn1 at hstep
  have hdec := contraction_residual_decay certBring certBring_valid p hp x0 x1 hx0 hx1 n xn xn1 hxn hstep
  -- Extract den = 1 + p + 5 * xn^4 and prove poly ≈ den * (xn - xn1)
  let denQ := ((ExactQ.ofInt 1).add p).add ((ExactQ.ofInt 5).mul xn.sqr.sqr)
  have hden_bounds : 0 < denQ.num ∧ denQ.le (ExactQ.ofInt 7) := by
    -- p ∈ [0, 1/2], xn ∈ [1/2, 1] ⇒ 1 + p + 5*xn^4 ∈ (0, 7]
    unfold certBring DyadicBall.contains at hp hmem; dsimp only at hp hmem
    -- hp: 0 ≤ p.num * 4 ≤ 2 * p.den; hmem: 2 * xn.den ≤ xn.num * 4 ≤ 4 * xn.den
    have hp_nn : 0 ≤ p.num := by omega
    have hp_le : 2 * p.num ≤ (p.den : Int) := by omega
    have hx_nn : 0 ≤ xn.num := by omega
    have hx_le : xn.num ≤ (xn.den : Int) := by omega
    have hpd := ExactQ.den_int_pos p
    have hxd := ExactQ.den_int_pos xn
    have hx2_le : xn.num * xn.num ≤ (xn.den : Int) * (xn.den : Int) :=
      Int.le_trans (Int.mul_le_mul_of_nonneg_right hx_le hx_nn)
                   (Int.mul_le_mul_of_nonneg_left hx_le (Int.le_of_lt hxd))
    have hx2_nn : 0 ≤ xn.num * xn.num := Int.mul_nonneg hx_nn hx_nn
    have hxd2 : 0 < (xn.den : Int) * (xn.den : Int) := Int.mul_pos hxd hxd
    have hx4_le : (xn.num * xn.num) * (xn.num * xn.num) ≤
                  ((xn.den : Int) * (xn.den : Int)) * ((xn.den : Int) * (xn.den : Int)) :=
      Int.le_trans (Int.mul_le_mul_of_nonneg_right hx2_le hx2_nn)
                   (Int.mul_le_mul_of_nonneg_left hx2_le (Int.le_of_lt hxd2))
    have hx4_nn : 0 ≤ (xn.num * xn.num) * (xn.num * xn.num) := Int.mul_nonneg hx2_nn hx2_nn
    dsimp only [denQ]
    simp only [ExactQ.le, ExactQ.add, ExactQ.mul, ExactQ.sqr, ExactQ.ofInt, Int.natCast_mul, Int.natCast_one]
    have h1p_pos : 0 < (1 * (p.den : Int) + p.num * 1) := by omega
    have hden_pos : 0 < (1 * (p.den : Int) + p.num * 1) * (1 * ((xn.den : Int) * (xn.den : Int) * ((xn.den : Int) * (xn.den : Int)))) +
                        5 * (xn.num * xn.num * (xn.num * xn.num)) * (1 * (p.den : Int)) := by
      have t1 : 0 < (1 * (p.den : Int) + p.num * 1) * (1 * ((xn.den : Int) * (xn.den : Int) * ((xn.den : Int) * (xn.den : Int)))) :=
        Int.mul_pos h1p_pos (by have := Int.mul_pos hxd2 hxd2; omega)
      have t2 : 0 ≤ 5 * (xn.num * xn.num * (xn.num * xn.num)) * (1 * (p.den : Int)) :=
        Int.mul_nonneg (by omega) (by omega)
      omega
    constructor
    · exact hden_pos
    · -- (1 + p + 5 * x^4) ≤ 1 + 1/2 + 5 = 13/2 ≤ 7!
      have h1p_le : (1 * (p.den : Int) + p.num * 1) ≤ 2 * (p.den : Int) := by omega
      have hxd4_pos : 0 ≤ ((xn.den : Int) * (xn.den : Int)) * ((xn.den : Int) * (xn.den : Int)) :=
        Int.le_of_lt (Int.mul_pos hxd2 hxd2)
      have m1 := Int.mul_le_mul_of_nonneg_right h1p_le hxd4_pos
      have m2 := Int.mul_le_mul_of_nonneg_right hx4_le (Int.le_of_lt hpd)
      grind
  have hpoly_eq : (bringPoly p xn).equiv (denQ.mul (xn.sub xn1)) := by
    simp only [exprBringNewton, evalQ, Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.some.injEq] at hstep
    rcases hstep with ⟨_, rfl, _, ⟨_, ⟨_, ⟨_, ⟨_, rfl, _, ⟨_, ⟨_, rfl, rfl⟩, rfl⟩, rfl⟩, _, ⟨_, ⟨_, rfl, _, rfl, rfl⟩, _, rfl, rfl⟩, rfl⟩, _, rfl, rfl⟩,
      _, ⟨_, ⟨_, ⟨_, rfl, _, rfl, rfl⟩, _, ⟨_, rfl, _, ⟨_, ⟨_, rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, hinv⟩, rfl⟩, rfl⟩
    split at hinv
    · rename_i hdpos
      injection hinv with hinv_eq; subst hinv_eq
      exact newton_residual_identity xn (bringPoly p xn) denQ hdpos
    · cases hinv
  -- |poly| ≈ |denQ| * |xn - xn1| = denQ * dist(xn1, xn) ≤ 7 * (7/8)^n * dist(x1, x0)!
  have habs_poly : (bringPoly p xn).abs.equiv (denQ.mul (xn1.dist xn)) := by
    have h1 := ExactQ.equiv_trans (ExactQ.abs_congr hpoly_eq) (ExactQ.abs_mul_equiv denQ (xn.sub xn1))
    have hden_abs : denQ.abs.equiv denQ := by
      unfold ExactQ.equiv ExactQ.abs; dsimp only
      have : (denQ.num.natAbs : Int) = denQ.num := by omega
      rw [this]
    have hdsym : (xn.dist xn1).equiv (xn1.dist xn) := ExactQ.dist_symm xn xn1
    exact ExactQ.equiv_trans h1 (ExactQ.mul_congr hden_abs hdsym)
  have hmul := ExactQ.mul_le_mul_nonneg (Int.le_of_lt hden_bounds.1)
    (Int.mul_nonneg (ExactQ.pow_nonneg (by unfold ExactQ.ofDyadic; dsimp; omega) n) (ExactQ.abs_nonneg _))
    hden_bounds.2 hdec
  exact ExactQ.le_congr_left (ExactQ.equiv_symm habs_poly) hmul

/-- Corollary: Doubly Infinite Dyadic Perturbation Family p = 2^(-k) (∀ k ≥ 1, ∀ n : Nat). -/
theorem bring_quintic_dyadic_family (k : Nat) (hk : 1 ≤ k)
    (x0 x1 : ExactQ) (hx0 : certBring.b0.contains x0)
    (hx1 : evalQ exprBringNewton (ExactQ.ofDyadic 1 k) x0 = some x1) :
    ∀ n : Nat, ∀ xn,
      iterQ exprBringNewton (ExactQ.ofDyadic 1 k) n x0 = some xn →
      (bringPoly (ExactQ.ofDyadic 1 k) xn).abs.le
        ((ExactQ.ofInt 7).mul (((ExactQ.ofDyadic 7 3).pow n).mul (x1.dist x0))) := by
  have hp : certBring.p0.contains (ExactQ.ofDyadic 1 k) := by
    unfold certBring ExactQ.ofDyadic DyadicBall.contains; dsimp only
    have hpow : 2 ≤ 2 ^ k := by
      have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
      simpa using this
    omega
  exact bring_quintic_residual_decay (ExactQ.ofDyadic 1 k) hp x0 x1 hx0 hx1

/-- Tight 2^(-20) Bring Radical Enclosure & Ultra-Fast Contraction (q = 2^(-16), ∀ n : Nat). -/
theorem bring_radical_tight_enclosure (x0 y0 : ExactQ)
    (hx0 : certBringTight.b0.contains x0) (hy0 : certBringTight.b0.contains y0) :
    (∀ n : Nat, ∃ xn, iterQ exprBringNewton (ExactQ.ofInt 0) n x0 = some xn ∧ certBringTight.b0.contains xn) ∧
    (∀ n : Nat, ∀ xn yn,
      iterQ exprBringNewton (ExactQ.ofInt 0) n x0 = some xn →
      iterQ exprBringNewton (ExactQ.ofInt 0) n y0 = some yn →
      (xn.dist yn).le (((ExactQ.ofDyadic 1 16).pow n).mul (x0.dist y0))) := by
  have hp0 : certBringTight.p0.contains (ExactQ.ofInt 0) := by
    unfold certBringTight ExactQ.ofInt DyadicBall.contains; dsimp only; omega
  exact ⟨contraction_orbit_invariant certBringTight certBringTight_valid _ hp0 x0 hx0,
         contraction_orbit_decay certBringTight certBringTight_valid _ hp0 x0 y0 hx0 hy0⟩

-- 5.4 Discharged Infinite Theorem 3: Non-Monotone Parametric Logistic Band
--     F_mu(x) = mu * x * (1 - x) across turning point x = 1/2 (∀ mu ∈ [19/8, 41/16], ∀ n : Nat)

theorem logistic_band_fixed_point_convergence (mu : ExactQ) (hmu_mem : certLogistic.p0.contains mu)
    (x0 : ExactQ) (hx0 : certLogistic.b0.contains x0) :
    ∃ (hmu_pos : 0 < mu.num),
      let xs := logisticFixedPoint mu hmu_pos
      certLogistic.b0.contains xs ∧
      (∀ n : Nat, ∃ xn, iterQ exprLogistic mu n x0 = some xn ∧ certLogistic.b0.contains xn) ∧
      (∀ n : Nat, ∀ xn, iterQ exprLogistic mu n x0 = some xn →
        (xn.dist xs).le (((ExactQ.ofDyadic 7 3).pow n).mul (x0.dist xs))) := by
  have hmu_bounds : 76 * (mu.den : Int) ≤ mu.num * 32 ∧ mu.num * 32 ≤ 82 * (mu.den : Int) := by
    unfold certLogistic DyadicBall.contains at hmu_mem; dsimp only at hmu_mem; omega
  have hmu_pos : 0 < mu.num := by have := ExactQ.den_int_pos mu; omega
  refine ⟨hmu_pos, ?_, contraction_orbit_invariant certLogistic certLogistic_valid mu hmu_mem x0 hx0, ?_⟩
  · -- Prove x*(mu) = (mu - 1)/mu ∈ [15/32, 21/32]
    unfold logisticFixedPoint certLogistic DyadicBall.contains ExactQ.mul ExactQ.sub ExactQ.invPos ExactQ.ofInt
    dsimp only
    have htn : (mu.num.toNat : Int) = mu.num := by omega
    simp only [Int.natCast_mul]
    rw [htn]
    have hmd := ExactQ.den_int_pos mu
    -- Need: 15 * (mu.den * mu.num) ≤ (mu.num - mu.den) * mu.den * 32 ≤ 21 * (mu.den * mu.num)
    -- Equivalently: 15 * mu.num ≤ 32 * (mu.num - mu.den) ≤ 21 * mu.num
    -- ⇔ 32 * mu.den ≤ 17 * mu.num (since 76/32 * 17 > 32) AND 11 * mu.num ≤ 32 * mu.den (since 82/32 * 11 = 902/32 < 1024/32)!
    have h1 : 32 * (mu.den : Int) ≤ 17 * mu.num := by omega
    have h2 : 11 * mu.num ≤ 32 * (mu.den : Int) := by omega
    have m1 := Int.mul_le_mul_of_nonneg_right h1 (Int.le_of_lt hmd)
    have m2 := Int.mul_le_mul_of_nonneg_right h2 (Int.le_of_lt hmd)
    constructor <;> grind
  · -- Prove F_mu(x*(mu)) ≈ x*(mu) and invoke Meta-Theorem 6!
    let xs := logisticFixedPoint mu hmu_pos
    have hxs_mem : certLogistic.b0.contains xs := by
      unfold xs logisticFixedPoint certLogistic DyadicBall.contains ExactQ.mul ExactQ.sub ExactQ.invPos ExactQ.ofInt
      dsimp only
      have htn : (mu.num.toNat : Int) = mu.num := by omega
      simp only [Int.natCast_mul]; rw [htn]
      have hmd := ExactQ.den_int_pos mu
      have m1 := Int.mul_le_mul_of_nonneg_right (by omega : 32 * (mu.den : Int) ≤ 17 * mu.num) (Int.le_of_lt hmd)
      have m2 := Int.mul_le_mul_of_nonneg_right (by omega : 11 * mu.num ≤ 32 * (mu.den : Int)) (Int.le_of_lt hmd)
      constructor <;> grind
    have hfx_eq : evalQ exprLogistic mu xs = some (mu.mul (xs.mul ((ExactQ.ofInt 1).sub xs))) := rfl
    have hfix : (mu.mul (xs.mul ((ExactQ.ofInt 1).sub xs))).equiv xs := by
      unfold xs logisticFixedPoint ExactQ.equiv ExactQ.mul ExactQ.sub ExactQ.invPos ExactQ.ofInt
      dsimp only
      have htn : (mu.num.toNat : Int) = mu.num := by omega
      simp only [Int.natCast_mul]; rw [htn]
      grind
    exact contraction_fixed_point_distance certLogistic certLogistic_valid mu hmu_mem x0 xs _ hx0 hxs_mem hfx_eq hfix

-- 5.5 Discharged Infinite Theorem 4: Oscillatory Alternating Direct Bring Map
--     G(x) = 1 / (1 + x^4) near its |G'| = 1 stability boundary (q = 63/64)

theorem bring_direct_oscillatory_contraction (x0 y0 : ExactQ)
    (hx0 : certBringAlt.b0.contains x0) (hy0 : certBringAlt.b0.contains y0) :
    (∀ n : Nat, ∃ xn, iterQ exprBringDirect (ExactQ.ofInt 0) n x0 = some xn ∧ certBringAlt.b0.contains xn) ∧
    (∀ n : Nat, ∀ xn yn,
      iterQ exprBringDirect (ExactQ.ofInt 0) n x0 = some xn →
      iterQ exprBringDirect (ExactQ.ofInt 0) n y0 = some yn →
      (xn.dist yn).le (((ExactQ.ofDyadic 63 6).pow n).mul (x0.dist y0))) := by
  have hp0 : certBringAlt.p0.contains (ExactQ.ofInt 0) := by
    unfold certBringAlt ExactQ.ofInt DyadicBall.contains; dsimp only; omega
  exact ⟨contraction_orbit_invariant certBringAlt certBringAlt_valid _ hp0 x0 hx0,
         contraction_orbit_decay certBringAlt certBringAlt_valid _ hp0 x0 y0 hx0 hy0⟩

-- 5.6 Kernel-Verified Sharpness / Boundary Falsification Witnesses (Zero Float!)

/-- Sharpness Witness 1: Logistic at μ = 7/2 has an EXACT rational 2-cycle {3/7, 6/7},
    proving global contraction fails past the period-doubling threshold μ = 3. -/
theorem sharpness_logistic_period2_cycle :
    let mu := ExactQ.ofDyadic 7 1
    let c1 : ExactQ := ⟨3, 7, by omega⟩
    let c2 : ExactQ := ⟨6, 7, by omega⟩
    (∃ y1, evalQ exprLogistic mu c1 = some y1 ∧ y1.equiv c2) ∧
    (∃ y2, evalQ exprLogistic mu c2 = some y2 ∧ y2.equiv c1) ∧
    ¬ c1.equiv c2 := by
  refine ⟨⟨_, rfl, ?_⟩, ⟨_, rfl, ?_⟩, ?_⟩ <;>
    (simp only [ExactQ.equiv, ExactQ.mul, ExactQ.sub, ExactQ.ofInt, ExactQ.ofDyadic]; decide)

/-- Sharpness Witness 2: Halley at a = 4 has exact secant slope > 1/2 on [1, 101/100],
    proving no contraction constant q ≤ 1/2 holds on [1, 4] × [1, 2]. -/
theorem sharpness_halley_slope_gt_half :
    let a := ExactQ.ofInt 4
    let x1 := ExactQ.ofInt 1
    let x2 : ExactQ := ⟨101, 100, by omega⟩
    ∃ y1 y2, evalQ exprHalley a x1 = some y1 ∧ evalQ exprHalley a x2 = some y2 ∧
      ((ExactQ.ofDyadic 1 1).mul (x2.dist x1)).lt (y2.dist y1) := by
  dsimp only
  refine ⟨_, _, (evalQ_halley_iff _ _ _).mpr ⟨by decide, rfl⟩,
                (evalQ_halley_iff _ _ _).mpr ⟨by decide, rfl⟩, ?_⟩
  unfold ExactQ.lt; decide

/-- Closed-form evaluation helper for exprBringDirect. -/
theorem evalQ_bringDirect_iff (x y : ExactQ) :
    evalQ exprBringDirect (ExactQ.ofInt 0) x = some y ↔
      ∃ (hden : 0 < ((ExactQ.ofInt 1).add x.sqr.sqr).num),
        y = ((ExactQ.ofInt 1).add x.sqr.sqr).invPos hden := by
  simp only [exprBringDirect, evalQ, Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.some.injEq]
  constructor
  · rintro ⟨_, ⟨_, rfl, _, ⟨_, ⟨_, rfl, rfl⟩, rfl⟩, rfl⟩, hinv⟩
    split at hinv
    · rename_i hpos; injection hinv with hyeq; subst hyeq; exact ⟨hpos, rfl⟩
    · cases hinv
  · rintro ⟨hpos, rfl⟩
    refine ⟨_, ⟨ExactQ.ofInt 1, rfl, _, ⟨_, ⟨x, rfl, rfl⟩, rfl⟩, rfl⟩, ?_⟩
    simp [hpos]

/-- Sharpness Witness 3: Direct Bring map G(x) = 1/(1+x^4) expands on [4/5, 81/100],
    showing |G(81/100) - G(4/5)| > |81/100 - 4/5| just past the stability boundary. -/
theorem sharpness_bring_direct_expands :
    let x1 : ExactQ := ⟨4, 5, by omega⟩
    let x2 : ExactQ := ⟨81, 100, by omega⟩
    ∃ y1 y2, evalQ exprBringDirect (ExactQ.ofInt 0) x1 = some y1 ∧
             evalQ exprBringDirect (ExactQ.ofInt 0) x2 = some y2 ∧
             (x2.dist x1).lt (y2.dist y1) := by
  dsimp only
  refine ⟨_, _, (evalQ_bringDirect_iff _ _).mpr ⟨by decide, rfl⟩,
                (evalQ_bringDirect_iff _ _).mpr ⟨by decide, rfl⟩, ?_⟩
  unfold ExactQ.lt; decide

-- 5.7 Kernel-Verified Negative / Mutation Certificate Rejection Tests (`checkParamContraction bad = false`)

theorem mutation_reject_halley_q_too_small :
    checkParamContraction { certHalley with qNum := 1, qExp := 1 } = false := by decide

theorem mutation_reject_halley_q_ge_one :
    checkParamContraction { certHalley with qNum := 1, qExp := 0 } = false := by decide

theorem mutation_reject_halley_no_subdivision :
    checkParamContraction { certHalley with tree := .pleaf (.leaf 14 true) } = false := by decide

theorem mutation_reject_logistic_period2_param :
    checkParamContraction { certLogistic with p0 := ⟨7, 1, 0⟩ } = false := by decide

theorem mutation_reject_bring_escaped_domain :
    checkParamContraction { certBring with b0 := ⟨3, 3, 1⟩ } = false := by decide

theorem mutation_reject_singular_denominator :
    checkParamContraction {
      expr := .inv (.sub .var (.constDyadic 3 2)),
      p0 := ⟨0, 0, 0⟩,
      b0 := ⟨3, 2, 1⟩,
      qNum := 1,
      qExp := 1,
      tree := .pleaf (.leaf 12 false)
    } = false := by decide

theorem mutation_reject_bring_alt_expanding_region :
    checkParamContraction { certBringAlt with b0 := ⟨17, 5, 1⟩ } = false := by decide

-- 5.8 Constructive Non-Vacuity Witnesses (Inhabiting All Theorem Hypotheses!)

example : 0 < (ExactQ.ofInt 12).num ∧
    certHalley.p0.contains (ExactQ.ofInt 3) ∧
    certHalley.b0.contains (ExactQ.ofDyadic 3 1) := by
  unfold certHalley DyadicBall.contains ExactQ.ofInt ExactQ.ofDyadic; dsimp only; omega

example : certBring.p0.contains (ExactQ.ofDyadic 1 2) ∧
    certBring.b0.contains (ExactQ.ofDyadic 3 2) ∧
    certBringTight.b0.contains (ExactQ.ofDyadic 791547 20) := by
  unfold certBring certBringTight DyadicBall.contains ExactQ.ofDyadic; dsimp only; omega

example : certLogistic.p0.contains (ExactQ.ofDyadic 5 1) ∧
    certLogistic.b0.contains (ExactQ.ofDyadic 1 1) ∧
    certBringAlt.b0.contains (ExactQ.ofDyadic 773 10) := by
  unfold certLogistic certBringAlt DyadicBall.contains ExactQ.ofDyadic; dsimp only; omega

end DyadicCompiler
