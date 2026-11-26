/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RopeQ32Coprime.Defs
import RopeQ32Coprime.RatOrder
import RopeQ32Coprime.RelativeErrorCayley

/-!
# Pillar 2A: Exact Unit-Circle Norm-Drift Bounds (`MXFP4-E2M1`, `FP8-E4M3`, and Dyadic Cayley)

Proves Theorem 4 (`quantized_rotation_norm_drift_exact`):
- `MXFP4-E2M1`: exact worst-case `max |c^2 + s^2 - 1| = 1/4`, attained at `(15/17, 8/17) ↦ (1, 1/2)`.
- `FP8-E4M3`: exact worst-case `max |c^2 + s^2 - 1| = 21/256`, attained at `(1323/1565, 836/1565) ↦ (7/8, 9/16)`.
- Dyadic Cayley: `c(t)^2 + s(t)^2 - 1 = 0` identically for all `t : Rat`, plus the exact
  integer Pythagorean identity `(2^(2B) - k^2)^2 + (2 * 2^B * k)^2 = (2^(2B) + k^2)^2`.
-/

namespace RopeQ32Coprime

/-! ### Helpers: `Rat` Cast & Cross-Multiplication Inequalities -/

theorem rat_intCast_le {a b : Int} (h : a ≤ b) : (a : Rat) ≤ (b : Rat) := by
  rw [Rat.le_iff]
  change a * (1 : Nat) ≤ b * (1 : Nat)
  omega

theorem rat_intCast_lt {a b : Int} (h : a < b) : (a : Rat) < (b : Rat) := by
  rw [Rat.lt_iff]
  change a * (1 : Nat) < b * (1 : Nat)
  omega

theorem int_le_of_rat_le {a b : Int} (h : (a : Rat) ≤ (b : Rat)) : a ≤ b := by
  rw [Rat.le_iff] at h
  change a * (1 : Nat) ≤ b * (1 : Nat) at h
  omega

theorem rat_natCast_pos {n : Nat} (hn : 0 < n) : (0 : Rat) < (n : Rat) := by
  rw [Rat.lt_iff]
  change (0 : Int) * (1 : Nat) < (n : Int) * (1 : Nat)
  omega

theorem rat_div_le_div_of_int {a b c d : Int} (hb : (0 : Int) < b) (hd : (0 : Int) < d)
    (h : a * d ≤ c * b) : (a : Rat) / (b : Rat) ≤ (c : Rat) / (d : Rat) := by
  have hb' : (0 : Rat) < (b : Rat) := rat_intCast_lt hb
  have hd' : (0 : Rat) < (d : Rat) := rat_intCast_lt hd
  have hbd : (0 : Rat) < (b : Rat) * (d : Rat) := rat_mul_pos hb' hd'
  apply rat_le_of_mul_pos_right hbd
  have hl : ((a : Rat) / (b : Rat)) * ((b : Rat) * (d : Rat)) = (a : Rat) * (d : Rat) := by
    have ha : ((a : Rat) / (b : Rat)) * ((b : Rat) * (d : Rat)) =
        (((a : Rat) / (b : Rat)) * (b : Rat)) * (d : Rat) := by grind
    rw [ha, rat_div_mul_cancel (Rat.ne_of_gt hb')]
  have hr : ((c : Rat) / (d : Rat)) * ((b : Rat) * (d : Rat)) = (c : Rat) * (b : Rat) := by
    have ha : ((c : Rat) / (d : Rat)) * ((b : Rat) * (d : Rat)) =
        (((c : Rat) / (d : Rat)) * (d : Rat)) * (b : Rat) := by grind
    rw [ha, rat_div_mul_cancel (Rat.ne_of_gt hd')]
  rw [hl, hr, ← Rat.intCast_mul, ← Rat.intCast_mul]
  exact rat_intCast_le h

theorem rat_div_lt_div_of_int {a b c d : Int} (hb : (0 : Int) < b) (hd : (0 : Int) < d)
    (h : a * d < c * b) : (a : Rat) / (b : Rat) < (c : Rat) / (d : Rat) := by
  have hb' : (0 : Rat) < (b : Rat) := rat_intCast_lt hb
  have hd' : (0 : Rat) < (d : Rat) := rat_intCast_lt hd
  have hle : (a : Rat) / (b : Rat) ≤ (c : Rat) / (d : Rat) := rat_div_le_div_of_int hb hd (Int.le_of_lt h)
  have hne : (a : Rat) / (b : Rat) ≠ (c : Rat) / (d : Rat) := by
    intro heq
    have hmul : ((a : Rat) / (b : Rat)) * ((b : Rat) * (d : Rat)) =
        ((c : Rat) / (d : Rat)) * ((b : Rat) * (d : Rat)) := congrArg (· * ((b : Rat) * (d : Rat))) heq
    have hl : ((a : Rat) / (b : Rat)) * ((b : Rat) * (d : Rat)) = (a : Rat) * (d : Rat) := by
      have ha : ((a : Rat) / (b : Rat)) * ((b : Rat) * (d : Rat)) =
          (((a : Rat) / (b : Rat)) * (b : Rat)) * (d : Rat) := by grind
      rw [ha, rat_div_mul_cancel (Rat.ne_of_gt hb')]
    have hr : ((c : Rat) / (d : Rat)) * ((b : Rat) * (d : Rat)) = (c : Rat) * (b : Rat) := by
      have ha : ((c : Rat) / (d : Rat)) * ((b : Rat) * (d : Rat)) =
          (((c : Rat) / (d : Rat)) * (d : Rat)) * (b : Rat) := by grind
      rw [ha, rat_div_mul_cancel (Rat.ne_of_gt hd')]
    rw [hl, hr, ← Rat.intCast_mul, ← Rat.intCast_mul] at hmul
    have hlt : ((a * d : Int) : Rat) < ((c * b : Int) : Rat) := rat_intCast_lt h
    exact Rat.ne_of_lt hlt hmul
  exact Rat.lt_of_le_of_ne hle hne

/-! ### `Rat.floor` & `rneUniformStep` Exact Bounds -/

theorem rat_floor_bounds (a : Rat) : (a.floor : Rat) ≤ a ∧ a < (a.floor : Rat) + 1 := by
  have hden_pos_nat : 0 < a.den := Nat.pos_of_ne_zero a.den_nz
  have hden_pos_int : (0 : Int) < (a.den : Int) := by omega
  have hdm : (a.den : Int) * (a.num / (a.den : Int)) + a.num % (a.den : Int) = a.num :=
    Int.mul_ediv_add_emod a.num (a.den : Int)
  have hmod_nonneg : (0 : Int) ≤ a.num % (a.den : Int) :=
    Int.emod_nonneg a.num (by omega)
  have hmod_lt : a.num % (a.den : Int) < (a.den : Int) :=
    Int.emod_lt_of_pos a.num hden_pos_int
  constructor
  · rw [Rat.floor_def, Rat.le_iff]
    change (a.num / (a.den : Int)) * (a.den : Int) ≤ a.num * (1 : Nat)
    rw [Int.mul_comm (a.num / (a.den : Int)) (a.den : Int)]
    omega
  · have hadd : (a.floor : Rat) + 1 = ((a.floor + 1 : Int) : Rat) := by
      rw [Rat.intCast_add]; rfl
    rw [hadd, Rat.floor_def, Rat.lt_iff]
    change a.num * (1 : Nat) < (a.num / (a.den : Int) + 1) * (a.den : Int)
    rw [Int.add_mul, Int.one_mul, Int.mul_comm (a.num / (a.den : Int)) (a.den : Int)]
    omega

theorem rneUniformStep_bounds {n : Nat} (hn : 0 < n) (x : Rat) :
    ratAbs (rneUniformStep n x - x) ≤ 1 / (2 * (n : Rat)) := by
  unfold rneUniformStep
  let s := (n : Rat) * x
  let q := s.floor
  let r := s - (q : Rat)
  have hb := rat_floor_bounds s
  have hr0 : (0 : Rat) ≤ r := rat_sub_nonneg hb.1
  have hr1 : r < 1 := by
    have : (0 : Rat) < (q : Rat) + 1 - s := rat_sub_pos hb.2
    apply rat_lt_of_sub_pos
    have heq : (1 : Rat) - r = (q : Rat) + 1 - s := by grind
    rw [heq]; exact this
  have hn_pos : (0 : Rat) < (n : Rat) := rat_natCast_pos hn
  have hn_ne : (n : Rat) ≠ 0 := Rat.ne_of_gt hn_pos
  have h2n_pos : (0 : Rat) < 2 * (n : Rat) := rat_mul_pos (by decide) hn_pos
  have hhalf_nonneg : (0 : Rat) ≤ (1 / 2 : Rat) := by
    have h := rat_div_le_div_of_int (a := 0) (b := 1) (c := 1) (d := 2) (by decide) (by decide) (by decide)
    have h0 : ((0 : Int) : Rat) / ((1 : Int) : Rat) = 0 := by grind
    rw [h0] at h; exact h
  let qR : Int :=
    if r < 1 / 2 then q
    else if (1 / 2 : Rat) < r then q + 1
    else if q % 2 = 0 then q else q + 1
  have hqR_err : ratAbs ((qR : Rat) - s) ≤ 1 / 2 := by
    show ratAbs (((if r < 1 / 2 then q else if (1 / 2 : Rat) < r then q + 1 else if q % 2 = 0 then q else q + 1) : Int) - s) ≤ 1 / 2
    by_cases h1 : r < 1 / 2
    · simp only [h1, ↓reduceIte]
      apply ratAbs_le_of_bounds
      · have : (0 : Rat) ≤ (1 / 2 : Rat) - r := rat_sub_nonneg (Rat.le_of_lt h1)
        have heq : ((q : Rat) - s) - (-(1 / 2 : Rat)) = (1 / 2 : Rat) - r := by grind
        exact rat_le_of_sub_nonneg (by rw [heq]; exact this)
      · have heq : (1 / 2 : Rat) - ((q : Rat) - s) = (1 / 2 : Rat) + r := by grind
        exact rat_le_of_sub_nonneg (by rw [heq]; exact rat_add_nonneg hhalf_nonneg hr0)
    · by_cases h2 : (1 / 2 : Rat) < r
      · simp only [h1, h2, ↓reduceIte, Rat.intCast_add]
        apply ratAbs_le_of_bounds
        · have hsub : (0 : Rat) ≤ 1 - r := rat_sub_nonneg (Rat.le_of_lt hr1)
          have heq : (((q : Rat) + (1 : Int)) - s) - (-(1 / 2 : Rat)) = (1 - r) + (1 / 2 : Rat) := by grind
          exact rat_le_of_sub_nonneg (by rw [heq]; exact rat_add_nonneg hsub hhalf_nonneg)
        · have hsub : (0 : Rat) ≤ r - (1 / 2 : Rat) := rat_sub_nonneg (Rat.le_of_lt h2)
          have heq : (1 / 2 : Rat) - (((q : Rat) + (1 : Int)) - s) = r - (1 / 2 : Rat) := by grind
          exact rat_le_of_sub_nonneg (by rw [heq]; exact hsub)
      · have hr_eq : r = 1 / 2 := Rat.le_antisymm (Rat.not_lt.mp h2) (Rat.not_lt.mp h1)
        simp only [h1, h2, ↓reduceIte]
        by_cases hev : q % 2 = 0
        · simp only [hev, ↓reduceIte]
          have hqs : (q : Rat) - s = -(1 / 2 : Rat) := by grind
          rw [hqs, ratAbs_neg, ratAbs_of_nonneg hhalf_nonneg]
          exact Rat.le_refl
        · simp only [hev, ↓reduceIte, Rat.intCast_add]
          have hqs : ((q : Rat) + (1 : Int)) - s = (1 / 2 : Rat) := by grind
          rw [hqs, ratAbs_of_nonneg hhalf_nonneg]
          exact Rat.le_refl
  have hdiff : (qR : Rat) / (n : Rat) - x = ((qR : Rat) - s) / (n : Rat) := by
    apply ((rat_div_eq_iff hn_ne).mpr _).symm
    have : ((qR : Rat) / (n : Rat) - x) * (n : Rat) = ((qR : Rat) / (n : Rat)) * (n : Rat) - (n : Rat) * x := by grind
    rw [this, rat_div_mul_cancel hn_ne]
  change ratAbs ((qR : Rat) / (n : Rat) - x) ≤ 1 / (2 * (n : Rat))
  rw [hdiff]
  have hmul_eq : ratAbs (((qR : Rat) - s) / (n : Rat)) * (n : Rat) = ratAbs ((qR : Rat) - s) := by
    have h1 : ratAbs (((qR : Rat) - s) / (n : Rat)) * ratAbs (n : Rat) = ratAbs (((qR : Rat) - s) / (n : Rat) * (n : Rat)) :=
      (ratAbs_mul _ _).symm
    rw [ratAbs_of_nonneg (Rat.le_of_lt hn_pos), rat_div_mul_cancel hn_ne] at h1
    exact h1
  apply rat_le_of_mul_pos_right hn_pos
  rw [hmul_eq]
  have hrhs : (1 / (2 * (n : Rat))) * (n : Rat) = 1 / 2 := by
    have h2n_ne : 2 * (n : Rat) ≠ 0 := Rat.ne_of_gt h2n_pos
    apply ((rat_div_eq_iff (by decide : (2 : Rat) ≠ 0)).mpr _).symm
    have h1 : (1 / (2 * (n : Rat))) * (n : Rat) * 2 = (1 / (2 * (n : Rat))) * (2 * (n : Rat)) := by grind
    rw [h1, rat_div_mul_cancel h2n_ne]
  rw [hrhs]
  exact hqR_err

theorem rneUniformStep_nonneg {n : Nat} (hn : 0 < n) {x : Rat} (hx : (0 : Rat) ≤ x) :
    (0 : Rat) ≤ rneUniformStep n x := by
  unfold rneUniformStep
  let s := (n : Rat) * x
  let q := s.floor
  have hn_pos : (0 : Rat) < (n : Rat) := rat_natCast_pos hn
  have hs0 : (0 : Rat) ≤ s := Rat.mul_nonneg (Rat.le_of_lt hn_pos) hx
  have hq0 : (0 : Int) ≤ q := by
    have hb := (rat_floor_bounds s).2
    have hlt : (0 : Rat) < (q : Rat) + 1 := rat_lt_of_le_of_lt hs0 hb
    have hadd : (q : Rat) + 1 = ((q + 1 : Int) : Rat) := by rw [Rat.intCast_add]; rfl
    rw [hadd, Rat.lt_iff] at hlt
    change (0 : Int) * (1 : Nat) < (q + 1) * (1 : Nat) at hlt
    omega
  have hqR0 : (0 : Rat) ≤ ((if s - (q : Rat) < 1 / 2 then q else if (1 / 2 : Rat) < s - (q : Rat) then q + 1 else if q % 2 = 0 then q else q + 1 : Int) : Rat) := by
    have hq1 : (0 : Int) ≤ q + 1 := Int.le_trans hq0 (Int.le_add_of_nonneg_right (by decide))
    split
    · exact rat_intCast_le hq0
    · split
      · exact rat_intCast_le hq1
      · split
        · exact rat_intCast_le hq0
        · exact rat_intCast_le hq1
  change (0 : Rat) ≤ ((if s - (q : Rat) < 1 / 2 then q else if (1 / 2 : Rat) < s - (q : Rat) then q + 1 else if q % 2 = 0 then q else q + 1 : Int) : Rat) / (n : Rat)
  apply rat_le_div_of_mul_le hn_pos
  rw [Rat.zero_mul]
  exact hqR0

/-! ### `MXFP4-E2M1` Exact `1/4` Norm-Drift Table (Integer Numerators over `16`) & Proof -/

def mxfp4ValN : Fin 7 → Int
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 4
  | ⟨3, _⟩ => 6
  | ⟨4, _⟩ => 8
  | ⟨5, _⟩ => 12
  | ⟨6, _⟩ => 16

def mxfp4LoN : Fin 7 → Int
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => 5
  | ⟨4, _⟩ => 7
  | ⟨5, _⟩ => 10
  | ⟨6, _⟩ => 14

def mxfp4HiN : Fin 7 → Int
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 3
  | ⟨2, _⟩ => 5
  | ⟨3, _⟩ => 7
  | ⟨4, _⟩ => 10
  | ⟨5, _⟩ => 14
  | ⟨6, _⟩ => 16

theorem mxfp4_grid_bound_int :
    ∀ i j : Fin 7,
      mxfp4LoN i * mxfp4LoN i + mxfp4LoN j * mxfp4LoN j ≤ 256 →
      256 ≤ mxfp4HiN i * mxfp4HiN i + mxfp4HiN j * mxfp4HiN j →
      -64 ≤ mxfp4ValN i * mxfp4ValN i + mxfp4ValN j * mxfp4ValN j - 256 ∧
      mxfp4ValN i * mxfp4ValN i + mxfp4ValN j * mxfp4ValN j - 256 ≤ 64 := by
  decide

theorem mxfp4_loN_nonneg (i : Fin 7) : (0 : Int) ≤ mxfp4LoN i := by
  revert i; decide

theorem quantMXFP4Nonneg_spec {x : Rat} (hx0 : (0 : Rat) ≤ x) (hx1 : x ≤ 1) :
    ∃ i : Fin 7,
      quantMXFP4Nonneg x = (mxfp4ValN i : Rat) / 16 ∧
      (mxfp4LoN i : Rat) / 16 ≤ x ∧
      x ≤ (mxfp4HiN i : Rat) / 16 := by
  unfold quantMXFP4Nonneg
  split
  · refine ⟨⟨0, by decide⟩, ?_, ?_, ?_⟩ <;> dsimp only [mxfp4ValN, mxfp4LoN, mxfp4HiN]
    · grind
    · have : ((0 : Int) : Rat) / 16 = 0 := by grind
      rw [this]; exact hx0
    · exact Rat.le_of_lt ‹_›
  · split
    · refine ⟨⟨1, by decide⟩, ?_, ?_, ?_⟩ <;> dsimp only [mxfp4ValN, mxfp4LoN, mxfp4HiN]
      · grind
      · exact Rat.not_lt.mp ‹_›
      · exact Rat.le_of_lt ‹_›
    · split
      · refine ⟨⟨2, by decide⟩, ?_, ?_, ?_⟩ <;> dsimp only [mxfp4ValN, mxfp4LoN, mxfp4HiN]
        · grind
        · exact Rat.not_lt.mp ‹_›
        · exact Rat.le_of_lt ‹_›
      · split
        · refine ⟨⟨3, by decide⟩, ?_, ?_, ?_⟩ <;> dsimp only [mxfp4ValN, mxfp4LoN, mxfp4HiN]
          · grind
          · exact Rat.not_lt.mp ‹_›
          · exact Rat.le_of_lt ‹_›
        · split
          · refine ⟨⟨4, by decide⟩, ?_, ?_, ?_⟩ <;> dsimp only [mxfp4ValN, mxfp4LoN, mxfp4HiN]
            · grind
            · exact Rat.not_lt.mp ‹_›
            · have : (5 / 8 : Rat) = ((10 : Int) : Rat) / 16 := by grind
              rw [← this]; exact Rat.le_of_lt ‹_›
          · split
            · refine ⟨⟨5, by decide⟩, ?_, ?_, ?_⟩ <;> dsimp only [mxfp4ValN, mxfp4LoN, mxfp4HiN]
              · grind
              · have : (5 / 8 : Rat) = ((10 : Int) : Rat) / 16 := by grind
                rw [← this]; exact Rat.not_lt.mp ‹_›
              · have : (7 / 8 : Rat) = ((14 : Int) : Rat) / 16 := by grind
                rw [← this]; exact Rat.le_of_lt ‹_›
            · refine ⟨⟨6, by decide⟩, ?_, ?_, ?_⟩ <;> dsimp only [mxfp4ValN, mxfp4LoN, mxfp4HiN]
              · grind
              · have : (7 / 8 : Rat) = ((14 : Int) : Rat) / 16 := by grind
                rw [← this]; exact Rat.not_lt.mp ‹_›
              · have : (1 : Rat) = ((16 : Int) : Rat) / 16 := by grind
                rw [← this]; exact hx1

theorem unit_circle_abs_le_one {c s : Rat} (h : c * c + s * s = 1) :
    ratAbs c ≤ 1 ∧ ratAbs s ≤ 1 := by
  have hc2 : c * c ≤ 1 := by
    have hs := rat_sq_nonneg s
    have : (0 : Rat) ≤ 1 - c * c := by grind
    exact rat_le_of_sub_nonneg this
  have hs2 : s * s ≤ 1 := by
    have hc := rat_sq_nonneg c
    have : (0 : Rat) ≤ 1 - s * s := by grind
    exact rat_le_of_sub_nonneg this
  constructor
  · cases Rat.le_total (a := ratAbs c) (b := (1 : Rat)) with
    | inl hle => exact hle
    | inr hge =>
      by_cases heq : ratAbs c = 1
      · rw [heq]; exact Rat.le_refl
      · exfalso
        have h1 : (1 : Rat) < ratAbs c := Rat.lt_of_le_of_ne hge (Ne.symm heq)
        have hsq : (1 : Rat) < ratAbs c * ratAbs c := by
          have hmul2 := rat_mul_lt_mul_of_pos_left h1 (rat_lt_trans (by decide) h1)
          rw [Rat.mul_one] at hmul2
          exact rat_lt_trans h1 hmul2
        rw [ratAbs_sq] at hsq
        exact Rat.not_le.mpr hsq hc2
  · cases Rat.le_total (a := ratAbs s) (b := (1 : Rat)) with
    | inl hle => exact hle
    | inr hge =>
      by_cases heq : ratAbs s = 1
      · rw [heq]; exact Rat.le_refl
      · exfalso
        have h1 : (1 : Rat) < ratAbs s := Rat.lt_of_le_of_ne hge (Ne.symm heq)
        have hsq : (1 : Rat) < ratAbs s * ratAbs s := by
          have hmul2 := rat_mul_lt_mul_of_pos_left h1 (rat_lt_trans (by decide) h1)
          rw [Rat.mul_one] at hmul2
          exact rat_lt_trans h1 hmul2
        rw [ratAbs_sq] at hsq
        exact Rat.not_le.mpr hsq hs2

theorem quantMXFP4_sq_eq (x : Rat) :
    quantMXFP4 x * quantMXFP4 x = quantMXFP4Nonneg (ratAbs x) * quantMXFP4Nonneg (ratAbs x) := by
  unfold quantMXFP4 ratAbs
  split
  · rfl
  · grind

theorem mxfp4_norm_drift_le (c s : Rat) (h : c * c + s * s = 1) :
    ratAbs (quantMXFP4 c * quantMXFP4 c + quantMXFP4 s * quantMXFP4 s - 1) ≤ 1 / 4 := by
  rw [quantMXFP4_sq_eq c, quantMXFP4_sq_eq s]
  let x := ratAbs c
  let y := ratAbs s
  have hx0 : (0 : Rat) ≤ x := ratAbs_nonneg c
  have hy0 : (0 : Rat) ≤ y := ratAbs_nonneg s
  have hle1 := unit_circle_abs_le_one h
  have hxy : x * x + y * y = 1 := by
    show ratAbs c * ratAbs c + ratAbs s * ratAbs s = 1
    rw [ratAbs_sq, ratAbs_sq]; exact h
  obtain ⟨i, hi_val, hi_lo, hi_hi⟩ := quantMXFP4Nonneg_spec hx0 hle1.1
  obtain ⟨j, hj_val, hj_lo, hj_hi⟩ := quantMXFP4Nonneg_spec hy0 hle1.2
  change ratAbs (quantMXFP4Nonneg x * quantMXFP4Nonneg x + quantMXFP4Nonneg y * quantMXFP4Nonneg y - 1) ≤ 1 / 4
  rw [hi_val, hj_val]
  have hlo_nonneg_i : (0 : Rat) ≤ (mxfp4LoN i : Rat) / 16 := by
    apply rat_le_div_of_mul_le (by decide)
    rw [Rat.zero_mul]; exact rat_intCast_le (mxfp4_loN_nonneg i)
  have hlo_nonneg_j : (0 : Rat) ≤ (mxfp4LoN j : Rat) / 16 := by
    apply rat_le_div_of_mul_le (by decide)
    rw [Rat.zero_mul]; exact rat_intCast_le (mxfp4_loN_nonneg j)
  have hlo_rat : ((mxfp4LoN i : Rat) / 16) * ((mxfp4LoN i : Rat) / 16) +
      ((mxfp4LoN j : Rat) / 16) * ((mxfp4LoN j : Rat) / 16) ≤ 1 := by
    rw [← hxy]
    exact rat_add_le_add (rat_sq_le_sq_of_nonneg hlo_nonneg_i hi_lo)
      (rat_sq_le_sq_of_nonneg hlo_nonneg_j hj_lo)
  have hhi_rat : 1 ≤ ((mxfp4HiN i : Rat) / 16) * ((mxfp4HiN i : Rat) / 16) +
      ((mxfp4HiN j : Rat) / 16) * ((mxfp4HiN j : Rat) / 16) := by
    rw [← hxy]
    exact rat_add_le_add (rat_sq_le_sq_of_nonneg hx0 hi_hi)
      (rat_sq_le_sq_of_nonneg hy0 hj_hi)
  have hlo_int : mxfp4LoN i * mxfp4LoN i + mxfp4LoN j * mxfp4LoN j ≤ 256 := by
    apply int_le_of_rat_le
    have hmul := rat_mul_le_mul_of_nonneg_right hlo_rat (by decide : (0 : Rat) ≤ 256)
    have hl : (((mxfp4LoN i : Rat) / 16) * ((mxfp4LoN i : Rat) / 16) +
        ((mxfp4LoN j : Rat) / 16) * ((mxfp4LoN j : Rat) / 16)) * 256 =
        ((mxfp4LoN i * mxfp4LoN i + mxfp4LoN j * mxfp4LoN j : Int) : Rat) := by
      rw [Rat.intCast_add, Rat.intCast_mul, Rat.intCast_mul]
      grind
    rw [hl, Rat.one_mul] at hmul
    exact hmul
  have hhi_int : 256 ≤ mxfp4HiN i * mxfp4HiN i + mxfp4HiN j * mxfp4HiN j := by
    apply int_le_of_rat_le
    have hmul := rat_mul_le_mul_of_nonneg_right hhi_rat (by decide : (0 : Rat) ≤ 256)
    have hr : (((mxfp4HiN i : Rat) / 16) * ((mxfp4HiN i : Rat) / 16) +
        ((mxfp4HiN j : Rat) / 16) * ((mxfp4HiN j : Rat) / 16)) * 256 =
        ((mxfp4HiN i * mxfp4HiN i + mxfp4HiN j * mxfp4HiN j : Int) : Rat) := by
      rw [Rat.intCast_add, Rat.intCast_mul, Rat.intCast_mul]
      grind
    rw [hr, Rat.one_mul] at hmul
    exact hmul
  have hbound := mxfp4_grid_bound_int i j hlo_int hhi_int
  have hexpr : ((mxfp4ValN i : Rat) / 16) * ((mxfp4ValN i : Rat) / 16) +
      ((mxfp4ValN j : Rat) / 16) * ((mxfp4ValN j : Rat) / 16) - 1 =
      ((mxfp4ValN i * mxfp4ValN i + mxfp4ValN j * mxfp4ValN j - 256 : Int) : Rat) / ((256 : Int) : Rat) := by
    rw [Rat.intCast_sub, Rat.intCast_add, Rat.intCast_mul, Rat.intCast_mul]
    grind
  rw [hexpr]
  apply ratAbs_le_of_bounds
  · have h1 : (-(1 / 4 : Rat)) = ((-64 : Int) : Rat) / ((256 : Int) : Rat) := by grind
    rw [h1]
    exact rat_div_le_div_of_int (by decide) (by decide) (by omega)
  · have h1 : (1 / 4 : Rat) = ((64 : Int) : Rat) / ((256 : Int) : Rat) := by grind
    rw [h1]
    exact rat_div_le_div_of_int (by decide) (by decide) (by omega)

/-! ### `FP8-E4M3` Exact `21/256` Norm-Drift Table (Integer Numerators over `64`) & Proof -/

def fp8TopValN : Fin 9 → Int
  | ⟨0, _⟩ => 32
  | ⟨1, _⟩ => 36
  | ⟨2, _⟩ => 40
  | ⟨3, _⟩ => 44
  | ⟨4, _⟩ => 48
  | ⟨5, _⟩ => 52
  | ⟨6, _⟩ => 56
  | ⟨7, _⟩ => 60
  | ⟨8, _⟩ => 64

def fp8TopLoN : Fin 9 → Int
  | ⟨0, _⟩ => 31
  | ⟨1, _⟩ => 34
  | ⟨2, _⟩ => 38
  | ⟨3, _⟩ => 42
  | ⟨4, _⟩ => 46
  | ⟨5, _⟩ => 50
  | ⟨6, _⟩ => 54
  | ⟨7, _⟩ => 58
  | ⟨8, _⟩ => 62

def fp8TopHiN : Fin 9 → Int
  | ⟨0, _⟩ => 34
  | ⟨1, _⟩ => 38
  | ⟨2, _⟩ => 42
  | ⟨3, _⟩ => 46
  | ⟨4, _⟩ => 50
  | ⟨5, _⟩ => 54
  | ⟨6, _⟩ => 58
  | ⟨7, _⟩ => 62
  | ⟨8, _⟩ => 64

theorem fp8Top_grid_bound_int :
    ∀ i j : Fin 9,
      fp8TopLoN i * fp8TopLoN i + fp8TopLoN j * fp8TopLoN j ≤ 4096 →
      4096 ≤ fp8TopHiN i * fp8TopHiN i + fp8TopHiN j * fp8TopHiN j →
      -336 ≤ fp8TopValN i * fp8TopValN i + fp8TopValN j * fp8TopValN j - 4096 ∧
      fp8TopValN i * fp8TopValN i + fp8TopValN j * fp8TopValN j - 4096 ≤ 336 := by
  decide

theorem fp8Top_loN_nonneg (i : Fin 9) : (0 : Int) ≤ fp8TopLoN i := by
  revert i; decide

theorem fp8Top_valN_bounds (i : Fin 9) :
    (0 : Int) ≤ fp8TopValN i ∧ fp8TopValN i ≤ 64 ∧
    fp8TopValN i - fp8TopLoN i ≤ 2 ∧ fp8TopHiN i - fp8TopValN i ≤ 2 := by
  revert i; decide

theorem quantFP8E4M3Top_spec {x : Rat} (hlo : (31 / 64 : Rat) ≤ x) (hhi : x ≤ 1) :
    ∃ i : Fin 9,
      quantFP8E4M3Top x = (fp8TopValN i : Rat) / 64 ∧
      (fp8TopLoN i : Rat) / 64 ≤ x ∧
      x ≤ (fp8TopHiN i : Rat) / 64 := by
  unfold quantFP8E4M3Top
  split
  · rename_i hle
    refine ⟨⟨0, by decide⟩, ?_, ?_, ?_⟩ <;> dsimp only [fp8TopValN, fp8TopLoN, fp8TopHiN]
    · grind
    · exact hlo
    · have : (17 / 32 : Rat) = ((34 : Int) : Rat) / 64 := by grind
      rw [← this]; exact hle
  · split
    · refine ⟨⟨1, by decide⟩, ?_, ?_, ?_⟩ <;> dsimp only [fp8TopValN, fp8TopLoN, fp8TopHiN]
      · grind
      · have : (17 / 32 : Rat) = ((34 : Int) : Rat) / 64 := by grind
        rw [← this]; exact Rat.le_of_lt (Rat.not_le.mp ‹_›)
      · have : (19 / 32 : Rat) = ((38 : Int) : Rat) / 64 := by grind
        rw [← this]; exact Rat.le_of_lt ‹_›
    · split
      · rename_i hle
        refine ⟨⟨2, by decide⟩, ?_, ?_, ?_⟩ <;> dsimp only [fp8TopValN, fp8TopLoN, fp8TopHiN]
        · grind
        · have : (19 / 32 : Rat) = ((38 : Int) : Rat) / 64 := by grind
          rw [← this]; exact Rat.not_lt.mp ‹_›
        · have : (21 / 32 : Rat) = ((42 : Int) : Rat) / 64 := by grind
          rw [← this]; exact hle
      · split
        · refine ⟨⟨3, by decide⟩, ?_, ?_, ?_⟩ <;> dsimp only [fp8TopValN, fp8TopLoN, fp8TopHiN]
          · grind
          · have : (21 / 32 : Rat) = ((42 : Int) : Rat) / 64 := by grind
            rw [← this]; exact Rat.le_of_lt (Rat.not_le.mp ‹_›)
          · have : (23 / 32 : Rat) = ((46 : Int) : Rat) / 64 := by grind
            rw [← this]; exact Rat.le_of_lt ‹_›
        · split
          · rename_i hle
            refine ⟨⟨4, by decide⟩, ?_, ?_, ?_⟩ <;> dsimp only [fp8TopValN, fp8TopLoN, fp8TopHiN]
            · grind
            · have : (23 / 32 : Rat) = ((46 : Int) : Rat) / 64 := by grind
              rw [← this]; exact Rat.not_lt.mp ‹_›
            · have : (25 / 32 : Rat) = ((50 : Int) : Rat) / 64 := by grind
              rw [← this]; exact hle
          · split
            · refine ⟨⟨5, by decide⟩, ?_, ?_, ?_⟩ <;> dsimp only [fp8TopValN, fp8TopLoN, fp8TopHiN]
              · grind
              · have : (25 / 32 : Rat) = ((50 : Int) : Rat) / 64 := by grind
                rw [← this]; exact Rat.le_of_lt (Rat.not_le.mp ‹_›)
              · have : (27 / 32 : Rat) = ((54 : Int) : Rat) / 64 := by grind
                rw [← this]; exact Rat.le_of_lt ‹_›
            · split
              · rename_i hle
                refine ⟨⟨6, by decide⟩, ?_, ?_, ?_⟩ <;> dsimp only [fp8TopValN, fp8TopLoN, fp8TopHiN]
                · grind
                · have : (27 / 32 : Rat) = ((54 : Int) : Rat) / 64 := by grind
                  rw [← this]; exact Rat.not_lt.mp ‹_›
                · have : (29 / 32 : Rat) = ((58 : Int) : Rat) / 64 := by grind
                  rw [← this]; exact hle
              · split
                · refine ⟨⟨7, by decide⟩, ?_, ?_, ?_⟩ <;> dsimp only [fp8TopValN, fp8TopLoN, fp8TopHiN]
                  · grind
                  · have : (29 / 32 : Rat) = ((58 : Int) : Rat) / 64 := by grind
                    rw [← this]; exact Rat.le_of_lt (Rat.not_le.mp ‹_›)
                  · have : (31 / 32 : Rat) = ((62 : Int) : Rat) / 64 := by grind
                    rw [← this]; exact Rat.le_of_lt ‹_›
                · refine ⟨⟨8, by decide⟩, ?_, ?_, ?_⟩ <;> dsimp only [fp8TopValN, fp8TopLoN, fp8TopHiN]
                  · grind
                  · have : (31 / 32 : Rat) = ((62 : Int) : Rat) / 64 := by grind
                    rw [← this]; exact Rat.not_lt.mp ‹_›
                  · have : (1 : Rat) = ((64 : Int) : Rat) / 64 := by grind
                    rw [← this]; exact hhi

theorem quantFP8E4M3Nonneg_low_bounds {x : Rat} (hx0 : (0 : Rat) ≤ x) (hxlt : x < 31 / 64) :
    (0 : Rat) ≤ quantFP8E4M3Nonneg x ∧
    ratAbs (quantFP8E4M3Nonneg x - x) ≤ 1 / 64 := by
  unfold quantFP8E4M3Nonneg
  have hnot : ¬ (31 / 64 : Rat) ≤ x := Rat.not_le.mpr hxlt
  simp only [hnot, ↓reduceIte]
  have hle64 : ∀ n : Nat, 32 ≤ n → 1 / (2 * (n : Rat)) ≤ 1 / 64 := by
    intro n hn
    have h1 : 1 / (2 * (n : Rat)) = ((1 : Int) : Rat) / (((2 * n : Nat) : Int) : Rat) := by
      have : (2 : Rat) * (n : Rat) = (((2 * n : Nat) : Int) : Rat) := by
        rw [Int.natCast_mul, Rat.intCast_mul]; rfl
      rw [this]; rfl
    have h2 : (1 / 64 : Rat) = ((1 : Int) : Rat) / ((64 : Int) : Rat) := rfl
    rw [h1, h2]
    exact rat_div_le_div_of_int (by omega) (by decide) (by omega)
  split
  · exact ⟨rneUniformStep_nonneg (by decide) hx0,
           Rat.le_trans (rneUniformStep_bounds (by decide) x) (hle64 32 (by decide))⟩
  · split
    · exact ⟨rneUniformStep_nonneg (by decide) hx0,
             Rat.le_trans (rneUniformStep_bounds (by decide) x) (hle64 64 (by decide))⟩
    · split
      · exact ⟨rneUniformStep_nonneg (by decide) hx0,
               Rat.le_trans (rneUniformStep_bounds (by decide) x) (hle64 128 (by decide))⟩
      · split
        · exact ⟨rneUniformStep_nonneg (by decide) hx0,
                 Rat.le_trans (rneUniformStep_bounds (by decide) x) (hle64 256 (by decide))⟩
        · exact ⟨rneUniformStep_nonneg (by decide) hx0,
                 Rat.le_trans (rneUniformStep_bounds (by decide) x) (hle64 512 (by decide))⟩

theorem quantFP8E4M3_sq_eq (x : Rat) :
    quantFP8E4M3 x * quantFP8E4M3 x =
      quantFP8E4M3Nonneg (ratAbs x) * quantFP8E4M3Nonneg (ratAbs x) := by
  unfold quantFP8E4M3 ratAbs
  split
  · rfl
  · grind

theorem fp8_low_high_bound {x y : Rat} (hx0 : (0 : Rat) ≤ x) (hxlt : x < 31 / 64)
    (hy0 : (0 : Rat) ≤ y) (hylo : (31 / 64 : Rat) ≤ y) (hy1 : y ≤ 1)
    (hxy : x * x + y * y = 1) :
    ratAbs (quantFP8E4M3Nonneg x * quantFP8E4M3Nonneg x +
            quantFP8E4M3Nonneg y * quantFP8E4M3Nonneg y - 1) ≤ 21 / 256 := by
  let a := quantFP8E4M3Nonneg x
  let b := quantFP8E4M3Nonneg y
  have ha := quantFP8E4M3Nonneg_low_bounds hx0 hxlt
  have ha_le : a ≤ 1 / 2 := by
    have hdiff : a - x ≤ 1 / 64 := Rat.le_trans (ratAbs_le_self_and_neg (a - x)).1 ha.2
    have h1 := rat_add_le_add hdiff (Rat.le_of_lt hxlt)
    have h2 : a - x + x = a := by grind
    have h3 : (1 / 64 : Rat) + 31 / 64 = 1 / 2 := by grind
    rw [h2, h3] at h1; exact h1
  have hb_top : b = quantFP8E4M3Top y := by
    show quantFP8E4M3Nonneg y = quantFP8E4M3Top y
    unfold quantFP8E4M3Nonneg
    simp [hylo]
  obtain ⟨j, hj_val, hj_lo, hj_hi⟩ := quantFP8E4M3Top_spec hylo hy1
  have hb_eq : b = (fp8TopValN j : Rat) / 64 := by rw [hb_top, hj_val]
  have hb_spec := fp8Top_valN_bounds j
  have hb0 : (0 : Rat) ≤ b := by
    rw [hb_eq]; apply rat_le_div_of_mul_le (by decide); rw [Rat.zero_mul]; exact rat_intCast_le hb_spec.1
  have hb1 : b ≤ 1 := by
    rw [hb_eq]; apply rat_div_le_of_mul_le (by decide); rw [Rat.one_mul]; exact rat_intCast_le hb_spec.2.1
  have hb_err : ratAbs (b - y) ≤ 1 / 32 := by
    rw [hb_eq]
    apply ratAbs_le_of_bounds
    · have h1 : (fp8TopValN j : Rat) / 64 - (fp8TopHiN j : Rat) / 64 ≤ (fp8TopValN j : Rat) / 64 - y := by
        have := rat_sub_nonneg hj_hi
        have heq : ((fp8TopValN j : Rat) / 64 - y) - ((fp8TopValN j : Rat) / 64 - (fp8TopHiN j : Rat) / 64) =
            (fp8TopHiN j : Rat) / 64 - y := by grind
        exact rat_le_of_sub_nonneg (by rw [heq]; exact this)
      have h2 : -(1 / 32 : Rat) ≤ (fp8TopValN j : Rat) / 64 - (fp8TopHiN j : Rat) / 64 := by
        have heq1 : -(1 / 32 : Rat) = ((-2 : Int) : Rat) / ((64 : Int) : Rat) := by grind
        have heq2 : (fp8TopValN j : Rat) / 64 - (fp8TopHiN j : Rat) / 64 =
            ((fp8TopValN j - fp8TopHiN j : Int) : Rat) / ((64 : Int) : Rat) := by
          rw [Rat.intCast_sub]; grind
        rw [heq1, heq2]
        exact rat_div_le_div_of_int (by decide) (by decide) (by omega)
      exact Rat.le_trans h2 h1
    · have h1 : (fp8TopValN j : Rat) / 64 - y ≤ (fp8TopValN j : Rat) / 64 - (fp8TopLoN j : Rat) / 64 := by
        have := rat_sub_nonneg hj_lo
        have heq : ((fp8TopValN j : Rat) / 64 - (fp8TopLoN j : Rat) / 64) - ((fp8TopValN j : Rat) / 64 - y) =
            y - (fp8TopLoN j : Rat) / 64 := by grind
        exact rat_le_of_sub_nonneg (by rw [heq]; exact this)
      have h2 : (fp8TopValN j : Rat) / 64 - (fp8TopLoN j : Rat) / 64 ≤ 1 / 32 := by
        have heq1 : (1 / 32 : Rat) = ((2 : Int) : Rat) / ((64 : Int) : Rat) := by grind
        have heq2 : (fp8TopValN j : Rat) / 64 - (fp8TopLoN j : Rat) / 64 =
            ((fp8TopValN j - fp8TopLoN j : Int) : Rat) / ((64 : Int) : Rat) := by
          rw [Rat.intCast_sub]; grind
        rw [heq1, heq2]
        exact rat_div_le_div_of_int (by decide) (by decide) (by omega)
      exact Rat.le_trans h1 h2
  change ratAbs (a * a + b * b - 1) ≤ 21 / 256
  have hrewrite : a * a + b * b - 1 = (a - x) * (a + x) + (b - y) * (b + y) := by grind
  rw [hrewrite]
  have htri := ratAbs_add_le ((a - x) * (a + x)) ((b - y) * (b + y))
  rw [ratAbs_mul, ratAbs_mul] at htri
  have hax_pos : (0 : Rat) ≤ a + x := rat_add_nonneg ha.1 hx0
  have hby_pos : (0 : Rat) ≤ b + y := rat_add_nonneg hb0 hy0
  rw [ratAbs_of_nonneg hax_pos, ratAbs_of_nonneg hby_pos] at htri
  have hax_le : a + x ≤ 63 / 64 := by
    have h1 := rat_add_le_add ha_le (Rat.le_of_lt hxlt)
    have h2 : (1 / 2 : Rat) + 31 / 64 = 63 / 64 := by grind
    rw [h2] at h1; exact h1
  have hby_le : b + y ≤ 2 := by
    have h1 := rat_add_le_add hb1 hy1
    have h2 : (1 : Rat) + 1 = 2 := by grind
    rw [h2] at h1; exact h1
  have h64_nonneg : (0 : Rat) ≤ (1 / 64 : Rat) := by
    have h := rat_div_le_div_of_int (a := 0) (b := 1) (c := 1) (d := 64) (by decide) (by decide) (by decide)
    have h0 : ((0 : Int) : Rat) / ((1 : Int) : Rat) = 0 := by grind
    rw [h0] at h; exact h
  have h32_nonneg : (0 : Rat) ≤ (1 / 32 : Rat) := by
    have h := rat_div_le_div_of_int (a := 0) (b := 1) (c := 1) (d := 32) (by decide) (by decide) (by decide)
    have h0 : ((0 : Int) : Rat) / ((1 : Int) : Rat) = 0 := by grind
    rw [h0] at h; exact h
  have hterm1 : ratAbs (a - x) * (a + x) ≤ (1 / 64 : Rat) * (63 / 64) :=
    Rat.le_trans (rat_mul_le_mul_of_nonneg_right ha.2 hax_pos)
      (rat_mul_le_mul_of_nonneg_left hax_le h64_nonneg)
  have hterm2 : ratAbs (b - y) * (b + y) ≤ (1 / 32 : Rat) * 2 :=
    Rat.le_trans (rat_mul_le_mul_of_nonneg_right hb_err hby_pos)
      (rat_mul_le_mul_of_nonneg_left hby_le h32_nonneg)
  have hsum_le : (1 / 64 : Rat) * (63 / 64) + (1 / 32 : Rat) * 2 ≤ 21 / 256 := by
    have hl : (1 / 64 : Rat) * (63 / 64) + (1 / 32 : Rat) * 2 = ((319 : Int) : Rat) / ((4096 : Int) : Rat) := by grind
    have hr : (21 / 256 : Rat) = ((21 : Int) : Rat) / ((256 : Int) : Rat) := rfl
    rw [hl, hr]
    exact rat_div_le_div_of_int (by decide) (by decide) (by decide)
  exact Rat.le_trans htri (Rat.le_trans (rat_add_le_add hterm1 hterm2) hsum_le)

theorem fp8_norm_drift_le (c s : Rat) (h : c * c + s * s = 1) :
    ratAbs (quantFP8E4M3 c * quantFP8E4M3 c + quantFP8E4M3 s * quantFP8E4M3 s - 1) ≤ 21 / 256 := by
  rw [quantFP8E4M3_sq_eq c, quantFP8E4M3_sq_eq s]
  let x := ratAbs c
  let y := ratAbs s
  have hx0 : (0 : Rat) ≤ x := ratAbs_nonneg c
  have hy0 : (0 : Rat) ≤ y := ratAbs_nonneg s
  have hle1 := unit_circle_abs_le_one h
  have hxy : x * x + y * y = 1 := by
    show ratAbs c * ratAbs c + ratAbs s * ratAbs s = 1
    rw [ratAbs_sq, ratAbs_sq]; exact h
  change ratAbs (quantFP8E4M3Nonneg x * quantFP8E4M3Nonneg x + quantFP8E4M3Nonneg y * quantFP8E4M3Nonneg y - 1) ≤ 21 / 256
  by_cases hx : (31 / 64 : Rat) ≤ x
  · by_cases hy : (31 / 64 : Rat) ≤ y
    · have hqx : quantFP8E4M3Nonneg x = quantFP8E4M3Top x := by
        unfold quantFP8E4M3Nonneg; simp [hx]
      have hqy : quantFP8E4M3Nonneg y = quantFP8E4M3Top y := by
        unfold quantFP8E4M3Nonneg; simp [hy]
      rw [hqx, hqy]
      obtain ⟨i, hi_val, hi_lo, hi_hi⟩ := quantFP8E4M3Top_spec hx hle1.1
      obtain ⟨j, hj_val, hj_lo, hj_hi⟩ := quantFP8E4M3Top_spec hy hle1.2
      rw [hi_val, hj_val]
      have hlo_nonneg_i : (0 : Rat) ≤ (fp8TopLoN i : Rat) / 64 := by
        apply rat_le_div_of_mul_le (by decide); rw [Rat.zero_mul]; exact rat_intCast_le (fp8Top_loN_nonneg i)
      have hlo_nonneg_j : (0 : Rat) ≤ (fp8TopLoN j : Rat) / 64 := by
        apply rat_le_div_of_mul_le (by decide); rw [Rat.zero_mul]; exact rat_intCast_le (fp8Top_loN_nonneg j)
      have hlo_rat : ((fp8TopLoN i : Rat) / 64) * ((fp8TopLoN i : Rat) / 64) +
          ((fp8TopLoN j : Rat) / 64) * ((fp8TopLoN j : Rat) / 64) ≤ 1 := by
        rw [← hxy]
        exact rat_add_le_add (rat_sq_le_sq_of_nonneg hlo_nonneg_i hi_lo)
          (rat_sq_le_sq_of_nonneg hlo_nonneg_j hj_lo)
      have hhi_rat : 1 ≤ ((fp8TopHiN i : Rat) / 64) * ((fp8TopHiN i : Rat) / 64) +
          ((fp8TopHiN j : Rat) / 64) * ((fp8TopHiN j : Rat) / 64) := by
        rw [← hxy]
        exact rat_add_le_add (rat_sq_le_sq_of_nonneg hx0 hi_hi)
          (rat_sq_le_sq_of_nonneg hy0 hj_hi)
      have hlo_int : fp8TopLoN i * fp8TopLoN i + fp8TopLoN j * fp8TopLoN j ≤ 4096 := by
        apply int_le_of_rat_le
        have hmul := rat_mul_le_mul_of_nonneg_right hlo_rat (by decide : (0 : Rat) ≤ 4096)
        have hl : (((fp8TopLoN i : Rat) / 64) * ((fp8TopLoN i : Rat) / 64) +
            ((fp8TopLoN j : Rat) / 64) * ((fp8TopLoN j : Rat) / 64)) * 4096 =
            ((fp8TopLoN i * fp8TopLoN i + fp8TopLoN j * fp8TopLoN j : Int) : Rat) := by
          rw [Rat.intCast_add, Rat.intCast_mul, Rat.intCast_mul]; grind
        rw [hl, Rat.one_mul] at hmul; exact hmul
      have hhi_int : 4096 ≤ fp8TopHiN i * fp8TopHiN i + fp8TopHiN j * fp8TopHiN j := by
        apply int_le_of_rat_le
        have hmul := rat_mul_le_mul_of_nonneg_right hhi_rat (by decide : (0 : Rat) ≤ 4096)
        have hr : (((fp8TopHiN i : Rat) / 64) * ((fp8TopHiN i : Rat) / 64) +
            ((fp8TopHiN j : Rat) / 64) * ((fp8TopHiN j : Rat) / 64)) * 4096 =
            ((fp8TopHiN i * fp8TopHiN i + fp8TopHiN j * fp8TopHiN j : Int) : Rat) := by
          rw [Rat.intCast_add, Rat.intCast_mul, Rat.intCast_mul]; grind
        rw [hr, Rat.one_mul] at hmul; exact hmul
      have hbound := fp8Top_grid_bound_int i j hlo_int hhi_int
      have hexpr : ((fp8TopValN i : Rat) / 64) * ((fp8TopValN i : Rat) / 64) +
          ((fp8TopValN j : Rat) / 64) * ((fp8TopValN j : Rat) / 64) - 1 =
          ((fp8TopValN i * fp8TopValN i + fp8TopValN j * fp8TopValN j - 4096 : Int) : Rat) / ((4096 : Int) : Rat) := by
        rw [Rat.intCast_sub, Rat.intCast_add, Rat.intCast_mul, Rat.intCast_mul]; grind
      rw [hexpr]
      apply ratAbs_le_of_bounds
      · have h1 : -(21 / 256 : Rat) = ((-336 : Int) : Rat) / ((4096 : Int) : Rat) := by grind
        rw [h1]
        exact rat_div_le_div_of_int (by decide) (by decide) (by omega)
      · have h1 : (21 / 256 : Rat) = ((336 : Int) : Rat) / ((4096 : Int) : Rat) := by grind
        rw [h1]
        exact rat_div_le_div_of_int (by decide) (by decide) (by omega)
    · have hylt : y < 31 / 64 := Rat.not_le.mp hy
      have hcomm : quantFP8E4M3Nonneg x * quantFP8E4M3Nonneg x +
          quantFP8E4M3Nonneg y * quantFP8E4M3Nonneg y - 1 =
          quantFP8E4M3Nonneg y * quantFP8E4M3Nonneg y +
          quantFP8E4M3Nonneg x * quantFP8E4M3Nonneg x - 1 := by grind
      rw [hcomm]
      exact fp8_low_high_bound hy0 hylt hx0 hx hle1.1 (by grind)
  · have hxlt : x < 31 / 64 := Rat.not_le.mp hx
    by_cases hy : (31 / 64 : Rat) ≤ y
    · exact fp8_low_high_bound hx0 hxlt hy0 hy hle1.2 hxy
    · exfalso
      have hylt : y < 31 / 64 := Rat.not_le.mp hy
      have hx2 : x * x ≤ (31 / 64 : Rat) * (31 / 64) :=
        rat_sq_le_sq_of_nonneg hx0 (Rat.le_of_lt hxlt)
      have hy2 : y * y ≤ (31 / 64 : Rat) * (31 / 64) :=
        rat_sq_le_sq_of_nonneg hy0 (Rat.le_of_lt hylt)
      have hsum := rat_add_le_add hx2 hy2
      rw [hxy] at hsum
      have hlt1 : (31 / 64 : Rat) * (31 / 64) + (31 / 64) * (31 / 64) < 1 := by
        have hl : (31 / 64 : Rat) * (31 / 64) + (31 / 64) * (31 / 64) = ((1922 : Int) : Rat) / ((4096 : Int) : Rat) := by grind
        have hr : (1 : Rat) = ((1 : Int) : Rat) / ((1 : Int) : Rat) := by grind
        rw [hl, hr]
        exact rat_div_lt_div_of_int (by decide) (by decide) (by decide)
      exact Rat.not_le.mpr hlt1 hsum

/-! ### Exact Witnesses for `MXFP4-E2M1` and `FP8-E4M3` -/

theorem mxfp4_witness :
    (15 / 17 : Rat) * (15 / 17) + (8 / 17) * (8 / 17) = 1 ∧
    quantMXFP4 (15 / 17) = 1 ∧ quantMXFP4 (8 / 17) = 1 / 2 ∧
    ratAbs (quantMXFP4 (15 / 17) * quantMXFP4 (15 / 17) +
            quantMXFP4 (8 / 17) * quantMXFP4 (8 / 17) - 1) = 1 / 4 := by
  have hq15 : quantMXFP4 (15 / 17) = 1 := by
    unfold quantMXFP4 quantMXFP4Nonneg
    have h0 : (0 : Rat) ≤ (15 / 17 : Rat) := by
      have h := rat_div_le_div_of_int (a := 0) (b := 1) (c := 15) (d := 17) (by decide) (by decide) (by decide)
      have h0' : ((0 : Int) : Rat) / ((1 : Int) : Rat) = 0 := by grind
      rw [h0'] at h; exact h
    have h78 : (7 / 8 : Rat) ≤ (15 / 17 : Rat) := rat_div_le_div_of_int (by decide) (by decide) (by decide)
    have h1 : ¬ (15 / 17 : Rat) < 1 / 16 := Rat.not_lt.mpr (Rat.le_trans (rat_div_le_div_of_int (by decide) (by decide) (by decide)) h78)
    have h2 : ¬ (15 / 17 : Rat) < 3 / 16 := Rat.not_lt.mpr (Rat.le_trans (rat_div_le_div_of_int (by decide) (by decide) (by decide)) h78)
    have h3 : ¬ (15 / 17 : Rat) < 5 / 16 := Rat.not_lt.mpr (Rat.le_trans (rat_div_le_div_of_int (by decide) (by decide) (by decide)) h78)
    have h4 : ¬ (15 / 17 : Rat) < 7 / 16 := Rat.not_lt.mpr (Rat.le_trans (rat_div_le_div_of_int (by decide) (by decide) (by decide)) h78)
    have h5 : ¬ (15 / 17 : Rat) < 5 / 8 := Rat.not_lt.mpr (Rat.le_trans (rat_div_le_div_of_int (by decide) (by decide) (by decide)) h78)
    have h6 : ¬ (15 / 17 : Rat) < 7 / 8 := Rat.not_lt.mpr h78
    simp [h0, h1, h2, h3, h4, h5, h6]
  have hq8 : quantMXFP4 (8 / 17) = 1 / 2 := by
    unfold quantMXFP4 quantMXFP4Nonneg
    have h0 : (0 : Rat) ≤ (8 / 17 : Rat) := by
      have h := rat_div_le_div_of_int (a := 0) (b := 1) (c := 8) (d := 17) (by decide) (by decide) (by decide)
      have h0' : ((0 : Int) : Rat) / ((1 : Int) : Rat) = 0 := by grind
      rw [h0'] at h; exact h
    have h716 : (7 / 16 : Rat) ≤ (8 / 17 : Rat) := rat_div_le_div_of_int (by decide) (by decide) (by decide)
    have h1 : ¬ (8 / 17 : Rat) < 1 / 16 := Rat.not_lt.mpr (Rat.le_trans (rat_div_le_div_of_int (by decide) (by decide) (by decide)) h716)
    have h2 : ¬ (8 / 17 : Rat) < 3 / 16 := Rat.not_lt.mpr (Rat.le_trans (rat_div_le_div_of_int (by decide) (by decide) (by decide)) h716)
    have h3 : ¬ (8 / 17 : Rat) < 5 / 16 := Rat.not_lt.mpr (Rat.le_trans (rat_div_le_div_of_int (by decide) (by decide) (by decide)) h716)
    have h4 : ¬ (8 / 17 : Rat) < 7 / 16 := Rat.not_lt.mpr h716
    have h5 : (8 / 17 : Rat) < 5 / 8 := rat_div_lt_div_of_int (by decide) (by decide) (by decide)
    simp [h0, h1, h2, h3, h4, h5]
  refine ⟨by grind, hq15, hq8, ?_⟩
  rw [hq15, hq8]
  have heq : (1 : Rat) * 1 + (1 / 2) * (1 / 2) - 1 = 1 / 4 := by grind
  rw [heq, ratAbs_of_nonneg]
  have h := rat_div_le_div_of_int (a := 0) (b := 1) (c := 1) (d := 4) (by decide) (by decide) (by decide)
  have h0' : ((0 : Int) : Rat) / ((1 : Int) : Rat) = 0 := by grind
  rw [h0'] at h; exact h

theorem fp8_witness :
    (1323 / 1565 : Rat) * (1323 / 1565) + (836 / 1565) * (836 / 1565) = 1 ∧
    quantFP8E4M3 (1323 / 1565) = 7 / 8 ∧ quantFP8E4M3 (836 / 1565) = 9 / 16 ∧
    ratAbs (quantFP8E4M3 (1323 / 1565) * quantFP8E4M3 (1323 / 1565) +
            quantFP8E4M3 (836 / 1565) * quantFP8E4M3 (836 / 1565) - 1) = 21 / 256 := by
  have hq1 : quantFP8E4M3 (1323 / 1565) = 7 / 8 := by
    unfold quantFP8E4M3 quantFP8E4M3Nonneg quantFP8E4M3Top
    have h0 : (0 : Rat) ≤ (1323 / 1565 : Rat) := by
      have h := rat_div_le_div_of_int (a := 0) (b := 1) (c := 1323) (d := 1565) (by decide) (by decide) (by decide)
      have h0' : ((0 : Int) : Rat) / ((1 : Int) : Rat) = 0 := by grind
      rw [h0'] at h; exact h
    have hlo : (31 / 64 : Rat) ≤ (1323 / 1565 : Rat) := rat_div_le_div_of_int (by decide) (by decide) (by decide)
    have hgt27 : (27 / 32 : Rat) < (1323 / 1565 : Rat) := rat_div_lt_div_of_int (by decide) (by decide) (by decide)
    have hle29 : (1323 / 1565 : Rat) ≤ 29 / 32 := rat_div_le_div_of_int (by decide) (by decide) (by decide)
    have h1 : ¬ (1323 / 1565 : Rat) ≤ 17 / 32 := Rat.not_le.mpr (rat_lt_of_le_of_lt (rat_div_le_div_of_int (by decide) (by decide) (by decide)) hgt27)
    have h2 : ¬ (1323 / 1565 : Rat) < 19 / 32 := Rat.not_lt.mpr (Rat.le_of_lt (rat_lt_of_le_of_lt (rat_div_le_div_of_int (by decide) (by decide) (by decide)) hgt27))
    have h3 : ¬ (1323 / 1565 : Rat) ≤ 21 / 32 := Rat.not_le.mpr (rat_lt_of_le_of_lt (rat_div_le_div_of_int (by decide) (by decide) (by decide)) hgt27)
    have h4 : ¬ (1323 / 1565 : Rat) < 23 / 32 := Rat.not_lt.mpr (Rat.le_of_lt (rat_lt_of_le_of_lt (rat_div_le_div_of_int (by decide) (by decide) (by decide)) hgt27))
    have h5 : ¬ (1323 / 1565 : Rat) ≤ 25 / 32 := Rat.not_le.mpr (rat_lt_of_le_of_lt (rat_div_le_div_of_int (by decide) (by decide) (by decide)) hgt27)
    have h6 : ¬ (1323 / 1565 : Rat) < 27 / 32 := Rat.not_lt.mpr (Rat.le_of_lt hgt27)
    simp only [h0, hlo, h1, h2, h3, h4, h5, h6, hle29, ↓reduceIte]
    grind
  have hq2 : quantFP8E4M3 (836 / 1565) = 9 / 16 := by
    unfold quantFP8E4M3 quantFP8E4M3Nonneg quantFP8E4M3Top
    have h0 : (0 : Rat) ≤ (836 / 1565 : Rat) := by
      have h := rat_div_le_div_of_int (a := 0) (b := 1) (c := 836) (d := 1565) (by decide) (by decide) (by decide)
      have h0' : ((0 : Int) : Rat) / ((1 : Int) : Rat) = 0 := by grind
      rw [h0'] at h; exact h
    have hlo : (31 / 64 : Rat) ≤ (836 / 1565 : Rat) := rat_div_le_div_of_int (by decide) (by decide) (by decide)
    have h1 : ¬ (836 / 1565 : Rat) ≤ 17 / 32 := Rat.not_le.mpr (rat_div_lt_div_of_int (by decide) (by decide) (by decide))
    have h2 : (836 / 1565 : Rat) < 19 / 32 := rat_div_lt_div_of_int (by decide) (by decide) (by decide)
    simp only [h0, hlo, h1, h2, ↓reduceIte]
  refine ⟨by grind, hq1, hq2, ?_⟩
  rw [hq1, hq2]
  have heq : (7 / 8 : Rat) * (7 / 8) + (9 / 16) * (9 / 16) - 1 = 21 / 256 := by grind
  rw [heq, ratAbs_of_nonneg]
  have h := rat_div_le_div_of_int (a := 0) (b := 1) (c := 21) (d := 256) (by decide) (by decide) (by decide)
  have h0' : ((0 : Int) : Rat) / ((1 : Int) : Rat) = 0 := by grind
  rw [h0'] at h; exact h

/-! ### Headline Theorem 4: `quantized_rotation_norm_drift_exact` -/

theorem quantized_rotation_norm_drift_exact :
    (∀ c s : Rat, c * c + s * s = 1 →
      ratAbs (quantMXFP4 c * quantMXFP4 c + quantMXFP4 s * quantMXFP4 s - 1) ≤ 1 / 4) ∧
    ((15 / 17 : Rat) * (15 / 17) + (8 / 17) * (8 / 17) = 1 ∧
     quantMXFP4 (15 / 17) = 1 ∧ quantMXFP4 (8 / 17) = 1 / 2 ∧
     ratAbs (quantMXFP4 (15 / 17) * quantMXFP4 (15 / 17) +
             quantMXFP4 (8 / 17) * quantMXFP4 (8 / 17) - 1) = 1 / 4) ∧
    (∀ c s : Rat, c * c + s * s = 1 →
      ratAbs (quantFP8E4M3 c * quantFP8E4M3 c + quantFP8E4M3 s * quantFP8E4M3 s - 1) ≤ 21 / 256) ∧
    ((1323 / 1565 : Rat) * (1323 / 1565) + (836 / 1565) * (836 / 1565) = 1 ∧
     quantFP8E4M3 (1323 / 1565) = 7 / 8 ∧ quantFP8E4M3 (836 / 1565) = 9 / 16 ∧
     ratAbs (quantFP8E4M3 (1323 / 1565) * quantFP8E4M3 (1323 / 1565) +
             quantFP8E4M3 (836 / 1565) * quantFP8E4M3 (836 / 1565) - 1) = 21 / 256) ∧
    (∀ t : Rat, cayleyCos t * cayleyCos t + cayleySin t * cayleySin t - 1 = 0) ∧
    (∀ (B k : Nat),
      ((2 ^ (2 * B) : Int) - (k : Int) * (k : Int)) * ((2 ^ (2 * B) : Int) - (k : Int) * (k : Int)) +
      (2 * (2 ^ B : Int) * (k : Int)) * (2 * (2 ^ B : Int) * (k : Int)) =
      ((2 ^ (2 * B) : Int) + (k : Int) * (k : Int)) * ((2 ^ (2 * B) : Int) + (k : Int) * (k : Int))) := by
  refine ⟨mxfp4_norm_drift_le, mxfp4_witness, fp8_norm_drift_le, fp8_witness, ?_, ?_⟩
  · intro t
    have h := cayley_unit_circle t
    grind
  · intro B k
    have hpow : (2 ^ (2 * B) : Int) = (2 ^ B : Int) * (2 ^ B : Int) := by
      have hnat : 2 ^ (2 * B) = 2 ^ B * 2 ^ B := by
        rw [← Nat.pow_add]
        congr 1; omega
      exact_mod_cast hnat
    rw [hpow]
    grind

end RopeQ32Coprime
