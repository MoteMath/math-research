/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RingAttnKulisch.SinkVanishing

/-!
# Theorem 4: The Descending-`m_i` Phase-Transition Paradox

Proves both regimes of max-first (`DESC`) online-softmax merging:
1. **Universal Rescale-Count Separation**: Any non-increasing (`DESC`) sequence performs
   strictly `0` running-accumulator rescales (`rescaleCount ws = 0`), whereas any strictly
   increasing (`ASC`/`L2R`) sequence of length `n` performs `n - 1` accumulator rescales.
2. **Regime I (Narrow-Span Staircase Witness, `p = 4` FP8-E4M3)**: On the narrow-span
   3-chunk ascending staircase `[(49/64, 5/8), (7/8, 1/8), (1, 1/2)]` (true denominator
   `557/512`), `DESC` performs `0` accumulator rescales (vs `2` for `L2R`/`ASC`) and
   achieves strictly smaller error (`19/512 < 45/512`, `> 2.3x` reduction).
3. **Regime II (Wide-Span / Attention-Sink Regime, universal for all `p ≥ 2`, `k ≥ 2`)**:
   `DESC` places the sink chunk first and forces every bulk chunk to meet the largest
   accumulator (`1 + 2^{-p} ↦ 1`), dropping 100% of bulk (`l = 1`), making `DESC` strictly
   WORSE than both balanced `TREE` and `ASC` (which accumulate bulk before meeting the sink).
-/

namespace RingAttnKulisch

theorem rescaleCountAux_eq_zero {cur : Rat} :
    ∀ ws : List Rat, isNonIncreasing (cur :: ws) → rescaleCountAux cur ws = 0
  | [], _ => rfl
  | w :: rest, h => by
      have hle : w ≤ cur := h.1
      have hnot : ¬ (cur < w) := Rat.not_lt.mpr hle
      unfold rescaleCountAux
      simp only [hnot, ↓reduceIte]
      have hrest : isNonIncreasing (cur :: rest) := by
        cases rest with
        | nil => trivial
        | cons u us =>
          have hwu : u ≤ w := h.2.1
          exact ⟨Rat.le_trans hwu hle, h.2.2⟩
      exact rescaleCountAux_eq_zero rest hrest

theorem rescaleCount_nonIncreasing {ws : List Rat} (h : isNonIncreasing ws) :
    rescaleCount ws = 0 := by
  cases ws with
  | nil => rfl
  | cons w rest => exact rescaleCountAux_eq_zero rest h

theorem rescaleCountAux_strictlyIncreasing {cur : Rat} :
    ∀ ws : List Rat, isStrictlyIncreasing (cur :: ws) → rescaleCountAux cur ws = ws.length
  | [], _ => rfl
  | w :: rest, h => by
      have hlt : cur < w := h.1
      unfold rescaleCountAux
      simp only [hlt, ↓reduceIte]
      have ih := rescaleCountAux_strictlyIncreasing rest h.2
      rw [ih]
      simp [Nat.add_comm]

theorem rat_le_of_mul_pos {a b c : Rat} (hc : (0 : Rat) < c) (h : a * c ≤ b * c) : a ≤ b := by
  have hinv := rat_mul_le_mul_of_nonneg_right h (Rat.le_of_lt (rat_inv_pos hc))
  have hne : c ≠ 0 := Rat.ne_of_gt hc
  have h1 : ∀ x : Rat, x * c * (1 / c) = x := by
    intro x; rw [Rat.mul_assoc, Rat.div_def, Rat.one_mul, Rat.mul_inv_cancel _ hne, Rat.mul_one]
  rw [h1 a, h1 b] at hinv
  exact hinv

theorem rat_lt_of_mul_pos {a b c : Rat} (hc : (0 : Rat) < c) (h : a * c < b * c) : a < b := by
  have hinv := rat_mul_lt_mul_of_pos_right h (rat_inv_pos hc)
  have hne : c ≠ 0 := Rat.ne_of_gt hc
  have h1 : ∀ x : Rat, x * c * (1 / c) = x := by
    intro x; rw [Rat.mul_assoc, Rat.div_def, Rat.one_mul, Rat.mul_inv_cancel _ hne, Rat.mul_one]
  rw [h1 a, h1 b] at hinv
  exact hinv

theorem rescaleCount_strictlyIncreasing {ws : List Rat} (h : isStrictlyIncreasing ws) :
    rescaleCount ws = ws.length - 1 := by
  cases ws with
  | nil => rfl
  | cons w rest =>
    change rescaleCountAux w rest = (w :: rest).length - 1
    rw [rescaleCountAux_strictlyIncreasing rest h]
    simp

/-! ### Regime I: Exact Narrow-Span Staircase Witness (`p = 4`, FP8-E4M3) -/

theorem rneGrid4_35_64 : rneGrid 4 (35 / 64) = 1 / 2 := by
  unfold rneGrid
  have hmul : (35 / 64 : Rat) * pow2Rat 3 = 35 / 8 := by
    unfold pow2Rat
    have h8 : ((2 ^ 3 : Nat) : Rat) = 8 := by decide
    rw [h8]; grind
  rw [hmul]
  have hrne : rneInt (35 / 8) = 4 := by
    apply rneInt_of_lt_half
    · apply rat_le_of_mul_pos (c := (8 : Rat)) (by decide)
      have h1 : ((4 : Int) : Rat) * 8 = ((32 : Int) : Rat) := by grind
      have h2 : (35 / 8 : Rat) * 8 = ((35 : Int) : Rat) := by grind
      rw [h1, h2]; exact rat_intCast_le (by omega)
    · apply rat_lt_of_mul_pos (c := (8 : Rat)) (by decide)
      have h1 : (35 / 8 : Rat) * 8 = ((35 : Int) : Rat) := by grind
      have h2 : (((4 : Int) : Rat) + 1 / 2) * 8 = ((36 : Int) : Rat) := by grind
      rw [h1, h2]; exact rat_intCast_lt (by omega)
  rw [hrne]
  unfold invPow2Rat
  have h8 : ((2 ^ 3 : Nat) : Rat) = 8 := by decide
  rw [h8]; grind

theorem rneGrid4_5_8 : rneGrid 4 (5 / 8) = 5 / 8 := by
  have hmul : (5 / 8 : Rat) * pow2Rat 3 = ((5 : Int) : Rat) := by
    unfold pow2Rat
    have h8 : ((2 ^ 3 : Nat) : Rat) = 8 := by decide
    rw [h8]; grind
  rw [rneGrid_of_int_mul hmul]
  unfold invPow2Rat
  have h8 : ((2 ^ 3 : Nat) : Rat) = 8 := by decide
  rw [h8]; grind

theorem rneGrid4_1 : rneGrid 4 1 = 1 := by
  have hmul : (1 : Rat) * pow2Rat 3 = ((8 : Int) : Rat) := by
    unfold pow2Rat
    have h8 : ((2 ^ 3 : Nat) : Rat) = 8 := by decide
    rw [h8]; grind
  rw [rneGrid_of_int_mul hmul]
  unfold invPow2Rat
  have h8 : ((2 ^ 3 : Nat) : Rat) = 8 := by decide
  rw [h8]; grind

theorem rneGrid4_7_64 : rneGrid 4 (7 / 64) = 1 / 8 := by
  unfold rneGrid
  have hmul : (7 / 64 : Rat) * pow2Rat 3 = 7 / 8 := by
    unfold pow2Rat
    have h8 : ((2 ^ 3 : Nat) : Rat) = 8 := by decide
    rw [h8]; grind
  rw [hmul]
  have hrne : rneInt (7 / 8) = 1 := by
    apply rneInt_of_gt_half (n := 0)
    · apply rat_lt_of_mul_pos (c := (8 : Rat)) (by decide)
      have h1 : (((0 : Int) : Rat) + 1 / 2) * 8 = ((4 : Int) : Rat) := by grind
      have h2 : (7 / 8 : Rat) * 8 = ((7 : Int) : Rat) := by grind
      rw [h1, h2]; exact rat_intCast_lt (by omega)
    · apply rat_lt_of_mul_pos (c := (8 : Rat)) (by decide)
      have h1 : (7 / 8 : Rat) * 8 = ((7 : Int) : Rat) := by grind
      have h2 : (((0 + 1 : Int) : Rat)) * 8 = ((8 : Int) : Rat) := by grind
      rw [h1, h2]; exact rat_intCast_lt (by omega)
  rw [hrne]
  unfold invPow2Rat
  have h8 : ((2 ^ 3 : Nat) : Rat) = 8 := by decide
  rw [h8]; grind

theorem rneGrid4_245_512 : rneGrid 4 (245 / 512) = 1 / 2 := by
  unfold rneGrid
  have hmul : (245 / 512 : Rat) * pow2Rat 3 = 245 / 64 := by
    unfold pow2Rat
    have h8 : ((2 ^ 3 : Nat) : Rat) = 8 := by decide
    rw [h8]; grind
  rw [hmul]
  have hrne : rneInt (245 / 64) = 4 := by
    apply rneInt_of_gt_half (n := 3)
    · apply rat_lt_of_mul_pos (c := (64 : Rat)) (by decide)
      have h1 : (((3 : Int) : Rat) + 1 / 2) * 64 = ((224 : Int) : Rat) := by grind
      have h2 : (245 / 64 : Rat) * 64 = ((245 : Int) : Rat) := by grind
      rw [h1, h2]; exact rat_intCast_lt (by omega)
    · apply rat_lt_of_mul_pos (c := (64 : Rat)) (by decide)
      have h1 : (245 / 64 : Rat) * 64 = ((245 : Int) : Rat) := by grind
      have h2 : (((3 + 1 : Int) : Rat)) * 64 = ((256 : Int) : Rat) := by grind
      rw [h1, h2]; exact rat_intCast_lt (by omega)
  rw [hrne]
  unfold invPow2Rat
  have h8 : ((2 ^ 3 : Nat) : Rat) = 8 := by decide
  rw [h8]; grind

theorem rneGrid4_9_8 : rneGrid 4 (9 / 8) = 9 / 8 := by
  have hmul : (9 / 8 : Rat) * pow2Rat 3 = ((9 : Int) : Rat) := by
    unfold pow2Rat
    have h8 : ((2 ^ 3 : Nat) : Rat) = 8 := by decide
    rw [h8]; grind
  rw [rneGrid_of_int_mul hmul]
  unfold invPow2Rat
  have h8 : ((2 ^ 3 : Nat) : Rat) = 8 := by decide
  rw [h8]; grind

theorem rat_49_64_lt_7_8 : (49 / 64 : Rat) < 7 / 8 := by
  apply rat_lt_of_mul_pos (c := (64 : Rat)) (by decide)
  have h1 : (49 / 64 : Rat) * 64 = ((49 : Int) : Rat) := by grind
  have h2 : (7 / 8 : Rat) * 64 = ((56 : Int) : Rat) := by grind
  rw [h1, h2]; exact rat_intCast_lt (by omega)

theorem rat_7_8_lt_1 : (7 / 8 : Rat) < 1 := by
  apply rat_lt_of_mul_pos (c := (8 : Rat)) (by decide)
  have h1 : (7 / 8 : Rat) * 8 = ((7 : Int) : Rat) := by grind
  have h2 : (1 : Rat) * 8 = ((8 : Int) : Rat) := by grind
  rw [h1, h2]; exact rat_intCast_lt (by omega)

theorem regimeI_asc_eval : seqMergeDenom 4 regimeIChunksAsc = 1 := by
  unfold seqMergeDenom regimeIChunksAsc seqMergeDenomAux
  have h1 : (49 / 64 : Rat) ≤ 7 / 8 := Rat.le_of_lt rat_49_64_lt_7_8
  have h2 : (7 / 8 : Rat) ≤ 1 := Rat.le_of_lt rat_7_8_lt_1
  simp only [h1, ↓reduceIte]
  have eq1 : (49 / 64 : Rat) / (7 / 8) * (5 / 8) = 35 / 64 := by grind
  rw [eq1, rneGrid4_35_64]
  have eq2 : (1 / 2 : Rat) + 1 / 8 = 5 / 8 := by grind
  rw [eq2, rneGrid4_5_8]
  unfold seqMergeDenomAux
  simp only [h2, ↓reduceIte]
  have eq3 : (7 / 8 : Rat) / 1 * (5 / 8) = 35 / 64 := by grind
  rw [eq3, rneGrid4_35_64]
  have eq4 : (1 / 2 : Rat) + 1 / 2 = 1 := by grind
  rw [eq4, rneGrid4_1]
  rfl

theorem regimeI_desc_eval : seqMergeDenom 4 regimeIChunksDesc = 9 / 8 := by
  unfold seqMergeDenom regimeIChunksDesc seqMergeDenomAux
  have h1 : ¬ ((1 : Rat) ≤ 7 / 8) := Rat.not_le.mpr rat_7_8_lt_1
  have h2 : ¬ ((1 : Rat) ≤ 49 / 64) :=
    Rat.not_le.mpr (rat_lt_of_lt_of_le rat_49_64_lt_7_8 (Rat.le_of_lt rat_7_8_lt_1))
  simp only [h1, ↓reduceIte]
  have eq1 : (7 / 8 : Rat) / 1 * (1 / 8) = 7 / 64 := by grind
  rw [eq1, rneGrid4_7_64]
  have eq2 : (1 / 2 : Rat) + 1 / 8 = 5 / 8 := by grind
  rw [eq2, rneGrid4_5_8]
  unfold seqMergeDenomAux
  simp only [h2, ↓reduceIte]
  have eq3 : (49 / 64 : Rat) / 1 * (5 / 8) = 245 / 512 := by grind
  rw [eq3, rneGrid4_245_512]
  have eq4 : (5 / 8 : Rat) + 1 / 2 = 9 / 8 := by grind
  rw [eq4, rneGrid4_9_8]
  rfl

/-! ### Regime II: Universal Wide-Span / Attention-Sink Reversal -/

theorem asc_sink_survives_at_p {p k : Nat} (hp : 2 ≤ p) (hk : 2 ≤ k) :
    1 + invPow2Rat (p - 1) ≤
      rneGrid p (1 + ((2 ^ k - 1 : Nat) : Rat) * invPow2Rat p) := by
  have h2k : 2 ≤ 2 ^ k - 1 := by
    have : 4 ≤ 2 ^ k := by
      have hpow : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
      omega
    omega
  have hge : 2 * invPow2Rat p ≤ ((2 ^ k - 1 : Nat) : Rat) * invPow2Rat p :=
    rat_mul_le_mul_of_nonneg_right (rat_natCast_le h2k) (Rat.le_of_lt (invPow2Rat_pos p))
  have h2ulp : 2 * invPow2Rat p = invPow2Rat (p - 1) := by
    have hp1 : p = 1 + (p - 1) := by omega
    have hinv : invPow2Rat p = invPow2Rat 1 * invPow2Rat (p - 1) := by
      rw [← invPow2Rat_add, ← hp1]
    rw [hinv]
    have h1 : invPow2Rat 1 = 1 / 2 := by unfold invPow2Rat; grind
    rw [h1]; grind
  rw [h2ulp] at hge
  have hsum : 1 + invPow2Rat (p - 1) ≤ 1 + ((2 ^ k - 1 : Nat) : Rat) * invPow2Rat p :=
    rat_add_le_add Rat.le_refl hge
  have hmul : (((2 ^ (p - 1) + 1 : Nat) : Int) : Rat) ≤
      (1 + ((2 ^ k - 1 : Nat) : Rat) * invPow2Rat p) * pow2Rat (p - 1) := by
    have h1 : (((2 ^ (p - 1) + 1 : Nat) : Int) : Rat) =
        (1 + invPow2Rat (p - 1)) * pow2Rat (p - 1) := by
      rw [Rat.add_mul, Rat.one_mul, invPow2Rat_mul_pow2Rat]
      unfold pow2Rat; rw [Int.natCast_add, Rat.intCast_add]; rfl
    rw [h1]
    exact rat_mul_le_mul_of_nonneg_right hsum (Rat.le_of_lt (pow2Rat_pos (p - 1)))
  have hrne := rneGrid_ge_of_int_le hmul
  have hcast : (((2 ^ (p - 1) + 1 : Nat) : Int) : Rat) * invPow2Rat (p - 1) =
      1 + invPow2Rat (p - 1) := by
    have : (((2 ^ (p - 1) + 1 : Nat) : Int) : Rat) = pow2Rat (p - 1) + 1 := by
      unfold pow2Rat; rw [Int.natCast_add, Rat.intCast_add]; rfl
    rw [this, Rat.add_mul, pow2Rat_mul_invPow2Rat, Rat.one_mul]
  rw [hcast] at hrne
  exact hrne

/-- Headline Theorem 4: The Descending-`m_i` Phase-Transition Paradox.
    Exhibits both regimes:
    - Universal rescale elimination (`0` rescales for `DESC` vs `n - 1` for `ASC`),
    - Regime I (narrow-span FP8-E4M3 staircase): `DESC` has `0` rescales vs `2` for `L2R`/`ASC`
      and strictly smaller error (`19/512 < 45/512`),
    - Regime II (wide-span attention sink, universal for all `p ≥ 2`, `k ≥ 2`): `DESC` drops
      100% of bulk (`l = 1`), making `DESC` strictly worse than both `TREE` and `ASC`. -/
theorem descending_mi_phase_transition_paradox :
    (∀ ws : List Rat, isNonIncreasing ws → rescaleCount ws = 0) ∧
    (∀ ws : List Rat, isStrictlyIncreasing ws → rescaleCount ws = ws.length - 1) ∧
    (rescaleCount [49 / 64, 7 / 8, 1] = 2 ∧
     rescaleCount [1, 7 / 8, 49 / 64] = 0 ∧
     seqMergeDenom 4 regimeIChunksAsc = 1 ∧
     seqMergeDenom 4 regimeIChunksDesc = 9 / 8 ∧
     ratAbs (557 / 512 - seqMergeDenom 4 regimeIChunksAsc) = 45 / 512 ∧
     ratAbs (557 / 512 - seqMergeDenom 4 regimeIChunksDesc) = 19 / 512 ∧
     ratAbs (557 / 512 - seqMergeDenom 4 regimeIChunksDesc) <
       ratAbs (557 / 512 - seqMergeDenom 4 regimeIChunksAsc)) ∧
    (∀ (p k : Nat), 2 ≤ p → 2 ≤ k →
      l2rSinkAccum p p (2 ^ k - 1) = 1 ∧
      l2rSinkAccum p p (2 ^ k - 1) < treeSinkAccum p p k ∧
      l2rSinkAccum p p (2 ^ k - 1) <
        rneGrid p (1 + ((2 ^ k - 1 : Nat) : Rat) * invPow2Rat p)) := by
  refine ⟨fun ws h => rescaleCount_nonIncreasing h,
    fun ws h => rescaleCount_strictlyIncreasing h, ?_, ?_⟩
  · have hr_asc : rescaleCount [49 / 64, 7 / 8, 1] = 2 := by
      apply rescaleCount_strictlyIncreasing
      unfold isStrictlyIncreasing
      exact ⟨rat_49_64_lt_7_8, rat_7_8_lt_1, trivial⟩
    have hr_desc : rescaleCount [1, 7 / 8, 49 / 64] = 0 := by
      apply rescaleCount_nonIncreasing
      unfold isNonIncreasing
      exact ⟨Rat.le_of_lt rat_7_8_lt_1, Rat.le_of_lt rat_49_64_lt_7_8, trivial⟩
    have ha : ratAbs (557 / 512 - seqMergeDenom 4 regimeIChunksAsc) = 45 / 512 := by
      rw [regimeI_asc_eval]
      have hdiff : (557 / 512 : Rat) - 1 = 45 / 512 := by grind
      rw [hdiff]; unfold ratAbs
      have hnn : (0 : Rat) ≤ 45 / 512 := Rat.le_of_lt (rat_div_pos (by decide) (by decide))
      simp [hnn]
    have hd : ratAbs (557 / 512 - seqMergeDenom 4 regimeIChunksDesc) = 19 / 512 := by
      rw [regimeI_desc_eval]
      have hdiff : (557 / 512 : Rat) - 9 / 8 = -(19 / 512) := by grind
      rw [hdiff]; unfold ratAbs
      have hneg : ¬ ((0 : Rat) ≤ -(19 / 512)) := by
        apply Rat.not_le.mpr
        apply rat_lt_of_mul_pos (c := (512 : Rat)) (by decide)
        have h1 : (-(19 / 512) : Rat) * 512 = ((-19 : Int) : Rat) := by grind
        have h2 : (0 : Rat) * 512 = ((0 : Int) : Rat) := by grind
        rw [h1, h2]; exact rat_intCast_lt (by omega)
      simp [hneg]
    refine ⟨hr_asc, hr_desc, regimeI_asc_eval, regimeI_desc_eval, ha, hd, ?_⟩
    rw [ha, hd]
    apply rat_lt_of_mul_pos (c := (512 : Rat)) (by decide)
    have h1 : (19 / 512 : Rat) * 512 = ((19 : Int) : Rat) := by grind
    have h2 : (45 / 512 : Rat) * 512 = ((45 : Int) : Rat) := by grind
    rw [h1, h2]; exact rat_intCast_lt (by omega)
  · intro p k hp hk
    have hl2r := l2rSinkAccum_eq_one hp (Nat.le_refl p) (2 ^ k - 1)
    have htree := treeSinkAccum_ge_one_add_ulp (Δ := p) hp k (by omega) (by omega)
    have hasc := asc_sink_survives_at_p hp hk
    have hlt1 : (1 : Rat) < 1 + invPow2Rat (p - 1) := by
      have h := rat_add_lt_add_left (c := (1 : Rat)) (invPow2Rat_pos (p - 1))
      have h0 : (1 : Rat) + 0 = 1 := by grind
      rw [h0] at h; exact h
    refine ⟨hl2r, ?_, ?_⟩
    · rw [hl2r]; exact rat_lt_of_lt_of_le hlt1 htree
    · rw [hl2r]; exact rat_lt_of_lt_of_le hlt1 hasc

end RingAttnKulisch
