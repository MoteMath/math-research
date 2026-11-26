/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EmbedZipfLazyStamp.RneFlush

/-!
# Theorem 3: Universal BF16 Sparse AdamW Second-Moment (`v_t`) Decay-Freeze Law

Pure-`Init` exact IEEE-754 RNE proof that for any `p`-mantissa-bit floating-point format
(`BF16`: `p = 7`), whenever `0 ≤ 1 - β_2 ≤ 2^(-(p + 2))` (`1/512` for `BF16`, which traps
standard `β_2 = 0.999` since `1 - β_2 = 1/1000 < 1/512` and weight decay `η * λ = 1/10000 < 1/512`):
1. `fl_F(β_2 * v) = v` for **EVERY** normal positive float `v = (2^p + m) * 2^(e - p)` (`m < 2^p`),
   including every binade boundary `v = 2^e` (`m = 0`) via RNE tie-to-even!
2. By induction on `K : Nat`, `K` absent steps (`g_t = 0`) leave `v_K = v_0` identically
   (`100%` permanent decay freeze).
3. Sharpness: for any `1 - β` strictly above `2^(-(p+2))` (and `< 2^(-(p+1))`), binade
   boundaries `v = 2^e` (`m = 0`) strictly decay (`fl_F(β * 2^e) ≠ 2^e`).
-/

namespace EmbedZipfLazyStamp

theorem normalFloat_freeze_one_step (p : Nat) (e : Int) (m : Nat) (hm : m < 2 ^ p)
    (β : Rat) (hβ_le : (0 : Rat) ≤ 1 - β) (hβ_thresh : 1 - β ≤ pow2Int (-((p + 2 : Nat) : Int))) :
    rneFloatBelow p e m (β * normalFloat p e m) = normalFloat p e m := by
  unfold rneFloatBelow
  by_cases hm0 : m = 0
  · subst hm0
    simp only [↓reduceIte]
    let u : Rat := pow2Int (e - 1 - (p : Int))
    have hu_pos : (0 : Rat) < u := pow2Int_pos _
    have hv_eq : normalFloat p e 0 = ((2 ^ (p + 1) : Nat) : Rat) * u := by
      unfold normalFloat
      have hadd : 2 ^ p + 0 = 2 ^ p := Nat.add_zero _
      rw [hadd]
      have hpow : pow2Int (e - (p : Int)) = 2 * u := by
        have : e - (p : Int) = (e - 1 - (p : Int)) + 1 := by omega
        rw [this, pow2Int_add_one]
      rw [hpow, Nat.pow_succ, Rat.natCast_mul]
      have h2 : ((2 : Nat) : Rat) = 2 := rfl
      rw [h2]; grind
    have hq_even : ((2 ^ (p + 1) : Nat) : Int) % 2 = 0 := by
      rw [Nat.pow_succ]
      omega
    have hsplit : β * normalFloat p e 0 =
        (((2 ^ (p + 1) : Nat) : Int) : Rat) * u + (-(1 - β) * normalFloat p e 0) := by
      have hcast : (((2 ^ (p + 1) : Nat) : Int) : Rat) = ((2 ^ (p + 1) : Nat) : Rat) := rfl
      rw [hcast, ← hv_eq]
      grind
    rw [hsplit]
    have hdw : ratAbs (-(1 - β) * normalFloat p e 0) ≤ u / 2 := by
      have hv_pos : (0 : Rat) ≤ normalFloat p e 0 :=
        Rat.mul_nonneg (rat_natCast_nonneg _) (Rat.le_of_lt (pow2Int_pos _))
      rw [ratAbs_mul, ratAbs_neg, ratAbs_of_nonneg hβ_le, ratAbs_of_nonneg hv_pos]
      have h1 : (1 - β) * normalFloat p e 0 ≤ pow2Int (-((p + 2 : Nat) : Int)) * normalFloat p e 0 :=
        rat_mul_le_mul_of_nonneg_right hβ_thresh hv_pos
      have h2 : pow2Int (-((p + 2 : Nat) : Int)) * normalFloat p e 0 = u / 2 := by
        rw [hv_eq]
        have h2p1 : ((2 ^ (p + 1) : Nat) : Rat) = pow2Int ((p + 1 : Nat) : Int) :=
          (pow2Int_ofNat (p + 1)).symm
        rw [h2p1]
        have hmul : pow2Int (-((p + 2 : Nat) : Int)) * (pow2Int ((p + 1 : Nat) : Int) * u) =
            (pow2Int (-((p + 2 : Nat) : Int)) * pow2Int ((p + 1 : Nat) : Int)) * u := by grind
        rw [hmul, ← pow2Int_add]
        have hexp : -((p + 2 : Nat) : Int) + ((p + 1 : Nat) : Int) = -1 := by omega
        rw [hexp]
        have hm1 : pow2Int (-1) = 1 / 2 := by unfold pow2Int; rfl
        rw [hm1]; grind
      rw [← h2]; exact h1
    rw [rneGrid_flush_even ((2 ^ (p + 1) : Nat) : Int) hq_even u _ hu_pos hdw]
    rw [hv_eq]; rfl
  · simp only [hm0, ↓reduceIte]
    let u : Rat := pow2Int (e - (p : Int))
    have hu_pos : (0 : Rat) < u := pow2Int_pos _
    have hv_eq : normalFloat p e m = (((2 ^ p + m : Nat) : Int) : Rat) * u := rfl
    have hsplit : β * normalFloat p e m =
        (((2 ^ p + m : Nat) : Int) : Rat) * u + (-(1 - β) * normalFloat p e m) := by
      rw [← hv_eq]; grind
    rw [hsplit]
    have hdw : ratAbs (-(1 - β) * normalFloat p e m) < u / 2 := by
      have hv_pos : (0 : Rat) < normalFloat p e m :=
        rat_mul_pos (rat_natCast_pos (by have := Nat.pow_pos (a := 2) (n := p) (by omega); omega)) hu_pos
      rw [ratAbs_mul, ratAbs_neg, ratAbs_of_nonneg hβ_le, ratAbs_of_nonneg (Rat.le_of_lt hv_pos)]
      have hlt_v : normalFloat p e m < ((2 ^ (p + 1) : Nat) : Rat) * u := by
        unfold normalFloat
        apply rat_mul_lt_mul_of_pos_right _ hu_pos
        have hnat : ((2 ^ p + m : Nat) : Int) < ((2 ^ (p + 1) : Nat) : Int) := by
          have : 2 ^ (p + 1) = 2 ^ p + 2 ^ p := by rw [Nat.pow_succ]; omega
          omega
        exact Rat.intCast_lt_intCast.mpr hnat
      have h1 : (1 - β) * normalFloat p e m ≤ pow2Int (-((p + 2 : Nat) : Int)) * normalFloat p e m :=
        rat_mul_le_mul_of_nonneg_right hβ_thresh (Rat.le_of_lt hv_pos)
      have h2 : pow2Int (-((p + 2 : Nat) : Int)) * normalFloat p e m <
          pow2Int (-((p + 2 : Nat) : Int)) * (((2 ^ (p + 1) : Nat) : Rat) * u) :=
        rat_mul_lt_mul_of_pos_left hlt_v (pow2Int_pos _)
      have h3 : pow2Int (-((p + 2 : Nat) : Int)) * (((2 ^ (p + 1) : Nat) : Rat) * u) = u / 2 := by
        have h2p1 : ((2 ^ (p + 1) : Nat) : Rat) = pow2Int ((p + 1 : Nat) : Int) :=
          (pow2Int_ofNat (p + 1)).symm
        rw [h2p1]
        have hmul : pow2Int (-((p + 2 : Nat) : Int)) * (pow2Int ((p + 1 : Nat) : Int) * u) =
            (pow2Int (-((p + 2 : Nat) : Int)) * pow2Int ((p + 1 : Nat) : Int)) * u := by grind
        rw [hmul, ← pow2Int_add]
        have hexp : -((p + 2 : Nat) : Int) + ((p + 1 : Nat) : Int) = -1 := by omega
        rw [hexp]
        have hm1 : pow2Int (-1) = 1 / 2 := by unfold pow2Int; rfl
        rw [hm1]; grind
      rw [← h3]
      exact rat_lt_of_le_of_lt h1 h2
    rw [rneGrid_flush_strict ((2 ^ p + m : Nat) : Int) u _ hu_pos hdw]
    exact hv_eq.symm

theorem normalFloat_freeze_k_steps (p : Nat) (e : Int) (m : Nat) (hm : m < 2 ^ p)
    (β : Rat) (hβ_le : (0 : Rat) ≤ 1 - β) (hβ_thresh : 1 - β ≤ pow2Int (-((p + 2 : Nat) : Int)))
    (K : Nat) :
    iterFloatDecay p e m β K (normalFloat p e m) = normalFloat p e m := by
  induction K with
  | zero => rfl
  | succ k ih =>
    simp only [iterFloatDecay]
    rw [normalFloat_freeze_one_step p e m hm β hβ_le hβ_thresh]
    exact ih

theorem normalFloat_boundary_unfreezes (p : Nat) (e : Int) (β : Rat)
    (hlo : pow2Int (-((p + 2 : Nat) : Int)) < 1 - β)
    (hhi : 1 - β < pow2Int (-((p + 1 : Nat) : Int))) :
    rneFloatBelow p e 0 (β * normalFloat p e 0) ≠ normalFloat p e 0 := by
  unfold rneFloatBelow
  simp only [↓reduceIte]
  let u : Rat := pow2Int (e - 1 - (p : Int))
  have hu_pos : (0 : Rat) < u := pow2Int_pos _
  have hv_eq : normalFloat p e 0 = ((2 ^ (p + 1) : Nat) : Rat) * u := by
    unfold normalFloat
    have hadd : 2 ^ p + 0 = 2 ^ p := Nat.add_zero _
    rw [hadd]
    have hpow : pow2Int (e - (p : Int)) = 2 * u := by
      have : e - (p : Int) = (e - 1 - (p : Int)) + 1 := by omega
      rw [this, pow2Int_add_one]
    rw [hpow, Nat.pow_succ, Rat.natCast_mul]
    have h2 : ((2 : Nat) : Rat) = 2 := rfl
    rw [h2]; grind
  have hv_pos : (0 : Rat) < normalFloat p e 0 := by
    rw [hv_eq]
    exact rat_mul_pos (pow2_nat_pos (p + 1)) hu_pos
  have h2p1_eq : ((2 ^ (p + 1) : Nat) : Rat) = pow2Int ((p + 1 : Nat) : Int) :=
    (pow2Int_ofNat (p + 1)).symm
  have hlo_dw : u / 2 < (1 - β) * normalFloat p e 0 := by
    have h1 := rat_mul_lt_mul_of_pos_right hlo hv_pos
    have h2 : pow2Int (-((p + 2 : Nat) : Int)) * normalFloat p e 0 = u / 2 := by
      rw [hv_eq, h2p1_eq]
      have hmul : pow2Int (-((p + 2 : Nat) : Int)) * (pow2Int ((p + 1 : Nat) : Int) * u) =
          (pow2Int (-((p + 2 : Nat) : Int)) * pow2Int ((p + 1 : Nat) : Int)) * u := by grind
      rw [hmul, ← pow2Int_add]
      have hexp : -((p + 2 : Nat) : Int) + ((p + 1 : Nat) : Int) = -1 := by omega
      rw [hexp]
      have hm1 : pow2Int (-1) = 1 / 2 := by unfold pow2Int; rfl
      rw [hm1]; grind
    rw [← h2]; exact h1
  have hhi_dw : (1 - β) * normalFloat p e 0 < u := by
    have h1 := rat_mul_lt_mul_of_pos_right hhi hv_pos
    have h2 : pow2Int (-((p + 1 : Nat) : Int)) * normalFloat p e 0 = u := by
      rw [hv_eq, h2p1_eq]
      have hmul : pow2Int (-((p + 1 : Nat) : Int)) * (pow2Int ((p + 1 : Nat) : Int) * u) =
          (pow2Int (-((p + 1 : Nat) : Int)) * pow2Int ((p + 1 : Nat) : Int)) * u := by grind
      rw [hmul, ← pow2Int_add]
      have hexp : -((p + 1 : Nat) : Int) + ((p + 1 : Nat) : Int) = 0 := by omega
      rw [hexp]
      have h0 : pow2Int 0 = 1 := by unfold pow2Int; rfl
      rw [h0, Rat.one_mul]
    rw [← h2]; exact h1
  let q1 : Int := ((2 ^ (p + 1) : Nat) : Int) - 1
  have hsplit : β * normalFloat p e 0 = (q1 : Rat) * u + (u - (1 - β) * normalFloat p e 0) := by
    have hq1 : (q1 : Rat) = ((2 ^ (p + 1) : Nat) : Rat) - 1 := by
      change (((2 ^ (p + 1) : Nat) : Int) - 1 : Int) = ((2 ^ (p + 1) : Nat) : Rat) - 1
      rw [Rat.intCast_sub]; rfl
    rw [hq1]
    have : (((2 ^ (p + 1) : Nat) : Rat) - 1) * u + (u - (1 - β) * normalFloat p e 0) =
        ((2 ^ (p + 1) : Nat) : Rat) * u - (1 - β) * normalFloat p e 0 := by grind
    rw [this, ← hv_eq]; grind
  have hdw_lt : ratAbs (u - (1 - β) * normalFloat p e 0) < u / 2 := by
    rw [ratAbs_lt_iff]
    constructor
    · have hpos : (0 : Rat) < u - (1 - β) * normalFloat p e 0 := rat_sub_pos hhi_dw
      have hneg : -(u / 2) < 0 := by
        have := rat_div_pos hu_pos (by decide : (0 : Rat) < 2)
        have : (0 : Rat) < 0 - (-(u / 2)) := by grind
        exact rat_lt_of_sub_pos this
      exact rat_lt_trans hneg hpos
    · have := rat_sub_pos hlo_dw
      have : (0 : Rat) < u / 2 - (u - (1 - β) * normalFloat p e 0) := by grind
      exact rat_lt_of_sub_pos this
  rw [hsplit, rneGrid_flush_strict q1 u _ hu_pos hdw_lt, hv_eq]
  intro heq
  have hq1 : (q1 : Rat) = ((2 ^ (p + 1) : Nat) : Rat) - 1 := by
    change (((2 ^ (p + 1) : Nat) : Int) - 1 : Int) = ((2 ^ (p + 1) : Nat) : Rat) - 1
    rw [Rat.intCast_sub]; rfl
  rw [hq1] at heq
  have hu0 : u = 0 := by grind
  exact Rat.ne_of_gt hu_pos hu0

/-- Headline Theorem 3 (`bf16_sparse_adamw_v_decay_freeze_exact`):
    Universal IEEE-754 RNE decay-freeze theorem for AdamW's second-moment EMA
    `v_{t+1} = β_2 * v_t` on absent rows (`g_t = 0`): proves that `1 - β_2 ≤ 2^(-(p+2))`
    (`1/512` for `BF16` `p = 7`, which traps standard `β_2 = 0.999` since `1/1000 < 1/512`,
    as well as `BF16` decoupled weight decay `η λ = 1/10000 < 1/512`) forces
    `fl_BF16(β_2 * v) = v` for EVERY normal `BF16` value `v` across all `K : Nat` steps
    (exact `100%` permanent decay freeze), and proves `2^(-(p+2))` is exact and sharp. -/
theorem bf16_sparse_adamw_v_decay_freeze_exact :
    (∀ (p : Nat) (e : Int) (m : Nat) (β : Rat),
      m < 2 ^ p → (0 : Rat) ≤ 1 - β → 1 - β ≤ pow2Int (-((p + 2 : Nat) : Int)) →
      rneFloatBelow p e m (β * normalFloat p e m) = normalFloat p e m ∧
      ∀ K : Nat, iterFloatDecay p e m β K (normalFloat p e m) = normalFloat p e m) ∧
    (pow2Int (-((7 + 2 : Nat) : Int)) = 1 / 512 ∧
     (1 : Rat) - (999 / 1000 : Rat) = 1 / 1000 ∧
     (1 / 1000 : Rat) < 1 / 512 ∧
     (1 : Rat) - (9999 / 10000 : Rat) = 1 / 10000 ∧
     (1 / 10000 : Rat) < 1 / 512) ∧
    (∀ (e : Int) (m : Nat), m < 128 →
      rneFloatBelow 7 e m ((999 / 1000 : Rat) * normalFloat 7 e m) = normalFloat 7 e m ∧
      (∀ K : Nat, iterFloatDecay 7 e m (999 / 1000 : Rat) K (normalFloat 7 e m) = normalFloat 7 e m) ∧
      rneFloatBelow 7 e m ((9999 / 10000 : Rat) * normalFloat 7 e m) = normalFloat 7 e m) ∧
    (∀ (p : Nat) (e : Int) (β : Rat),
      pow2Int (-((p + 2 : Nat) : Int)) < 1 - β → 1 - β < pow2Int (-((p + 1 : Nat) : Int)) →
      rneFloatBelow p e 0 (β * normalFloat p e 0) ≠ normalFloat p e 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p e m β hm hlo hhi
    exact ⟨normalFloat_freeze_one_step p e m hm β hlo hhi,
           normalFloat_freeze_k_steps p e m hm β hlo hhi⟩
  · have h1 : (1 : Rat) - (999 / 1000 : Rat) = 1 / 1000 := by grind
    have h2 : (1 / 1000 : Rat) < 1 / 512 := by
      apply rat_lt_of_mul_pos_right (c := (512000 : Rat)) (by decide)
      have ha : (1 / 1000 : Rat) * 512000 = 512 := by grind
      have hb : (1 / 512 : Rat) * 512000 = 1000 := by grind
      rw [ha, hb]; decide
    have h3 : (1 : Rat) - (9999 / 10000 : Rat) = 1 / 10000 := by grind
    have h4 : (1 / 10000 : Rat) < 1 / 512 := by
      apply rat_lt_of_mul_pos_right (c := (5120000 : Rat)) (by decide)
      have ha : (1 / 10000 : Rat) * 5120000 = 512 := by grind
      have hb : (1 / 512 : Rat) * 5120000 = 10000 := by grind
      rw [ha, hb]; decide
    exact ⟨by unfold pow2Int; rfl, h1, h2, h3, h4⟩
  · intro e m hm
    have hbf : pow2Int (-((7 + 2 : Nat) : Int)) = 1 / 512 := by unfold pow2Int; rfl
    have h999_eq : (1 : Rat) - (999 / 1000 : Rat) = 1 / 1000 := by grind
    have h999_lo : (0 : Rat) ≤ 1 - (999 / 1000 : Rat) := by
      rw [h999_eq]; exact rat_div_nonneg (by decide) (by decide)
    have h999_hi : 1 - (999 / 1000 : Rat) ≤ pow2Int (-((7 + 2 : Nat) : Int)) := by
      rw [hbf, h999_eq]
      apply rat_le_of_mul_pos_right (c := (512000 : Rat)) (by decide)
      have ha : (1 / 1000 : Rat) * 512000 = 512 := by grind
      have hb : (1 / 512 : Rat) * 512000 = 1000 := by grind
      rw [ha, hb]; decide
    have h9999_eq : (1 : Rat) - (9999 / 10000 : Rat) = 1 / 10000 := by grind
    have h9999_lo : (0 : Rat) ≤ 1 - (9999 / 10000 : Rat) := by
      rw [h9999_eq]; exact rat_div_nonneg (by decide) (by decide)
    have h9999_hi : 1 - (9999 / 10000 : Rat) ≤ pow2Int (-((7 + 2 : Nat) : Int)) := by
      rw [hbf, h9999_eq]
      apply rat_le_of_mul_pos_right (c := (5120000 : Rat)) (by decide)
      have ha : (1 / 10000 : Rat) * 5120000 = 512 := by grind
      have hb : (1 / 512 : Rat) * 5120000 = 10000 := by grind
      rw [ha, hb]; decide
    have hm' : m < 2 ^ 7 := hm
    exact ⟨normalFloat_freeze_one_step 7 e m hm' (999 / 1000) h999_lo h999_hi,
           normalFloat_freeze_k_steps 7 e m hm' (999 / 1000) h999_lo h999_hi,
           normalFloat_freeze_one_step 7 e m hm' (9999 / 10000) h9999_lo h9999_hi⟩
  · intro p e β hlo hhi
    exact normalFloat_boundary_unfreezes p e β hlo hhi

end EmbedZipfLazyStamp
