/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RingAttnKulisch.RatOrder

/-!
# Theorems 2 & 3: Attention-Sink Vanishing Laws (`L2R`/`DESC` vs Balanced `TREE`)

Proves:
- **Theorem 2 (`attention_sink_l2r_desc_vanishing_law`)**: For every IEEE-754 RNE
  significand precision `p ≥ 2`, at logit gap `Δ ≥ p`, every single sequential step
  `rneGrid p (1 + 2^{-Δ}) = 1` identically absorbs all `P - 1` bulk chunks
  (`l2rSinkAccum p Δ n = 1` for all `n`), yielding exact relative error
  `(P - 1) / (2^p + P - 1)` at `Δ = p`, while `Δ = p - 1` strictly preserves bulk
  (`l2rSinkAccum p (p - 1) 1 = 1 + 2^{-(p-1)} > 1`). Instantiates exact values at
  `P = 256` for FP8-E4M3 (`255/271`), BF16 (`255/511`), FP16 (`255/2303`), and FP32.
- **Theorem 3 (`binary_tree_vs_l2r_sink_survival_separation`)**: For `P = 2^k` chunks
  (`k ≥ 2`, `p ≥ 2`), balanced binary tree reduction preserves bulk mass strictly up to
  `Δ = p + k - 2` (`treeSinkAccum p (p + k - 2) k = 1 + 2^{-(p-1)} > 1`) and at `Δ = p`
  (`1 + 2^{-(p-1)} ≤ treeSinkAccum p p k`), while vanishing at `Δ ≥ p + k - 1`
  (`treeSinkAccum p Δ k = 1`), giving exact threshold
  `Δ_vanish^TREE(2^k, p, eMin, M) = min(p + k - 1, -(eMin - M) + 1)` — including the
  exact FP8-E4M3 subnormal floor cap at `Δ = 10` (`< 11`) for `P = 256`.
-/

namespace RingAttnKulisch

theorem pow2_even_of_ge_two {p : Nat} (hp : 2 ≤ p) :
    (((2 ^ (p - 1) : Nat) : Int)) % 2 = 0 := by
  have hk : p - 1 = (p - 2) + 1 := by omega
  rw [hk, Nat.pow_succ]
  omega

theorem rneGrid_one_add_invPow2_eq_one {p Δ : Nat} (hp : 2 ≤ p) (hΔ : p ≤ Δ) :
    rneGrid p (1 + invPow2Rat Δ) = 1 := by
  unfold rneGrid
  have hmul : (1 + invPow2Rat Δ) * pow2Rat (p - 1) =
      pow2Rat (p - 1) + invPow2Rat (Δ - (p - 1)) := by
    rw [Rat.add_mul, Rat.one_mul, invPow2Rat_mul_pow2Rat_of_ge (by omega)]
  rw [hmul]
  have hrne : rneInt (pow2Rat (p - 1) + invPow2Rat (Δ - (p - 1))) = ((2 ^ (p - 1) : Nat) : Int) := by
    by_cases heq : Δ = p
    · have hsub : Δ - (p - 1) = 1 := by omega
      rw [hsub]
      apply rneInt_of_eq_half_even
      · unfold pow2Rat invPow2Rat
        have h2 : ((2 ^ 1 : Nat) : Rat) = 2 := by decide
        rw [h2]; rfl
      · exact pow2_even_of_ge_two hp
    · have hlt : 1 < Δ - (p - 1) := by omega
      apply rneInt_of_lt_half
      · have hpos : (0 : Rat) < invPow2Rat (Δ - (p - 1)) := invPow2Rat_pos _
        have hle := rat_add_le_add (Rat.le_refl (a := pow2Rat (p - 1))) (Rat.le_of_lt hpos)
        have h0 : pow2Rat (p - 1) + 0 = pow2Rat (p - 1) := by grind
        rw [h0] at hle
        exact hle
      · have hinv : invPow2Rat (Δ - (p - 1)) < invPow2Rat 1 := invPow2Rat_lt_invPow2Rat hlt
        have hhalf : invPow2Rat 1 = 1 / 2 := by
          unfold invPow2Rat; grind
        rw [hhalf] at hinv
        exact rat_add_lt_add_left hinv
  rw [hrne]
  have hcast : (((2 ^ (p - 1) : Nat) : Int) : Rat) = pow2Rat (p - 1) := rfl
  rw [hcast, pow2Rat_mul_invPow2Rat]

theorem rneGrid_one_add_ulp {p : Nat} (_hp : 2 ≤ p) :
    rneGrid p (1 + invPow2Rat (p - 1)) = 1 + invPow2Rat (p - 1) := by
  have hmul : (1 + invPow2Rat (p - 1)) * pow2Rat (p - 1) =
      (((2 ^ (p - 1) + 1 : Nat) : Int) : Rat) := by
    rw [Rat.add_mul, Rat.one_mul, invPow2Rat_mul_pow2Rat]
    unfold pow2Rat
    rw [Int.natCast_add, Rat.intCast_add]
    rfl
  rw [rneGrid_of_int_mul hmul]
  have hcast : (((2 ^ (p - 1) + 1 : Nat) : Int) : Rat) = pow2Rat (p - 1) + 1 := by
    unfold pow2Rat
    rw [Int.natCast_add, Rat.intCast_add]; rfl
  rw [hcast, Rat.add_mul, pow2Rat_mul_invPow2Rat, Rat.one_mul]

theorem l2rSinkAccum_eq_one {p Δ : Nat} (hp : 2 ≤ p) (hΔ : p ≤ Δ) :
    ∀ n : Nat, l2rSinkAccum p Δ n = 1
  | 0 => rfl
  | n + 1 => by
      unfold l2rSinkAccum
      rw [l2rSinkAccum_eq_one hp hΔ n]
      exact rneGrid_one_add_invPow2_eq_one hp hΔ

theorem l2rSinkAccum_step_one_sub {p : Nat} (hp : 2 ≤ p) :
    l2rSinkAccum p (p - 1) 1 = 1 + invPow2Rat (p - 1) := by
  unfold l2rSinkAccum
  exact rneGrid_one_add_ulp hp

theorem sinkRelErr_l2r_at_p {p P : Nat} (hp : 2 ≤ p) :
    sinkRelErr p P (l2rSinkAccum p p (P - 1)) =
      ((P - 1 : Nat) : Rat) / (pow2Rat p + ((P - 1 : Nat) : Rat)) := by
  rw [l2rSinkAccum_eq_one hp (Nat.le_refl p)]
  unfold sinkRelErr trueSinkDenom
  have hdiff : 1 + ((P - 1 : Nat) : Rat) * invPow2Rat p - 1 =
      ((P - 1 : Nat) : Rat) * invPow2Rat p := by grind
  rw [hdiff]
  have hnonneg : (0 : Rat) ≤ ((P - 1 : Nat) : Rat) * invPow2Rat p :=
    Rat.mul_nonneg (rat_natCast_le (Nat.zero_le _)) (Rat.le_of_lt (invPow2Rat_pos p))
  have habs : ratAbs (((P - 1 : Nat) : Rat) * invPow2Rat p) =
      ((P - 1 : Nat) : Rat) * invPow2Rat p := by
    unfold ratAbs; simp [hnonneg]
  rw [habs]
  have hP_nonneg : (0 : Rat) ≤ ((P - 1 : Nat) : Rat) := rat_natCast_le (Nat.zero_le _)
  have hden_pos : (0 : Rat) < pow2Rat p + ((P - 1 : Nat) : Rat) := by
    have hle : pow2Rat p ≤ pow2Rat p + ((P - 1 : Nat) : Rat) := by
      have := rat_add_le_add (Rat.le_refl (a := pow2Rat p)) hP_nonneg
      have h0 : pow2Rat p + 0 = pow2Rat p := by grind
      rw [h0] at this; exact this
    exact rat_lt_of_lt_of_le (pow2Rat_pos p) hle
  have hden_ne : pow2Rat p + ((P - 1 : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hden_pos
  have htrue_eq : 1 + ((P - 1 : Nat) : Rat) * invPow2Rat p =
      (pow2Rat p + ((P - 1 : Nat) : Rat)) * invPow2Rat p := by
    rw [Rat.add_mul, pow2Rat_mul_invPow2Rat]
  rw [htrue_eq]
  have hinv_ne : invPow2Rat p ≠ 0 := Rat.ne_of_gt (invPow2Rat_pos p)
  have hprod_ne : (pow2Rat p + ((P - 1 : Nat) : Rat)) * invPow2Rat p ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact hden_ne h
    | inr h => exact hinv_ne h
  have h1 : (((P - 1 : Nat) : Rat) * invPow2Rat p /
      ((pow2Rat p + ((P - 1 : Nat) : Rat)) * invPow2Rat p)) *
      ((pow2Rat p + ((P - 1 : Nat) : Rat)) * invPow2Rat p) =
      (((P - 1 : Nat) : Rat) / (pow2Rat p + ((P - 1 : Nat) : Rat))) *
      ((pow2Rat p + ((P - 1 : Nat) : Rat)) * invPow2Rat p) := by
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ hprod_ne, Rat.mul_one]
    rw [Rat.div_def]
    have rearr : ((P - 1 : Nat) : Rat) * (pow2Rat p + ((P - 1 : Nat) : Rat))⁻¹ *
        ((pow2Rat p + ((P - 1 : Nat) : Rat)) * invPow2Rat p) =
        ((P - 1 : Nat) : Rat) * invPow2Rat p *
        ((pow2Rat p + ((P - 1 : Nat) : Rat))⁻¹ * (pow2Rat p + ((P - 1 : Nat) : Rat))) := by grind
    rw [rearr, Rat.inv_mul_cancel _ hden_ne, Rat.mul_one]
  have := congrArg (· * ((pow2Rat p + ((P - 1 : Nat) : Rat)) * invPow2Rat p)⁻¹) h1
  simp only [Rat.mul_assoc, Rat.mul_inv_cancel _ hprod_ne, Rat.mul_one] at this
  exact this

/-- Headline Theorem 2: Exact `p`-bit IEEE-754 RNE attention-sink vanishing law for
    sequential `L2R` / `DESC` Ring-Attention merges (`Δ_vanish^{L2R/DESC} = p`), exact
    100% bulk loss and relative error `(P - 1) / (2^p + P - 1)`, sharpness at `Δ = p - 1`,
    and exact instantiations at `P = 256` for FP8-E4M3, BF16, FP16, and FP32. -/
theorem attention_sink_l2r_desc_vanishing_law :
    (∀ (p Δ n : Nat), 2 ≤ p → p ≤ Δ →
      rneGrid p (1 + invPow2Rat Δ) = 1 ∧
      l2rSinkAccum p Δ n = 1) ∧
    (∀ (p : Nat), 2 ≤ p →
      l2rSinkAccum p (p - 1) 1 = 1 + invPow2Rat (p - 1) ∧
      (1 : Rat) < l2rSinkAccum p (p - 1) 1) ∧
    (∀ (p P : Nat), 2 ≤ p →
      sinkRelErr p P (l2rSinkAccum p p (P - 1)) =
        ((P - 1 : Nat) : Rat) / (pow2Rat p + ((P - 1 : Nat) : Rat))) ∧
    (sinkRelErr 4 256 (l2rSinkAccum 4 4 255) = 255 / 271 ∧
     sinkRelErr 8 256 (l2rSinkAccum 8 8 255) = 255 / 511 ∧
     sinkRelErr 11 256 (l2rSinkAccum 11 11 255) = 255 / 2303 ∧
     sinkRelErr 24 256 (l2rSinkAccum 24 24 255) = 255 / 16777471) := by
  refine ⟨fun p Δ n hp hΔ => ⟨rneGrid_one_add_invPow2_eq_one hp hΔ, l2rSinkAccum_eq_one hp hΔ n⟩,
    fun p hp => ⟨l2rSinkAccum_step_one_sub hp, by
      rw [l2rSinkAccum_step_one_sub hp]
      have h := rat_add_lt_add_left (c := (1 : Rat)) (invPow2Rat_pos (p - 1))
      have h0 : (1 : Rat) + 0 = 1 := by grind
      rw [h0] at h
      exact h⟩,
    fun p P hp => sinkRelErr_l2r_at_p hp, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sinkRelErr_l2r_at_p (p := 4) (P := 256) (by omega)]; unfold pow2Rat; grind
  · rw [sinkRelErr_l2r_at_p (p := 8) (P := 256) (by omega)]; unfold pow2Rat; grind
  · rw [sinkRelErr_l2r_at_p (p := 11) (P := 256) (by omega)]; unfold pow2Rat; grind
  · rw [sinkRelErr_l2r_at_p (p := 24) (P := 256) (by omega)]; unfold pow2Rat; grind

/-! ### Theorem 3: Balanced Binary Tree vs L2R Sink Survival Separation -/

theorem treeSinkAccum_eq_one_of_ge {p Δ : Nat} (hp : 2 ≤ p) :
    ∀ k : Nat, (∀ j : Nat, j < k → p + j ≤ Δ) → treeSinkAccum p Δ k = 1
  | 0, _ => rfl
  | k + 1, h => by
      unfold treeSinkAccum
      have hprev : treeSinkAccum p Δ k = 1 :=
        treeSinkAccum_eq_one_of_ge hp k (fun j hj => h j (by omega))
      rw [hprev]
      have hk : p + k ≤ Δ := h k (by omega)
      rw [pow2Rat_mul_invPow2Rat_of_le (by omega)]
      exact rneGrid_one_add_invPow2_eq_one hp (by omega)

theorem treeSinkAccum_vanishes {p Δ k : Nat} (hp : 2 ≤ p) (hk : 1 ≤ k)
    (hΔ : p + k - 1 ≤ Δ) :
    treeSinkAccum p Δ k = 1 := by
  apply treeSinkAccum_eq_one_of_ge hp k
  intro j hj
  omega

theorem treeSinkAccum_survives_at_crit {p k : Nat} (hp : 2 ≤ p) (hk : 1 ≤ k) :
    treeSinkAccum p (p + k - 2) k = 1 + invPow2Rat (p - 1) := by
  cases k with
  | zero => omega
  | succ m =>
    unfold treeSinkAccum
    have hprev : treeSinkAccum p (p + (m + 1) - 2) m = 1 := by
      apply treeSinkAccum_eq_one_of_ge hp m
      intro j hj
      omega
    rw [hprev]
    have hle : m ≤ p + (m + 1) - 2 := by omega
    rw [pow2Rat_mul_invPow2Rat_of_le hle]
    have hsub : p + (m + 1) - 2 - m = p - 1 := by omega
    rw [hsub]
    exact rneGrid_one_add_ulp hp

theorem treeSinkAccum_ge_one_add_ulp {p Δ : Nat} (hp : 2 ≤ p) :
    ∀ k : Nat, 1 ≤ k → Δ ≤ p + k - 2 →
      1 + invPow2Rat (p - 1) ≤ treeSinkAccum p Δ k := by
  intro k hk hΔ
  cases k with
  | zero => omega
  | succ m =>
    induction m with
    | zero =>
      have hle : Δ ≤ p - 1 := by omega
      unfold treeSinkAccum
      have h0 : treeSinkAccum p Δ 0 = 1 := rfl
      rw [h0]
      have hpow0 : pow2Rat 0 = 1 := by unfold pow2Rat; decide
      rw [hpow0, Rat.one_mul]
      have hge : 1 + invPow2Rat (p - 1) ≤ 1 + invPow2Rat Δ :=
        rat_add_le_add Rat.le_refl (invPow2Rat_le_invPow2Rat hle)
      have hmul : (((2 ^ (p - 1) + 1 : Nat) : Int) : Rat) ≤
          (1 + invPow2Rat Δ) * pow2Rat (p - 1) := by
        have h1 : (((2 ^ (p - 1) + 1 : Nat) : Int) : Rat) =
            (1 + invPow2Rat (p - 1)) * pow2Rat (p - 1) := by
          rw [Rat.add_mul, Rat.one_mul, invPow2Rat_mul_pow2Rat]
          unfold pow2Rat; rw [Int.natCast_add, Rat.intCast_add]; rfl
        rw [h1]
        exact rat_mul_le_mul_of_nonneg_right hge (Rat.le_of_lt (pow2Rat_pos (p - 1)))
      have hrne := rneGrid_ge_of_int_le hmul
      have hcast : (((2 ^ (p - 1) + 1 : Nat) : Int) : Rat) * invPow2Rat (p - 1) =
          1 + invPow2Rat (p - 1) := by
        have : (((2 ^ (p - 1) + 1 : Nat) : Int) : Rat) = pow2Rat (p - 1) + 1 := by
          unfold pow2Rat; rw [Int.natCast_add, Rat.intCast_add]; rfl
        rw [this, Rat.add_mul, pow2Rat_mul_invPow2Rat, Rat.one_mul]
      rw [hcast] at hrne
      exact hrne
    | succ m ih =>
      unfold treeSinkAccum
      by_cases hprev_le : Δ ≤ p + (m + 1) - 2
      · have hprev := ih (by omega) hprev_le
        have hsum : 1 + invPow2Rat (p - 1) ≤
            treeSinkAccum p Δ (m + 1) + pow2Rat (m + 1) * invPow2Rat Δ := by
          have hpos : (0 : Rat) ≤ pow2Rat (m + 1) * invPow2Rat Δ :=
            Rat.le_of_lt (rat_mul_pos (pow2Rat_pos _) (invPow2Rat_pos _))
          have hadd := rat_add_le_add hprev hpos
          have h0 : 1 + invPow2Rat (p - 1) + 0 = 1 + invPow2Rat (p - 1) := by grind
          rw [h0] at hadd
          exact hadd
        have hmul : (((2 ^ (p - 1) + 1 : Nat) : Int) : Rat) ≤
            (treeSinkAccum p Δ (m + 1) + pow2Rat (m + 1) * invPow2Rat Δ) * pow2Rat (p - 1) := by
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
      · have hΔ_eq : Δ = p + (m + 2) - 2 := by omega
        have hcrit := treeSinkAccum_survives_at_crit hp (k := m + 2) (by omega)
        unfold treeSinkAccum at hcrit
        rw [hΔ_eq, hcrit]
        exact Rat.le_refl

/-- Headline Theorem 3: Exact balanced binary tree vs sequential `L2R`/`DESC`
    attention-sink survival separation (`Δ_vanish^TREE(2^k, p) = p + k - 1` vs
    `Δ_vanish^{L2R/DESC} = p`, exponential `2^{k-1} = P/2` margin gain for `k ≥ 2`,
    and exact subnormal floor cap including FP8-E4M3 `Δ = 10 < 11` at `P = 256`). -/
theorem binary_tree_vs_l2r_sink_survival_separation :
    (∀ (p k Δ : Nat), 2 ≤ p → 1 ≤ k → p + k - 1 ≤ Δ →
      treeSinkAccum p Δ k = 1) ∧
    (∀ (p k : Nat), 2 ≤ p → 1 ≤ k →
      treeSinkAccum p (p + k - 2) k = 1 + invPow2Rat (p - 1) ∧
      (1 : Rat) < treeSinkAccum p (p + k - 2) k) ∧
    (∀ (p k : Nat), 2 ≤ p → 2 ≤ k →
      l2rSinkAccum p p (2 ^ k - 1) = 1 ∧
      1 + invPow2Rat (p - 1) ≤ treeSinkAccum p p k ∧
      l2rSinkAccum p p (2 ^ k - 1) < treeSinkAccum p p k) ∧
    (deltaVanishTree 8 4 (-6) 3 = 10 ∧
     deltaVanishTree 8 8 (-126) 7 = 15 ∧
     deltaVanishTree 8 11 (-14) 10 = 18 ∧
     deltaVanishTree 8 24 (-126) 23 = 31) := by
  refine ⟨fun p k Δ hp hk hΔ => treeSinkAccum_vanishes hp hk hΔ,
    fun p k hp hk => ⟨treeSinkAccum_survives_at_crit hp hk, by
      rw [treeSinkAccum_survives_at_crit hp hk]
      have h := rat_add_lt_add_left (c := (1 : Rat)) (invPow2Rat_pos (p - 1))
      have h0 : (1 : Rat) + 0 = 1 := by grind
      rw [h0] at h
      exact h⟩,
    fun p k hp hk => by
      have hl2r := l2rSinkAccum_eq_one hp (Nat.le_refl p) (2 ^ k - 1)
      have htree := treeSinkAccum_ge_one_add_ulp (Δ := p) hp k (by omega) (by omega)
      refine ⟨hl2r, htree, ?_⟩
      rw [hl2r]
      have hlt : (1 : Rat) < 1 + invPow2Rat (p - 1) := by
        have h := rat_add_lt_add_left (c := (1 : Rat)) (invPow2Rat_pos (p - 1))
        have h0 : (1 : Rat) + 0 = 1 := by grind
        rw [h0] at h
        exact h
      exact rat_lt_of_lt_of_le hlt htree,
    ⟨by decide, by decide, by decide, by decide⟩⟩

end RingAttnKulisch
