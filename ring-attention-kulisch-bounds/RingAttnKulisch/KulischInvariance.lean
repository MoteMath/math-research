/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RingAttnKulisch.RatOrder

/-!
# Theorems 5 & 6: Fixed-Point / Kulisch Reproducibility-Invariance & Sink-Cliff Elimination

Proves:
- **Theorem 5 (`fixed_point_kulisch_topology_partition_invariance`)**:
  Exponent-aligned integer fixed-point accumulation (`fixptSum`) is 100% bit-for-bit
  invariant under:
  1. ALL binary reduction tree topologies (`t.evalInt = fixptSum t.toList`),
  2. ALL Context-Parallel partition degrees `P` (`fixptSum (chunks.map fixptSum) = fixptSum chunks.flatten`),
  3. ALL chunk permutations (`ListPerm xs ys → fixptSum xs = fixptSum ys`), including
     list reversal and arbitrary cyclic ring shifts (`xs.drop r ++ xs.take r`).
  Together with the exact non-overflow two's-complement width theorem
  `W_inv(k, p) = p + 2k + 4` (`|fixptSum xs| < 2^{W_inv(k, p) - 1}` for all `≤ 2^k`
  bounded chunk contributions) and exact `int32` / `int64` Kulisch containment
  (`W_inv(8, p) ∈ {24, 28, 31, 44}`, `W_Kulisch(8, fmt) ∈ {27, 49, 270, 286}`).
- **Theorem 6 (`fixed_point_sink_cliff_elimination`)**:
  Proves that `F ≥ Δ` yields zero per-chunk quantization error (`fixptBulkTerm F Δ = 2^{F - Δ}`)
  and exact rational sum `fixptSinkDenom F Δ k = trueSinkDenom Δ (2^k)`, certifies that
  `F = p + k` strictly avoids bulk-vanishing at `Δ = p + k - 1` (`fixptSinkOut = 1 + 2^{-(p-1)} > 1`),
  proves the exact information-theoretic RNE vanishing ceiling `Δ = p + k`
  (`fixptSinkOut p (p + k) (p + k) k = 1`), and proves the sharp sink-cliff at `F = p + k - 2`
  where `fixptBulkTerm (p + k - 2) (p + k - 1) = 0` drops 100% of bulk before summation.
-/

namespace RingAttnKulisch

/-! ### Exact `fixptSum` Algebraic Laws -/

theorem foldl_add_shift (xs : List Int) (init : Int) :
    xs.foldl (· + ·) init = init + xs.foldl (· + ·) 0 := by
  induction xs generalizing init with
  | nil => simp
  | cons x rest ih =>
    simp only [List.foldl_cons]
    rw [ih (init + x), ih (0 + x)]
    omega

theorem fixptSum_nil : fixptSum [] = 0 := rfl

theorem fixptSum_cons (x : Int) (xs : List Int) :
    fixptSum (x :: xs) = x + fixptSum xs := by
  unfold fixptSum
  simp only [List.foldl_cons]
  rw [foldl_add_shift xs (0 + x)]
  omega

theorem fixptSum_append (xs ys : List Int) :
    fixptSum (xs ++ ys) = fixptSum xs + fixptSum ys := by
  induction xs with
  | nil => simp [fixptSum_nil]
  | cons x rest ih =>
    simp only [List.cons_append, fixptSum_cons, ih]
    omega

theorem binTree_evalInt_eq_fixptSum (t : BinTree Int) :
    t.evalInt = fixptSum t.toList := by
  induction t with
  | leaf a =>
    simp [BinTree.evalInt, BinTree.toList, fixptSum_cons, fixptSum_nil]
  | node l r ihl ihr =>
    simp [BinTree.evalInt, BinTree.toList, fixptSum_append, ihl, ihr]

theorem fixptSum_flatten (chunks : List (List Int)) :
    fixptSum (chunks.map fixptSum) = fixptSum chunks.flatten := by
  induction chunks with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.map_cons, List.flatten_cons, fixptSum_cons, fixptSum_append, ih]

theorem fixptSum_perm {xs ys : List Int} (h : ListPerm xs ys) :
    fixptSum xs = fixptSum ys := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [fixptSum_cons, ih]
  | swap x y l => simp [fixptSum_cons]; omega
  | trans _ _ ih1 ih2 => exact Eq.trans ih1 ih2

theorem fixptSum_reverse (xs : List Int) :
    fixptSum xs.reverse = fixptSum xs := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.reverse_cons, fixptSum_append, fixptSum_cons, fixptSum_nil, ih]
    omega

theorem fixptSum_cyclicShift (xs : List Int) (r : Nat) :
    fixptSum (xs.drop r ++ xs.take r) = fixptSum xs := by
  rw [fixptSum_append, Int.add_comm, ← fixptSum_append, List.take_append_drop]

/-! ### Exact Non-Overflow Width Theorem for `W_inv(k, p)` -/

theorem fixptSum_abs_bound {B : Int} (hB : 0 ≤ B) :
    ∀ xs : List Int, (∀ x, x ∈ xs → -B ≤ x ∧ x ≤ B) →
      -(xs.length : Int) * B ≤ fixptSum xs ∧ fixptSum xs ≤ (xs.length : Int) * B
  | [], _ => by simp [fixptSum_nil]
  | x :: rest, h => by
      have hx := h x (List.mem_cons_self ..)
      have hrest := fixptSum_abs_bound hB rest (fun y hy => h y (List.mem_cons_of_mem x hy))
      rw [fixptSum_cons]
      simp only [List.length_cons]
      have hlen : (((rest.length + 1 : Nat) : Int)) * B = (rest.length : Int) * B + B := by
        rw [Int.natCast_add, Int.add_mul]; omega
      have hneg : -(((rest.length + 1 : Nat) : Int)) * B = -(rest.length : Int) * B - B := by
        have : -(((rest.length + 1 : Nat) : Int)) * B = -((((rest.length + 1 : Nat) : Int)) * B) :=
          Int.neg_mul _ _
        rw [this, hlen]
        have h2 : -(rest.length : Int) * B = -((rest.length : Int) * B) := Int.neg_mul _ _
        omega
      omega

theorem wInvBits_eq (k p : Nat) : wInvBits k p = p + 2 * k + 4 := by
  unfold wInvBits
  omega

theorem fixptSum_no_overflow (k p : Nat) (xs : List Int)
    (hlen : xs.length ≤ 2 ^ k)
    (hbound : ∀ x, x ∈ xs →
      -((2 ^ (p + k + 3) : Nat) : Int) + 1 ≤ x ∧ x ≤ ((2 ^ (p + k + 3) : Nat) : Int) - 1) :
    -((2 ^ (wInvBits k p - 1) : Nat) : Int) < fixptSum xs ∧
    fixptSum xs < ((2 ^ (wInvBits k p - 1) : Nat) : Int) := by
  let B : Int := ((2 ^ (p + k + 3) : Nat) : Int) - 1
  have hB_pos : 0 ≤ B := by
    have : 1 ≤ 2 ^ (p + k + 3) := pow2_pos_nat (p + k + 3)
    omega
  have hsum := fixptSum_abs_bound hB_pos xs (fun x hx => by
    have := hbound x hx
    constructor <;> omega)
  have hlen_int : (xs.length : Int) ≤ ((2 ^ k : Nat) : Int) := by omega
  have hmul : (xs.length : Int) * B ≤ ((2 ^ k : Nat) : Int) * B :=
    Int.mul_le_mul_of_nonneg_right hlen_int hB_pos
  have hexp : wInvBits k p - 1 = k + (p + k + 3) := by
    rw [wInvBits_eq]; omega
  have hpow : ((2 ^ (wInvBits k p - 1) : Nat) : Int) =
      ((2 ^ k : Nat) : Int) * ((2 ^ (p + k + 3) : Nat) : Int) := by
    rw [hexp, Nat.pow_add, Int.natCast_mul]
  have h2k_pos : (0 : Int) < ((2 ^ k : Nat) : Int) := by
    have := pow2_pos_nat k; omega
  have hstrict : ((2 ^ k : Nat) : Int) * B < ((2 ^ (wInvBits k p - 1) : Nat) : Int) := by
    rw [hpow]
    have hB_def : B = ((2 ^ (p + k + 3) : Nat) : Int) - 1 := rfl
    rw [hB_def, Int.mul_sub, Int.mul_one]
    omega
  have hneg_le : -((2 ^ k : Nat) : Int) * B ≤ -(xs.length : Int) * B := by
    have h1 : -((2 ^ k : Nat) : Int) * B = -(((2 ^ k : Nat) : Int) * B) := Int.neg_mul _ _
    have h2 : -(xs.length : Int) * B = -((xs.length : Int) * B) := Int.neg_mul _ _
    omega
  have hneg_eq : -((2 ^ k : Nat) : Int) * B = -(((2 ^ k : Nat) : Int) * B) := Int.neg_mul _ _
  constructor <;> omega

/-- Headline Theorem 5: Bit-for-bit permutation, tree-topology, and Context-Parallel
    partition invariance of exponent-aligned fixed-point/Kulisch accumulation, exact
    non-overflow width `W_inv(k, p) = p + 2k + 4`, and exact `int32`/`int64` containment. -/
theorem fixed_point_kulisch_topology_partition_invariance :
    (∀ t : BinTree Int, t.evalInt = fixptSum t.toList) ∧
    (∀ chunks : List (List Int), fixptSum (chunks.map fixptSum) = fixptSum chunks.flatten) ∧
    (∀ xs ys : List Int, ListPerm xs ys → fixptSum xs = fixptSum ys) ∧
    (∀ xs : List Int, fixptSum xs.reverse = fixptSum xs) ∧
    (∀ (xs : List Int) (r : Nat), fixptSum (xs.drop r ++ xs.take r) = fixptSum xs) ∧
    (∀ (k p : Nat), wInvBits k p = p + 2 * k + 4) ∧
    (∀ (k p : Nat) (xs : List Int), xs.length ≤ 2 ^ k →
      (∀ x, x ∈ xs →
        -((2 ^ (p + k + 3) : Nat) : Int) + 1 ≤ x ∧
        x ≤ ((2 ^ (p + k + 3) : Nat) : Int) - 1) →
      -((2 ^ (wInvBits k p - 1) : Nat) : Int) < fixptSum xs ∧
      fixptSum xs < ((2 ^ (wInvBits k p - 1) : Nat) : Int)) ∧
    ((wInvBits 8 4 = 24 ∧ wInvBits 8 8 = 28 ∧ wInvBits 8 11 = 31 ∧ wInvBits 8 24 = 44) ∧
     (wKulischBits 8 8 (-6) 3 = 27 ∧ wKulischBits 8 15 (-14) 10 = 49 ∧
      wKulischBits 8 127 (-126) 7 = 270 ∧ wKulischBits 8 127 (-126) 23 = 286)) := by
  refine ⟨binTree_evalInt_eq_fixptSum, fixptSum_flatten, fun _ _ h => fixptSum_perm h,
    fixptSum_reverse, fixptSum_cyclicShift, wInvBits_eq,
    fun k p xs hlen hb => fixptSum_no_overflow k p xs hlen hb,
    ⟨⟨rfl, rfl, rfl, rfl⟩, ⟨by decide, by decide, by decide, by decide⟩⟩⟩

/-! ### Theorem 6: Fixed-Point Sink-Cliff Elimination (`F = p + log_2 P`) -/

theorem fixptBulkTerm_exact_of_le {F Δ : Nat} (h : Δ ≤ F) :
    fixptBulkTerm F Δ = ((2 ^ (F - Δ) : Nat) : Int) := by
  unfold fixptBulkTerm
  rw [invPow2Rat_mul_pow2Rat_of_le h]
  have hcast : pow2Rat (F - Δ) = (((2 ^ (F - Δ) : Nat) : Int) : Rat) := rfl
  rw [hcast, rneInt_int]

theorem fixptBulkTerm_zero_at_succ (F : Nat) :
    fixptBulkTerm F (F + 1) = 0 := by
  unfold fixptBulkTerm
  rw [invPow2Rat_mul_pow2Rat_of_ge (by omega)]
  have hsub : F + 1 - F = 1 := by omega
  rw [hsub]
  apply rneInt_of_eq_half_even (n := 0)
  · unfold invPow2Rat
    have h2 : ((2 ^ 1 : Nat) : Rat) = 2 := by decide
    rw [h2]; grind
  · decide

theorem fixptSinkDenom_exact_of_le {F Δ k : Nat} (h : Δ ≤ F) :
    fixptSinkDenom F Δ k = trueSinkDenom Δ (2 ^ k) := by
  unfold fixptSinkDenom fixptSinkIntSum trueSinkDenom
  rw [fixptBulkTerm_exact_of_le h]
  rw [Rat.intCast_add, Rat.intCast_mul, Rat.add_mul]
  have h1 : (((2 ^ F : Nat) : Int) : Rat) * invPow2Rat F = 1 := by
    have : (((2 ^ F : Nat) : Int) : Rat) = pow2Rat F := rfl
    rw [this, pow2Rat_mul_invPow2Rat]
  have h2 : (((2 ^ (F - Δ) : Nat) : Int) : Rat) * invPow2Rat F = invPow2Rat Δ := by
    have : (((2 ^ (F - Δ) : Nat) : Int) : Rat) = pow2Rat (F - Δ) := rfl
    rw [this, pow2Rat_mul_invPow2Rat_of_le (by omega)]
    have hsub : F - (F - Δ) = Δ := by omega
    rw [hsub]
  rw [h1, Rat.mul_assoc, h2]
  rfl

theorem fixptSinkOut_survives_at_crit {p F k : Nat} (hp : 2 ≤ p) (hk : 2 ≤ k)
    (hF : p + k - 1 ≤ F) :
    fixptSinkOut p F (p + k - 1) k = 1 + invPow2Rat (p - 1) := by
  unfold fixptSinkOut
  rw [fixptSinkDenom_exact_of_le hF]
  unfold trueSinkDenom rneGrid
  have hmul : (1 + ((2 ^ k - 1 : Nat) : Rat) * invPow2Rat (p + k - 1)) * pow2Rat (p - 1) =
      pow2Rat (p - 1) + ((2 ^ k - 1 : Nat) : Rat) * invPow2Rat k := by
    rw [Rat.add_mul, Rat.one_mul, Rat.mul_assoc, invPow2Rat_mul_pow2Rat_of_ge (by omega)]
    have hsub : p + k - 1 - (p - 1) = k := by omega
    rw [hsub]
  rw [hmul]
  have hfrac : ((2 ^ k - 1 : Nat) : Rat) * invPow2Rat k = 1 - invPow2Rat k := by
    have hcast : ((2 ^ k - 1 : Nat) : Rat) = pow2Rat k - 1 := by
      have hpos : 1 ≤ 2 ^ k := pow2_pos_nat k
      unfold pow2Rat
      have hnat : 2 ^ k = (2 ^ k - 1) + 1 := by omega
      have hrat : ((2 ^ k : Nat) : Rat) = ((2 ^ k - 1 : Nat) : Rat) + 1 := by
        have : ((2 ^ k : Nat) : Rat) = (((2 ^ k - 1) + 1 : Nat) : Rat) :=
          congrArg (fun n : Nat => (n : Rat)) hnat
        rw [this, Rat.natCast_add]; rfl
      grind
    have hsub_mul : (pow2Rat k - 1) * invPow2Rat k = pow2Rat k * invPow2Rat k - 1 * invPow2Rat k := by grind
    rw [hcast, hsub_mul, pow2Rat_mul_invPow2Rat, Rat.one_mul]
  rw [hfrac]
  have hrne : rneInt (pow2Rat (p - 1) + (1 - invPow2Rat k)) = ((2 ^ (p - 1) : Nat) : Int) + 1 := by
    apply rneInt_of_gt_half (n := ((2 ^ (p - 1) : Nat) : Int))
    · have hinv : invPow2Rat k < invPow2Rat 1 := invPow2Rat_lt_invPow2Rat (by omega)
      have hhalf : invPow2Rat 1 = 1 / 2 := by unfold invPow2Rat; grind
      rw [hhalf] at hinv
      have hsub : (1 / 2 : Rat) < 1 - invPow2Rat k := by
        apply rat_lt_of_sub_pos
        have eq : (1 - invPow2Rat k) - 1 / 2 = 1 / 2 - invPow2Rat k := by grind
        rw [eq]; exact rat_sub_pos hinv
      exact rat_add_lt_add_left hsub
    · have hpos : (0 : Rat) < invPow2Rat k := invPow2Rat_pos k
      have hlt : 1 - invPow2Rat k < 1 := by
        apply rat_lt_of_sub_pos
        have eq : 1 - (1 - invPow2Rat k) = invPow2Rat k := by grind
        rw [eq]; exact hpos
      have hadd := rat_add_lt_add_left (c := pow2Rat (p - 1)) hlt
      have hcast : ((((2 ^ (p - 1) : Nat) : Int) + 1 : Int) : Rat) = pow2Rat (p - 1) + 1 := by
        rw [Rat.intCast_add]; rfl
      rw [hcast]; exact hadd
  rw [hrne]
  have hcast : ((((2 ^ (p - 1) : Nat) : Int) + 1 : Int) : Rat) = pow2Rat (p - 1) + 1 := by
    rw [Rat.intCast_add]; rfl
  rw [hcast, Rat.add_mul, pow2Rat_mul_invPow2Rat, Rat.one_mul]

theorem fixptSinkOut_vanishes_at_ceil {p F k : Nat} (hp : 2 ≤ p) (hk : 1 ≤ k)
    (hF : p + k ≤ F) :
    fixptSinkOut p F (p + k) k = 1 := by
  unfold fixptSinkOut
  rw [fixptSinkDenom_exact_of_le hF]
  unfold trueSinkDenom rneGrid
  have hmul : (1 + ((2 ^ k - 1 : Nat) : Rat) * invPow2Rat (p + k)) * pow2Rat (p - 1) =
      pow2Rat (p - 1) + ((2 ^ k - 1 : Nat) : Rat) * invPow2Rat (k + 1) := by
    rw [Rat.add_mul, Rat.one_mul, Rat.mul_assoc, invPow2Rat_mul_pow2Rat_of_ge (by omega)]
    have hsub : p + k - (p - 1) = k + 1 := by omega
    rw [hsub]
  rw [hmul]
  have hrne : rneInt (pow2Rat (p - 1) + ((2 ^ k - 1 : Nat) : Rat) * invPow2Rat (k + 1)) =
      ((2 ^ (p - 1) : Nat) : Int) := by
    apply rneInt_of_lt_half
    · have hnn : (0 : Rat) ≤ ((2 ^ k - 1 : Nat) : Rat) * invPow2Rat (k + 1) :=
        Rat.mul_nonneg (rat_natCast_le (Nat.zero_le _)) (Rat.le_of_lt (invPow2Rat_pos _))
      have hle := rat_add_le_add (Rat.le_refl (a := pow2Rat (p - 1))) hnn
      have h0 : pow2Rat (p - 1) + 0 = pow2Rat (p - 1) := by grind
      rw [h0] at hle; exact hle
    · have hlt_nat : 2 ^ k - 1 < 2 ^ k := by
        have := pow2_pos_nat k; omega
      have hlt_rat : ((2 ^ k - 1 : Nat) : Rat) < pow2Rat k := rat_natCast_lt hlt_nat
      have hmul_lt : ((2 ^ k - 1 : Nat) : Rat) * invPow2Rat (k + 1) <
          pow2Rat k * invPow2Rat (k + 1) :=
        rat_mul_lt_mul_of_pos_right hlt_rat (invPow2Rat_pos (k + 1))
      rw [pow2Rat_mul_invPow2Rat_of_le (by omega)] at hmul_lt
      have hsub : k + 1 - k = 1 := by omega
      rw [hsub] at hmul_lt
      have hhalf : invPow2Rat 1 = 1 / 2 := by unfold invPow2Rat; grind
      rw [hhalf] at hmul_lt
      exact rat_add_lt_add_left hmul_lt
  rw [hrne]
  have hcast : (((2 ^ (p - 1) : Nat) : Int) : Rat) = pow2Rat (p - 1) := rfl
  rw [hcast, pow2Rat_mul_invPow2Rat]

theorem fixptSinkDenom_cliff_vanishes {p k : Nat} (hp : 2 ≤ p) (hk : 1 ≤ k) :
    fixptBulkTerm (p + k - 2) (p + k - 1) = 0 ∧
    fixptSinkDenom (p + k - 2) (p + k - 1) k = 1 := by
  have heq : p + k - 1 = (p + k - 2) + 1 := by omega
  have hbulk : fixptBulkTerm (p + k - 2) (p + k - 1) = 0 := by
    rw [heq]; exact fixptBulkTerm_zero_at_succ (p + k - 2)
  refine ⟨hbulk, ?_⟩
  unfold fixptSinkDenom fixptSinkIntSum
  rw [hbulk]
  have h0 : ((2 ^ (p + k - 2) : Nat) : Int) + ((2 ^ k - 1 : Nat) : Int) * 0 =
      ((2 ^ (p + k - 2) : Nat) : Int) := by omega
  rw [h0]
  have hcast : (((2 ^ (p + k - 2) : Nat) : Int) : Rat) = pow2Rat (p + k - 2) := rfl
  rw [hcast, pow2Rat_mul_invPow2Rat]

/-- Headline Theorem 6: Fixed-point sink-cliff elimination at `F = p + log_2 P`.
    Certifies zero bulk loss for all `Δ ≤ F`, strict bulk survival at `Δ = p + k - 1`
    for `F = p + k` (strictly beating balanced `TREE`, which vanishes at `p + k - 1`),
    exact information-theoretic RNE ceiling `Δ_vanish^FIXPT = p + k`, and the sharp
    sink-cliff at `F = p + k - 2` where all `2^k - 1` bulk chunks vanish before summation. -/
theorem fixed_point_sink_cliff_elimination :
    (∀ (F Δ k : Nat), Δ ≤ F →
      fixptBulkTerm F Δ = ((2 ^ (F - Δ) : Nat) : Int) ∧
      fixptSinkDenom F Δ k = trueSinkDenom Δ (2 ^ k)) ∧
    (∀ (p k : Nat), 2 ≤ p → 2 ≤ k →
      fixptSinkDenom (p + k) (p + k - 1) k = trueSinkDenom (p + k - 1) (2 ^ k) ∧
      fixptSinkOut p (p + k) (p + k - 1) k = 1 + invPow2Rat (p - 1) ∧
      (1 : Rat) < fixptSinkOut p (p + k) (p + k - 1) k) ∧
    (∀ (p k : Nat), 2 ≤ p → 1 ≤ k →
      fixptSinkOut p (p + k) (p + k) k = 1) ∧
    (∀ (p k : Nat), 2 ≤ p → 1 ≤ k →
      fixptBulkTerm (p + k - 2) (p + k - 1) = 0 ∧
      fixptSinkDenom (p + k - 2) (p + k - 1) k = 1) := by
  refine ⟨fun F Δ k h => ⟨fixptBulkTerm_exact_of_le h, fixptSinkDenom_exact_of_le h⟩,
    fun p k hp hk => ⟨fixptSinkDenom_exact_of_le (by omega),
      fixptSinkOut_survives_at_crit hp hk (by omega), by
        rw [fixptSinkOut_survives_at_crit hp hk (by omega)]
        have h := rat_add_lt_add_left (c := (1 : Rat)) (invPow2Rat_pos (p - 1))
        have h0 : (1 : Rat) + 0 = 1 := by grind
        rw [h0] at h; exact h⟩,
    fun p k hp hk => fixptSinkOut_vanishes_at_ceil hp hk (Nat.le_refl _),
    fun p k hp hk => fixptSinkDenom_cliff_vanishes hp hk⟩

end RingAttnKulisch
