/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RmsnormHybridLinfL1.RatOrder

/-!
# Exact `L∞ + L1` Hybrid Norm Envelopes, Minimax `d^(1/4)` Law, and Llama-3 Dyadic Witnesses

Proves Theorems 1, 2, and 3 in pure `Init` (zero Mathlib, zero `native_decide`).
-/

namespace RmsnormHybridLinfL1

/-! ## Helper evaluations for extremal vectors -/

/-- `finSum` of a function that equals `a` at index `0` and `b` at all indices `i ≥ 1`. -/
theorem finSum_spike_uniform (d : Nat) (hd : 1 ≤ d) (a b : Rat) :
    finSum d (fun i => if i.val = 0 then a else b) = a + ((d - 1 : Nat) : Rat) * b := by
  induction d with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      simp only [finSum]
      have h0 : ((0 : Nat) : Rat) = 0 := rfl
      simp [h0]
      grind
    | succ m =>
      have hstep : finSum (m + 1 + 1) (fun i => if i.val = 0 then a else b) =
          finSum (m + 1) (fun i => if i.castSucc.val = 0 then a else b) +
            (if (⟨m + 1, Nat.lt_succ_self (m + 1)⟩ : Fin (m + 1 + 1)).val = 0 then a else b) := rfl
      rw [hstep]
      have hih := ih (Nat.succ_pos m)
      have hcast : finSum (m + 1) (fun i : Fin (m + 1) => if i.castSucc.val = 0 then a else b) =
          finSum (m + 1) (fun i : Fin (m + 1) => if i.val = 0 then a else b) := by
        apply finSum_congr; intro i; rfl
      rw [hcast, hih]
      have hne : ¬ (m + 1 = 0) := by omega
      simp only [hne, ite_false]
      have hnat : ((m + 1 : Nat) : Rat) = ((m : Nat) : Rat) + 1 := by
        rw [Rat.natCast_add]; rfl
      have hsub1 : m + 1 - 1 = m := by omega
      have hsub2 : m + 1 + 1 - 1 = m + 1 := by omega
      rw [hsub1, hsub2, hnat]
      grind

/-- `linfNorm` of `upperExtremalVec d α β` is `1` whenever `d ≥ 1`, `α > 0`, `β > 0`. -/
theorem linfNorm_upperExtremalVec (d : Nat) (hd : 1 ≤ d) (α β : Rat)
    (hα : (0 : Rat) < α) (hβ : (0 : Rat) < β) :
    linfNorm (upperExtremalVec d α β) = 1 := by
  have hdpos : (0 : Rat) < (d : Rat) := rat_natCast_pos hd
  have hdenpos : (0 : Rat) < α * (d : Rat) + β :=
    rat_add_pos (rat_mul_pos hα hdpos) hβ
  have htpos : (0 : Rat) < β / (α * (d : Rat) + β) := rat_div_pos hβ hdenpos
  have htle1 : β / (α * (d : Rat) + β) ≤ 1 := by
    apply rat_div_le_of_mul_le hdenpos
    have hαd : (0 : Rat) < α * (d : Rat) := rat_mul_pos hα hdpos
    have h1 : (0 : Rat) ≤ α * (d : Rat) := Rat.le_of_lt hαd
    have h2 : β ≤ 1 * (α * (d : Rat) + β) := by
      have := rat_add_le_add h1 (Rat.le_refl (a := β))
      grind
    exact h2
  have hle : linfNorm (upperExtremalVec d α β) ≤ 1 := by
    obtain ⟨i, hi⟩ := exists_eq_linfNorm hd (upperExtremalVec d α β)
    rw [← hi]
    unfold upperExtremalVec
    split
    · rw [ratAbs_of_nonneg (by decide)]; exact Rat.le_refl
    · rw [ratAbs_of_nonneg (Rat.le_of_lt htpos)]; exact htle1
  have hge : (1 : Rat) ≤ linfNorm (upperExtremalVec d α β) := by
    have h0 := ratAbs_le_linfNorm (upperExtremalVec d α β) ⟨0, hd⟩
    have hv : upperExtremalVec d α β ⟨0, hd⟩ = 1 := by simp [upperExtremalVec]
    rw [hv, ratAbs_of_nonneg (by decide)] at h0
    exact h0
  exact Rat.le_antisymm hle hge

/-- `finSum` of `kSparseVec d k` (and its square/abs) is `k` whenever `k ≤ d`. -/
theorem finSum_kSparseVec (d : Nat) : ∀ (k : Nat), k ≤ d →
    finSum d (kSparseVec d k) = (k : Rat) := by
  induction d with
  | zero =>
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    rfl
  | succ n ih =>
    intro k hk
    simp only [finSum]
    by_cases hkn : k ≤ n
    · have hcongr : finSum n (fun i : Fin n => kSparseVec (n + 1) k i.castSucc) =
          finSum n (kSparseVec n k) := by
        apply finSum_congr; intro i; rfl
      rw [hcongr, ih k hkn]
      have hnotlt : ¬ (n < k) := by omega
      simp only [kSparseVec, hnotlt, ite_false]
      exact Rat.add_zero _
    · have hkeq : k = n + 1 := by omega
      subst hkeq
      have hcongr : finSum n (fun i : Fin n => kSparseVec (n + 1) (n + 1) i.castSucc) =
          finSum n (kSparseVec n n) := by
        apply finSum_congr
        intro i
        have h1 : i.val < n + 1 := by omega
        have h2 : i.val < n := i.isLt
        simp [kSparseVec, h1, h2]
      rw [hcongr, ih n (Nat.le_refl n)]
      have hlt : n < n + 1 := Nat.lt_succ_self n
      simp only [kSparseVec, hlt, ite_true, Rat.natCast_add]
      rfl

theorem linfNorm_kSparseVec (d k : Nat) (hk1 : 1 ≤ k) (hkd : k ≤ d) :
    linfNorm (kSparseVec d k) = 1 := by
  have hd : 1 ≤ d := Nat.le_trans hk1 hkd
  have hle : linfNorm (kSparseVec d k) ≤ 1 := by
    obtain ⟨i, hi⟩ := exists_eq_linfNorm hd (kSparseVec d k)
    rw [← hi]
    unfold kSparseVec
    split
    · rw [ratAbs_of_nonneg (by decide)]; exact Rat.le_refl
    · rw [ratAbs_of_nonneg (by decide)]; decide
  have hge : (1 : Rat) ≤ linfNorm (kSparseVec d k) := by
    have h0 := ratAbs_le_linfNorm (kSparseVec d k) ⟨0, hd⟩
    have hv : kSparseVec d k ⟨0, hd⟩ = 1 := by
      unfold kSparseVec
      have : 0 < k := hk1
      simp [this]
    rw [hv, ratAbs_of_nonneg (by decide)] at h0
    exact h0
  exact Rat.le_antisymm hle hge

/-! ## Theorem 1: Universal Upper and Lower Envelopes + Exact Attainment -/

/-- Universal upper envelope:
    `H_{α,β}(x)^2 ≤ (α^2 d + 2 α β + β^2) * MS(x)` for all `d ≥ 1`, `α > 0`, `β > 0`, `x`. -/
theorem hybrid_upper_envelope_universal (d : Nat) (hd : 1 ≤ d) (α β : Rat)
    (hα : (0 : Rat) < α) (hβ : (0 : Rat) < β) (x : Fin d → Rat) :
    hybridNorm α β x * hybridNorm α β x ≤ hybridUpperConstSq d α β * meanSq x := by
  have hdpos : (0 : Rat) < (d : Rat) := rat_natCast_pos hd
  have hdne : (d : Rat) ≠ 0 := Rat.ne_of_gt hdpos
  obtain ⟨i0, hi0⟩ := exists_eq_linfNorm hd x
  let M : Rat := linfNorm x
  let g : Fin d → Rat := fun i => if i = i0 then 0 else ratAbs (x i)
  let S : Rat := finSum d g
  let Q : Rat := finSum d (fun i => g i * g i)
  have hl1 : l1Norm x = M + S := by
    unfold l1Norm
    rw [finSum_split_at (fun i => ratAbs (x i)) i0, hi0]
  have hsq : sumSq x = M * M + Q := by
    unfold sumSq
    have hcongr1 : finSum d (fun i => x i * x i) = finSum d (fun i => ratAbs (x i) * ratAbs (x i)) := by
      apply finSum_congr; intro i; exact (ratAbs_sq (x i)).symm
    rw [hcongr1, finSum_split_at (fun i => ratAbs (x i) * ratAbs (x i)) i0, hi0]
    have hcongr2 :
        finSum d (fun i => if i = i0 then 0 else ratAbs (x i) * ratAbs (x i)) = Q := by
      apply finSum_congr
      intro i
      by_cases h : i = i0
      · simp [g, h]
      · simp [g, h]
    rw [hcongr2]
  have hH : hybridNorm α β x * (d : Rat) = (α * (d : Rat) + β) * M + β * S := by
    unfold hybridNorm
    rw [hl1]
    have h1 : (β / (d : Rat)) * (M + S) * (d : Rat) = β * (M + S) := by
      have : (β / (d : Rat)) * (M + S) * (d : Rat) = ((β / (d : Rat)) * (d : Rat)) * (M + S) := by grind
      rw [this, rat_div_mul_cancel hdne]
    have h2 : (α * M + (β / (d : Rat)) * (M + S)) * (d : Rat) =
        α * M * (d : Rat) + (β / (d : Rat)) * (M + S) * (d : Rat) := by grind
    rw [h2, h1]
    grind
  have hd2pos : (0 : Rat) < (d : Rat) * (d : Rat) := rat_mul_pos hdpos hdpos
  apply rat_le_of_mul_pos_right hd2pos
  have hLHS : (hybridNorm α β x * hybridNorm α β x) * ((d : Rat) * (d : Rat)) =
      ((α * (d : Rat) + β) * M + β * S) * ((α * (d : Rat) + β) * M + β * S) := by
    have : (hybridNorm α β x * hybridNorm α β x) * ((d : Rat) * (d : Rat)) =
        (hybridNorm α β x * (d : Rat)) * (hybridNorm α β x * (d : Rat)) := by grind
    rw [this, hH]
  have hRHS : (hybridUpperConstSq d α β * meanSq x) * ((d : Rat) * (d : Rat)) =
      (d : Rat) * hybridUpperConstSq d α β * (M * M + Q) := by
    unfold meanSq
    rw [hsq]
    have : (hybridUpperConstSq d α β * ((M * M + Q) / (d : Rat))) * ((d : Rat) * (d : Rat)) =
        (d : Rat) * hybridUpperConstSq d α β * (((M * M + Q) / (d : Rat)) * (d : Rat)) := by grind
    rw [this, rat_div_mul_cancel hdne]
  rw [hLHS, hRHS]
  cases d with
  | zero => omega
  | succ n =>
    cases n with
    | zero =>
      have hS0 : S = 0 := by
        simp only [S, finSum, g]
        have hi00 : (⟨0, Nat.lt_succ_self 0⟩ : Fin 1) = i0 := Fin.ext (by omega)
        simp [hi00]; grind
      have hQ0 : Q = 0 := by
        simp only [Q, finSum, g]
        have hi00 : (⟨0, Nat.lt_succ_self 0⟩ : Fin 1) = i0 := Fin.ext (by omega)
        simp [hi00]; grind
      rw [hS0, hQ0]
      unfold hybridUpperConstSq
      have h1 : ((0 + 1 : Nat) : Rat) = 1 := by decide
      rw [h1]
      have heq : ((α * 1 + β) * M + β * 0) * ((α * 1 + β) * M + β * 0) =
          1 * (α * α * 1 + 2 * α * β + β * β) * (M * M + 0) := by grind
      rw [heq]
      exact Rat.le_refl
    | succ m =>
      have hmpos : (0 : Rat) < ((m + 1 : Nat) : Rat) := rat_natCast_pos (Nat.succ_pos m)
      have hcs : S * S ≤ ((m + 1 : Nat) : Rat) * Q := by
        have h := finSum_excl_sq_le (fun i => ratAbs (x i)) i0
        have hsub : m + 1 + 1 - 1 = m + 1 := by omega
        rw [hsub] at h
        exact h
      have hCpos : (0 : Rat) < ((m + 1 + 1 : Nat) : Rat) * hybridUpperConstSq (m + 1 + 1) α β := by
        unfold hybridUpperConstSq
        have h1 : (0 : Rat) < α * α * ((m + 1 + 1 : Nat) : Rat) :=
          rat_mul_pos (rat_mul_pos hα hα) hdpos
        have h2 : (0 : Rat) < 2 * α * β := rat_mul_pos (rat_mul_pos (by decide) hα) hβ
        have h3 : (0 : Rat) < β * β := rat_mul_pos hβ hβ
        exact rat_mul_pos hdpos (rat_add_pos (rat_add_pos h1 h2) h3)
      apply rat_le_of_mul_pos_right hmpos
      apply rat_le_of_sub_nonneg
      have hcast : ((m + 1 + 1 : Nat) : Rat) = ((m + 1 : Nat) : Rat) + 1 := by
        rw [Rat.natCast_add]; rfl
      have hdiffQ : (0 : Rat) ≤ ((m + 1 : Nat) : Rat) * Q - S * S := rat_sub_nonneg hcs
      have hsqTerm : (0 : Rat) ≤
          (((m + 1 : Nat) : Rat) * β * M - (α * ((m + 1 + 1 : Nat) : Rat) + β) * S) *
          (((m + 1 : Nat) : Rat) * β * M - (α * ((m + 1 + 1 : Nat) : Rat) + β) * S) :=
        rat_sq_nonneg _
      have hident :
          ((m + 1 + 1 : Nat) : Rat) * hybridUpperConstSq (m + 1 + 1) α β * (M * M + Q) * ((m + 1 : Nat) : Rat) -
            ((α * ((m + 1 + 1 : Nat) : Rat) + β) * M + β * S) *
            ((α * ((m + 1 + 1 : Nat) : Rat) + β) * M + β * S) * ((m + 1 : Nat) : Rat) =
          (((m + 1 + 1 : Nat) : Rat) * hybridUpperConstSq (m + 1 + 1) α β) *
            (((m + 1 : Nat) : Rat) * Q - S * S) +
          (((m + 1 : Nat) : Rat) * β * M - (α * ((m + 1 + 1 : Nat) : Rat) + β) * S) *
          (((m + 1 : Nat) : Rat) * β * M - (α * ((m + 1 + 1 : Nat) : Rat) + β) * S) := by
        unfold hybridUpperConstSq
        rw [hcast]
        grind
      rw [hident]
      exact rat_add_nonneg (Rat.mul_nonneg (Rat.le_of_lt hCpos) hdiffQ) hsqTerm

/-- Exact attainment of the upper envelope at `upperExtremalVec d α β`. -/
theorem hybrid_upper_envelope_attained (d : Nat) (hd : 1 ≤ d) (α β : Rat)
    (hα : (0 : Rat) < α) (hβ : (0 : Rat) < β) :
    0 < meanSq (upperExtremalVec d α β) ∧
    hybridNorm α β (upperExtremalVec d α β) * hybridNorm α β (upperExtremalVec d α β) =
      hybridUpperConstSq d α β * meanSq (upperExtremalVec d α β) := by
  have hdpos : (0 : Rat) < (d : Rat) := rat_natCast_pos hd
  have hdne : (d : Rat) ≠ 0 := Rat.ne_of_gt hdpos
  have hdenpos : (0 : Rat) < α * (d : Rat) + β := rat_add_pos (rat_mul_pos hα hdpos) hβ
  have hdenne : α * (d : Rat) + β ≠ 0 := Rat.ne_of_gt hdenpos
  let t : Rat := β / (α * (d : Rat) + β)
  have htpos : (0 : Rat) < t := rat_div_pos hβ hdenpos
  have hlinf : linfNorm (upperExtremalVec d α β) = 1 :=
    linfNorm_upperExtremalVec d hd α β hα hβ
  have hl1 : l1Norm (upperExtremalVec d α β) = 1 + ((d - 1 : Nat) : Rat) * t := by
    unfold l1Norm upperExtremalVec
    have hcongr : finSum d (fun i => ratAbs (if i.val = 0 then (1 : Rat) else t)) =
        finSum d (fun i => if i.val = 0 then (1 : Rat) else t) := by
      apply finSum_congr; intro i
      split
      · exact ratAbs_of_nonneg (by decide)
      · exact ratAbs_of_nonneg (Rat.le_of_lt htpos)
    rw [hcongr]
    exact finSum_spike_uniform d hd 1 t
  have hsumsq : sumSq (upperExtremalVec d α β) = 1 + ((d - 1 : Nat) : Rat) * (t * t) := by
    unfold sumSq upperExtremalVec
    have hcongr : finSum d (fun i => (if i.val = 0 then (1 : Rat) else t) *
        (if i.val = 0 then (1 : Rat) else t)) =
        finSum d (fun i => if i.val = 0 then (1 : Rat) else t * t) := by
      apply finSum_congr; intro i
      split <;> simp
    rw [hcongr]
    exact finSum_spike_uniform d hd 1 (t * t)
  have hmspos : (0 : Rat) < meanSq (upperExtremalVec d α β) := by
    unfold meanSq
    rw [hsumsq]
    have h1 : (0 : Rat) ≤ ((d - 1 : Nat) : Rat) * (t * t) :=
      Rat.mul_nonneg (rat_natCast_nonneg (d - 1)) (rat_sq_nonneg t)
    exact rat_div_pos (rat_add_pos_of_pos_of_nonneg (by decide) h1) hdpos
  refine ⟨hmspos, ?_⟩
  have hdsub : ((d - 1 : Nat) : Rat) = (d : Rat) - 1 := by
    have hnat : (d - 1) + 1 = d := Nat.sub_add_cancel hd
    have hcast : (((d - 1) + 1 : Nat) : Rat) = (d : Rat) := by rw [hnat]
    rw [Rat.natCast_add] at hcast
    grind
  -- Clear denominators `d * d` and `(α d + β) * (α d + β)`
  have ht_mul : t * (α * (d : Rat) + β) = β := rat_div_mul_cancel hdenne
  have hH_mul : hybridNorm α β (upperExtremalVec d α β) * ((d : Rat) * (α * (d : Rat) + β)) =
      (α * (d : Rat) + β) * (α * (d : Rat) + β) + ((d : Rat) - 1) * (β * β) := by
    unfold hybridNorm
    rw [hlinf, hl1, hdsub]
    have h1 : (β / (d : Rat)) * (1 + ((d : Rat) - 1) * t) * ((d : Rat) * (α * (d : Rat) + β)) =
        β * (α * (d : Rat) + β) + ((d : Rat) - 1) * (β * (t * (α * (d : Rat) + β))) := by
      have hc : (β / (d : Rat)) * (d : Rat) = β := rat_div_mul_cancel hdne
      have : (β / (d : Rat)) * (1 + ((d : Rat) - 1) * t) * ((d : Rat) * (α * (d : Rat) + β)) =
          ((β / (d : Rat)) * (d : Rat)) * ((1 + ((d : Rat) - 1) * t) * (α * (d : Rat) + β)) := by grind
      rw [this, hc]
      grind
    rw [ht_mul] at h1
    have h2 : (α * 1 + (β / (d : Rat)) * (1 + ((d : Rat) - 1) * t)) * ((d : Rat) * (α * (d : Rat) + β)) =
        α * (d : Rat) * (α * (d : Rat) + β) +
          (β / (d : Rat)) * (1 + ((d : Rat) - 1) * t) * ((d : Rat) * (α * (d : Rat) + β)) := by grind
    rw [h2, h1]
    grind
  have hH_simp : hybridNorm α β (upperExtremalVec d α β) * ((d : Rat) * (α * (d : Rat) + β)) =
      (d : Rat) * hybridUpperConstSq d α β := by
    rw [hH_mul]
    unfold hybridUpperConstSq
    grind
  have hMS_mul : meanSq (upperExtremalVec d α β) * ((d : Rat) * ((α * (d : Rat) + β) * (α * (d : Rat) + β))) =
      (d : Rat) * hybridUpperConstSq d α β := by
    unfold meanSq
    rw [hsumsq, hdsub]
    have h1 : ((1 + ((d : Rat) - 1) * (t * t)) / (d : Rat)) *
        ((d : Rat) * ((α * (d : Rat) + β) * (α * (d : Rat) + β))) =
        (1 + ((d : Rat) - 1) * (t * t)) * ((α * (d : Rat) + β) * (α * (d : Rat) + β)) := by
      have : ((1 + ((d : Rat) - 1) * (t * t)) / (d : Rat)) *
          ((d : Rat) * ((α * (d : Rat) + β) * (α * (d : Rat) + β))) =
          (((1 + ((d : Rat) - 1) * (t * t)) / (d : Rat)) * (d : Rat)) *
            ((α * (d : Rat) + β) * (α * (d : Rat) + β)) := by grind
      rw [this, rat_div_mul_cancel hdne]
    rw [h1]
    have h2 : (t * t) * ((α * (d : Rat) + β) * (α * (d : Rat) + β)) = β * β := by
      have : (t * t) * ((α * (d : Rat) + β) * (α * (d : Rat) + β)) =
          (t * (α * (d : Rat) + β)) * (t * (α * (d : Rat) + β)) := by grind
      rw [this, ht_mul]
    unfold hybridUpperConstSq
    have h3 : (1 + ((d : Rat) - 1) * (t * t)) * ((α * (d : Rat) + β) * (α * (d : Rat) + β)) =
        (α * (d : Rat) + β) * (α * (d : Rat) + β) +
          ((d : Rat) - 1) * ((t * t) * ((α * (d : Rat) + β) * (α * (d : Rat) + β))) := by grind
    rw [h3, h2]
    grind
  -- Both sides multiplied by `(d * (α d + β))^2` are equal!
  let K : Rat := ((d : Rat) * (α * (d : Rat) + β)) * ((d : Rat) * (α * (d : Rat) + β))
  have hKne : K ≠ 0 := by
    have hKpos : (0 : Rat) < K :=
      rat_mul_pos (rat_mul_pos hdpos hdenpos) (rat_mul_pos hdpos hdenpos)
    exact Rat.ne_of_gt hKpos
  have hmul : (hybridNorm α β (upperExtremalVec d α β) * hybridNorm α β (upperExtremalVec d α β) -
      hybridUpperConstSq d α β * meanSq (upperExtremalVec d α β)) * K = 0 := by
    have hL : (hybridNorm α β (upperExtremalVec d α β) * hybridNorm α β (upperExtremalVec d α β)) * K =
        ((d : Rat) * hybridUpperConstSq d α β) * ((d : Rat) * hybridUpperConstSq d α β) := by
      have : (hybridNorm α β (upperExtremalVec d α β) * hybridNorm α β (upperExtremalVec d α β)) * K =
          (hybridNorm α β (upperExtremalVec d α β) * ((d : Rat) * (α * (d : Rat) + β))) *
          (hybridNorm α β (upperExtremalVec d α β) * ((d : Rat) * (α * (d : Rat) + β))) := by
        simp only [K]; grind
      rw [this, hH_simp]
    have hR : (hybridUpperConstSq d α β * meanSq (upperExtremalVec d α β)) * K =
        ((d : Rat) * hybridUpperConstSq d α β) * ((d : Rat) * hybridUpperConstSq d α β) := by
      have : (hybridUpperConstSq d α β * meanSq (upperExtremalVec d α β)) * K =
          ((d : Rat) * hybridUpperConstSq d α β) *
            (meanSq (upperExtremalVec d α β) * ((d : Rat) * ((α * (d : Rat) + β) * (α * (d : Rat) + β)))) := by
        simp only [K]; grind
      rw [this, hMS_mul]
    grind
  cases Rat.mul_eq_zero.mp hmul with
  | inl h0 => grind
  | inr hK0 => exact False.elim (hKne hK0)

/-- Universal lower envelope:
    `4 α β * MS(x) ≤ H_{α,β}(x)^2` for all `d ≥ 1`, `α > 0`, `β > 0`, `x`. -/
theorem hybrid_lower_envelope_universal (d : Nat) (hd : 1 ≤ d) (α β : Rat)
    (hα : (0 : Rat) < α) (hβ : (0 : Rat) < β) (x : Fin d → Rat) :
    hybridLowerConstSq α β * meanSq x ≤ hybridNorm α β x * hybridNorm α β x := by
  have hdpos : (0 : Rat) < (d : Rat) := rat_natCast_pos hd
  -- Step 1: sumSq x ≤ linfNorm x * l1Norm x
  have hsum_le : sumSq x ≤ linfNorm x * l1Norm x := by
    unfold sumSq l1Norm
    rw [← finSum_mul_left]
    apply finSum_le_finSum
    intro i
    rw [← ratAbs_sq (x i)]
    exact rat_mul_le_mul_of_nonneg_right (ratAbs_le_linfNorm x i) (ratAbs_nonneg (x i))
  -- Step 2: 4 α β * meanSq x ≤ 4 * (α * linfNorm x) * ((β / d) * l1Norm x)
  have hstep2 : hybridLowerConstSq α β * meanSq x ≤
      4 * (α * linfNorm x) * ((β / (d : Rat)) * l1Norm x) := by
    unfold hybridLowerConstSq meanSq
    have h4αβ : (0 : Rat) ≤ (4 * α * β) / (d : Rat) :=
      rat_div_nonneg (Rat.le_of_lt (rat_mul_pos (rat_mul_pos (by decide) hα) hβ)) hdpos
    have hmul := rat_mul_le_mul_of_nonneg_left hsum_le h4αβ
    have hL : (4 * α * β) / (d : Rat) * sumSq x = 4 * α * β * (sumSq x / (d : Rat)) := by
      rw [Rat.div_def, Rat.div_def]; grind
    have hR : (4 * α * β) / (d : Rat) * (linfNorm x * l1Norm x) =
        4 * (α * linfNorm x) * ((β / (d : Rat)) * l1Norm x) := by
      rw [Rat.div_def, Rat.div_def]; grind
    rw [hL, hR] at hmul
    exact hmul
  -- Step 3: AM-GM `4 a b ≤ (a + b)^2`
  have hamgm : 4 * (α * linfNorm x) * ((β / (d : Rat)) * l1Norm x) ≤
      hybridNorm α β x * hybridNorm α β x := by
    unfold hybridNorm
    apply rat_le_of_sub_nonneg
    have hident :
        (α * linfNorm x + β / (d : Rat) * l1Norm x) * (α * linfNorm x + β / (d : Rat) * l1Norm x) -
          4 * (α * linfNorm x) * (β / (d : Rat) * l1Norm x) =
        (α * linfNorm x - β / (d : Rat) * l1Norm x) * (α * linfNorm x - β / (d : Rat) * l1Norm x) := by
      grind
    rw [hident]
    exact rat_sq_nonneg _
  exact Rat.le_trans hstep2 hamgm

/-- Exact attainment of the lower envelope on `s`-sparse binary vectors in square dimension `d = s^2`. -/
theorem hybrid_lower_envelope_attained (s : Nat) (hs : 1 ≤ s) (α : Rat) (_hα : (0 : Rat) < α) :
    let d := s * s
    let β := (s : Rat) * α
    let x := kSparseVec d s
    0 < meanSq x ∧
    hybridNorm α β x * hybridNorm α β x = hybridLowerConstSq α β * meanSq x := by
  intro d β x
  have hsle : s ≤ d := by
    have : s * 1 ≤ s * s := Nat.mul_le_mul_left s hs
    omega
  have hdpos : (0 : Rat) < (d : Rat) := rat_natCast_pos (Nat.le_trans hs hsle)
  have hdne : (d : Rat) ≠ 0 := Rat.ne_of_gt hdpos
  have hspos : (0 : Rat) < (s : Rat) := rat_natCast_pos hs
  have hsne : (s : Rat) ≠ 0 := Rat.ne_of_gt hspos
  have hdcast : (d : Rat) = (s : Rat) * (s : Rat) := by
    simp only [d, Rat.natCast_mul]
  have hlinf : linfNorm x = 1 := linfNorm_kSparseVec d s hs hsle
  have hl1 : l1Norm x = (s : Rat) := by
    unfold l1Norm
    have hcongr : finSum d (fun i => ratAbs (x i)) = finSum d x := by
      apply finSum_congr; intro i; simp only [x, kSparseVec]
      split
      · exact ratAbs_of_nonneg (by decide)
      · exact ratAbs_of_nonneg (by decide)
    rw [hcongr]
    exact finSum_kSparseVec d s hsle
  have hsumsq : sumSq x = (s : Rat) := by
    unfold sumSq
    have hcongr : finSum d (fun i => x i * x i) = finSum d x := by
      apply finSum_congr; intro i; simp only [x, kSparseVec]
      split <;> simp
    rw [hcongr]
    exact finSum_kSparseVec d s hsle
  have hms : meanSq x = 1 / (s : Rat) := by
    unfold meanSq
    rw [hsumsq, hdcast]
    have h1 : ((s : Rat) / ((s : Rat) * (s : Rat))) * ((s : Rat) * (s : Rat)) = (s : Rat) :=
      rat_div_mul_cancel (by rw [← hdcast]; exact hdne)
    have h2 : (1 / (s : Rat)) * ((s : Rat) * (s : Rat)) = (s : Rat) := by
      have : (1 / (s : Rat)) * ((s : Rat) * (s : Rat)) = ((1 / (s : Rat)) * (s : Rat)) * (s : Rat) := by grind
      rw [this, rat_div_mul_cancel hsne, Rat.one_mul]
    have hmul : ((s : Rat) / ((s : Rat) * (s : Rat)) - 1 / (s : Rat)) * ((s : Rat) * (s : Rat)) = 0 := by
      grind
    cases Rat.mul_eq_zero.mp hmul with
    | inl h0 => grind
    | inr h0 =>
      have hne2 : (s : Rat) * (s : Rat) ≠ 0 := by rw [← hdcast]; exact hdne
      exact False.elim (hne2 h0)
  have hmspos : (0 : Rat) < meanSq x := by
    rw [hms]; exact rat_div_pos (by decide) hspos
  refine ⟨hmspos, ?_⟩
  have hH : hybridNorm α β x = 2 * α := by
    unfold hybridNorm
    rw [hlinf, hl1]
    have h1 : (β / (d : Rat)) * (s : Rat) = α := by
      have hc : (β / (d : Rat)) * (s : Rat) * (s : Rat) = α * (s : Rat) := by
        have : (β / (d : Rat)) * (s : Rat) * (s : Rat) = (β / (d : Rat)) * (d : Rat) := by
          rw [hdcast]; grind
        rw [this, rat_div_mul_cancel hdne]
        simp only [β]; grind
      have hmul : ((β / (d : Rat)) * (s : Rat) - α) * (s : Rat) = 0 := by grind
      cases Rat.mul_eq_zero.mp hmul with
      | inl h0 => grind
      | inr h0 => exact False.elim (hsne h0)
    rw [h1]
    grind
  rw [hH, hms]
  unfold hybridLowerConstSq
  simp only [β]
  have h1 : 4 * α * ((s : Rat) * α) * (1 / (s : Rat)) = 4 * α * α * ((1 / (s : Rat)) * (s : Rat)) := by
    grind
  rw [h1, rat_div_mul_cancel hsne]
  grind

/-- Headline Theorem 1: Universal Upper & Lower Envelopes and Exact Attainment. -/
theorem hybrid_linf_l1_exact_upper_and_lower_envelopes :
    (∀ (d : Nat) (α β : Rat) (x : Fin d → Rat), 1 ≤ d → 0 < α → 0 < β →
      hybridNorm α β x * hybridNorm α β x ≤ hybridUpperConstSq d α β * meanSq x) ∧
    (∀ (d : Nat) (α β : Rat), 1 ≤ d → 0 < α → 0 < β →
      0 < meanSq (upperExtremalVec d α β) ∧
      hybridNorm α β (upperExtremalVec d α β) * hybridNorm α β (upperExtremalVec d α β) =
        hybridUpperConstSq d α β * meanSq (upperExtremalVec d α β)) ∧
    (∀ (d : Nat) (α β : Rat) (x : Fin d → Rat), 1 ≤ d → 0 < α → 0 < β →
      hybridLowerConstSq α β * meanSq x ≤ hybridNorm α β x * hybridNorm α β x) ∧
    (∀ (s : Nat) (α : Rat), 1 ≤ s → 0 < α →
      0 < meanSq (kSparseVec (s * s) s) ∧
      hybridNorm α ((s : Rat) * α) (kSparseVec (s * s) s) *
        hybridNorm α ((s : Rat) * α) (kSparseVec (s * s) s) =
        hybridLowerConstSq α ((s : Rat) * α) * meanSq (kSparseVec (s * s) s)) :=
  ⟨fun d α β x hd hα hβ => hybrid_upper_envelope_universal d hd α β hα hβ x,
   fun d α β hd hα hβ => hybrid_upper_envelope_attained d hd α β hα hβ,
   fun d α β x hd hα hβ => hybrid_lower_envelope_universal d hd α β hα hβ x,
   fun s α hs hα => hybrid_lower_envelope_attained s hs α hα⟩

/-! ## Theorem 2: Universal Minimax `d^(1/4)` Law & Impossibility of `O(1)` Distortion -/

/-- Headline Theorem 2: Universal Minimax Optimality and `Θ(d^(1/4))` Law. -/
theorem hybrid_linf_l1_minimax_d_quarter_law :
    (∀ (d : Nat) (α β : Rat), 1 ≤ d → 0 < α → 0 < β →
      (2 * hybridKappaSq d α β - 1) * (2 * hybridKappaSq d α β - 1) - (d : Rat) =
        ((α * α * (d : Rat) - β * β) * (α * α * (d : Rat) - β * β)) / (4 * α * α * β * β) ∧
      (d : Rat) ≤ 4 * hybridKappaSq d α β * hybridKappaSq d α β - 4 * hybridKappaSq d α β + 1) ∧
    (∀ (s : Nat) (α β : Rat), 1 ≤ s → 0 < α → 0 < β →
      hybridKappaSq (s * s) α β - ((s : Rat) + 1) / 2 =
        ((α * (s : Rat) - β) * (α * (s : Rat) - β)) / (4 * α * β) ∧
      ((s : Rat) + 1) / 2 ≤ hybridKappaSq (s * s) α β ∧
      (hybridKappaSq (s * s) α β = ((s : Rat) + 1) / 2 ↔ β = (s : Rat) * α)) ∧
    (∀ C : Rat, 1 ≤ C → ∃ d : Nat, 1 ≤ d ∧ ∀ α β : Rat, 0 < α → 0 < β → C < hybridKappaSq d α β) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Part (a): Universal (2 κ^2 - 1)^2 - d = (α^2 d - β^2)^2 / (4 α^2 β^2) ≥ 0
    intro d α β _ hα hβ
    have h4αβ_pos : (0 : Rat) < 4 * α * β := rat_mul_pos (rat_mul_pos (by decide) hα) hβ
    have h4αβ_ne : 4 * α * β ≠ 0 := Rat.ne_of_gt h4αβ_pos
    have hden_pos : (0 : Rat) < 4 * α * α * β * β :=
      rat_mul_pos (rat_mul_pos (rat_mul_pos (rat_mul_pos (by decide) hα) hα) hβ) hβ
    have hden_ne : 4 * α * α * β * β ≠ 0 := Rat.ne_of_gt hden_pos
    have hk_mul : hybridKappaSq d α β * (4 * α * β) = α * α * (d : Rat) + 2 * α * β + β * β := by
      unfold hybridKappaSq hybridUpperConstSq hybridLowerConstSq
      exact rat_div_mul_cancel h4αβ_ne
    have hident : (2 * hybridKappaSq d α β - 1) * (2 * hybridKappaSq d α β - 1) - (d : Rat) =
        ((α * α * (d : Rat) - β * β) * (α * α * (d : Rat) - β * β)) / (4 * α * α * β * β) := by
      have hmul : (((2 * hybridKappaSq d α β - 1) * (2 * hybridKappaSq d α β - 1) - (d : Rat)) -
          ((α * α * (d : Rat) - β * β) * (α * α * (d : Rat) - β * β)) / (4 * α * α * β * β)) *
          (4 * α * α * β * β) = 0 := by
        have h1 : (2 * hybridKappaSq d α β - 1) * (2 * α * β) = α * α * (d : Rat) + β * β := by
          have : (2 * hybridKappaSq d α β - 1) * (2 * α * β) =
              hybridKappaSq d α β * (4 * α * β) - 2 * α * β := by grind
          rw [this, hk_mul]; grind
        have h2 : ((2 * hybridKappaSq d α β - 1) * (2 * hybridKappaSq d α β - 1)) * (4 * α * α * β * β) =
            (α * α * (d : Rat) + β * β) * (α * α * (d : Rat) + β * β) := by
          have : ((2 * hybridKappaSq d α β - 1) * (2 * hybridKappaSq d α β - 1)) * (4 * α * α * β * β) =
              ((2 * hybridKappaSq d α β - 1) * (2 * α * β)) *
              ((2 * hybridKappaSq d α β - 1) * (2 * α * β)) := by grind
          rw [this, h1]
        have h3 : (((α * α * (d : Rat) - β * β) * (α * α * (d : Rat) - β * β)) / (4 * α * α * β * β)) *
            (4 * α * α * β * β) =
            (α * α * (d : Rat) - β * β) * (α * α * (d : Rat) - β * β) :=
          rat_div_mul_cancel hden_ne
        grind
      cases Rat.mul_eq_zero.mp hmul with
      | inl h0 => grind
      | inr h0 => exact False.elim (hden_ne h0)
    refine ⟨hident, ?_⟩
    have hnonneg : (0 : Rat) ≤
        (2 * hybridKappaSq d α β - 1) * (2 * hybridKappaSq d α β - 1) - (d : Rat) := by
      rw [hident]
      exact rat_div_nonneg (rat_sq_nonneg _) hden_pos
    apply rat_le_of_sub_nonneg
    have heq : 4 * hybridKappaSq d α β * hybridKappaSq d α β - 4 * hybridKappaSq d α β + 1 - (d : Rat) =
        (2 * hybridKappaSq d α β - 1) * (2 * hybridKappaSq d α β - 1) - (d : Rat) := by grind
    rw [heq]
    exact hnonneg
  · -- Part (b): Exact square-dimension minimax law & unique equality iff β = s α
    intro s α β _ hα hβ
    have h4αβ_pos : (0 : Rat) < 4 * α * β := rat_mul_pos (rat_mul_pos (by decide) hα) hβ
    have h4αβ_ne : 4 * α * β ≠ 0 := Rat.ne_of_gt h4αβ_pos
    have hk_mul : hybridKappaSq (s * s) α β * (4 * α * β) =
        α * α * ((s : Rat) * (s : Rat)) + 2 * α * β + β * β := by
      unfold hybridKappaSq hybridUpperConstSq hybridLowerConstSq
      rw [Rat.natCast_mul]
      exact rat_div_mul_cancel h4αβ_ne
    have hdiff : hybridKappaSq (s * s) α β - ((s : Rat) + 1) / 2 =
        ((α * (s : Rat) - β) * (α * (s : Rat) - β)) / (4 * α * β) := by
      have hmul : ((hybridKappaSq (s * s) α β - ((s : Rat) + 1) / 2) -
          ((α * (s : Rat) - β) * (α * (s : Rat) - β)) / (4 * α * β)) * (4 * α * β) = 0 := by
        have h1 : (((s : Rat) + 1) / 2) * (4 * α * β) = 2 * α * β * ((s : Rat) + 1) := by
          have : (((s : Rat) + 1) / 2) * (4 * α * β) =
              ((((s : Rat) + 1) / 2) * 2) * (2 * α * β) := by grind
          rw [this, rat_div_mul_cancel (by decide)]
          grind
        have h2 : (((α * (s : Rat) - β) * (α * (s : Rat) - β)) / (4 * α * β)) * (4 * α * β) =
            (α * (s : Rat) - β) * (α * (s : Rat) - β) :=
          rat_div_mul_cancel h4αβ_ne
        grind
      cases Rat.mul_eq_zero.mp hmul with
      | inl h0 => grind
      | inr h0 => exact False.elim (h4αβ_ne h0)
    have hle : ((s : Rat) + 1) / 2 ≤ hybridKappaSq (s * s) α β := by
      apply rat_le_of_sub_nonneg
      rw [hdiff]
      exact rat_div_nonneg (rat_sq_nonneg _) h4αβ_pos
    refine ⟨hdiff, hle, ?_⟩
    constructor
    · intro heq
      have h0 : ((α * (s : Rat) - β) * (α * (s : Rat) - β)) / (4 * α * β) = 0 := by
        rw [← hdiff, heq]; grind
      have hsq0 : (α * (s : Rat) - β) * (α * (s : Rat) - β) = 0 := by
        have := rat_div_mul_cancel (a := (α * (s : Rat) - β) * (α * (s : Rat) - β)) h4αβ_ne
        rw [h0, Rat.zero_mul] at this
        exact this.symm
      cases Rat.mul_eq_zero.mp hsq0 with
      | inl h => grind
      | inr h => grind
    · intro hβeq
      have h0 : hybridKappaSq (s * s) α β - ((s : Rat) + 1) / 2 = 0 := by
        rw [hdiff, hβeq]
        have : α * (s : Rat) - (s : Rat) * α = 0 := by grind
        rw [this, Rat.zero_mul, Rat.div_def, Rat.zero_mul]
      grind
  · -- Part (c): No O(1) distortion — for any C ≥ 1, take s = 2 * C.ceil.toNat + 2, d = s * s
    intro C hC
    let s : Nat := 2 * C.ceil.toNat + 2
    have hs1 : 1 ≤ s := by omega
    refine ⟨s * s, Nat.mul_le_mul hs1 hs1, ?_⟩
    intro α β hα hβ
    have h4αβ_pos : (0 : Rat) < 4 * α * β := rat_mul_pos (rat_mul_pos (by decide) hα) hβ
    have h4αβ_ne : 4 * α * β ≠ 0 := Rat.ne_of_gt h4αβ_pos
    have hle : ((s : Rat) + 1) / 2 ≤ hybridKappaSq (s * s) α β := by
      apply rat_le_of_sub_nonneg
      have hk_mul : hybridKappaSq (s * s) α β * (4 * α * β) =
          α * α * ((s : Rat) * (s : Rat)) + 2 * α * β + β * β := by
        unfold hybridKappaSq hybridUpperConstSq hybridLowerConstSq
        rw [Rat.natCast_mul]
        exact rat_div_mul_cancel h4αβ_ne
      have hdiff : hybridKappaSq (s * s) α β - ((s : Rat) + 1) / 2 =
          ((α * (s : Rat) - β) * (α * (s : Rat) - β)) / (4 * α * β) := by
        have hmul : ((hybridKappaSq (s * s) α β - ((s : Rat) + 1) / 2) -
            ((α * (s : Rat) - β) * (α * (s : Rat) - β)) / (4 * α * β)) * (4 * α * β) = 0 := by
          have h1 : (((s : Rat) + 1) / 2) * (4 * α * β) = 2 * α * β * ((s : Rat) + 1) := by
            have : (((s : Rat) + 1) / 2) * (4 * α * β) =
                ((((s : Rat) + 1) / 2) * 2) * (2 * α * β) := by grind
            rw [this, rat_div_mul_cancel (by decide)]
            grind
          have h2 : (((α * (s : Rat) - β) * (α * (s : Rat) - β)) / (4 * α * β)) * (4 * α * β) =
              (α * (s : Rat) - β) * (α * (s : Rat) - β) :=
            rat_div_mul_cancel h4αβ_ne
          grind
        cases Rat.mul_eq_zero.mp hmul with
        | inl h0 => grind
        | inr h0 => exact False.elim (h4αβ_ne h0)
      rw [hdiff]
      exact rat_div_nonneg (rat_sq_nonneg _) h4αβ_pos
    have hClt : C < ((s : Rat) + 1) / 2 := by
      have hCeil : C ≤ (C.ceil : Rat) := Rat.le_ceil
      have hCeilPos : (1 : Rat) ≤ (C.ceil : Rat) := Rat.le_trans hC hCeil
      have hCeilNonneg : (0 : Int) ≤ C.ceil := by
        by_cases h : (0 : Int) ≤ C.ceil
        · exact h
        · have hneg : C.ceil < 0 := Int.not_le.mp h
          have hlt0 : (C.ceil : Rat) < 0 := by
            rw [Rat.lt_iff]
            have hcn : ((C.ceil : Rat)).num = C.ceil := rfl
            have hcd : ((C.ceil : Rat)).den = 1 := rfl
            have h0n : ((0 : Rat)).num = 0 := rfl
            have h0d : ((0 : Rat)).den = 1 := rfl
            rw [hcn, hcd, h0n, h0d]
            omega
          exact False.elim (Rat.not_le.mpr (rat_lt_trans hlt0 (by decide : (0 : Rat) < 1)) hCeilPos)
      have hCeilEq : (C.ceil : Rat) = (C.ceil.toNat : Rat) := by
        have hi : (C.ceil.toNat : Int) = C.ceil := Int.toNat_of_nonneg hCeilNonneg
        have hr : ((C.ceil.toNat : Int) : Rat) = (C.ceil : Rat) := by rw [hi]
        rw [Rat.intCast_natCast] at hr
        exact hr.symm
      have hCleNat : C ≤ (C.ceil.toNat : Rat) := by rw [← hCeilEq]; exact hCeil
      have hNumLt : (C.ceil.toNat : Rat) < ((s : Rat) + 1) / 2 := by
        apply rat_lt_div_of_mul_lt (by decide)
        have hnat : 2 * C.ceil.toNat < s + 1 := by omega
        have hrat : ((2 * C.ceil.toNat : Nat) : Rat) < ((s + 1 : Nat) : Rat) := rat_natCast_lt hnat
        rw [Rat.natCast_mul, Rat.natCast_add] at hrat
        have h2 : ((2 : Nat) : Rat) = 2 := by decide
        have h1 : ((1 : Nat) : Rat) = 1 := by decide
        rw [h2, h1] at hrat
        grind
      exact rat_lt_of_le_of_lt hCleNat hNumLt
    exact rat_lt_of_lt_of_le hClt hle

/-! ## Theorem 3: Exact Llama-3 `d = 4096` and `d = 8192` Dyadic Hybrid Norm Witnesses -/

/-- Headline Theorem 3: Exact pure-bitshift dyadic instantiations for Llama-3 8B (`d = 4096`),
    Llama-3 70B (`d = 8192`), and the power-of-4 dyadic scaling table. -/
theorem dyadic_llama3_d4096_hybrid_norm_exact :
    (hybridLowerConstSq (invPow2Rat 6) 1 = 1 / 16 ∧
     hybridUpperConstSq 4096 (invPow2Rat 6) 1 = 65 / 32 ∧
     hybridKappaSq 4096 (invPow2Rat 6) 1 = 65 / 2 ∧
     (4096 : Rat) / hybridKappaSq 4096 (invPow2Rat 6) 1 = 8192 / 65 ∧
     (126 : Rat) < 8192 / 65 ∧
     (∀ x : Fin 4096 → Rat,
       hybridNorm (invPow2Rat 6) 1 x = invPow2Rat 6 * linfNorm x + invPow2Rat 12 * l1Norm x ∧
       (1 / 16 : Rat) * meanSq x ≤ hybridNorm (invPow2Rat 6) 1 x * hybridNorm (invPow2Rat 6) 1 x ∧
       hybridNorm (invPow2Rat 6) 1 x * hybridNorm (invPow2Rat 6) 1 x ≤ (65 / 32 : Rat) * meanSq x)) ∧
    (hybridLowerConstSq (invPow2Rat 6) 1 = 1 / 16 ∧
     hybridUpperConstSq 8192 (invPow2Rat 6) 1 = 97 / 32 ∧
     hybridKappaSq 8192 (invPow2Rat 6) 1 = 97 / 2 ∧
     (8192 : Rat) / hybridKappaSq 8192 (invPow2Rat 6) 1 = 16384 / 97 ∧
     (168 : Rat) < 16384 / 97 ∧
     (∀ x : Fin 8192 → Rat,
       hybridNorm (invPow2Rat 6) 1 x = invPow2Rat 6 * linfNorm x + invPow2Rat 13 * l1Norm x ∧
       (1 / 16 : Rat) * meanSq x ≤ hybridNorm (invPow2Rat 6) 1 x * hybridNorm (invPow2Rat 6) 1 x ∧
       hybridNorm (invPow2Rat 6) 1 x * hybridNorm (invPow2Rat 6) 1 x ≤ (97 / 32 : Rat) * meanSq x)) ∧
    (hybridKappaSq 64 (invPow2Rat 3) 1 = 9 / 2 ∧
     hybridKappaSq 256 (invPow2Rat 4) 1 = 17 / 2 ∧
     hybridKappaSq 1024 (invPow2Rat 5) 1 = 33 / 2 ∧
     hybridKappaSq 4096 (invPow2Rat 6) 1 = 65 / 2 ∧
     hybridKappaSq 16384 (invPow2Rat 7) 1 = 129 / 2) := by
  have hL6 : hybridLowerConstSq (invPow2Rat 6) 1 = 1 / 16 := by
    unfold hybridLowerConstSq invPow2Rat pow2Rat; grind
  have hU4096 : hybridUpperConstSq 4096 (invPow2Rat 6) 1 = 65 / 32 := by
    unfold hybridUpperConstSq invPow2Rat pow2Rat; grind
  have hU8192 : hybridUpperConstSq 8192 (invPow2Rat 6) 1 = 97 / 32 := by
    unfold hybridUpperConstSq invPow2Rat pow2Rat; grind
  have hK4096 : hybridKappaSq 4096 (invPow2Rat 6) 1 = 65 / 2 := by
    unfold hybridKappaSq; rw [hU4096, hL6]; grind
  have hK8192 : hybridKappaSq 8192 (invPow2Rat 6) 1 = 97 / 2 := by
    unfold hybridKappaSq; rw [hU8192, hL6]; grind
  have hImp4096 : (4096 : Rat) / hybridKappaSq 4096 (invPow2Rat 6) 1 = 8192 / 65 := by
    rw [hK4096]; grind
  have hImp8192 : (8192 : Rat) / hybridKappaSq 8192 (invPow2Rat 6) 1 = 16384 / 97 := by
    rw [hK8192]; grind
  have hK64 : hybridKappaSq 64 (invPow2Rat 3) 1 = 9 / 2 := by
    unfold hybridKappaSq hybridUpperConstSq hybridLowerConstSq invPow2Rat pow2Rat; grind
  have hK256 : hybridKappaSq 256 (invPow2Rat 4) 1 = 17 / 2 := by
    unfold hybridKappaSq hybridUpperConstSq hybridLowerConstSq invPow2Rat pow2Rat; grind
  have hK1024 : hybridKappaSq 1024 (invPow2Rat 5) 1 = 33 / 2 := by
    unfold hybridKappaSq hybridUpperConstSq hybridLowerConstSq invPow2Rat pow2Rat; grind
  have hK16384 : hybridKappaSq 16384 (invPow2Rat 7) 1 = 129 / 2 := by
    unfold hybridKappaSq hybridUpperConstSq hybridLowerConstSq invPow2Rat pow2Rat; grind
  refine ⟨⟨hL6, hU4096, hK4096, hImp4096, by grind, ?_⟩,
          ⟨hL6, hU8192, hK8192, hImp8192, by grind, ?_⟩,
          ⟨hK64, hK256, hK1024, hK4096, hK16384⟩⟩
  · intro x
    have hlow := hybrid_lower_envelope_universal 4096 (by decide) (invPow2Rat 6) 1
      (invPow2Rat_pos 6) (by decide) x
    have hup := hybrid_upper_envelope_universal 4096 (by decide) (invPow2Rat 6) 1
      (invPow2Rat_pos 6) (by decide) x
    rw [hL6] at hlow
    rw [hU4096] at hup
    have hdyad : (1 : Rat) / (4096 : Nat) = invPow2Rat 12 := by
      unfold invPow2Rat pow2Rat; grind
    refine ⟨?_, hlow, hup⟩
    unfold hybridNorm
    rw [hdyad]
  · intro x
    have hlow := hybrid_lower_envelope_universal 8192 (by decide) (invPow2Rat 6) 1
      (invPow2Rat_pos 6) (by decide) x
    have hup := hybrid_upper_envelope_universal 8192 (by decide) (invPow2Rat 6) 1
      (invPow2Rat_pos 6) (by decide) x
    rw [hL6] at hlow
    rw [hU8192] at hup
    have hdyad : (1 : Rat) / (8192 : Nat) = invPow2Rat 13 := by
      unfold invPow2Rat pow2Rat; grind
    refine ⟨?_, hlow, hup⟩
    unfold hybridNorm
    rw [hdyad]

end RmsnormHybridLinfL1
