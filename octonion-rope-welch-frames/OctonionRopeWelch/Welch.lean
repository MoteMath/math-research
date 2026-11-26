/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OctonionRopeWelch.Defs

/-!
# Theorems 3 & 4: Universal Welch Frobenius Lower Bound & 5 Exact Welch-Tight Sparse Ternary Frames

Proves:
1. Universal integer Welch Frobenius lower bound (`welch_frame_energy_lower_bound`):
   For ALL `m d s : Nat` and ALL `S : IntMat m d` with column squared norm `s`,
   `(d * s)^2 ≤ m * (d * s^2 + Φ(S))` and `d * s^2 * (d - m) ≤ m * Φ(S)`.
2. Exact Welch tightness of ALL 5 GPU-discovered sparse ternary attention-key sketch frames
   (`(8, 16) s ∈ {3, 4, 5}`, `(12, 24) s ∈ {3, 4}`), achieving `ratio = 1.00000` with zero
   multiplications (`welch_tight_sparse_ternary_frames_exact`).
-/

namespace OctonionRopeWelch

/-! ## Finite Sum Algebra for `sumInt` -/

theorem sumInt_add {n : Nat} (f g : Fin n → Int) :
    sumInt (fun i => f i + g i) = sumInt f + sumInt g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumInt]
    rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc)]
    omega

theorem sumInt_sub {n : Nat} (f g : Fin n → Int) :
    sumInt (fun i => f i - g i) = sumInt f - sumInt g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumInt]
    rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc)]
    omega

theorem sumInt_const (n : Nat) (c : Int) :
    sumInt (fun _ : Fin n => c) = (n : Int) * c := by
  induction n with
  | zero => simp [sumInt]
  | succ k ih =>
    simp only [sumInt]
    rw [ih]
    grind

theorem sumInt_mul_left {n : Nat} (c : Int) (f : Fin n → Int) :
    sumInt (fun i => c * f i) = c * sumInt f := by
  induction n with
  | zero => simp [sumInt]
  | succ k ih =>
    simp only [sumInt]
    rw [ih (fun i => f i.castSucc), Int.mul_add]

theorem sumInt_mul_right {n : Nat} (f : Fin n → Int) (c : Int) :
    sumInt (fun i => f i * c) = sumInt f * c := by
  induction n with
  | zero => simp [sumInt]
  | succ k ih =>
    simp only [sumInt]
    rw [ih (fun i => f i.castSucc), Int.add_mul]

theorem sumInt_comm {m n : Nat} (f : Fin m → Fin n → Int) :
    sumInt (fun i => sumInt (fun j => f i j)) =
    sumInt (fun j => sumInt (fun i => f i j)) := by
  induction m with
  | zero =>
    simp only [sumInt]
    symm
    exact sumInt_const n 0 |>.trans (by simp)
  | succ k ih =>
    simp only [sumInt]
    rw [ih (fun i j => f i.castSucc j)]
    rw [← sumInt_add]

theorem sumInt_nonneg {n : Nat} (f : Fin n → Int) (h : ∀ i, 0 ≤ f i) :
    0 ≤ sumInt f := by
  induction n with
  | zero => simp [sumInt]
  | succ k ih =>
    simp only [sumInt]
    have h1 := ih (fun i => f i.castSucc) (fun i => h i.castSucc)
    have h2 := h ⟨k, Nat.lt_succ_self k⟩
    omega

theorem sumInt_le_sumInt {n : Nat} (f g : Fin n → Int) (h : ∀ i, f i ≤ g i) :
    sumInt f ≤ sumInt g := by
  induction n with
  | zero => simp [sumInt]
  | succ k ih =>
    simp only [sumInt]
    have h1 := ih (fun i => f i.castSucc) (fun i => g i.castSucc) (fun i => h i.castSucc)
    have h2 := h ⟨k, Nat.lt_succ_self k⟩
    omega

theorem sumInt_ite_eq {n : Nat} (j : Fin n) (f : Fin n → Int) :
    sumInt (fun i : Fin n => if i = j then f i else 0) = f j := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    simp only [sumInt]
    by_cases hlast : j.val = k
    · have hj : j = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext hlast
      subst hj
      have hzero : sumInt (fun i : Fin k => if i.castSucc = ⟨k, Nat.lt_succ_self k⟩ then f i.castSucc else 0) = 0 := by
        have hcongr : (fun i : Fin k => if i.castSucc = ⟨k, Nat.lt_succ_self k⟩ then f i.castSucc else 0) =
                      (fun _ : Fin k => (0 : Int)) := by
          funext i
          have hne : i.castSucc ≠ ⟨k, Nat.lt_succ_self k⟩ := by
            intro h
            have := congrArg Fin.val h
            exact Nat.ne_of_lt i.isLt this
          simp [hne]
        rw [hcongr, sumInt_const]
        simp
      rw [hzero]
      simp
    · have hjlt : j.val < k := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp j.isLt) hlast
      let j' : Fin k := ⟨j.val, hjlt⟩
      have hj : j = j'.castSucc := Fin.ext rfl
      rw [hj]
      have hne : ¬ (⟨k, Nat.lt_succ_self k⟩ = j'.castSucc) := by
        intro h
        have := congrArg Fin.val h
        exact Nat.ne_of_gt hjlt this
      simp only [hne, ite_false, Int.add_zero]
      have hcongr : (fun i : Fin k => if i.castSucc = j'.castSucc then f i.castSucc else 0) =
                    (fun i : Fin k => if i = j' then f i.castSucc else 0) := by
        funext i
        by_cases h : i = j'
        · subst h; simp
        · have h' : i.castSucc ≠ j'.castSucc := by
            intro hc
            have hv : i.val = j'.val := congrArg (fun x : Fin (k + 1) => x.val) hc
            exact h (Fin.ext hv)
          simp [h, h']
      rw [hcongr, ih j' (fun i => f i.castSucc)]

theorem sumInt_ite_eq_right {n : Nat} (i : Fin n) (f : Fin n → Int) :
    sumInt (fun j : Fin n => if i = j then f j else 0) = f i := by
  have h : (fun j : Fin n => if i = j then f j else 0) =
           (fun j : Fin n => if j = i then f j else 0) := by
    funext j
    by_cases hij : i = j
    · subst hij; simp
    · have hji : j ≠ i := fun hc => hij hc.symm
      simp [hij, hji]
  rw [h]
  exact sumInt_ite_eq i f

/-- Integer Cauchy–Schwarz inequality: `(∑_i a_i)^2 ≤ m * ∑_i a_i^2`. -/
theorem sumInt_cauchy_schwarz {m : Nat} (a : Fin m → Int) :
    sumInt a * sumInt a ≤ (m : Int) * sumInt (fun i => a i * a i) := by
  have hnonneg : 0 ≤ sumInt (fun i => sumInt (fun j => (a i - a j) * (a i - a j))) :=
    sumInt_nonneg _ (fun i => sumInt_nonneg _ (fun j => by
      cases Int.le_total 0 (a i - a j) with
      | inl h => exact Int.mul_nonneg h h
      | inr h => exact Int.mul_nonneg_of_nonpos_of_nonpos h h))
  have hexpand :
      sumInt (fun i => sumInt (fun j => (a i - a j) * (a i - a j))) =
      2 * ((m : Int) * sumInt (fun i => a i * a i) - sumInt a * sumInt a) := by
    have hpt : (fun i => sumInt (fun j => (a i - a j) * (a i - a j))) =
               (fun i => sumInt (fun j => a i * a i + a j * a j - 2 * (a i * a j))) := by
      funext i; congr 1; funext j; grind
    rw [hpt]
    have hinner : ∀ i : Fin m,
        sumInt (fun j => a i * a i + a j * a j - 2 * (a i * a j)) =
        (m : Int) * (a i * a i) + sumInt (fun j => a j * a j) - 2 * (a i * sumInt a) := by
      intro i
      rw [sumInt_sub, sumInt_add, sumInt_const, sumInt_mul_left, sumInt_mul_left]
    have hfun : (fun i => sumInt (fun j => a i * a i + a j * a j - 2 * (a i * a j))) =
                (fun i => (m : Int) * (a i * a i) + sumInt (fun j => a j * a j) - 2 * (a i * sumInt a)) := by
      funext i; exact hinner i
    rw [hfun, sumInt_sub, sumInt_add, sumInt_mul_left, sumInt_const, sumInt_mul_left, sumInt_mul_right]
    grind
  rw [hexpand] at hnonneg
  omega

/-! ## Frobenius Identity & Universal Welch Lower Bound (Theorem 3) -/

/-- Row inner product `(S S^T)_{i1, i2} = ∑_j S_{i1, j} * S_{i2, j}`. -/
def rowInner {m d : Nat} (S : IntMat m d) (i1 i2 : Fin m) : Int :=
  sumInt (fun j => S i1 j * S i2 j)

/-- Exact Frobenius norm duality `‖S^T S‖_F^2 = ‖S S^T‖_F^2`. -/
theorem frobenius_gram_eq_frame {m d : Nat} (S : IntMat m d) :
    sumInt (fun j1 => sumInt (fun j2 => colInner S j1 j2 * colInner S j1 j2)) =
    sumInt (fun i1 => sumInt (fun i2 => rowInner S i1 i2 * rowInner S i1 i2)) := by
  have hL :
      sumInt (fun j1 => sumInt (fun j2 => colInner S j1 j2 * colInner S j1 j2)) =
      sumInt (fun j1 => sumInt (fun j2 => sumInt (fun i1 => sumInt (fun i2 =>
        (S i1 j1 * S i2 j1) * (S i1 j2 * S i2 j2))))) := by
    congr 1; funext j1; congr 1; funext j2
    simp only [colInner]
    rw [← sumInt_mul_right]
    congr 1; funext i1
    rw [← sumInt_mul_left]
    congr 1; funext i2
    grind
  have hR :
      sumInt (fun i1 => sumInt (fun i2 => rowInner S i1 i2 * rowInner S i1 i2)) =
      sumInt (fun i1 => sumInt (fun i2 => sumInt (fun j1 => sumInt (fun j2 =>
        (S i1 j1 * S i2 j1) * (S i1 j2 * S i2 j2))))) := by
    congr 1; funext i1; congr 1; funext i2
    simp only [rowInner]
    rw [← sumInt_mul_right]
    congr 1; funext j1
    rw [← sumInt_mul_left]
  rw [hL, hR]
  -- Swap (j1, j2) with (i1, i2) using `sumInt_comm`
  rw [sumInt_comm (fun j1 j2 => sumInt (fun i1 => sumInt (fun i2 => (S i1 j1 * S i2 j1) * (S i1 j2 * S i2 j2))))]
  have s1 :
      sumInt (fun j2 => sumInt (fun j1 => sumInt (fun i1 => sumInt (fun i2 => (S i1 j1 * S i2 j1) * (S i1 j2 * S i2 j2))))) =
      sumInt (fun j2 => sumInt (fun i1 => sumInt (fun j1 => sumInt (fun i2 => (S i1 j1 * S i2 j1) * (S i1 j2 * S i2 j2))))) := by
    congr 1; funext j2; exact sumInt_comm _
  rw [s1, sumInt_comm]
  congr 1; funext i1
  have s2 :
      sumInt (fun j2 => sumInt (fun j1 => sumInt (fun i2 => (S i1 j1 * S i2 j1) * (S i1 j2 * S i2 j2)))) =
      sumInt (fun j2 => sumInt (fun i2 => sumInt (fun j1 => (S i1 j1 * S i2 j1) * (S i1 j2 * S i2 j2)))) := by
    congr 1; funext j2; exact sumInt_comm _
  rw [s2, sumInt_comm]
  congr 1; funext i2
  exact sumInt_comm _

/-- Splitting full Gram energy into diagonal `d * s^2` plus off-diagonal `Φ(S)`. -/
theorem full_gram_eq_diag_add_offDiag {m d s : Nat} (S : IntMat m d)
    (hcol : ∀ j : Fin d, colInner S j j = (s : Int)) :
    sumInt (fun j1 => sumInt (fun j2 => colInner S j1 j2 * colInner S j1 j2)) =
    (d : Int) * ((s : Int) * (s : Int)) + offDiagGramEnergy S := by
  have hsplit :
      sumInt (fun j1 => sumInt (fun j2 => colInner S j1 j2 * colInner S j1 j2)) =
      sumInt (fun j1 => sumInt (fun j2 =>
        (if j1 = j2 then colInner S j1 j2 * colInner S j1 j2 else 0) +
        (if j1 = j2 then 0 else colInner S j1 j2 * colInner S j1 j2))) := by
    congr 1; funext j1; congr 1; funext j2
    by_cases h : j1 = j2 <;> simp [h]
  rw [hsplit]
  have hadd :
      sumInt (fun j1 => sumInt (fun j2 =>
        (if j1 = j2 then colInner S j1 j2 * colInner S j1 j2 else 0) +
        (if j1 = j2 then 0 else colInner S j1 j2 * colInner S j1 j2))) =
      sumInt (fun j1 => sumInt (fun j2 => if j1 = j2 then colInner S j1 j2 * colInner S j1 j2 else 0)) +
      offDiagGramEnergy S := by
    simp only [offDiagGramEnergy]
    rw [← sumInt_add]
    congr 1; funext j1; exact sumInt_add _ _
  rw [hadd]
  congr 1
  have hdiag :
      sumInt (fun j1 => sumInt (fun j2 => if j1 = j2 then colInner S j1 j2 * colInner S j1 j2 else 0)) =
      sumInt (fun _ : Fin d => (s : Int) * (s : Int)) := by
    congr 1; funext j1
    rw [sumInt_ite_eq_right j1 (fun j2 => colInner S j1 j2 * colInner S j1 j2), hcol j1]
  rw [hdiag, sumInt_const]

/-- Headline Theorem 3: Universal Integer Welch Frobenius Lower Bound.
    For ANY `m d s : Nat` and ANY `m × d` integer matrix `S` whose columns all have squared norm `s`,
    `(d * s)^2 ≤ m * (d * s^2 + Φ(S))` and `d * s^2 * (d - m) ≤ m * Φ(S)`. -/
theorem welch_frame_energy_lower_bound (m d s : Nat) (S : IntMat m d)
    (hcol : ∀ j : Fin d, colInner S j j = (s : Int)) :
    ((d : Int) * (s : Int)) * ((d : Int) * (s : Int)) ≤
      (m : Int) * ((d : Int) * ((s : Int) * (s : Int)) + offDiagGramEnergy S) ∧
    (d : Int) * ((s : Int) * (s : Int)) * ((d : Int) - (m : Int)) ≤
      (m : Int) * offDiagGramEnergy S := by
  have htrace : sumInt (fun i => rowInner S i i) = (d : Int) * (s : Int) := by
    simp only [rowInner]
    rw [sumInt_comm]
    have hfun : (fun j : Fin d => sumInt (fun i : Fin m => S i j * S i j)) =
                (fun _ : Fin d => (s : Int)) := by
      funext j; exact hcol j
    rw [hfun, sumInt_const]
  have hcs : ((d : Int) * (s : Int)) * ((d : Int) * (s : Int)) ≤
             (m : Int) * sumInt (fun i => rowInner S i i * rowInner S i i) := by
    rw [← htrace]
    exact sumInt_cauchy_schwarz (fun i => rowInner S i i)
  have hdiag_le :
      sumInt (fun i => rowInner S i i * rowInner S i i) ≤
      sumInt (fun i1 => sumInt (fun i2 => rowInner S i1 i2 * rowInner S i1 i2)) := by
    apply sumInt_le_sumInt
    intro i1
    have h1 : rowInner S i1 i1 * rowInner S i1 i1 =
              sumInt (fun i2 => if i1 = i2 then rowInner S i1 i2 * rowInner S i1 i2 else 0) :=
      (sumInt_ite_eq_right i1 (fun i2 => rowInner S i1 i2 * rowInner S i1 i2)).symm
    rw [h1]
    apply sumInt_le_sumInt
    intro i2
    by_cases h : i1 = i2
    · simp [h]
    · simp only [h, ite_false]
      cases Int.le_total 0 (rowInner S i1 i2) with
      | inl hp => exact Int.mul_nonneg hp hp
      | inr hn => exact Int.mul_nonneg_of_nonpos_of_nonpos hn hn
  have hfull :
      sumInt (fun i1 => sumInt (fun i2 => rowInner S i1 i2 * rowInner S i1 i2)) =
      (d : Int) * ((s : Int) * (s : Int)) + offDiagGramEnergy S := by
    rw [← frobenius_gram_eq_frame S, full_gram_eq_diag_add_offDiag S hcol]
  have hm0 : (0 : Int) ≤ (m : Int) := Int.natCast_nonneg m
  have hmul : (m : Int) * sumInt (fun i => rowInner S i i * rowInner S i i) ≤
              (m : Int) * ((d : Int) * ((s : Int) * (s : Int)) + offDiagGramEnergy S) := by
    rw [← hfull]
    exact Int.mul_le_mul_of_nonneg_left hdiag_le hm0
  have hmain : ((d : Int) * (s : Int)) * ((d : Int) * (s : Int)) ≤
               (m : Int) * ((d : Int) * ((s : Int) * (s : Int)) + offDiagGramEnergy S) :=
    Int.le_trans hcs hmul
  refine ⟨hmain, ?_⟩
  grind

/-! ## Fast Algebraic Tightness Certificate & 5 Exact Welch-Tight Frames (Theorem 4) -/

/-- Any `m × d` matrix with column squared norm `s` and tight frame identity `S S^T = c I_m`
    (where `m * c = d * s`) automatically attains EXACT equality in the Welch Frobenius bound! -/
theorem welch_tight_of_rowOrthogonal {m d s : Nat} (c : Int) (S : IntMat m d)
    (hcol : ∀ j : Fin d, colInner S j j = (s : Int))
    (hrow : ∀ i1 i2 : Fin m, rowInner S i1 i2 = if i1 = i2 then c else 0)
    (hmc : (m : Int) * c = (d : Int) * (s : Int)) :
    (m : Int) * offDiagGramEnergy S = (d : Int) * ((s : Int) * (s : Int)) * ((d : Int) - (m : Int)) := by
  have hfull :
      (d : Int) * ((s : Int) * (s : Int)) + offDiagGramEnergy S =
      sumInt (fun i1 => sumInt (fun i2 => rowInner S i1 i2 * rowInner S i1 i2)) := by
    rw [← full_gram_eq_diag_add_offDiag S hcol, frobenius_gram_eq_frame S]
  have hsum :
      sumInt (fun i1 => sumInt (fun i2 => rowInner S i1 i2 * rowInner S i1 i2)) =
      (m : Int) * (c * c) := by
    have h1 : (fun i1 : Fin m => sumInt (fun i2 : Fin m => rowInner S i1 i2 * rowInner S i1 i2)) =
              (fun _ : Fin m => c * c) := by
      funext i1
      have h2 : (fun i2 : Fin m => rowInner S i1 i2 * rowInner S i1 i2) =
                (fun i2 : Fin m => if i1 = i2 then c * c else 0) := by
        funext i2
        rw [hrow i1 i2]
        by_cases h : i1 = i2 <;> simp [h]
      rw [h2, sumInt_ite_eq_right i1 (fun _ => c * c)]
    rw [h1, sumInt_const]
  rw [hsum] at hfull
  have hsq : (m : Int) * ((m : Int) * (c * c)) = ((d : Int) * (s : Int)) * ((d : Int) * (s : Int)) := by
    have : (m : Int) * ((m : Int) * (c * c)) = ((m : Int) * c) * ((m : Int) * c) := by grind
    rw [this, hmc]
  grind

private theorem decodeBitmaskFrame_isTernary (m d : Nat) (pos neg : Fin d → Nat) :
    ∀ i j, isTernary (decodeBitmaskFrame m d pos neg i j) := by
  intro i j
  simp only [decodeBitmaskFrame, isTernary]
  by_cases h1 : Nat.testBit (pos j) i.val
  · simp [h1]
  · by_cases h2 : Nat.testBit (neg j) i.val
    · simp [h1, h2]
    · simp [h1, h2]

private theorem frame_8_16_s3_tight : isWelchTightSparseTernaryFrame 3 1 frame_8_16_s3 := by
  refine ⟨decodeBitmaskFrame_isTernary _ _ _ _, by decide, by decide, by decide, ?_⟩
  exact welch_tight_of_rowOrthogonal 6 frame_8_16_s3 (by decide) (by decide) (by decide)

private theorem frame_8_16_s4_tight : isWelchTightSparseTernaryFrame 4 2 frame_8_16_s4 := by
  refine ⟨decodeBitmaskFrame_isTernary _ _ _ _, by decide, by decide, by decide, ?_⟩
  exact welch_tight_of_rowOrthogonal 8 frame_8_16_s4 (by decide) (by decide) (by decide)

private theorem frame_8_16_s5_tight : isWelchTightSparseTernaryFrame 5 2 frame_8_16_s5 := by
  refine ⟨decodeBitmaskFrame_isTernary _ _ _ _, by decide, by decide, by decide, ?_⟩
  exact welch_tight_of_rowOrthogonal 10 frame_8_16_s5 (by decide) (by decide) (by decide)

private theorem frame_12_24_s3_tight : isWelchTightSparseTernaryFrame 3 1 frame_12_24_s3 := by
  refine ⟨decodeBitmaskFrame_isTernary _ _ _ _, by decide, by decide, by decide, ?_⟩
  exact welch_tight_of_rowOrthogonal 6 frame_12_24_s3 (by decide) (by decide) (by decide)

private theorem frame_12_24_s4_tight : isWelchTightSparseTernaryFrame 4 1 frame_12_24_s4 := by
  refine ⟨decodeBitmaskFrame_isTernary _ _ _ _, by decide, by decide, by decide, ?_⟩
  exact welch_tight_of_rowOrthogonal 8 frame_12_24_s4 (by decide) (by decide) (by decide)

/-- Headline Theorem 4: All 5 GPU-discovered sparse ternary attention-key sketch matrices
    are exact Welch-tight frames (`ratio = 1.00000`, zero multiplications). -/
theorem welch_tight_sparse_ternary_frames_exact :
    isWelchTightSparseTernaryFrame 3 1 frame_8_16_s3 ∧
    isWelchTightSparseTernaryFrame 4 2 frame_8_16_s4 ∧
    isWelchTightSparseTernaryFrame 5 2 frame_8_16_s5 ∧
    isWelchTightSparseTernaryFrame 3 1 frame_12_24_s3 ∧
    isWelchTightSparseTernaryFrame 4 1 frame_12_24_s4 :=
  ⟨frame_8_16_s3_tight, frame_8_16_s4_tight, frame_8_16_s5_tight,
   frame_12_24_s3_tight, frame_12_24_s4_tight⟩

end OctonionRopeWelch
