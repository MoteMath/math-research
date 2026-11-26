/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MhcSinkhornFp8.RatLinAlg

/-!
# Theorems 2 & 4: Bit-Exact BF16 / FP8-E4M3FN Anti-Diagonal Swamping & Mode-B Fixed Points

2. `antidiagonal_swamping_bf16_fp8_fixed_point`:
   Proves that `bf16AntiDiag n` (`u = 2^-8`, `eps = 2^-14`) and `fp8AntiDiag n` (`u = 2^-4`,
   `eps = 2^-9`) at `n = 4, 8, 16` have hardware sequential RNE row/column sum identically
   equal to `1.0`, are permanent fixed points of Mode-A Sinkhorn for ALL `T : Nat`, have exact
   rational max row/column sums `259/256, 263/256, 271/256` (BF16) and `19/16, 23/16, 31/16`
   (FP8-E4M3FN), satisfy `‖H ones‖_2^2 > ‖ones‖_2^2`, and exhibit certified exponential
   `L`-layer blowup for ALL `L : Nat`.

4. `mode_b_exact_sum_symmetric_overshoot_fixed_point`:
   Proves that `fp8ModeBFixed4` (`I + (5/512)(J - I)`) and `bf16ModeBFixed4`
   (`I + (85/131072)(J - I)`) are permanent fixed points of Mode-B exact-sum Sinkhorn for ALL
   `T : Nat`, attain exact spectral norms `527/512` (FP8) and `131327/131072` (BF16) (both
   attainment and universal upper bound), and certify `L = 128` amplification (`> 40` for FP8,
   `> 32/25` for BF16).
-/

namespace MhcSinkhornFp8

/-! ### 1. Structural Lemmas for Sequential RNE Summation on `antiDiagBits` -/

/-- Repeated left-to-right addition of `k` copies of `eps` starting from `0`. -/
def iterAdd (add : Nat → Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, eps => add (iterAdd add k eps) eps

theorem seqSumFin_congr (add : Nat → Nat → Nat) {n : Nat} {f g : Fin n → Nat}
    (h : ∀ i, f i = g i) : seqSumFin add n f = seqSumFin add n g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [seqSumFin]
    rw [ih (fun i => h i.castSucc), h (Fin.last m)]

theorem seqSumFin_const (add : Nat → Nat → Nat) (k eps : Nat) :
    seqSumFin add k (fun _ => eps) = iterAdd add k eps := by
  induction k with
  | zero => rfl
  | succ m ih =>
    simp only [seqSumFin, iterAdd]
    rw [ih]

/-- Key structural swamping lemma: if `f` equals `eps` on `0..p-1`, `one` at `p`, and `u` on `p+1..n-1`,
    with `add (iterAdd add p eps) one = one` and `add one u = one`, then `seqSumFin add n f = one`. -/
theorem seqSumFin_swamp (add : Nat → Nat → Nat) (n p one u eps : Nat) (hp : p < n)
    (hpref : add (iterAdd add p eps) one = one)
    (hswamp : add one u = one) :
    seqSumFin add n (fun j => if j.val = p then one else if j.val > p then u else eps) = one := by
  induction n with
  | zero => omega
  | succ m ih =>
    simp only [seqSumFin, Fin.val_castSucc, Fin.val_last]
    by_cases hpm : p = m
    · subst hpm
      have hleft : seqSumFin add p (fun j : Fin p =>
          if j.val = p then one else if j.val > p then u else eps) =
          seqSumFin add p (fun _ : Fin p => eps) := by
        apply seqSumFin_congr
        intro j
        have hj : j.val < p := j.isLt
        have h1 : j.val ≠ p := by omega
        have h2 : ¬(j.val > p) := by omega
        simp [h1, h2]
      rw [hleft, seqSumFin_const]
      simp only [↓reduceIte]
      exact hpref
    · have hlt : p < m := by omega
      have h1 : m ≠ p := by omega
      have h2 : m > p := by omega
      rw [ih hlt]
      simp only [h1, h2, ↓reduceIte]
      exact hswamp

theorem antiDiagBits_symm (n one u eps : Nat) (i j : Fin n) :
    antiDiagBits n one u eps i j = antiDiagBits n one u eps j i := by
  simp only [antiDiagBits, Nat.add_comm]

theorem hwRowSum_antiDiagBits (fmt : FloatFormat) (n one u eps : Nat)
    (hpref : ∀ k < n, fmt.add (iterAdd fmt.add k eps) one = one)
    (hswamp : fmt.add one u = one) (i : Fin n) :
    hwRowSum fmt (antiDiagBits n one u eps) i = one := by
  simp only [hwRowSum]
  have hp : n - 1 - i.val < n := by omega
  have hcongr : ∀ j : Fin n,
      antiDiagBits n one u eps i j =
      if j.val = n - 1 - i.val then one else if j.val > n - 1 - i.val then u else eps := by
    intro j
    have hi : i.val < n := i.isLt
    simp only [antiDiagBits]
    split
    · next heq =>
      split
      · rfl
      · next h1 => omega
    · next hne =>
      split
      · next hgt =>
        split
        · next h1 => omega
        · split
          · rfl
          · next h2 => omega
      · next hngt =>
        split
        · next h1 => omega
        · split
          · next h2 => omega
          · rfl
  rw [seqSumFin_congr fmt.add hcongr]
  exact seqSumFin_swamp fmt.add n (n - 1 - i.val) one u eps hp (hpref _ hp) hswamp

theorem hwColSum_antiDiagBits (fmt : FloatFormat) (n one u eps : Nat)
    (hpref : ∀ k < n, fmt.add (iterAdd fmt.add k eps) one = one)
    (hswamp : fmt.add one u = one) (j : Fin n) :
    hwColSum fmt (antiDiagBits n one u eps) j = one := by
  simp only [hwColSum]
  have hcongr : ∀ i : Fin n, antiDiagBits n one u eps i j = antiDiagBits n one u eps j i :=
    fun i => antiDiagBits_symm n one u eps i j
  rw [seqSumFin_congr fmt.add hcongr]
  exact hwRowSum_antiDiagBits fmt n one u eps hpref hswamp j

/-- General Mode-A permanent fixed-point theorem for `antiDiagBits`. -/
theorem sinkhornModeA_antiDiag_fixed (fmt : FloatFormat) (n one u eps : Nat)
    (hone_ne : one ≠ 0)
    (hpref : ∀ k < n, fmt.add (iterAdd fmt.add k eps) one = one)
    (hswamp : fmt.add one u = one)
    (hdiv_one : fmt.div one one = one)
    (hdiv_u : fmt.div u one = u)
    (hdiv_eps : fmt.div eps one = eps) :
    sinkhornModeAStep fmt (antiDiagBits n one u eps) = antiDiagBits n one u eps ∧
    ∀ T : Nat, sinkhornModeAIter fmt T (antiDiagBits n one u eps) = antiDiagBits n one u eps := by
  have hdiv_entry : ∀ i j : Fin n,
      fmt.div (antiDiagBits n one u eps i j) one = antiDiagBits n one u eps i j := by
    intro i j
    simp only [antiDiagBits]
    split
    · exact hdiv_one
    · split
      · exact hdiv_u
      · exact hdiv_eps
  have hrow : sinkhornModeARow fmt (antiDiagBits n one u eps) = antiDiagBits n one u eps := by
    funext i j
    simp only [sinkhornModeARow, hwRowSum_antiDiagBits fmt n one u eps hpref hswamp i,
      hone_ne, ↓reduceIte]
    exact hdiv_entry i j
  have hcol : sinkhornModeACol fmt (antiDiagBits n one u eps) = antiDiagBits n one u eps := by
    funext i j
    simp only [sinkhornModeACol, hwColSum_antiDiagBits fmt n one u eps hpref hswamp j,
      hone_ne, ↓reduceIte]
    exact hdiv_entry i j
  have hstep : sinkhornModeAStep fmt (antiDiagBits n one u eps) = antiDiagBits n one u eps := by
    simp only [sinkhornModeAStep, hrow, hcol]
  refine ⟨hstep, ?_⟩
  intro T
  induction T with
  | zero => rfl
  | succ t ih => simp only [sinkhornModeAIter, ih, hstep]

/-! ### 2. Exact Rational Row/Column Sums & Spectral Blowup for `antiDiagBits` -/

theorem sumFinRat_antiDiag_row (n : Nat) (p : Nat) (hp : p < n) (U E : Rat) :
    sumFinRat n (fun j : Fin n => if j.val = p then (1 : Rat) else if j.val > p then U else E) =
    1 + ((n - 1 - p : Nat) : Rat) * U + (p : Rat) * E := by
  induction n with
  | zero => omega
  | succ m ih =>
    simp only [sumFinRat, Fin.val_castSucc, Fin.val_last]
    by_cases hpm : p = m
    · subst hpm
      have hleft : sumFinRat p (fun j : Fin p =>
          if j.val = p then (1 : Rat) else if j.val > p then U else E) =
          sumFinRat p (fun _ : Fin p => E) := by
        apply sumFinRat_congr
        intro j
        have hj := j.isLt
        have h1 : j.val ≠ p := by omega
        have h2 : ¬(j.val > p) := by omega
        simp [h1, h2]
      rw [hleft, sumFinRat_const]
      simp only [↓reduceIte]
      have h0 : p + 1 - 1 - p = 0 := by omega
      rw [h0]; simp; grind
    · have hlt : p < m := by omega
      have h1 : m ≠ p := by omega
      have h2 : m > p := by omega
      rw [ih hlt]
      simp only [h1, h2, ↓reduceIte]
      have hstep : m + 1 - 1 - p = (m - 1 - p) + 1 := by omega
      rw [hstep, Rat.natCast_add]
      grind

theorem antiDiag_rat_rowSum (fmt : FloatFormat) (n one u eps : Nat) (U E : Rat)
    (h1 : fmt.toRat one = 1) (hU : fmt.toRat u = U) (hE : fmt.toRat eps = E) (i : Fin n) :
    rowSum (bitsMatToRat fmt (antiDiagBits n one u eps)) i =
    1 + (i.val : Rat) * U + ((n - 1 - i.val : Nat) : Rat) * E := by
  simp only [rowSum, bitsMatToRat]
  have hi := i.isLt
  have hp : n - 1 - i.val < n := by omega
  have hcongr : ∀ j : Fin n,
      fmt.toRat (antiDiagBits n one u eps i j) =
      if j.val = n - 1 - i.val then (1 : Rat) else if j.val > n - 1 - i.val then U else E := by
    intro j
    simp only [antiDiagBits]
    split
    · next heq =>
      split
      · exact h1
      · next h1' => omega
    · next hne =>
      split
      · next hgt =>
        split
        · next h1' => omega
        · split
          · exact hU
          · next h2' => omega
      · next hngt =>
        split
        · next h1' => omega
        · split
          · next h2' => omega
          · exact hE
  rw [sumFinRat_congr hcongr, sumFinRat_antiDiag_row n (n - 1 - i.val) hp U E]
  have hsub : n - 1 - (n - 1 - i.val) = i.val := by omega
  rw [hsub]

theorem antiDiag_rat_colSum (fmt : FloatFormat) (n one u eps : Nat) (U E : Rat)
    (h1 : fmt.toRat one = 1) (hU : fmt.toRat u = U) (hE : fmt.toRat eps = E) (j : Fin n) :
    colSum (bitsMatToRat fmt (antiDiagBits n one u eps)) j =
    1 + (j.val : Rat) * U + ((n - 1 - j.val : Nat) : Rat) * E := by
  simp only [colSum, bitsMatToRat]
  have hcongr : ∀ i : Fin n,
      fmt.toRat (antiDiagBits n one u eps i j) = fmt.toRat (antiDiagBits n one u eps j i) :=
    fun i => congrArg fmt.toRat (antiDiagBits_symm n one u eps i j)
  rw [sumFinRat_congr hcongr]
  exact antiDiag_rat_rowSum fmt n one u eps U E h1 hU hE j

/-- Spectral overshoot & exponential `L`-layer blowup for any `antiDiagBits` with `0 < E ≤ U`. -/
theorem antiDiag_spectral_blowup (fmt : FloatFormat) (n one u eps : Nat) (hn : 2 ≤ n)
    (U E : Rat) (h1 : fmt.toRat one = 1) (hU : fmt.toRat u = U) (hE : fmt.toRat eps = E)
    (hE_pos : (0 : Rat) < E) (hEU : E ≤ U) :
    let H := bitsMatToRat fmt (antiDiagBits n one u eps)
    let lam := 1 + ((n - 1 : Nat) : Rat) * E
    normSq (onesVec n) < normSq (matVecMul H (onesVec n)) ∧
    (1 : Rat) < lam ∧
    ∀ L : Nat, ratPow lam L * ratPow lam L * normSq (onesVec n) ≤
      normSq (vecApplyIter H L (onesVec n)) := by
  intro H lam
  have hH_nn : ∀ i j : Fin n, (0 : Rat) ≤ H i j := by
    intro i j
    simp only [H, bitsMatToRat, antiDiagBits]
    split
    · rw [h1]; decide
    · split
      · rw [hU]; exact Rat.le_trans (Rat.le_of_lt hE_pos) hEU
      · rw [hE]; exact Rat.le_of_lt hE_pos
  have hH_ones : ∀ i : Fin n, matVecMul H (onesVec n) i = rowSum H i := by
    intro i
    simp only [matVecMul, rowSum, onesVec]
    exact sumFinRat_congr (fun j => by grind)
  have hrow_ge_lam : ∀ i : Fin n, lam ≤ rowSum H i := by
    intro i
    rw [antiDiag_rat_rowSum fmt n one u eps U E h1 hU hE i]
    have hi := i.isLt
    have hsplit : ((n - 1 : Nat) : Rat) = (i.val : Rat) + ((n - 1 - i.val : Nat) : Rat) := by
      have : n - 1 = i.val + (n - 1 - i.val) := by omega
      conv => lhs; rw [this]
      rw [Rat.natCast_add]
    have hlam_eq : lam = 1 + (i.val : Rat) * E + ((n - 1 - i.val : Nat) : Rat) * E := by
      simp only [lam, hsplit]; grind
    rw [hlam_eq]
    have hmul : (i.val : Rat) * E ≤ (i.val : Rat) * U :=
      rat_mul_le_mul_of_nonneg_left hEU (rat_natCast_nonneg i.val)
    have hadd1 := rat_add_le_add (Rat.le_refl (a := (1 : Rat))) hmul
    exact rat_add_le_add hadd1 (Rat.le_refl)
  have hlam_gt1 : (1 : Rat) < lam := by
    have hn1 : (0 : Rat) < ((n - 1 : Nat) : Rat) := rat_natCast_pos (by omega)
    have hp : (0 : Rat) < ((n - 1 : Nat) : Rat) * E := rat_mul_pos hn1 hE_pos
    have h := rat_add_pos_of_nonneg_of_pos (Rat.le_refl (a := (0 : Rat))) hp
    simp only [lam]
    have hle : (1 : Rat) ≤ 1 + ((n - 1 : Nat) : Rat) * E := by
      have h0 := rat_add_le_add (Rat.le_refl (a := (1 : Rat))) (Rat.le_of_lt hp)
      rw [Rat.add_zero] at h0; exact h0
    have hne : (1 : Rat) ≠ 1 + ((n - 1 : Nat) : Rat) * E := by
      intro heq
      have : ((n - 1 : Nat) : Rat) * E = 0 := by grind
      exact Rat.ne_of_gt hp this
    exact Rat.lt_of_le_of_ne hle hne
  have hlam_nn : (0 : Rat) ≤ lam := Rat.le_trans (by decide : (0 : Rat) ≤ 1) (Rat.le_of_lt hlam_gt1)
  have hstep : ∀ i : Fin n, lam * onesVec n i ≤ matVecMul H (onesVec n) i := by
    intro i
    rw [hH_ones i]
    simp only [onesVec]
    have : lam * 1 = lam := by grind
    rw [this]
    exact hrow_ge_lam i
  have hcw := vecApplyIter_collatz_wielandt hH_nn (fun _ => by simp only [onesVec]; decide) hlam_nn hstep
  have hray : normSq (onesVec n) < normSq (matVecMul H (onesVec n)) := by
    have h1_step := (hcw 1).2
    simp only [vecApplyIter, ratPow] at h1_step
    have hns_ones : normSq (onesVec n) = (n : Rat) := by
      simp only [normSq, onesVec]
      have : sumFinRat n (fun _ : Fin n => (1 : Rat) * 1) = sumFinRat n (fun _ : Fin n => (1 : Rat)) :=
        sumFinRat_congr (fun _ => by grind)
      rw [this, sumFinRat_const]; grind
    have hns_pos : (0 : Rat) < normSq (onesVec n) := by
      rw [hns_ones]; exact rat_natCast_pos (by omega)
    have hlam2_gt1 : (1 : Rat) < lam * lam := by
      have hmul1 : lam * 1 ≤ lam * lam :=
        rat_mul_le_mul_of_nonneg_left (Rat.le_of_lt hlam_gt1) hlam_nn
      have hle : (1 : Rat) ≤ lam * lam := Rat.le_trans (Rat.le_of_lt hlam_gt1) (by simpa using hmul1)
      have hne : (1 : Rat) ≠ lam * lam := by
        intro heq
        have hdiff : (lam - 1) * (lam + 1) = 0 := by grind
        cases Rat.mul_eq_zero.mp hdiff with
        | inl h0 => exact Rat.ne_of_gt (rat_sub_pos hlam_gt1) h0
        | inr h0 =>
          have hpos : (0 : Rat) < lam + 1 := rat_add_pos_of_pos_of_nonneg
            (Rat.lt_of_le_of_ne hlam_nn (Ne.symm (by intro hz; rw [hz] at hlam_gt1; exact Rat.not_le.mpr hlam_gt1 (by decide))))
            (by decide)
          exact Rat.ne_of_gt hpos h0
      exact Rat.lt_of_le_of_ne hle hne
    have hstrict : normSq (onesVec n) < lam * lam * normSq (onesVec n) := by
      have hdiff : (0 : Rat) < (lam * lam - 1) * normSq (onesVec n) :=
        rat_mul_pos (rat_sub_pos hlam2_gt1) hns_pos
      have heq : lam * lam * normSq (onesVec n) - normSq (onesVec n) =
          (lam * lam - 1) * normSq (onesVec n) := by grind
      have hpos : (0 : Rat) < lam * lam * normSq (onesVec n) - normSq (onesVec n) := by
        rw [heq]; exact hdiff
      have hle : normSq (onesVec n) ≤ lam * lam * normSq (onesVec n) :=
        rat_le_of_sub_nonneg (Rat.le_of_lt hpos)
      have hne : normSq (onesVec n) ≠ lam * lam * normSq (onesVec n) := by
        intro heq'
        have h0 : lam * lam * normSq (onesVec n) - normSq (onesVec n) = 0 := by grind
        rw [h0] at hpos; exact Rat.not_le.mpr hpos Rat.le_refl
      exact Rat.lt_of_le_of_ne hle hne
    have hrew : lam * 1 * (lam * 1) * normSq (onesVec n) = lam * lam * normSq (onesVec n) := by grind
    rw [hrew] at h1_step
    have hle_tot : normSq (onesVec n) ≤ normSq (matVecMul H (onesVec n)) :=
      Rat.le_trans (Rat.le_of_lt hstrict) h1_step
    have hne_tot : normSq (onesVec n) ≠ normSq (matVecMul H (onesVec n)) := by
      intro heq; rw [← heq] at h1_step
      exact Rat.not_le.mpr hstrict h1_step
    exact Rat.lt_of_le_of_ne hle_tot hne_tot
  exact ⟨hray, hlam_gt1, fun L => (hcw L).2⟩

/-! ### 3. Concrete Bit-Exact RNE Certificates for BF16 and FP8-E4M3FN -/

theorem bf16_toRat_one : bf16ToRat 0x3F80 = 1 := by
  have h : bf16NumDen 0x3F80 = (128, 128) := by decide
  simp only [bf16ToRat, h]; grind

theorem bf16_toRat_u : bf16ToRat 0x3B80 = (1 : Rat) / 256 := by
  have h : bf16NumDen 0x3B80 = (128, 32768) := by decide
  simp only [bf16ToRat, h]; grind

theorem bf16_toRat_eps : bf16ToRat 0x3880 = (1 : Rat) / 16384 := by
  have h : bf16NumDen 0x3880 = (128, 2097152) := by decide
  simp only [bf16ToRat, h]; grind

theorem bf16_swamp_u : bf16Add 0x3F80 0x3B80 = 0x3F80 := by decide
theorem bf16_div_one : bf16Div 0x3F80 0x3F80 = 0x3F80 := by decide
theorem bf16_div_u : bf16Div 0x3B80 0x3F80 = 0x3B80 := by decide
theorem bf16_div_eps : bf16Div 0x3880 0x3F80 = 0x3880 := by decide

theorem bf16_swamp_prefix :
    ∀ k < 16, bf16Add (iterAdd bf16Add k 0x3880) 0x3F80 = 0x3F80 := by
  intro k hk
  match k with
  | 0 => decide | 1 => decide | 2 => decide | 3 => decide
  | 4 => decide | 5 => decide | 6 => decide | 7 => decide
  | 8 => decide | 9 => decide | 10 => decide | 11 => decide
  | 12 => decide | 13 => decide | 14 => decide | 15 => decide
  | k + 16 => omega

theorem fp8_toRat_one : fp8ToRat 0x38 = 1 := by
  have h : fp8NumDen 0x38 = (512, 512) := by decide
  simp only [fp8ToRat, h]; grind

theorem fp8_toRat_u : fp8ToRat 0x18 = (1 : Rat) / 16 := by
  have h : fp8NumDen 0x18 = (32, 512) := by decide
  simp only [fp8ToRat, h]; grind

theorem fp8_toRat_eps : fp8ToRat 0x01 = (1 : Rat) / 512 := by
  have h : fp8NumDen 0x01 = (1, 512) := by decide
  simp only [fp8ToRat, h]; grind

theorem fp8_swamp_u : fp8Add 0x38 0x18 = 0x38 := by decide
theorem fp8_div_one : fp8Div 0x38 0x38 = 0x38 := by decide
theorem fp8_div_u : fp8Div 0x18 0x38 = 0x18 := by decide
theorem fp8_div_eps : fp8Div 0x01 0x38 = 0x01 := by decide

theorem fp8_swamp_prefix :
    ∀ k < 16, fp8Add (iterAdd fp8Add k 0x01) 0x38 = 0x38 := by
  intro k hk
  match k with
  | 0 => decide | 1 => decide | 2 => decide | 3 => decide
  | 4 => decide | 5 => decide | 6 => decide | 7 => decide
  | 8 => decide | 9 => decide | 10 => decide | 11 => decide
  | 12 => decide | 13 => decide | 14 => decide | 15 => decide
  | k + 16 => omega

/-- Theorem 2 (Anti-Diagonal Swamping Permanent Fixed-Point Law for BF16 & FP8-E4M3FN):
    For `n ∈ {4, 8, 16}` in both BF16 (`u = 2^-8`) and FP8-E4M3FN (`u = 2^-4`):
    1. Every sequential RNE row and column sum equals `1.0` (`0x3F80` / `0x38`), so `H_anti` is a
       permanent fixed point of Mode-A Sinkhorn for ALL `T : Nat`.
    2. True exact rational max row/column sum equals `259/256, 263/256, 271/256` (BF16) and
       `19/16, 23/16, 31/16` (FP8-E4M3FN).
    3. Certified Rayleigh-quotient spectral lower bound `‖H ones‖_2^2 > ‖ones‖_2^2` and
       exponential `L`-layer blowup `λ^(2L) ‖ones‖_2^2 ≤ ‖H^L ones‖_2^2` for ALL `L : Nat`. -/
theorem antidiagonal_swamping_bf16_fp8_fixed_point :
    (∀ n : Nat, 2 ≤ n → n ≤ 16 →
      (∀ i : Fin n, hwRowSum bf16Format (bf16AntiDiag n) i = 0x3F80) ∧
      (∀ j : Fin n, hwColSum bf16Format (bf16AntiDiag n) j = 0x3F80) ∧
      (∀ T : Nat, sinkhornModeAIter bf16Format T (bf16AntiDiag n) = bf16AntiDiag n) ∧
      normSq (onesVec n) < normSq (matVecMul (bitsMatToRat bf16Format (bf16AntiDiag n)) (onesVec n)) ∧
      (∀ L : Nat,
        ratPow (1 + ((n - 1 : Nat) : Rat) * ((1 : Rat) / 16384)) L *
        ratPow (1 + ((n - 1 : Nat) : Rat) * ((1 : Rat) / 16384)) L * normSq (onesVec n) ≤
        normSq (vecApplyIter (bitsMatToRat bf16Format (bf16AntiDiag n)) L (onesVec n)))) ∧
    (rowSum (bitsMatToRat bf16Format (bf16AntiDiag 4)) ⟨3, by omega⟩ = 259 / 256 ∧
     colSum (bitsMatToRat bf16Format (bf16AntiDiag 4)) ⟨3, by omega⟩ = 259 / 256 ∧
     rowSum (bitsMatToRat bf16Format (bf16AntiDiag 8)) ⟨7, by omega⟩ = 263 / 256 ∧
     colSum (bitsMatToRat bf16Format (bf16AntiDiag 8)) ⟨7, by omega⟩ = 263 / 256 ∧
     rowSum (bitsMatToRat bf16Format (bf16AntiDiag 16)) ⟨15, by omega⟩ = 271 / 256 ∧
     colSum (bitsMatToRat bf16Format (bf16AntiDiag 16)) ⟨15, by omega⟩ = 271 / 256) ∧
    (∀ n : Nat, 2 ≤ n → n ≤ 16 →
      (∀ i : Fin n, hwRowSum fp8Format (fp8AntiDiag n) i = 0x38) ∧
      (∀ j : Fin n, hwColSum fp8Format (fp8AntiDiag n) j = 0x38) ∧
      (∀ T : Nat, sinkhornModeAIter fp8Format T (fp8AntiDiag n) = fp8AntiDiag n) ∧
      normSq (onesVec n) < normSq (matVecMul (bitsMatToRat fp8Format (fp8AntiDiag n)) (onesVec n)) ∧
      (∀ L : Nat,
        ratPow (1 + ((n - 1 : Nat) : Rat) * ((1 : Rat) / 512)) L *
        ratPow (1 + ((n - 1 : Nat) : Rat) * ((1 : Rat) / 512)) L * normSq (onesVec n) ≤
        normSq (vecApplyIter (bitsMatToRat fp8Format (fp8AntiDiag n)) L (onesVec n)))) ∧
    (rowSum (bitsMatToRat fp8Format (fp8AntiDiag 4)) ⟨3, by omega⟩ = 19 / 16 ∧
     colSum (bitsMatToRat fp8Format (fp8AntiDiag 4)) ⟨3, by omega⟩ = 19 / 16 ∧
     rowSum (bitsMatToRat fp8Format (fp8AntiDiag 8)) ⟨7, by omega⟩ = 23 / 16 ∧
     colSum (bitsMatToRat fp8Format (fp8AntiDiag 8)) ⟨7, by omega⟩ = 23 / 16 ∧
     rowSum (bitsMatToRat fp8Format (fp8AntiDiag 16)) ⟨15, by omega⟩ = 31 / 16 ∧
     colSum (bitsMatToRat fp8Format (fp8AntiDiag 16)) ⟨15, by omega⟩ = 31 / 16) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn2 hn16
    have hpref : ∀ k < n, bf16Format.add (iterAdd bf16Format.add k 0x3880) 0x3F80 = 0x3F80 :=
      fun k hk => bf16_swamp_prefix k (by omega)
    have hfix := sinkhornModeA_antiDiag_fixed bf16Format n 0x3F80 0x3B80 0x3880
      (by decide) hpref bf16_swamp_u bf16_div_one bf16_div_u bf16_div_eps
    have hspec := antiDiag_spectral_blowup bf16Format n 0x3F80 0x3B80 0x3880 hn2
      ((1 : Rat) / 256) ((1 : Rat) / 16384) bf16_toRat_one bf16_toRat_u bf16_toRat_eps
      (rat_div_pos (by decide) (by decide))
      (by have : ((1 : Rat) / 16384) ≤ ((1 : Rat) / 256) := by
            apply rat_le_of_sub_nonneg
            have heq : (1 : Rat) / 256 - 1 / 16384 = 63 / 16384 := by grind
            rw [heq]; exact rat_div_nonneg (by decide) (by decide)
          exact this)
    exact ⟨hwRowSum_antiDiagBits bf16Format n 0x3F80 0x3B80 0x3880 hpref bf16_swamp_u,
           hwColSum_antiDiagBits bf16Format n 0x3F80 0x3B80 0x3880 hpref bf16_swamp_u,
           hfix.2, hspec.1, hspec.2.2⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold bf16AntiDiag
      rw [antiDiag_rat_rowSum bf16Format 4 0x3F80 0x3B80 0x3880 ((1 : Rat) / 256) ((1 : Rat) / 16384)
            bf16_toRat_one bf16_toRat_u bf16_toRat_eps]; grind
    · unfold bf16AntiDiag
      rw [antiDiag_rat_colSum bf16Format 4 0x3F80 0x3B80 0x3880 ((1 : Rat) / 256) ((1 : Rat) / 16384)
            bf16_toRat_one bf16_toRat_u bf16_toRat_eps]; grind
    · unfold bf16AntiDiag
      rw [antiDiag_rat_rowSum bf16Format 8 0x3F80 0x3B80 0x3880 ((1 : Rat) / 256) ((1 : Rat) / 16384)
            bf16_toRat_one bf16_toRat_u bf16_toRat_eps]; grind
    · unfold bf16AntiDiag
      rw [antiDiag_rat_colSum bf16Format 8 0x3F80 0x3B80 0x3880 ((1 : Rat) / 256) ((1 : Rat) / 16384)
            bf16_toRat_one bf16_toRat_u bf16_toRat_eps]; grind
    · unfold bf16AntiDiag
      rw [antiDiag_rat_rowSum bf16Format 16 0x3F80 0x3B80 0x3880 ((1 : Rat) / 256) ((1 : Rat) / 16384)
            bf16_toRat_one bf16_toRat_u bf16_toRat_eps]; grind
    · unfold bf16AntiDiag
      rw [antiDiag_rat_colSum bf16Format 16 0x3F80 0x3B80 0x3880 ((1 : Rat) / 256) ((1 : Rat) / 16384)
            bf16_toRat_one bf16_toRat_u bf16_toRat_eps]; grind
  · intro n hn2 hn16
    have hpref : ∀ k < n, fp8Format.add (iterAdd fp8Format.add k 0x01) 0x38 = 0x38 :=
      fun k hk => fp8_swamp_prefix k (by omega)
    have hfix := sinkhornModeA_antiDiag_fixed fp8Format n 0x38 0x18 0x01
      (by decide) hpref fp8_swamp_u fp8_div_one fp8_div_u fp8_div_eps
    have hspec := antiDiag_spectral_blowup fp8Format n 0x38 0x18 0x01 hn2
      ((1 : Rat) / 16) ((1 : Rat) / 512) fp8_toRat_one fp8_toRat_u fp8_toRat_eps
      (rat_div_pos (by decide) (by decide))
      (by apply rat_le_of_sub_nonneg
          have heq : (1 : Rat) / 16 - 1 / 512 = 31 / 512 := by grind
          rw [heq]; exact rat_div_nonneg (by decide) (by decide))
    exact ⟨hwRowSum_antiDiagBits fp8Format n 0x38 0x18 0x01 hpref fp8_swamp_u,
           hwColSum_antiDiagBits fp8Format n 0x38 0x18 0x01 hpref fp8_swamp_u,
           hfix.2, hspec.1, hspec.2.2⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold fp8AntiDiag
      rw [antiDiag_rat_rowSum fp8Format 4 0x38 0x18 0x01 ((1 : Rat) / 16) ((1 : Rat) / 512)
            fp8_toRat_one fp8_toRat_u fp8_toRat_eps]; grind
    · unfold fp8AntiDiag
      rw [antiDiag_rat_colSum fp8Format 4 0x38 0x18 0x01 ((1 : Rat) / 16) ((1 : Rat) / 512)
            fp8_toRat_one fp8_toRat_u fp8_toRat_eps]; grind
    · unfold fp8AntiDiag
      rw [antiDiag_rat_rowSum fp8Format 8 0x38 0x18 0x01 ((1 : Rat) / 16) ((1 : Rat) / 512)
            fp8_toRat_one fp8_toRat_u fp8_toRat_eps]; grind
    · unfold fp8AntiDiag
      rw [antiDiag_rat_colSum fp8Format 8 0x38 0x18 0x01 ((1 : Rat) / 16) ((1 : Rat) / 512)
            fp8_toRat_one fp8_toRat_u fp8_toRat_eps]; grind
    · unfold fp8AntiDiag
      rw [antiDiag_rat_rowSum fp8Format 16 0x38 0x18 0x01 ((1 : Rat) / 16) ((1 : Rat) / 512)
            fp8_toRat_one fp8_toRat_u fp8_toRat_eps]; grind
    · unfold fp8AntiDiag
      rw [antiDiag_rat_colSum fp8Format 16 0x38 0x18 0x01 ((1 : Rat) / 16) ((1 : Rat) / 512)
            fp8_toRat_one fp8_toRat_u fp8_toRat_eps]; grind

/-! ### 4. Theorem 4: Mode-B Exact-Sum Symmetric Overshoot Fixed Points -/

/-- Exact spectral norm of `a I + b J` (`0 ≤ a, 0 ≤ b`): `‖(a I + b J) u‖_2^2 ≤ (a + n b)^2 ‖u‖_2^2`. -/
theorem symDiag_spectral_upper {n : Nat} (a b : Rat) (ha : (0 : Rat) ≤ a) (hb : (0 : Rat) ≤ b)
    (u : RatVec n) :
    let M : RatMat n := fun i j => if i = j then a + b else b
    normSq (matVecMul M u) ≤ (a + (n : Rat) * b) * (a + (n : Rat) * b) * normSq u := by
  intro M
  let S : Rat := sumFinRat n u
  have hMu : ∀ i : Fin n, matVecMul M u i = a * u i + b * S := by
    intro i
    simp only [matVecMul, M, S]
    have hsplit : ∀ j : Fin n, (if i = j then a + b else b) * u j =
        (if i = j then a * u i else 0) + b * u j := by
      intro j
      by_cases h : i = j
      · subst h; simp; grind
      · simp [h]; grind
    rw [sumFinRat_congr hsplit, sumFinRat_add, sumFinRat_mul_left]
    have hdelta : sumFinRat n (fun j : Fin n => if i = j then a * u i else 0) = a * u i := by
      clear hsplit
      induction n with
      | zero => exact Fin.elim0 i
      | succ m ih =>
        simp only [sumFinRat]
        by_cases hl : i = Fin.last m
        · subst hl
          have h0 : sumFinRat m (fun j : Fin m => if Fin.last m = j.castSucc then a * u (Fin.last m) else 0) =
              sumFinRat m (fun _ => 0) := by
            apply sumFinRat_congr
            intro j
            have hne : Fin.last m ≠ j.castSucc := by
              intro heq
              have hv := congrArg Fin.val heq
              simp only [Fin.val_last, Fin.val_castSucc] at hv
              omega
            simp [hne]
          rw [h0, sumFinRat_zero]; simp; grind
        · have hlt : i.val < m := by
            have := i.isLt
            have hne : i.val ≠ m := fun hv => hl (Fin.ext hv)
            omega
          let i' : Fin m := ⟨i.val, hlt⟩
          have hleft : sumFinRat m (fun j : Fin m => if i = j.castSucc then a * u i else 0) =
              sumFinRat m (fun j : Fin m => if i' = j then a * u i'.castSucc else 0) := by
            apply sumFinRat_congr
            intro j
            have hiff : (i = j.castSucc) ↔ (i' = j) := by
              constructor
              · intro heq; apply Fin.ext; have hv := congrArg Fin.val heq; simpa [i'] using hv
              · intro heq; apply Fin.ext; have hv := congrArg Fin.val heq; simpa [i'] using hv
            have hui : u i = u i'.castSucc := congrArg u (Fin.ext rfl)
            simp [hiff, hui]
          rw [hleft, ih (fun k => u k.castSucc) i']
          have hlast : (if i = Fin.last m then a * u i else 0) = 0 := by simp [hl]
          rw [hlast, Rat.add_zero]
          exact congrArg (fun x => a * x) (congrArg u (Fin.ext rfl))
    rw [hdelta]
  have hns : normSq (matVecMul M u) =
      a * a * normSq u + (2 * a * b + (n : Rat) * b * b) * (S * S) := by
    simp only [normSq]
    have hterm : ∀ i : Fin n,
        matVecMul M u i * matVecMul M u i =
        (a * a * (u i * u i) + (2 * a * b * S) * u i) + (b * b * (S * S)) := by
      intro i; rw [hMu i]; grind
    rw [sumFinRat_congr hterm, sumFinRat_add, sumFinRat_add,
        sumFinRat_mul_left, sumFinRat_mul_left, sumFinRat_const]
    have hS : sumFinRat n u = S := rfl
    rw [hS]; grind
  rw [hns]
  have hcs : S * S ≤ (n : Rat) * normSq u := cauchy_schwarz_ones u
  have hcoeff_nn : (0 : Rat) ≤ 2 * a * b + (n : Rat) * b * b :=
    rat_add_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) ha) hb)
      (Rat.mul_nonneg (Rat.mul_nonneg (rat_natCast_nonneg n) hb) hb)
  have hmul := rat_mul_le_mul_of_nonneg_left hcs hcoeff_nn
  have htot := rat_add_le_add (Rat.le_refl (a := a * a * normSq u)) hmul
  have heq : a * a * normSq u + (2 * a * b + (n : Rat) * b * b) * ((n : Rat) * normSq u) =
      (a + (n : Rat) * b) * (a + (n : Rat) * b) * normSq u := by grind
  rw [heq] at htot
  exact htot

theorem ratPow_div_nat (p q : Nat) (hq : 0 < q) (L : Nat) :
    ratPow ((p : Rat) / (q : Rat)) L = ((p ^ L : Nat) : Rat) / ((q ^ L : Nat) : Rat) := by
  induction L with
  | zero =>
    simp only [ratPow, Nat.pow_zero]
    have : ((1 : Nat) : Rat) / ((1 : Nat) : Rat) = 1 := by grind
    exact this.symm
  | succ k ih =>
    simp only [ratPow, Nat.pow_succ, ih]
    have hq_ne : (q : Rat) ≠ 0 := Rat.ne_of_gt (rat_natCast_pos hq)
    have hqk_ne : ((q ^ k : Nat) : Rat) ≠ 0 :=
      Rat.ne_of_gt (rat_natCast_pos (Nat.pow_pos hq))
    have hmul_ne : ((q ^ k * q : Nat) : Rat) ≠ 0 :=
      Rat.ne_of_gt (rat_natCast_pos (Nat.mul_pos (Nat.pow_pos hq) hq))
    rw [Rat.natCast_mul, Rat.natCast_mul]
    have hcross : (((p : Rat) / (q : Rat)) * (((p ^ k : Nat) : Rat) / ((q ^ k : Nat) : Rat)) -
        ((p ^ k : Nat) : Rat) * (p : Rat) / (((q ^ k : Nat) : Rat) * (q : Rat))) *
        (((q ^ k : Nat) : Rat) * (q : Rat)) = 0 := by
      have h1 : ((p : Rat) / (q : Rat)) * (q : Rat) = (p : Rat) := rat_div_mul_cancel hq_ne
      have h2 : (((p ^ k : Nat) : Rat) / ((q ^ k : Nat) : Rat)) * ((q ^ k : Nat) : Rat) =
          ((p ^ k : Nat) : Rat) := rat_div_mul_cancel hqk_ne
      have h3 : (((p ^ k : Nat) : Rat) * (p : Rat) / (((q ^ k : Nat) : Rat) * (q : Rat))) *
          (((q ^ k : Nat) : Rat) * (q : Rat)) = ((p ^ k : Nat) : Rat) * (p : Rat) :=
        rat_div_mul_cancel (by
          intro hz
          cases Rat.mul_eq_zero.mp hz with
          | inl h => exact hqk_ne h
          | inr h => exact hq_ne h)
      grind
    cases Rat.mul_eq_zero.mp hcross with
    | inl h0 => grind
    | inr h0 =>
      cases Rat.mul_eq_zero.mp h0 with
      | inl h => exact False.elim (hqk_ne h)
      | inr h => exact False.elim (hq_ne h)

theorem rat_div_lt_div_nat_pos (a b c d : Nat) (hb : 0 < b) (hd : 0 < d) (h : a * d < c * b) :
    (a : Rat) / (b : Rat) < (c : Rat) / (d : Rat) := by
  have hbpos : (0 : Rat) < (b : Rat) := rat_natCast_pos hb
  have hdpos : (0 : Rat) < (d : Rat) := rat_natCast_pos hd
  have hbd : (0 : Rat) < (b : Rat) * (d : Rat) := rat_mul_pos hbpos hdpos
  have h1 : (a : Rat) / (b : Rat) * ((b : Rat) * (d : Rat)) = (a : Rat) * (d : Rat) := by
    have := rat_div_mul_cancel (a := (a : Rat)) (Rat.ne_of_gt hbpos)
    grind
  have h2 : (c : Rat) / (d : Rat) * ((b : Rat) * (d : Rat)) = (c : Rat) * (b : Rat) := by
    have := rat_div_mul_cancel (a := (c : Rat)) (Rat.ne_of_gt hdpos)
    grind
  have hnat_lt : (a : Rat) * (d : Rat) < (c : Rat) * (b : Rat) := by
    have hle : ((a * d : Nat) : Rat) ≤ ((c * b : Nat) : Rat) := rat_natCast_le (Nat.le_of_lt h)
    have hne : ((a * d : Nat) : Rat) ≠ ((c * b : Nat) : Rat) := by
      intro heq
      have hint : (((a * d : Nat) : Int) : Rat) = (((c * b : Nat) : Int) : Rat) := by
        simpa [Rat.intCast_natCast] using heq
      have := Rat.intCast_inj.mp hint
      omega
    rw [Rat.natCast_mul, Rat.natCast_mul] at hle hne
    exact Rat.lt_of_le_of_ne hle hne
  have hdiff_pos : (0 : Rat) < ((c : Rat) / (d : Rat) - (a : Rat) / (b : Rat)) * ((b : Rat) * (d : Rat)) := by
    have heq : ((c : Rat) / (d : Rat) - (a : Rat) / (b : Rat)) * ((b : Rat) * (d : Rat)) =
        (c : Rat) * (b : Rat) - (a : Rat) * (d : Rat) := by grind
    rw [heq]; exact rat_sub_pos hnat_lt
  cases Rat.le_total (a := (c : Rat) / (d : Rat)) (b := (a : Rat) / (b : Rat)) with
  | inl hge =>
    have hle0 : ((c : Rat) / (d : Rat) - (a : Rat) / (b : Rat)) * ((b : Rat) * (d : Rat)) ≤ 0 := by
      have hsub : (c : Rat) / (d : Rat) - (a : Rat) / (b : Rat) ≤ 0 := by
        have := rat_sub_nonneg hge; grind
      have := rat_mul_le_mul_of_nonneg_right hsub (Rat.le_of_lt hbd)
      rw [Rat.zero_mul] at this; exact this
    exact False.elim (Rat.not_le.mpr hdiff_pos hle0)
  | inr hle =>
    by_cases heq : (a : Rat) / (b : Rat) = (c : Rat) / (d : Rat)
    · rw [heq] at hdiff_pos
      have : ((c : Rat) / (d : Rat) - (c : Rat) / (d : Rat)) * ((b : Rat) * (d : Rat)) = 0 := by grind
      rw [this] at hdiff_pos
      exact False.elim (Rat.not_le.mpr hdiff_pos Rat.le_refl)
    · exact Rat.lt_of_le_of_ne hle heq

theorem fp8_modeB_delta : fp8ToRat 0x05 = (5 : Rat) / 512 := by
  have h : fp8NumDen 0x05 = (5, 512) := by decide
  simp only [fp8ToRat, h]; grind

theorem fp8_modeB_div_diag : ratToFp8 (1 / ((527 : Rat) / 512)) = 0x38 := by
  have h : (1 : Rat) / ((527 : Rat) / 512) = Rat.divInt 512 527 := by
    rw [Rat.divInt_eq_div]; grind
  rw [h]; decide

theorem fp8_modeB_div_off : ratToFp8 (((5 : Rat) / 512) / ((527 : Rat) / 512)) = 0x05 := by
  have h : ((5 : Rat) / 512) / ((527 : Rat) / 512) = Rat.divInt 5 527 := by
    rw [Rat.divInt_eq_div]; grind
  rw [h]; decide

theorem fp8_pow128_gt40 : 40 * (512 ^ 128) < 1 * (527 ^ 128) := by decide

theorem bf16_modeB_delta : bf16ToRat 0x3A2A = (85 : Rat) / 131072 := by
  have h : bf16NumDen 0x3A2A = (170, 262144) := by decide
  simp only [bf16ToRat, h]; grind

theorem bf16_modeB_div_diag : ratToBf16 (1 / ((131327 : Rat) / 131072)) = 0x3F80 := by
  have h : (1 : Rat) / ((131327 : Rat) / 131072) = Rat.divInt 131072 131327 := by
    rw [Rat.divInt_eq_div]; grind
  rw [h]; decide

theorem bf16_modeB_div_off : ratToBf16 (((85 : Rat) / 131072) / ((131327 : Rat) / 131072)) = 0x3A2A := by
  have h : ((85 : Rat) / 131072) / ((131327 : Rat) / 131072) = Rat.divInt 85 131327 := by
    rw [Rat.divInt_eq_div]; grind
  rw [h]; decide

theorem bf16_pow128_gt32_25 : 32 * (131072 ^ 128) < 25 * (131327 ^ 128) := by decide

/-- Helper: Mode-B fixed point for `symDiagBits 4 oneBits deltaBits`. -/
theorem sinkhornModeB_symDiag4_fixed (fmt : FloatFormat) (oneBits deltaBits : Nat) (d s : Rat)
    (h1 : fmt.toRat oneBits = 1) (hd : fmt.toRat deltaBits = d) (hs : 1 + 3 * d = s)
    (hs_ne : s ≠ 0)
    (hround1 : fmt.fromRat (1 / s) = oneBits)
    (hroundd : fmt.fromRat (d / s) = deltaBits) :
    sinkhornModeBStep fmt (symDiagBits 4 oneBits deltaBits) = symDiagBits 4 oneBits deltaBits ∧
    ∀ T : Nat, sinkhornModeBIter fmt T (symDiagBits 4 oneBits deltaBits) = symDiagBits 4 oneBits deltaBits := by
  have hrow_sum : ∀ i : Fin 4, rowSum (bitsMatToRat fmt (symDiagBits 4 oneBits deltaBits)) i = s := by
    intro i
    match i with
    | ⟨0, _⟩ => simp only [rowSum, sumFinRat, bitsMatToRat, symDiagBits, Fin.castSucc, Fin.last]; grind
    | ⟨1, _⟩ => simp only [rowSum, sumFinRat, bitsMatToRat, symDiagBits, Fin.castSucc, Fin.last]; grind
    | ⟨2, _⟩ => simp only [rowSum, sumFinRat, bitsMatToRat, symDiagBits, Fin.castSucc, Fin.last]; grind
    | ⟨3, _⟩ => simp only [rowSum, sumFinRat, bitsMatToRat, symDiagBits, Fin.castSucc, Fin.last]; grind
  have hcol_sum : ∀ j : Fin 4, colSum (bitsMatToRat fmt (symDiagBits 4 oneBits deltaBits)) j = s := by
    intro j
    match j with
    | ⟨0, _⟩ => simp only [colSum, sumFinRat, bitsMatToRat, symDiagBits, Fin.castSucc, Fin.last]; grind
    | ⟨1, _⟩ => simp only [colSum, sumFinRat, bitsMatToRat, symDiagBits, Fin.castSucc, Fin.last]; grind
    | ⟨2, _⟩ => simp only [colSum, sumFinRat, bitsMatToRat, symDiagBits, Fin.castSucc, Fin.last]; grind
    | ⟨3, _⟩ => simp only [colSum, sumFinRat, bitsMatToRat, symDiagBits, Fin.castSucc, Fin.last]; grind
  have hrow : sinkhornModeBRow fmt (symDiagBits 4 oneBits deltaBits) = symDiagBits 4 oneBits deltaBits := by
    funext i j
    simp only [sinkhornModeBRow, hrow_sum i, hs_ne, ↓reduceIte, symDiagBits]
    by_cases h : i = j
    · simp [h, h1, hround1]
    · simp [h, hd, hroundd]
  have hcol : sinkhornModeBCol fmt (symDiagBits 4 oneBits deltaBits) = symDiagBits 4 oneBits deltaBits := by
    funext i j
    simp only [sinkhornModeBCol, hcol_sum j, hs_ne, ↓reduceIte, symDiagBits]
    by_cases h : i = j
    · simp [h, h1, hround1]
    · simp [h, hd, hroundd]
  have hstep : sinkhornModeBStep fmt (symDiagBits 4 oneBits deltaBits) = symDiagBits 4 oneBits deltaBits := by
    simp only [sinkhornModeBStep, hrow, hcol]
  refine ⟨hstep, ?_⟩
  intro T
  induction T with
  | zero => rfl
  | succ t ih => simp only [sinkhornModeBIter, ih, hstep]

/-- Theorem 4 (Mode-B Exact-Sum Symmetric Overshoot Fixed Points — FP8-E4M3FN & BF16):
    1. `fp8ModeBFixed4` (`I_4 + (5/512)(J_4 - I_4)`) is a permanent fixed point of exact-sum
       Mode-B Sinkhorn for ALL `T : Nat`, attains exact spectral norm `527/512` (both exact
       eigenvector identity `‖H^L ones‖_2^2 = (527/512)^(2L) ‖ones‖_2^2` and universal upper
       bound `‖H u‖_2^2 ≤ (527/512)^2 ‖u‖_2^2`), and satisfies `40 < (527/512)^128`.
    2. `bf16ModeBFixed4` (`I_4 + (85/131072)(J_4 - I_4)`) is a permanent fixed point of exact-sum
       Mode-B Sinkhorn for ALL `T : Nat`, attains exact spectral norm `131327/131072`, and
       satisfies `32/25 < (131327/131072)^128`. -/
theorem mode_b_exact_sum_symmetric_overshoot_fixed_point :
    let H_fp8 := bitsMatToRat fp8Format fp8ModeBFixed4
    let H_bf16 := bitsMatToRat bf16Format bf16ModeBFixed4
    (∀ T : Nat, sinkhornModeBIter fp8Format T fp8ModeBFixed4 = fp8ModeBFixed4) ∧
    (∀ L : Nat, normSq (vecApplyIter H_fp8 L (onesVec 4)) =
      ratPow (527 / 512) L * ratPow (527 / 512) L * normSq (onesVec 4)) ∧
    (∀ u : RatVec 4, normSq (matVecMul H_fp8 u) ≤ (527 / 512) * (527 / 512) * normSq u) ∧
    ((40 : Rat) < ratPow (527 / 512) 128) ∧
    (∀ T : Nat, sinkhornModeBIter bf16Format T bf16ModeBFixed4 = bf16ModeBFixed4) ∧
    (∀ L : Nat, normSq (vecApplyIter H_bf16 L (onesVec 4)) =
      ratPow (131327 / 131072) L * ratPow (131327 / 131072) L * normSq (onesVec 4)) ∧
    (∀ u : RatVec 4, normSq (matVecMul H_bf16 u) ≤ (131327 / 131072) * (131327 / 131072) * normSq u) ∧
    ((32 / 25 : Rat) < ratPow (131327 / 131072) 128) := by
  intro H_fp8 H_bf16
  have hfp8_fix := sinkhornModeB_symDiag4_fixed fp8Format 0x38 0x05 ((5 : Rat) / 512) ((527 : Rat) / 512)
    fp8_toRat_one fp8_modeB_delta (by grind) (Rat.ne_of_gt (rat_div_pos (by decide) (by decide))) fp8_modeB_div_diag fp8_modeB_div_off
  have hbf16_fix := sinkhornModeB_symDiag4_fixed bf16Format 0x3F80 0x3A2A ((85 : Rat) / 131072) ((131327 : Rat) / 131072)
    bf16_toRat_one bf16_modeB_delta (by grind) (Rat.ne_of_gt (rat_div_pos (by decide) (by decide))) bf16_modeB_div_diag bf16_modeB_div_off
  have hfp8_eq : H_fp8 = fun i j => if i = j then (507 / 512 : Rat) + (5 / 512) else (5 / 512) := by
    funext i j
    simp only [H_fp8, bitsMatToRat, fp8ModeBFixed4, symDiagBits]
    by_cases h : i = j
    · simp only [h, ↓reduceIte, fp8Format, fp8_toRat_one]; grind
    · simp only [h, ↓reduceIte, fp8Format, fp8_modeB_delta]
  have hbf16_eq : H_bf16 = fun i j => if i = j then (130987 / 131072 : Rat) + (85 / 131072) else (85 / 131072) := by
    funext i j
    simp only [H_bf16, bitsMatToRat, bf16ModeBFixed4, symDiagBits]
    by_cases h : i = j
    · simp only [h, ↓reduceIte, bf16Format, bf16_toRat_one]; grind
    · simp only [h, ↓reduceIte, bf16Format, bf16_modeB_delta]
  have hfp8_eig : ∀ i : Fin 4, matVecMul H_fp8 (onesVec 4) i = (527 / 512 : Rat) * onesVec 4 i := by
    rw [hfp8_eq]
    intro i
    match i with
    | ⟨0, _⟩ => simp only [matVecMul, sumFinRat, onesVec, Fin.castSucc, Fin.last]; grind
    | ⟨1, _⟩ => simp only [matVecMul, sumFinRat, onesVec, Fin.castSucc, Fin.last]; grind
    | ⟨2, _⟩ => simp only [matVecMul, sumFinRat, onesVec, Fin.castSucc, Fin.last]; grind
    | ⟨3, _⟩ => simp only [matVecMul, sumFinRat, onesVec, Fin.castSucc, Fin.last]; grind
  have hbf16_eig : ∀ i : Fin 4, matVecMul H_bf16 (onesVec 4) i = (131327 / 131072 : Rat) * onesVec 4 i := by
    rw [hbf16_eq]
    intro i
    match i with
    | ⟨0, _⟩ => simp only [matVecMul, sumFinRat, onesVec, Fin.castSucc, Fin.last]; grind
    | ⟨1, _⟩ => simp only [matVecMul, sumFinRat, onesVec, Fin.castSucc, Fin.last]; grind
    | ⟨2, _⟩ => simp only [matVecMul, sumFinRat, onesVec, Fin.castSucc, Fin.last]; grind
    | ⟨3, _⟩ => simp only [matVecMul, sumFinRat, onesVec, Fin.castSucc, Fin.last]; grind
  refine ⟨hfp8_fix.2, normSq_vecApplyIter_eigenvector H_fp8 (onesVec 4) (527 / 512) hfp8_eig, ?_, ?_,
          hbf16_fix.2, normSq_vecApplyIter_eigenvector H_bf16 (onesVec 4) (131327 / 131072) hbf16_eig, ?_, ?_⟩
  · intro u
    rw [hfp8_eq]
    have h := symDiag_spectral_upper (507 / 512 : Rat) (5 / 512 : Rat)
      (rat_div_nonneg (by decide) (by decide)) (rat_div_nonneg (by decide) (by decide)) u
    have heq : ((507 / 512 : Rat) + ((4 : Nat) : Rat) * (5 / 512)) = (527 / 512 : Rat) := by grind
    rw [heq] at h
    exact h
  · have hpow := ratPow_div_nat 527 512 (by omega) 128
    have hlt := rat_div_lt_div_nat_pos 40 1 (527 ^ 128) (512 ^ 128) (by omega) (Nat.pow_pos (by omega)) fp8_pow128_gt40
    have h40 : ((40 : Nat) : Rat) / ((1 : Nat) : Rat) = (40 : Rat) := by grind
    have h527 : ((527 : Nat) : Rat) / ((512 : Nat) : Rat) = (527 / 512 : Rat) := by rfl
    rw [h527] at hpow
    rw [hpow, ← h40]
    exact hlt
  · intro u
    rw [hbf16_eq]
    have h := symDiag_spectral_upper (130987 / 131072 : Rat) (85 / 131072 : Rat)
      (rat_div_nonneg (by decide) (by decide)) (rat_div_nonneg (by decide) (by decide)) u
    have heq : ((130987 / 131072 : Rat) + ((4 : Nat) : Rat) * (85 / 131072)) = (131327 / 131072 : Rat) := by grind
    rw [heq] at h
    exact h
  · have hpow := ratPow_div_nat 131327 131072 (by omega) 128
    have hlt := rat_div_lt_div_nat_pos 32 25 (131327 ^ 128) (131072 ^ 128) (by omega) (Nat.pow_pos (by omega)) bf16_pow128_gt32_25
    have h32 : ((32 : Nat) : Rat) / ((25 : Nat) : Rat) = (32 / 25 : Rat) := by rfl
    have h131 : ((131327 : Nat) : Rat) / ((131072 : Nat) : Rat) = (131327 / 131072 : Rat) := by rfl
    rw [h131] at hpow
    rw [hpow, ← h32]
    exact hlt

end MhcSinkhornFp8
