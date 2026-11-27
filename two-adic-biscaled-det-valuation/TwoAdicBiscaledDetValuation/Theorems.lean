/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TwoAdicBiscaledDetValuation.Defs

/-!
# Theorems (`two-adic-biscaled-det-valuation`)

Full proofs of the headline infinite theorems of Exact 2-Adic Valuation Biscaled Elimination Engine.
-/

namespace SpecMat12

theorem castSucc_ne_last {n : Nat} (i : Fin n) : i.castSucc ≠ Fin.last n := by
  intro h
  have hv := congrArg Fin.val h
  simp at hv
  omega

theorem sumFin_congr {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i = g i) :
    sumFin f = sumFin g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumFin]
    rw [ih (fun i => h i.castSucc), h (Fin.last n)]

theorem prodFin_congr {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i = g i) :
    prodFin f = prodFin g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [prodFin]
    rw [ih (fun i => h i.castSucc), h (Fin.last n)]

theorem sumNat_congr {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i = g i) :
    sumNat f = sumNat g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumNat]
    rw [ih (fun i => h i.castSucc), h (Fin.last n)]

theorem sumFin_zero {n : Nat} : sumFin (fun _ : Fin n => (0 : Int)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumFin, ih]

theorem sumFin_add {n : Nat} (f g : Fin n → Int) :
    sumFin (fun i => f i + g i) = sumFin f + sumFin g := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih =>
    simp only [sumFin, ih]
    omega

theorem sumFin_neg {n : Nat} (f : Fin n → Int) :
    sumFin (fun i => -f i) = -sumFin f := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih =>
    simp only [sumFin, ih]
    omega

theorem sumFin_mul_left {n : Nat} (c : Int) (f : Fin n → Int) :
    sumFin (fun i => c * f i) = c * sumFin f := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih =>
    simp only [sumFin, ih, Int.mul_add]

theorem sumFin_mul_right {n : Nat} (f : Fin n → Int) (c : Int) :
    sumFin (fun i => f i * c) = sumFin f * c := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih =>
    simp only [sumFin, ih, Int.add_mul]

theorem sumFin_comm {m n : Nat} (F : Fin m → Fin n → Int) :
    sumFin (fun i => sumFin (fun j => F i j)) =
      sumFin (fun j => sumFin (fun i => F i j)) := by
  induction m with
  | zero =>
    simp only [sumFin]
    symm
    exact sumFin_zero
  | succ m ih =>
    simp only [sumFin]
    rw [ih (fun i j => F i.castSucc j), ← sumFin_add]

theorem sumFin_antisym {m : Nat} (F : Fin m → Fin m → Int)
    (hanti : ∀ i j, F i j = -F j i) :
    sumFin (fun i => sumFin (fun j => F i j)) = 0 := by
  have h1 : sumFin (fun i => sumFin (fun j => F i j)) =
      -sumFin (fun i => sumFin (fun j => F i j)) := by
    calc sumFin (fun i => sumFin (fun j => F i j))
        = sumFin (fun j => sumFin (fun i => F i j)) := sumFin_comm F
      _ = sumFin (fun j => sumFin (fun i => -F j i)) := by
            apply sumFin_congr; intro j; apply sumFin_congr; intro i; exact hanti i j
      _ = -sumFin (fun j => sumFin (fun i => F j i)) := by
            rw [← sumFin_neg]
            apply sumFin_congr; intro j; rw [sumFin_neg]
  omega

theorem sumFin_single {n : Nat} (k : Fin n) (f : Fin n → Int)
    (h : ∀ i, i ≠ k → f i = 0) : sumFin f = f k := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    simp only [sumFin]
    by_cases hk : k = Fin.last n
    · subst hk
      have h0 : sumFin (fun i : Fin n => f i.castSucc) = 0 := by
        rw [sumFin_congr (g := fun _ => 0)]
        · exact sumFin_zero
        · intro i
          exact h i.castSucc (castSucc_ne_last i)
      rw [h0, Int.zero_add]
    · have hlt : k.val < n := by
        have := k.isLt
        have hne : k.val ≠ n := fun hval => hk (Fin.ext hval)
        omega
      let k' : Fin n := ⟨k.val, hlt⟩
      have hk' : k'.castSucc = k := Fin.ext rfl
      have hlast : f (Fin.last n) = 0 := h (Fin.last n) (Ne.symm hk)
      rw [hlast, Int.add_zero]
      have hsub : sumFin (fun i : Fin n => f i.castSucc) = f k'.castSucc := by
        apply ih k'
        intro i hi
        apply h
        intro heq
        apply hi
        apply Fin.ext
        have := congrArg Fin.val heq
        simpa [k'] using this
      rw [hsub, hk']

theorem sumFin_mod2_congr {n : Nat} {f g : Fin n → Int}
    (h : ∀ i, f i % 2 = g i % 2) : sumFin f % 2 = sumFin g % 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumFin]
    have h1 := ih (fun i => h i.castSucc)
    have h2 := h (Fin.last n)
    omega

theorem prodFin_two_pow {n : Nat} (a : Fin n → Nat) :
    prodFin (fun i => (2 : Int) ^ (a i)) = (2 : Int) ^ (sumNat a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [prodFin, sumNat, ih]
    rw [Int.pow_add]

theorem prodFin_ones {n : Nat} : prodFin (fun _ : Fin n => (1 : Int)) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [prodFin, ih]

theorem sumNat_add {n : Nat} (a b : Fin n → Nat) :
    sumNat (fun i => a i + b i) = sumNat a + sumNat b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumNat, ih]
    omega

theorem prodFin_update_one {m : Nat} (g : Fin m → Int) (idx : Fin m) (val : Int)
    (hidx : g idx = 1) :
    prodFin (fun i => if i = idx then val else g i) = val * prodFin g := by
  induction m with
  | zero => exact Fin.elim0 idx
  | succ m ihm =>
    revert hidx
    refine Fin.lastCases ?_ ?_ idx
    · intro hlast
      simp only [prodFin, ↓reduceIte]
      have hsub : prodFin (fun i : Fin m => if i.castSucc = Fin.last m then val else g i.castSucc) =
          prodFin (fun i : Fin m => g i.castSucc) :=
        prodFin_congr (fun i => by simp [castSucc_ne_last])
      rw [hsub, hlast, Int.mul_one, Int.mul_comm]
    · intro idx' hidx'
      simp only [prodFin]
      have hne : Fin.last m ≠ idx'.castSucc := (castSucc_ne_last idx').symm
      simp only [hne, ↓reduceIte]
      have hsub : prodFin (fun i : Fin m => if i.castSucc = idx'.castSucc then val else g i.castSucc) =
          val * prodFin (fun i : Fin m => g i.castSucc) := by
        have hcongr : (fun i : Fin m => if i.castSucc = idx'.castSucc then val else g i.castSucc) =
            (fun i : Fin m => if i = idx' then val else g i.castSucc) := by
          funext i
          by_cases h : i = idx'
          · subst h; simp
          · have : i.castSucc ≠ idx'.castSucc := fun heq => h (Fin.castSucc_inj.mp heq)
            simp [h, this]
        rw [hcongr]
        exact ihm (fun i => g i.castSucc) idx' hidx'
      rw [hsub, Int.mul_assoc]

/-! ### Index-Skipping Helper `skipIdx` and Symmetric Double-Skip `skipPair` -/

theorem skipIdx_ne {n : Nat} (c : Fin (n + 1)) (j : Fin n) : skipIdx c j ≠ c := by
  intro h
  have hv := congrArg Fin.val h
  unfold skipIdx at hv
  split at hv <;> simp at hv <;> omega

theorem skipIdx_inj {n : Nat} (c : Fin (n + 1)) {j₁ j₂ : Fin n}
    (h : skipIdx c j₁ = skipIdx c j₂) : j₁ = j₂ := by
  have hv := congrArg Fin.val h
  unfold skipIdx at hv
  split at hv <;> split at hv <;> simp at hv <;> apply Fin.ext <;> omega

theorem skipIdx_surj {n : Nat} (c k : Fin (n + 1)) (h : k ≠ c) :
    ∃ j : Fin n, skipIdx c j = k := by
  have hne : k.val ≠ c.val := fun hv => h (Fin.ext hv)
  by_cases hlt : k.val < c.val
  · refine ⟨⟨k.val, by omega⟩, ?_⟩
    apply Fin.ext
    simp [skipIdx, hlt]
  · refine ⟨⟨k.val - 1, by omega⟩, ?_⟩
    apply Fin.ext
    have hnot : ¬ (k.val - 1 < c.val) := by omega
    simp [skipIdx, hnot]
    omega

theorem skipIdx_last {n : Nat} (j : Fin n) :
    skipIdx (Fin.last n) j = j.castSucc := by
  apply Fin.ext
  simp [skipIdx]

theorem sumFin_skipIdx {n : Nat} (c : Fin (n + 1)) (f : Fin (n + 1) → Int)
    (hc : f c = 0) :
    sumFin (fun j : Fin n => f (skipIdx c j)) = sumFin f := by
  induction n with
  | zero =>
    have hc0 : c = Fin.last 0 := Fin.ext (by omega)
    change 0 = 0 + f (Fin.last 0)
    rw [← hc0, hc]
    rfl
  | succ n ih =>
    by_cases hclast : c = Fin.last (n + 1)
    · subst hclast
      change sumFin (fun j : Fin (n + 1) => f (skipIdx (Fin.last (n + 1)) j)) =
        sumFin (fun i : Fin (n + 1) => f i.castSucc) + f (Fin.last (n + 1))
      rw [hc, Int.add_zero]
      apply sumFin_congr
      intro j
      rw [skipIdx_last]
    · have hclt : c.val < n + 1 := by
        have := c.isLt
        have hne : c.val ≠ n + 1 := fun hv => hclast (Fin.ext hv)
        omega
      let c' : Fin (n + 1) := ⟨c.val, hclt⟩
      have hlast : skipIdx c (Fin.last n) = Fin.last (n + 1) := by
        apply Fin.ext
        have hnot : ¬ (n < c.val) := by omega
        simp [skipIdx, hnot]
      have hsub : sumFin (fun j : Fin n => f (skipIdx c j.castSucc)) =
          sumFin (fun i : Fin (n + 1) => f i.castSucc) := by
        have hstep : (fun j : Fin n => f (skipIdx c j.castSucc)) =
            (fun j : Fin n => f (skipIdx c' j).castSucc) := by
          funext j
          congr 1
          apply Fin.ext
          simp only [skipIdx, c', Fin.val_castSucc]
          split <;> simp
        rw [hstep]
        exact ih c' (fun i => f i.castSucc) (by
          have : c'.castSucc = c := Fin.ext rfl
          rw [this, hc])
      change sumFin (fun j : Fin n => f (skipIdx c j.castSucc)) + f (skipIdx c (Fin.last n)) =
        sumFin (fun i : Fin (n + 1) => f i.castSucc) + f (Fin.last (n + 1))
      rw [hsub, hlast]

theorem skipPair_comm {n : Nat} (c₁ c₂ : Fin (n + 2)) (k : Fin n) :
    skipPair c₁ c₂ k = skipPair c₂ c₁ k := by
  apply Fin.ext
  unfold skipPair
  have hmin : min c₁.val c₂.val = min c₂.val c₁.val := Nat.min_comm _ _
  have hmax : max c₁.val c₂.val = max c₂.val c₁.val := Nat.max_comm _ _
  simp only [hmin, hmax]

theorem skipIdx_skipIdx_eq_skipPair {n : Nat} (c : Fin (n + 2)) (j : Fin (n + 1)) (k : Fin n) :
    skipIdx c (skipIdx j k) = skipPair c (skipIdx c j) k := by
  apply Fin.ext
  unfold skipIdx skipPair
  by_cases hjc : j.val < c.val
  · have hmin : min c.val j.val = j.val := Nat.min_eq_right (by omega)
    have hmax : max c.val j.val = c.val := Nat.max_eq_left (by omega)
    simp only [hjc, ↓reduceDIte, hmin, hmax]
    by_cases hkj : k.val < j.val
    · have hkc : k.val < c.val := by omega
      simp [hkj, hkc]
    · by_cases hkc : k.val + 1 < c.val
      · simp [hkj, hkc]
      · simp [hkj, hkc]
  · have hmin : min c.val (j.val + 1) = c.val := Nat.min_eq_left (by omega)
    have hmax : max c.val (j.val + 1) = j.val + 1 := Nat.max_eq_right (by omega)
    simp only [hjc, ↓reduceDIte, hmin, hmax]
    by_cases hkc : k.val < c.val
    · have hkj : k.val < j.val := by omega
      simp [hkj, hkc]
    · by_cases hkj : k.val < j.val
      · have h2 : k.val + 1 < j.val + 1 := by omega
        simp [hkj, hkc, h2]
      · have h2 : ¬ (k.val + 1 < j.val + 1) := by omega
        have hkc2 : ¬ (k.val + 1 < c.val) := by omega
        simp [hkj, hkc, h2, hkc2]

/-! ### Matrix Operations and Recursive Determinant -/

theorem signNat_add_self (k : Nat) : signNat (k + k) = 1 := by
  unfold signNat
  have : (k + k) % 2 = 0 := by omega
  simp [this]

theorem signNat_mul (a b : Nat) : signNat a * signNat b = signNat (a + b) := by
  unfold signNat
  by_cases ha : a % 2 = 0 <;> by_cases hb : b % 2 = 0
  · have : (a + b) % 2 = 0 := by omega
    simp [ha, hb, this]
  · have : (a + b) % 2 ≠ 0 := by omega
    simp [ha, hb, this]
  · have : (a + b) % 2 ≠ 0 := by omega
    simp [ha, hb, this]
  · have : (a + b) % 2 = 0 := by omega
    simp [ha, hb, this]

theorem det_congr {n : Nat} {A B : Mat n} (h : ∀ i j, A i j = B i j) :
    det A = det B := by
  have heq : A = B := funext (fun i => funext (fun j => h i j))
  rw [heq]

theorem det_mod2_congr {n : Nat} {A B : Mat n}
    (h : ∀ i j, A i j % 2 = B i j % 2) : det A % 2 = det B % 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [det]
    apply sumFin_mod2_congr
    intro j
    have h1 : A (Fin.last n) j % 2 = B (Fin.last n) j % 2 := h (Fin.last n) j
    have h2 : det (minorLast A j) % 2 = det (minorLast B j) % 2 :=
      ih (fun i k => h i.castSucc (skipIdx j k))
    have hmul : ∀ x y z w s : Int, x % 2 = z % 2 → y % 2 = w % 2 →
        (s * x * y) % 2 = (s * z * w) % 2 := by
      intro x y z w s hx hy
      rw [Int.mul_emod, Int.mul_emod s x, hx, hy, ← Int.mul_emod s z, ← Int.mul_emod]
    exact hmul _ _ _ _ _ h1 h2

/-! ### Row Multilinearity and Column Scaling -/

theorem minorLast_setRow_last {n : Nat} (A : Mat (n + 1)) (v : Fin (n + 1) → Int)
    (c : Fin (n + 1)) : minorLast (setRow A (Fin.last n) v) c = minorLast A c := by
  funext i j
  simp only [minorLast, setRow, castSucc_ne_last, ↓reduceIte]

theorem minorLast_setRow_castSucc {n : Nat} (A : Mat (n + 1)) (r : Fin n)
    (v : Fin (n + 1) → Int) (c : Fin (n + 1)) :
    minorLast (setRow A r.castSucc v) c =
      setRow (minorLast A c) r (fun j => v (skipIdx c j)) := by
  funext i j
  simp only [minorLast, setRow]
  by_cases h : i = r
  · subst h; simp
  · have hne : i.castSucc ≠ r.castSucc := fun heq => h (Fin.castSucc_inj.mp heq)
    simp [h, hne]

theorem det_setRow_add {n : Nat} (A : Mat n) (r : Fin n) (u v : Fin n → Int) :
    det (setRow A r (fun j => u j + v j)) =
      det (setRow A r u) + det (setRow A r v) := by
  induction n with
  | zero => exact Fin.elim0 r
  | succ n ih =>
    refine Fin.lastCases ?_ ?_ r
    · simp only [det, minorLast_setRow_last]
      rw [← sumFin_add]
      apply sumFin_congr
      intro j
      simp only [setRow, ↓reduceIte]
      rw [Int.mul_add, Int.add_mul]
    · intro r'
      simp only [det, minorLast_setRow_castSucc]
      rw [← sumFin_add]
      apply sumFin_congr
      intro j
      have hne : Fin.last n ≠ r'.castSucc := (castSucc_ne_last r').symm
      simp only [setRow, hne, ↓reduceIte]
      rw [ih (minorLast A j) r' (fun k => u (skipIdx j k)) (fun k => v (skipIdx j k))]
      rw [Int.mul_add]

theorem det_setRow_smul {n : Nat} (A : Mat n) (r : Fin n) (c : Int) (u : Fin n → Int) :
    det (setRow A r (fun j => c * u j)) = c * det (setRow A r u) := by
  induction n with
  | zero => exact Fin.elim0 r
  | succ n ih =>
    refine Fin.lastCases ?_ ?_ r
    · simp only [det, minorLast_setRow_last]
      rw [← sumFin_mul_left]
      apply sumFin_congr
      intro j
      simp only [setRow, ↓reduceIte]
      rw [Int.mul_left_comm (signNat _), Int.mul_assoc]
    · intro r'
      simp only [det, minorLast_setRow_castSucc]
      rw [← sumFin_mul_left]
      apply sumFin_congr
      intro j
      have hne : Fin.last n ≠ r'.castSucc := (castSucc_ne_last r').symm
      simp only [setRow, hne, ↓reduceIte]
      rw [ih (minorLast A j) r' (fun k => u (skipIdx j k))]
      rw [Int.mul_left_comm]

theorem setRow_self {n : Nat} (A : Mat n) (r : Fin n) : setRow A r (A r) = A := by
  funext i j
  simp only [setRow]
  by_cases h : i = r
  · subst h; simp
  · simp [h]

theorem det_row_smul {n : Nat} (A : Mat n) (r : Fin n) (c : Int) :
    det (setRow A r (fun j => c * A r j)) = c * det A := by
  have h := det_setRow_smul A r c (A r)
  rw [setRow_self] at h
  exact h

theorem det_scaleCol {n : Nat} (A : Mat n) (k : Fin n) (c : Int) :
    det (scaleCol A k c) = c * det A := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    simp only [det]
    rw [← sumFin_mul_left]
    apply sumFin_congr
    intro j
    by_cases hjk : j = k
    · subst hjk
      have hm : minorLast (scaleCol A j c) j = minorLast A j := by
        funext i l
        simp only [minorLast, scaleCol, skipIdx_ne, ↓reduceIte]
      rw [hm]
      simp only [scaleCol, ↓reduceIte]
      rw [Int.mul_left_comm (signNat _), Int.mul_assoc]
    · rcases skipIdx_surj j k (Ne.symm hjk) with ⟨k', hk'⟩
      have hm : minorLast (scaleCol A k c) j = scaleCol (minorLast A j) k' c := by
        funext i l
        simp only [minorLast, scaleCol]
        by_cases hl : l = k'
        · subst hl; simp [hk']
        · have hne2 : skipIdx j l ≠ k := by
            intro heq
            rw [← hk'] at heq
            exact hl (skipIdx_inj j heq)
          simp [hl, hne2]
      rw [hm, ih (minorLast A j) k']
      simp only [scaleCol, hjk, ↓reduceIte]
      rw [Int.mul_left_comm]

theorem det_col_zero {n : Nat} (A : Mat n) (k : Fin n) (h : ∀ i, A i k = 0) :
    det A = 0 := by
  have h1 := det_scaleCol A k 0
  have heq : scaleCol A k 0 = A := by
    funext i j
    simp only [scaleCol]
    by_cases hj : j = k
    · subst hj; simp [h i]
    · simp [hj]
  rw [heq] at h1
  simpa using h1

/-! ### Alternating Property, Row Swaps, and Uniqueness -/

theorem det_last_two_eq {n : Nat} (A : Mat (n + 2))
    (heq : A (Fin.last (n + 1)) = A (Fin.last n).castSucc) : det A = 0 := by
  let F : Fin (n + 2) → Fin (n + 2) → Int := fun c₁ c₂ =>
    if c₁ = c₂ then 0
    else
      (if c₁.val < c₂.val then signNat (c₁.val + c₂.val) else -signNat (c₁.val + c₂.val)) *
      A (Fin.last (n + 1)) c₁ * A (Fin.last (n + 1)) c₂ *
      det (fun (i j : Fin n) => A i.castSucc.castSucc (skipPair c₁ c₂ j))
  have hanti : ∀ c₁ c₂, F c₁ c₂ = -F c₂ c₁ := by
    intro c₁ c₂
    dsimp only [F]
    by_cases h : c₁ = c₂
    · subst h; simp
    · have hne' : c₂ ≠ c₁ := Ne.symm h
      simp only [h, hne', ↓reduceIte]
      have hmin : (fun (i j : Fin n) => A i.castSucc.castSucc (skipPair c₁ c₂ j)) =
          (fun (i j : Fin n) => A i.castSucc.castSucc (skipPair c₂ c₁ j)) := by
        funext i j; rw [skipPair_comm]
      rw [hmin, Nat.add_comm c₂.val c₁.val]
      have hne_val : c₁.val ≠ c₂.val := fun hv => h (Fin.ext hv)
      by_cases hlt : c₁.val < c₂.val
      · have hnot : ¬ (c₂.val < c₁.val) := by omega
        simp only [hlt, hnot, ↓reduceIte]
        rw [Int.neg_mul, Int.neg_mul, Int.neg_mul, Int.neg_neg]
        have hxy : signNat (c₁.val + c₂.val) * A (Fin.last (n + 1)) c₁ * A (Fin.last (n + 1)) c₂ =
            signNat (c₁.val + c₂.val) * A (Fin.last (n + 1)) c₂ * A (Fin.last (n + 1)) c₁ := by
          rw [Int.mul_right_comm]
        rw [hxy]
      · have hgt : c₂.val < c₁.val := by omega
        simp only [hlt, hgt, ↓reduceIte]
        rw [Int.neg_mul, Int.neg_mul, Int.neg_mul]
        have hxy : signNat (c₁.val + c₂.val) * A (Fin.last (n + 1)) c₁ * A (Fin.last (n + 1)) c₂ =
            signNat (c₁.val + c₂.val) * A (Fin.last (n + 1)) c₂ * A (Fin.last (n + 1)) c₁ := by
          rw [Int.mul_right_comm]
        rw [hxy]
  have hdet_eq : det A = sumFin (fun c₁ => sumFin (fun c₂ => F c₁ c₂)) := by
    simp only [det]
    apply sumFin_congr
    intro c₁
    rw [← sumFin_mul_left]
    rw [← sumFin_skipIdx c₁ (fun c₂ => F c₁ c₂) (by simp [F])]
    apply sumFin_congr
    intro j
    have hne : c₁ ≠ skipIdx c₁ j := (skipIdx_ne c₁ j).symm
    dsimp only [F]
    simp only [hne, ↓reduceIte]
    have hminor : minorLast (minorLast A c₁) j =
        (fun (i k : Fin n) => A i.castSucc.castSucc (skipPair c₁ (skipIdx c₁ j) k)) := by
      funext i k
      simp only [minorLast]
      rw [skipIdx_skipIdx_eq_skipPair]
    rw [hminor]
    have hrow : minorLast A c₁ (Fin.last n) j = A (Fin.last (n + 1)) (skipIdx c₁ j) := by
      simp only [minorLast]
      exact (congrFun heq (skipIdx c₁ j)).symm
    rw [hrow]
    have hsign_lhs : signNat (n + 1 + c₁.val) * signNat (n + j.val) =
        if c₁.val < (skipIdx c₁ j).val then signNat (c₁.val + (skipIdx c₁ j).val)
        else -signNat (c₁.val + (skipIdx c₁ j).val) := by
      rw [signNat_mul]
      by_cases hjc : j.val < c₁.val
      · have hval : (skipIdx c₁ j).val = j.val := by simp [skipIdx, hjc]
        rw [hval]
        have hnot : ¬ (c₁.val < j.val) := by omega
        rw [ite_eq_right_iff.mpr (fun h => absurd h hnot)]
        unfold signNat
        by_cases hp : (c₁.val + j.val) % 2 = 0
        · have hodd : (n + 1 + c₁.val + (n + j.val)) % 2 ≠ 0 := by omega
          simp [hp, hodd]
        · have heven : (n + 1 + c₁.val + (n + j.val)) % 2 = 0 := by omega
          simp [hp, heven]
      · have hval : (skipIdx c₁ j).val = j.val + 1 := by simp [skipIdx, hjc]
        rw [hval]
        have hlt : c₁.val < j.val + 1 := by omega
        rw [ite_eq_left_iff.mpr (fun h => absurd hlt h)]
        unfold signNat
        by_cases hp : (c₁.val + (j.val + 1)) % 2 = 0
        · have heven : (n + 1 + c₁.val + (n + j.val)) % 2 = 0 := by omega
          simp [hp, heven]
        · have hodd : (n + 1 + c₁.val + (n + j.val)) % 2 ≠ 0 := by omega
          simp [hp, hodd]
    calc signNat (n + 1 + c₁.val) * A (Fin.last (n + 1)) c₁ *
          (signNat (n + j.val) * A (Fin.last (n + 1)) (skipIdx c₁ j) *
            det (fun (i k : Fin n) => A i.castSucc.castSucc (skipPair c₁ (skipIdx c₁ j) k)))
        = (signNat (n + 1 + c₁.val) * signNat (n + j.val)) *
          A (Fin.last (n + 1)) c₁ * A (Fin.last (n + 1)) (skipIdx c₁ j) *
          det (fun (i k : Fin n) => A i.castSucc.castSucc (skipPair c₁ (skipIdx c₁ j) k)) := by
            simp only [Int.mul_assoc]
            rw [Int.mul_left_comm (A (Fin.last (n + 1)) c₁) (signNat (n + j.val))]
      _ = _ := by rw [hsign_lhs]
  rw [hdet_eq]
  exact sumFin_antisym F hanti

theorem det_eq_zero_of_adj_eq {n : Nat} (A : Mat n) (i : Nat) (hi : i + 1 < n)
    (heq : A ⟨i, by omega⟩ = A ⟨i + 1, hi⟩) : det A = 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hlast : i + 1 = n
    · cases n with
      | zero => omega
      | succ m =>
        apply det_last_two_eq
        have h1 : (Fin.last (m + 1)) = ⟨i + 1, hi⟩ := Fin.ext (by simp; omega)
        have h2 : (Fin.last m).castSucc = ⟨i, by omega⟩ := Fin.ext (by simp; omega)
        rw [h1, h2, heq]
    · have hi' : i + 1 < n := by omega
      simp only [det]
      rw [sumFin_congr (g := fun _ => 0)]
      · exact sumFin_zero
      · intro j
        have hz : det (minorLast A j) = 0 := by
          apply ih (minorLast A j) hi'
          funext k
          simp only [minorLast]
          exact congrFun heq (skipIdx j k)
        rw [hz, Int.mul_zero]

theorem setRow_comm {n : Nat} (A : Mat n) {r₁ r₂ : Fin n} (hne : r₁ ≠ r₂)
    (w₁ w₂ : Fin n → Int) :
    setRow (setRow A r₁ w₁) r₂ w₂ = setRow (setRow A r₂ w₂) r₁ w₁ := by
  funext r c
  simp only [setRow]
  by_cases h1 : r = r₁
  · subst h1; simp [hne]
  · by_cases h2 : r = r₂
    · subst h2; simp [h1]
    · simp [h1, h2]

theorem det_swap_adj {n : Nat} (A : Mat n) (i : Nat) (hi : i + 1 < n) :
    det (swapRows A ⟨i, by omega⟩ ⟨i + 1, hi⟩) = -det A := by
  let r₁ : Fin n := ⟨i, by omega⟩
  let r₂ : Fin n := ⟨i + 1, hi⟩
  have hne : r₁ ≠ r₂ := by intro h; have := congrArg Fin.val h; simp [r₁, r₂] at this
  let u := A r₁
  let v := A r₂
  let uv : Fin n → Int := fun j => u j + v j
  have hB0 : det (setRow (setRow A r₁ uv) r₂ uv) = 0 :=
    det_eq_zero_of_adj_eq _ i hi (by funext j; simp [setRow, r₁, r₂, hne])
  have hstep1 : det (setRow (setRow A r₁ uv) r₂ uv) =
      det (setRow (setRow A r₁ u) r₂ uv) + det (setRow (setRow A r₁ v) r₂ uv) := by
    rw [setRow_comm A hne uv uv, det_setRow_add, ← setRow_comm A hne u uv, ← setRow_comm A hne v uv]
  have hstep2 : det (setRow (setRow A r₁ u) r₂ uv) =
      det (setRow (setRow A r₁ u) r₂ u) + det (setRow (setRow A r₁ u) r₂ v) :=
    det_setRow_add (setRow A r₁ u) r₂ u v
  have hstep3 : det (setRow (setRow A r₁ v) r₂ uv) =
      det (setRow (setRow A r₁ v) r₂ u) + det (setRow (setRow A r₁ v) r₂ v) :=
    det_setRow_add (setRow A r₁ v) r₂ u v
  have huu : det (setRow (setRow A r₁ u) r₂ u) = 0 :=
    det_eq_zero_of_adj_eq _ i hi (by funext j; simp [setRow, r₁, r₂, hne])
  have hvv : det (setRow (setRow A r₁ v) r₂ v) = 0 :=
    det_eq_zero_of_adj_eq _ i hi (by funext j; simp [setRow, r₁, r₂, hne])
  have huv : setRow (setRow A r₁ u) r₂ v = A := by
    funext r c; simp only [setRow]
    by_cases h2 : r = r₂
    · subst h2; simp [v]
    · by_cases h1 : r = r₁
      · subst h1; simp [h2, u]
      · simp [h1, h2]
  have hvu : setRow (setRow A r₁ v) r₂ u = swapRows A r₁ r₂ := by
    funext r c; simp only [setRow, swapRows]
    by_cases h2 : r = r₂
    · subst h2; simp [hne.symm, u]
    · by_cases h1 : r = r₁
      · subst h1; simp [h2, v]
      · simp [h1, h2]
  rw [hstep2, hstep3, huu, hvv, huv, hvu] at hstep1
  change det (swapRows A r₁ r₂) = -det A
  omega

theorem swapRows_symm {n : Nat} (A : Mat n) (r₁ r₂ : Fin n) :
    swapRows A r₁ r₂ = swapRows A r₂ r₁ := by
  funext i j; simp only [swapRows]
  by_cases h1 : i = r₁
  · subst h1
    by_cases h2 : i = r₂
    · subst h2; simp
    · simp [h2]
  · by_cases h2 : i = r₂
    · subst h2; simp [h1]
    · simp [h1, h2]

theorem swapRows_step {n : Nat} (A : Mat n) (a b c : Fin n)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    swapRows A a c = swapRows (swapRows (swapRows A a b) b c) a b := by
  funext i j
  simp only [swapRows]
  by_cases hi1 : i = a
  · subst hi1; simp [hbc.symm, hac.symm]
  · by_cases hi2 : i = b
    · subst hi2; simp [hab, hac, hbc, hab.symm]
    · by_cases hi3 : i = c
      · subst hi3; simp [hab.symm, hac.symm, hbc.symm]
      · simp [hi1, hi2, hi3]

theorem det_swapRows_lt {n : Nat} (A : Mat n) (i j : Nat) (hij : i < j) (hj : j < n) :
    det (swapRows A ⟨i, by omega⟩ ⟨j, hj⟩) = -det A := by
  have hmain : ∀ d : Nat, ∀ (A : Mat n) (i j : Nat) (hi : i < n) (hj : j < n),
      j - i = d → i < j →
      det (swapRows A ⟨i, hi⟩ ⟨j, hj⟩) = -det A := by
    intro d
    induction d with
    | zero => intro _ i j _ _ hd hij; omega
    | succ d ih =>
      intro A i j hi hj hd hij
      by_cases hd0 : d = 0
      · subst hd0
        have hj1 : j = i + 1 := by omega
        subst hj1
        exact det_swap_adj A i hj
      · have h1 : i + 1 < j := by omega
        let a : Fin n := ⟨i, hi⟩
        let b : Fin n := ⟨i + 1, by omega⟩
        let c : Fin n := ⟨j, hj⟩
        have hab : a ≠ b := by intro h; have := congrArg Fin.val h; simp [a, b] at this
        have hbc : b ≠ c := by intro h; have := congrArg Fin.val h; simp [b, c] at this; omega
        have hac : a ≠ c := by intro h; have := congrArg Fin.val h; simp [a, c] at this; omega
        change det (swapRows A a c) = -det A
        rw [swapRows_step A a b c hab hbc hac]
        rw [det_swap_adj _ i (by omega)]
        rw [ih _ (i + 1) j (by omega) hj (by omega) h1]
        rw [det_swap_adj A i (by omega)]
        omega
  exact hmain (j - i) A i j (by omega) hj rfl hij

theorem det_swapRows {n : Nat} (A : Mat n) (r₁ r₂ : Fin n) (hne : r₁ ≠ r₂) :
    det (swapRows A r₁ r₂) = -det A := by
  have hne_v : r₁.val ≠ r₂.val := fun hv => hne (Fin.ext hv)
  by_cases hlt : r₁.val < r₂.val
  · exact det_swapRows_lt A r₁.val r₂.val hlt r₂.isLt
  · rw [swapRows_symm]
    exact det_swapRows_lt A r₂.val r₁.val (by omega) r₁.isLt

theorem det_eq_zero_of_row_eq {n : Nat} (A : Mat n) (r₁ r₂ : Fin n)
    (hne : r₁ ≠ r₂) (heq : A r₁ = A r₂) : det A = 0 := by
  have hsw : swapRows A r₁ r₂ = A := by
    funext i j; simp only [swapRows]
    by_cases h1 : i = r₁
    · subst h1; simp [heq]
    · by_cases h2 : i = r₂
      · subst h2; simp [h1, heq]
      · simp [h1, h2]
  have hneg := det_swapRows A r₁ r₂ hne
  rw [hsw] at hneg
  omega

/-! ### Alternating Multilinear Uniqueness and Multiplicativity `det (A * B) = det A * det B` -/

theorem row_eq_sum_stdBasis {n : Nat} (v : Fin n → Int) (j : Fin n) :
    v j = sumFin (fun c : Fin n => v c * stdBasis c j) := by
  symm
  rw [sumFin_single j]
  · simp [stdBasis]
  · intro c hc
    simp [stdBasis, Ne.symm hc]

theorem alt_swap_neg {n : Nat} (ψ : Mat n → Int)
    (hadd : ∀ A r u v, ψ (setRow A r (fun j => u j + v j)) = ψ (setRow A r u) + ψ (setRow A r v))
    (halt : ∀ A r₁ r₂, r₁ ≠ r₂ → A r₁ = A r₂ → ψ A = 0)
    (A : Mat n) (r₁ r₂ : Fin n) (hne : r₁ ≠ r₂) :
    ψ (swapRows A r₁ r₂) = -ψ A := by
  let u := A r₁
  let v := A r₂
  let uv : Fin n → Int := fun j => u j + v j
  have hB0 : ψ (setRow (setRow A r₁ uv) r₂ uv) = 0 :=
    halt _ r₁ r₂ hne (by funext j; simp [setRow, hne])
  have hstep1 : ψ (setRow (setRow A r₁ uv) r₂ uv) =
      ψ (setRow (setRow A r₁ u) r₂ uv) + ψ (setRow (setRow A r₁ v) r₂ uv) := by
    rw [setRow_comm A hne uv uv, hadd, ← setRow_comm A hne u uv, ← setRow_comm A hne v uv]
  have hstep2 : ψ (setRow (setRow A r₁ u) r₂ uv) =
      ψ (setRow (setRow A r₁ u) r₂ u) + ψ (setRow (setRow A r₁ u) r₂ v) :=
    hadd (setRow A r₁ u) r₂ u v
  have hstep3 : ψ (setRow (setRow A r₁ v) r₂ uv) =
      ψ (setRow (setRow A r₁ v) r₂ u) + ψ (setRow (setRow A r₁ v) r₂ v) :=
    hadd (setRow A r₁ v) r₂ u v
  have huu : ψ (setRow (setRow A r₁ u) r₂ u) = 0 :=
    halt _ r₁ r₂ hne (by funext j; simp [setRow, hne])
  have hvv : ψ (setRow (setRow A r₁ v) r₂ v) = 0 :=
    halt _ r₁ r₂ hne (by funext j; simp [setRow, hne])
  have huv : setRow (setRow A r₁ u) r₂ v = A := by
    funext r c; simp only [setRow]
    by_cases h2 : r = r₂
    · subst h2; simp [v]
    · by_cases h1 : r = r₁
      · subst h1; simp [h2, u]
      · simp [h1, h2]
  have hvu : setRow (setRow A r₁ v) r₂ u = swapRows A r₁ r₂ := by
    funext r c; simp only [setRow, swapRows]
    by_cases h2 : r = r₂
    · subst h2; simp [hne.symm, u]
    · by_cases h1 : r = r₁
      · subst h1; simp [h2, v]
      · simp [h1, h2]
  rw [hstep2, hstep3, huu, hvv, huv, hvu] at hstep1
  omega

/-- Constructive (zero `Classical.choice`!) proof that every alternating row-multilinear functional
    vanishing on `idMat n` vanishes identically. -/
theorem alt_multilin_eq_zero {n : Nat} (ψ : Mat n → Int)
    (hadd : ∀ A r u v, ψ (setRow A r (fun j => u j + v j)) = ψ (setRow A r u) + ψ (setRow A r v))
    (hsmul : ∀ A r c u, ψ (setRow A r (fun j => c * u j)) = c * ψ (setRow A r u))
    (halt : ∀ A r₁ r₂, r₁ ≠ r₂ → A r₁ = A r₂ → ψ A = 0)
    (hid : ψ (idMat n) = 0) :
    ∀ A : Mat n, ψ A = 0 := by
  have hzero : ∀ A r, ψ (setRow A r (fun _ => 0)) = 0 := by
    intro A r
    have h := hsmul A r 0 (fun _ => 0)
    simp at h; exact h
  have hsum : ∀ {m : Nat} (A : Mat n) (r : Fin n) (F : Fin m → Fin n → Int),
      ψ (setRow A r (fun j => sumFin (fun c => F c j))) =
        sumFin (fun c => ψ (setRow A r (F c))) := by
    intro m
    induction m with
    | zero => intro A r F; simp only [sumFin]; exact hzero A r
    | succ m ih =>
      intro A r F
      simp only [sumFin]
      rw [hadd, ih A r (fun c => F c.castSucc)]
  have hbasis_step : ∀ k : Nat, k ≤ n → ∀ f : Fin n → Fin n,
      (∀ i : Fin n, i.val ≥ k → f i = i) → ψ (basisMat f) = 0 := by
    intro k
    induction k with
    | zero =>
      intro _ f hf
      have heq : basisMat f = idMat n := by
        funext i j
        simp only [basisMat, stdBasis, idMat, hf i (Nat.zero_le _)]
        by_cases h : j = i
        · subst h; simp
        · simp [h, Ne.symm h]
      rw [heq]; exact hid
    | succ k ih =>
      intro hk f hf
      let r : Fin n := ⟨k, by omega⟩
      have hsearch : ∀ m : Nat, m ≤ k + 1 →
          (∃ p : Fin n, p.val < m ∧ f p = r) ∨ (∀ p : Fin n, p.val < m → f p ≠ r) := by
        intro m
        induction m with
        | zero => intro _; right; intro p hp; omega
        | succ m ihm =>
          intro hm
          rcases ihm (by omega) with ⟨p, hp, hfp⟩ | hno
          · left; exact ⟨p, by omega, hfp⟩
          · let q : Fin n := ⟨m, by omega⟩
            by_cases hfq : f q = r
            · left; exact ⟨q, by simp [q], hfq⟩
            · right
              intro p hp
              by_cases hpm : p.val < m
              · exact hno p hpm
              · have hpq : p = q := Fin.ext (by simp [q]; omega)
                rw [hpq]; exact hfq
      rcases hsearch (k + 1) (Nat.le_refl _) with ⟨p, hp, hfp⟩ | hmiss
      · by_cases hpr : p = r
        · apply ih (by omega) f
          intro i hi
          by_cases hik : i.val = k
          · have hir : i = r := Fin.ext hik
            rw [hir, ← hpr, hfp, hpr]
          · exact hf i (by omega)
        · let g : Fin n → Fin n := fun i => if i = p then f r else if i = r then f p else f i
          have hsw : swapRows (basisMat f) p r = basisMat g := by
            funext i j; simp only [swapRows, basisMat, g]
            by_cases h1 : i = p
            · subst h1; simp
            · by_cases h2 : i = r
              · subst h2; simp [h1]
              · simp [h1, h2]
          have hg0 : ψ (basisMat g) = 0 := by
            apply ih (by omega) g
            intro i hi
            by_cases hik : i.val = k
            · have hir : i = r := Fin.ext hik
              subst hir
              have hne_rp : r ≠ p := Ne.symm hpr
              simp [g, hne_rp, hfp]
            · have hip : i ≠ p := by
                intro h; subst h; omega
              have hir : i ≠ r := by
                intro h; subst h; exact hik rfl
              simp [g, hip, hir, hf i (by omega)]
          have hneg := alt_swap_neg ψ hadd halt (basisMat f) p r hpr
          rw [hsw, hg0] at hneg
          omega
      · have hpigeon : ∀ m : Nat, ∀ g : Fin (m + 1) → Fin m,
            ∃ a b : Fin (m + 1), a ≠ b ∧ g a = g b := by
          intro m
          induction m with
          | zero => intro g; exact Fin.elim0 (g ⟨0, by omega⟩)
          | succ m ihm =>
            intro g
            have hchk : ∀ t : Nat, t ≤ m + 1 →
                (∃ i : Fin (m + 2), i.val < t ∧ g i = g (Fin.last (m + 1))) ∨
                (∀ i : Fin (m + 2), i.val < t → g i ≠ g (Fin.last (m + 1))) := by
              intro t
              induction t with
              | zero => intro _; right; intro i hi; omega
              | succ t iht =>
                intro ht
                rcases iht (by omega) with ⟨i, hi, hgi⟩ | hno
                · left; exact ⟨i, by omega, hgi⟩
                · let q : Fin (m + 2) := ⟨t, by omega⟩
                  by_cases hgq : g q = g (Fin.last (m + 1))
                  · left; exact ⟨q, by simp [q], hgq⟩
                  · right; intro i hi
                    by_cases hit : i.val < t
                    · exact hno i hit
                    · have : i = q := Fin.ext (by simp [q]; omega)
                      rw [this]; exact hgq
            rcases hchk (m + 1) (Nat.le_refl _) with ⟨i, hi, hgi⟩ | hnone
            · refine ⟨i, Fin.last (m + 1), ?_, hgi⟩
              intro h; have := congrArg Fin.val h; simp at this; omega
            · let c := g (Fin.last (m + 1))
              let g' : Fin (m + 1) → Fin m := fun i =>
                if hlt : (g i.castSucc).val < c.val then ⟨(g i.castSucc).val, by omega⟩
                else ⟨(g i.castSucc).val - 1, by
                  have hne : g i.castSucc ≠ c := hnone i.castSucc i.isLt
                  have hnev : (g i.castSucc).val ≠ c.val := fun hv => hne (Fin.ext hv)
                  have := (g i.castSucc).isLt
                  omega⟩
              rcases ihm g' with ⟨a, b, hab, hgab⟩
              refine ⟨a.castSucc, b.castSucc, fun h => hab (Fin.castSucc_inj.mp h), ?_⟩
              have hval := congrArg Fin.val hgab
              dsimp only [g'] at hval
              have hnea : (g a.castSucc).val ≠ c.val := fun hv => hnone a.castSucc a.isLt (Fin.ext hv)
              have hneb : (g b.castSucc).val ≠ c.val := fun hv => hnone b.castSucc b.isLt (Fin.ext hv)
              apply Fin.ext
              split at hval <;> split at hval <;> simp at hval <;> omega
        have hgt_chk : ∀ m : Nat, m ≤ k + 1 →
            (∃ p : Fin n, p.val < m ∧ (f p).val ≥ k + 1) ∨
            (∀ p : Fin n, p.val < m → (f p).val < k + 1) := by
          intro m
          induction m with
          | zero => intro _; right; intro p hp; omega
          | succ m ihm =>
            intro hm
            rcases ihm (by omega) with ⟨p, hp, hfp⟩ | hno
            · left; exact ⟨p, by omega, hfp⟩
            · let q : Fin n := ⟨m, by omega⟩
              by_cases hfq : (f q).val ≥ k + 1
              · left; exact ⟨q, by simp [q], hfq⟩
              · right; intro p hp
                by_cases hpm : p.val < m
                · exact hno p hpm
                · have : p = q := Fin.ext (by simp [q]; omega)
                  rw [this]; omega
        rcases hgt_chk (k + 1) (Nat.le_refl _) with ⟨p, hp, hfp⟩ | hbounded
        · have hne : p ≠ f p := by intro h; rw [← h] at hfp; omega
          have heq : basisMat f p = basisMat f (f p) := by
            simp only [basisMat, hf (f p) hfp]
          exact halt (basisMat f) p (f p) hne heq
        · let g : Fin (k + 1) → Fin k := fun i =>
            ⟨(f ⟨i.val, by omega⟩).val, by
              have h1 := hbounded ⟨i.val, by omega⟩ i.isLt
              have h2 : f ⟨i.val, by omega⟩ ≠ r := hmiss ⟨i.val, by omega⟩ i.isLt
              have h3 : (f ⟨i.val, by omega⟩).val ≠ k := fun hv => h2 (Fin.ext hv)
              omega⟩
          rcases hpigeon k g with ⟨a, b, hab, hgab⟩
          let ra : Fin n := ⟨a.val, by omega⟩
          let rb : Fin n := ⟨b.val, by omega⟩
          have hne : ra ≠ rb := by
            intro h
            apply hab
            apply Fin.ext
            have hv : ra.val = rb.val := congrArg Fin.val h
            exact hv
          have heq : basisMat f ra = basisMat f rb := by
            simp only [basisMat]
            congr 1
            apply Fin.ext
            have hv : (g a).val = (g b).val := congrArg Fin.val hgab
            exact hv
          exact halt (basisMat f) ra rb hne heq
  -- Step 2: Expand rows 0..k-1 constructively carrying the target basis map `f`!
  have hexpand : ∀ k : Nat, k ≤ n → ∀ (A : Mat n) (f : Fin n → Fin n),
      (∀ i : Fin n, i.val ≥ k → A i = stdBasis (f i)) → ψ A = 0 := by
    intro k
    induction k with
    | zero =>
      intro _ A f hA
      have hAf : A = basisMat f := by
        funext i j
        exact congrFun (hA i (Nat.zero_le _)) j
      rw [hAf]
      exact hbasis_step n (Nat.le_refl n) f (fun i hi => by omega)
    | succ k ih =>
      intro hk A f hA
      let r : Fin n := ⟨k, by omega⟩
      have hrow : A = setRow A r (fun j => sumFin (fun c => A r c * stdBasis c j)) := by
        funext i j; simp only [setRow]
        by_cases h : i = r
        · subst h; simp only [↓reduceIte]; exact row_eq_sum_stdBasis (A r) j
        · simp only [h, ↓reduceIte]
      rw [hrow, hsum]
      rw [sumFin_congr (g := fun _ => 0)]
      · exact sumFin_zero
      · intro c
        rw [hsmul]
        let f' : Fin n → Fin n := fun i => if i = r then c else f i
        have hz : ψ (setRow A r (stdBasis c)) = 0 := by
          apply ih (by omega) _ f'
          intro i hi
          funext j
          simp only [setRow, f']
          by_cases hir : i = r
          · subst hir; simp
          · have hgt : i.val ≥ k + 1 := by
              have hnev : i.val ≠ k := fun hv => hir (Fin.ext hv)
              omega
            simp only [hir, ↓reduceIte]
            exact congrFun (hA i hgt) j
        rw [hz, Int.mul_zero]
  intro A
  exact hexpand n (Nat.le_refl n) A id (fun i hi => by omega)

theorem det_idMat (n : Nat) : det (idMat n) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [det]
    rw [sumFin_single (Fin.last n)]
    · have hminor : minorLast (idMat (n + 1)) (Fin.last n) = idMat n := by
        funext i j
        simp only [minorLast, idMat, skipIdx_last]
        by_cases h : i = j
        · subst h; simp
        · have hne : i.castSucc ≠ j.castSucc := fun heq => h (Fin.castSucc_inj.mp heq)
          simp [h, hne]
      rw [hminor, ih]
      simp [idMat, signNat_add_self]
    · intro j hj
      simp [idMat, Ne.symm hj]

theorem alt_multilin_eq_det_mul {n : Nat} (φ : Mat n → Int)
    (hadd : ∀ A r u v, φ (setRow A r (fun j => u j + v j)) = φ (setRow A r u) + φ (setRow A r v))
    (hsmul : ∀ A r c u, φ (setRow A r (fun j => c * u j)) = c * φ (setRow A r u))
    (halt : ∀ A r₁ r₂, r₁ ≠ r₂ → A r₁ = A r₂ → φ A = 0) :
    ∀ A : Mat n, φ A = det A * φ (idMat n) := by
  let ψ : Mat n → Int := fun A => φ A - det A * φ (idMat n)
  have hψ0 : ∀ A, ψ A = 0 := by
    apply alt_multilin_eq_zero ψ
    · intro A r u v
      dsimp only [ψ]
      rw [hadd, det_setRow_add, Int.add_mul]
      omega
    · intro A r c u
      dsimp only [ψ]
      rw [hsmul, det_setRow_smul, Int.mul_assoc, Int.mul_sub]
    · intro A r₁ r₂ hne heq
      dsimp only [ψ]
      rw [halt A r₁ r₂ hne heq, det_eq_zero_of_row_eq A r₁ r₂ hne heq]
      simp
    · dsimp only [ψ]; rw [det_idMat]; omega
  intro A
  have := hψ0 A
  dsimp only [ψ] at this
  omega

theorem det_matMul {n : Nat} (A B : Mat n) : det (matMul A B) = det A * det B := by
  let φ : Mat n → Int := fun X => det (matMul X B)
  have h := alt_multilin_eq_det_mul φ
    (by
      intro X r u v
      dsimp only [φ]
      have heq : matMul (setRow X r (fun j => u j + v j)) B =
          setRow (matMul X B) r (fun j => sumFin (fun k => u k * B k j) + sumFin (fun k => v k * B k j)) := by
        funext i j; simp only [matMul, setRow]
        by_cases hi : i = r
        · subst hi; simp only [↓reduceIte, Int.add_mul, sumFin_add]
        · simp [hi]
      have hu : matMul (setRow X r u) B = setRow (matMul X B) r (fun j => sumFin (fun k => u k * B k j)) := by
        funext i j; simp only [matMul, setRow]; split <;> rfl
      have hv : matMul (setRow X r v) B = setRow (matMul X B) r (fun j => sumFin (fun k => v k * B k j)) := by
        funext i j; simp only [matMul, setRow]; split <;> rfl
      rw [heq, hu, hv, det_setRow_add])
    (by
      intro X r c u
      dsimp only [φ]
      have heq : matMul (setRow X r (fun j => c * u j)) B =
          setRow (matMul X B) r (fun j => c * sumFin (fun k => u k * B k j)) := by
        funext i j; simp only [matMul, setRow]
        by_cases hi : i = r
        · subst hi; simp only [↓reduceIte, Int.mul_assoc, sumFin_mul_left]
        · simp [hi]
      have hu : matMul (setRow X r u) B = setRow (matMul X B) r (fun j => sumFin (fun k => u k * B k j)) := by
        funext i j; simp only [matMul, setRow]; split <;> rfl
      rw [heq, hu, det_setRow_smul])
    (by
      intro X r₁ r₂ hne heq
      dsimp only [φ]
      apply det_eq_zero_of_row_eq _ r₁ r₂ hne
      funext j
      simp only [matMul]
      apply sumFin_congr
      intro k
      rw [congrFun heq k])
    A
  have hid : matMul (idMat n) B = B := by
    funext i j
    simp only [matMul, idMat]
    rw [sumFin_single i]
    · simp
    · intro k hk; simp [Ne.symm hk]
  dsimp only [φ] at h
  rw [hid] at h
  exact h

/-! ### Triangular Matrices, Bi-Scaling, and Mod-2 Finite-Corner Certification Engine -/

theorem det_upper_tri {n : Nat} (A : Mat n) (h : ∀ i j : Fin n, j.val < i.val → A i j = 0) :
    det A = prodFin (fun i => A i i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [det, prodFin]
    rw [sumFin_single (Fin.last n)]
    · have hminor : minorLast A (Fin.last n) = fun i j => A i.castSucc j.castSucc := by
        funext i j; simp only [minorLast, skipIdx_last]
      rw [hminor, ih (fun i j => A i.castSucc j.castSucc) (fun i j hij => h i.castSucc j.castSucc hij)]
      simp [signNat_add_self, Int.mul_comm]
    · intro j hj
      have hlt : j.val < (Fin.last n).val := by
        have := j.isLt
        have hne : j.val ≠ n := fun hv => hj (Fin.ext hv)
        simp; omega
      simp [h (Fin.last n) j hlt]

theorem det_lower_tri {n : Nat} (A : Mat n) (h : ∀ i j : Fin n, i.val < j.val → A i j = 0) :
    det A = prodFin (fun i => A i i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [det, prodFin]
    rw [sumFin_single (Fin.last n)]
    · have hminor : minorLast A (Fin.last n) = fun i j => A i.castSucc j.castSucc := by
        funext i j; simp only [minorLast, skipIdx_last]
      rw [hminor, ih (fun i j => A i.castSucc j.castSucc) (fun i j hij => h i.castSucc j.castSucc hij)]
      simp [signNat_add_self, Int.mul_comm]
    · intro j hj
      cases n with
      | zero => exact absurd (Fin.ext (by omega)) hj
      | succ m =>
        have hcol0 : det (minorLast A j) = 0 := by
          apply det_col_zero (minorLast A j) (Fin.last m)
          intro i
          simp only [minorLast]
          have hskip : skipIdx j (Fin.last m) = Fin.last (m + 1) := by
            apply Fin.ext
            have hnot : ¬ (m < j.val) := by
              have := j.isLt
              have hne : j.val ≠ m + 1 := fun hv => hj (Fin.ext hv)
              omega
            simp [skipIdx, hnot]
          rw [hskip]
          exact h i.castSucc (Fin.last (m + 1)) (by simp)
        rw [hcol0, Int.mul_zero]

theorem det_scaleRows_all {n : Nat} (c : Fin n → Int) (A : Mat n) :
    det (fun i j => c i * A i j) = prodFin c * det A := by
  have hstep : ∀ k : Nat, k ≤ n →
      det (fun i j => (if i.val < k then c i else 1) * A i j) =
        prodFin (fun i => if i.val < k then c i else 1) * det A := by
    intro k
    induction k with
    | zero =>
      intro _
      have h1 : (fun i j => (if i.val < 0 then c i else 1) * A i j) = A := by
        funext i j; simp
      have h2 : prodFin (fun i : Fin n => if i.val < 0 then c i else 1) = 1 := by
        rw [prodFin_congr (g := fun _ => 1) (fun i => by simp)]
        exact prodFin_ones
      rw [h1, h2, Int.one_mul]
    | succ k ih =>
      intro hk
      let r : Fin n := ⟨k, by omega⟩
      let M_prev : Mat n := fun i j => (if i.val < k then c i else 1) * A i j
      have hM : (fun i j => (if i.val < k + 1 then c i else 1) * A i j) =
          setRow M_prev r (fun j => c r * M_prev r j) := by
        funext i j; simp only [setRow, M_prev]
        by_cases hir : i = r
        · subst hir; simp [r]
        · have hnev : i.val ≠ k := fun hv => hir (Fin.ext hv)
          have hiff : (i.val < k + 1) ↔ (i.val < k) := by omega
          simp [hir, hiff]
      rw [hM, det_row_smul, ih (by omega)]
      have hprod : prodFin (fun i : Fin n => if i.val < k + 1 then c i else 1) =
          c r * prodFin (fun i : Fin n => if i.val < k then c i else 1) := by
        have hcongr : (fun i : Fin n => if i.val < k + 1 then c i else 1) =
            (fun i : Fin n => if i = r then c r else (if i.val < k then c i else 1)) := by
          funext i
          by_cases hir : i = r
          · subst hir; simp [r]
          · have hnev : i.val ≠ k := fun hv => hir (Fin.ext hv)
            have hiff : (i.val < k + 1) ↔ (i.val < k) := by omega
            simp [hir, hiff]
        rw [hcongr]
        exact prodFin_update_one (fun i => if i.val < k then c i else 1) r (c r) (by simp [r])
      rw [hprod, Int.mul_assoc]
  have hfinal := hstep n (Nat.le_refl n)
  have h1 : (fun i j => (if i.val < n then c i else 1) * A i j) = (fun i j => c i * A i j) := by
    funext i j; simp [i.isLt]
  have h2 : prodFin (fun i : Fin n => if i.val < n then c i else 1) = prodFin c :=
    prodFin_congr (fun i => by simp [i.isLt])
  rw [h1, h2] at hfinal
  exact hfinal

theorem det_scaleCols_all {n : Nat} (d : Fin n → Int) (A : Mat n) :
    det (fun i j => d j * A i j) = prodFin d * det A := by
  have hstep : ∀ k : Nat, k ≤ n →
      det (fun i j => (if j.val < k then d j else 1) * A i j) =
        prodFin (fun j => if j.val < k then d j else 1) * det A := by
    intro k
    induction k with
    | zero =>
      intro _
      have h1 : (fun i j => (if j.val < 0 then d j else 1) * A i j) = A := by
        funext i j; simp
      have h2 : prodFin (fun j : Fin n => if j.val < 0 then d j else 1) = 1 := by
        rw [prodFin_congr (g := fun _ => 1) (fun j => by simp)]
        exact prodFin_ones
      rw [h1, h2, Int.one_mul]
    | succ k ih =>
      intro hk
      let col : Fin n := ⟨k, by omega⟩
      let M_prev : Mat n := fun i j => (if j.val < k then d j else 1) * A i j
      have hM : (fun i j => (if j.val < k + 1 then d j else 1) * A i j) =
          scaleCol M_prev col (d col) := by
        funext i j; simp only [scaleCol, M_prev]
        by_cases hj : j = col
        · subst hj; simp [col]
        · have hnev : j.val ≠ k := fun hv => hj (Fin.ext hv)
          have hiff : (j.val < k + 1) ↔ (j.val < k) := by omega
          simp [hj, hiff]
      rw [hM, det_scaleCol, ih (by omega)]
      have hprod : prodFin (fun j : Fin n => if j.val < k + 1 then d j else 1) =
          d col * prodFin (fun j : Fin n => if j.val < k then d j else 1) := by
        have hcongr : (fun j : Fin n => if j.val < k + 1 then d j else 1) =
            (fun j : Fin n => if j = col then d col else (if j.val < k then d j else 1)) := by
          funext j
          by_cases hj : j = col
          · subst hj; simp [col]
          · have hnev : j.val ≠ k := fun hv => hj (Fin.ext hv)
            have hiff : (j.val < k + 1) ↔ (j.val < k) := by omega
            simp [hj, hiff]
        rw [hcongr]
        exact prodFin_update_one (fun j => if j.val < k then d j else 1) col (d col) (by simp [col])
      rw [hprod, Int.mul_assoc]
  have hfinal := hstep n (Nat.le_refl n)
  have h1 : (fun i j => (if j.val < n then d j else 1) * A i j) = (fun i j => d j * A i j) := by
    funext i j; simp [j.isLt]
  have h2 : prodFin (fun j : Fin n => if j.val < n then d j else 1) = prodFin d :=
    prodFin_congr (fun j => by simp [j.isLt])
  rw [h1, h2] at hfinal
  exact hfinal

theorem det_biScale {n : Nat} (a b : Fin n → Nat) (Ω : Mat n) :
    det (biScale a b Ω) = (2 : Int) ^ (sumNat (fun i => a i + b i)) * det Ω := by
  have heq : biScale a b Ω = fun i j => (2 : Int) ^ (a i) * ((2 : Int) ^ (b j) * Ω i j) := by
    funext i j
    simp only [biScale, Int.pow_add, Int.mul_assoc]
  rw [heq, det_scaleRows_all, det_scaleCols_all, prodFin_two_pow, prodFin_two_pow]
  rw [← Int.mul_assoc, ← Int.pow_add, ← sumNat_add]

theorem det_odd_of_mod2_inv {n : Nat} (R Ω : Mat n)
    (hinv : ∀ i j, matMul R Ω i j % 2 = idMat n i j) : det Ω % 2 = 1 := by
  have h1 : det (matMul R Ω) % 2 = det (idMat n) % 2 := by
    apply det_mod2_congr
    intro i j
    rw [hinv i j]
    simp only [idMat]
    split <;> rfl
  rw [det_matMul, det_idMat] at h1
  have h2 : (det R % 2) * (det Ω % 2) % 2 = 1 := by
    rw [← Int.mul_emod]
    exact h1
  have hO0 := Int.emod_nonneg (det Ω) (by omega : (2 : Int) ≠ 0)
  have hO2 := Int.emod_lt_of_pos (det Ω) (by omega : (0 : Int) < 2)
  by_cases h0 : det Ω % 2 = 0
  · rw [h0] at h2; simp at h2
  · omega

/-! ### Finite-Corner-to-∞ Mod-2 Certification Lifter -/

theorem det_mod2_strip_last {m : Nat} (Ω : Mat (m + 1))
    (hlast : ∀ j : Fin (m + 1), Ω (Fin.last m) j % 2 = if j = Fin.last m then 1 else 0) :
    det Ω % 2 = det (fun (i j : Fin m) => Ω i.castSucc j.castSucc) % 2 := by
  let Ω' : Mat (m + 1) := fun i j =>
    if i = Fin.last m then (if j = Fin.last m then 1 else 0) else Ω i j
  have hcongr : det Ω % 2 = det Ω' % 2 := by
    apply det_mod2_congr
    intro i j
    dsimp only [Ω']
    by_cases hi : i = Fin.last m
    · subst hi
      simp only [↓reduceIte, hlast j]
      split <;> rfl
    · simp only [hi, ↓reduceIte]
  rw [hcongr]
  have hdet' : det Ω' = det (fun (i j : Fin m) => Ω i.castSucc j.castSucc) := by
    simp only [det]
    rw [sumFin_single (Fin.last m)]
    · have hminor : minorLast Ω' (Fin.last m) = fun i j => Ω i.castSucc j.castSucc := by
        funext i j
        simp only [minorLast, Ω', castSucc_ne_last, ↓reduceIte, skipIdx_last]
      rw [hminor]
      simp [Ω', signNat_add_self]
    · intro j hj
      simp [Ω', hj]
  rw [hdet']

/-- General Finite-Corner-to-∞ Mod-2 Certification Lifter:
    If `k ≤ n`, `Ω : Mat n` agrees mod 2 with `idMat n` for all rows `i ≥ k`,
    and the leading `k × k` corner admits an `F_2`-left-inverse `R : Mat k`,
    then `det Ω % 2 = 1`! -/
theorem det_odd_of_finite_corner {n k : Nat} (hk : k ≤ n) (Ω : Mat n)
    (houtside : ∀ (i j : Fin n), k ≤ i.val → Ω i j % 2 = if i = j then 1 else 0)
    (R : Mat k)
    (hinv : ∀ (i j : Fin k),
      matMul R (fun a b => Ω ⟨a.val, by omega⟩ ⟨b.val, by omega⟩) i j % 2 = idMat k i j) :
    det Ω % 2 = 1 := by
  have hgo : ∀ d : Nat, ∀ (Ω : Mat (k + d)),
      (∀ (i j : Fin (k + d)), k ≤ i.val → Ω i j % 2 = if i = j then 1 else 0) →
      (∀ (i j : Fin k),
        matMul R (fun a b => Ω ⟨a.val, by omega⟩ ⟨b.val, by omega⟩) i j % 2 = idMat k i j) →
      det Ω % 2 = 1 := by
    intro d
    induction d with
    | zero =>
      intro Ω _ hinv'
      exact det_odd_of_mod2_inv R Ω hinv'
    | succ d ih =>
      intro Ω hout hinv'
      have hstrip := det_mod2_strip_last Ω (fun j => by
        have := hout (Fin.last (k + d)) j (by simp)
        simpa [eq_comm] using this)
      rw [hstrip]
      apply ih (fun i j => Ω i.castSucc j.castSucc)
      · intro i j hi
        have := hout i.castSucc j.castSucc hi
        have hiff : (i.castSucc = j.castSucc) ↔ (i = j) := Fin.castSucc_inj
        simpa [hiff] using this
      · intro i j
        exact hinv' i j
  rcases (⟨n - k, by omega⟩ : ∃ d, n = k + d) with ⟨d, rfl⟩
  exact hgo d Ω houtside hinv

/-! ### Exact 2-Adic Valuation Predicate & Reusable Elimination Engine Theorems -/

theorem two_pow_pos (v : Nat) : (0 : Int) < (2 : Int) ^ v := by
  induction v with
  | zero => decide
  | succ v ih =>
    rw [Int.pow_succ]
    omega

theorem HasV2_ne_zero {x : Int} {v : Nat} (h : HasV2 x v) : x ≠ 0 := by
  rcases h with ⟨u, hu, rfl⟩
  intro h0
  have h2 : (2 : Int) ^ v ≠ 0 := by have := two_pow_pos v; omega
  rcases Int.mul_eq_zero.mp h0 with hpow | hu0
  · exact h2 hpow
  · omega

theorem HasV2_unique {x : Int} {v₁ v₂ : Nat} (h₁ : HasV2 x v₁) (h₂ : HasV2 x v₂) :
    v₁ = v₂ := by
  rcases h₁ with ⟨u₁, hu₁, hx₁⟩
  rcases h₂ with ⟨u₂, hu₂, hx₂⟩
  have hcancel : ∀ a b : Nat, ∀ s t : Int, s % 2 = 1 → t % 2 = 1 →
      (2 : Int) ^ a * s = (2 : Int) ^ b * t → a = b := by
    intro a
    induction a with
    | zero =>
      intro b s t hs ht heq
      cases b with
      | zero => rfl
      | succ b =>
        rw [Int.pow_zero, Int.one_mul, Int.pow_succ] at heq
        have heven : s = 2 * ((2 : Int) ^ b * t) := by
          rw [heq, Int.mul_right_comm, Int.mul_comm]
        omega
    | succ a iha =>
      intro b s t hs ht heq
      cases b with
      | zero =>
        rw [Int.pow_zero, Int.one_mul, Int.pow_succ] at heq
        have heven : t = 2 * ((2 : Int) ^ a * s) := by
          rw [← heq, Int.mul_right_comm, Int.mul_comm]
        omega
      | succ b =>
        rw [Int.pow_succ, Int.pow_succ] at heq
        have h2a : (2 : Int) ^ a * 2 * s = 2 * ((2 : Int) ^ a * s) := by
          rw [Int.mul_right_comm, Int.mul_comm]
        have h2b : (2 : Int) ^ b * 2 * t = 2 * ((2 : Int) ^ b * t) := by
          rw [Int.mul_right_comm, Int.mul_comm]
        rw [h2a, h2b] at heq
        have hstep : (2 : Int) ^ a * s = (2 : Int) ^ b * t := by omega
        exact congrArg Nat.succ (iha b s t hs ht hstep)
  exact hcancel v₁ v₂ u₁ u₂ hu₁ hu₂ (hx₁.symm.trans hx₂)

/-- **Reusable Engine Theorem 1 (2-Adic Bi-Scaled Block-Elimination & Finite-Corner Engine):**
    Given ANY `n : Nat`, integer matrix `M : Mat n`, unimodular transforms `U, V : Mat n`,
    asymmetric 2-adic scaling profile `a, b : Fin n → Nat`, quotient matrix `Ω : Mat n`,
    and finite corner size `k ≤ n`:
    If `U * M * V = biScale a b Ω`, `Ω` agrees mod 2 with `idMat n` for rows `i ≥ k`,
    and the finite `k × k` corner has an `F_2`-left-inverse `R : Mat k`,
    then `HasV2 (det M) (∑ i, (a i + b i))`. -/
theorem v2_det_biscaled_elimination_engine
    {n k : Nat} (hk : k ≤ n) (M U V Ω : Mat n) (a b : Fin n → Nat)
    (hU : det U = 1) (hV : det V = 1)
    (hfac : matMul (matMul U M) V = biScale a b Ω)
    (houtside : ∀ (i j : Fin n), k ≤ i.val → Ω i j % 2 = if i = j then 1 else 0)
    (R : Mat k)
    (hinv : ∀ (i j : Fin k),
      matMul R (fun r c => Ω ⟨r.val, by omega⟩ ⟨c.val, by omega⟩) i j % 2 = idMat k i j) :
    HasV2 (det M) (sumNat (fun i => a i + b i)) := by
  have hdet : det M = (2 : Int) ^ (sumNat (fun i => a i + b i)) * det Ω := by
    have h1 := congrArg det hfac
    rw [det_matMul, det_matMul, hU, hV, Int.one_mul, Int.mul_one, det_biScale] at h1
    exact h1
  have hodd : det Ω % 2 = 1 := det_odd_of_finite_corner hk Ω houtside R hinv
  exact ⟨det Ω, hodd, hdet⟩

/-- **Reusable Engine Theorem 2 (2-Adic Perturbation Stability Lifter):**
    Under the same bi-scaled elimination factorization of `M`, adding ANY integer perturbation `Δ`
    whose transformed matrix `U * Δ * V` satisfies `2^(a i + b j + 1) ∣ (U * Δ * V) i j`
    leaves `v_2(det (M + Δ))` strictly invariant! -/
theorem v2_det_perturbation_stability
    {n k : Nat} (hk : k ≤ n) (M Δ U V Ω E : Mat n) (a b : Fin n → Nat)
    (hU : det U = 1) (hV : det V = 1)
    (hfacM : matMul (matMul U M) V = biScale a b Ω)
    (hfacΔ : matMul (matMul U Δ) V = fun i j => (2 : Int) ^ (a i + b j + 1) * E i j)
    (houtside : ∀ (i j : Fin n), k ≤ i.val → Ω i j % 2 = if i = j then 1 else 0)
    (R : Mat k)
    (hinv : ∀ (i j : Fin k),
      matMul R (fun r c => Ω ⟨r.val, by omega⟩ ⟨c.val, by omega⟩) i j % 2 = idMat k i j) :
    HasV2 (det (matAdd M Δ)) (sumNat (fun i => a i + b i)) := by
  let Ω' : Mat n := fun i j => Ω i j + 2 * E i j
  have hfac' : matMul (matMul U (matAdd M Δ)) V = biScale a b Ω' := by
    funext i j
    have hlin : matMul (matMul U (matAdd M Δ)) V i j =
        matMul (matMul U M) V i j + matMul (matMul U Δ) V i j := by
      simp only [matMul, matAdd]
      rw [← sumFin_add]
      apply sumFin_congr
      intro c
      rw [← Int.add_mul]
      congr 1
      rw [← sumFin_add]
      apply sumFin_congr
      intro l
      rw [Int.mul_add]
    rw [hlin, hfacM, hfacΔ]
    simp only [biScale, Ω', Int.pow_succ, Int.mul_add]
    rw [Int.mul_assoc ((2 : Int) ^ (a i + b j)) 2 (E i j)]
  have hmod : ∀ i j, Ω' i j % 2 = Ω i j % 2 := by
    intro i j; dsimp only [Ω']; omega
  exact v2_det_biscaled_elimination_engine hk (matAdd M Δ) U V Ω' a b hU hV hfac'
    (fun i j hi => by rw [hmod, houtside i j hi])
    R
    (fun i j => by
      have hmul_mod : matMul R (fun r c => Ω' ⟨r.val, by omega⟩ ⟨c.val, by omega⟩) i j % 2 =
          matMul R (fun r c => Ω ⟨r.val, by omega⟩ ⟨c.val, by omega⟩) i j % 2 := by
        simp only [matMul]
        apply sumFin_mod2_congr
        intro c
        rw [Int.mul_emod, hmod, ← Int.mul_emod]
      rw [hmul_mod, hinv i j])

theorem popFuel_eq_of_ge : ∀ n f₁ f₂ : Nat, n ≤ f₁ → n ≤ f₂ → popFuel f₁ n = popFuel f₂ n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f₁ f₂ h1 h2
    cases n with
    | zero =>
      cases f₁ <;> cases f₂ <;> simp [popFuel]
    | succ m =>
      cases f₁ with
      | zero => omega
      | succ f₁ =>
        cases f₂ with
        | zero => omega
        | succ f₂ =>
          simp only [popFuel, Nat.succ_ne_zero, ↓reduceIte]
          congr 1
          exact ih ((m + 1) / 2) (by omega) f₁ f₂ (by omega) (by omega)

theorem pop_zero : pop 0 = 0 := rfl

theorem pop_eq (n : Nat) : pop n = n % 2 + pop (n / 2) := by
  cases n with
  | zero => rfl
  | succ m =>
    unfold pop
    simp only [popFuel, Nat.succ_ne_zero, ↓reduceIte]
    congr 1
    exact popFuel_eq_of_ge ((m + 1) / 2) m ((m + 1) / 2) (by omega) (Nat.le_refl _)

theorem pop_two_mul_add (q b : Nat) (hb : b < 2) : pop (2 * q + b) = b + pop q := by
  rw [pop_eq]
  have h1 : (2 * q + b) % 2 = b := by omega
  have h2 : (2 * q + b) / 2 = q := by omega
  rw [h1, h2]

theorem pop_two_mul (q : Nat) : pop (2 * q) = pop q := by
  have h := pop_two_mul_add q 0 (by omega)
  simpa using h

theorem pop_two_mul_add_one (q : Nat) : pop (2 * q + 1) = 1 + pop q :=
  pop_two_mul_add q 1 (by omega)

theorem pop_pos_of_ne_zero {n : Nat} (h : n ≠ 0) : 1 ≤ pop n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [pop_eq]
    by_cases hmod : n % 2 = 1
    · omega
    · have hdiv : n / 2 ≠ 0 := by omega
      have hlt : n / 2 < n := by omega
      have := ih (n / 2) hlt hdiv
      omega

theorem pop_eq_zero_iff (n : Nat) : pop n = 0 ↔ n = 0 := by
  constructor
  · intro h
    cases n with
    | zero => rfl
    | succ m =>
      have hpos : 1 ≤ pop (m + 1) := pop_pos_of_ne_zero (by omega)
      omega
  · intro h
    subst h
    exact pop_zero

theorem v2SuccFuel_eq_of_ge : ∀ n f₁ f₂ : Nat, n ≤ f₁ → n ≤ f₂ → v2SuccFuel f₁ n = v2SuccFuel f₂ n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f₁ f₂ h1 h2
    cases n with
    | zero =>
      cases f₁ <;> cases f₂ <;> simp [v2SuccFuel]
    | succ m =>
      cases f₁ with
      | zero => omega
      | succ f₁ =>
        cases f₂ with
        | zero => omega
        | succ f₂ =>
          simp only [v2SuccFuel]
          by_cases hp : (m + 1) % 2 = 1
          · simp only [hp, ↓reduceIte]
            congr 1
            exact ih ((m + 1) / 2) (by omega) f₁ f₂ (by omega) (by omega)
          · simp [hp]

theorem v2Succ_zero : v2Succ 0 = 0 := rfl

theorem v2Succ_two_mul (q : Nat) : v2Succ (2 * q) = 0 := by
  cases q with
  | zero => rfl
  | succ q =>
    have heq : 2 * (q + 1) = (2 * q + 1) + 1 := by omega
    rw [heq]
    unfold v2Succ
    have hmod : ((2 * q + 1) + 1) % 2 ≠ 1 := by omega
    simp [v2SuccFuel, hmod]

theorem v2Succ_two_mul_add_one (q : Nat) : v2Succ (2 * q + 1) = 1 + v2Succ q := by
  unfold v2Succ
  have hmod : (2 * q + 1) % 2 = 1 := by omega
  have hdiv : (2 * q + 1) / 2 = q := by omega
  simp only [v2SuccFuel, hmod, ↓reduceIte, hdiv]
  congr 1
  exact v2SuccFuel_eq_of_ge q (2 * q) q (by omega) (Nat.le_refl q)

theorem v2Succ_spec (x : Nat) : ∃ m : Nat, m % 2 = 1 ∧ x + 1 = 2 ^ (v2Succ x) * m := by
  induction x using Nat.strongRecOn with
  | ind x ih =>
    by_cases hpar : x % 2 = 0
    · have hx : x = 2 * (x / 2) := by omega
      rw [hx, v2Succ_two_mul]
      refine ⟨2 * (x / 2) + 1, by omega, by simp⟩
    · have hx : x = 2 * (x / 2) + 1 := by omega
      have hlt : x / 2 < x := by omega
      rcases ih (x / 2) hlt with ⟨m, hm, heq⟩
      rw [hx, v2Succ_two_mul_add_one]
      refine ⟨m, hm, ?_⟩
      rw [Nat.add_comm 1, Nat.pow_succ, Nat.mul_right_comm, Nat.mul_comm _ 2, ← heq]
      omega

/-- Fundamental LSB bit-slicing lemmas for `&&&`, `|||`, `^^^`. -/
theorem land_mod_two (a b : Nat) : (a &&& b) % 2 = (a % 2) &&& (b % 2) := by
  have h := Nat.testBit_and a b 0
  simp only [Nat.testBit_zero] at h
  rcases (by omega : a % 2 = 0 ∨ a % 2 = 1) with ha | ha <;>
  rcases (by omega : b % 2 = 0 ∨ b % 2 = 1) with hb | hb <;>
  rcases (by omega : (a &&& b) % 2 = 0 ∨ (a &&& b) % 2 = 1) with hab | hab <;>
  simp [ha, hb, hab] at h ⊢

theorem lor_mod_two (a b : Nat) : (a ||| b) % 2 = (a % 2) ||| (b % 2) := by
  have h := Nat.testBit_or a b 0
  simp only [Nat.testBit_zero] at h
  rcases (by omega : a % 2 = 0 ∨ a % 2 = 1) with ha | ha <;>
  rcases (by omega : b % 2 = 0 ∨ b % 2 = 1) with hb | hb <;>
  rcases (by omega : (a ||| b) % 2 = 0 ∨ (a ||| b) % 2 = 1) with hab | hab <;>
  simp [ha, hb, hab] at h ⊢

theorem xor_mod_two (a b : Nat) : (a ^^^ b) % 2 = (a % 2) ^^^ (b % 2) := by
  have h := Nat.testBit_xor a b 0
  simp only [Nat.testBit_zero] at h
  rcases (by omega : a % 2 = 0 ∨ a % 2 = 1) with ha | ha <;>
  rcases (by omega : b % 2 = 0 ∨ b % 2 = 1) with hb | hb <;>
  rcases (by omega : (a ^^^ b) % 2 = 0 ∨ (a ^^^ b) % 2 = 1) with hab | hab <;>
  simp [ha, hb, hab] at h ⊢

theorem land_div_two (a b : Nat) : (a &&& b) / 2 = (a / 2) &&& (b / 2) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_div_two, Nat.testBit_and, Nat.testBit_and, Nat.testBit_div_two, Nat.testBit_div_two]

theorem lor_div_two (a b : Nat) : (a ||| b) / 2 = (a / 2) ||| (b / 2) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_div_two, Nat.testBit_or, Nat.testBit_or, Nat.testBit_div_two, Nat.testBit_div_two]

theorem xor_div_two (a b : Nat) : (a ^^^ b) / 2 = (a / 2) ^^^ (b / 2) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_div_two, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_div_two, Nat.testBit_div_two]

theorem land_comm_nat (a b : Nat) : a &&& b = b &&& a := by
  apply Nat.eq_of_testBit_eq; intro k; simp [Nat.testBit_and, Bool.and_comm]

theorem land_self_nat (a : Nat) : a &&& a = a := by
  apply Nat.eq_of_testBit_eq; intro k; simp

theorem lor_eq_zero_iff (a b : Nat) : (a ||| b = 0) ↔ (a = 0 ∧ b = 0) := by
  constructor
  · intro h
    constructor
    · apply Nat.eq_of_testBit_eq; intro k
      have hk := congrArg (fun x => x.testBit k) h
      simp [Nat.testBit_or] at hk
      simp [hk.1]
    · apply Nat.eq_of_testBit_eq; intro k
      have hk := congrArg (fun x => x.testBit k) h
      simp [Nat.testBit_or] at hk
      simp [hk.2]
  · rintro ⟨rfl, rfl⟩; rfl

theorem land_two_mul_add (a b : Nat) {ba bb : Nat} (ha : ba < 2) (hb : bb < 2) :
    (2 * a + ba) &&& (2 * b + bb) = 2 * (a &&& b) + (ba &&& bb) := by
  have hdiv : ((2 * a + ba) &&& (2 * b + bb)) / 2 = a &&& b := by
    rw [land_div_two]
    have h1 : (2 * a + ba) / 2 = a := by omega
    have h2 : (2 * b + bb) / 2 = b := by omega
    rw [h1, h2]
  have hmod : ((2 * a + ba) &&& (2 * b + bb)) % 2 = ba &&& bb := by
    rw [land_mod_two]
    have h1 : (2 * a + ba) % 2 = ba := by omega
    have h2 : (2 * b + bb) % 2 = bb := by omega
    rw [h1, h2]
  omega

theorem lor_two_mul_add (a b : Nat) {ba bb : Nat} (ha : ba < 2) (hb : bb < 2) :
    (2 * a + ba) ||| (2 * b + bb) = 2 * (a ||| b) + (ba ||| bb) := by
  have hdiv : ((2 * a + ba) ||| (2 * b + bb)) / 2 = a ||| b := by
    rw [lor_div_two]
    have h1 : (2 * a + ba) / 2 = a := by omega
    have h2 : (2 * b + bb) / 2 = b := by omega
    rw [h1, h2]
  have hmod : ((2 * a + ba) ||| (2 * b + bb)) % 2 = ba ||| bb := by
    rw [lor_mod_two]
    have h1 : (2 * a + ba) % 2 = ba := by omega
    have h2 : (2 * b + bb) % 2 = bb := by omega
    rw [h1, h2]
  omega

theorem xor_two_mul_add (a b : Nat) {ba bb : Nat} (ha : ba < 2) (hb : bb < 2) :
    (2 * a + ba) ^^^ (2 * b + bb) = 2 * (a ^^^ b) + (ba ^^^ bb) := by
  have hdiv : ((2 * a + ba) ^^^ (2 * b + bb)) / 2 = a ^^^ b := by
    rw [xor_div_two]
    have h1 : (2 * a + ba) / 2 = a := by omega
    have h2 : (2 * b + bb) / 2 = b := by omega
    rw [h1, h2]
  have hmod : ((2 * a + ba) ^^^ (2 * b + bb)) % 2 = ba ^^^ bb := by
    rw [xor_mod_two]
    have h1 : (2 * a + ba) % 2 = ba := by omega
    have h2 : (2 * b + bb) % 2 = bb := by omega
    rw [h1, h2]
  omega

theorem submask_iff (u i : Nat) :
    submask u i = true ↔ (u % 2 ≤ i % 2 ∧ submask (u / 2) (i / 2) = true) := by
  simp only [submask, beq_iff_eq]
  constructor
  · intro h
    have hdiv : (u / 2) &&& (i / 2) = u / 2 := by rw [← land_div_two, h]
    have hmod : (u % 2) &&& (i % 2) = u % 2 := by rw [← land_mod_two, h]
    rcases (by omega : u % 2 = 0 ∨ u % 2 = 1) with hu | hu <;>
    rcases (by omega : i % 2 = 0 ∨ i % 2 = 1) with hi | hi <;>
    simp [hu, hi] at hmod <;> exact ⟨by omega, hdiv⟩
  · rintro ⟨hle, hdiv⟩
    have hu : u = 2 * (u / 2) + u % 2 := by omega
    have hi : i = 2 * (i / 2) + i % 2 := by omega
    rw [hu, hi, land_two_mul_add _ _ (by omega) (by omega), hdiv]
    rcases (by omega : u % 2 = 0 ∨ u % 2 = 1) with hu' | hu' <;>
    rcases (by omega : i % 2 = 0 ∨ i % 2 = 1) with hi' | hi' <;>
    simp [hu', hi'] at hle ⊢

theorem submask_two_mul_add (a b : Nat) {ba bb : Nat} (ha : ba < 2) (hb : bb < 2) :
    submask (2 * a + ba) (2 * b + bb) = (decide (ba ≤ bb) && submask a b) := by
  have h1 : (2 * a + ba) % 2 = ba := by omega
  have h2 : (2 * b + bb) % 2 = bb := by omega
  have h3 : (2 * a + ba) / 2 = a := by omega
  have h4 : (2 * b + bb) / 2 = b := by omega
  cases h : submask (2 * a + ba) (2 * b + bb)
  · symm
    cases hle : decide (ba ≤ bb)
    · rfl
    · cases hs : submask a b
      · rfl
      · exfalso
        have htrue : submask (2 * a + ba) (2 * b + bb) = true := by
          rw [submask_iff, h1, h2, h3, h4]
          exact ⟨of_decide_eq_true hle, hs⟩
        rw [h] at htrue; cases htrue
  · rw [submask_iff, h1, h2, h3, h4] at h
    rw [decide_eq_true h.1, h.2]; rfl

theorem submask_le {u i : Nat} (h : submask u i = true) : u ≤ i := by
  induction i using Nat.strongRecOn generalizing u with
  | ind i ih =>
    cases i with
    | zero => simp [submask] at h; omega
    | succ i =>
      rw [submask_iff] at h
      have hdiv := ih ((i + 1) / 2) (by omega) h.2
      omega

theorem submask_self (i : Nat) : submask i i = true := by
  simp [submask]

theorem pop_or_add_and (i j : Nat) : pop (i ||| j) + pop (i &&& j) = pop i + pop j := by
  induction i using Nat.strongRecOn generalizing j with
  | ind i ih =>
    by_cases hi : i = 0
    · subst hi; simp [pop_zero]
    · rw [pop_eq (i ||| j), pop_eq (i &&& j), pop_eq i, pop_eq j]
      rw [lor_mod_two, land_mod_two, lor_div_two, land_div_two]
      have hsub := ih (i / 2) (by omega) (j / 2)
      rcases (by omega : i % 2 = 0 ∨ i % 2 = 1) with ha | ha <;>
      rcases (by omega : j % 2 = 0 ∨ j % 2 = 1) with hb | hb <;>
      simp [ha, hb] <;> omega

theorem pop_submask_add {u i : Nat} (h : submask u i = true) :
    pop (i ^^^ u) + pop u = pop i := by
  induction i using Nat.strongRecOn generalizing u with
  | ind i ih =>
    by_cases hi : i = 0
    · subst hi; simp [submask] at h; subst h; simp [pop_zero]
    · rw [submask_iff] at h
      rw [pop_eq (i ^^^ u), pop_eq u, pop_eq i, xor_mod_two, xor_div_two]
      have hsub := ih (i / 2) (by omega) h.2
      rcases (by omega : u % 2 = 0 ∨ u % 2 = 1) with ha | ha <;>
      rcases (by omega : i % 2 = 0 ∨ i % 2 = 1) with hb | hb <;>
      simp [ha, hb] at h ⊢ <;> omega

theorem pop_and_le_left (i j : Nat) : pop (i &&& j) ≤ pop i := by
  have h : submask (i &&& j) i = true := by
    simp only [submask, beq_iff_eq]
    apply Nat.eq_of_testBit_eq; intro k
    simp only [Nat.testBit_and]
    cases i.testBit k <;> cases j.testBit k <;> rfl
  have := pop_submask_add h
  omega

theorem pop_and_le_right (i j : Nat) : pop (i &&& j) ≤ pop j := by
  rw [land_comm_nat]
  exact pop_and_le_left j i

theorem pop_pow_two_sub_one (k : Nat) : pop (2 ^ k - 1) = k := by
  induction k with
  | zero => simp [pop_zero]
  | succ k ih =>
    have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have heq : 2 ^ (k + 1) - 1 = 2 * (2 ^ k - 1) + 1 := by
      rw [Nat.pow_succ]; omega
    rw [heq, pop_two_mul_add_one, ih]
    omega

/-! ### Boolean Möbius Matrix `mobMat` and Bit-Sliced Double Möbius Transform -/

theorem det_mobMat (n : Nat) : det (mobMat n) = 1 := by
  rw [det_lower_tri]
  · rw [prodFin_congr (g := fun _ => 1)]
    · exact prodFin_ones
    · intro i
      simp [mobMat, mobCoeff, submask_self, pop_zero, signNat]
  · intro i j hij
    simp only [mobMat, mobCoeff]
    by_cases hs : submask j.val i.val = true
    · have hle := submask_le hs; omega
    · simp [hs]

theorem det_mobMat_transpose (n : Nat) : det (transpose (mobMat n)) = 1 := by
  rw [det_upper_tri]
  · rw [prodFin_congr (g := fun _ => 1)]
    · exact prodFin_ones
    · intro i
      simp [transpose, mobMat, mobCoeff, submask_self, pop_zero, signNat]
  · intro i j hij
    simp only [transpose, mobMat, mobCoeff]
    by_cases hs : submask i.val j.val = true
    · have hle := submask_le hs; omega
    · simp [hs]

theorem sumFin_eq_sumRange {n : Nat} (f : Nat → Int) :
    sumFin (fun i : Fin n => f i.val) = sumRange n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumFin, sumRange, Fin.val_castSucc, Fin.val_last]
    rw [ih]

theorem sumRange_congr {m : Nat} {f g : Nat → Int} (h : ∀ k < m, f k = g k) :
    sumRange m f = sumRange m g := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [sumRange]
    rw [ih (fun k hk => h k (by omega)), h m (by omega)]

theorem sumRange_zero {m : Nat} : sumRange m (fun _ => 0) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [sumRange, ih]

theorem sumRange_add {m : Nat} (f g : Nat → Int) :
    sumRange m (fun k => f k + g k) = sumRange m f + sumRange m g := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [sumRange, ih]; omega

theorem sumRange_sub {m : Nat} (f g : Nat → Int) :
    sumRange m (fun k => f k - g k) = sumRange m f - sumRange m g := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [sumRange, ih]; omega

theorem sumRange_mul_left {m : Nat} (c : Int) (f : Nat → Int) :
    sumRange m (fun k => c * f k) = c * sumRange m f := by
  induction m with
  | zero => simp [sumRange]
  | succ m ih => simp only [sumRange, ih, Int.mul_add]

theorem sumRange_extend {m₁ m₂ : Nat} (hle : m₁ ≤ m₂) (f : Nat → Int)
    (hzero : ∀ k, m₁ ≤ k → k < m₂ → f k = 0) :
    sumRange m₁ f = sumRange m₂ f := by
  induction m₂ with
  | zero =>
    have : m₁ = 0 := by omega
    subst this; rfl
  | succ m₂ ih =>
    by_cases hlt : m₁ ≤ m₂
    · simp only [sumRange]
      rw [← ih hlt (fun k h1 h2 => hzero k h1 (by omega)), hzero m₂ hlt (by omega), Int.add_zero]
    · have : m₁ = m₂ + 1 := by omega
      subst this; rfl

theorem sumRange_even_odd (m : Nat) (f : Nat → Int) :
    sumRange (2 * m) f = sumRange m (fun k => f (2 * k)) + sumRange m (fun k => f (2 * k + 1)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have heq : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
    rw [heq]
    simp only [sumRange]
    rw [ih]
    omega

theorem mob1_eq_sumRange {n : Nat} (g : Nat → Int) {i : Nat} (hi : i < n) :
    sumRange n (fun u => mobCoeff i u * g u) = mob1 g i := by
  symm
  apply sumRange_extend (by omega)
  intro u hu _
  simp only [mobCoeff]
  by_cases hs : submask u i = true
  · have := submask_le hs; omega
  · simp [hs]

theorem mob1_bit_zero (g : Nat → Int) (q : Nat) :
    mob1 g (2 * q) = mob1 (fun u => g (2 * u)) q := by
  unfold mob1
  have h1 : sumRange (2 * q + 1) (fun u => mobCoeff (2 * q) u * g u) =
      sumRange (2 * (q + 1)) (fun u => mobCoeff (2 * q) u * g u) := by
    apply sumRange_extend (by omega)
    intro u hu _
    simp only [mobCoeff]
    by_cases hs : submask u (2 * q) = true
    · have := submask_le hs; omega
    · simp [hs]
  rw [h1, sumRange_even_odd]
  have hodd : sumRange (q + 1) (fun k => mobCoeff (2 * q) (2 * k + 1) * g (2 * k + 1)) = 0 := by
    rw [sumRange_congr (g := fun _ => 0)]
    · exact sumRange_zero
    · intro k _
      have hs : submask (2 * k + 1) (2 * q) = false := by
        simpa using submask_two_mul_add k q (ba := 1) (bb := 0) (by omega) (by omega)
      simp [mobCoeff, hs]
  rw [hodd, Int.add_zero]
  apply sumRange_congr
  intro k _
  have hs : submask (2 * k) (2 * q) = submask k q := by
    simpa using submask_two_mul_add k q (ba := 0) (bb := 0) (by omega) (by omega)
  have hpop : pop ((2 * q) ^^^ (2 * k)) = pop (q ^^^ k) := by
    have hx : (2 * q) ^^^ (2 * k) = 2 * (q ^^^ k) := by
      simpa using xor_two_mul_add q k (ba := 0) (bb := 0) (by omega) (by omega)
    rw [hx, pop_two_mul]
  simp [mobCoeff, hs, hpop]

theorem mob1_bit_one (g : Nat → Int) (q : Nat) :
    mob1 g (2 * q + 1) = mob1 (fun u => g (2 * u + 1) - g (2 * u)) q := by
  unfold mob1
  have heq : 2 * q + 1 + 1 = 2 * (q + 1) := by omega
  rw [heq, sumRange_even_odd]
  have heven : sumRange (q + 1) (fun k => mobCoeff (2 * q + 1) (2 * k) * g (2 * k)) =
      sumRange (q + 1) (fun k => -(mobCoeff q k * g (2 * k))) := by
    apply sumRange_congr
    intro k _
    have hs : submask (2 * k) (2 * q + 1) = submask k q := by
      simpa using submask_two_mul_add k q (ba := 0) (bb := 1) (by omega) (by omega)
    have hpop : pop ((2 * q + 1) ^^^ (2 * k)) = 1 + pop (q ^^^ k) := by
      have hx : (2 * q + 1) ^^^ (2 * k) = 2 * (q ^^^ k) + 1 := by
        simpa using xor_two_mul_add q k (ba := 1) (bb := 0) (by omega) (by omega)
      rw [hx, pop_two_mul_add_one]
    simp only [mobCoeff, hs, hpop]
    cases submask k q
    · simp
    · simp only [↓reduceIte]
      have hsn : signNat (1 + pop (q ^^^ k)) = -signNat (pop (q ^^^ k)) := by
        unfold signNat
        by_cases hp : pop (q ^^^ k) % 2 = 0
        · have : (1 + pop (q ^^^ k)) % 2 ≠ 0 := by omega
          simp [hp, this]
        · have : (1 + pop (q ^^^ k)) % 2 = 0 := by omega
          simp [hp, this]
      rw [hsn, Int.neg_mul]
  have hodd : sumRange (q + 1) (fun k => mobCoeff (2 * q + 1) (2 * k + 1) * g (2 * k + 1)) =
      sumRange (q + 1) (fun k => mobCoeff q k * g (2 * k + 1)) := by
    apply sumRange_congr
    intro k _
    have hs : submask (2 * k + 1) (2 * q + 1) = submask k q := by
      simpa using submask_two_mul_add k q (ba := 1) (bb := 1) (by omega) (by omega)
    have hpop : pop ((2 * q + 1) ^^^ (2 * k + 1)) = pop (q ^^^ k) := by
      have hx : (2 * q + 1) ^^^ (2 * k + 1) = 2 * (q ^^^ k) := by
        simpa using xor_two_mul_add q k (ba := 1) (bb := 1) (by omega) (by omega)
      rw [hx, pop_two_mul]
    simp [mobCoeff, hs, hpop]
  rw [heven, hodd, ← sumRange_add]
  apply sumRange_congr
  intro k _
  rw [Int.mul_sub]
  omega

theorem matMul_mob_eq_mob2 {n : Nat} (F : Nat → Nat → Int) (i j : Fin n) :
    matMul (matMul (mobMat n) (fun u v => F u.val v.val)) (transpose (mobMat n)) i j =
      mob2 F i.val j.val := by
  simp only [matMul, transpose, mobMat]
  have h1 : sumFin (fun k : Fin n =>
      sumFin (fun l : Fin n => mobCoeff i.val l.val * F l.val k.val) * mobCoeff j.val k.val) =
      sumFin (fun l : Fin n => mobCoeff i.val l.val *
        sumFin (fun k : Fin n => mobCoeff j.val k.val * F l.val k.val)) := by
    calc sumFin (fun k : Fin n =>
            sumFin (fun l : Fin n => mobCoeff i.val l.val * F l.val k.val) * mobCoeff j.val k.val)
        = sumFin (fun k : Fin n =>
            sumFin (fun l : Fin n => mobCoeff i.val l.val * F l.val k.val * mobCoeff j.val k.val)) := by
            apply sumFin_congr; intro k; rw [sumFin_mul_right]
      _ = sumFin (fun l : Fin n =>
            sumFin (fun k : Fin n => mobCoeff i.val l.val * F l.val k.val * mobCoeff j.val k.val)) :=
            sumFin_comm _
      _ = sumFin (fun l : Fin n => mobCoeff i.val l.val *
            sumFin (fun k : Fin n => mobCoeff j.val k.val * F l.val k.val)) := by
            apply sumFin_congr; intro l
            rw [← sumFin_mul_left]
            apply sumFin_congr; intro k
            rw [Int.mul_assoc, Int.mul_comm (F l.val k.val) (mobCoeff j.val k.val)]
  rw [h1]
  have hinner : ∀ l : Nat,
      sumFin (fun k : Fin n => mobCoeff j.val k.val * F l k.val) = mob1 (fun v => F l v) j.val := by
    intro l
    rw [sumFin_eq_sumRange (fun k => mobCoeff j.val k * F l k)]
    exact mob1_eq_sumRange (fun v => F l v) j.isLt
  rw [sumFin_congr (fun l => by rw [hinner l.val])]
  rw [sumFin_eq_sumRange (fun l => mobCoeff i.val l * mob1 (fun v => F l v) j.val)]
  exact mob1_eq_sumRange (fun u => mob1 (fun v => F u v) j.val) i.isLt

theorem mob1_congr {f g : Nat → Int} {i : Nat} (h : ∀ u, f u = g u) : mob1 f i = mob1 g i := by
  unfold mob1; apply sumRange_congr; intro u _; rw [h u]

theorem mob1_zero (i : Nat) : mob1 (fun _ => 0) i = 0 := by
  unfold mob1
  rw [sumRange_congr (g := fun _ => 0) (fun u _ => by simp)]
  exact sumRange_zero

theorem mob1_add (f g : Nat → Int) (i : Nat) :
    mob1 (fun u => f u + g u) i = mob1 f i + mob1 g i := by
  unfold mob1
  rw [← sumRange_add]
  apply sumRange_congr; intro u _; rw [Int.mul_add]

theorem mob1_sub (f g : Nat → Int) (i : Nat) :
    mob1 (fun u => f u - g u) i = mob1 f i - mob1 g i := by
  unfold mob1
  rw [← sumRange_sub]
  apply sumRange_congr; intro u _; rw [Int.mul_sub]

theorem mob1_mul_left (c : Int) (f : Nat → Int) (i : Nat) :
    mob1 (fun u => c * f u) i = c * mob1 f i := by
  unfold mob1
  rw [← sumRange_mul_left]
  apply sumRange_congr; intro u _; rw [Int.mul_left_comm]

theorem mob1_const (c : Int) (i : Nat) : mob1 (fun _ => c) i = if i = 0 then c else 0 := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
    by_cases hi : i = 0
    · subst hi; simp [mob1, sumRange, mobCoeff, submask, pop_zero, signNat]
    · by_cases hp : i % 2 = 0
      · have hq : i = 2 * (i / 2) := by omega
        have hq0 : i / 2 ≠ 0 := by omega
        have h2q0 : 2 * (i / 2) ≠ 0 := by omega
        rw [hq, mob1_bit_zero, ih (i / 2) (by omega)]
        simp [hq0, h2q0]
      · have hq : i = 2 * (i / 2) + 1 := by omega
        rw [hq, mob1_bit_one]
        have hz : (fun _ : Nat => c - c) = (fun _ : Nat => (0 : Int)) := by funext _; omega
        rw [hz, mob1_zero]
        simp

theorem mob2_congr {F G : Nat → Nat → Int} {i j : Nat} (h : ∀ u v, F u v = G u v) :
    mob2 F i j = mob2 G i j := by
  unfold mob2
  apply mob1_congr; intro u
  apply mob1_congr; intro v
  exact h u v

theorem mob2_zero (i j : Nat) : mob2 (fun _ _ => 0) i j = 0 := by
  unfold mob2
  rw [mob1_congr (fun _ => mob1_zero j)]
  exact mob1_zero i

theorem mob2_add (F G : Nat → Nat → Int) (i j : Nat) :
    mob2 (fun u v => F u v + G u v) i j = mob2 F i j + mob2 G i j := by
  unfold mob2
  rw [mob1_congr (fun u => mob1_add (F u) (G u) j)]
  exact mob1_add _ _ i

theorem mob2_sub (F G : Nat → Nat → Int) (i j : Nat) :
    mob2 (fun u v => F u v - G u v) i j = mob2 F i j - mob2 G i j := by
  unfold mob2
  rw [mob1_congr (fun u => mob1_sub (F u) (G u) j)]
  exact mob1_sub _ _ i

theorem mob2_mul_left (c : Int) (F : Nat → Nat → Int) (i j : Nat) :
    mob2 (fun u v => c * F u v) i j = c * mob2 F i j := by
  unfold mob2
  rw [mob1_congr (fun u => mob1_mul_left c (F u) j)]
  exact mob1_mul_left c _ i

theorem mob2_const (c : Int) (i j : Nat) :
    mob2 (fun _ _ => c) i j = if i = 0 ∧ j = 0 then c else 0 := by
  unfold mob2
  rw [mob1_congr (fun _ => mob1_const c j), mob1_const]
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi, hj]

theorem mob2_00 (F : Nat → Nat → Int) (i j : Nat) :
    mob2 F (2 * i) (2 * j) = mob2 (fun u v => F (2 * u) (2 * v)) i j := by
  unfold mob2
  rw [mob1_bit_zero]
  apply mob1_congr; intro u
  exact mob1_bit_zero (fun v => F (2 * u) v) j

theorem mob2_01 (F : Nat → Nat → Int) (i j : Nat) :
    mob2 F (2 * i) (2 * j + 1) = mob2 (fun u v => F (2 * u) (2 * v + 1) - F (2 * u) (2 * v)) i j := by
  unfold mob2
  rw [mob1_bit_zero]
  apply mob1_congr; intro u
  exact mob1_bit_one (fun v => F (2 * u) v) j

theorem mob2_10 (F : Nat → Nat → Int) (i j : Nat) :
    mob2 F (2 * i + 1) (2 * j) = mob2 (fun u v => F (2 * u + 1) (2 * v) - F (2 * u) (2 * v)) i j := by
  unfold mob2
  rw [mob1_bit_one]
  apply mob1_congr; intro u
  rw [mob1_bit_zero, mob1_bit_zero, ← mob1_sub]

theorem mob2_11 (F : Nat → Nat → Int) (i j : Nat) :
    mob2 F (2 * i + 1) (2 * j + 1) =
      mob2 (fun u v => F (2 * u + 1) (2 * v + 1) - F (2 * u + 1) (2 * v) -
        F (2 * u) (2 * v + 1) + F (2 * u) (2 * v)) i j := by
  unfold mob2
  rw [mob1_bit_one]
  apply mob1_congr; intro u
  rw [mob1_bit_one, mob1_bit_one, ← mob1_sub]
  apply mob1_congr; intro v
  dsimp only
  omega

/-! ### Exact Closed-Form Möbius Transforms for the Three Bitwise Kernels -/

/-- Kernel 1: `K(q)(u, v) = q^{pop(u &&& v)}`. Exact Möbius transform: `δ_{i,j} (q - 1)^{pop i}`. -/
theorem mob2_pop_and (q : Int) (i j : Nat) :
    mob2 (fun u v => q ^ pop (u &&& v)) i j = if i = j then (q - 1) ^ pop i else 0 := by
  induction h : i + j using Nat.strongRecOn generalizing i j with
  | ind s ih =>
    by_cases h0 : i = 0 ∧ j = 0
    · rcases h0 with ⟨rfl, rfl⟩
      simp [mob2, mob1, sumRange, mobCoeff, submask, pop_zero, signNat]
    · have hlt : i / 2 + j / 2 < s := by omega
      rcases (by omega : i % 2 = 0 ∨ i % 2 = 1) with hi | hi <;>
      rcases (by omega : j % 2 = 0 ∨ j % 2 = 1) with hj | hj
      · have hi' : i = 2 * (i / 2) := by omega
        have hj' : j = 2 * (j / 2) := by omega
        rw [hi', hj', mob2_00]
        have hF : ∀ u v, q ^ pop ((2 * u) &&& (2 * v)) = q ^ pop (u &&& v) := by
          intro u v
          have ha : (2 * u) &&& (2 * v) = 2 * (u &&& v) := by
            simpa using land_two_mul_add u v (ba := 0) (bb := 0) (by omega) (by omega)
          rw [ha, pop_two_mul]
        rw [mob2_congr hF, ih (i / 2 + j / 2) hlt (i / 2) (j / 2) rfl, pop_two_mul]
        by_cases heq : i / 2 = j / 2
        · simp [heq]
        · have h2 : 2 * (i / 2) ≠ 2 * (j / 2) := by omega
          simp [heq, h2]
      · have hi' : i = 2 * (i / 2) := by omega
        have hj' : j = 2 * (j / 2) + 1 := by omega
        rw [hi', hj', mob2_01]
        have hF : ∀ u v, q ^ pop ((2 * u) &&& (2 * v + 1)) - q ^ pop ((2 * u) &&& (2 * v)) = 0 := by
          intro u v
          have h1 : (2 * u) &&& (2 * v + 1) = 2 * (u &&& v) := by
            simpa using land_two_mul_add u v (ba := 0) (bb := 1) (by omega) (by omega)
          have h2 : (2 * u) &&& (2 * v) = 2 * (u &&& v) := by
            simpa using land_two_mul_add u v (ba := 0) (bb := 0) (by omega) (by omega)
          rw [h1, h2]; omega
        rw [mob2_congr hF, mob2_zero]
        have hne : 2 * (i / 2) ≠ 2 * (j / 2) + 1 := by omega
        simp [hne]
      · have hi' : i = 2 * (i / 2) + 1 := by omega
        have hj' : j = 2 * (j / 2) := by omega
        rw [hi', hj', mob2_10]
        have hF : ∀ u v, q ^ pop ((2 * u + 1) &&& (2 * v)) - q ^ pop ((2 * u) &&& (2 * v)) = 0 := by
          intro u v
          have h1 : (2 * u + 1) &&& (2 * v) = 2 * (u &&& v) := by
            simpa using land_two_mul_add u v (ba := 1) (bb := 0) (by omega) (by omega)
          have h2 : (2 * u) &&& (2 * v) = 2 * (u &&& v) := by
            simpa using land_two_mul_add u v (ba := 0) (bb := 0) (by omega) (by omega)
          rw [h1, h2]; omega
        rw [mob2_congr hF, mob2_zero]
        have hne : 2 * (i / 2) + 1 ≠ 2 * (j / 2) := by omega
        simp [hne]
      · have hi' : i = 2 * (i / 2) + 1 := by omega
        have hj' : j = 2 * (j / 2) + 1 := by omega
        rw [hi', hj', mob2_11]
        have hF : ∀ u v, q ^ pop ((2 * u + 1) &&& (2 * v + 1)) - q ^ pop ((2 * u + 1) &&& (2 * v)) -
            q ^ pop ((2 * u) &&& (2 * v + 1)) + q ^ pop ((2 * u) &&& (2 * v)) =
            (q - 1) * q ^ pop (u &&& v) := by
          intro u v
          have h11 : (2 * u + 1) &&& (2 * v + 1) = 2 * (u &&& v) + 1 := by
            simpa using land_two_mul_add u v (ba := 1) (bb := 1) (by omega) (by omega)
          have h10 : (2 * u + 1) &&& (2 * v) = 2 * (u &&& v) := by
            simpa using land_two_mul_add u v (ba := 1) (bb := 0) (by omega) (by omega)
          have h01 : (2 * u) &&& (2 * v + 1) = 2 * (u &&& v) := by
            simpa using land_two_mul_add u v (ba := 0) (bb := 1) (by omega) (by omega)
          have h00 : (2 * u) &&& (2 * v) = 2 * (u &&& v) := by
            simpa using land_two_mul_add u v (ba := 0) (bb := 0) (by omega) (by omega)
          rw [h11, h10, h01, h00, pop_two_mul_add_one, pop_two_mul]
          rw [Nat.add_comm 1, Int.pow_succ, Int.sub_mul, Int.one_mul, Int.mul_comm (q ^ pop (u &&& v)) q]
          omega
        rw [mob2_congr hF, mob2_mul_left, ih (i / 2 + j / 2) hlt (i / 2) (j / 2) rfl, pop_two_mul_add_one]
        by_cases heq : i / 2 = j / 2
        · simp only [heq, ↓reduceIte, Nat.add_comm 1, Int.pow_succ, Int.mul_comm]
        · have h2 : 2 * (i / 2) + 1 ≠ 2 * (j / 2) + 1 := by omega
          simp only [heq, h2, ↓reduceIte, Int.mul_zero]

theorem isMask_two_mul_add_one (m : Nat) :
    (((2 * m + 1) + 1) &&& (2 * m + 1) = 0) ↔ (((m + 1) &&& m) = 0) := by
  have heq : (2 * m + 1) + 1 = 2 * (m + 1) + 0 := by omega
  rw [heq, land_two_mul_add (m + 1) m (ba := 0) (bb := 1) (by omega) (by omega)]
  simp only [show (0 : Nat) &&& 1 = 0 by decide, Nat.add_zero]
  omega

theorem isMask_two_mul_ne_zero {m : Nat} (hm : m ≠ 0) :
    ((2 * m + 1) &&& (2 * m)) ≠ 0 := by
  have heq : (2 * m + 1) &&& (2 * m) = 2 * (m &&& m) + (1 &&& 0) :=
    land_two_mul_add m m (ba := 1) (bb := 0) (by omega) (by omega)
  rw [heq, land_self_nat]
  have hz : (1 : Nat) &&& 0 = 0 := by decide
  rw [hz]
  omega

/-- Kernel 2: `V(a)(u, v) = a^{v2Succ (u ^^^ v)}`. Exact Möbius transform: `WKernel a i j`! -/
theorem mob2_v2Succ_xor (a : Int) (i j : Nat) :
    mob2 (fun u v => a ^ v2Succ (u ^^^ v)) i j = WKernel a i j := by
  induction h : i + j using Nat.strongRecOn generalizing i j with
  | ind s ih =>
    by_cases h0 : i = 0 ∧ j = 0
    · rcases h0 with ⟨rfl, rfl⟩
      simp [mob2, mob1, sumRange, mobCoeff, submask, pop_zero, signNat, v2Succ_zero, WKernel]
    · have hlt : i / 2 + j / 2 < s := by omega
      have h00_val : ∀ u v, a ^ v2Succ ((2 * u) ^^^ (2 * v)) = 1 := by
        intro u v
        have hx : (2 * u) ^^^ (2 * v) = 2 * (u ^^^ v) := by
          simpa using xor_two_mul_add u v (ba := 0) (bb := 0) (by omega) (by omega)
        rw [hx, v2Succ_two_mul, Int.pow_zero]
      have h11_val : ∀ u v, a ^ v2Succ ((2 * u + 1) ^^^ (2 * v + 1)) = 1 := by
        intro u v
        have hx : (2 * u + 1) ^^^ (2 * v + 1) = 2 * (u ^^^ v) := by
          simpa using xor_two_mul_add u v (ba := 1) (bb := 1) (by omega) (by omega)
        rw [hx, v2Succ_two_mul, Int.pow_zero]
      have h01_val : ∀ u v, a ^ v2Succ ((2 * u) ^^^ (2 * v + 1)) = a * a ^ v2Succ (u ^^^ v) := by
        intro u v
        have hx : (2 * u) ^^^ (2 * v + 1) = 2 * (u ^^^ v) + 1 := by
          simpa using xor_two_mul_add u v (ba := 0) (bb := 1) (by omega) (by omega)
        rw [hx, v2Succ_two_mul_add_one, Nat.add_comm 1, Int.pow_succ, Int.mul_comm]
      have h10_val : ∀ u v, a ^ v2Succ ((2 * u + 1) ^^^ (2 * v)) = a * a ^ v2Succ (u ^^^ v) := by
        intro u v
        have hx : (2 * u + 1) ^^^ (2 * v) = 2 * (u ^^^ v) + 1 := by
          simpa using xor_two_mul_add u v (ba := 1) (bb := 0) (by omega) (by omega)
        rw [hx, v2Succ_two_mul_add_one, Nat.add_comm 1, Int.pow_succ, Int.mul_comm]
      rcases (by omega : i % 2 = 0 ∨ i % 2 = 1) with hi | hi <;>
      rcases (by omega : j % 2 = 0 ∨ j % 2 = 1) with hj | hj
      · -- (0, 0) with (i, j) ≠ (0, 0)
        have hi' : i = 2 * (i / 2) := by omega
        have hj' : j = 2 * (j / 2) := by omega
        have hne0 : ¬ (i / 2 = 0 ∧ j / 2 = 0) := by omega
        rw [hi', hj', mob2_00, mob2_congr h00_val, mob2_const]
        simp only [hne0, ↓reduceIte]
        have hor : (2 * (i / 2)) ||| (2 * (j / 2)) = 2 * ((i / 2) ||| (j / 2)) := by
          simpa using lor_two_mul_add (i / 2) (j / 2) (ba := 0) (bb := 0) (by omega) (by omega)
        have hmne : ((i / 2) ||| (j / 2)) ≠ 0 := fun hz => hne0 ((lor_eq_zero_iff _ _).mp hz)
        unfold WKernel
        simp only [show ¬ (2 * (i / 2) = 0 ∧ 2 * (j / 2) = 0) by omega, ↓reduceIte, hor]
        simp [isMask_two_mul_ne_zero hmne]
      · -- (0, 1)
        have hi' : i = 2 * (i / 2) := by omega
        have hj' : j = 2 * (j / 2) + 1 := by omega
        rw [hi', hj', mob2_01]
        have hF : ∀ u v, a ^ v2Succ ((2 * u) ^^^ (2 * v + 1)) - a ^ v2Succ ((2 * u) ^^^ (2 * v)) =
            a * a ^ v2Succ (u ^^^ v) - 1 := fun u v => by rw [h01_val, h00_val]
        rw [mob2_congr hF, mob2_sub, mob2_mul_left, mob2_const, ih (i / 2 + j / 2) hlt (i / 2) (j / 2) rfl]
        have hor : (2 * (i / 2)) ||| (2 * (j / 2) + 1) = 2 * ((i / 2) ||| (j / 2)) + 1 := by
          simpa using lor_two_mul_add (i / 2) (j / 2) (ba := 0) (bb := 1) (by omega) (by omega)
        have hand : (2 * (i / 2)) &&& (2 * (j / 2) + 1) = 2 * ((i / 2) &&& (j / 2)) := by
          simpa using land_two_mul_add (i / 2) (j / 2) (ba := 0) (bb := 1) (by omega) (by omega)
        unfold WKernel
        simp only [show ¬ (2 * (i / 2) = 0 ∧ 2 * (j / 2) + 1 = 0) by omega, ↓reduceIte, hor, hand,
          isMask_two_mul_add_one, pop_two_mul_add_one, pop_two_mul]
        by_cases hq0 : i / 2 = 0 ∧ j / 2 = 0
        · rcases hq0 with ⟨h1, h2⟩; simp [h1, h2, pop_zero]
        · simp only [hq0, ↓reduceIte, Int.sub_zero]
          by_cases hmask : (((i / 2) ||| (j / 2)) + 1) &&& ((i / 2) ||| (j / 2)) = 0
          · simp only [hmask, ↓reduceIte]
            have hmpos : 1 ≤ pop ((i / 2) ||| (j / 2)) :=
              pop_pos_of_ne_zero (fun hz => hq0 ((lor_eq_zero_iff _ _).mp hz))
            have hexp : 1 + pop ((i / 2) ||| (j / 2)) - 1 = (pop ((i / 2) ||| (j / 2)) - 1) + 1 := by omega
            rw [hexp, Int.pow_succ]
            ac_rfl
          · simp [hmask]
      · -- (1, 0)
        have hi' : i = 2 * (i / 2) + 1 := by omega
        have hj' : j = 2 * (j / 2) := by omega
        rw [hi', hj', mob2_10]
        have hF : ∀ u v, a ^ v2Succ ((2 * u + 1) ^^^ (2 * v)) - a ^ v2Succ ((2 * u) ^^^ (2 * v)) =
            a * a ^ v2Succ (u ^^^ v) - 1 := fun u v => by rw [h10_val, h00_val]
        rw [mob2_congr hF, mob2_sub, mob2_mul_left, mob2_const, ih (i / 2 + j / 2) hlt (i / 2) (j / 2) rfl]
        have hor : (2 * (i / 2) + 1) ||| (2 * (j / 2)) = 2 * ((i / 2) ||| (j / 2)) + 1 := by
          simpa using lor_two_mul_add (i / 2) (j / 2) (ba := 1) (bb := 0) (by omega) (by omega)
        have hand : (2 * (i / 2) + 1) &&& (2 * (j / 2)) = 2 * ((i / 2) &&& (j / 2)) := by
          simpa using land_two_mul_add (i / 2) (j / 2) (ba := 1) (bb := 0) (by omega) (by omega)
        unfold WKernel
        simp only [show ¬ (2 * (i / 2) + 1 = 0 ∧ 2 * (j / 2) = 0) by omega, ↓reduceIte, hor, hand,
          isMask_two_mul_add_one, pop_two_mul_add_one, pop_two_mul]
        by_cases hq0 : i / 2 = 0 ∧ j / 2 = 0
        · rcases hq0 with ⟨h1, h2⟩; simp [h1, h2, pop_zero]
        · simp only [hq0, ↓reduceIte, Int.sub_zero]
          by_cases hmask : (((i / 2) ||| (j / 2)) + 1) &&& ((i / 2) ||| (j / 2)) = 0
          · simp only [hmask, ↓reduceIte]
            have hmpos : 1 ≤ pop ((i / 2) ||| (j / 2)) :=
              pop_pos_of_ne_zero (fun hz => hq0 ((lor_eq_zero_iff _ _).mp hz))
            have hexp : 1 + pop ((i / 2) ||| (j / 2)) - 1 = (pop ((i / 2) ||| (j / 2)) - 1) + 1 := by omega
            rw [hexp, Int.pow_succ]
            ac_rfl
          · simp [hmask]
      · -- (1, 1)
        have hi' : i = 2 * (i / 2) + 1 := by omega
        have hj' : j = 2 * (j / 2) + 1 := by omega
        rw [hi', hj', mob2_11]
        have hF : ∀ u v, a ^ v2Succ ((2 * u + 1) ^^^ (2 * v + 1)) - a ^ v2Succ ((2 * u + 1) ^^^ (2 * v)) -
            a ^ v2Succ ((2 * u) ^^^ (2 * v + 1)) + a ^ v2Succ ((2 * u) ^^^ (2 * v)) =
            (-2 * a) * a ^ v2Succ (u ^^^ v) + 2 := by
          intro u v
          rw [h11_val, h10_val, h01_val, h00_val]
          rw [Int.mul_assoc]
          omega
        rw [mob2_congr hF, mob2_add, mob2_mul_left, mob2_const, ih (i / 2 + j / 2) hlt (i / 2) (j / 2) rfl]
        have hor : (2 * (i / 2) + 1) ||| (2 * (j / 2) + 1) = 2 * ((i / 2) ||| (j / 2)) + 1 := by
          simpa using lor_two_mul_add (i / 2) (j / 2) (ba := 1) (bb := 1) (by omega) (by omega)
        have hand : (2 * (i / 2) + 1) &&& (2 * (j / 2) + 1) = 2 * ((i / 2) &&& (j / 2)) + 1 := by
          simpa using land_two_mul_add (i / 2) (j / 2) (ba := 1) (bb := 1) (by omega) (by omega)
        unfold WKernel
        simp only [show ¬ (2 * (i / 2) + 1 = 0 ∧ 2 * (j / 2) + 1 = 0) by omega, ↓reduceIte, hor, hand,
          isMask_two_mul_add_one, pop_two_mul_add_one]
        by_cases hq0 : i / 2 = 0 ∧ j / 2 = 0
        · rcases hq0 with ⟨h1, h2⟩
          simp [h1, h2, pop_zero]
          omega
        · simp only [hq0, ↓reduceIte, Int.add_zero]
          by_cases hmask : (((i / 2) ||| (j / 2)) + 1) &&& ((i / 2) ||| (j / 2)) = 0
          · simp only [hmask, ↓reduceIte]
            have hmpos : 1 ≤ pop ((i / 2) ||| (j / 2)) :=
              pop_pos_of_ne_zero (fun hz => hq0 ((lor_eq_zero_iff _ _).mp hz))
            have hexp : 1 + pop ((i / 2) ||| (j / 2)) - 1 = (pop ((i / 2) ||| (j / 2)) - 1) + 1 := by omega
            rw [hexp, Int.pow_succ, Nat.add_comm 1 (pop _), Int.pow_succ]
            ac_rfl
          · simp [hmask]

/-- Kernel 3 (Asymmetric Dense Bitwise Perturbation):
    `Q(c, d)(u, v) = c^{pop(bitDiff v u)} * d^{pop(u &&& v)}`.
    Exact Möbius transform: upper-triangular `[i ⊆ j] * (c - 1)^{pop(j ^^^ i)} * (d - c)^{pop i}`! -/
theorem mob2_asym_pert (c d : Int) (i j : Nat) :
    mob2 (fun u v => c ^ pop (bitDiff v u) * d ^ pop (u &&& v)) i j =
      if submask i j then (c - 1) ^ pop (j ^^^ i) * (d - c) ^ pop i else 0 := by
  induction h : i + j using Nat.strongRecOn generalizing i j with
  | ind s ih =>
    by_cases h0 : i = 0 ∧ j = 0
    · rcases h0 with ⟨rfl, rfl⟩
      simp [mob2, mob1, sumRange, mobCoeff, submask, bitDiff, pop_zero, signNat]
    · have hlt : i / 2 + j / 2 < s := by omega
      have hbd00 : ∀ u v, bitDiff (2 * v) (2 * u) = 2 * bitDiff v u := by
        intro u v; unfold bitDiff
        have l0 := land_two_mul_add u v (ba := 0) (bb := 0) (by omega) (by omega)
        have x0 := xor_two_mul_add v (u &&& v) (ba := 0) (bb := 0) (by omega) (by omega)
        simp only [Nat.add_zero, show (0 : Nat) &&& 0 = 0 by decide, show (0 : Nat) ^^^ 0 = 0 by decide] at l0 x0
        rw [l0, x0]
      have hbd01 : ∀ u v, bitDiff (2 * v + 1) (2 * u) = 2 * bitDiff v u + 1 := by
        intro u v; unfold bitDiff
        have l0 := land_two_mul_add u v (ba := 0) (bb := 1) (by omega) (by omega)
        have x0 := xor_two_mul_add v (u &&& v) (ba := 1) (bb := 0) (by omega) (by omega)
        simp only [Nat.add_zero, show (0 : Nat) &&& 1 = 0 by decide, show (1 : Nat) ^^^ 0 = 1 by decide] at l0 x0
        rw [l0, x0]
      have hbd10 : ∀ u v, bitDiff (2 * v) (2 * u + 1) = 2 * bitDiff v u := by
        intro u v; unfold bitDiff
        have l0 := land_two_mul_add u v (ba := 1) (bb := 0) (by omega) (by omega)
        have x0 := xor_two_mul_add v (u &&& v) (ba := 0) (bb := 0) (by omega) (by omega)
        simp only [Nat.add_zero, show (1 : Nat) &&& 0 = 0 by decide, show (0 : Nat) ^^^ 0 = 0 by decide] at l0 x0
        rw [l0, x0]
      have hbd11 : ∀ u v, bitDiff (2 * v + 1) (2 * u + 1) = 2 * bitDiff v u := by
        intro u v; unfold bitDiff
        have l0 := land_two_mul_add u v (ba := 1) (bb := 1) (by omega) (by omega)
        have x0 := xor_two_mul_add v (u &&& v) (ba := 1) (bb := 1) (by omega) (by omega)
        simp only [Nat.add_zero, show (1 : Nat) &&& 1 = 1 by decide, show (1 : Nat) ^^^ 1 = 0 by decide] at l0 x0
        rw [l0, x0]
      rcases (by omega : i % 2 = 0 ∨ i % 2 = 1) with hi | hi <;>
      rcases (by omega : j % 2 = 0 ∨ j % 2 = 1) with hj | hj
      · -- (0, 0)
        have hi' : i = 2 * (i / 2) := by omega
        have hj' : j = 2 * (j / 2) := by omega
        rw [hi', hj', mob2_00]
        have hF : ∀ u v, c ^ pop (bitDiff (2 * v) (2 * u)) * d ^ pop ((2 * u) &&& (2 * v)) =
            c ^ pop (bitDiff v u) * d ^ pop (u &&& v) := by
          intro u v
          have l0 : (2 * u) &&& (2 * v) = 2 * (u &&& v) := by
            simpa using land_two_mul_add u v (ba := 0) (bb := 0) (by omega) (by omega)
          rw [hbd00, l0, pop_two_mul, pop_two_mul]
        rw [mob2_congr hF, ih (i / 2 + j / 2) hlt (i / 2) (j / 2) rfl]
        have hs : submask (2 * (i / 2)) (2 * (j / 2)) = submask (i / 2) (j / 2) := by
          simpa using submask_two_mul_add (i / 2) (j / 2) (ba := 0) (bb := 0) (by omega) (by omega)
        have hx : (2 * (j / 2)) ^^^ (2 * (i / 2)) = 2 * ((j / 2) ^^^ (i / 2)) := by
          simpa using xor_two_mul_add (j / 2) (i / 2) (ba := 0) (bb := 0) (by omega) (by omega)
        rw [hs, hx, pop_two_mul, pop_two_mul]
      · -- (0, 1)
        have hi' : i = 2 * (i / 2) := by omega
        have hj' : j = 2 * (j / 2) + 1 := by omega
        rw [hi', hj', mob2_01]
        have hF : ∀ u v, c ^ pop (bitDiff (2 * v + 1) (2 * u)) * d ^ pop ((2 * u) &&& (2 * v + 1)) -
            c ^ pop (bitDiff (2 * v) (2 * u)) * d ^ pop ((2 * u) &&& (2 * v)) =
            (c - 1) * (c ^ pop (bitDiff v u) * d ^ pop (u &&& v)) := by
          intro u v
          have l1 : (2 * u) &&& (2 * v + 1) = 2 * (u &&& v) := by
            simpa using land_two_mul_add u v (ba := 0) (bb := 1) (by omega) (by omega)
          have l2 : (2 * u) &&& (2 * v) = 2 * (u &&& v) := by
            simpa using land_two_mul_add u v (ba := 0) (bb := 0) (by omega) (by omega)
          rw [hbd01, hbd00, l1, l2, pop_two_mul_add_one, pop_two_mul, pop_two_mul]
          rw [Nat.add_comm 1, Int.pow_succ, Int.mul_comm (c ^ _), Int.sub_mul, Int.one_mul, Int.mul_assoc]
        rw [mob2_congr hF, mob2_mul_left, ih (i / 2 + j / 2) hlt (i / 2) (j / 2) rfl]
        have hs : submask (2 * (i / 2)) (2 * (j / 2) + 1) = submask (i / 2) (j / 2) := by
          simpa using submask_two_mul_add (i / 2) (j / 2) (ba := 0) (bb := 1) (by omega) (by omega)
        have hx : (2 * (j / 2) + 1) ^^^ (2 * (i / 2)) = 2 * ((j / 2) ^^^ (i / 2)) + 1 := by
          simpa using xor_two_mul_add (j / 2) (i / 2) (ba := 1) (bb := 0) (by omega) (by omega)
        rw [hs, hx, pop_two_mul_add_one, pop_two_mul]
        cases submask (i / 2) (j / 2)
        · simp
        · simp only [↓reduceIte, Nat.add_comm 1, Int.pow_succ]
          rw [Int.mul_comm ((c - 1) ^ _) (c - 1), Int.mul_assoc]
      · -- (1, 0)
        have hi' : i = 2 * (i / 2) + 1 := by omega
        have hj' : j = 2 * (j / 2) := by omega
        rw [hi', hj', mob2_10]
        have hF : ∀ u v, c ^ pop (bitDiff (2 * v) (2 * u + 1)) * d ^ pop ((2 * u + 1) &&& (2 * v)) -
            c ^ pop (bitDiff (2 * v) (2 * u)) * d ^ pop ((2 * u) &&& (2 * v)) = 0 := by
          intro u v
          have l1 : (2 * u + 1) &&& (2 * v) = 2 * (u &&& v) := by
            simpa using land_two_mul_add u v (ba := 1) (bb := 0) (by omega) (by omega)
          have l2 : (2 * u) &&& (2 * v) = 2 * (u &&& v) := by
            simpa using land_two_mul_add u v (ba := 0) (bb := 0) (by omega) (by omega)
          rw [hbd10, hbd00, l1, l2]; omega
        rw [mob2_congr hF, mob2_zero]
        have hs : submask (2 * (i / 2) + 1) (2 * (j / 2)) = false := by
          simpa using submask_two_mul_add (i / 2) (j / 2) (ba := 1) (bb := 0) (by omega) (by omega)
        simp [hs]
      · -- (1, 1)
        have hi' : i = 2 * (i / 2) + 1 := by omega
        have hj' : j = 2 * (j / 2) + 1 := by omega
        rw [hi', hj', mob2_11]
        have hF : ∀ u v,
            c ^ pop (bitDiff (2 * v + 1) (2 * u + 1)) * d ^ pop ((2 * u + 1) &&& (2 * v + 1)) -
            c ^ pop (bitDiff (2 * v) (2 * u + 1)) * d ^ pop ((2 * u + 1) &&& (2 * v)) -
            c ^ pop (bitDiff (2 * v + 1) (2 * u)) * d ^ pop ((2 * u) &&& (2 * v + 1)) +
            c ^ pop (bitDiff (2 * v) (2 * u)) * d ^ pop ((2 * u) &&& (2 * v)) =
            (d - c) * (c ^ pop (bitDiff v u) * d ^ pop (u &&& v)) := by
          intro u v
          have l11 : (2 * u + 1) &&& (2 * v + 1) = 2 * (u &&& v) + 1 := by
            simpa using land_two_mul_add u v (ba := 1) (bb := 1) (by omega) (by omega)
          have l10 : (2 * u + 1) &&& (2 * v) = 2 * (u &&& v) := by
            simpa using land_two_mul_add u v (ba := 1) (bb := 0) (by omega) (by omega)
          have l01 : (2 * u) &&& (2 * v + 1) = 2 * (u &&& v) := by
            simpa using land_two_mul_add u v (ba := 0) (bb := 1) (by omega) (by omega)
          have l00 : (2 * u) &&& (2 * v) = 2 * (u &&& v) := by
            simpa using land_two_mul_add u v (ba := 0) (bb := 0) (by omega) (by omega)
          rw [hbd11, hbd10, hbd01, hbd00, l11, l10, l01, l00]
          rw [pop_two_mul, pop_two_mul_add_one, pop_two_mul_add_one, pop_two_mul]
          rw [Nat.add_comm 1 (pop (bitDiff v u)), Nat.add_comm 1 (pop (u &&& v)),
            Int.pow_succ, Int.pow_succ]
          have hd : c ^ pop (bitDiff v u) * (d ^ pop (u &&& v) * d) =
              d * (c ^ pop (bitDiff v u) * d ^ pop (u &&& v)) := by
            rw [Int.mul_comm (d ^ pop (u &&& v)) d, Int.mul_left_comm]
          have hc : c ^ pop (bitDiff v u) * c * d ^ pop (u &&& v) =
              c * (c ^ pop (bitDiff v u) * d ^ pop (u &&& v)) := by
            rw [Int.mul_comm (c ^ pop (bitDiff v u)) c, Int.mul_assoc]
          rw [hd, hc, Int.sub_mul]
          omega
        rw [mob2_congr hF, mob2_mul_left, ih (i / 2 + j / 2) hlt (i / 2) (j / 2) rfl]
        have hs : submask (2 * (i / 2) + 1) (2 * (j / 2) + 1) = submask (i / 2) (j / 2) := by
          simpa using submask_two_mul_add (i / 2) (j / 2) (ba := 1) (bb := 1) (by omega) (by omega)
        have hx : (2 * (j / 2) + 1) ^^^ (2 * (i / 2) + 1) = 2 * ((j / 2) ^^^ (i / 2)) := by
          simpa using xor_two_mul_add (j / 2) (i / 2) (ba := 1) (bb := 1) (by omega) (by omega)
        rw [hs, hx, pop_two_mul, pop_two_mul_add_one]
        cases submask (i / 2) (j / 2)
        · simp
        · simp only [↓reduceIte, Nat.add_comm 1, Int.pow_succ]
          rw [Int.mul_left_comm (d - c), Int.mul_comm (d - c) ((d - c) ^ _)]

theorem sum_rowExp_colExp (e n : Nat) (hn : 2 ≤ n) :
    sumNat (fun i : Fin n => rowExp e i.val + colExp e i.val) = e * popSum n - e := by
  have h1 : ∀ m : Nat,
      sumNat (fun i : Fin (m + 2) => rowExp e i.val + colExp e i.val) + e =
        e * popSum (m + 2) := by
    intro m
    induction m with
    | zero =>
      simp only [popSum, sumNat, Fin.val_castSucc, Fin.val_last, rowExp, colExp]
      have p0 : pop 0 = 0 := pop_zero
      have p1 : pop 1 = 1 := by decide
      simp [p0, p1]
    | succ m ih =>
      have hlast : rowExp e (m + 2) + colExp e (m + 2) = e * pop (m + 2) := by
        have hge : ¬ (m + 2 ≤ 1) := by omega
        simp only [rowExp, colExp, hge, ↓reduceIte]
        omega
      change sumNat (fun i : Fin (m + 2) => rowExp e i.val + colExp e i.val) +
          (rowExp e (m + 2) + colExp e (m + 2)) + e =
          e * (popSum (m + 2) + pop (m + 2))
      rw [hlast, Nat.mul_add]
      omega
  have h2 := h1 (n - 2)
  have hne : n - 2 + 2 = n := by omega
  rw [hne] at h2
  omega

theorem mask_eq_pow_two_sub_one {m : Nat} (h : ((m + 1) &&& m) = 0) :
    m + 1 = 2 ^ pop m := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    cases m with
    | zero => simp [pop_zero]
    | succ m =>
      by_cases hp : (m + 1) % 2 = 0
      · have hq : m + 1 = 2 * ((m + 1) / 2) := by omega
        have hqne : (m + 1) / 2 ≠ 0 := by omega
        rw [hq] at h
        exact absurd h (isMask_two_mul_ne_zero hqne)
      · have hq : m + 1 = 2 * ((m + 1) / 2) + 1 := by omega
        rw [hq] at h ⊢
        rw [isMask_two_mul_add_one] at h
        have hlt : (m + 1) / 2 < m + 1 := by omega
        have hsub := ih ((m + 1) / 2) hlt h
        rw [pop_two_mul_add_one, Nat.add_comm 1, Nat.pow_succ]
        omega

theorem le_lor_left (i j : Nat) : i ≤ i ||| j := by
  have hs : submask i (i ||| j) = true := by
    simp only [submask, beq_iff_eq]
    apply Nat.eq_of_testBit_eq; intro k
    simp only [Nat.testBit_and, Nat.testBit_or]
    cases i.testBit k <;> cases j.testBit k <;> rfl
  exact submask_le hs

theorem le_lor_right (i j : Nat) : j ≤ i ||| j := by
  have hs : submask j (i ||| j) = true := by
    simp only [submask, beq_iff_eq]
    apply Nat.eq_of_testBit_eq; intro k
    simp only [Nat.testBit_and, Nat.testBit_or]
    cases i.testBit k <;> cases j.testBit k <;> rfl
  exact submask_le hs

theorem pop_lor_ge_of_mask {i j c : Nat} (hmask : (((i ||| j) + 1) &&& (i ||| j)) = 0)
    (hge : 2 ^ c ≤ i ∨ 2 ^ c ≤ j) : c + 1 ≤ pop (i ||| j) := by
  have hm := mask_eq_pow_two_sub_one hmask
  have h1 : i ≤ i ||| j := le_lor_left i j
  have h2 : j ≤ i ||| j := le_lor_right i j
  have hpow : 2 ^ c < 2 ^ pop (i ||| j) := by omega
  rcases Nat.lt_or_ge (pop (i ||| j)) (c + 1) with hlt | hok
  · have hle : pop (i ||| j) ≤ c := by omega
    have hmono : 2 ^ pop (i ||| j) ≤ 2 ^ c := Nat.pow_le_pow_right (by omega) hle
    omega
  · exact hok

theorem odd_pow_mod2 (u : Int) (hu : u % 2 = 1) (k : Nat) : (u ^ k) % 2 = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Int.pow_succ, Int.mul_emod, ih, hu]
    rfl

theorem neg_one_pow_mod2 (k : Nat) : ((-1 : Int) ^ k) % 2 = 1 :=
  odd_pow_mod2 (-1) (by decide) k

theorem two_pow_mul_mod2 (d : Nat) (x : Int) (hx : x % 2 = 1) :
    ((2 : Int) ^ d * x) % 2 = if d = 0 then 1 else 0 := by
  cases d with
  | zero => simpa using hx
  | succ d =>
    simp only [Nat.succ_ne_zero, ↓reduceIte, Int.pow_succ]
    have h2 : (2 : Int) ^ d * 2 * x = 2 * ((2 : Int) ^ d * x) := by ac_rfl
    rw [h2]
    omega

theorem int_pow_mul_distrib (x y : Int) (k : Nat) : (x * y) ^ k = x ^ k * y ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Int.pow_succ, Int.pow_succ, Int.pow_succ, ih]
    ac_rfl

theorem int_pow_pow (x : Int) (a b : Nat) : (x ^ a) ^ b = x ^ (a * b) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Int.pow_succ, ih, Nat.mul_succ, Int.pow_add]

/-! ### Exact Bi-Scaled Quotient Construction for `hybridMat` and `asymPertMat` -/

/-- Core divisibility factorization: whenever `rowExp e i + colExp e j ≤ vW` on every mask pair `(i, j)`,
    `mobMat * hybridMat * mobMat^T = biScale (rowExp e) (colExp e) (omegaEntry e r u_a u_q)`! -/
theorem hybridMat_biscaled_fac (e r n : Nat) (u_a u_q : Int)
    (hdom : ∀ i j : Nat, ¬ (i = 0 ∧ j = 0) → (((i ||| j) + 1) &&& (i ||| j)) = 0 →
      rowExp e i + colExp e j ≤ r * (pop (i ||| j) - 1) + pop (i &&& j)) :
    matMul (matMul (mobMat n) (hybridMat ((2 : Int) ^ r * u_a) (1 + (2 : Int) ^ e * u_q) n))
      (transpose (mobMat n)) =
    biScale (fun i => rowExp e i.val) (fun j => colExp e j.val)
      (fun i j => omegaEntry e r u_a u_q i.val j.val) := by
  funext i j
  have hmob := matMul_mob_eq_mob2
    (fun u v => ((2 : Int) ^ r * u_a) ^ v2Succ (u ^^^ v) + (1 + (2 : Int) ^ e * u_q) ^ pop (u &&& v)) i j
  change matMul (matMul (mobMat n) (fun u v => ((2 : Int) ^ r * u_a) ^ v2Succ (u ^^^ v) +
      (1 + (2 : Int) ^ e * u_q) ^ pop (u &&& v))) (transpose (mobMat n)) i j = _
  rw [hmob, mob2_add, mob2_v2Succ_xor, mob2_pop_and]
  simp only [biScale, omegaEntry, Int.mul_add]
  congr 1
  · -- WKernel term
    unfold WKernel
    by_cases h0 : i.val = 0 ∧ j.val = 0
    · rcases h0 with ⟨hi0, hj0⟩
      simp [hi0, hj0, rowExp, colExp]
    · simp only [h0, ↓reduceIte]
      by_cases hmask : (((i.val ||| j.val) + 1) &&& (i.val ||| j.val)) = 0
      · simp only [hmask, ↓reduceIte]
        have hle := hdom i.val j.val h0 hmask
        have hsplit : (2 : Int) ^ (rowExp e i.val + colExp e j.val) *
            (2 : Int) ^ (r * (pop (i.val ||| j.val) - 1) + pop (i.val &&& j.val) -
              (rowExp e i.val + colExp e j.val)) =
            (2 : Int) ^ (r * (pop (i.val ||| j.val) - 1) + pop (i.val &&& j.val)) := by
          rw [← Int.pow_add]
          congr 1
          omega
        rw [← Int.mul_assoc, hsplit, Int.pow_add]
        rw [int_pow_mul_distrib ((2 : Int) ^ r) u_a, int_pow_pow]
        have hneg2 : (-2 : Int) ^ pop (i.val &&& j.val) =
            (2 : Int) ^ pop (i.val &&& j.val) * (-1 : Int) ^ pop (i.val &&& j.val) := by
          have : (-2 : Int) = 2 * (-1) := by decide
          rw [this, int_pow_mul_distrib]
        rw [hneg2]
        ac_rfl
      · simp [hmask]
  · -- Diagonal term
    by_cases hij : i.val = j.val
    · simp only [hij, ↓reduceIte]
      have hsub1 : (1 + (2 : Int) ^ e * u_q) - 1 = (2 : Int) ^ e * u_q := by omega
      rw [hsub1, int_pow_mul_distrib, int_pow_pow]
      by_cases hj0 : j.val = 0
      · simp [hj0, pop_zero, rowExp, colExp]
      · by_cases hj1 : j.val = 1
        · have p1 : pop 1 = 1 := by decide
          simp [hj1, p1, rowExp, colExp, Int.pow_one]
        · have hge2 : ¬ (j.val ≤ 1) := by omega
          simp only [hj0, hj1, ↓reduceIte, rowExp, colExp, hge2]
          have hhalf : (e * pop j.val) / 2 + (e * pop j.val + 1) / 2 = e * pop j.val := by omega
          rw [hhalf]
    · simp [hij]

/-- Exact perturbation divisibility for `asymPertMat lam (1 + 2^e * tc) (1 + 2^e * td)`! -/
theorem asymPertMat_div_fac (e n : Nat) (lam tc td : Int) :
    ∃ E : Mat n,
      matMul (matMul (mobMat n) (asymPertMat lam (1 + (2 : Int) ^ e * tc) (1 + (2 : Int) ^ e * td) n))
        (transpose (mobMat n)) =
      fun i j => (2 : Int) ^ (rowExp e i.val + colExp e j.val + 1) * E i j := by
  let E : Mat n := fun i j =>
    if submask i.val j.val then
      (2 : Int) ^ (e * pop j.val - (rowExp e i.val + colExp e j.val)) *
        (lam * tc ^ pop (j.val ^^^ i.val) * (td - tc) ^ pop i.val)
    else 0
  refine ⟨E, ?_⟩
  funext i j
  have hmob := matMul_mob_eq_mob2
    (fun u v => (2 * lam) * ((1 + (2 : Int) ^ e * tc) ^ pop (bitDiff v u) *
      (1 + (2 : Int) ^ e * td) ^ pop (u &&& v))) i j
  change matMul (matMul (mobMat n) (fun u v => (2 * lam) *
      ((1 + (2 : Int) ^ e * tc) ^ pop (bitDiff v u) * (1 + (2 : Int) ^ e * td) ^ pop (u &&& v))))
      (transpose (mobMat n)) i j = _
  rw [hmob, mob2_mul_left, mob2_asym_pert]
  dsimp only [E]
  by_cases hs : submask i.val j.val = true
  · simp only [hs, ↓reduceIte]
    have hpop_le : pop i.val ≤ pop j.val := by
      have := pop_submask_add hs; omega
    have hexp_le : rowExp e i.val + colExp e j.val ≤ e * pop j.val := by
      unfold rowExp colExp
      have hmul_le : e * pop i.val ≤ e * pop j.val := Nat.mul_le_mul_left e hpop_le
      split <;> split <;> omega
    have hsub1 : (1 + (2 : Int) ^ e * tc) - 1 = (2 : Int) ^ e * tc := by omega
    have hsub2 : (1 + (2 : Int) ^ e * td) - (1 + (2 : Int) ^ e * tc) = (2 : Int) ^ e * (td - tc) := by
      rw [Int.mul_sub]; omega
    rw [hsub1, hsub2, int_pow_mul_distrib, int_pow_mul_distrib, int_pow_pow, int_pow_pow]
    have hpow_sum : (2 : Int) ^ (e * pop (j.val ^^^ i.val)) * (2 : Int) ^ (e * pop i.val) =
        (2 : Int) ^ (e * pop j.val) := by
      rw [← Int.pow_add, ← Nat.mul_add, pop_submask_add hs]
    have hsplit : (2 : Int) ^ (rowExp e i.val + colExp e j.val + 1) *
        (2 : Int) ^ (e * pop j.val - (rowExp e i.val + colExp e j.val)) =
        2 * (2 : Int) ^ (e * pop j.val) := by
      rw [← Int.pow_add, show rowExp e i.val + colExp e j.val + 1 +
        (e * pop j.val - (rowExp e i.val + colExp e j.val)) = e * pop j.val + 1 by omega,
        Int.pow_succ, Int.mul_comm]
    calc (2 * lam) * ((2 : Int) ^ (e * pop (j.val ^^^ i.val)) * tc ^ pop (j.val ^^^ i.val) *
            ((2 : Int) ^ (e * pop i.val) * (td - tc) ^ pop i.val))
        = 2 * ((2 : Int) ^ (e * pop (j.val ^^^ i.val)) * (2 : Int) ^ (e * pop i.val)) *
            (lam * tc ^ pop (j.val ^^^ i.val) * (td - tc) ^ pop i.val) := by ac_rfl
      _ = (2 * (2 : Int) ^ (e * pop j.val)) *
            (lam * tc ^ pop (j.val ^^^ i.val) * (td - tc) ^ pop i.val) := by rw [hpow_sum]
      _ = ((2 : Int) ^ (rowExp e i.val + colExp e j.val + 1) *
            (2 : Int) ^ (e * pop j.val - (rowExp e i.val + colExp e j.val))) *
            (lam * tc ^ pop (j.val ^^^ i.val) * (td - tc) ^ pop i.val) := by rw [hsplit]
      _ = (2 : Int) ^ (rowExp e i.val + colExp e j.val + 1) *
            ((2 : Int) ^ (e * pop j.val - (rowExp e i.val + colExp e j.val)) *
              (lam * tc ^ pop (j.val ^^^ i.val) * (td - tc) ^ pop i.val)) := by rw [Int.mul_assoc]
  · simp [hs]

/-- Exact mod-2 characterization of `omegaEntry e r u_a u_q i j` when `e ≥ 1, r ≥ 1, u_a, u_q` odd! -/
theorem omegaEntry_mod2 (e r : Nat) (he : 1 ≤ e) (hr : 1 ≤ r) (u_a u_q : Int)
    (hua : u_a % 2 = 1) (huq : u_q % 2 = 1) (i j : Nat) :
    omegaEntry e r u_a u_q i j % 2 =
      ((if i = 0 ∧ j = 0 then 1
        else if (((i ||| j) + 1) &&& (i ||| j)) = 0 then
          if r * (pop (i ||| j) - 1) + pop (i &&& j) - (rowExp e i + colExp e j) = 0 then 1 else 0
        else 0) +
       (if i = j then if i = 0 then 1 else if i = 1 then 0 else 1 else 0)) % 2 := by
  unfold omegaEntry
  have ha_even : ((2 : Int) ^ r * u_a) % 2 = 0 := by
    have := two_pow_mul_mod2 r u_a hua
    have hne : r ≠ 0 := by omega
    simpa [hne] using this
  have ham1_odd : ((2 : Int) ^ r * u_a - 1) % 2 = 1 := by omega
  have how_odd : (((2 : Int) ^ r * u_a - 1) * u_a ^ (pop (i ||| j) - 1) * (-1 : Int) ^ pop (i &&& j)) % 2 = 1 := by
    rw [Int.mul_emod, Int.mul_emod ((2 : Int) ^ r * u_a - 1), ham1_odd,
      odd_pow_mod2 u_a hua, neg_one_pow_mod2]
    rfl
  have h2e_even : ((2 : Int) ^ e * u_q) % 2 = 0 := by
    have := two_pow_mul_mod2 e u_q huq
    have hne : e ≠ 0 := by omega
    simpa [hne] using this
  have huq_pow : (u_q ^ pop i) % 2 = 1 := odd_pow_mod2 u_q huq (pop i)
  rw [Int.add_emod]
  congr 1
  congr 1
  · by_cases h0 : i = 0 ∧ j = 0
    · simp [h0]
    · simp only [h0, ↓reduceIte]
      by_cases hmask : (((i ||| j) + 1) &&& (i ||| j)) = 0
      · simp only [hmask, ↓reduceIte]
        rw [two_pow_mul_mod2 _ _ how_odd]
      · simp [hmask]
  · by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte]
      by_cases hj0 : i = 0
      · simp [hj0]
      · by_cases hj1 : i = 1
        · simp [hj1, h2e_even]
        · simp [hj0, hj1, huq_pow]
    · simp [hij]

/-! ### Helper: Unified `fullHybridMat` Lifting Lemma from Bounds + Finite Corner Certificate -/

theorem fullHybridMat_lift {e r C n : Nat} (he : 1 ≤ e) (hr : 1 ≤ r) (hn : 2 ≤ n)
    (u_a u_q lam tc td : Int) (hua : u_a % 2 = 1) (huq : u_q % 2 = 1)
    (hdom : ∀ i j : Nat, ¬ (i = 0 ∧ j = 0) → (((i ||| j) + 1) &&& (i ||| j)) = 0 →
      rowExp e i + colExp e j ≤ r * (pop (i ||| j) - 1) + pop (i &&& j))
    (hstrict : ∀ i j : Nat, C ≤ i → (((i ||| j) + 1) &&& (i ||| j)) = 0 →
      rowExp e i + colExp e j < r * (pop (i ||| j) - 1) + pop (i &&& j))
    (hC2 : 2 ≤ C)
    (R : Mat (min n C))
    (hinv : ∀ (i j : Fin (min n C)),
      matMul R (fun x y => omegaEntry e r u_a u_q x.val y.val) i j % 2 = idMat (min n C) i j) :
    HasV2 (det (fullHybridMat ((2 : Int) ^ r * u_a) (1 + (2 : Int) ^ e * u_q)
      lam (1 + (2 : Int) ^ e * tc) (1 + (2 : Int) ^ e * td) n)) (e * popSum n - e) := by
  let k := min n C
  have hk : k ≤ n := Nat.min_le_left n C
  have hfacM := hybridMat_biscaled_fac e r n u_a u_q hdom
  rcases asymPertMat_div_fac e n lam tc td with ⟨E, hfacΔ⟩
  have hmain := v2_det_perturbation_stability hk
    (hybridMat ((2 : Int) ^ r * u_a) (1 + (2 : Int) ^ e * u_q) n)
    (asymPertMat lam (1 + (2 : Int) ^ e * tc) (1 + (2 : Int) ^ e * td) n)
    (mobMat n) (transpose (mobMat n))
    (fun i j => omegaEntry e r u_a u_q i.val j.val) E
    (fun i => rowExp e i.val) (fun j => colExp e j.val)
    (det_mobMat n) (det_mobMat_transpose n) hfacM hfacΔ
    (by
      intro i j hi
      have hCi : C ≤ i.val := by
        by_cases hle : n ≤ C
        · have : k = n := Nat.min_eq_left hle; omega
        · have : k = C := Nat.min_eq_right (by omega); omega
      rw [omegaEntry_mod2 e r he hr u_a u_q hua huq i.val j.val]
      have hi0 : ¬ (i.val = 0 ∧ j.val = 0) := by omega
      have hi_ne0 : i.val ≠ 0 := by omega
      have hi_ne1 : i.val ≠ 1 := by omega
      have hw0 : (if i.val = 0 ∧ j.val = 0 then (1 : Int)
          else if (((i.val ||| j.val) + 1) &&& (i.val ||| j.val)) = 0 then
            if r * (pop (i.val ||| j.val) - 1) + pop (i.val &&& j.val) -
              (rowExp e i.val + colExp e j.val) = 0 then 1 else 0
          else 0) = 0 := by
        simp only [hi0, ↓reduceIte]
        by_cases hmask : (((i.val ||| j.val) + 1) &&& (i.val ||| j.val)) = 0
        · simp only [hmask, ↓reduceIte]
          have hst := hstrict i.val j.val hCi hmask
          have hne0 : r * (pop (i.val ||| j.val) - 1) + pop (i.val &&& j.val) -
              (rowExp e i.val + colExp e j.val) ≠ 0 := by omega
          simp [hne0]
        · simp [hmask]
      rw [hw0, Int.zero_add]
      by_cases hij : i = j
      · subst hij; simp [hi_ne0, hi_ne1]
      · have hnev : i.val ≠ j.val := fun hv => hij (Fin.ext hv)
        simp [hij, hnev])
    R
    (fun i j => hinv i j)
  rw [sum_rowExp_colExp e n hn] at hmain
  exact hmain

/-! ### Infinite Theorem 1A: Supercritical Regime (`r ≥ 2` and `r ≥ 2e - 1`, `2 × 2` Corner) -/

/-- Exact arithmetic inequality for the Supercritical Regime: `2 × 2` finite corner for ALL `e ≥ 1`! -/
theorem supercritical_strict (e r i j : Nat) (he : 1 ≤ e) (hr2 : 2 ≤ r) (hr : 2 * e - 1 ≤ r)
    (hge : 2 ≤ i ∨ 2 ≤ j) (hmask : (((i ||| j) + 1) &&& (i ||| j)) = 0) :
    rowExp e i + colExp e j < r * (pop (i ||| j) - 1) + pop (i &&& j) := by
  have hk2 : 2 ≤ pop (i ||| j) := by
    have := pop_lor_ge_of_mask hmask (c := 1) (by simpa using hge)
    omega
  have hks : pop (i ||| j) + pop (i &&& j) = pop i + pop j := pop_or_add_and i j
  have hs_le : pop (i &&& j) ≤ pop (i ||| j) := by
    have hs1 : pop (i &&& j) ≤ pop i := pop_and_le_left i j
    have hs2 : pop (i &&& j) ≤ pop j := pop_and_le_right i j
    omega
  have h2sum : 2 * (rowExp e i + colExp e j) ≤ e * (pop (i ||| j) + pop (i &&& j)) + 1 := by
    unfold rowExp colExp
    have hmul : e * pop i + e * pop j = e * (pop (i ||| j) + pop (i &&& j)) := by rw [← Nat.mul_add, hks]
    split <;> split <;> omega
  generalize pop (i ||| j) = k at hk2 hs_le h2sum ⊢
  generalize pop (i &&& j) = s at hs_le h2sum ⊢
  have h2rk : 2 * r * (k - 1) = 2 * (r * (k - 1)) := Nat.mul_assoc 2 r (k - 1)
  by_cases he1 : e = 1
  · subst he1
    have hrk : 4 * (k - 1) ≤ 2 * r * (k - 1) :=
      Nat.mul_le_mul_right (k - 1) (by omega)
    omega
  · have h2r : 4 * e - 2 ≤ 2 * r := by omega
    have hbase : (4 * e - 2) * (k - 1) ≤ 2 * r * (k - 1) :=
      Nat.mul_le_mul_right (k - 1) h2r
    have hs_bound : (e - 2) * s ≤ (e - 2) * k := Nat.mul_le_mul_left (e - 2) hs_le
    have hexp1 : e * (k + s) = e * k + e * s := Nat.mul_add e k s
    have hexp2 : (e - 2) * s + 2 * s = e * s := by
      rw [← Nat.add_mul]; congr 1; omega
    have hexp3 : (e - 2) * k + 2 * k = e * k := by
      rw [← Nat.add_mul]; congr 1; omega
    have hexp4 : (4 * e - 2) * (k - 1) + (4 * e - 2) = (4 * e - 2) * k := by
      have h1 : (4 * e - 2) * (k - 1) + (4 * e - 2) * 1 = (4 * e - 2) * (k - 1 + 1) :=
        (Nat.mul_add (4 * e - 2) (k - 1) 1).symm
      rw [Nat.mul_one, show k - 1 + 1 = k by omega] at h1
      exact h1
    have hexp5 : (4 * e - 2) * k + 2 * k = 4 * (e * k) := by
      rw [← Nat.add_mul]
      have : (4 * e - 2) + 2 = 4 * e := by omega
      rw [this, Nat.mul_assoc]
    have hek_ge : 2 * e ≤ e * k := by
      have := Nat.mul_le_mul_left e hk2; omega
    omega

theorem supercritical_dom (e r i j : Nat) (he : 1 ≤ e) (hr2 : 2 ≤ r) (hr : 2 * e - 1 ≤ r)
    (_h0 : ¬ (i = 0 ∧ j = 0)) (hmask : (((i ||| j) + 1) &&& (i ||| j)) = 0) :
    rowExp e i + colExp e j ≤ r * (pop (i ||| j) - 1) + pop (i &&& j) := by
  by_cases hge : 2 ≤ i ∨ 2 ≤ j
  · exact Nat.le_of_lt (supercritical_strict e r i j he hr2 hr hge hmask)
  · have hi : i ≤ 1 := by omega
    have hj : j ≤ 1 := by omega
    simp [rowExp, colExp, hi, hj]

theorem R_super2_cert :
    ∀ i j : Fin 2, matMul R_super2 (fun r c => if r.val + c.val = 1 then 1 else 0) i j % 2 = idMat 2 i j := by
  decide

/-- **INFINITE THEOREM 1A (Supercritical All-`(e, r)` 5-Parameter Family):**
    For ALL `e ≥ 1`, ALL `r ≥ max(2, 2e - 1)`, ALL odd `u_a, u_q`, ALL perturbation integers
    `lam, tc, td`, and ALL `n ≥ 2`:
    `v_2(det(fullHybridMat (2^r * u_a) (1 + 2^e * u_q) lam (1 + 2^e * tc) (1 + 2^e * td) n)) = e * popSum n - e`! -/
theorem theorem_1A_supercritical (e r n : Nat) (he : 1 ≤ e) (hr2 : 2 ≤ r) (hr : 2 * e - 1 ≤ r)
    (hn : 2 ≤ n) (u_a u_q lam tc td : Int) (hua : u_a % 2 = 1) (huq : u_q % 2 = 1) :
    HasV2 (det (fullHybridMat ((2 : Int) ^ r * u_a) (1 + (2 : Int) ^ e * u_q)
      lam (1 + (2 : Int) ^ e * tc) (1 + (2 : Int) ^ e * td) n)) (e * popSum n - e) := by
  have hmin : min n 2 = 2 := Nat.min_eq_right hn
  apply fullHybridMat_lift (C := 2) he (by omega) hn u_a u_q lam tc td hua huq
    (fun i j h0 hmask => supercritical_dom e r i j he hr2 hr h0 hmask)
    (fun i j hi hmask => supercritical_strict e r i j he hr2 hr (Or.inl hi) hmask)
    (Nat.le_refl 2)
    (fun i j => R_super2 ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)
  · intro i j
    have hcorner : ∀ (x y : Fin (min n 2)),
        omegaEntry e r u_a u_q x.val y.val % 2 = (if x.val + y.val = 1 then 1 else 0) := by
      intro x y
      rw [omegaEntry_mod2 e r he (by omega) u_a u_q hua huq x.val y.val]
      have hx : x.val = 0 ∨ x.val = 1 := by omega
      have hy : y.val = 0 ∨ y.val = 1 := by omega
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · simp [hx, hy]
      · simp [hx, hy, show (0 : Nat) ||| 1 = 1 by decide, show (0 : Nat) &&& 1 = 0 by decide,
          show pop 1 = 1 by decide, pop_zero, rowExp, colExp]
      · simp [hx, hy, show (1 : Nat) ||| 0 = 1 by decide, show (1 : Nat) &&& 0 = 0 by decide,
          show pop 1 = 1 by decide, pop_zero, rowExp, colExp]
      · simp [hx, hy, show (1 : Nat) ||| 1 = 1 by decide, show (1 : Nat) &&& 1 = 1 by decide,
          show pop 1 = 1 by decide, rowExp, colExp]
    have hmul : matMul (fun a b : Fin (min n 2) => R_super2 ⟨a.val, by omega⟩ ⟨b.val, by omega⟩)
        (fun x y : Fin (min n 2) => omegaEntry e r u_a u_q x.val y.val) i j % 2 =
        matMul R_super2 (fun r c => if r.val + c.val = 1 then 1 else 0) ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ % 2 := by
      have h1 : matMul (fun a b : Fin (min n 2) => R_super2 ⟨a.val, by omega⟩ ⟨b.val, by omega⟩)
          (fun x y : Fin (min n 2) => omegaEntry e r u_a u_q x.val y.val) i j % 2 =
          matMul (fun a b : Fin (min n 2) => R_super2 ⟨a.val, by omega⟩ ⟨b.val, by omega⟩)
          (fun x y : Fin (min n 2) => if x.val + y.val = 1 then 1 else 0) i j % 2 := by
        simp only [matMul]
        apply sumFin_mod2_congr; intro c
        rw [Int.mul_emod, hcorner c j]
        have hbit : (if c.val + j.val = 1 then (1 : Int) else 0) % 2 =
            (if c.val + j.val = 1 then (1 : Int) else 0) := by split <;> rfl
        rw [Int.mul_emod (R_super2 ⟨i.val, by omega⟩ ⟨c.val, by omega⟩), hbit]
      rw [h1]
      have hlen : ∀ (m : Nat) (hm : m = 2) (i' j' : Fin m),
          matMul (fun a b : Fin m => R_super2 ⟨a.val, by omega⟩ ⟨b.val, by omega⟩)
            (fun x y : Fin m => if x.val + y.val = 1 then 1 else 0) i' j' =
          matMul R_super2 (fun r c => if r.val + c.val = 1 then 1 else 0)
            ⟨i'.val, by omega⟩ ⟨j'.val, by omega⟩ := by
        intro m hm i' j'; subst hm; rfl
      rw [hlen (min n 2) hmin i j]
    rw [hmul, R_super2_cert]
    simp only [idMat]
    by_cases hij : i = j
    · subst hij; simp
    · have hne : (⟨i.val, by omega⟩ : Fin 2) ≠ ⟨j.val, by omega⟩ := by
        intro h; apply hij; apply Fin.ext
        have hv : (⟨i.val, by omega⟩ : Fin 2).val = (⟨j.val, by omega⟩ : Fin 2).val := congrArg Fin.val h
        exact hv
      simp [hij, hne]

/-! ### Infinite Theorem 1B: Critical Rescue Regime I (`e = 1, r = 1`, `8 × 8` Finite Corner) -/

theorem critical1_dom (i j : Nat) (_h0 : ¬ (i = 0 ∧ j = 0))
    (hmask : (((i ||| j) + 1) &&& (i ||| j)) = 0) :
    rowExp 1 i + colExp 1 j ≤ 1 * (pop (i ||| j) - 1) + pop (i &&& j) := by
  by_cases hge : 2 ≤ i ∨ 2 ≤ j
  · have hk2 : 2 ≤ pop (i ||| j) := by
      have := pop_lor_ge_of_mask hmask (c := 1) (by simpa using hge); omega
    have hks : pop (i ||| j) + pop (i &&& j) = pop i + pop j := pop_or_add_and i j
    unfold rowExp colExp
    split <;> split <;> omega
  · have hi : i ≤ 1 := by omega
    have hj : j ≤ 1 := by omega
    simp [rowExp, colExp, hi, hj]

theorem critical1_strict (i j : Nat) (hi8 : 8 ≤ i)
    (hmask : (((i ||| j) + 1) &&& (i ||| j)) = 0) :
    rowExp 1 i + colExp 1 j < 1 * (pop (i ||| j) - 1) + pop (i &&& j) := by
  have hk4 : 4 ≤ pop (i ||| j) := by
    have := pop_lor_ge_of_mask hmask (c := 3) (Or.inl (by simpa using hi8)); omega
  have hks : pop (i ||| j) + pop (i &&& j) = pop i + pop j := pop_or_add_and i j
  unfold rowExp colExp
  split <;> split <;> omega

theorem R_crit1_cert_2 : ∀ i j : Fin 2, matMul (R_crit1 2) (cornerCrit1 2) i j % 2 = idMat 2 i j := by decide

theorem R_crit1_cert_3 : ∀ i j : Fin 3, matMul (R_crit1 3) (cornerCrit1 3) i j % 2 = idMat 3 i j := by decide

theorem R_crit1_cert_4 : ∀ i j : Fin 4, matMul (R_crit1 4) (cornerCrit1 4) i j % 2 = idMat 4 i j := by decide

theorem R_crit1_cert_5 : ∀ i j : Fin 5, matMul (R_crit1 5) (cornerCrit1 5) i j % 2 = idMat 5 i j := by decide

theorem R_crit1_cert_6 : ∀ i j : Fin 6, matMul (R_crit1 6) (cornerCrit1 6) i j % 2 = idMat 6 i j := by decide

theorem R_crit1_cert_7 : ∀ i j : Fin 7, matMul (R_crit1 7) (cornerCrit1 7) i j % 2 = idMat 7 i j := by decide

theorem R_crit1_cert_8 : ∀ i j : Fin 8, matMul (R_crit1 8) (cornerCrit1 8) i j % 2 = idMat 8 i j := by decide

theorem R_crit1_cert_all (k : Nat) (hk2 : 2 ≤ k) (hk8 : k ≤ 8) :
    ∀ i j : Fin k, matMul (R_crit1 k) (cornerCrit1 k) i j % 2 = idMat k i j := by
  have hcases : k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact R_crit1_cert_2
  · exact R_crit1_cert_3
  · exact R_crit1_cert_4
  · exact R_crit1_cert_5
  · exact R_crit1_cert_6
  · exact R_crit1_cert_7
  · exact R_crit1_cert_8

/-- **INFINITE THEOREM 1B (Critical Rescue Regime I: `e = 1, r = 1`, `a ≡ 2 (mod 4)`, `q ≡ 3 (mod 4)`):**
    For ALL odd `u_a, u_q`, ALL perturbation integers `lam, tc, td`, and ALL `n ≥ 2`:
    `v_2(det(fullHybridMat (2 * u_a) (1 + 2 * u_q) lam (1 + 2 * tc) (1 + 2 * td) n)) = popSum n - 1`! -/
theorem theorem_1B_critical_I (n : Nat) (hn : 2 ≤ n)
    (u_a u_q lam tc td : Int) (hua : u_a % 2 = 1) (huq : u_q % 2 = 1) :
    HasV2 (det (fullHybridMat (2 * u_a) (1 + 2 * u_q) lam (1 + 2 * tc) (1 + 2 * td) n))
      (popSum n - 1) := by
  have h := fullHybridMat_lift (e := 1) (r := 1) (C := 8) (n := n)
    (by omega) (by omega) hn u_a u_q lam tc td hua huq
    critical1_dom critical1_strict (by omega)
    (R_crit1 (min n 8))
    (by
      intro i j
      have hmod : matMul (R_crit1 (min n 8)) (fun x y => omegaEntry 1 1 u_a u_q x.val y.val) i j % 2 =
          matMul (R_crit1 (min n 8)) (cornerCrit1 (min n 8)) i j % 2 := by
        simp only [matMul]
        apply sumFin_mod2_congr; intro c
        rw [Int.mul_emod, omegaEntry_mod2 1 1 (by omega) (by omega) u_a u_q hua huq c.val j.val]
        have hcc : cornerCrit1 (min n 8) c j % 2 = cornerCrit1 (min n 8) c j := Int.emod_emod _ 2
        rw [Int.mul_emod (R_crit1 (min n 8) i c) (cornerCrit1 (min n 8) c j), hcc]
        simp only [cornerCrit1, Nat.one_mul]
      rw [hmod]
      exact R_crit1_cert_all (min n 8) (by omega) (Nat.min_le_right n 8) i j)
  simpa using h

/-! ### Infinite Theorem 1C: Critical Rescue Regime II (`e = 2, r = 2`, `4 × 4` Finite Corner) -/

theorem critical2_dom (i j : Nat) (_h0 : ¬ (i = 0 ∧ j = 0))
    (hmask : (((i ||| j) + 1) &&& (i ||| j)) = 0) :
    rowExp 2 i + colExp 2 j ≤ 2 * (pop (i ||| j) - 1) + pop (i &&& j) := by
  by_cases hge : 2 ≤ i ∨ 2 ≤ j
  · have hk2 : 2 ≤ pop (i ||| j) := by
      have := pop_lor_ge_of_mask hmask (c := 1) (by simpa using hge); omega
    have hks : pop (i ||| j) + pop (i &&& j) = pop i + pop j := pop_or_add_and i j
    unfold rowExp colExp
    split <;> split <;> omega
  · have hi : i ≤ 1 := by omega
    have hj : j ≤ 1 := by omega
    simp [rowExp, colExp, hi, hj]

theorem critical2_strict (i j : Nat) (hi4 : 4 ≤ i)
    (hmask : (((i ||| j) + 1) &&& (i ||| j)) = 0) :
    rowExp 2 i + colExp 2 j < 2 * (pop (i ||| j) - 1) + pop (i &&& j) := by
  have hk3 : 3 ≤ pop (i ||| j) := by
    have := pop_lor_ge_of_mask hmask (c := 2) (Or.inl (by simpa using hi4)); omega
  have hks : pop (i ||| j) + pop (i &&& j) = pop i + pop j := pop_or_add_and i j
  unfold rowExp colExp
  split <;> split <;> omega

theorem R_crit2_cert_2 : ∀ i j : Fin 2, matMul (R_crit2 2) (cornerCrit2 2) i j % 2 = idMat 2 i j := by decide

theorem R_crit2_cert_3 : ∀ i j : Fin 3, matMul (R_crit2 3) (cornerCrit2 3) i j % 2 = idMat 3 i j := by decide

theorem R_crit2_cert_4 : ∀ i j : Fin 4, matMul (R_crit2 4) (cornerCrit2 4) i j % 2 = idMat 4 i j := by decide

theorem R_crit2_cert_all (k : Nat) (hk2 : 2 ≤ k) (hk4 : k ≤ 4) :
    ∀ i j : Fin k, matMul (R_crit2 k) (cornerCrit2 k) i j % 2 = idMat k i j := by
  have hcases : k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact R_crit2_cert_2
  · exact R_crit2_cert_3
  · exact R_crit2_cert_4

/-- **INFINITE THEOREM 1C (Critical Rescue Regime II: `e = 2, r = 2`, `a ≡ 4 (mod 8)`, `q ≡ 5 (mod 8)`):**
    For ALL odd `u_a, u_q`, ALL perturbation integers `lam, tc, td`, and ALL `n ≥ 2`:
    `v_2(det(fullHybridMat (4 * u_a) (1 + 4 * u_q) lam (1 + 4 * tc) (1 + 4 * td) n)) = 2 * popSum n - 2`! -/
theorem theorem_1C_critical_II (n : Nat) (hn : 2 ≤ n)
    (u_a u_q lam tc td : Int) (hua : u_a % 2 = 1) (huq : u_q % 2 = 1) :
    HasV2 (det (fullHybridMat (4 * u_a) (1 + 4 * u_q) lam (1 + 4 * tc) (1 + 4 * td) n))
      (2 * popSum n - 2) := by
  have h := fullHybridMat_lift (e := 2) (r := 2) (C := 4) (n := n)
    (by omega) (by omega) hn u_a u_q lam tc td hua huq
    critical2_dom critical2_strict (by omega)
    (R_crit2 (min n 4))
    (by
      intro i j
      have hmod : matMul (R_crit2 (min n 4)) (fun x y => omegaEntry 2 2 u_a u_q x.val y.val) i j % 2 =
          matMul (R_crit2 (min n 4)) (cornerCrit2 (min n 4)) i j % 2 := by
        simp only [matMul]
        apply sumFin_mod2_congr; intro c
        rw [Int.mul_emod, omegaEntry_mod2 2 2 (by omega) (by omega) u_a u_q hua huq c.val j.val]
        have hcc : cornerCrit2 (min n 4) c j % 2 = cornerCrit2 (min n 4) c j := Int.emod_emod _ 2
        rw [Int.mul_emod (R_crit2 (min n 4) i c) (cornerCrit2 (min n 4) c j), hcc]
        simp only [cornerCrit2]
      rw [hmod]
      exact R_crit2_cert_all (min n 4) (by omega) (Nat.min_le_right n 4) i j)
  simpa using h

/-- **Boundary Jump at `n = 1`:** For ALL `a, q`, `det (hybridMat a q 1) = 2`, hence `v_2 = 1`! -/
theorem theorem_n1_jump (a q : Int) : HasV2 (det (hybridMat a q 1)) 1 := by
  refine ⟨1, by decide, ?_⟩
  simp [det, sumFin, signNat, hybridMat, v2Succ_zero, pop_zero]

/-! ### Section 4: Kernel-Checked Sharpness & Phase-Transition Breakdown Theorems -/

/-- **Sharpness Theorem S1 (Odd `a` Unconditional Failure at `n = 2`):**
    Relaxing `r ≥ 1` (`a` even) to `r = 0` (`a` odd) breaks `v_2(det N_2) = 0` for EVERY odd `a, q`! -/
theorem sharpness_S1_odd_a_fails (a q : Int) (ha : a % 2 = 1) (hq : q % 2 = 1) :
    ¬ HasV2 (det (hybridMat a q 2)) 0 := by
  have hdet : det (hybridMat a q 2) = 2 * (q + 1) - (a + 1) * (a + 1) := by
    simp only [det, sumFin, minorLast, skipIdx, hybridMat, signNat, Fin.last, Fin.val_castSucc]
    simp only [show (0 : Nat) < 0 ↔ False by decide, show (0 : Nat) < 1 ↔ True by decide,
      ↓reduceDIte, show (1 + 0) % 2 = 0 ↔ False by decide, ↓reduceIte]
    have h00 : v2Succ (0 ^^^ 0) = 0 := rfl
    have h01 : v2Succ (0 ^^^ 1) = 1 := rfl
    have h10 : v2Succ (1 ^^^ 0) = 1 := rfl
    have h11 : v2Succ (1 ^^^ 1) = 0 := rfl
    have p00 : pop (0 &&& 0) = 0 := rfl
    have p01 : pop (0 &&& 1) = 0 := rfl
    have p10 : pop (1 &&& 0) = 0 := rfl
    have p11 : pop (1 &&& 1) = 1 := rfl
    simp only [h00, h01, h10, h11, p00, p01, p10, p11, Int.pow_zero, Int.pow_one,
      Int.zero_add, Int.one_mul, Int.mul_one, Int.neg_mul]
    omega
  intro ⟨u, hu, heq⟩
  rw [hdet, Int.pow_zero, Int.one_mul] at heq
  have h1 : (a + 1) % 2 = 0 := by omega
  have hsq : ((a + 1) * (a + 1)) % 2 = 0 := by
    rw [Int.mul_emod, h1]; rfl
  omega

/-- **Sharpness Theorem S2 (Exact Singularity Counterexample at `(e, r) = (2, 1)`):**
    At `a = 2, q = 5` (`r = 1 < e = 2`), `det (hybridMat 2 5 4) = 0`, so `v_2 = ∞`! -/
theorem sharpness_S2_singularity_2_5 : det (hybridMat 2 5 4) = 0 := by
  decide

/-- **Sharpness Theorem S3 (Infinite Breakdown Line `r = 2e - 2` for ALL `e ≥ 3`):**
    Proved directly through our bi-scaled elimination engine!
    For EVERY `e ≥ 3` and EVERY odd `u_a, u_q`, at `r = 2e - 2` row 3 of `Ω_4` vanishes identically mod 2,
    forcing `2^(3e + 1) ∣ det (hybridMat (2^(2e-2)*u_a) (1 + 2^e*u_q) 4)`, hence breaking `e * popSum 4 - e = 3e`! -/
theorem sharpness_S3_infinite_breakdown_line (e : Nat) (he : 3 ≤ e)
    (u_a u_q : Int) (hua : u_a % 2 = 1) (huq : u_q % 2 = 1) :
    ¬ HasV2 (det (hybridMat ((2 : Int) ^ (2 * e - 2) * u_a) (1 + (2 : Int) ^ e * u_q) 4))
      (e * popSum 4 - e) := by
  -- Step 1: Show rowExp e i + colExp e j ≤ (2*e - 2)*(pop(i|||j) - 1) + pop(i&&&j) for ALL i, j < 4!
  -- In fact it holds for ALL i, j ∈ Nat! Let's prove it for the 4×4 matrix directly!
  let a := (2 : Int) ^ (2 * e - 2) * u_a
  let q := 1 + (2 : Int) ^ e * u_q
  let Ω : Mat 4 := fun i j => omegaEntry e (2 * e - 2) u_a u_q i.val j.val
  have hfac : matMul (matMul (mobMat 4) (hybridMat a q 4)) (transpose (mobMat 4)) =
      biScale (fun i => rowExp e i.val) (fun j => colExp e j.val) Ω := by
    apply hybridMat_biscaled_fac e (2 * e - 2) 4 u_a u_q
    intro i j _h0 hmask
    by_cases hge : 2 ≤ i ∨ 2 ≤ j
    · have hk2 : 2 ≤ pop (i ||| j) := by
        have := pop_lor_ge_of_mask hmask (c := 1) (by simpa using hge); omega
      have hks : pop (i ||| j) + pop (i &&& j) = pop i + pop j := pop_or_add_and i j
      have hs_le : pop (i &&& j) ≤ pop (i ||| j) := by
        have := pop_and_le_left i j; have := pop_and_le_right i j; omega
      have h2sum : 2 * (rowExp e i + colExp e j) ≤ e * (pop (i ||| j) + pop (i &&& j)) + 1 := by
        unfold rowExp colExp
        have hmul : e * pop i + e * pop j = e * (pop (i ||| j) + pop (i &&& j)) := by rw [← Nat.mul_add, hks]
        split <;> split <;> omega
      by_cases h22 : pop (i ||| j) = 2 ∧ pop (i &&& j) = 2
      · rcases h22 with ⟨hk_eq, hs_eq⟩
        have hpi : pop i = 2 := by have := pop_and_le_left i j; have := pop_and_le_right i j; omega
        have hpj : pop j = 2 := by have := pop_and_le_left i j; have := pop_and_le_right i j; omega
        rw [hk_eq, hs_eq]
        unfold rowExp colExp
        rw [hpi, hpj]
        split <;> split <;> omega
      · generalize pop (i ||| j) = k at hk2 hs_le h2sum h22 ⊢
        generalize pop (i &&& j) = s at hs_le h2sum h22 ⊢
        have hs_bound : (e - 2) * s ≤ (e - 2) * k := Nat.mul_le_mul_left (e - 2) hs_le
        have hexp1 : e * (k + s) = e * k + e * s := Nat.mul_add e k s
        have hexp2 : (e - 2) * s + 2 * s = e * s := by rw [← Nat.add_mul]; congr 1; omega
        have hexp3 : (e - 2) * k + 2 * k = e * k := by rw [← Nat.add_mul]; congr 1; omega
        have hexp4 : (4 * e - 4) * (k - 1) + (4 * e - 4) = (4 * e - 4) * k := by
          have h1 : (4 * e - 4) * (k - 1) + (4 * e - 4) * 1 = (4 * e - 4) * (k - 1 + 1) :=
            (Nat.mul_add (4 * e - 4) (k - 1) 1).symm
          rw [Nat.mul_one, show k - 1 + 1 = k by omega] at h1
          exact h1
        have hexp5 : (4 * e - 4) * k + 4 * k = 4 * (e * k) := by
          rw [← Nat.add_mul]
          have : (4 * e - 4) + 4 = 4 * e := by omega
          rw [this, Nat.mul_assoc]
        have h2r : 2 * ((2 * e - 2) * (k - 1)) = (4 * e - 4) * (k - 1) := by
          rw [← Nat.mul_assoc]; congr 1; omega
        by_cases hk3 : 3 ≤ k
        · have hek3 : 3 * e ≤ e * k := by have := Nat.mul_le_mul_left e hk3; omega
          have hek_k : 3 * k ≤ e * k := Nat.mul_le_mul_right k he
          omega
        · have hk_eq : k = 2 := by omega
          subst hk_eq
          have hs_lt : s ≤ 1 := by omega
          have hs_b1 : (e - 2) * s ≤ e - 2 := by
            have := Nat.mul_le_mul_left (e - 2) hs_lt; simpa using this
          omega
    · have hi : i ≤ 1 := by omega
      have hj : j ≤ 1 := by omega
      simp [rowExp, colExp, hi, hj]
  -- Step 2: Take det of hfac: det (hybridMat a q 4) = 2^(e * popSum 4 - e) * det Ω
  have hdet_eq : det (hybridMat a q 4) = (2 : Int) ^ (e * popSum 4 - e) * det Ω := by
    have h1 := congrArg det hfac
    rw [det_matMul, det_matMul, det_mobMat, det_mobMat_transpose, Int.one_mul, Int.mul_one,
      det_biScale, sum_rowExp_colExp e 4 (by omega)] at h1
    exact h1
  -- Step 3: Show column 3 (Fin.last 3) of Ω is identically EVEN (≡ 0 mod 2) for ALL e ≥ 3!
  have hcol3_even : ∀ i : Fin 4, Ω i (Fin.last 3) % 2 = 0 := by
    intro i
    dsimp only [Ω]
    simp only [Fin.val_last]
    rw [omegaEntry_mod2 e (2 * e - 2) (by omega) (by omega) u_a u_q hua huq i.val 3]
    have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
    rcases hi with hi | hi | hi | hi
    · simp only [hi, show (0 : Nat) ||| 3 = 3 by decide, show (0 : Nat) &&& 3 = 0 by decide,
        show pop 3 = 2 by decide, pop_zero, rowExp, colExp]
      have hne : 2 * e - 2 - (e * 2 + 1) / 2 ≠ 0 := by omega
      simp [hne]
    · simp only [hi, show (1 : Nat) ||| 3 = 3 by decide, show (1 : Nat) &&& 3 = 1 by decide,
        show pop 3 = 2 by decide, show pop 1 = 1 by decide, rowExp, colExp]
      have hne : 2 * e - 2 + 1 - (e * 2 + 1) / 2 ≠ 0 := by omega
      simp [hne]
    · simp only [hi, show (2 : Nat) ||| 3 = 3 by decide, show (2 : Nat) &&& 3 = 2 by decide,
        show pop 3 = 2 by decide, show pop 2 = 1 by decide, rowExp, colExp]
      have hne : 2 * e - 2 + 1 - (e / 2 + (e * 2 + 1) / 2) ≠ 0 := by omega
      simp [hne]
    · simp only [hi, show (3 : Nat) ||| 3 = 3 by decide, show (3 : Nat) &&& 3 = 3 by decide,
        show pop 3 = 2 by decide, rowExp, colExp]
      have heq0 : 2 * e - 2 + 2 - (e + (e * 2 + 1) / 2) = 0 := by omega
      simp [heq0]
  -- Step 4: Since column 3 of Ω is identically even, det Ω % 2 = 0!
  have hdetΩ_even : det Ω % 2 = 0 := by
    have hzero : det (scaleCol Ω (Fin.last 3) 0) = 0 := by
      rw [det_scaleCol]; simp
    have hcongr : det Ω % 2 = det (scaleCol Ω (Fin.last 3) 0) % 2 := by
      apply det_mod2_congr
      intro i j
      unfold scaleCol
      by_cases hj : j = Fin.last 3
      · subst hj; rw [ite_eq_left_iff.mpr (fun h => absurd rfl h), Int.zero_mul]; exact hcol3_even i
      · rw [ite_eq_right_iff.mpr (fun h => absurd h hj)]
    rw [hcongr, hzero]
    rfl
  -- Step 5: Contradiction with HasV2 (det (hybridMat a q 4)) (e * popSum 4 - e)!
  intro ⟨u, hu, heq⟩
  rw [hdet_eq] at heq
  have hpos : (0 : Int) < (2 : Int) ^ (e * popSum 4 - e) := two_pow_pos _
  have hu_eq : det Ω = u := Int.eq_of_mul_eq_mul_left (by omega) heq
  rw [hu_eq] at hdetΩ_even
  omega

/-- **Sharpness Theorem S4 (Odd Perturbation Multiple Breaks Invariance at `n = 3`):**
    Replacing the factor `2 * lam` by `1` (odd multiple of `Q(3, 5)`) breaks `v_2 = S(3) - 1 = 1`! -/
theorem sharpness_S4_odd_perturbation_fails :
    det (matAdd (hybridMat 4 3 3)
      (fun i j => (3 : Int) ^ pop (bitDiff j.val i.val) * (5 : Int) ^ pop (i.val &&& j.val))) % 4 = 0 := by
  decide

/-! ### Section 5: Kernel-Checked Non-Vacuity Witnesses & Axiom Audit -/

/-- Non-vacuity witness 1: Supercritical `(e=3, r=5)` with asymmetric dense perturbation `(lam=1, c=9, d=17)` for ALL `n ≥ 2`. -/
example (n : Nat) (hn : 2 ≤ n) :
    HasV2 (det (fullHybridMat 32 9 1 9 17 n)) (3 * popSum n - 3) := by
  have h := theorem_1A_supercritical 3 5 n (by omega) (by omega) (by omega) hn 1 1 1 1 2
    (by decide) (by decide)
  simpa using h

/-- Non-vacuity witness 2: Critical Rescue I `(e=1, r=1)` with asymmetric dense perturbation `(a=2, q=3, lam=1, c=3, d=5)` for ALL `n ≥ 2`. -/
example (n : Nat) (hn : 2 ≤ n) :
    HasV2 (det (fullHybridMat 2 3 1 3 5 n)) (popSum n - 1) := by
  have h := theorem_1B_critical_I n hn 1 1 1 1 2 (by decide) (by decide)
  simpa using h

/-- Non-vacuity witness 3: Critical Rescue II `(e=2, r=2)` with asymmetric dense perturbation `(a=4, q=5, lam=1, c=5, d=9)` for ALL `n ≥ 2`. -/
example (n : Nat) (hn : 2 ≤ n) :
    HasV2 (det (fullHybridMat 4 5 1 5 9 n)) (2 * popSum n - 2) := by
  have h := theorem_1C_critical_II n hn 1 1 1 1 2 (by decide) (by decide)
  simpa using h

/-- Non-vacuity witness 4: Concrete determinant check confirming non-trivial odd parts (not pure powers of 2!). -/
example : det (fullHybridMat 2 3 1 3 5 4) = 8 * 149 := by decide

example : det (fullHybridMat 4 5 1 5 9 4) = 64 * (-171) := by decide

end SpecMat12
