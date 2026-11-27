/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BitSliceHankelDifferenceLdu.Defs

/-!
# Theorems (`bit-slice-hankel-difference-ldu`)

Full proofs of the headline infinite theorems of Bitwise Hankel and Automatic-Sequence LDU Factorization Engine.
-/

namespace BitwiseHankelLDU

theorem altSign_add (a b : Nat) : altSign (a + b) = altSign a * altSign b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.add_succ, altSign_succ, altSign_succ, ih, Int.mul_neg]

theorem altSign_mul_self (k : Nat) : altSign k * altSign k = 1 := by
  unfold altSign
  split <;> decide

theorem altSign_two_mul (k : Nat) : altSign (2 * k) = 1 := by
  unfold altSign
  have : (2 * k) % 2 = 0 := by omega
  simp [this]

theorem altSign_sq_eq (k : Nat) : altSign (k * k) = altSign k := by
  unfold altSign
  rw [Nat.mul_mod]
  by_cases h : k % 2 = 0
  · simp [h]
  · have h1 : k % 2 = 1 := by omega
    simp [h1]

theorem finSum_congr {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i = g i) :
    finSum f = finSum g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [finSum, finSum, h 0]
    congr 1
    exact ih (fun i => h i.succ)

theorem finSum_zero {n : Nat} : finSum (fun _ : Fin n => (0 : Int)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [finSum, ih]; omega

theorem finSum_add {n : Nat} (f g : Fin n → Int) :
    finSum (fun i => f i + g i) = finSum f + finSum g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [finSum, finSum, finSum, ih]
    omega

theorem finSum_neg {n : Nat} (f : Fin n → Int) :
    finSum (fun i => -f i) = -finSum f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [finSum, finSum, ih]
    omega

theorem finSum_mul_left {n : Nat} (c : Int) (f : Fin n → Int) :
    finSum (fun i => c * f i) = c * finSum f := by
  induction n with
  | zero => simp [finSum]
  | succ n ih =>
    rw [finSum, finSum, ih, Int.mul_add]

theorem finSum_mul_right {n : Nat} (f : Fin n → Int) (c : Int) :
    finSum (fun i => f i * c) = finSum f * c := by
  induction n with
  | zero => simp [finSum]
  | succ n ih =>
    rw [finSum, finSum, ih, Int.add_mul]

theorem finSum_single {n : Nat} (k : Fin n) (f : Fin n → Int)
    (h : ∀ i : Fin n, i ≠ k → f i = 0) :
    finSum f = f k := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    rw [finSum]
    cases k using Fin.cases with
    | zero =>
      have htail : finSum (fun i : Fin n => f i.succ) = 0 := by
        rw [finSum_congr (g := fun _ => 0)]
        · exact finSum_zero
        · intro i; exact h i.succ (Fin.succ_ne_zero i)
      omega
    | succ k' =>
      have h0 : f 0 = 0 := h 0 (Fin.succ_ne_zero k').symm
      rw [h0, Int.zero_add]
      exact ih k' (fun i => f i.succ) (fun i hi => h i.succ (fun heq => hi (Fin.succ_inj.mp heq)))

theorem finSum_comm {m n : Nat} (f : Fin m → Fin n → Int) :
    finSum (fun i => finSum (fun j => f i j)) = finSum (fun j => finSum (fun i => f i j)) := by
  induction m with
  | zero =>
    rw [finSum]
    symm
    exact (finSum_congr (g := fun _ => 0) (fun _ => rfl)).trans finSum_zero
  | succ m ih =>
    rw [finSum, ih, ← finSum_add]
    apply finSum_congr
    intro j
    rw [finSum]

theorem finSum_succ {n : Nat} (f : Fin (n + 1) → Int) :
    finSum f = f 0 + finSum (fun i : Fin n => f i.succ) := rfl

theorem finSum_split_last {m : Nat} (f : Fin (m + 1) → Int) :
    finSum f = finSum (fun k : Fin m => f ⟨k.val, by omega⟩) + f ⟨m, by omega⟩ := by
  induction m with
  | zero =>
    rw [finSum_succ, finSum, finSum]
    have h0 : (⟨0, by omega⟩ : Fin 1) = 0 := rfl
    rw [h0]; omega
  | succ m ih =>
    rw [finSum_succ f, finSum_succ (fun k : Fin (m + 1) => f ⟨k.val, by omega⟩)]
    have h0 : (⟨(0 : Fin (m + 1)).val, by omega⟩ : Fin (m + 2)) = 0 := rfl
    rw [h0, ih (fun k : Fin (m + 1) => f k.succ)]
    have h1 : (fun i : Fin m => f ⟨i.succ.val, by omega⟩) =
              (fun k : Fin m => f (⟨k.val, by omega⟩ : Fin (m + 1)).succ) := by
      funext k; congr 1
    have h2 : (⟨m + 1, by omega⟩ : Fin (m + 2)) = (⟨m, by omega⟩ : Fin (m + 1)).succ := rfl
    rw [h1, h2]
    omega

theorem adjSwapFin_invol {n : Nat} (k : Fin n) (i : Fin (n + 1)) :
    adjSwapFin k (adjSwapFin k i) = i := by
  apply Fin.ext
  unfold adjSwapFin
  by_cases h1 : i.val = k.val
  · simp [h1]
  · by_cases h2 : i.val = k.val + 1
    · simp [h2]
    · simp [h1, h2]

theorem adjSwapFin_zero_zero {n : Nat} : adjSwapFin (0 : Fin (n + 1)) 0 = Fin.succ 0 := by
  apply Fin.ext; simp [adjSwapFin]

theorem adjSwapFin_zero_one {n : Nat} : adjSwapFin (0 : Fin (n + 1)) (Fin.succ 0) = 0 := by
  apply Fin.ext; simp [adjSwapFin]

theorem adjSwapFin_zero_succ_succ {n : Nat} (i : Fin n) :
    adjSwapFin (0 : Fin (n + 1)) i.succ.succ = i.succ.succ := by
  apply Fin.ext
  unfold adjSwapFin
  simp [Fin.val_succ]

theorem adjSwapFin_succ_zero {n : Nat} (k : Fin n) :
    adjSwapFin k.succ 0 = 0 := by
  apply Fin.ext
  unfold adjSwapFin
  simp [Fin.val_succ]

theorem adjSwapFin_val {n : Nat} (k : Fin n) (i : Fin (n + 1)) :
    (adjSwapFin k i).val =
      if i.val = k.val then k.val + 1
      else if i.val = k.val + 1 then k.val
      else i.val := by
  unfold adjSwapFin
  split
  · rfl
  · split <;> rfl

theorem adjSwapFin_succ_succ {n : Nat} (k : Fin n) (i : Fin (n + 1)) :
    adjSwapFin k.succ i.succ = (adjSwapFin k i).succ := by
  apply Fin.ext
  simp only [adjSwapFin_val, Fin.val_succ]
  grind

theorem finSum_swap_adj {n : Nat} (c : Fin n) (f : Fin (n + 1) → Int) :
    finSum (fun j : Fin (n + 1) => f (adjSwapFin c j)) = finSum f := by
  induction n with
  | zero => exact Fin.elim0 c
  | succ n ih =>
    cases c using Fin.cases with
    | zero =>
      rw [finSum_succ (fun j => f (adjSwapFin 0 j)),
          finSum_succ (fun j => f (adjSwapFin 0 j.succ)),
          finSum_succ f, finSum_succ (fun j => f j.succ)]
      rw [adjSwapFin_zero_zero, adjSwapFin_zero_one]
      have hrest : finSum (fun i : Fin n => f (adjSwapFin 0 i.succ.succ)) =
                   finSum (fun i : Fin n => f i.succ.succ) := by
        apply finSum_congr; intro i; rw [adjSwapFin_zero_succ_succ]
      rw [hrest]
      omega
    | succ c' =>
      rw [finSum_succ (fun j => f (adjSwapFin c'.succ j)), finSum_succ f]
      rw [adjSwapFin_succ_zero]
      congr 1
      have hstep : finSum (fun i : Fin (n + 1) => f (adjSwapFin c'.succ i.succ)) =
                   finSum (fun i : Fin (n + 1) => f (adjSwapFin c' i).succ) := by
        apply finSum_congr; intro i; rw [adjSwapFin_succ_succ]
      rw [hstep]
      exact ih c' (fun i => f i.succ)

theorem skipIdx_val {n : Nat} (p : Fin (n + 1)) (i : Fin n) :
    (skipIdx p i).val = if i.val < p.val then i.val else i.val + 1 := by
  unfold skipIdx; split <;> rfl

theorem skipIdx_val_lt {n : Nat} (p : Fin (n + 1)) (i : Fin n) (h : i.val < p.val) :
    (skipIdx p i).val = i.val := by
  simp [skipIdx, h]

theorem skipIdx_val_ge {n : Nat} (p : Fin (n + 1)) (i : Fin n) (h : ¬ i.val < p.val) :
    (skipIdx p i).val = i.val + 1 := by
  simp [skipIdx, h]

theorem skipIdx_zero {n : Nat} (i : Fin n) : skipIdx 0 i = i.succ := by
  apply Fin.ext; simp [skipIdx]

theorem skipIdx_succ_zero {n : Nat} (p : Fin (n + 1)) : skipIdx p.succ 0 = 0 := by
  apply Fin.ext; simp [skipIdx]

theorem skipIdx_succ_succ {n : Nat} (p : Fin (n + 1)) (i : Fin n) :
    skipIdx p.succ i.succ = (skipIdx p i).succ := by
  apply Fin.ext
  unfold skipIdx
  by_cases h : i.val < p.val
  · have h' : i.val + 1 < p.val + 1 := by omega
    simp [h, h']
  · have h' : ¬ (i.val + 1 < p.val + 1) := by omega
    simp [h, h']

theorem finSum_skipIdx {m : Nat} (p : Fin (m + 1)) (g : Fin (m + 1) → Int) (hgp : g p = 0) :
    finSum (fun k : Fin m => g (skipIdx p k)) = finSum g := by
  induction m with
  | zero =>
    have hp0 : p = 0 := Fin.ext (by omega)
    subst hp0
    rw [finSum_succ, finSum, finSum, hgp]; omega
  | succ m ih =>
    cases p using Fin.cases with
    | zero =>
      rw [finSum_succ g, hgp, Int.zero_add]
      apply finSum_congr; intro k; rw [skipIdx_zero]
    | succ p' =>
      rw [finSum_succ (fun k => g (skipIdx p'.succ k)), finSum_succ g, skipIdx_succ_zero]
      congr 1
      rw [← ih p' (fun i => g i.succ) hgp]
      apply finSum_congr; intro k; rw [skipIdx_succ_succ]

theorem det_zero (M : Matrix 0) : det M = 1 := rfl

theorem det_one (M : Matrix 1) : det M = M 0 0 := by
  simp [det, finSum, altSign]

theorem det_two (M : Matrix 2) : det M = M 0 0 * M 1 1 - M 0 1 * M 1 0 := by
  rw [det, finSum_succ, finSum_succ, finSum]
  have h1 : det (minor M 0) = M 1 1 := by rw [det_one]; rfl
  have h2 : det (minor M (Fin.succ 0)) = M 1 0 := by rw [det_one]; rfl
  rw [h1, h2]
  have hs0 : altSign (0 : Fin 2).val = 1 := rfl
  have hs1 : altSign (Fin.succ (0 : Fin 1)).val = -1 := rfl
  have hf1 : (Fin.succ (0 : Fin 1)) = 1 := rfl
  rw [hs0, hs1, hf1]
  grind

/-! ### Row Multilinearity and Alternating Law -/

theorem minor_setRow_zero {n : Nat} (M : Matrix (n + 1)) (v : Fin (n + 1) → Int) (j : Fin (n + 1)) :
    minor (setRow M 0 v) j = minor M j := by
  funext a b
  simp [minor, setRow, Fin.succ_ne_zero]

theorem minor_setRow_succ {n : Nat} (M : Matrix (n + 1)) (r : Fin n) (v : Fin (n + 1) → Int)
    (j : Fin (n + 1)) :
    minor (setRow M r.succ v) j = setRow (minor M j) r (fun b => v (skipIdx j b)) := by
  funext a b
  simp only [minor, setRow]
  by_cases h : a = r
  · subst h; simp
  · have h' : a.succ ≠ r.succ := fun heq => h (Fin.succ_inj.mp heq)
    simp [h, h']

theorem det_row_add {n : Nat} (M : Matrix n) (r : Fin n) (u v : Fin n → Int) :
    det (setRow M r (fun j => u j + v j)) = det (setRow M r u) + det (setRow M r v) := by
  induction n with
  | zero => exact Fin.elim0 r
  | succ n ih =>
    cases r using Fin.cases with
    | zero =>
      rw [det, det, det, ← finSum_add]
      apply finSum_congr
      intro j
      simp only [minor_setRow_zero, setRow, ↓reduceIte]
      grind
    | succ r' =>
      rw [det, det, det, ← finSum_add]
      apply finSum_congr
      intro j
      have hne : (0 : Fin (n + 1)) ≠ r'.succ := (Fin.succ_ne_zero r').symm
      simp only [minor_setRow_succ, setRow, hne, ↓reduceIte]
      rw [ih (minor M j) r' (fun b => u (skipIdx j b)) (fun b => v (skipIdx j b)), Int.mul_add]

theorem det_row_smul {n : Nat} (M : Matrix n) (r : Fin n) (c : Int) (u : Fin n → Int) :
    det (setRow M r (fun j => c * u j)) = c * det (setRow M r u) := by
  induction n with
  | zero => exact Fin.elim0 r
  | succ n ih =>
    cases r using Fin.cases with
    | zero =>
      rw [det, det, ← finSum_mul_left]
      apply finSum_congr
      intro j
      simp only [minor_setRow_zero, setRow, ↓reduceIte]
      grind
    | succ r' =>
      rw [det, det, ← finSum_mul_left]
      apply finSum_congr
      intro j
      have hne : (0 : Fin (n + 1)) ≠ r'.succ := (Fin.succ_ne_zero r').symm
      simp only [minor_setRow_succ, setRow, hne, ↓reduceIte]
      rw [ih (minor M j) r' (fun b => u (skipIdx j b))]
      grind

theorem det_row_zero {n : Nat} (M : Matrix n) (r : Fin n) :
    det (setRow M r (fun _ => 0)) = 0 := by
  have h := det_row_smul M r 0 (fun _ => 0)
  simp only [Int.zero_mul] at h
  exact h

/-- Key commutation of `skipIdx`: deleting `j` then `k` vs deleting `k'` then `j'`. -/
theorem skipIdx_comm_lt {n : Nat} (j : Fin (n + 2)) (k : Fin (n + 1)) (h : j.val ≤ k.val) :
    ∀ x : Fin n,
      skipIdx j (skipIdx k x) =
      skipIdx ⟨k.val + 1, by omega⟩ (skipIdx ⟨j.val, by omega⟩ x) := by
  intro x
  apply Fin.ext
  unfold skipIdx
  by_cases hx1 : x.val < j.val
  · have hx2 : x.val < k.val := by omega
    have hx3 : x.val < k.val + 1 := by omega
    simp [hx1, hx2, hx3]
  · by_cases hx2 : x.val < k.val
    · have hx3 : x.val + 1 < k.val + 1 := by omega
      simp [hx1, hx2, hx3]
    · have hx3 : ¬ (x.val + 1 < j.val) := by omega
      have hx4 : ¬ (x.val + 1 < k.val + 1) := by omega
      simp [hx1, hx2, hx3, hx4]

theorem skipIdx_comm_gt {n : Nat} (j : Fin (n + 2)) (k : Fin (n + 1)) (h : k.val < j.val) :
    ∀ x : Fin n,
      skipIdx j (skipIdx k x) =
      skipIdx ⟨k.val, by omega⟩ (skipIdx ⟨j.val - 1, by omega⟩ x) := by
  intro x
  apply Fin.ext
  unfold skipIdx
  by_cases hx1 : x.val < k.val
  · have hx2 : x.val < j.val - 1 := by omega
    have hx3 : x.val < j.val := by omega
    simp [hx1, hx2, hx3]
  · by_cases hx2 : x.val < j.val - 1
    · have hx3 : x.val + 1 < j.val := by omega
      simp [hx1, hx2, hx3]
    · have hx3 : ¬ (x.val + 1 < j.val) := by omega
      have hx4 : ¬ (x.val + 1 < k.val) := by omega
      simp [hx1, hx2, hx3, hx4]

/-- Swapping row 0 and row 1 negates `det`. -/
theorem det_swap_row01 {n : Nat} (M : Matrix (n + 2)) :
    det (fun i j => M (adjSwapFin 0 i) j) = -det M := by
  let M' : Matrix (n + 2) := fun i j => M (adjSwapFin 0 i) j
  have hM'_row0 : ∀ j, M' 0 j = M (Fin.succ 0) j := fun j => by
    change M (adjSwapFin 0 0) j = M (Fin.succ 0) j
    rw [adjSwapFin_zero_zero]
  have hM'_row1 : ∀ j, M' (Fin.succ 0) j = M 0 j := fun j => by
    change M (adjSwapFin 0 (Fin.succ 0)) j = M 0 j
    rw [adjSwapFin_zero_one]
  have hM'_rest : ∀ (i : Fin n) j, M' i.succ.succ j = M i.succ.succ j := fun i j => by
    change M (adjSwapFin 0 i.succ.succ) j = M i.succ.succ j
    rw [adjSwapFin_zero_succ_succ]
  let term (A : Matrix (n + 2)) (j : Fin (n + 2)) (k : Fin (n + 1)) : Int :=
    altSign j.val * altSign k.val * A 0 j * A (Fin.succ 0) (skipIdx j k) *
      det (minor (minor A j) k)
  have hExpand : ∀ A : Matrix (n + 2),
      det A = finSum (fun j => finSum (fun k => term A j k)) := by
    intro A
    rw [det]
    apply finSum_congr
    intro j
    rw [det, ← finSum_mul_left]
    apply finSum_congr
    intro k
    simp only [term, minor]
    grind
  let pairTerm (A : Matrix (n + 2)) (j l : Fin (n + 2)) : Int :=
    if h1 : j.val < l.val then
      altSign j.val * altSign (l.val - 1) * A 0 j * A (Fin.succ 0) l *
        det (minor (minor A j) ⟨l.val - 1, by have := l.isLt; omega⟩)
    else if h2 : l.val < j.val then
      altSign j.val * altSign l.val * A 0 j * A (Fin.succ 0) l *
        det (minor (minor A j) ⟨l.val, by have := j.isLt; omega⟩)
    else 0
  have hLift : ∀ (A : Matrix (n + 2)) (j : Fin (n + 2)),
      finSum (fun k : Fin (n + 1) => term A j k) = finSum (fun l : Fin (n + 2) => pairTerm A j l) := by
    intro A j
    have h0 : pairTerm A j j = 0 := by simp [pairTerm]
    rw [← finSum_skipIdx j (pairTerm A j) h0]
    apply finSum_congr
    intro k
    by_cases hkj : k.val < j.val
    · have hval : (skipIdx j k).val = k.val := skipIdx_val_lt j k hkj
      have hlt1 : ¬ (j.val < (skipIdx j k).val) := by omega
      have hlt2 : (skipIdx j k).val < j.val := by omega
      simp only [pairTerm, hlt1, hlt2, ↓reduceDIte, term]
      have hfin : (⟨(skipIdx j k).val, by have := j.isLt; omega⟩ : Fin (n + 1)) = k := Fin.ext hval
      rw [hfin, hval]
    · have hval : (skipIdx j k).val = k.val + 1 := skipIdx_val_ge j k hkj
      have hlt1 : j.val < (skipIdx j k).val := by omega
      simp only [pairTerm, hlt1, ↓reduceDIte, term]
      have hsub : (skipIdx j k).val - 1 = k.val := by omega
      have hfin : (⟨(skipIdx j k).val - 1, by have := (skipIdx j k).isLt; omega⟩ : Fin (n + 1)) = k :=
        Fin.ext hsub
      rw [hfin, hsub]
  have hAnti : ∀ j l : Fin (n + 2), pairTerm M' j l = -pairTerm M l j := by
    intro j l
    have hminorEq : ∀ (k1 k2 : Fin (n + 1)),
        (∀ x : Fin n, skipIdx j (skipIdx k1 x) = skipIdx l (skipIdx k2 x)) →
        minor (minor M' j) k1 = minor (minor M l) k2 := by
      intro k1 k2 hskip
      funext a b
      simp only [minor, hM'_rest, hskip b]
    by_cases h1 : j.val < l.val
    · have h2 : ¬ (l.val < j.val) := by omega
      simp only [pairTerm, h1, h2, ↓reduceDIte]
      have hmin : minor (minor M' j) ⟨l.val - 1, by have := l.isLt; omega⟩ =
                  minor (minor M l) ⟨j.val, by have := l.isLt; omega⟩ := by
        apply hminorEq
        intro x
        have hle : j.val ≤ (⟨l.val - 1, by have := l.isLt; omega⟩ : Fin (n + 1)).val := by
          dsimp only; omega
        have hcomm := skipIdx_comm_lt j ⟨l.val - 1, by have := l.isLt; omega⟩ hle x
        have hl' : (⟨(⟨l.val - 1, by have := l.isLt; omega⟩ : Fin (n + 1)).val + 1, by have := l.isLt; omega⟩ : Fin (n + 2)) = l :=
          Fin.ext (by dsimp only; omega)
        rw [hl'] at hcomm
        exact hcomm
      rw [hmin, hM'_row0, hM'_row1]
      have hsign : altSign (l.val - 1) = -altSign l.val := by
        have hl : l.val - 1 + 1 = l.val := by omega
        have hs := altSign_succ (l.val - 1)
        rw [hl] at hs
        omega
      rw [hsign]
      grind
    · by_cases h2 : l.val < j.val
      · simp only [pairTerm, h1, h2, ↓reduceDIte]
        have hmin : minor (minor M' j) ⟨l.val, by have := j.isLt; omega⟩ =
                    minor (minor M l) ⟨j.val - 1, by have := j.isLt; omega⟩ := by
          apply hminorEq
          intro x
          have hcomm := skipIdx_comm_gt j ⟨l.val, by have := j.isLt; omega⟩ h2 x
          have hl' : (⟨l.val, by have := l.isLt; omega⟩ : Fin (n + 2)) = l := Fin.ext rfl
          rw [hl'] at hcomm
          exact hcomm
        rw [hmin, hM'_row0, hM'_row1]
        have hsign : altSign j.val = -altSign (j.val - 1) := by
          have hj : j.val - 1 + 1 = j.val := by omega
          have hs := altSign_succ (j.val - 1)
          rw [hj] at hs
          exact hs
        rw [hsign]
        grind
      · simp [pairTerm, h1, h2]
  change det M' = -det M
  rw [hExpand M', hExpand M]
  simp only [hLift]
  rw [finSum_comm (fun j l => pairTerm M' j l), ← finSum_neg]
  apply finSum_congr; intro l
  rw [← finSum_neg]
  apply finSum_congr; intro j
  exact hAnti j l

/-- Swapping any two adjacent rows negates `det`. -/
theorem det_row_adj_swap {n : Nat} (M : Matrix (n + 1)) (k : Fin n) :
    det (fun i j => M (adjSwapFin k i) j) = -det M := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    cases k using Fin.cases with
    | zero => exact det_swap_row01 M
    | succ k' =>
      rw [det, det, ← finSum_neg]
      apply finSum_congr
      intro j
      rw [adjSwapFin_succ_zero]
      have hmin : minor (fun i c => M (adjSwapFin k'.succ i) c) j =
          fun a b => minor M j (adjSwapFin k' a) b := by
        funext a b
        simp [minor, adjSwapFin_succ_succ]
      rw [hmin, ih (minor M j) k', Int.mul_neg]

/-! ### Column Multilinearity and Adjacent Swap Law -/

theorem minor_setCol_ne {n : Nat} (M : Matrix (n + 1)) (c j : Fin (n + 1)) (hj : j ≠ c)
    (w : Fin (n + 1) → Int) :
    minor (setCol M c w) j =
      setCol (minor M j)
        (if h : c.val < j.val then ⟨c.val, by have := j.isLt; omega⟩
         else ⟨c.val - 1, by have := c.isLt; omega⟩)
        (fun a => w a.succ) := by
  have hcj_ne : c.val ≠ j.val := fun h => hj (Fin.ext h.symm)
  funext a b
  simp only [minor, setCol]
  by_cases hcj : c.val < j.val
  · simp only [hcj, ↓reduceDIte]
    have hiff : skipIdx j b = c ↔ b = ⟨c.val, by have := j.isLt; omega⟩ := by
      constructor
      · intro h; apply Fin.ext
        have hv := congrArg Fin.val h
        rw [skipIdx_val] at hv
        split at hv <;> dsimp only <;> omega
      · intro h; subst h; apply Fin.ext; simp [skipIdx_val, hcj]
    by_cases hb : b = ⟨c.val, by have := j.isLt; omega⟩
    · have hs : skipIdx j b = c := hiff.mpr hb
      rw [hs, hb]; simp
    · have hs : skipIdx j b ≠ c := fun h => hb (hiff.mp h)
      simp only [hb, hs, ↓reduceIte]
  · simp only [hcj, ↓reduceDIte]
    have hiff : skipIdx j b = c ↔ b = ⟨c.val - 1, by have := c.isLt; omega⟩ := by
      constructor
      · intro h; apply Fin.ext
        have hv := congrArg Fin.val h
        rw [skipIdx_val] at hv
        split at hv <;> dsimp only <;> omega
      · intro h; subst h; apply Fin.ext
        have hnot : ¬ (c.val - 1 < j.val) := by omega
        simp [skipIdx_val, hnot]; omega
    by_cases hb : b = ⟨c.val - 1, by have := c.isLt; omega⟩
    · have hs : skipIdx j b = c := hiff.mpr hb
      rw [hs, hb]; simp
    · have hs : skipIdx j b ≠ c := fun h => hb (hiff.mp h)
      simp only [hb, hs, ↓reduceIte]

theorem minor_setCol_eq {n : Nat} (M : Matrix (n + 1)) (j : Fin (n + 1))
    (w : Fin (n + 1) → Int) :
    minor (setCol M j w) j = minor M j := by
  funext a b
  simp only [minor, setCol]
  have hne : skipIdx j b ≠ j := by
    intro heq
    have hv := congrArg Fin.val heq
    rw [skipIdx_val] at hv
    split at hv <;> omega
  simp [hne]

theorem det_col_add {n : Nat} (M : Matrix n) (c : Fin n) (u v : Fin n → Int) :
    det (setCol M c (fun i => u i + v i)) = det (setCol M c u) + det (setCol M c v) := by
  induction n with
  | zero => exact Fin.elim0 c
  | succ n ih =>
    rw [det, det, det, ← finSum_add]
    apply finSum_congr
    intro j
    by_cases hj : j = c
    · subst hj
      simp only [setCol, ↓reduceIte, minor_setCol_eq]
      grind
    · simp only [setCol, hj, ↓reduceIte, minor_setCol_ne M c j hj]
      rw [ih (minor M j), Int.mul_add]

theorem det_col_smul {n : Nat} (M : Matrix n) (c : Fin n) (s : Int) (u : Fin n → Int) :
    det (setCol M c (fun i => s * u i)) = s * det (setCol M c u) := by
  induction n with
  | zero => exact Fin.elim0 c
  | succ n ih =>
    rw [det, det, ← finSum_mul_left]
    apply finSum_congr
    intro j
    by_cases hj : j = c
    · subst hj
      simp only [setCol, ↓reduceIte, minor_setCol_eq]
      grind
    · simp only [setCol, hj, ↓reduceIte, minor_setCol_ne M c j hj]
      rw [ih (minor M j)]
      grind

theorem det_col_zero {n : Nat} (M : Matrix n) (c : Fin n) :
    det (setCol M c (fun _ => 0)) = 0 := by
  have h := det_col_smul M c 0 (fun _ => 0)
  simp only [Int.zero_mul] at h
  exact h

/-- Helper: value of `adjSwapFin k (skipIdx p b)`. -/
theorem adjSwapFin_skipIdx_eq {n : Nat} (k : Fin (n + 1)) (j : Fin (n + 2))
    (hj1 : j.val = k.val) (b : Fin (n + 1)) :
    adjSwapFin k (skipIdx (adjSwapFin k j) b) = skipIdx j b := by
  apply Fin.ext; simp only [adjSwapFin_val, skipIdx_val]; grind

theorem adjSwapFin_skipIdx_eq2 {n : Nat} (k : Fin (n + 1)) (j : Fin (n + 2))
    (hj2 : j.val = k.val + 1) (b : Fin (n + 1)) :
    adjSwapFin k (skipIdx (adjSwapFin k j) b) = skipIdx j b := by
  apply Fin.ext; simp only [adjSwapFin_val, skipIdx_val]; grind

theorem adjSwapFin_skipIdx_lt {n : Nat} (k : Fin (n + 1)) (j : Fin (n + 2))
    (hjk : j.val < k.val) (b : Fin (n + 1)) :
    adjSwapFin k (skipIdx j b) = skipIdx j (adjSwapFin ⟨k.val - 1, by have := k.isLt; omega⟩ b) := by
  apply Fin.ext; simp only [adjSwapFin_val, skipIdx_val]; grind

theorem adjSwapFin_skipIdx_gt {n : Nat} (k : Fin (n + 1)) (j : Fin (n + 2))
    (hkj : k.val + 1 < j.val) (b : Fin (n + 1)) :
    adjSwapFin k (skipIdx j b) = skipIdx j (adjSwapFin ⟨k.val, by have := k.isLt; omega⟩ b) := by
  apply Fin.ext; simp only [adjSwapFin_val, skipIdx_val]; grind

/-- Swapping any two adjacent columns negates `det`. -/
theorem det_col_adj_swap {n : Nat} (M : Matrix (n + 1)) (k : Fin n) :
    det (fun i j => M i (adjSwapFin k j)) = -det M := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    let M' : Matrix (n + 2) := fun i j => M i (adjSwapFin k j)
    change det M' = -det M
    rw [det, ← finSum_swap_adj k, det, ← finSum_neg]
    apply finSum_congr
    intro j
    have h0 : M' 0 (adjSwapFin k j) = M 0 j := by simp [M', adjSwapFin_invol]
    rw [h0]
    by_cases hj1 : j.val = k.val
    · have hval : (adjSwapFin k j).val = k.val + 1 := by simp [adjSwapFin, hj1]
      have hsign : altSign (adjSwapFin k j).val = -altSign j.val := by
        rw [hval, ← hj1, altSign_succ]
      have hmin : minor M' (adjSwapFin k j) = minor M j := by
        funext a b; simp only [minor, M', adjSwapFin_skipIdx_eq k j hj1 b]
      rw [hsign, hmin]; grind
    · by_cases hj2 : j.val = k.val + 1
      · have hval : (adjSwapFin k j).val = k.val := by simp [adjSwapFin, hj2]
        have hsign : altSign (adjSwapFin k j).val = -altSign j.val := by
          rw [hval, hj2, altSign_succ]; omega
        have hmin : minor M' (adjSwapFin k j) = minor M j := by
          funext a b; simp only [minor, M', adjSwapFin_skipIdx_eq2 k j hj2 b]
        rw [hsign, hmin]; grind
      · have hjfix : adjSwapFin k j = j := by
          apply Fin.ext; simp [adjSwapFin, hj1, hj2]
        rw [hjfix]
        by_cases hjk : j.val < k.val
        · have hk' : k.val - 1 < n := by have := k.isLt; omega
          have hmin : minor M' j = fun a b => minor M j a (adjSwapFin ⟨k.val - 1, hk'⟩ b) := by
            funext a b; simp only [minor, M', adjSwapFin_skipIdx_lt k j hjk b]
          rw [hmin, ih (minor M j) ⟨k.val - 1, hk'⟩, Int.mul_neg]
        · have hkj : k.val + 1 < j.val := by omega
          have hk' : k.val < n := by have := k.isLt; omega
          have hmin : minor M' j = fun a b => minor M j a (adjSwapFin ⟨k.val, hk'⟩ b) := by
            funext a b; simp only [minor, M', adjSwapFin_skipIdx_gt k j hkj b]
          rw [hmin, ih (minor M j) ⟨k.val, hk'⟩, Int.mul_neg]

/-! ### General Transpositions, Alternating Zero, Shears, and Permutation Congruence -/

theorem swapFin_comm {n : Nat} (p q : Fin n) : swapFin p q = swapFin q p := by
  funext i
  unfold swapFin
  by_cases h1 : i = p
  · subst h1; by_cases h2 : i = q <;> simp [h2]
  · by_cases h2 : i = q <;> simp [h1, h2]

theorem swapFin_invol {n : Nat} (p q i : Fin n) : swapFin p q (swapFin p q i) = i := by
  unfold swapFin
  by_cases h1 : i = p
  · subst h1; by_cases h2 : i = q <;> simp [h2]
  · by_cases h2 : i = q
    · subst h2; simp [h1]
    · simp [h1, h2]

/-- Generic lemma: any function on tuples that negates under adjacent swaps negates under ANY swap `p ≠ q`. -/
theorem swap_neg_of_adj_swap {α : Type} {n : Nat}
    (F : (Fin n → α) → Int)
    (hadj : ∀ (v : Fin n → α) (k : Nat) (hk : k + 1 < n),
      F (fun i => v (swapFin ⟨k, by omega⟩ ⟨k + 1, hk⟩ i)) = -F v) :
    ∀ (v : Fin n → α) (p q : Fin n), p ≠ q →
      F (fun i => v (swapFin p q i)) = -F v := by
  have hAdjFin : ∀ (w : Fin n → α) (a b : Fin n), b.val = a.val + 1 →
      F (fun i => w (swapFin a b i)) = -F w := by
    intro w a b hab
    have hk : a.val + 1 < n := by have := b.isLt; omega
    have ha : a = ⟨a.val, by omega⟩ := Fin.ext rfl
    have hb : b = ⟨a.val + 1, hk⟩ := Fin.ext hab
    have hfn : (fun i => w (swapFin a b i)) =
               (fun i => w (swapFin ⟨a.val, by omega⟩ ⟨a.val + 1, hk⟩ i)) := by
      funext i; rw [← ha, ← hb]
    rw [hfn]
    exact hadj w a.val hk
  have hlt : ∀ (d : Nat) (v : Fin n → α) (p q : Fin n),
      p.val < q.val → q.val - p.val - 1 = d →
      F (fun i => v (swapFin p q i)) = -F v := by
    intro d
    induction d with
    | zero =>
      intro v p q hlt hd
      exact hAdjFin v p q (by omega)
    | succ d ih =>
      intro v p q hlt hd
      have hqlt := q.isLt
      let m : Fin n := ⟨q.val - 1, by omega⟩
      have hmval : m.val = q.val - 1 := rfl
      have hpm : p ≠ m := fun h => by have := congrArg Fin.val h; omega
      have hpq : p ≠ q := fun h => by have := congrArg Fin.val h; omega
      have hmq : m ≠ q := fun h => by have := congrArg Fin.val h; omega
      have hcomp : ∀ i : Fin n,
          swapFin p q i = swapFin m q (swapFin p m (swapFin m q i)) := by
        intro i
        unfold swapFin
        by_cases hi1 : i = p
        · subst hi1; simp [hpm, hpq]
        · by_cases hi2 : i = q
          · subst hi2; simp [hpm, hpq, hpm.symm, hpq.symm, hmq.symm]
          · by_cases hi3 : i = m
            · subst hi3; simp [hmq, hpm.symm, hpq.symm, hmq.symm]
            · simp [hi1, hi2, hi3]
      let w1 : Fin n → α := fun k => v (swapFin m q k)
      let w2 : Fin n → α := fun j => w1 (swapFin p m j)
      have hstep : (fun i => v (swapFin p q i)) = (fun i => w2 (swapFin m q i)) := by
        funext i; exact congrArg v (hcomp i)
      rw [hstep, hAdjFin w2 m q (by omega)]
      have hstep2 : F w2 = -F w1 := ih w1 p m (by omega) (by omega)
      have hstep3 : F w1 = -F v := hAdjFin v m q (by omega)
      omega
  intro v p q hne
  by_cases h : p.val < q.val
  · exact hlt (q.val - p.val - 1) v p q h rfl
  · have h2 : q.val < p.val := by
      have : p.val ≠ q.val := fun heq => hne (Fin.ext heq)
      omega
    rw [swapFin_comm]
    exact hlt (p.val - q.val - 1) v q p h2 rfl

theorem det_row_swap {n : Nat} (M : Matrix n) (p q : Fin n) (hne : p ≠ q) :
    det (fun i j => M (swapFin p q i) j) = -det M := by
  exact swap_neg_of_adj_swap (F := fun R : Matrix n => det R) (by
    intro R k hk
    cases n with
    | zero => omega
    | succ m =>
      have h := det_row_adj_swap R ⟨k, by omega⟩
      have heq : (fun i j => R (swapFin ⟨k, by omega⟩ ⟨k + 1, hk⟩ i) j) =
                 (fun i j => R (adjSwapFin ⟨k, by omega⟩ i) j) := by
        funext i j; congr 1; apply Fin.ext
        unfold swapFin adjSwapFin
        by_cases h1 : i.val = k
        · have hi : i = ⟨k, by omega⟩ := Fin.ext h1
          simp [hi]
        · have hi : i ≠ ⟨k, by omega⟩ := fun he => h1 (congrArg Fin.val he)
          by_cases h2 : i.val = k + 1
          · have hi2 : i = ⟨k + 1, hk⟩ := Fin.ext h2
            simp [hi2]
          · have hi2 : i ≠ ⟨k + 1, hk⟩ := fun he => h2 (congrArg Fin.val he)
            simp [hi, hi2, h1, h2]
      rw [heq]; exact h) M p q hne

theorem det_col_swap {n : Nat} (M : Matrix n) (p q : Fin n) (hne : p ≠ q) :
    det (fun i j => M i (swapFin p q j)) = -det M := by
  let colView (M : Matrix n) : Fin n → (Fin n → Int) := fun j i => M i j
  let ofCols (C : Fin n → (Fin n → Int)) : Matrix n := fun i j => C j i
  exact swap_neg_of_adj_swap (F := fun C : Fin n → (Fin n → Int) => det (ofCols C)) (by
    intro C k hk
    cases n with
    | zero => omega
    | succ m =>
      have h0 := det_col_adj_swap (ofCols C) ⟨k, by omega⟩
      have heq : ofCols (fun j => C (swapFin ⟨k, by omega⟩ ⟨k + 1, hk⟩ j)) =
                 (fun i j => ofCols C i (adjSwapFin ⟨k, by omega⟩ j)) := by
        funext i j; simp only [ofCols]; congr 1; apply Fin.ext
        unfold swapFin adjSwapFin
        by_cases h1 : j.val = k
        · have hj : j = ⟨k, by omega⟩ := Fin.ext h1
          simp [hj]
        · have hj : j ≠ ⟨k, by omega⟩ := fun he => h1 (congrArg Fin.val he)
          by_cases h2 : j.val = k + 1
          · have hj2 : j = ⟨k + 1, hk⟩ := Fin.ext h2
            simp [hj2]
          · have hj2 : j ≠ ⟨k + 1, hk⟩ := fun he => h2 (congrArg Fin.val he)
            simp [hj, hj2, h1, h2]
      rw [heq]; exact h0) (colView M) p q hne

/-- Simultaneous row+column swap preserves `det`! -/
theorem det_swap_cong {n : Nat} (M : Matrix n) (p q : Fin n) :
    det (fun i j => M (swapFin p q i) (swapFin p q j)) = det M := by
  by_cases h : p = q
  · subst h
    have hs : ∀ i, swapFin p p i = i := fun i => by unfold swapFin; split <;> simp_all
    simp [hs]
  · rw [det_row_swap (fun i j => M i (swapFin p q j)) p q h, det_col_swap M p q h]
    omega

/-- Equal rows imply `det = 0`. -/
theorem det_row_eq_zero {n : Nat} (M : Matrix n) (p q : Fin n) (hne : p ≠ q)
    (heq : ∀ j, M p j = M q j) : det M = 0 := by
  have hd := det_row_swap M p q hne
  have hsame : (fun i j => M (swapFin p q i) j) = M := by
    funext i j
    unfold swapFin
    by_cases h1 : i = p
    · subst h1; simp [heq j]
    · by_cases h2 : i = q
      · subst h2; simp [h1, (heq j).symm]
      · simp [h1, h2]
  rw [hsame] at hd
  omega

/-- Equal columns imply `det = 0`. -/
theorem det_col_eq_zero {n : Nat} (M : Matrix n) (p q : Fin n) (hne : p ≠ q)
    (heq : ∀ i, M i p = M i q) : det M = 0 := by
  have hd := det_col_swap M p q hne
  have hsame : (fun i j => M i (swapFin p q j)) = M := by
    funext i j
    unfold swapFin
    by_cases h1 : j = p
    · subst h1; simp [heq i]
    · by_cases h2 : j = q
      · subst h2; simp [h1, (heq i).symm]
      · simp [h1, h2]
  rw [hsame] at hd
  omega

/-- Elementary row shear (`row p += c * row q`, `p ≠ q`) preserves `det`. -/
theorem det_row_shear {n : Nat} (M : Matrix n) (p q : Fin n) (hne : p ≠ q) (c : Int) :
    det (setRow M p (fun j => M p j + c * M q j)) = det M := by
  rw [det_row_add, det_row_smul]
  have h1 : setRow M p (fun j => M p j) = M := by
    funext i j; unfold setRow; split <;> simp_all
  have h2 : det (setRow M p (fun j => M q j)) = 0 := by
    apply det_row_eq_zero _ p q hne
    intro j; simp [setRow, hne.symm]
  rw [h1, h2]
  omega

/-- Elementary column shear (`col p += c * col q`, `p ≠ q`) preserves `det`. -/
theorem det_col_shear {n : Nat} (M : Matrix n) (p q : Fin n) (hne : p ≠ q) (c : Int) :
    det (setCol M p (fun i => M i p + c * M i q)) = det M := by
  rw [det_col_add, det_col_smul]
  have h1 : setCol M p (fun i => M i p) = M := by
    funext i j; unfold setCol; split <;> simp_all
  have h2 : det (setCol M p (fun i => M i q)) = 0 := by
    apply det_col_eq_zero _ p q hne
    intro i; simp [setCol, hne.symm]
  rw [h1, h2]
  omega

/-- Adding a linear combination of OTHER rows `k ≠ p` to row `p` preserves `det`. -/
theorem det_row_add_lincomb {n : Nat} (M : Matrix n) (p : Fin n) (coeff : Fin n → Int)
    (hp : coeff p = 0) :
    det (setRow M p (fun j => M p j + finSum (fun k => coeff k * M k j))) = det M := by
  suffices h : ∀ (m : Nat) (hm : m ≤ n),
      det (setRow M p (fun j => M p j +
        finSum (fun k : Fin m => coeff ⟨k.val, by omega⟩ * M ⟨k.val, by omega⟩ j))) = det M by
    exact h n (Nat.le_refl n)
  intro m hm
  induction m with
  | zero =>
    have h0 : setRow M p (fun j => M p j + finSum (fun k : Fin 0 => coeff ⟨k.val, by omega⟩ * M ⟨k.val, by omega⟩ j)) = M := by
      funext i j; unfold setRow; split
      · subst_vars; simp [finSum]
      · rfl
    rw [h0]
  | succ m ih =>
    let kLast : Fin n := ⟨m, by omega⟩
    let prevM : Matrix n := setRow M p (fun j => M p j +
        finSum (fun k : Fin m => coeff ⟨k.val, by omega⟩ * M ⟨k.val, by omega⟩ j))
    by_cases hpk : p = kLast
    · have hc0 : coeff kLast = 0 := by rw [← hpk]; exact hp
      have heq : setRow M p (fun j => M p j +
          finSum (fun k : Fin (m + 1) => coeff ⟨k.val, by omega⟩ * M ⟨k.val, by omega⟩ j)) = prevM := by
        funext i j
        simp only [prevM, setRow]
        split
        · rw [finSum_split_last]
          change M p j + (finSum (fun k : Fin m => coeff ⟨k.val, by omega⟩ * M ⟨k.val, by omega⟩ j) +
            coeff kLast * M kLast j) = _
          rw [hc0]; omega
        · rfl
      rw [heq]
      exact ih (by omega)
    · have heq : setRow M p (fun j => M p j +
          finSum (fun k : Fin (m + 1) => coeff ⟨k.val, by omega⟩ * M ⟨k.val, by omega⟩ j)) =
          setRow prevM p (fun j => prevM p j + coeff kLast * prevM kLast j) := by
        funext i j
        simp only [prevM, setRow]
        by_cases hip : i = p
        · subst hip
          simp only [↓reduceIte, Ne.symm hpk]
          rw [finSum_split_last]
          change M i j + (finSum (fun k : Fin m => coeff ⟨k.val, by omega⟩ * M ⟨k.val, by omega⟩ j) +
            coeff kLast * M kLast j) = _
          omega
        · simp [hip]
      rw [heq, det_row_shear prevM p kLast hpk (coeff kLast)]
      exact ih (by omega)

/-- Adding a linear combination of OTHER columns `k ≠ p` to column `p` preserves `det`. -/
theorem det_col_add_lincomb {n : Nat} (M : Matrix n) (p : Fin n) (coeff : Fin n → Int)
    (hp : coeff p = 0) :
    det (setCol M p (fun i => M i p + finSum (fun k => coeff k * M i k))) = det M := by
  suffices h : ∀ (m : Nat) (hm : m ≤ n),
      det (setCol M p (fun i => M i p +
        finSum (fun k : Fin m => coeff ⟨k.val, by omega⟩ * M i ⟨k.val, by omega⟩))) = det M by
    exact h n (Nat.le_refl n)
  intro m hm
  induction m with
  | zero =>
    have h0 : setCol M p (fun i => M i p + finSum (fun k : Fin 0 => coeff ⟨k.val, by omega⟩ * M i ⟨k.val, by omega⟩)) = M := by
      funext i j; unfold setCol; split
      · subst_vars; simp [finSum]
      · rfl
    rw [h0]
  | succ m ih =>
    let kLast : Fin n := ⟨m, by omega⟩
    let prevM : Matrix n := setCol M p (fun i => M i p +
        finSum (fun k : Fin m => coeff ⟨k.val, by omega⟩ * M i ⟨k.val, by omega⟩))
    by_cases hpk : p = kLast
    · have hc0 : coeff kLast = 0 := by rw [← hpk]; exact hp
      have heq : setCol M p (fun i => M i p +
          finSum (fun k : Fin (m + 1) => coeff ⟨k.val, by omega⟩ * M i ⟨k.val, by omega⟩)) = prevM := by
        funext i j
        simp only [prevM, setCol]
        split
        · rw [finSum_split_last]
          change M i p + (finSum (fun k : Fin m => coeff ⟨k.val, by omega⟩ * M i ⟨k.val, by omega⟩) +
            coeff kLast * M i kLast) = _
          rw [hc0]; omega
        · rfl
      rw [heq]
      exact ih (by omega)
    · have heq : setCol M p (fun i => M i p +
          finSum (fun k : Fin (m + 1) => coeff ⟨k.val, by omega⟩ * M i ⟨k.val, by omega⟩)) =
          setCol prevM p (fun i => prevM i p + coeff kLast * prevM i kLast) := by
        funext i j
        simp only [prevM, setCol]
        by_cases hjp : j = p
        · subst hjp
          simp only [↓reduceIte, Ne.symm hpk]
          rw [finSum_split_last]
          change M i j + (finSum (fun k : Fin m => coeff ⟨k.val, by omega⟩ * M i ⟨k.val, by omega⟩) +
            coeff kLast * M i kLast) = _
          omega
        · simp [hjp]
      rw [heq, det_col_shear prevM p kLast hpk (coeff kLast)]
      exact ih (by omega)

/-! ## Part 2A: Unit-Triangular LDU, Permutation Congruence, and Block-LDU Theorems -/

/-- Left multiplication by any unit lower-triangular matrix preserves `det`. -/
theorem det_unit_lower_mul {n : Nat} (L M : Matrix n) (hL : IsUnitLower L) :
    det (matMul L M) = det M := by
  let hybrid (k : Nat) : Matrix n :=
    fun i j => if i.val < k then M i j else matMul L M i j
  have hDown : ∀ (d : Nat) (hd : d ≤ n), det (hybrid (n - d)) = det (hybrid n) := by
    intro d
    induction d with
    | zero => intro _; simp [hybrid]
    | succ d ih =>
      intro hd
      let p : Fin n := ⟨n - d - 1, by omega⟩
      let coeff : Fin n → Int := fun k => if k.val < p.val then L p k else 0
      have hcp : coeff p = 0 := by simp [coeff]
      have hEq : hybrid (n - (d + 1)) =
          setRow (hybrid (n - d)) p (fun j => hybrid (n - d) p j +
            finSum (fun k => coeff k * hybrid (n - d) k j)) := by
        funext i j
        by_cases hip : i = p
        · subst hip
          have hlt1 : ¬ (p.val < n - (d + 1)) := by simp [p]; omega
          have hlt2 : p.val < n - d := by simp [p]; omega
          simp only [hybrid, setRow, ↓reduceIte, hlt1, hlt2]
          unfold matMul
          -- Split finSum (L p k * M k j) into k = p plus k ≠ p!
          have hsplit : finSum (fun k => L p k * M k j) =
              M p j + finSum (fun k => coeff k * (if k.val < n - d then M k j else matMul L M k j)) := by
            have h1 : M p j = finSum (fun k => if k = p then L p k * M k j else 0) := by
              rw [finSum_single p _ (fun k hk => by simp [hk])]
              simp [hL.1 p]
            rw [h1, ← finSum_add]
            apply finSum_congr
            intro k
            by_cases hkp : k = p
            · subst hkp; simp [coeff]
            · have hne : k.val ≠ p.val := fun h => hkp (Fin.ext h)
              by_cases hkl : k.val < p.val
              · have hknd : k.val < n - d := by simp [p] at hkl; omega
                simp [coeff, hkp, hkl, hknd]
              · have hgt : p.val < k.val := by omega
                simp [coeff, hkp, hkl, hL.2 p k hgt]
          exact hsplit
        · have hne : i.val ≠ n - d - 1 := fun h => hip (Fin.ext h)
          have hiff : (i.val < n - (d + 1)) ↔ (i.val < n - d) := by omega
          simp only [hybrid, setRow, hip, ↓reduceIte]
          by_cases h1 : i.val < n - (d + 1)
          · have h2 : i.val < n - d := hiff.mp h1
            simp [h1, h2]
          · have h2 : ¬ (i.val < n - d) := fun h => h1 (hiff.mpr h)
            simp [h1, h2]
      rw [hEq, det_row_add_lincomb (hybrid (n - d)) p coeff hcp, ih (by omega)]
  have h0 : hybrid 0 = matMul L M := by funext i j; simp [hybrid]
  have hn : hybrid n = M := by funext i j; simp [hybrid, i.isLt]
  have hres := hDown n (Nat.le_refl n)
  rw [Nat.sub_self, h0, hn] at hres
  exact hres

/-- Right multiplication by any unit upper-triangular matrix preserves `det`. -/
theorem det_mul_unit_upper {n : Nat} (M U : Matrix n) (hU : IsUnitUpper U) :
    det (matMul M U) = det M := by
  let hybrid (k : Nat) : Matrix n :=
    fun i j => if j.val < k then M i j else matMul M U i j
  have hDown : ∀ (d : Nat) (hd : d ≤ n), det (hybrid (n - d)) = det (hybrid n) := by
    intro d
    induction d with
    | zero => intro _; simp [hybrid]
    | succ d ih =>
      intro hd
      let p : Fin n := ⟨n - d - 1, by omega⟩
      let coeff : Fin n → Int := fun k => if k.val < p.val then U k p else 0
      have hcp : coeff p = 0 := by simp [coeff]
      have hEq : hybrid (n - (d + 1)) =
          setCol (hybrid (n - d)) p (fun i => hybrid (n - d) i p +
            finSum (fun k => coeff k * hybrid (n - d) i k)) := by
        funext i j
        by_cases hjp : j = p
        · subst hjp
          have hlt1 : ¬ (p.val < n - (d + 1)) := by simp [p]; omega
          have hlt2 : p.val < n - d := by simp [p]; omega
          simp only [hybrid, setCol, ↓reduceIte, hlt1, hlt2]
          unfold matMul
          have hsplit : finSum (fun k => M i k * U k p) =
              M i p + finSum (fun k => coeff k * (if k.val < n - d then M i k else matMul M U i k)) := by
            have h1 : M i p = finSum (fun k => if k = p then M i k * U k p else 0) := by
              rw [finSum_single p _ (fun k hk => by simp [hk])]
              simp [hU.1 p]
            rw [h1, ← finSum_add]
            apply finSum_congr
            intro k
            by_cases hkp : k = p
            · subst hkp; simp [coeff]
            · have hne : k.val ≠ p.val := fun h => hkp (Fin.ext h)
              by_cases hkl : k.val < p.val
              · have hknd : k.val < n - d := by simp [p] at hkl; omega
                simp [coeff, hkp, hkl, hknd, Int.mul_comm]
              · have hgt : p.val < k.val := by omega
                simp [coeff, hkp, hkl, hU.2 k p hgt]
          exact hsplit
        · have hne : j.val ≠ n - d - 1 := fun h => hjp (Fin.ext h)
          have hiff : (j.val < n - (d + 1)) ↔ (j.val < n - d) := by omega
          simp only [hybrid, setCol, hjp, ↓reduceIte]
          by_cases h1 : j.val < n - (d + 1)
          · have h2 : j.val < n - d := hiff.mp h1
            simp [h1, h2]
          · have h2 : ¬ (j.val < n - d) := fun h => h1 (hiff.mpr h)
            simp [h1, h2]
      rw [hEq, det_col_add_lincomb (hybrid (n - d)) p coeff hcp, ih (by omega)]
  have h0 : hybrid 0 = matMul M U := by funext i j; simp [hybrid]
  have hn : hybrid n = M := by funext i j; simp [hybrid, j.isLt]
  have hres := hDown n (Nat.le_refl n)
  rw [Nat.sub_self, h0, hn] at hres
  exact hres

/-- Determinant of a diagonal matrix equals the product of its diagonal entries. -/
theorem det_diag {n : Nat} (d : Fin n → Int) : det (diagMat d) = finProd d := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [det, finProd]
    rw [finSum_single 0 _ (fun j hj => by simp [diagMat, hj.symm])]
    have hmin : minor (diagMat d) 0 = diagMat (fun i => d i.succ) := by
      funext a b
      simp only [minor, diagMat, skipIdx_zero]
      by_cases h : a = b
      · subst h; simp
      · have h' : a.succ ≠ b.succ := fun heq => h (Fin.succ_inj.mp heq)
        simp [h, h']
    simp [diagMat, hmin, ih]

/-- Exact LDU Determinant Theorem: `det (L * D * U) = ∏ d_i`. -/
theorem det_ldu {n : Nat} (L U : Matrix n) (d : Fin n → Int)
    (hL : IsUnitLower L) (hU : IsUnitUpper U) :
    det (matMul (matMul L (diagMat d)) U) = finProd d := by
  rw [det_mul_unit_upper _ U hU, det_unit_lower_mul L _ hL, det_diag]

theorem isUnitUpper_trans_of_isUnitLower {n : Nat} {L : Matrix n} (hL : IsUnitLower L) :
    IsUnitUpper (matTrans L) :=
  ⟨hL.1, fun i j hij => hL.2 j i hij⟩

/-- Symmetric LDU Congruence Invariance: `det (L * M * L^T) = det M` for any unit lower-triangular `L`. -/
theorem det_unit_lower_cong {n : Nat} (L M : Matrix n) (hL : IsUnitLower L) :
    det (matMul (matMul L M) (matTrans L)) = det M := by
  rw [det_mul_unit_upper _ _ (isUnitUpper_trans_of_isUnitLower hL), det_unit_lower_mul L M hL]

/-- Arbitrary Permutation Congruence Invariance: for ANY bijection `π : Fin n → Fin n`,
    `det (fun i j => M (π i) (π j)) = det M`. -/
theorem det_perm_cong {n : Nat} (M : Matrix n) (π πInv : Fin n → Fin n)
    (hL : ∀ i, πInv (π i) = i) (hR : ∀ i, π (πInv i) = i) :
    det (fun i j => M (π i) (π j)) = det M := by
  suffices h : ∀ (d : Nat) (hd : d ≤ n) (f fInv : Fin n → Fin n),
      (∀ i, fInv (f i) = i) → (∀ i, f (fInv i) = i) →
      (∀ i : Fin n, i.val < n - d → f i = i) →
      det (fun i j => M (f i) (f j)) = det M by
    exact h n (Nat.le_refl n) π πInv hL hR (fun i hi => by omega)
  intro d
  induction d with
  | zero =>
    intro _ f _ _ _ hfix
    have hf : ∀ i, f i = i := fun i => hfix i (by have := i.isLt; omega)
    have hEq : (fun i j => M (f i) (f j)) = M := by funext i j; rw [hf i, hf j]
    rw [hEq]
  | succ d ih =>
    intro hd f fInv hfL hfR hfix
    let k : Fin n := ⟨n - (d + 1), by omega⟩
    let p : Fin n := fInv k
    let g : Fin n → Fin n := fun i => f (swapFin k p i)
    let gInv : Fin n → Fin n := fun i => swapFin k p (fInv i)
    have hgL : ∀ i, gInv (g i) = i := fun i => by simp [g, gInv, hfL, swapFin_invol]
    have hgR : ∀ i, g (gInv i) = i := fun i => by simp [g, gInv, swapFin_invol, hfR]
    have hpge : ¬ (p.val < n - (d + 1)) := by
      intro hlt
      have hfp := hfix p hlt
      have hfp2 : f p = k := hfR k
      have hpk : p = k := by rw [← hfp, hfp2]
      have hv := congrArg Fin.val hpk
      simp [k] at hv; omega
    have hgfix : ∀ i : Fin n, i.val < n - d → g i = i := by
      intro i hi
      by_cases hik : i = k
      · subst hik
        simp only [g, swapFin, ↓reduceIte]
        exact hfR k
      · have hilt : i.val < n - (d + 1) := by
          have : i.val ≠ n - (d + 1) := fun h => hik (Fin.ext h)
          omega
        have hip : i ≠ p := fun h => hpge (h ▸ hilt)
        simp only [g, swapFin, hik, hip, ↓reduceIte]
        exact hfix i hilt
    have hswap := det_swap_cong (fun i j => M (f i) (f j)) k p
    rw [← hswap]
    exact ih (by omega) g gInv hgL hgR hgfix

/-- Zero-Block Vanishing Theorem: if the top-left `r × c` block is zero with `r ≤ n`, `c ≤ n`, `r + c > n`, then `det M = 0`. -/
theorem det_zero_block_gt {n : Nat} (M : Matrix n) (r c : Nat) (hr : r ≤ n) (hc : c ≤ n) (hrc : r + c > n)
    (hz : ∀ i j : Fin n, i.val < r → j.val < c → M i j = 0) :
    det M = 0 := by
  induction n generalizing r c with
  | zero => omega
  | succ n ih =>
    have hr1 : r ≥ 1 := by omega
    rw [det]
    rw [finSum_congr (g := fun _ => 0)]
    · exact finSum_zero
    · intro j
      by_cases hj : j.val < c
      · have h0 : M 0 j = 0 := hz 0 j (by simp [Fin.val_zero]; omega) hj
        rw [h0]; simp
      · have hmin : det (minor M j) = 0 := by
          apply ih (minor M j) (r - 1) c (by omega) (by omega) (by omega)
          intro a b ha hb
          simp only [minor]
          have hskip : (skipIdx j b).val = b.val := by
            apply skipIdx_val_lt; omega
          exact hz a.succ (skipIdx j b) (by simp [Fin.val_succ]; omega) (by omega)
        rw [hmin]; simp

/-- Dimension-cast invariance for `det`. -/
theorem det_cast {m n : Nat} (h : m = n) (M : Matrix m) :
    det (fun (i j : Fin n) => M ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) = det M := by
  subst h
  rfl

/-- General Block Lower-Triangular Determinant Theorem (with arbitrary `n = p + q`). -/
theorem det_block_lower_eq {n p q : Nat} (hn : n = p + q) (M : Matrix n)
    (hz : ∀ (i j : Fin n), i.val < p → p ≤ j.val → M i j = 0) :
    det M =
      det (fun (i j : Fin p) => M ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) *
      det (fun (i j : Fin q) => M ⟨p + i.val, by omega⟩ ⟨p + j.val, by omega⟩) := by
  induction p generalizing n with
  | zero =>
    have h0 : det (fun (i j : Fin 0) => M ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) = 1 := rfl
    rw [h0, Int.one_mul]
    have hnq : n = q := by omega
    have hc := det_cast hnq M
    rw [← hc]
    congr 1; funext i j; simp
  | succ p ih =>
    have hns : n = (p + q) + 1 := by omega
    let M' : Matrix ((p + q) + 1) := fun i j => M ⟨i.val, by omega⟩ ⟨j.val, by omega⟩
    have hcast : det M = det M' := (det_cast hns M).symm
    rw [hcast, det]
    -- Split the sum over `Fin ((p + q) + 1)`: terms with `j.val ≥ p + 1` vanish because `M' 0 j = 0`!
    let A : Matrix (p + 1) := fun i j => M ⟨i.val, by omega⟩ ⟨j.val, by omega⟩
    let D : Matrix q := fun i j => M ⟨(p + 1) + i.val, by omega⟩ ⟨(p + 1) + j.val, by omega⟩
    change _ = det A * det D
    rw [det, ← finSum_mul_right]
    -- Helper: sum over `Fin (a + b)` where indices `≥ a` vanish equals sum over `Fin a`
    have hSumTrunc : ∀ (a b : Nat) (f : Fin (a + b) → Int),
        (∀ j : Fin (a + b), a ≤ j.val → f j = 0) →
        finSum f = finSum (fun j : Fin a => f ⟨j.val, by omega⟩) := by
      intro a b
      induction a with
      | zero =>
        intro f hf
        rw [finSum]
        exact (finSum_congr (g := fun _ => 0) (fun j => hf j (Nat.zero_le _))).trans finSum_zero
      | succ a iha =>
        intro f hf
        have hstep : ∀ (x y : Nat) (hxy : x = y) (g : Fin x → Int),
            finSum g = finSum (fun j : Fin y => g ⟨j.val, by omega⟩) := by
          intro x y hxy g; subst hxy; rfl
        rw [hstep (a + 1 + b) ((a + b) + 1) (by omega) f, finSum_succ, finSum_succ]
        congr 1
        have htail := iha (fun j : Fin (a + b) => f ⟨j.val + 1, by omega⟩) (fun j hj => by
          apply hf ⟨j.val + 1, by omega⟩; dsimp only; omega)
        exact htail
    have hcastSum : ∀ (x y : Nat) (hxy : x = y) (g : Fin x → Int),
        finSum g = finSum (fun j : Fin y => g ⟨j.val, by omega⟩) := by
      intro x y hxy g; subst hxy; rfl
    rw [hcastSum ((p + q) + 1) ((p + 1) + q) (by omega)]
    rw [hSumTrunc (p + 1) q _ (fun j hj => by
      have h0 : M' 0 ⟨j.val, by omega⟩ = 0 := by
        simp only [M']
        exact hz ⟨0, by omega⟩ ⟨j.val, by omega⟩ (by dsimp only; omega) (by dsimp only; omega)
      rw [h0]; simp)]
    apply finSum_congr
    intro j
    have hjlt := j.isLt
    have hM0 : M' 0 ⟨j.val, by omega⟩ = A 0 j := rfl
    have hMin : det (minor M' ⟨j.val, by omega⟩) = det (minor A j) * det D := by
      have hih := ih (n := p + q) rfl (minor M' ⟨j.val, by omega⟩) (fun a b ha hb => by
        simp only [minor, M']
        have hskip : (skipIdx (⟨j.val, by omega⟩ : Fin ((p + q) + 1)) b).val = b.val + 1 := by
          rw [skipIdx_val]; dsimp only
          have : ¬ (b.val < j.val) := by omega
          simp [this]
        exact hz ⟨a.succ.val, by omega⟩ ⟨(skipIdx ⟨j.val, by omega⟩ b).val, by omega⟩
          (by simp [Fin.val_succ]; omega) (by dsimp only; rw [hskip]; omega))
      rw [hih]
      congr 1
      · congr 1; funext a b
        simp only [minor, M', A]
        congr 1; apply Fin.ext
        rw [skipIdx_val, skipIdx_val]
      · congr 1; funext a b
        simp only [minor, M', D]
        congr 1
        · apply Fin.ext; simp; omega
        · apply Fin.ext
          rw [skipIdx_val]; dsimp only
          have hnot : ¬ (p + b.val < j.val) := by omega
          simp [hnot]; omega
    rw [hM0, hMin]
    grind

/-- Helper: cyclic rotation moving row `k` down to row `0` multiplies `det` by `altSign k`. -/
theorem det_row_cycle_to_zero {n : Nat} (M : Matrix (n + 1)) (k : Fin (n + 1)) :
    det (fun i j =>
      M (if i.val = 0 then k
         else if i.val ≤ k.val then ⟨i.val - 1, by omega⟩
         else i) j) = altSign k.val * det M := by
  -- Induct on k.val
  suffices h : ∀ (m : Nat) (hm : m < n + 1) (A : Matrix (n + 1)),
      det (fun i j =>
        A (if i.val = 0 then ⟨m, hm⟩
           else if i.val ≤ m then ⟨i.val - 1, by omega⟩
           else i) j) = altSign m * det A by
    exact h k.val k.isLt M
  intro m
  induction m with
  | zero =>
    intro hm A
    have hEq : (fun i j =>
        A (if i.val = 0 then ⟨0, hm⟩
           else if i.val ≤ 0 then ⟨i.val - 1, by omega⟩
           else i) j) = A := by
      funext i j; congr 1; apply Fin.ext
      by_cases h0 : i.val = 0
      · simp [h0]
      · have hle : ¬ (i.val ≤ 0) := by omega
        simp [h0, hle]
    rw [hEq, altSign_zero, Int.one_mul]
  | succ m ih =>
    intro hm A
    let A1 : Matrix (n + 1) := fun i j => A (adjSwapFin ⟨m, by omega⟩ i) j
    have hEq : (fun i j =>
        A (if i.val = 0 then ⟨m + 1, hm⟩
           else if i.val ≤ m + 1 then ⟨i.val - 1, by omega⟩
           else i) j) =
      (fun i j =>
        A1 (if i.val = 0 then ⟨m, by omega⟩
            else if i.val ≤ m then ⟨i.val - 1, by omega⟩
            else i) j) := by
      funext i j; simp only [A1]; congr 1; apply Fin.ext
      rw [adjSwapFin_val]
      grind
    rw [hEq, ih (by omega) A1, det_row_adj_swap A ⟨m, by omega⟩, altSign_succ]
    grind

/-- Swapping the top `p` rows with the bottom `q` rows of a `(p + q) × (p + q)` matrix
    multiplies `det` by `altSign (p * q)`. -/
theorem det_row_block_swap {p q : Nat} (M : Matrix (p + q)) :
    det (fun (i j : Fin (p + q)) =>
      M (if h : i.val < q then ⟨p + i.val, by omega⟩ else ⟨i.val - q, by have := i.isLt; omega⟩) j) =
    altSign (p * q) * det M := by
  cases q with
  | zero =>
    have hEq : (fun (i j : Fin (p + 0)) =>
      M (if h : i.val < 0 then ⟨p + i.val, by omega⟩ else ⟨i.val - 0, by have := i.isLt; omega⟩) j) = M := by
      funext i j; simp
    rw [hEq, Nat.mul_zero, altSign_zero, Int.one_mul]
  | succ q =>
    -- Cycle row `p + q` to row 0 (sign `altSign (p + q)`), then wait —
    -- even easier: cycle row `p` to row 0 (sign `altSign p`), leaving `q` more bottom rows to cycle past `p` rows!
    -- Wait: cycling row `p + q` to row 0 moves the LAST row to 0, then we rotate the remaining!
    -- Even cleaner: let M1 move row `p + q` to row 0, no, move row `p` to row `0`!
    -- Wait: let's move row `p + q` to row `0` on `M'`:
    -- If `M1` is `M` with the top `p` rows and next `q` rows swapped (keeping row `p+q` at the end),
    -- wait: `Fin (p + (q + 1))` = `Fin ((p + q) + 1)`.
    -- Let `M1` have row `p + q` moved to row `q` (no, move row `p + q` to row `0` in the result!).
    -- Check: in the target matrix `T`:
    --   row 0 of T is row p of M
    --   row 1 of T is row p+1 of M
    --   ...
    --   row q of T is row p+q of M
    --   row q+1 of T is row 0 of M
    --   ...
    --   row p+q of T is row p-1 of M.
    -- Compare with `T_prev` (moving `q` rows instead of `q+1`, applied to `M` with row `p+q` moved to row `0`!):
    -- Let `M1` be `M` with row `p + q` moved to row `0`? Wait: row `0` of `M1` is row `p+q`, rows `1..p` are `0..p-1`, rows `p+1..p+q` are `p..p+q-1`.
    -- No! Look at `det_row_cycle_to_zero`: moving row `p` to row `0` of `M` produces:
    --   `M1` with row `0` = `M p`, rows `1..p` = `M 0..M (p-1)`, rows `p+1..p+q` = `M (p+1)..M (p+q)`!
    -- Now in `M1`, row `0` is ALREADY in its final position (row 0 of T)!
    -- Wait: in `M1`, the remaining `p + q` rows (indices `1..p+q`) are:
    --   `M 0..M (p-1)` (top `p` rows) followed by `M (p+1)..M (p+q)` (bottom `q` rows)!
    -- Applying `ih` to the bottom `p + q` rows (Wait: `ih` works on a `(p+q) × (p+q)` matrix, not inside a `(p+q+1) × (p+q+1)` matrix!).
    -- EVEN SIMPLER: prove `det_row_cycle_range` or just apply `det_row_cycle_to_zero` `q + 1` times in REVERSE order:
    --   To get `T` from `M`, move row `p+q` to row 0 (`altSign (p+q)`), Wait: no!
    --   Move row `p+q` to row 0: rows become `[p+q, 0..p-1, p..p+q-1]`.
    --   Move row `p+q` (= old `p+q-1`) to row 0: rows become `[p+q-1, p+q, 0..p-1, p..p+q-2]`.
    --   Repeat `q+1` times!! Each step moves the LAST row `p+q` to row 0, with sign `altSign (p + q)`!
    --   WAIT A SECOND!! Doing that `q+1` times gives `altSign ((q+1) * (p+q))` = `altSign (p*(q+1) + q*(q+1))` = `altSign (p*(q+1))` because `q*(q+1)` is ALWAYS EVEN!!
    --   OH!! MY!! GOD!! ONE-LINE PROOF!!
    have hRot : ∀ (k : Nat) (hk : k ≤ p + q + 1) (A : Matrix (p + (q + 1))),
        det (fun (i j : Fin (p + (q + 1))) =>
          A (if h : i.val < k then ⟨p + q + 1 - k + i.val, by omega⟩ else ⟨i.val - k, by have := i.isLt; omega⟩) j) =
        altSign (k * (p + q)) * det A := by
      intro k
      induction k with
      | zero =>
        intro _ A
        have hEq : (fun (i j : Fin (p + (q + 1))) =>
          A (if h : i.val < 0 then ⟨p + q + 1 - 0 + i.val, by omega⟩ else ⟨i.val - 0, by have := i.isLt; omega⟩) j) = A := by
          funext i j; simp
        rw [hEq, Nat.zero_mul, altSign_zero, Int.one_mul]
      | succ k ihk =>
        intro hk A
        let B : Matrix (p + (q + 1)) := fun i j =>
          A (if h : i.val < k then ⟨p + q + 1 - k + i.val, by omega⟩ else ⟨i.val - k, by have := i.isLt; omega⟩) j
        let pq : Fin (p + (q + 1)) := ⟨p + q, Nat.lt_succ_self (p + q)⟩
        have hstep := det_row_cycle_to_zero B pq
        have hEq : (fun (i j : Fin (p + (q + 1))) =>
            A (if h : i.val < k + 1 then ⟨p + q + 1 - (k + 1) + i.val, by omega⟩ else ⟨i.val - (k + 1), by have := i.isLt; omega⟩) j) =
          (fun i j =>
            B (if i.val = 0 then pq
               else if i.val ≤ pq.val then ⟨i.val - 1, by omega⟩
               else i) j) := by
          funext i j; simp only [B]; congr 1; apply Fin.ext
          have hilt := i.isLt
          by_cases h0 : i.val = 0
          · have h2 : ¬ (pq.val < k) := by dsimp [pq]; omega
            simp only [h0, h2, ↓reduceIte, ↓reduceDIte, Fin.val_mk]; dsimp [pq]; omega
          · have hle : i.val ≤ pq.val := by dsimp [pq]; omega
            simp only [h0, hle, ↓reduceIte]
            by_cases hlt : i.val < k + 1
            · have hlt' : i.val - 1 < k := by omega
              simp only [hlt, hlt', ↓reduceDIte, Fin.val_mk]; omega
            · have hlt' : ¬ (i.val - 1 < k) := by omega
              simp only [hlt, hlt', ↓reduceDIte, Fin.val_mk]; omega
        calc det (fun (i j : Fin (p + (q + 1))) =>
              A (if h : i.val < k + 1 then ⟨p + q + 1 - (k + 1) + i.val, by omega⟩ else ⟨i.val - (k + 1), by have := i.isLt; omega⟩) j)
            = det (fun i j => B (if i.val = 0 then pq else if i.val ≤ pq.val then ⟨i.val - 1, by omega⟩ else i) j) :=
              congrArg det hEq
          _ = altSign pq.val * det B := hstep
          _ = altSign (p + q) * (altSign (k * (p + q)) * det A) := by
              change altSign (p + q) * det B = _; rw [ihk (by omega) A]
          _ = altSign ((k + 1) * (p + q)) * det A := by
              rw [Nat.succ_mul, altSign_add (k * (p + q)) (p + q), ← Int.mul_assoc, Int.mul_comm (altSign (p + q))]
    have hres := hRot (q + 1) (by omega) M
    have hEq : (fun (i j : Fin (p + (q + 1))) =>
        M (if h : i.val < q + 1 then ⟨p + i.val, by omega⟩ else ⟨i.val - (q + 1), by have := i.isLt; omega⟩) j) =
      (fun (i j : Fin (p + (q + 1))) =>
        M (if h : i.val < q + 1 then ⟨p + q + 1 - (q + 1) + i.val, by omega⟩ else ⟨i.val - (q + 1), by have := i.isLt; omega⟩) j) := by
      funext i j; congr 1; apply Fin.ext
      by_cases h : i.val < q + 1 <;> simp [h]
    rw [hEq, hres]
    congr 1
    -- Show altSign ((q + 1) * (p + q)) = altSign (p * (q + 1)) because (q + 1) * q is even!
    have heven : ((q + 1) * q) % 2 = 0 := by
      by_cases hq : q % 2 = 0
      · rw [Nat.mul_mod, hq]; simp
      · have hq1 : (q + 1) % 2 = 0 := by omega
        rw [Nat.mul_mod, hq1]; simp
    have hmod : ((q + 1) * (p + q)) % 2 = (p * (q + 1)) % 2 := by
      rw [Nat.mul_add, Nat.add_mod, heven, Nat.add_zero, Nat.mod_mod, Nat.mul_comm]
    unfold altSign
    rw [hmod]

/-- Column version: cycling column `k` to column `0` multiplies `det` by `altSign k`. -/
theorem det_col_cycle_to_zero {n : Nat} (M : Matrix (n + 1)) (k : Fin (n + 1)) :
    det (fun i j =>
      M i (if j.val = 0 then k
           else if j.val ≤ k.val then ⟨j.val - 1, by omega⟩
           else j)) = altSign k.val * det M := by
  suffices h : ∀ (m : Nat) (hm : m < n + 1) (A : Matrix (n + 1)),
      det (fun i j =>
        A i (if j.val = 0 then ⟨m, hm⟩
             else if j.val ≤ m then ⟨j.val - 1, by omega⟩
             else j)) = altSign m * det A by
    exact h k.val k.isLt M
  intro m
  induction m with
  | zero =>
    intro hm A
    have hEq : (fun i j =>
        A i (if j.val = 0 then ⟨0, hm⟩
             else if j.val ≤ 0 then ⟨j.val - 1, by omega⟩
             else j)) = A := by
      funext i j; congr 1; apply Fin.ext
      by_cases h0 : j.val = 0
      · simp [h0]
      · have hle : ¬ (j.val ≤ 0) := by omega
        simp [h0, hle]
    rw [hEq, altSign_zero, Int.one_mul]
  | succ m ih =>
    intro hm A
    let A1 : Matrix (n + 1) := fun i j => A i (adjSwapFin ⟨m, by omega⟩ j)
    have hEq : (fun i j =>
        A i (if j.val = 0 then ⟨m + 1, hm⟩
             else if j.val ≤ m + 1 then ⟨j.val - 1, by omega⟩
             else j)) =
      (fun i j =>
        A1 i (if j.val = 0 then ⟨m, by omega⟩
              else if j.val ≤ m then ⟨j.val - 1, by omega⟩
              else j)) := by
      funext i j; simp only [A1]; congr 1; apply Fin.ext
      rw [adjSwapFin_val]
      grind
    rw [hEq, ih (by omega) A1, det_col_adj_swap A ⟨m, by omega⟩, altSign_succ]
    grind

/-- Swapping the left `p` columns with the right `q` columns multiplies `det` by `altSign (p * q)`. -/
theorem det_col_block_swap {p q : Nat} (M : Matrix (p + q)) :
    det (fun (i j : Fin (p + q)) =>
      M i (if h : j.val < q then ⟨p + j.val, by omega⟩ else ⟨j.val - q, by have := j.isLt; omega⟩)) =
    altSign (p * q) * det M := by
  cases q with
  | zero =>
    have hEq : (fun (i j : Fin (p + 0)) =>
      M i (if h : j.val < 0 then ⟨p + j.val, by omega⟩ else ⟨j.val - 0, by have := j.isLt; omega⟩)) = M := by
      funext i j; simp
    rw [hEq, Nat.mul_zero, altSign_zero, Int.one_mul]
  | succ q =>
    have hRot : ∀ (k : Nat) (hk : k ≤ p + q + 1) (A : Matrix (p + (q + 1))),
        det (fun (i j : Fin (p + (q + 1))) =>
          A i (if h : j.val < k then ⟨p + q + 1 - k + j.val, by omega⟩ else ⟨j.val - k, by have := j.isLt; omega⟩)) =
        altSign (k * (p + q)) * det A := by
      intro k
      induction k with
      | zero =>
        intro _ A
        have hEq : (fun (i j : Fin (p + (q + 1))) =>
          A i (if h : j.val < 0 then ⟨p + q + 1 - 0 + j.val, by omega⟩ else ⟨j.val - 0, by have := j.isLt; omega⟩)) = A := by
          funext i j; simp
        rw [hEq, Nat.zero_mul, altSign_zero, Int.one_mul]
      | succ k ihk =>
        intro hk A
        let B : Matrix (p + (q + 1)) := fun i j =>
          A i (if h : j.val < k then ⟨p + q + 1 - k + j.val, by omega⟩ else ⟨j.val - k, by have := j.isLt; omega⟩)
        let pq : Fin (p + (q + 1)) := ⟨p + q, Nat.lt_succ_self (p + q)⟩
        have hstep := det_col_cycle_to_zero B pq
        have hEq : (fun (i j : Fin (p + (q + 1))) =>
            A i (if h : j.val < k + 1 then ⟨p + q + 1 - (k + 1) + j.val, by omega⟩ else ⟨j.val - (k + 1), by have := j.isLt; omega⟩)) =
          (fun i j =>
            B i (if j.val = 0 then pq
                 else if j.val ≤ pq.val then ⟨j.val - 1, by omega⟩
                 else j)) := by
          funext i j; simp only [B]; congr 1; apply Fin.ext
          have hjlt := j.isLt
          by_cases h0 : j.val = 0
          · have h2 : ¬ (pq.val < k) := by dsimp [pq]; omega
            simp only [h0, h2, ↓reduceIte, ↓reduceDIte, Fin.val_mk]; dsimp [pq]; omega
          · have hle : j.val ≤ pq.val := by dsimp [pq]; omega
            simp only [h0, hle, ↓reduceIte]
            by_cases hlt : j.val < k + 1
            · have hlt' : j.val - 1 < k := by omega
              simp only [hlt, hlt', ↓reduceDIte, Fin.val_mk]; omega
            · have hlt' : ¬ (j.val - 1 < k) := by omega
              simp only [hlt, hlt', ↓reduceDIte, Fin.val_mk]; omega
        calc det (fun (i j : Fin (p + (q + 1))) =>
              A i (if h : j.val < k + 1 then ⟨p + q + 1 - (k + 1) + j.val, by omega⟩ else ⟨j.val - (k + 1), by have := j.isLt; omega⟩))
            = det (fun i j => B i (if j.val = 0 then pq else if j.val ≤ pq.val then ⟨j.val - 1, by omega⟩ else j)) :=
              congrArg det hEq
          _ = altSign pq.val * det B := hstep
          _ = altSign (p + q) * (altSign (k * (p + q)) * det A) := by
              change altSign (p + q) * det B = _; rw [ihk (by omega) A]
          _ = altSign ((k + 1) * (p + q)) * det A := by
              rw [Nat.succ_mul, altSign_add (k * (p + q)) (p + q), ← Int.mul_assoc, Int.mul_comm (altSign (p + q))]
    have hres := hRot (q + 1) (by omega) M
    have hEq : (fun (i j : Fin (p + (q + 1))) =>
        M i (if h : j.val < q + 1 then ⟨p + j.val, by omega⟩ else ⟨j.val - (q + 1), by have := j.isLt; omega⟩)) =
      (fun (i j : Fin (p + (q + 1))) =>
        M i (if h : j.val < q + 1 then ⟨p + q + 1 - (q + 1) + j.val, by omega⟩ else ⟨j.val - (q + 1), by have := j.isLt; omega⟩)) := by
      funext i j; congr 1; apply Fin.ext
      by_cases h : j.val < q + 1 <;> simp [h]
    rw [hEq, hres]
    congr 1
    have heven : ((q + 1) * q) % 2 = 0 := by
      by_cases hq : q % 2 = 0
      · rw [Nat.mul_mod, hq]; simp
      · have hq1 : (q + 1) % 2 = 0 := by omega
        rw [Nat.mul_mod, hq1]; simp
    have hmod : ((q + 1) * (p + q)) % 2 = (p * (q + 1)) % 2 := by
      rw [Nat.mul_add, Nat.add_mod, heven, Nat.add_zero, Nat.mod_mod, Nat.mul_comm]
    unfold altSign
    rw [hmod]

/-- Anti-diagonal block with zero bottom-right block: `det [[A, B], [C, 0]] = (-1)^m * det B * det C`. -/
theorem det_block_anti_zero_br {m : Nat} (M : Matrix (m + m))
    (hz : ∀ (i j : Fin (m + m)), m ≤ i.val → m ≤ j.val → M i j = 0) :
    det M = altSign m *
      det (fun (i j : Fin m) => M ⟨i.val, by omega⟩ ⟨m + j.val, by omega⟩) *
      det (fun (i j : Fin m) => M ⟨m + i.val, by omega⟩ ⟨j.val, by omega⟩) := by
  let M' : Matrix (m + m) := fun i j =>
    M (if h : i.val < m then ⟨m + i.val, by omega⟩ else ⟨i.val - m, by have := i.isLt; omega⟩) j
  have hswap := det_row_block_swap (p := m) (q := m) M
  change det M' = altSign (m * m) * det M at hswap
  have hbl := det_block_lower_eq (p := m) (q := m) rfl M' (fun i j hi hj => by
    simp only [M', hi, ↓reduceDIte]
    exact hz ⟨m + i.val, by omega⟩ j (by dsimp only; omega) hj)
  have hA : (fun (i j : Fin m) => M' ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) =
            (fun (i j : Fin m) => M ⟨m + i.val, by omega⟩ ⟨j.val, by omega⟩) := by
    funext i j; simp [M', i.isLt]
  have hD : (fun (i j : Fin m) => M' ⟨m + i.val, by omega⟩ ⟨m + j.val, by omega⟩) =
            (fun (i j : Fin m) => M ⟨i.val, by omega⟩ ⟨m + j.val, by omega⟩) := by
    funext i j
    have hnot : ¬ (m + i.val < m) := by omega
    simp only [M', hnot, ↓reduceDIte]
    congr 1; apply Fin.ext; dsimp only; omega
  rw [hA, hD] at hbl
  rw [altSign_sq_eq] at hswap
  have hmul : altSign m * det M' = det M := by
    rw [hswap, ← Int.mul_assoc, altSign_mul_self, Int.one_mul]
  rw [← hmul, hbl]
  rw [Int.mul_assoc, Int.mul_comm (det fun (i j : Fin m) => M ⟨m + i.val, by omega⟩ ⟨j.val, by omega⟩), ← Int.mul_assoc]

/-- Anti-diagonal block with zero top-left block: `det [[0, B], [C, D]] = (-1)^m * det B * det C`. -/
theorem det_block_anti_zero_tl {m : Nat} (M : Matrix (m + m))
    (hz : ∀ (i j : Fin (m + m)), i.val < m → j.val < m → M i j = 0) :
    det M = altSign m *
      det (fun (i j : Fin m) => M ⟨i.val, by omega⟩ ⟨m + j.val, by omega⟩) *
      det (fun (i j : Fin m) => M ⟨m + i.val, by omega⟩ ⟨j.val, by omega⟩) := by
  let M' : Matrix (m + m) := fun i j =>
    M i (if h : j.val < m then ⟨m + j.val, by omega⟩ else ⟨j.val - m, by have := j.isLt; omega⟩)
  have hswap := det_col_block_swap (p := m) (q := m) M
  change det M' = altSign (m * m) * det M at hswap
  have hbl := det_block_lower_eq (p := m) (q := m) rfl M' (fun i j hi hj => by
    simp only [M']
    have hnot : ¬ (j.val < m) := by omega
    simp only [hnot, ↓reduceDIte]
    exact hz i ⟨j.val - m, by have := j.isLt; omega⟩ hi (by dsimp only; omega))
  have hA : (fun (i j : Fin m) => M' ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) =
            (fun (i j : Fin m) => M ⟨i.val, by omega⟩ ⟨m + j.val, by omega⟩) := by
    funext i j; simp [M', j.isLt]
  have hD : (fun (i j : Fin m) => M' ⟨m + i.val, by omega⟩ ⟨m + j.val, by omega⟩) =
            (fun (i j : Fin m) => M ⟨m + i.val, by omega⟩ ⟨j.val, by omega⟩) := by
    funext i j
    have hnot : ¬ (m + j.val < m) := by omega
    simp only [M', hnot, ↓reduceDIte]
    congr 1; apply Fin.ext; dsimp only; omega
  rw [hA, hD] at hbl
  rw [altSign_sq_eq] at hswap
  have hmul : altSign m * det M' = det M := by
    rw [hswap, ← Int.mul_assoc, altSign_mul_self, Int.one_mul]
  rw [← hmul, hbl, ← Int.mul_assoc]

/-- Rank-1 Corner Anti-Diagonal Theorem (Even Size `2*(m+1)`). -/
theorem det_rank1_corner_anti {m : Nat} (M : Matrix ((m + 1) + (m + 1))) (c d : Int)
    (htl : ∀ i j : Fin ((m + 1) + (m + 1)), i.val < m + 1 → j.val < m + 1 →
      M i j = if i.val = 0 ∧ j.val = 0 then c else 0)
    (hbr : ∀ i j : Fin ((m + 1) + (m + 1)), m + 1 ≤ i.val → m + 1 ≤ j.val →
      M i j = if i.val = m + 1 ∧ j.val = m + 1 then d else 0) :
    det M =
      altSign (m + 1) *
        det (fun (i j : Fin (m + 1)) => M ⟨i.val, by omega⟩ ⟨m + 1 + j.val, by omega⟩) *
        det (fun (i j : Fin (m + 1)) => M ⟨m + 1 + i.val, by omega⟩ ⟨j.val, by omega⟩) +
      altSign m * c * d *
        det (fun (i j : Fin m) => M ⟨i.val + 1, by omega⟩ ⟨m + 1 + j.val + 1, by omega⟩) *
        det (fun (i j : Fin m) => M ⟨m + 1 + i.val + 1, by omega⟩ ⟨j.val + 1, by omega⟩) := by
  let N := (m + 1) + (m + 1)
  let r0_c : Fin N → Int := fun j => if j.val = 0 then c else 0
  let r0_B : Fin N → Int := fun j => if j.val < m + 1 then 0 else M 0 j
  have hMsplit : M = setRow M 0 (fun j => r0_c j + r0_B j) := by
    funext i j; simp only [setRow]
    by_cases hi : i = 0
    · subst hi; simp only [↓reduceIte, r0_c, r0_B]
      by_cases hj : j.val < m + 1
      · have h := htl 0 j (by simp) hj
        simp only [Fin.val_zero, true_and] at h
        simp [hj, h]
      · have hne : j.val ≠ 0 := by omega
        simp [hj, hne]
    · simp [hi]
  have hDetSplit : det M = det (setRow M 0 r0_c) + det (setRow M 0 r0_B) := by
    have h := det_row_add M 0 r0_c r0_B
    rw [← hMsplit] at h
    exact h
  let M1 : Matrix N := setRow M 0 r0_c
  let M2 : Matrix N := setRow M 0 r0_B
  have hM2 : det M2 =
      altSign (m + 1) *
        det (fun (i j : Fin (m + 1)) => M ⟨i.val, by omega⟩ ⟨m + 1 + j.val, by omega⟩) *
        det (fun (i j : Fin (m + 1)) => M ⟨m + 1 + i.val, by omega⟩ ⟨j.val, by omega⟩) := by
    rw [det_block_anti_zero_tl M2 (fun i j hi hj => by
      simp only [M2, setRow]
      by_cases hi0 : i = 0
      · subst hi0; simp [r0_B, hj]
      · have hiv : i.val ≠ 0 := fun hv => hi0 (Fin.ext hv)
        simp [hi0, htl i j hi hj, hiv])]
    have hBeq : (fun (i j : Fin (m + 1)) => M2 ⟨i.val, by omega⟩ ⟨m + 1 + j.val, by omega⟩) =
                (fun (i j : Fin (m + 1)) => M ⟨i.val, by omega⟩ ⟨m + 1 + j.val, by omega⟩) := by
      funext i j
      simp only [M2, setRow]
      by_cases hi0 : (⟨i.val, by omega⟩ : Fin N) = 0
      · have hnot : ¬ (m + 1 + j.val < m + 1) := by omega
        simp [hi0, r0_B, hnot]
      · simp [hi0]
    have hCeq : (fun (i j : Fin (m + 1)) => M2 ⟨m + 1 + i.val, by omega⟩ ⟨j.val, by omega⟩) =
                (fun (i j : Fin (m + 1)) => M ⟨m + 1 + i.val, by omega⟩ ⟨j.val, by omega⟩) := by
      funext i j
      have hne : (⟨m + 1 + i.val, by omega⟩ : Fin N) ≠ 0 := fun h => by
        have hv := congrArg Fin.val h; simp at hv
      simp [M2, setRow, hne]
    rw [hBeq, hCeq]
  let N1 := (m + 1) + m
  have hN : N = N1 + 1 := by omega
  let M1' : Matrix (N1 + 1) := fun i j => M1 ⟨i.val, by omega⟩ ⟨j.val, by omega⟩
  have hM1_exp : det M1 = c * det (minor M1' 0) := by
    rw [← det_cast hN M1]
    change det M1' = c * det (minor M1' 0)
    rw [det, finSum_single 0 _ (fun j hj => by
      have h0 : M1' 0 j = 0 := by simp [M1', M1, setRow, r0_c, hj]
      rw [h0]; simp)]
    have h00 : M1' 0 0 = c := by simp [M1', M1, setRow, r0_c]
    rw [h00, Fin.val_zero, altSign_zero, Int.one_mul]
  let K : Matrix N1 := minor M1' 0
  let pm : Fin N1 := ⟨m, by omega⟩
  let rm_d : Fin N1 → Int := fun j => if j.val = m then d else 0
  let rm_C : Fin N1 → Int := fun j => if j.val < m then K pm j else 0
  have hKsplit : K = setRow K pm (fun j => rm_d j + rm_C j) := by
    funext i j; simp only [setRow]
    by_cases hip : i = pm
    · subst hip; simp only [↓reduceIte, rm_d, rm_C]
      by_cases hj : j.val < m
      · have hne : j.val ≠ m := by omega
        simp [hj, hne]
      · have hjlt := j.isLt
        have hne0 : (⟨m + 1, by omega⟩ : Fin N) ≠ 0 := fun he => by
          have := congrArg Fin.val he; simp at this
        have hKval : K pm j = M ⟨m + 1, by omega⟩ ⟨j.val + 1, by omega⟩ := by
          simp only [K, minor, M1', M1, setRow, skipIdx_zero]
          have h1 : (⟨pm.succ.val, by omega⟩ : Fin N) = ⟨m + 1, by omega⟩ := Fin.ext rfl
          have h2 : (⟨j.succ.val, by omega⟩ : Fin N) = ⟨j.val + 1, by omega⟩ := Fin.ext rfl
          rw [h1, h2]; simp [hne0]
        rw [hKval]
        have hbrv := hbr ⟨m + 1, by omega⟩ ⟨j.val + 1, by omega⟩ (by dsimp only; omega) (by dsimp only; omega)
        by_cases hjm : j.val = m
        · simp only [hjm, ↓reduceIte]
          simpa [hjm] using hbrv
        · simp only [hj, hjm, ↓reduceIte, Int.add_zero]
          simpa [hjm] using hbrv
    · simp [hip]
  have hK_det : det K =
      altSign m * d *
        det (fun (i j : Fin m) => M ⟨i.val + 1, by omega⟩ ⟨m + 1 + j.val + 1, by omega⟩) *
        det (fun (i j : Fin m) => M ⟨m + 1 + i.val + 1, by omega⟩ ⟨j.val + 1, by omega⟩) := by
    have hKAdd : det K = det (setRow K pm rm_d) + det (setRow K pm rm_C) := by
      have h := det_row_add K pm rm_d rm_C
      rw [← hKsplit] at h
      exact h
    let K1 : Matrix N1 := setRow K pm rm_d
    let K2 : Matrix N1 := setRow K pm rm_C
    have hK2 : det K2 = 0 := by
      have hcastK : N1 = m + (m + 1) := by omega
      let K2' : Matrix (m + (m + 1)) := fun i j => K2 ⟨i.val, by omega⟩ ⟨j.val, by omega⟩
      rw [← det_cast hcastK K2]
      change det K2' = 0
      have hr := det_row_block_swap (p := m) (q := m + 1) K2'
      let K2r : Matrix (m + (m + 1)) := fun i j =>
        K2' (if h : i.val < m + 1 then ⟨m + i.val, by omega⟩ else ⟨i.val - (m + 1), by have := i.isLt; omega⟩) j
      have hc := det_col_block_swap (p := m) (q := m + 1) K2r
      have hz0 : det (fun i j =>
          K2r i (if h : j.val < m + 1 then ⟨m + j.val, by omega⟩ else ⟨j.val - (m + 1), by have := j.isLt; omega⟩)) = 0 := by
        apply det_zero_block_gt _ (m + 1) (m + 1) (by omega) (by omega) (by omega)
        intro i j hi hj
        simp only [K2r, hi, hj, ↓reduceDIte, K2', K2, setRow]
        by_cases hi0 : i.val = 0
        · have heq : (⟨m + i.val, by omega⟩ : Fin N1) = pm := Fin.ext (by simp [pm, hi0])
          simp only [heq, ↓reduceIte, rm_C]
          have hnot : ¬ (m + j.val < m) := by omega
          simp [hnot]
        · have hne : (⟨m + i.val, by omega⟩ : Fin N1) ≠ pm := fun h => hi0 (by
            have hv := congrArg Fin.val h; dsimp [pm] at hv; omega)
          simp only [hne, ↓reduceIte, K, minor, M1', M1, setRow, skipIdx_zero]
          have hne0 : (⟨(⟨m + i.val, by omega⟩ : Fin N1).succ.val, by omega⟩ : Fin N) ≠ 0 := fun h => by
            have := congrArg Fin.val h; simp at this
          simp only [hne0, ↓reduceIte]
          have h := hbr ⟨m + i.val + 1, by omega⟩ ⟨m + j.val + 1, by omega⟩ (by dsimp only; omega) (by dsimp only; omega)
          have heq1 : (⟨(⟨m + i.val, by omega⟩ : Fin N1).succ.val, by omega⟩ : Fin N) = ⟨m + i.val + 1, by omega⟩ :=
            Fin.ext (by simp)
          have heq2 : (⟨(⟨m + j.val, by omega⟩ : Fin N1).succ.val, by omega⟩ : Fin N) = ⟨m + j.val + 1, by omega⟩ :=
            Fin.ext (by simp)
          rw [heq1, heq2, h]; simp [hi0]
      rw [hz0] at hc
      have hK2r0 : det K2r = 0 := by
        have h1 : altSign (m * (m + 1)) * (altSign (m * (m + 1)) * det K2r) = 0 := by rw [← hc]; simp
        rw [← Int.mul_assoc, altSign_mul_self, Int.one_mul] at h1
        exact h1
      change det K2r = altSign (m * (m + 1)) * det K2' at hr
      rw [hK2r0] at hr
      have h2 : altSign (m * (m + 1)) * (altSign (m * (m + 1)) * det K2') = 0 := by rw [← hr]; simp
      rw [← Int.mul_assoc, altSign_mul_self, Int.one_mul] at h2
      exact h2
    have hK1 : det K1 =
        altSign m * d *
          det (fun (i j : Fin m) => M ⟨i.val + 1, by omega⟩ ⟨m + 1 + j.val + 1, by omega⟩) *
          det (fun (i j : Fin m) => M ⟨m + 1 + i.val + 1, by omega⟩ ⟨j.val + 1, by omega⟩) := by
      have hN1s : N1 = (m + m) + 1 := by omega
      let K1' : Matrix ((m + m) + 1) := fun i j => K1 ⟨i.val, by omega⟩ ⟨j.val, by omega⟩
      rw [← det_cast hN1s K1]
      change det K1' = _
      let p' : Fin ((m + m) + 1) := ⟨m, by omega⟩
      let K1r : Matrix ((m + m) + 1) := fun i j =>
        K1' (if i.val = 0 then p' else if i.val ≤ p'.val then ⟨i.val - 1, by omega⟩ else i) j
      let K1rc : Matrix ((m + m) + 1) := fun i j =>
        K1r i (if j.val = 0 then p' else if j.val ≤ p'.val then ⟨j.val - 1, by omega⟩ else j)
      have hr := det_row_cycle_to_zero K1' p'
      have hc := det_col_cycle_to_zero K1r p'
      have hcong : det K1rc = det K1' := by
        change det K1rc = altSign p'.val * det K1r at hc
        change det K1r = altSign p'.val * det K1' at hr
        rw [hc, hr, ← Int.mul_assoc, altSign_mul_self, Int.one_mul]
      rw [← hcong, det]
      rw [finSum_single 0 _ (fun j hj => by
        have hjne : j.val ≠ 0 := fun hv => hj (Fin.ext hv)
        have h0 : K1rc 0 j = 0 := by
          simp only [K1rc, K1r, Fin.val_zero, ↓reduceIte, K1', K1, setRow, hjne]
          have hpeq : (⟨p'.val, by omega⟩ : Fin N1) = pm := Fin.ext rfl
          simp only [hpeq, ↓reduceIte, rm_d]
          split
          · have hne : j.val - 1 ≠ m := by simp [p'] at *; omega
            simp [hne]
          · have hne : j.val ≠ m := by simp [p'] at *; omega
            simp [hne]
        rw [h0]; simp)]
      have h00 : K1rc 0 0 = d := by
        simp only [K1rc, K1r, Fin.val_zero, ↓reduceIte, K1', K1, setRow]
        have hpeq : (⟨p'.val, by omega⟩ : Fin N1) = pm := Fin.ext rfl
        simp [hpeq, rm_d, p', pm]
      rw [h00, Fin.val_zero, altSign_zero, Int.one_mul]
      rw [det_block_anti_zero_tl (minor K1rc 0) (fun i j hi hj => by
        simp only [minor, K1rc, K1r, skipIdx_zero, Fin.val_succ]
        have h1 : ¬ (i.val + 1 = 0) := by omega
        have h2 : i.val + 1 ≤ p'.val := by simp [p']; omega
        have h3 : ¬ (j.val + 1 = 0) := by omega
        have h4 : j.val + 1 ≤ p'.val := by simp [p']; omega
        simp only [h1, h2, h3, h4, ↓reduceIte, K1', K1, setRow]
        have hnep : (⟨i.val + 1 - 1, by omega⟩ : Fin N1) ≠ pm := fun h => by
          have := congrArg Fin.val h; simp [pm] at this; omega
        simp only [hnep, ↓reduceIte, K, minor, M1', M1, setRow, skipIdx_zero]
        have hne0 : (⟨(⟨i.val + 1 - 1, by omega⟩ : Fin N1).succ.val, by omega⟩ : Fin N) ≠ 0 := fun h => by
          have := congrArg Fin.val h; simp at this
        simp only [hne0, ↓reduceIte]
        have h := htl ⟨i.val + 1, by omega⟩ ⟨j.val + 1, by omega⟩ (by dsimp only; omega) (by dsimp only; omega)
        have hni : i.val + 1 ≠ 0 := by omega
        have heq1 : (⟨(⟨i.val + 1 - 1, by omega⟩ : Fin N1).succ.val, by omega⟩ : Fin N) = ⟨i.val + 1, by omega⟩ :=
          Fin.ext (by simp)
        have heq2 : (⟨(⟨j.val + 1 - 1, by omega⟩ : Fin N1).succ.val, by omega⟩ : Fin N) = ⟨j.val + 1, by omega⟩ :=
          Fin.ext (by simp)
        rw [heq1, heq2, h]; simp)]
      have hB1 : (fun (i j : Fin m) => minor K1rc 0 ⟨i.val, by omega⟩ ⟨m + j.val, by omega⟩) =
                 (fun (i j : Fin m) => M ⟨i.val + 1, by omega⟩ ⟨m + 1 + j.val + 1, by omega⟩) := by
        funext i j
        have hilt := i.isLt; have hjlt := j.isLt
        simp only [minor, K1rc, K1r, skipIdx_zero, Fin.val_succ]
        have h1 : ¬ (i.val + 1 = 0) := by omega
        have h2 : i.val + 1 ≤ p'.val := by simp [p']; omega
        have h3 : ¬ (m + j.val + 1 = 0) := by omega
        have h4 : ¬ (m + j.val + 1 ≤ p'.val) := by simp [p']; omega
        simp only [h1, h2, h3, h4, ↓reduceIte, K1', K1, setRow]
        have hnep : (⟨i.val + 1 - 1, by omega⟩ : Fin N1) ≠ pm := fun h => by
          have := congrArg Fin.val h; simp [pm] at this; omega
        simp only [hnep, ↓reduceIte, K, minor, M1', M1, setRow, skipIdx_zero]
        have hne0 : (⟨(⟨i.val + 1 - 1, by omega⟩ : Fin N1).succ.val, by omega⟩ : Fin N) ≠ 0 := fun h => by
          have := congrArg Fin.val h; simp at this
        simp only [hne0, ↓reduceIte]
        congr 1 <;> apply Fin.ext <;> simp <;> omega
      have hC1 : (fun (i j : Fin m) => minor K1rc 0 ⟨m + i.val, by omega⟩ ⟨j.val, by omega⟩) =
                 (fun (i j : Fin m) => M ⟨m + 1 + i.val + 1, by omega⟩ ⟨j.val + 1, by omega⟩) := by
        funext i j
        have hilt := i.isLt; have hjlt := j.isLt
        simp only [minor, K1rc, K1r, skipIdx_zero, Fin.val_succ]
        have h1 : ¬ (m + i.val + 1 = 0) := by omega
        have h2 : ¬ (m + i.val + 1 ≤ p'.val) := by simp [p']; omega
        have h3 : ¬ (j.val + 1 = 0) := by omega
        have h4 : j.val + 1 ≤ p'.val := by simp [p']; omega
        simp only [h1, h2, h3, h4, ↓reduceIte, K1', K1, setRow]
        have hnep : (⟨(⟨m + i.val, by omega⟩ : Fin (m + m)).succ.val, by omega⟩ : Fin N1) ≠ pm := fun h => by
          have := congrArg Fin.val h; simp [pm] at this; omega
        simp only [hnep, ↓reduceIte, K, minor, M1', M1, setRow, skipIdx_zero]
        have hne0 : (⟨(⟨(⟨m + i.val, by omega⟩ : Fin (m + m)).succ.val, by omega⟩ : Fin N1).succ.val, by omega⟩ : Fin N) ≠ 0 := fun h => by
          have := congrArg Fin.val h; simp at this
        simp only [hne0, ↓reduceIte]
        congr 1 <;> apply Fin.ext <;> simp <;> omega
      rw [hB1, hC1]
      rw [← Int.mul_assoc, ← Int.mul_assoc, Int.mul_comm d (altSign m)]
    change det K = _
    rw [hKAdd]
    change det K1 + det K2 = _
    rw [hK1, hK2, Int.add_zero]
  rw [hDetSplit]
  change det M1 + det M2 = _
  rw [hM1_exp, hK_det, hM2, Int.add_comm]
  congr 1
  rw [← Int.mul_assoc, ← Int.mul_assoc, ← Int.mul_assoc, Int.mul_comm c (altSign m)]

/-- Rank-1 Corner Anti-Diagonal Theorem (Odd Size `(m+1) + m`). -/
theorem det_rank1_corner_anti_odd {m : Nat} (M : Matrix ((m + 1) + m)) (c : Int)
    (htl : ∀ i j : Fin ((m + 1) + m), i.val < m + 1 → j.val < m + 1 →
      M i j = if i.val = 0 ∧ j.val = 0 then c else 0) :
    det M =
      altSign m * c *
        det (fun (i j : Fin m) => M ⟨i.val + 1, by omega⟩ ⟨m + 1 + j.val, by omega⟩) *
        det (fun (i j : Fin m) => M ⟨m + 1 + i.val, by omega⟩ ⟨j.val + 1, by omega⟩) := by
  let N := (m + 1) + m
  let r0_c : Fin N → Int := fun j => if j.val = 0 then c else 0
  let r0_B : Fin N → Int := fun j => if j.val < m + 1 then 0 else M 0 j
  have hMsplit : M = setRow M 0 (fun j => r0_c j + r0_B j) := by
    funext i j; simp only [setRow]
    by_cases hi : i = 0
    · subst hi; simp only [↓reduceIte, r0_c, r0_B]
      by_cases hj : j.val < m + 1
      · have h := htl 0 j (by simp) hj
        simp only [Fin.val_zero, true_and] at h
        simp [hj, h]
      · have hne : j.val ≠ 0 := by omega
        simp [hj, hne]
    · simp [hi]
  have hDetSplit : det M = det (setRow M 0 r0_c) + det (setRow M 0 r0_B) := by
    have h := det_row_add M 0 r0_c r0_B
    rw [← hMsplit] at h
    exact h
  have hM2 : det (setRow M 0 r0_B) = 0 := by
    apply det_zero_block_gt _ (m + 1) (m + 1) (by omega) (by omega) (by omega)
    intro i j hi hj
    simp only [setRow]
    by_cases hi0 : i = 0
    · subst hi0; simp [r0_B, hj]
    · have hiv : i.val ≠ 0 := fun hv => hi0 (Fin.ext hv)
      simp [hi0, htl i j hi hj, hiv]
  let M1 : Matrix N := setRow M 0 r0_c
  have hN : N = (m + m) + 1 := by omega
  let M1' : Matrix ((m + m) + 1) := fun i j => M1 ⟨i.val, by omega⟩ ⟨j.val, by omega⟩
  have hM1 : det M1 = c * det (minor M1' 0) := by
    rw [← det_cast hN M1]
    change det M1' = c * det (minor M1' 0)
    rw [det, finSum_single 0 _ (fun j hj => by
      have h0 : M1' 0 j = 0 := by simp [M1', M1, setRow, r0_c, hj]
      rw [h0]; simp)]
    have h00 : M1' 0 0 = c := by simp [M1', M1, setRow, r0_c]
    rw [h00, Fin.val_zero, altSign_zero, Int.one_mul]
  rw [hDetSplit]
  change det M1 + det (setRow M 0 r0_B) = _
  rw [hM1, hM2, Int.add_zero]
  rw [det_block_anti_zero_tl (minor M1' 0) (fun i j hi hj => by
    simp only [minor, M1', M1, setRow, skipIdx_zero]
    have hne0 : (⟨i.succ.val, by omega⟩ : Fin N) ≠ 0 := fun h => by
      have := congrArg Fin.val h; simp at this
    simp only [hne0, ↓reduceIte]
    have h := htl ⟨i.succ.val, by omega⟩ ⟨j.succ.val, by omega⟩ (by simp; omega) (by simp; omega)
    have hni : i.succ.val ≠ 0 := by simp
    simpa [hni] using h)]
  have hB1 : (fun (i j : Fin m) => minor M1' 0 ⟨i.val, by omega⟩ ⟨m + j.val, by omega⟩) =
             (fun (i j : Fin m) => M ⟨i.val + 1, by omega⟩ ⟨m + 1 + j.val, by omega⟩) := by
    funext i j
    simp only [minor, M1', M1, setRow, skipIdx_zero]
    have hne0 : (⟨(⟨i.val, by omega⟩ : Fin (m + m)).succ.val, by omega⟩ : Fin N) ≠ 0 := fun h => by
      have := congrArg Fin.val h; simp at this
    simp only [hne0, ↓reduceIte]
    congr 1 <;> apply Fin.ext <;> simp <;> omega
  have hC1 : (fun (i j : Fin m) => minor M1' 0 ⟨m + i.val, by omega⟩ ⟨j.val, by omega⟩) =
             (fun (i j : Fin m) => M ⟨m + 1 + i.val, by omega⟩ ⟨j.val + 1, by omega⟩) := by
    funext i j
    simp only [minor, M1', M1, setRow, skipIdx_zero]
    have hne0 : (⟨(⟨m + i.val, by omega⟩ : Fin (m + m)).succ.val, by omega⟩ : Fin N) ≠ 0 := fun h => by
      have := congrArg Fin.val h; simp at this
    simp only [hne0, ↓reduceIte]
    congr 1 <;> apply Fin.ext <;> simp <;> omega
  rw [hB1, hC1, ← Int.mul_assoc, ← Int.mul_assoc, Int.mul_comm c (altSign m)]

/-! ## Part 2B: The Reusable Silicon Bit-Slice Hankel Congruence Engine (Operators A–D) -/

theorem intPow_add (x : Int) (a b : Nat) : intPow x (a + b) = intPow x a * intPow x b := by
  induction a with
  | zero => simp [intPow]
  | succ a ih => rw [Nat.succ_add, intPow_succ, intPow_succ, ih, Int.mul_assoc]

theorem intPow_mul_pow (x y : Int) (n : Nat) : intPow (x * y) n = intPow x n * intPow y n := by
  induction n with
  | zero => simp [intPow]
  | succ n ih => rw [intPow_succ, intPow_succ, intPow_succ, ih]; grind

/-- Scaling all entries of an `n × n` matrix by `α` multiplies `det` by `α^n`. -/
theorem det_smul_all {n : Nat} (α : Int) (M : Matrix n) :
    det (fun i j => α * M i j) = intPow α n * det M := by
  suffices h : ∀ (k : Nat) (hk : k ≤ n),
      det (fun i j => if i.val < k then α * M i j else M i j) = intPow α k * det M by
    have hres := h n (Nat.le_refl n)
    have hEq : (fun i j => if i.val < n then α * M i j else M i j) = (fun i j => α * M i j) := by
      funext i j; simp [i.isLt]
    rw [hEq] at hres
    exact hres
  intro k
  induction k with
  | zero =>
    intro _
    have hEq : (fun i j => if i.val < 0 then α * M i j else M i j) = M := by funext i j; simp
    rw [hEq, intPow_zero, Int.one_mul]
  | succ k ih =>
    intro hk
    let prev : Matrix n := fun i j => if i.val < k then α * M i j else M i j
    let pk : Fin n := ⟨k, by omega⟩
    have hEq : (fun i j => if i.val < k + 1 then α * M i j else M i j) =
        setRow prev pk (fun j => α * prev pk j) := by
      funext i j; simp only [setRow, prev]
      by_cases hip : i = pk
      · subst hip; simp [pk]
      · have hne : i.val ≠ k := fun h => hip (Fin.ext h)
        have hiff : (i.val < k + 1) ↔ (i.val < k) := by omega
        by_cases h1 : i.val < k + 1
        · have h2 : i.val < k := hiff.mp h1
          simp [hip, h1, h2]
        · have h2 : ¬ (i.val < k) := fun h => h1 (hiff.mpr h)
          simp [hip, h1, h2]
    have hprev : setRow prev pk (fun j => prev pk j) = prev := by
      funext i j; unfold setRow; split <;> simp_all
    rw [hEq, det_row_smul, hprev, ih (by omega), intPow_succ, Int.mul_assoc]

theorem qDiff_one_eq_diff1 (a : Nat → Int) : qDiff 1 a = diff1 a := by
  funext k; simp [qDiff, diff1]

theorem isUnitLower_qDiffMat (q : Int) (n : Nat) : IsUnitLower (qDiffMat q n) := by
  refine ⟨fun i => by simp [qDiffMat], fun i j hij => ?_⟩
  have hne : i ≠ j := fun h => by subst h; omega
  have hne2 : ¬ (j.val + 1 = i.val) := by omega
  simp [qDiffMat, hne, hne2]

/-- Explicit entries of `D_q * M`. -/
theorem matMul_qDiffMat_left {n : Nat} (q : Int) (M : Matrix n) (i j : Fin n) :
    matMul (qDiffMat q n) M i j =
      if _ : i.val = 0 then M i j else M i j - q * M ⟨i.val - 1, by have := i.isLt; omega⟩ j := by
  unfold matMul
  by_cases hi : i.val = 0
  · simp only [hi, ↓reduceDIte]
    rw [finSum_single i _ (fun k hk => by
      have hne : i ≠ k := hk.symm
      have hne2 : ¬ (k.val + 1 = i.val) := by omega
      simp [qDiffMat, hne, hne2])]
    simp [qDiffMat]
  · simp only [hi, ↓reduceDIte]
    let im1 : Fin n := ⟨i.val - 1, by have := i.isLt; omega⟩
    have hne_im : i ≠ im1 := fun h => by have := congrArg Fin.val h; dsimp [im1] at this; omega
    -- Split sum into k = i and k = im1!
    have hsplit : (fun k => qDiffMat q n i k * M k j) =
        (fun k => (if k = i then M i j else 0) + (if k = im1 then -q * M im1 j else 0)) := by
      funext k
      by_cases hk1 : k = i
      · subst hk1; simp [qDiffMat, hne_im]
      · by_cases hk2 : k = im1
        · subst hk2
          have hadd : im1.val + 1 = i.val := by dsimp [im1]; omega
          simp [qDiffMat, hne_im, hadd, hk1]
        · have hne1 : i ≠ k := fun h => hk1 h.symm
          have hne2 : ¬ (k.val + 1 = i.val) := fun h => hk2 (Fin.ext (by dsimp [im1]; omega))
          simp [qDiffMat, hne1, hne2, hk1, hk2]
    rw [hsplit, finSum_add]
    rw [finSum_single i _ (fun k hk => by simp [hk]),
        finSum_single im1 _ (fun k hk => by simp [hk])]
    simp only [↓reduceIte]
    grind

/-- Explicit entries of `M * (D_q)^T`. -/
theorem matMul_qDiffMat_right {n : Nat} (q : Int) (M : Matrix n) (i j : Fin n) :
    matMul M (matTrans (qDiffMat q n)) i j =
      if _ : j.val = 0 then M i j else M i j - q * M i ⟨j.val - 1, by have := j.isLt; omega⟩ := by
  unfold matMul matTrans
  by_cases hj : j.val = 0
  · simp only [hj, ↓reduceDIte]
    rw [finSum_single j _ (fun k hk => by
      have hne : j ≠ k := hk.symm
      have hne2 : ¬ (k.val + 1 = j.val) := by omega
      simp [qDiffMat, hne, hne2])]
    simp [qDiffMat]
  · simp only [hj, ↓reduceDIte]
    let jm1 : Fin n := ⟨j.val - 1, by have := j.isLt; omega⟩
    have hne_jm : j ≠ jm1 := fun h => by have := congrArg Fin.val h; dsimp [jm1] at this; omega
    have hsplit : (fun k => M i k * qDiffMat q n j k) =
        (fun k => (if k = j then M i j else 0) + (if k = jm1 then M i jm1 * (-q) else 0)) := by
      funext k
      by_cases hk1 : k = j
      · subst hk1; simp [qDiffMat, hne_jm]
      · by_cases hk2 : k = jm1
        · subst hk2
          have hadd : jm1.val + 1 = j.val := by dsimp [jm1]; omega
          simp [qDiffMat, hne_jm, hadd, hk1]
        · have hne1 : j ≠ k := fun h => hk1 h.symm
          have hne2 : ¬ (k.val + 1 = j.val) := fun h => hk2 (Fin.ext (by dsimp [jm1]; omega))
          simp [qDiffMat, hne1, hne2, hk1, hk2]
    rw [hsplit, finSum_add]
    rw [finSum_single j _ (fun k hk => by simp [hk]),
        finSum_single jm1 _ (fun k hk => by simp [hk])]
    simp only [↓reduceIte]
    grind

/-- **Operator A (Universal Rank-1 Affine-Shift Hankel Law):**
    For ANY sequence `a : Nat → Int`, ANY `α β : Int`, and ANY `m : Nat`:
    `det H_{m+1}(α * a + β) = α^(m+1) * det H_{m+1}(a) + β * α^m * det H_m(Δ² a)`. -/
theorem hankel_affine_shift (a : Nat → Int) (α β : Int) (m : Nat) :
    det (hankel (fun k => α * a k + β) (m + 1)) =
      intPow α (m + 1) * det (hankel a (m + 1)) + β * intPow α m * det (hankel (diff2 a) m) := by
  let D := qDiffMat 1 (m + 1)
  let H1 := hankel (fun k => α * a k + β) (m + 1)
  let H0 := hankel (fun k => α * a k) (m + 1)
  let M1 := matMul (matMul D H1) (matTrans D)
  let M0 := matMul (matMul D H0) (matTrans D)
  have h1 : det H1 = det M1 := (det_unit_lower_cong D H1 (isUnitLower_qDiffMat 1 (m + 1))).symm
  have h0 : det H0 = det M0 := (det_unit_lower_cong D H0 (isUnitLower_qDiffMat 1 (m + 1))).symm
  -- Compare M1 and M0 entrywise: they are identical EXCEPT `M1 0 0 = M0 0 0 + β`!
  have hEntry : ∀ i j : Fin (m + 1),
      M1 i j = M0 i j + (if i = 0 ∧ j = 0 then β else 0) := by
    intro i j
    simp only [M1, M0, D, matMul_qDiffMat_right, matMul_qDiffMat_left, H1, H0, hankel]
    by_cases hi : i.val = 0
    · by_cases hj : j.val = 0
      · have hi0 : i = 0 := Fin.ext hi
        have hj0 : j = 0 := Fin.ext hj
        simp [hi0, hj0]
      · have hj0 : j ≠ 0 := fun h => hj (congrArg Fin.val h)
        simp only [hi, hj, hj0, ↓reduceDIte, and_false, ↓reduceIte]; omega
    · have hi0 : i ≠ 0 := fun h => hi (congrArg Fin.val h)
      by_cases hj : j.val = 0
      · simp only [hi, hj, hi0, ↓reduceDIte, false_and, ↓reduceIte]; omega
      · simp only [hi, hj, hi0, ↓reduceDIte, false_and, ↓reduceIte]; omega
  -- Split row 0 of M1 as `M0 0 + β * e_0`
  let e0 : Fin (m + 1) → Int := fun j => if j = 0 then β else 0
  have hM1Split : M1 = setRow M0 0 (fun j => M0 0 j + e0 j) := by
    funext i j; simp only [setRow, hEntry i j]
    by_cases hi : i = 0
    · subst hi; simp [e0]
    · simp [hi]
  have hM0Self : setRow M0 0 (fun j => M0 0 j) = M0 := by
    funext i j; unfold setRow; split <;> simp_all
  rw [show det (hankel (fun k => α * a k + β) (m + 1)) = det H1 from rfl, h1, hM1Split,
      det_row_add, hM0Self, ← h0]
  -- Evaluate term 1: `det H0 = α^(m+1) * det H_{m+1}(a)`
  have hTerm1 : det H0 = intPow α (m + 1) * det (hankel a (m + 1)) := det_smul_all α (hankel a (m + 1))
  -- Evaluate term 2: `det (setRow M0 0 e0) = β * det (minor M0 0)`
  have hTerm2 : det (setRow M0 0 e0) = β * intPow α m * det (hankel (diff2 a) m) := by
    rw [det, finSum_single 0 _ (fun j hj => by simp [setRow, e0, hj])]
    simp only [setRow, e0, ↓reduceIte, Fin.val_zero, altSign_zero, Int.one_mul, minor_setRow_zero]
    have hMin : minor M0 0 = fun i j => α * hankel (diff2 a) m i j := by
      funext i j
      simp only [minor, M0, D, skipIdx_zero, matMul_qDiffMat_right, matMul_qDiffMat_left, H0, hankel]
      have hi : ¬ (i.succ.val = 0) := by simp
      have hj : ¬ (j.succ.val = 0) := by simp
      simp only [Fin.val_succ, Nat.add_sub_cancel, diff2, diff1]
      have h1 : i.val + 1 + (j.val + 1) = (i.val + j.val) + 1 + 1 := by omega
      have h2 : i.val + (j.val + 1) = (i.val + j.val) + 1 := by omega
      have h3 : i.val + 1 + j.val = (i.val + j.val) + 1 := by omega
      rw [h1, h2, h3]
      grind
    rw [hMin, det_smul_all, Int.mul_assoc]
  rw [hTerm1, hTerm2]

/-! ### LSB Even-Odd Permutation and Bit-Slice Block Decomposition -/

theorem eoPerm_left_inv (n : Nat) (i : Fin n) : eoPermInv n (eoPerm n i) = i := by
  apply Fin.ext
  unfold eoPerm eoPermInv
  have hi := i.isLt
  by_cases h : i.val < (n + 1) / 2
  · simp only [h, ↓reduceDIte, Fin.val_mk]
    have hm : (2 * i.val) % 2 = 0 := by omega
    simp only [hm, ↓reduceDIte, Fin.val_mk]; omega
  · simp only [h, ↓reduceDIte, Fin.val_mk]
    have hm : ¬ ((2 * (i.val - (n + 1) / 2) + 1) % 2 = 0) := by omega
    simp only [hm, ↓reduceDIte, Fin.val_mk]; omega

theorem eoPerm_right_inv (n : Nat) (k : Fin n) : eoPerm n (eoPermInv n k) = k := by
  apply Fin.ext
  unfold eoPerm eoPermInv
  have hk := k.isLt
  by_cases h : k.val % 2 = 0
  · simp only [h, ↓reduceDIte, Fin.val_mk]
    have hlt : k.val / 2 < (n + 1) / 2 := by omega
    simp only [hlt, ↓reduceDIte, Fin.val_mk]; omega
  · simp only [h, ↓reduceDIte, Fin.val_mk]
    have hge : ¬ ((n + 1) / 2 + k.val / 2 < (n + 1) / 2) := by omega
    simp only [hge, ↓reduceDIte, Fin.val_mk]; omega

/-- Permuting a Hankel matrix by LSB even-odd indices preserves `det`. -/
theorem det_hankel_eoPerm (a : Nat → Int) (n : Nat) :
    det (hankel a n) = det (fun i j => hankel a n (eoPerm n i) (eoPerm n j)) :=
  (det_perm_cong (hankel a n) (eoPerm n) (eoPermInv n) (eoPerm_left_inv n) (eoPerm_right_inv n)).symm

theorem isUnitLower_blockDiag {p q : Nat} {L1 : Matrix p} {L2 : Matrix q}
    (h1 : IsUnitLower L1) (h2 : IsUnitLower L2) : IsUnitLower (blockDiag L1 L2) := by
  constructor
  · intro i; unfold blockDiag
    by_cases hi : i.val < p
    · simp [hi, h1.1]
    · simp [hi, h2.1]
  · intro i j hij; unfold blockDiag
    by_cases hi : i.val < p
    · by_cases hj : j.val < p
      · simp [hi, hj, h1.2 ⟨i.val, hi⟩ ⟨j.val, hj⟩ hij]
      · simp [hi, hj]
    · have hj : ¬ (j.val < p) := by omega
      simp [hi, hj, h2.2 ⟨i.val - p, by have := i.isLt; omega⟩ ⟨j.val - p, by have := j.isLt; omega⟩ (by dsimp only; omega)]

/-- Explicit entries of `blockDiag(D_q, D_q) * M` on `(p + q') × (p + q')`. -/
theorem matMul_blockDiag_qDiff_left {p r : Nat} (q1 q2 : Int) (M : Matrix (p + r))
    (i j : Fin (p + r)) :
    matMul (blockDiag (qDiffMat q1 p) (qDiffMat q2 r)) M i j =
      if hi : i.val < p then
        if _ : i.val = 0 then M i j
        else M i j - q1 * M ⟨i.val - 1, by omega⟩ j
      else
        if _ : i.val = p then M i j
        else M i j - q2 * M ⟨i.val - 1, by have := i.isLt; omega⟩ j := by
  unfold matMul
  let L := blockDiag (qDiffMat q1 p) (qDiffMat q2 r)
  have hL : ∀ k : Fin (p + r), L i k =
      if k = i then 1
      else if (i.val < p ∧ k.val + 1 = i.val) then -q1
      else if (p < i.val ∧ k.val + 1 = i.val) then -q2
      else 0 := by
    intro k; simp only [L, blockDiag, qDiffMat]
    by_cases hi : i.val < p
    · by_cases hk : k.val < p
      · simp only [hi, hk, ↓reduceDIte]
        by_cases hki : k = i
        · subst hki; simp
        · have hik : (⟨i.val, hi⟩ : Fin p) ≠ ⟨k.val, hk⟩ := fun h => hki (Fin.ext (congrArg Fin.val h).symm)
          have hnotp : ¬ (p < i.val) := by omega
          by_cases hadd : k.val + 1 = i.val
          · simp [hki, hik, hadd]
          · simp [hki, hik, hadd, hnotp]
      · have hki : k ≠ i := fun h => hk (h ▸ hi)
        have hadd : ¬ (k.val + 1 = i.val) := by omega
        simp [hi, hk, hki, hadd]
    · by_cases hk : k.val < p
      · have hki : k ≠ i := fun h => hi (h ▸ hk)
        have hnot : ¬ (p < i.val ∧ k.val + 1 = i.val) := by omega
        simp [hi, hk, hki, hnot]
      · simp only [hi, hk, ↓reduceDIte]
        by_cases hki : k = i
        · subst hki; simp
        · have hik : (⟨i.val - p, by have := i.isLt; omega⟩ : Fin r) ≠ ⟨k.val - p, by have := k.isLt; omega⟩ := fun h =>
            hki (Fin.ext (by have := congrArg Fin.val h; dsimp only at this; omega))
          by_cases hp : p < i.val
          · have hiff : (k.val - p + 1 = i.val - p) ↔ (k.val + 1 = i.val) := by omega
            by_cases hadd : k.val + 1 = i.val
            · have hadd' := hiff.mpr hadd
              simp [hki, hik, hp, hadd, hadd']
            · have hadd' : ¬ (k.val - p + 1 = i.val - p) := fun h => hadd (hiff.mp h)
              simp [hki, hik, hp, hadd, hadd']
          · have hadd' : ¬ (k.val - p + 1 = i.val - p) := by omega
            simp [hki, hik, hp, hadd']
  by_cases hi : i.val < p
  · simp only [hi, ↓reduceDIte]
    by_cases h0 : i.val = 0
    · simp only [h0, ↓reduceDIte]
      rw [finSum_single i _ (fun k hk => by
        rw [show blockDiag (qDiffMat q1 p) (qDiffMat q2 r) i k = L i k from rfl, hL k]
        have : ¬ (k.val + 1 = i.val) := by omega
        simp [hk, this])]
      rw [show blockDiag (qDiffMat q1 p) (qDiffMat q2 r) i i = L i i from rfl, hL i]; simp
    · simp only [h0, ↓reduceDIte]
      let im1 : Fin (p + r) := ⟨i.val - 1, by omega⟩
      have hsplit : (fun k => L i k * M k j) =
          (fun k => (if k = i then M i j else 0) + (if k = im1 then -q1 * M im1 j else 0)) := by
        funext k; rw [hL k]
        by_cases hk1 : k = i
        · subst hk1; have hne : k ≠ im1 := fun h => by have := congrArg Fin.val h; dsimp [im1] at this; omega
          simp [hne]
        · by_cases hk2 : k = im1
          · subst hk2; have hadd : im1.val + 1 = i.val := by dsimp [im1]; omega
            simp [hk1, hi, hadd]
          · have hadd : ¬ (k.val + 1 = i.val) := fun h => hk2 (Fin.ext (by dsimp [im1]; omega))
            simp [hk1, hk2, hadd]
      change finSum (fun k => L i k * M k j) = _
      rw [hsplit, finSum_add, finSum_single i _ (fun k hk => by simp [hk]),
          finSum_single im1 _ (fun k hk => by simp [hk])]
      simp only [↓reduceIte]; grind
  · simp only [hi, ↓reduceDIte]
    by_cases h0 : i.val = p
    · simp only [h0, ↓reduceDIte]
      rw [finSum_single i _ (fun k hk => by
        rw [show blockDiag (qDiffMat q1 p) (qDiffMat q2 r) i k = L i k from rfl, hL k]
        have : ¬ (p < i.val) := by omega
        simp [hk, hi, this])]
      rw [show blockDiag (qDiffMat q1 p) (qDiffMat q2 r) i i = L i i from rfl, hL i]; simp
    · simp only [h0, ↓reduceDIte]
      have hp : p < i.val := by omega
      let im1 : Fin (p + r) := ⟨i.val - 1, by have := i.isLt; omega⟩
      have hsplit : (fun k => L i k * M k j) =
          (fun k => (if k = i then M i j else 0) + (if k = im1 then -q2 * M im1 j else 0)) := by
        funext k; rw [hL k]
        by_cases hk1 : k = i
        · subst hk1; have hne : k ≠ im1 := fun h => by have := congrArg Fin.val h; dsimp [im1] at this; omega
          simp [hne]
        · by_cases hk2 : k = im1
          · subst hk2; have hadd : im1.val + 1 = i.val := by dsimp [im1]; omega
            simp [hk1, hi, hp, hadd]
          · have hadd : ¬ (k.val + 1 = i.val) := fun h => hk2 (Fin.ext (by dsimp [im1]; omega))
            simp [hk1, hk2, hadd]
      change finSum (fun k => L i k * M k j) = _
      rw [hsplit, finSum_add, finSum_single i _ (fun k hk => by simp [hk]),
          finSum_single im1 _ (fun k hk => by simp [hk])]
      simp only [↓reduceIte]; grind

/-- Explicit entries of `M * (blockDiag(D_q1, D_q2))^T`. -/
theorem matMul_blockDiag_qDiff_right {p r : Nat} (q1 q2 : Int) (M : Matrix (p + r))
    (i j : Fin (p + r)) :
    matMul M (matTrans (blockDiag (qDiffMat q1 p) (qDiffMat q2 r))) i j =
      if hj : j.val < p then
        if _ : j.val = 0 then M i j
        else M i j - q1 * M i ⟨j.val - 1, by omega⟩
      else
        if _ : j.val = p then M i j
        else M i j - q2 * M i ⟨j.val - 1, by have := j.isLt; omega⟩ := by
  -- Identical by symmetry of indices
  unfold matMul matTrans
  have hsym := matMul_blockDiag_qDiff_left q1 q2 (matTrans M) j i
  unfold matMul matTrans at hsym
  have hcomm : finSum (fun k => M i k * blockDiag (qDiffMat q1 p) (qDiffMat q2 r) j k) =
               finSum (fun k => blockDiag (qDiffMat q1 p) (qDiffMat q2 r) j k * M i k) := by
    apply finSum_congr; intro k; rw [Int.mul_comm]
  rw [hcomm, hsym]

/-- **Operator B1 (Universal `q`-Geometric Even-Slice Decimation, Even Size `2*(m+1)`):**
    For ANY `c q : Int`, ANY sequence `b : Nat → Int`, if `a(2k) = c * q^k` and `a(2k+1) = b(k)`:
    `det H_{2*(m+1)}(a) = (-1)^(m+1) * (det H_{m+1}(b))^2 + (-1)^m * c^2 * q * (det H_m(Δ_q² b))^2`. -/
theorem hankel_geom_even_even (a b : Nat → Int) (c q : Int)
    (heven : ∀ k, a (2 * k) = c * intPow q k)
    (hodd : ∀ k, a (2 * k + 1) = b k) (m : Nat) :
    det (hankel a ((m + 1) + (m + 1))) =
      altSign (m + 1) * (det (hankel b (m + 1)) * det (hankel b (m + 1))) +
      altSign m * c * c * q * (det (hankel (qDiff q (qDiff q b)) m) * det (hankel (qDiff q (qDiff q b)) m)) := by
  let N := (m + 1) + (m + 1)
  let P : Matrix N := fun i j => hankel a N (eoPerm N i) (eoPerm N j)
  let L : Matrix N := blockDiag (qDiffMat q (m + 1)) (qDiffMat q (m + 1))
  let M : Matrix N := matMul (matMul L P) (matTrans L)
  have hP : det (hankel a N) = det P := det_hankel_eoPerm a N
  have hM : det P = det M := (det_unit_lower_cong L P (isUnitLower_blockDiag (isUnitLower_qDiffMat q _) (isUnitLower_qDiffMat q _))).symm
  -- Helper: compute `P i j` on all 4 quadrants
  have hP_tl : ∀ (i j : Fin N), i.val < m + 1 → j.val < m + 1 → P i j = c * intPow q (i.val + j.val) := by
    intro i j hi hj
    have hhalf : (N + 1) / 2 = m + 1 := by omega
    simp only [P, hankel, eoPerm, hhalf, hi, hj, ↓reduceDIte, Fin.val_mk]
    have h2 : 2 * i.val + 2 * j.val = 2 * (i.val + j.val) := by omega
    rw [h2, heven]
  have hP_br : ∀ (i j : Fin N), ¬ (i.val < m + 1) → ¬ (j.val < m + 1) →
      P i j = c * q * intPow q ((i.val - (m + 1)) + (j.val - (m + 1))) := by
    intro i j hi hj
    have hhalf : (N + 1) / 2 = m + 1 := by omega
    simp only [P, hankel, eoPerm, hhalf, hi, hj, ↓reduceDIte, Fin.val_mk]
    have h2 : 2 * (i.val - (m + 1)) + 1 + (2 * (j.val - (m + 1)) + 1) =
              2 * ((i.val - (m + 1)) + (j.val - (m + 1)) + 1) := by omega
    rw [h2, heven, intPow_add, intPow_one]; grind
  have hP_tr : ∀ (i j : Fin N), i.val < m + 1 → ¬ (j.val < m + 1) →
      P i j = b (i.val + (j.val - (m + 1))) := by
    intro i j hi hj
    have hhalf : (N + 1) / 2 = m + 1 := by omega
    simp only [P, hankel, eoPerm, hhalf, hi, hj, ↓reduceDIte, Fin.val_mk]
    have h2 : 2 * i.val + (2 * (j.val - (m + 1)) + 1) = 2 * (i.val + (j.val - (m + 1))) + 1 := by omega
    rw [h2, hodd]
  have hP_bl : ∀ (i j : Fin N), ¬ (i.val < m + 1) → j.val < m + 1 →
      P i j = b ((i.val - (m + 1)) + j.val) := by
    intro i j hi hj
    have hhalf : (N + 1) / 2 = m + 1 := by omega
    simp only [P, hankel, eoPerm, hhalf, hi, hj, ↓reduceDIte, Fin.val_mk]
    have h2 : 2 * (i.val - (m + 1)) + 1 + 2 * j.val = 2 * ((i.val - (m + 1)) + j.val) + 1 := by omega
    rw [h2, hodd]
  -- Check top-left and bottom-right blocks of M!
  have hM_tl : ∀ i j : Fin N, i.val < m + 1 → j.val < m + 1 →
      M i j = if i.val = 0 ∧ j.val = 0 then c else 0 := by
    intro i j hi hj
    simp only [M, L, matMul_blockDiag_qDiff_right, matMul_blockDiag_qDiff_left, hi, hj, ↓reduceDIte]
    by_cases hi0 : i.val = 0
    · by_cases hj0 : j.val = 0
      · simp only [hi0, hj0, ↓reduceDIte, and_self, ↓reduceIte]
        rw [hP_tl i j hi hj, hi0, hj0]; simp
      · have hj1 : j.val - 1 < m + 1 := by omega
        simp only [hi0, hj0, ↓reduceDIte, and_false, ↓reduceIte]
        rw [hP_tl i j hi hj, hP_tl i ⟨j.val - 1, by omega⟩ hi hj1]
        have hs : i.val + j.val = (i.val + (j.val - 1)) + 1 := by omega
        dsimp only; rw [hs, intPow_add, intPow_one]; grind
    · have hi1 : i.val - 1 < m + 1 := by omega
      by_cases hj0 : j.val = 0
      · simp only [hi0, hj0, ↓reduceDIte, false_and, ↓reduceIte]
        rw [hP_tl i j hi hj, hP_tl ⟨i.val - 1, by omega⟩ j hi1 hj]
        have hs : i.val + j.val = ((i.val - 1) + j.val) + 1 := by omega
        dsimp only; rw [hs, intPow_add, intPow_one]; grind
      · have hj1 : j.val - 1 < m + 1 := by omega
        simp only [hi0, hj0, ↓reduceDIte, false_and, ↓reduceIte]
        rw [hP_tl i j hi hj, hP_tl ⟨i.val - 1, by omega⟩ j hi1 hj,
            hP_tl i ⟨j.val - 1, by omega⟩ hi hj1,
            hP_tl ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩ hi1 hj1]
        dsimp only
        have hs1 : i.val + j.val = ((i.val - 1) + (j.val - 1)) + 2 := by omega
        have hs2 : i.val - 1 + j.val = ((i.val - 1) + (j.val - 1)) + 1 := by omega
        have hs3 : i.val + (j.val - 1) = ((i.val - 1) + (j.val - 1)) + 1 := by omega
        rw [hs1, hs2, hs3]; simp only [intPow_add, intPow]; grind
  have hM_br : ∀ i j : Fin N, m + 1 ≤ i.val → m + 1 ≤ j.val →
      M i j = if i.val = m + 1 ∧ j.val = m + 1 then c * q else 0 := by
    intro i j hi hj
    have hni : ¬ (i.val < m + 1) := by omega
    have hnj : ¬ (j.val < m + 1) := by omega
    simp only [M, L, matMul_blockDiag_qDiff_right, matMul_blockDiag_qDiff_left, hni, hnj, ↓reduceDIte]
    by_cases hi0 : i.val = m + 1
    · by_cases hj0 : j.val = m + 1
      · simp only [hi0, hj0, ↓reduceDIte, and_self, ↓reduceIte]
        rw [hP_br i j hni hnj, hi0, hj0]; simp
      · have hj1 : ¬ (j.val - 1 < m + 1) := by omega
        simp only [hi0, hj0, ↓reduceDIte, and_false, ↓reduceIte]
        rw [hP_br i j hni hnj, hP_br i ⟨j.val - 1, by have := j.isLt; omega⟩ hni hj1]
        dsimp only
        have hs : i.val - (m + 1) + (j.val - (m + 1)) = (i.val - (m + 1) + (j.val - 1 - (m + 1))) + 1 := by omega
        rw [hs, intPow_add, intPow_one]; grind
    · have hi1 : ¬ (i.val - 1 < m + 1) := by omega
      by_cases hj0 : j.val = m + 1
      · simp only [hi0, hj0, ↓reduceDIte, false_and, ↓reduceIte]
        rw [hP_br i j hni hnj, hP_br ⟨i.val - 1, by have := i.isLt; omega⟩ j hi1 hnj]
        dsimp only
        have hs : i.val - (m + 1) + (j.val - (m + 1)) = (i.val - 1 - (m + 1) + (j.val - (m + 1))) + 1 := by omega
        rw [hs, intPow_add, intPow_one]; grind
      · have hj1 : ¬ (j.val - 1 < m + 1) := by omega
        simp only [hi0, hj0, ↓reduceDIte, false_and, ↓reduceIte]
        rw [hP_br i j hni hnj, hP_br ⟨i.val - 1, by have := i.isLt; omega⟩ j hi1 hnj,
            hP_br i ⟨j.val - 1, by have := j.isLt; omega⟩ hni hj1,
            hP_br ⟨i.val - 1, by have := i.isLt; omega⟩ ⟨j.val - 1, by have := j.isLt; omega⟩ hi1 hj1]
        dsimp only
        have hs1 : i.val - (m + 1) + (j.val - (m + 1)) = (i.val - 1 - (m + 1) + (j.val - 1 - (m + 1))) + 2 := by omega
        have hs2 : i.val - 1 - (m + 1) + (j.val - (m + 1)) = (i.val - 1 - (m + 1) + (j.val - 1 - (m + 1))) + 1 := by omega
        have hs3 : i.val - (m + 1) + (j.val - 1 - (m + 1)) = (i.val - 1 - (m + 1) + (j.val - 1 - (m + 1))) + 1 := by omega
        rw [hs1, hs2, hs3]; simp only [intPow_add, intPow]; grind
  -- Check top-right and bottom-left blocks of M equal `D_q * H_{m+1}(b) * D_q^T`!
  let Bmat : Matrix (m + 1) := matMul (matMul (qDiffMat q (m + 1)) (hankel b (m + 1))) (matTrans (qDiffMat q (m + 1)))
  have hM_tr_eq : (fun (i j : Fin (m + 1)) => M ⟨i.val, by omega⟩ ⟨m + 1 + j.val, by omega⟩) = Bmat := by
    funext i j
    have hi := i.isLt; have hj := j.isLt
    have hnj : ¬ (m + 1 + j.val < m + 1) := by omega
    simp only [M, L, Bmat, matMul_blockDiag_qDiff_right, matMul_blockDiag_qDiff_left,
               matMul_qDiffMat_right, matMul_qDiffMat_left, hi, hnj, ↓reduceDIte]
    by_cases hi0 : i.val = 0
    · by_cases hj0 : j.val = 0
      · have hj0' : m + 1 + j.val = m + 1 := by omega
        simp only [hi0, hj0, ↓reduceDIte]
        rw [hP_tr _ _ (by dsimp only; omega) (by dsimp only; omega)]
        simp only [hankel]; congr 1; omega
      · have hj0' : ¬ (m + 1 + j.val = m + 1) := by omega
        simp only [hi0, hj0, hj0', ↓reduceDIte]
        rw [hP_tr _ _ (by dsimp only; omega) (by dsimp only; omega),
            hP_tr _ _ (by dsimp only; omega) (by dsimp only; omega)]
        simp only [hankel]; congr 1
        · congr 1; omega
        · congr 1; congr 1; omega
    · by_cases hj0 : j.val = 0
      · simp only [hi0, hj0, ↓reduceDIte]
        rw [hP_tr _ _ (by dsimp only; omega) (by dsimp only; omega),
            hP_tr _ _ (by dsimp only; omega) (by dsimp only; omega)]
        simp only [hankel]; congr 1
        · congr 1; omega
        · congr 1; congr 1; omega
      · have hj0' : ¬ (m + 1 + j.val = m + 1) := by omega
        simp only [hi0, hj0, hj0', ↓reduceDIte]
        rw [hP_tr _ _ (by dsimp only; omega) (by dsimp only; omega),
            hP_tr _ _ (by dsimp only; omega) (by dsimp only; omega),
            hP_tr _ _ (by dsimp only; omega) (by dsimp only; omega),
            hP_tr _ _ (by dsimp only; omega) (by dsimp only; omega)]
        simp only [hankel]
        have e1 : i.val + (m + 1 + j.val - (m + 1)) = i.val + j.val := by omega
        have e2 : i.val - 1 + (m + 1 + j.val - (m + 1)) = i.val - 1 + j.val := by omega
        have e3 : i.val + (m + 1 + j.val - 1 - (m + 1)) = i.val + (j.val - 1) := by omega
        have e4 : i.val - 1 + (m + 1 + j.val - 1 - (m + 1)) = i.val - 1 + (j.val - 1) := by omega
        rw [e1, e2, e3, e4]
  have hM_bl_eq : (fun (i j : Fin (m + 1)) => M ⟨m + 1 + i.val, by omega⟩ ⟨j.val, by omega⟩) = Bmat := by
    funext i j
    have hi := i.isLt; have hj := j.isLt
    have hni : ¬ (m + 1 + i.val < m + 1) := by omega
    simp only [M, L, Bmat, matMul_blockDiag_qDiff_right, matMul_blockDiag_qDiff_left,
               matMul_qDiffMat_right, matMul_qDiffMat_left, hni, hj, ↓reduceDIte]
    by_cases hi0 : i.val = 0
    · by_cases hj0 : j.val = 0
      · simp only [hi0, hj0, ↓reduceDIte]
        rw [hP_bl _ _ (by dsimp only; omega) (by dsimp only; omega)]
        simp only [hankel]; congr 1; omega
      · simp only [hi0, hj0, ↓reduceDIte]
        rw [hP_bl _ _ (by dsimp only; omega) (by dsimp only; omega),
            hP_bl _ _ (by dsimp only; omega) (by dsimp only; omega)]
        simp only [hankel]; congr 1
        · congr 1; omega
        · congr 1; congr 1; omega
    · have hi0' : ¬ (m + 1 + i.val = m + 1) := by omega
      by_cases hj0 : j.val = 0
      · simp only [hi0, hi0', hj0, ↓reduceDIte]
        rw [hP_bl _ _ (by dsimp only; omega) (by dsimp only; omega),
            hP_bl _ _ (by dsimp only; omega) (by dsimp only; omega)]
        simp only [hankel]; congr 1
        · congr 1; omega
        · congr 1; congr 1; omega
      · simp only [hi0, hi0', hj0, ↓reduceDIte]
        rw [hP_bl _ _ (by dsimp only; omega) (by dsimp only; omega),
            hP_bl _ _ (by dsimp only; omega) (by dsimp only; omega),
            hP_bl _ _ (by dsimp only; omega) (by dsimp only; omega),
            hP_bl _ _ (by dsimp only; omega) (by dsimp only; omega)]
        simp only [hankel]
        have e1 : m + 1 + i.val - (m + 1) + j.val = i.val + j.val := by omega
        have e2 : m + 1 + i.val - 1 - (m + 1) + j.val = i.val - 1 + j.val := by omega
        have e3 : m + 1 + i.val - (m + 1) + (j.val - 1) = i.val + (j.val - 1) := by omega
        have e4 : m + 1 + i.val - 1 - (m + 1) + (j.val - 1) = i.val - 1 + (j.val - 1) := by omega
        rw [e1, e2, e3, e4]
  have hBmat_sub : (fun (i j : Fin m) => Bmat ⟨i.val + 1, by omega⟩ ⟨j.val + 1, by omega⟩) =
      hankel (qDiff q (qDiff q b)) m := by
    funext i j
    simp only [Bmat, matMul_qDiffMat_right, matMul_qDiffMat_left, hankel]
    have hi : ¬ (i.val + 1 = 0) := by omega
    have hj : ¬ (j.val + 1 = 0) := by omega
    simp only [hi, hj, ↓reduceDIte, Nat.add_sub_cancel, qDiff]
    have e1 : i.val + 1 + (j.val + 1) = (i.val + j.val) + 1 + 1 := by omega
    have e2 : i.val + (j.val + 1) = (i.val + j.val) + 1 := by omega
    have e3 : i.val + 1 + j.val = (i.val + j.val) + 1 := by omega
    rw [e1, e2, e3]
  have hM_tr_sub : (fun (i j : Fin m) => M ⟨i.val + 1, by omega⟩ ⟨m + 1 + j.val + 1, by omega⟩) =
      hankel (qDiff q (qDiff q b)) m := by
    rw [← hBmat_sub]; funext i j
    have h := congrFun (congrFun hM_tr_eq ⟨i.val + 1, by omega⟩) ⟨j.val + 1, by omega⟩
    dsimp only at h; rw [← h]
    exact congrArg (M _) (Fin.ext (by dsimp only; omega))
  have hM_bl_sub : (fun (i j : Fin m) => M ⟨m + 1 + i.val + 1, by omega⟩ ⟨j.val + 1, by omega⟩) =
      hankel (qDiff q (qDiff q b)) m := by
    rw [← hBmat_sub]; funext i j
    have h := congrFun (congrFun hM_bl_eq ⟨i.val + 1, by omega⟩) ⟨j.val + 1, by omega⟩
    dsimp only at h; rw [← h]
    exact congrFun (congrArg M (Fin.ext (by dsimp only; omega))) _
  have hBmat_det : det Bmat = det (hankel b (m + 1)) :=
    det_unit_lower_cong (qDiffMat q (m + 1)) (hankel b (m + 1)) (isUnitLower_qDiffMat q (m + 1))
  rw [show det (hankel a ((m + 1) + (m + 1))) = det (hankel a N) from rfl, hP, hM]
  rw [det_rank1_corner_anti M c (c * q) hM_tl hM_br]
  rw [hM_tr_eq, hM_bl_eq, hBmat_det, hM_tr_sub, hM_bl_sub]
  grind

/-- **Operator B2 (Universal `q`-Geometric Even-Slice Decimation, Odd Size `2*m + 1`):**
    For ANY `c q : Int`, ANY sequence `b : Nat → Int`, if `a(2k) = c * q^k` and `a(2k+1) = b(k)`:
    `det H_{2*m+1}(a) = (-1)^m * c * (det H_m(Δ_q b))^2`. -/
theorem hankel_geom_even_odd (a b : Nat → Int) (c q : Int)
    (heven : ∀ k, a (2 * k) = c * intPow q k)
    (hodd : ∀ k, a (2 * k + 1) = b k) (m : Nat) :
    det (hankel a ((m + 1) + m)) =
      altSign m * c * (det (hankel (qDiff q b) m) * det (hankel (qDiff q b) m)) := by
  let N := (m + 1) + m
  let P : Matrix N := fun i j => hankel a N (eoPerm N i) (eoPerm N j)
  -- Use `L = blockDiag (qDiffMat q (m + 1)) (qDiffMat 0 m)` (note `qDiffMat 0 m = I_m`!)
  let L : Matrix N := blockDiag (qDiffMat q (m + 1)) (qDiffMat 0 m)
  let M : Matrix N := matMul (matMul L P) (matTrans L)
  have hP : det (hankel a N) = det P := det_hankel_eoPerm a N
  have hM : det P = det M := (det_unit_lower_cong L P (isUnitLower_blockDiag (isUnitLower_qDiffMat q _) (isUnitLower_qDiffMat 0 _))).symm
  have hP_tl : ∀ (i j : Fin N), i.val < m + 1 → j.val < m + 1 → P i j = c * intPow q (i.val + j.val) := by
    intro i j hi hj
    have hhalf : (N + 1) / 2 = m + 1 := by omega
    simp only [P, hankel, eoPerm, hhalf, hi, hj, ↓reduceDIte, Fin.val_mk]
    have h2 : 2 * i.val + 2 * j.val = 2 * (i.val + j.val) := by omega
    rw [h2, heven]
  have hP_tr : ∀ (i j : Fin N), i.val < m + 1 → ¬ (j.val < m + 1) →
      P i j = b (i.val + (j.val - (m + 1))) := by
    intro i j hi hj
    have hhalf : (N + 1) / 2 = m + 1 := by omega
    simp only [P, hankel, eoPerm, hhalf, hi, hj, ↓reduceDIte, Fin.val_mk]
    have h2 : 2 * i.val + (2 * (j.val - (m + 1)) + 1) = 2 * (i.val + (j.val - (m + 1))) + 1 := by omega
    rw [h2, hodd]
  have hP_bl : ∀ (i j : Fin N), ¬ (i.val < m + 1) → j.val < m + 1 →
      P i j = b ((i.val - (m + 1)) + j.val) := by
    intro i j hi hj
    have hhalf : (N + 1) / 2 = m + 1 := by omega
    simp only [P, hankel, eoPerm, hhalf, hi, hj, ↓reduceDIte, Fin.val_mk]
    have h2 : 2 * (i.val - (m + 1)) + 1 + 2 * j.val = 2 * ((i.val - (m + 1)) + j.val) + 1 := by omega
    rw [h2, hodd]
  have hM_tl : ∀ i j : Fin N, i.val < m + 1 → j.val < m + 1 →
      M i j = if i.val = 0 ∧ j.val = 0 then c else 0 := by
    intro i j hi hj
    simp only [M, L, matMul_blockDiag_qDiff_right, matMul_blockDiag_qDiff_left, hi, hj, ↓reduceDIte]
    by_cases hi0 : i.val = 0
    · by_cases hj0 : j.val = 0
      · simp only [hi0, hj0, ↓reduceDIte, and_self, ↓reduceIte]
        rw [hP_tl i j hi hj, hi0, hj0]; simp
      · have hj1 : j.val - 1 < m + 1 := by omega
        simp only [hi0, hj0, ↓reduceDIte, and_false, ↓reduceIte]
        rw [hP_tl i j hi hj, hP_tl i ⟨j.val - 1, by omega⟩ hi hj1]
        dsimp only; have hs : i.val + j.val = (i.val + (j.val - 1)) + 1 := by omega
        rw [hs, intPow_add, intPow_one]; grind
    · have hi1 : i.val - 1 < m + 1 := by omega
      by_cases hj0 : j.val = 0
      · simp only [hi0, hj0, ↓reduceDIte, false_and, ↓reduceIte]
        rw [hP_tl i j hi hj, hP_tl ⟨i.val - 1, by omega⟩ j hi1 hj]
        dsimp only; have hs : i.val + j.val = ((i.val - 1) + j.val) + 1 := by omega
        rw [hs, intPow_add, intPow_one]; grind
      · have hj1 : j.val - 1 < m + 1 := by omega
        simp only [hi0, hj0, ↓reduceDIte, false_and, ↓reduceIte]
        rw [hP_tl i j hi hj, hP_tl ⟨i.val - 1, by omega⟩ j hi1 hj,
            hP_tl i ⟨j.val - 1, by omega⟩ hi hj1,
            hP_tl ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩ hi1 hj1]
        dsimp only
        have hs1 : i.val + j.val = ((i.val - 1) + (j.val - 1)) + 2 := by omega
        have hs2 : i.val - 1 + j.val = ((i.val - 1) + (j.val - 1)) + 1 := by omega
        have hs3 : i.val + (j.val - 1) = ((i.val - 1) + (j.val - 1)) + 1 := by omega
        rw [hs1, hs2, hs3]; simp only [intPow_add, intPow]; grind
  have hM_tr : (fun (i j : Fin m) => M ⟨i.val + 1, by omega⟩ ⟨m + 1 + j.val, by omega⟩) =
      hankel (qDiff q b) m := by
    funext i j
    have hi : i.val + 1 < m + 1 := by omega
    have hi0 : ¬ (i.val + 1 = 0) := by omega
    have hnj : ¬ (m + 1 + j.val < m + 1) := by omega
    simp only [M, L, matMul_blockDiag_qDiff_right, matMul_blockDiag_qDiff_left, hi, hi0, hnj, ↓reduceDIte]
    by_cases hj0 : m + 1 + j.val = m + 1
    · simp only [hj0, ↓reduceDIte]
      rw [hP_tr _ _ (by dsimp only; omega) (by dsimp only; omega),
          hP_tr _ _ (by dsimp only; omega) (by dsimp only; omega)]
      simp only [hankel, qDiff]
      have e1 : i.val + 1 + (m + 1 - (m + 1)) = i.val + j.val + 1 := by omega
      have e2 : i.val + 1 - 1 + (m + 1 - (m + 1)) = i.val + j.val := by omega
      rw [e1, e2]
    · simp only [hj0, ↓reduceDIte, Int.zero_mul, Int.sub_zero]
      rw [hP_tr _ _ (by dsimp only; omega) (by dsimp only; omega),
          hP_tr _ _ (by dsimp only; omega) (by dsimp only; omega)]
      simp only [hankel, qDiff]
      have e1 : i.val + 1 + (m + 1 + j.val - (m + 1)) = i.val + j.val + 1 := by omega
      have e2 : i.val + 1 - 1 + (m + 1 + j.val - (m + 1)) = i.val + j.val := by omega
      rw [e1, e2]
  have hM_bl : (fun (i j : Fin m) => M ⟨m + 1 + i.val, by omega⟩ ⟨j.val + 1, by omega⟩) =
      hankel (qDiff q b) m := by
    funext i j
    have hj : j.val + 1 < m + 1 := by omega
    have hj0 : ¬ (j.val + 1 = 0) := by omega
    have hni : ¬ (m + 1 + i.val < m + 1) := by omega
    simp only [M, L, matMul_blockDiag_qDiff_right, matMul_blockDiag_qDiff_left, hni, hj, hj0, ↓reduceDIte]
    by_cases hi0 : m + 1 + i.val = m + 1
    · simp only [hi0, ↓reduceDIte]
      rw [hP_bl _ _ (by dsimp only; omega) (by dsimp only; omega),
          hP_bl _ _ (by dsimp only; omega) (by dsimp only; omega)]
      simp only [hankel, qDiff]
      have e1 : m + 1 - (m + 1) + (j.val + 1) = i.val + j.val + 1 := by omega
      have e2 : m + 1 - (m + 1) + (j.val + 1 - 1) = i.val + j.val := by omega
      rw [e1, e2]
    · simp only [hi0, ↓reduceDIte, Int.zero_mul, Int.sub_zero]
      rw [hP_bl _ _ (by dsimp only; omega) (by dsimp only; omega),
          hP_bl _ _ (by dsimp only; omega) (by dsimp only; omega)]
      simp only [hankel, qDiff]
      have e1 : m + 1 + i.val - (m + 1) + (j.val + 1) = i.val + j.val + 1 := by omega
      have e2 : m + 1 + i.val - (m + 1) + (j.val + 1 - 1) = i.val + j.val := by omega
      rw [e1, e2]
  rw [show det (hankel a ((m + 1) + m)) = det (hankel a N) from rfl, hP, hM]
  rw [det_rank1_corner_anti_odd M c hM_tl, hM_tr, hM_bl, Int.mul_assoc]

theorem isUnitLower_blockShearMat (n : Nat) (s : Int) : IsUnitLower (blockShearMat n s) := by
  refine ⟨fun i => by simp [blockShearMat], fun i j hij => ?_⟩
  have hne : i ≠ j := fun h => by subst h; omega
  have hnot : ¬ ((n + 1) / 2 ≤ i.val ∧ j.val = i.val - (n + 1) / 2) := by omega
  simp [blockShearMat, hne, hnot]

theorem matMul_blockShear_left {n : Nat} (s : Int) (M : Matrix n) (i j : Fin n) :
    matMul (blockShearMat n s) M i j =
      if h : (n + 1) / 2 ≤ i.val then
        M i j + s * M ⟨i.val - (n + 1) / 2, by have := i.isLt; omega⟩ j
      else M i j := by
  unfold matMul
  by_cases hi : (n + 1) / 2 ≤ i.val
  · simp only [hi, ↓reduceDIte]
    let i0 : Fin n := ⟨i.val - (n + 1) / 2, by have := i.isLt; omega⟩
    have hne : i ≠ i0 := fun h => by have := congrArg Fin.val h; dsimp [i0] at this; omega
    have hsplit : (fun k => blockShearMat n s i k * M k j) =
        (fun k => (if k = i then M i j else 0) + (if k = i0 then s * M i0 j else 0)) := by
      funext k; simp only [blockShearMat]
      by_cases hk1 : k = i
      · subst hk1; have hne' : k ≠ i0 := fun h => hne h
        simp [hne']
      · by_cases hk2 : k = i0
        · subst hk2; simp [hk1, hne, hi, i0]
        · have hne1 : i ≠ k := fun h => hk1 h.symm
          have hne2 : ¬ ((n + 1) / 2 ≤ i.val ∧ k.val = i.val - (n + 1) / 2) := fun h =>
            hk2 (Fin.ext (by dsimp [i0]; exact h.2))
          simp [hk1, hk2, hne1, hne2]
    rw [hsplit, finSum_add, finSum_single i _ (fun k hk => by simp [hk]),
        finSum_single i0 _ (fun k hk => by simp [hk])]
    simp [i0]
  · simp only [hi, ↓reduceDIte]
    rw [finSum_single i _ (fun k hk => by
      have hne : i ≠ k := hk.symm
      simp [blockShearMat, hne, hi])]
    simp [blockShearMat]

theorem matMul_blockShear_right {n : Nat} (s : Int) (M : Matrix n) (i j : Fin n) :
    matMul M (matTrans (blockShearMat n s)) i j =
      if h : (n + 1) / 2 ≤ j.val then
        M i j + s * M i ⟨j.val - (n + 1) / 2, by have := j.isLt; omega⟩
      else M i j := by
  unfold matMul matTrans
  have hsym := matMul_blockShear_left s (matTrans M) j i
  unfold matMul matTrans at hsym
  have hcomm : finSum (fun k => M i k * blockShearMat n s j k) =
               finSum (fun k => blockShearMat n s j k * M i k) := by
    apply finSum_congr; intro k; rw [Int.mul_comm]
  rw [hcomm, hsym]

/-- **Operator C (Universal `r`-Paired Block-LDU Diagonalization):**
    For ANY `r : Int`, ANY sequence `d : Nat → Int`, and ANY `n : Nat`,
    if `u(2k) = d(k)` and `u(2k+1) = r * d(k)`, then:
    `det H_n(u) = det H_{(n+1)/2}(d) * det H_{n/2}(S d - r^2 d)`. -/
theorem hankel_r_pair (u d : Nat → Int) (r : Int)
    (heven : ∀ k, u (2 * k) = d k)
    (hodd : ∀ k, u (2 * k + 1) = r * d k) (n : Nat) :
    det (hankel u n) =
      det (hankel d ((n + 1) / 2)) * det (hankel (fun k => d (k + 1) - r * r * d k) (n / 2)) := by
  let m0 := (n + 1) / 2
  let m1 := n / 2
  let P : Matrix n := fun i j => hankel u n (eoPerm n i) (eoPerm n j)
  let L : Matrix n := blockShearMat n (-r)
  let M : Matrix n := matMul (matMul L P) (matTrans L)
  have hP : det (hankel u n) = det P := det_hankel_eoPerm u n
  have hM : det P = det M := (det_unit_lower_cong L P (isUnitLower_blockShearMat n (-r))).symm
  have hP_tl : ∀ (i j : Fin n), i.val < m0 → j.val < m0 → P i j = d (i.val + j.val) := by
    intro i j hi hj
    simp only [P, hankel, eoPerm, show (n + 1) / 2 = m0 from rfl, hi, hj, ↓reduceDIte, Fin.val_mk]
    have h2 : 2 * i.val + 2 * j.val = 2 * (i.val + j.val) := by omega
    rw [h2, heven]
  have hP_tr : ∀ (i j : Fin n), i.val < m0 → m0 ≤ j.val → P i j = r * d (i.val + (j.val - m0)) := by
    intro i j hi hj
    have hnj : ¬ (j.val < m0) := by omega
    simp only [P, hankel, eoPerm, show (n + 1) / 2 = m0 from rfl, hi, hnj, ↓reduceDIte, Fin.val_mk]
    have h2 : 2 * i.val + (2 * (j.val - m0) + 1) = 2 * (i.val + (j.val - m0)) + 1 := by omega
    rw [h2, hodd]
  have hP_bl : ∀ (i j : Fin n), m0 ≤ i.val → j.val < m0 → P i j = r * d ((i.val - m0) + j.val) := by
    intro i j hi hj
    have hni : ¬ (i.val < m0) := by omega
    simp only [P, hankel, eoPerm, show (n + 1) / 2 = m0 from rfl, hni, hj, ↓reduceDIte, Fin.val_mk]
    have h2 : 2 * (i.val - m0) + 1 + 2 * j.val = 2 * ((i.val - m0) + j.val) + 1 := by omega
    rw [h2, hodd]
  have hP_br : ∀ (i j : Fin n), m0 ≤ i.val → m0 ≤ j.val → P i j = d ((i.val - m0) + (j.val - m0) + 1) := by
    intro i j hi hj
    have hni : ¬ (i.val < m0) := by omega
    have hnj : ¬ (j.val < m0) := by omega
    simp only [P, hankel, eoPerm, show (n + 1) / 2 = m0 from rfl, hni, hnj, ↓reduceDIte, Fin.val_mk]
    have h2 : 2 * (i.val - m0) + 1 + (2 * (j.val - m0) + 1) = 2 * ((i.val - m0) + (j.val - m0) + 1) := by omega
    rw [h2, heven]
  rw [hP, hM]
  rw [det_block_lower_eq (p := m0) (q := m1) (by omega) M (fun i j hi hj => by
    have hni : ¬ (m0 ≤ i.val) := by omega
    have hj0 : j.val - m0 < m0 := by have := j.isLt; omega
    simp only [M, L, matMul_blockShear_right, matMul_blockShear_left, show (n + 1) / 2 = m0 from rfl,
               hni, hj, ↓reduceDIte]
    rw [hP_tr i j hi hj, hP_tl i ⟨j.val - m0, by omega⟩ hi hj0]; dsimp only; grind)]
  congr 1
  · congr 1; funext i j
    have hi : ¬ (m0 ≤ i.val) := by omega
    have hj : ¬ (m0 ≤ j.val) := by omega
    simp only [M, L, matMul_blockShear_right, matMul_blockShear_left, show (n + 1) / 2 = m0 from rfl,
               hi, hj, ↓reduceDIte]
    rw [hP_tl _ _ i.isLt j.isLt]; rfl
  · congr 1; funext i j
    have hi : m0 ≤ m0 + i.val := by omega
    have hj : m0 ≤ m0 + j.val := by omega
    have hi0 : m0 + i.val - m0 < m0 := by have := i.isLt; omega
    have hj0 : m0 + j.val - m0 < m0 := by have := j.isLt; omega
    have hni0 : ¬ (m0 ≤ m0 + i.val - m0) := by omega
    simp only [M, L, matMul_blockShear_right, matMul_blockShear_left, show (n + 1) / 2 = m0 from rfl,
               hi, hj, ↓reduceDIte]
    rw [hP_br _ _ (by dsimp only; omega) (by dsimp only; omega),
        hP_tr _ _ (by dsimp only; omega) (by dsimp only; omega),
        hP_bl _ _ (by dsimp only; omega) (by dsimp only; omega),
        hP_tl _ _ (by dsimp only; omega) (by dsimp only; omega)]
    simp only [hankel]
    have e1 : m0 + i.val - m0 = i.val := by omega
    have e2 : m0 + j.val - m0 = j.val := by omega
    rw [e1, e2]; grind

/-- **Operator D1 (Universal Level-2 Second-Difference Block-LDU Decimation, Even Size `2*m`):**
    For ANY sequence `d : Nat → Int`, if `v(2k) = -2 * d(k)` and `v(2k+1) = d(k) + d(k+1)`:
    `det H_{2*m}(v) = (-1)^m * (det H_m(Δ d))^2`. -/
theorem hankel_level2_even (v d : Nat → Int)
    (heven : ∀ k, v (2 * k) = -2 * d k)
    (hodd : ∀ k, v (2 * k + 1) = d k + d (k + 1)) (m : Nat) :
    det (hankel v (m + m)) = altSign m * (det (hankel (diff1 d) m) * det (hankel (diff1 d) m)) := by
  let N := m + m
  let P : Matrix N := fun i j => hankel v N (eoPerm N i) (eoPerm N j)
  let L : Matrix N := blockShearMat N 1
  let M : Matrix N := matMul (matMul L P) (matTrans L)
  have hhalf : (N + 1) / 2 = m := by omega
  have hP : det (hankel v N) = det P := det_hankel_eoPerm v N
  have hM : det P = det M := (det_unit_lower_cong L P (isUnitLower_blockShearMat N 1)).symm
  have hP_tl : ∀ (i j : Fin N), i.val < m → j.val < m → P i j = -2 * d (i.val + j.val) := by
    intro i j hi hj
    simp only [P, hankel, eoPerm, hhalf, hi, hj, ↓reduceDIte, Fin.val_mk]
    have h2 : 2 * i.val + 2 * j.val = 2 * (i.val + j.val) := by omega
    rw [h2, heven]
  have hP_tr : ∀ (i j : Fin N), i.val < m → m ≤ j.val → P i j = d (i.val + (j.val - m)) + d (i.val + (j.val - m) + 1) := by
    intro i j hi hj
    have hnj : ¬ (j.val < m) := by omega
    simp only [P, hankel, eoPerm, hhalf, hi, hnj, ↓reduceDIte, Fin.val_mk]
    have h2 : 2 * i.val + (2 * (j.val - m) + 1) = 2 * (i.val + (j.val - m)) + 1 := by omega
    rw [h2, hodd]
  have hP_bl : ∀ (i j : Fin N), m ≤ i.val → j.val < m → P i j = d ((i.val - m) + j.val) + d ((i.val - m) + j.val + 1) := by
    intro i j hi hj
    have hni : ¬ (i.val < m) := by omega
    simp only [P, hankel, eoPerm, hhalf, hni, hj, ↓reduceDIte, Fin.val_mk]
    have h2 : 2 * (i.val - m) + 1 + 2 * j.val = 2 * ((i.val - m) + j.val) + 1 := by omega
    rw [h2, hodd]
  have hP_br : ∀ (i j : Fin N), m ≤ i.val → m ≤ j.val → P i j = -2 * d ((i.val - m) + (j.val - m) + 1) := by
    intro i j hi hj
    have hni : ¬ (i.val < m) := by omega
    have hnj : ¬ (j.val < m) := by omega
    simp only [P, hankel, eoPerm, hhalf, hni, hnj, ↓reduceDIte, Fin.val_mk]
    have h2 : 2 * (i.val - m) + 1 + (2 * (j.val - m) + 1) = 2 * ((i.val - m) + (j.val - m) + 1) := by omega
    rw [h2, heven]
  rw [show det (hankel v (m + m)) = det (hankel v N) from rfl, hP, hM]
  rw [det_block_anti_zero_br M (fun i j hi hj => by
    have hi0 : i.val - m < m := by have := i.isLt; omega
    have hj0 : j.val - m < m := by have := j.isLt; omega
    have hni0 : ¬ (m ≤ i.val - m) := by omega
    simp only [M, L, matMul_blockShear_right, matMul_blockShear_left, hhalf, hi, hj, ↓reduceDIte]
    rw [hP_br i j hi hj, hP_tr ⟨i.val - m, by omega⟩ j hi0 hj,
        hP_bl i ⟨j.val - m, by omega⟩ hi hj0, hP_tl ⟨i.val - m, by omega⟩ ⟨j.val - m, by omega⟩ hi0 hj0]
    dsimp only; grind)]
  have hTR : (fun (i j : Fin m) => M ⟨i.val, by omega⟩ ⟨m + j.val, by omega⟩) = hankel (diff1 d) m := by
    funext i j
    have hni : ¬ (m ≤ i.val) := by omega
    have hj : m ≤ m + j.val := by omega
    have hj0 : m + j.val - m < m := by have := j.isLt; omega
    simp only [M, L, matMul_blockShear_right, matMul_blockShear_left, hhalf, hni, hj, ↓reduceDIte]
    rw [hP_tr _ _ i.isLt hj, hP_tl _ _ i.isLt hj0]
    simp only [hankel, diff1]
    have e : m + j.val - m = j.val := by omega
    rw [e]; grind
  have hBL : (fun (i j : Fin m) => M ⟨m + i.val, by omega⟩ ⟨j.val, by omega⟩) = hankel (diff1 d) m := by
    funext i j
    have hi : m ≤ m + i.val := by omega
    have hnj : ¬ (m ≤ j.val) := by omega
    have hi0 : m + i.val - m < m := by have := i.isLt; omega
    simp only [M, L, matMul_blockShear_right, matMul_blockShear_left, hhalf, hi, hnj, ↓reduceDIte]
    rw [hP_bl _ _ hi j.isLt, hP_tl _ _ hi0 j.isLt]
    simp only [hankel, diff1]
    have e : m + i.val - m = i.val := by omega
    rw [e]; grind
  rw [hTR, hBL, Int.mul_assoc]

/-- **Operator D2 (Universal Level-2 Second-Difference Block-LDU Decimation, Odd Size `2*m + 1`):**
    For ANY sequence `d : Nat → Int`, if `v(2k) = -2 * d(k)` and `v(2k+1) = d(k) + d(k+1)`:
    `det H_{2*m+1}(v) = (-1)^(m+1) * 2 * det H_{m+1}(d) * det H_m(Δ² d)`. -/
theorem hankel_level2_odd (v d : Nat → Int)
    (heven : ∀ k, v (2 * k) = -2 * d k)
    (hodd : ∀ k, v (2 * k + 1) = d k + d (k + 1)) (m : Nat) :
    det (hankel v ((m + 1) + m)) =
      altSign (m + 1) * 2 * det (hankel d (m + 1)) * det (hankel (diff2 d) m) := by
  let N := (m + 1) + m
  let P : Matrix N := fun i j => hankel v N (eoPerm N i) (eoPerm N j)
  let L1 : Matrix N := blockShearMat N 1
  let M1 : Matrix N := matMul (matMul L1 P) (matTrans L1)
  have hhalf : (N + 1) / 2 = m + 1 := by omega
  have hP : det (hankel v N) = det P := det_hankel_eoPerm v N
  have hM1 : det P = det M1 := (det_unit_lower_cong L1 P (isUnitLower_blockShearMat N 1)).symm
  have hP_tl : ∀ (i j : Fin N), i.val < m + 1 → j.val < m + 1 → P i j = -2 * d (i.val + j.val) := by
    intro i j hi hj
    simp only [P, hankel, eoPerm, hhalf, hi, hj, ↓reduceDIte, Fin.val_mk]
    have h2 : 2 * i.val + 2 * j.val = 2 * (i.val + j.val) := by omega
    rw [h2, heven]
  have hP_tr : ∀ (i j : Fin N), i.val < m + 1 → m + 1 ≤ j.val →
      P i j = d (i.val + (j.val - (m + 1))) + d (i.val + (j.val - (m + 1)) + 1) := by
    intro i j hi hj
    have hnj : ¬ (j.val < m + 1) := by omega
    simp only [P, hankel, eoPerm, hhalf, hi, hnj, ↓reduceDIte, Fin.val_mk]
    have h2 : 2 * i.val + (2 * (j.val - (m + 1)) + 1) = 2 * (i.val + (j.val - (m + 1))) + 1 := by omega
    rw [h2, hodd]
  have hP_bl : ∀ (i j : Fin N), m + 1 ≤ i.val → j.val < m + 1 →
      P i j = d ((i.val - (m + 1)) + j.val) + d ((i.val - (m + 1)) + j.val + 1) := by
    intro i j hi hj
    have hni : ¬ (i.val < m + 1) := by omega
    simp only [P, hankel, eoPerm, hhalf, hni, hj, ↓reduceDIte, Fin.val_mk]
    have h2 : 2 * (i.val - (m + 1)) + 1 + 2 * j.val = 2 * ((i.val - (m + 1)) + j.val) + 1 := by omega
    rw [h2, hodd]
  have hP_br : ∀ (i j : Fin N), m + 1 ≤ i.val → m + 1 ≤ j.val →
      P i j = -2 * d ((i.val - (m + 1)) + (j.val - (m + 1)) + 1) := by
    intro i j hi hj
    have hni : ¬ (i.val < m + 1) := by omega
    have hnj : ¬ (j.val < m + 1) := by omega
    simp only [P, hankel, eoPerm, hhalf, hni, hnj, ↓reduceDIte, Fin.val_mk]
    have h2 : 2 * (i.val - (m + 1)) + 1 + (2 * (j.val - (m + 1)) + 1) =
              2 * ((i.val - (m + 1)) + (j.val - (m + 1)) + 1) := by omega
    rw [h2, heven]
  -- Explicit entries of M1 on all 4 quadrants:
  have hM1_tl : ∀ (i j : Fin N), i.val < m + 1 → j.val < m + 1 → M1 i j = -2 * d (i.val + j.val) := by
    intro i j hi hj
    have hni : ¬ (m + 1 ≤ i.val) := by omega
    have hnj : ¬ (m + 1 ≤ j.val) := by omega
    simp only [M1, L1, matMul_blockShear_right, matMul_blockShear_left, hhalf, hni, hnj, ↓reduceDIte]
    exact hP_tl i j hi hj
  have hM1_tr : ∀ (i j : Fin N), i.val < m + 1 → m + 1 ≤ j.val → M1 i j = diff1 d (i.val + (j.val - (m + 1))) := by
    intro i j hi hj
    have hni : ¬ (m + 1 ≤ i.val) := by omega
    have hj0 : j.val - (m + 1) < m + 1 := by have := j.isLt; omega
    simp only [M1, L1, matMul_blockShear_right, matMul_blockShear_left, hhalf, hni, hj, ↓reduceDIte]
    rw [hP_tr i j hi hj, hP_tl i ⟨j.val - (m + 1), by omega⟩ hi hj0]; dsimp only [diff1]; grind
  have hM1_bl : ∀ (i j : Fin N), m + 1 ≤ i.val → j.val < m + 1 → M1 i j = diff1 d ((i.val - (m + 1)) + j.val) := by
    intro i j hi hj
    have hnj : ¬ (m + 1 ≤ j.val) := by omega
    have hi0 : i.val - (m + 1) < m + 1 := by have := i.isLt; omega
    simp only [M1, L1, matMul_blockShear_right, matMul_blockShear_left, hhalf, hi, hnj, ↓reduceDIte]
    rw [hP_bl i j hi hj, hP_tl ⟨i.val - (m + 1), by omega⟩ j hi0 hj]; dsimp only [diff1]; grind
  have hM1_br : ∀ (i j : Fin N), m + 1 ≤ i.val → m + 1 ≤ j.val → M1 i j = 0 := by
    intro i j hi hj
    have hi0 : i.val - (m + 1) < m + 1 := by have := i.isLt; omega
    have hj0 : j.val - (m + 1) < m + 1 := by have := j.isLt; omega
    have hni0 : ¬ (m + 1 ≤ i.val - (m + 1)) := by omega
    simp only [M1, L1, matMul_blockShear_right, matMul_blockShear_left, hhalf, hi, hj, ↓reduceDIte]
    rw [hP_br i j hi hj, hP_bl i ⟨j.val - (m + 1), by omega⟩ hi hj0,
        hP_tr ⟨i.val - (m + 1), by omega⟩ j hi0 hj,
        hP_tl ⟨i.val - (m + 1), by omega⟩ ⟨j.val - (m + 1), by omega⟩ hi0 hj0]
    dsimp only; grind
  -- Step 2: Left-multiply M1 by unit lower-triangular `L2 = blockDiag (qDiffMat 1 (m+1)) (qDiffMat 0 m)`!
  let L2 : Matrix N := blockDiag (qDiffMat 1 (m + 1)) (qDiffMat 0 m)
  let M2 : Matrix N := matMul L2 M1
  have hM2 : det M1 = det M2 := (det_unit_lower_mul L2 M1 (isUnitLower_blockDiag (isUnitLower_qDiffMat 1 _) (isUnitLower_qDiffMat 0 _))).symm
  -- Step 3: Add `2 * row (m + i)` to `row i` for `1 ≤ i ≤ m` (preserves `det` via `det_row_shear`!)
  let M3 : Matrix N := fun i j =>
    if h : 1 ≤ i.val ∧ i.val < m + 1 then M2 i j + 2 * M2 ⟨m + i.val, by omega⟩ j else M2 i j
  have hM3 : det M2 = det M3 := by
    suffices h : ∀ (k : Nat) (hk : k ≤ m),
        det (fun i j => if h : 1 ≤ i.val ∧ i.val ≤ k then M2 i j + 2 * M2 ⟨m + i.val, by omega⟩ j else M2 i j) = det M2 by
      have hres := h m (Nat.le_refl m)
      have hEq : (fun i j => if h : 1 ≤ i.val ∧ i.val ≤ m then M2 i j + 2 * M2 ⟨m + i.val, by omega⟩ j else M2 i j) = M3 := by
        funext i j; simp only [M3]
        by_cases hc : 1 ≤ i.val ∧ i.val ≤ m
        · have hc' : 1 ≤ i.val ∧ i.val < m + 1 := by omega
          simp [hc, hc']
        · have hc' : ¬ (1 ≤ i.val ∧ i.val < m + 1) := by omega
          simp [hc, hc']
      rw [hEq] at hres; exact hres.symm
    intro k
    induction k with
    | zero =>
      intro _
      have hEq : (fun i j => if h : 1 ≤ i.val ∧ i.val ≤ 0 then M2 i j + 2 * M2 ⟨m + i.val, by omega⟩ j else M2 i j) = M2 := by
        funext i j
        have h0 : ¬ (1 ≤ i.val ∧ i.val ≤ 0) := by omega
        simp only [h0, ↓reduceDIte]
      rw [hEq]
    | succ k ih =>
      intro hk
      let prev : Matrix N := fun i j => if h : 1 ≤ i.val ∧ i.val ≤ k then M2 i j + 2 * M2 ⟨m + i.val, by omega⟩ j else M2 i j
      let p : Fin N := ⟨k + 1, by omega⟩
      let qIdx : Fin N := ⟨m + (k + 1), by omega⟩
      have hne : p ≠ qIdx := fun h => by have := congrArg Fin.val h; dsimp [p, qIdx] at this; omega
      have hEq : (fun i j => if h : 1 ≤ i.val ∧ i.val ≤ k + 1 then M2 i j + 2 * M2 ⟨m + i.val, by omega⟩ j else M2 i j) =
          setRow prev p (fun j => prev p j + 2 * prev qIdx j) := by
        funext i j; simp only [setRow, prev]
        by_cases hip : i = p
        · subst hip
          have h1a : 1 ≤ p.val := by dsimp [p]; omega
          have h1b : p.val ≤ k + 1 := by dsimp [p]; omega
          have h2b : ¬ (p.val ≤ k) := by dsimp [p]; omega
          have h3 : ¬ (1 ≤ qIdx.val ∧ qIdx.val ≤ k) := by dsimp [qIdx]; omega
          simp only [h1a, h1b, h2b, h3, and_self, and_false, ↓reduceIte, ↓reduceDIte]
          rfl
        · have hiv : i.val ≠ k + 1 := fun h => hip (Fin.ext h)
          have hiff : (1 ≤ i.val ∧ i.val ≤ k + 1) ↔ (1 ≤ i.val ∧ i.val ≤ k) := by omega
          by_cases h1 : 1 ≤ i.val ∧ i.val ≤ k + 1
          · have h2 := hiff.mp h1; simp [hip, h1, h2]
          · have h2 : ¬ (1 ≤ i.val ∧ i.val ≤ k) := fun h => h1 (hiff.mpr h)
            simp [hip, h1, h2]
      rw [hEq, det_row_shear prev p qIdx hne 2, ih (by omega)]
  -- Check entries of M3!
  have hM2_row_ge : ∀ (i j : Fin N), m + 1 ≤ i.val → M2 i j = M1 i j := by
    intro i j hi
    have hni : ¬ (i.val < m + 1) := by omega
    simp only [M2, L2, matMul_blockDiag_qDiff_left, hni, ↓reduceDIte]
    split <;> simp
  have hM3_mid_left : ∀ (i j : Fin N), 1 ≤ i.val → i.val < m + 1 → j.val < m + 1 → M3 i j = 0 := by
    intro i j hi1 hi2 hj
    have hi0 : ¬ (i.val = 0) := by omega
    simp only [M3, hi1, hi2, and_self, ↓reduceDIte]
    rw [hM2_row_ge ⟨m + i.val, by omega⟩ j (by dsimp only; omega)]
    simp only [M2, L2, matMul_blockDiag_qDiff_left, hi2, hi0, ↓reduceDIte]
    rw [hM1_tl i j hi2 hj, hM1_tl ⟨i.val - 1, by omega⟩ j (by dsimp only; omega) hj,
        hM1_bl ⟨m + i.val, by omega⟩ j (by dsimp only; omega) hj]
    dsimp only [diff1]
    have e1 : m + i.val - (m + 1) + j.val = i.val - 1 + j.val := by omega
    have e2 : i.val + j.val = (i.val - 1 + j.val) + 1 := by omega
    rw [e1, e2]; grind
  have hM3_mid_right : ∀ (i j : Fin N), 1 ≤ i.val → i.val < m + 1 → m + 1 ≤ j.val →
      M3 i j = diff2 d ((i.val - 1) + (j.val - (m + 1))) := by
    intro i j hi1 hi2 hj
    have hi0 : ¬ (i.val = 0) := by omega
    simp only [M3, hi1, hi2, and_self, ↓reduceDIte]
    rw [hM2_row_ge ⟨m + i.val, by omega⟩ j (by dsimp only; omega)]
    rw [hM1_br ⟨m + i.val, by omega⟩ j (by dsimp only; omega) hj]
    simp only [M2, L2, matMul_blockDiag_qDiff_left, hi2, hi0, ↓reduceDIte, Int.mul_zero, Int.add_zero]
    rw [hM1_tr i j hi2 hj, hM1_tr ⟨i.val - 1, by omega⟩ j (by dsimp only; omega) hj]
    dsimp only [diff2, diff1]
    have e : i.val + (j.val - (m + 1)) = (i.val - 1 + (j.val - (m + 1))) + 1 := by omega
    rw [e]; grind
  let M4 : Matrix N := fun i j =>
    M3 (if h : i.val < m then ⟨i.val + 1, by omega⟩ else if i.val = m then 0 else i) j
  have hM4_to_M3 : det M3 = altSign m * det M4 := by
    have hN1 : N = (m + m) + 1 := by omega
    let M4' : Matrix ((m + m) + 1) := fun i j => M4 ⟨i.val, by omega⟩ ⟨j.val, by omega⟩
    let M3' : Matrix ((m + m) + 1) := fun i j => M3 ⟨i.val, by omega⟩ ⟨j.val, by omega⟩
    rw [← det_cast hN1 M3, ← det_cast hN1 M4]
    change det M3' = altSign m * det M4'
    have hcyc := det_row_cycle_to_zero M4' ⟨m, by omega⟩
    have hEq : M3' = fun i j => M4' (if i.val = 0 then ⟨m, by omega⟩ else if i.val ≤ m then ⟨i.val - 1, by omega⟩ else i) j := by
      funext i j; simp only [M3', M4', M4]; congr 1; apply Fin.ext
      by_cases h0 : i.val = 0
      · have hm : ¬ (m < m) := by omega
        simp [h0, hm]
      · by_cases hle : i.val ≤ m
        · have hlt : i.val - 1 < m := by omega
          simp [h0, hle, hlt]; omega
        · have hnot1 : ¬ (i.val < m) := by omega
          have hnot2 : ¬ (i.val = m) := by omega
          simp [h0, hle, hnot1, hnot2]
    rw [hEq, hcyc]
  let M5 : Matrix N := fun i j =>
    M4 i (if h : j.val < m then ⟨m + 1 + j.val, by omega⟩ else ⟨j.val - m, by have := j.isLt; omega⟩)
  have hM5 : det M5 = det M4 := by
    have hcs := det_col_block_swap (p := m + 1) (q := m) M4
    change det M5 = altSign ((m + 1) * m) * det M4 at hcs
    have heven : ((m + 1) * m) % 2 = 0 := by
      by_cases hm : m % 2 = 0
      · rw [Nat.mul_mod, hm]; simp
      · have hm1 : (m + 1) % 2 = 0 := by omega
        rw [Nat.mul_mod, hm1]; simp
    have hs1 : altSign ((m + 1) * m) = 1 := by unfold altSign; simp [heven]
    rw [hs1, Int.one_mul] at hcs
    exact hcs
  have hM5_bl : det M5 = det (hankel (diff2 d) m) * (-2 * det (hankel d (m + 1))) := by
    rw [det_block_lower_eq (p := m) (q := m + 1) (by omega) M5 (fun i j hi hj => by
      have hnj : ¬ (j.val < m) := by omega
      simp only [M5, M4, hi, hnj, ↓reduceDIte]
      exact hM3_mid_left ⟨i.val + 1, by omega⟩ ⟨j.val - m, by have := j.isLt; omega⟩
        (by dsimp only; omega) (by dsimp only; omega) (by have := j.isLt; dsimp only; omega))]
    congr 1
    · congr 1; funext i j
      simp only [M5, M4, i.isLt, j.isLt, ↓reduceDIte]
      rw [hM3_mid_right ⟨i.val + 1, by omega⟩ ⟨m + 1 + j.val, by omega⟩
          (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)]
      simp only [hankel]; congr 1; omega
    · let R : Matrix (m + 1) := fun i j => M5 ⟨m + i.val, by omega⟩ ⟨m + j.val, by omega⟩
      let S : Matrix (m + 1) := matMul (qDiffMat 1 (m + 1)) (hankel d (m + 1))
      have hR_eq : R = setRow S 0 (fun j => -2 * S 0 j) := by
        funext i j
        have hni : ¬ (m + i.val < m) := by omega
        have hnj : ¬ (m + j.val < m) := by omega
        simp only [R, M5, M4, hni, hnj, ↓reduceDIte, setRow, S, matMul_qDiffMat_left, hankel]
        by_cases hi0 : i = 0
        · subst hi0
          have h0m : m + (0 : Fin (m + 1)).val = m := by simp
          simp only [h0m, ↓reduceIte]
          have hnot0 : ¬ (1 ≤ 0) := by omega
          have h0lt0 : 0 < m + 1 := by omega
          simp only [M3, M2, L2, matMul_blockDiag_qDiff_left, Fin.val_zero, hnot0, false_and, h0lt0, ↓reduceDIte]
          rw [hM1_tl 0 ⟨m + j.val - m, by omega⟩ (by simp) (by dsimp only; omega)]
          simp only [Fin.val_zero]; congr 1; congr 1; omega
        · have hiv : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
          have hne_m : ¬ (m + i.val = m) := by omega
          have hnot : ¬ (1 ≤ m + i.val ∧ m + i.val < m + 1) := by omega
          simp only [hi0, hiv, hne_m, M3, hnot, ↓reduceIte, ↓reduceDIte]
          rw [hM2_row_ge ⟨m + i.val, by omega⟩ ⟨m + j.val - m, by omega⟩ (by dsimp only; omega)]
          rw [hM1_bl ⟨m + i.val, by omega⟩ ⟨m + j.val - m, by omega⟩ (by dsimp only; omega) (by dsimp only; omega)]
          dsimp only [diff1]
          have e1 : m + i.val - (m + 1) + (m + j.val - m) = i.val - 1 + j.val := by omega
          have e2 : i.val + j.val = (i.val - 1 + j.val) + 1 := by omega
          rw [e1, e2]; grind
      change det R = -2 * det (hankel d (m + 1))
      rw [hR_eq, det_row_smul]
      have hS0 : setRow S 0 (fun j => S 0 j) = S := by funext i j; unfold setRow; split <;> simp_all
      rw [hS0, det_unit_lower_mul (qDiffMat 1 (m + 1)) (hankel d (m + 1)) (isUnitLower_qDiffMat 1 (m + 1))]
  rw [show det (hankel v ((m + 1) + m)) = det (hankel v N) from rfl,
      hP, hM1, hM2, hM3, hM4_to_M3, ← hM5, hM5_bl, altSign_succ]
  grind


/-! ### Generic Hankel Helpers & Elementary Bitwise Functions -/

theorem det_hankel_eq (f : Nat → Int) {n1 n2 : Nat} (h : n1 = n2) :
    det (hankel f n1) = det (hankel f n2) := by
  subst h; rfl

theorem det_hankel_congr {f g : Nat → Int} (h : ∀ k, f k = g k) (n : Nat) :
    det (hankel f n) = det (hankel g n) := by
  congr 1; funext i j; exact h (i.val + j.val)

theorem det_hankel_scale (α : Int) (f : Nat → Int) (n : Nat) :
    det (hankel (fun k => α * f k) n) = intPow α n * det (hankel f n) :=
  det_smul_all α (hankel f n)

theorem intPow_two_mul (x : Int) (m : Nat) : intPow x (2 * m) = intPow x m * intPow x m := by
  have h : 2 * m = m + m := by omega
  rw [h, intPow_add]

theorem intPow_one_base (k : Nat) : intPow 1 k = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [intPow, ih]

theorem intPow_neg_one (k : Nat) : intPow (-1) k = altSign k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [intPow, ih, altSign_succ]; grind

theorem intPow_neg_one_even (k : Nat) : intPow (-1) (2 * k) = 1 := by
  rw [intPow_neg_one]; unfold altSign; simp

theorem intPow_odd (x : Int) (hx : x % 2 = 1) (k : Nat) : intPow x k % 2 = 1 := by
  induction k with
  | zero => simp [intPow]
  | succ k ih => rw [intPow, Int.mul_emod, ih, hx]; rfl

theorem intPow_two_pos (k : Nat) : 0 < intPow 2 k := by
  induction k with
  | zero => simp [intPow]
  | succ k ih => rw [intPow]; omega

theorem nat_strong_ind {P : Nat → Prop} (h : ∀ n, (∀ k, k < n → P k) → P n) (n : Nat) : P n := by
  suffices ∀ m k, k ≤ m → P k from this n n (Nat.le_refl n)
  intro m
  induction m with
  | zero => intro k hk; apply h; intro j hj; omega
  | succ m ih =>
    intro k hk
    by_cases hkm : k ≤ m
    · exact ih k hkm
    · apply h; intro j hj; exact ih j (by omega)

theorem v2_odd (k : Nat) : v2 (2 * k + 1) = 0 := by
  rw [v2]; simp

theorem v2_even_succ (k : Nat) : v2 (2 * (k + 1)) = 1 + v2 (k + 1) := by
  have h1 : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
  rw [h1, v2]
  have he : ((2 * k + 1) + 1) % 2 = 0 := by omega
  have hd : ((2 * k + 1) + 1) / 2 = k + 1 := by omega
  simp [he, hd]

theorem popcount_zero : popcount 0 = 0 := by
  rw [popcount]; simp

theorem popcount_even (k : Nat) : popcount (2 * k) = popcount k := by
  by_cases hk : k = 0
  · subst hk; simp
  · rw [popcount]
    have hne : 2 * k ≠ 0 := by omega
    have hm : (2 * k) % 2 = 0 := by omega
    have hd : (2 * k) / 2 = k := by omega
    simp [hne, hm, hd]

theorem popcount_odd (k : Nat) : popcount (2 * k + 1) = 1 + popcount k := by
  rw [popcount]
  have hm : (2 * k + 1) % 2 = 1 := by omega
  have hd : (2 * k + 1) / 2 = k := by omega
  simp [hm, hd]

/-! ### The 3-Parameter Binary-Valuation Automatic Family `ecSeq c α β` -/

theorem ecSeq_zero (c α β : Int) : ecSeq c α β 0 = c := by
  rw [ecSeq]; simp

theorem ecSeq_even (c α β : Int) (k : Nat) : ecSeq c α β (2 * k) = c := by
  rw [ecSeq]
  by_cases hk : k = 0
  · subst hk; simp
  · have hne : 2 * k ≠ 0 := by omega
    have hm : (2 * k) % 2 = 0 := by omega
    simp [hne, hm]

theorem ecSeq_odd (c α β : Int) (k : Nat) :
    ecSeq c α β (2 * k + 1) = α * ecSeq c α β k + β := by
  rw [ecSeq]
  have hd : (2 * k + 1) / 2 = k := by omega
  simp [hd]

/-- Pointwise identification: `ecSeq 0 1 1` is the exact ruler sequence `v2(n + 1)`. -/
theorem ecSeq_ruler_eq_v2 (n : Nat) : ecSeq 0 1 1 n = (v2 (n + 1) : Int) := by
  induction n using nat_strong_ind with
  | h n ih =>
    by_cases hp : n % 2 = 0
    · have hk : n = 2 * (n / 2) := by omega
      rw [hk, ecSeq_even, v2_odd]; rfl
    · have hk : n = 2 * (n / 2) + 1 := by omega
      have hsucc : 2 * (n / 2) + 1 + 1 = 2 * (n / 2 + 1) := by omega
      rw [hk, ecSeq_odd, hsucc, v2_even_succ, ih (n / 2) (by omega)]
      omega

/-- Pointwise identification: `ecSeq 1 1 1` is the shifted ruler sequence `1 + v2(n + 1)`. -/
theorem ecSeq_shifted_ruler_eq_v2 (n : Nat) : ecSeq 1 1 1 n = 1 + (v2 (n + 1) : Int) := by
  induction n using nat_strong_ind with
  | h n ih =>
    by_cases hp : n % 2 = 0
    · have hk : n = 2 * (n / 2) := by omega
      rw [hk, ecSeq_even, v2_odd]; rfl
    · have hk : n = 2 * (n / 2) + 1 := by omega
      have hsucc : 2 * (n / 2) + 1 + 1 = 2 * (n / 2 + 1) := by omega
      rw [hk, ecSeq_odd, hsucc, v2_even_succ, ih (n / 2) (by omega)]
      omega

/-- Pointwise identification: `ecSeq 1 (-1) 0` is the signed ruler `(-1)^{v2(n + 1)}`. -/
theorem ecSeq_signed_ruler_eq_v2 (n : Nat) : ecSeq 1 (-1) 0 n = altSign (v2 (n + 1)) := by
  induction n using nat_strong_ind with
  | h n ih =>
    by_cases hp : n % 2 = 0
    · have hk : n = 2 * (n / 2) := by omega
      rw [hk, ecSeq_even, v2_odd]; rfl
    · have hk : n = 2 * (n / 2) + 1 := by omega
      have hsucc : 2 * (n / 2) + 1 + 1 = 2 * (n / 2 + 1) := by omega
      rw [hk, ecSeq_odd, hsucc, v2_even_succ, ih (n / 2) (by omega)]
      have h1 : 1 + v2 (n / 2 + 1) = v2 (n / 2 + 1) + 1 := by omega
      rw [h1, altSign_succ]; grind

/-- Pointwise affine link between signed ruler and period-doubling: `(-1)^{v2(n+1)} = 2 * pd(n) - 1`. -/
theorem ecSeq_signed_ruler_eq_pd (n : Nat) :
    ecSeq 1 (-1) 0 n = 2 * ecSeq 1 (-1) 1 n + (-1) := by
  induction n using nat_strong_ind with
  | h n ih =>
    by_cases hp : n % 2 = 0
    · have hk : n = 2 * (n / 2) := by omega
      rw [hk, ecSeq_even, ecSeq_even]; rfl
    · have hk : n = 2 * (n / 2) + 1 := by omega
      rw [hk, ecSeq_odd, ecSeq_odd, ih (n / 2) (by omega)]; grind

/-- Pointwise identification: `ecSeq 1 r 0` is the exponential ruler `r^{v2(n + 1)}`. -/
theorem ecSeq_exp_ruler_eq_v2 (r : Int) (n : Nat) :
    ecSeq 1 r 0 n = intPow r (v2 (n + 1)) := by
  induction n using nat_strong_ind with
  | h n ih =>
    by_cases hp : n % 2 = 0
    · have hk : n = 2 * (n / 2) := by omega
      rw [hk, ecSeq_even, v2_odd]; rfl
    · have hk : n = 2 * (n / 2) + 1 := by omega
      have hsucc : 2 * (n / 2) + 1 + 1 = 2 * (n / 2 + 1) := by omega
      rw [hk, ecSeq_odd, hsucc, v2_even_succ, ih (n / 2) (by omega)]
      have h1 : 1 + v2 (n / 2 + 1) = v2 (n / 2 + 1) + 1 := by omega
      rw [h1, intPow]; grind

/-! ### Theorem 1: The Exact Closed 3-State Bit-Slice Recurrence over `Int` -/

theorem hankelA_zero (c α β : Int) : hankelA c α β 0 = 1 := rfl

theorem hankelB_zero (c α β : Int) : hankelB c α β 0 = 1 := rfl

theorem hankelC_zero (c α β : Int) : hankelC c α β 0 = 1 := rfl

/-- Exact 1-step decimation of `A_{2m+1}` via Operator B2. -/
theorem hankelA_odd (c α β : Int) (m : Nat) :
    hankelA c α β (2 * m + 1) =
      altSign m * c * intPow α (2 * m) * (hankelB c α β m * hankelB c α β m) := by
  let a := ecSeq c α β
  let b : Nat → Int := fun k => α * a k + β
  have h1 := hankel_geom_even_odd a b c 1
    (fun k => by rw [intPow_one_base, Int.mul_one]; exact ecSeq_even c α β k)
    (fun k => ecSeq_odd c α β k) m
  have hsz : 2 * m + 1 = (m + 1) + m := by omega
  have hq : ∀ k, qDiff 1 b k = α * diff1 a k := by
    intro k; simp only [qDiff, b, diff1]; grind
  rw [hankelA, det_hankel_eq a hsz, h1, det_hankel_congr hq m, det_hankel_scale, intPow_two_mul]
  grind

/-- Exact 1-step decimation of `A_{2(m+1)}` via Operators B1 and A. -/
theorem hankelA_even (c α β : Int) (m : Nat) :
    hankelA c α β (2 * (m + 1)) =
      altSign (m + 1) *
        ((intPow α (m + 1) * hankelA c α β (m + 1) + β * intPow α m * hankelC c α β m) *
         (intPow α (m + 1) * hankelA c α β (m + 1) + β * intPow α m * hankelC c α β m)) +
      altSign m * (c * c) * intPow α (2 * m) * (hankelC c α β m * hankelC c α β m) := by
  let a := ecSeq c α β
  let b : Nat → Int := fun k => α * a k + β
  have h1 := hankel_geom_even_even a b c 1
    (fun k => by rw [intPow_one_base, Int.mul_one]; exact ecSeq_even c α β k)
    (fun k => ecSeq_odd c α β k) m
  have hsz : 2 * (m + 1) = (m + 1) + (m + 1) := by omega
  have hq2 : ∀ k, qDiff 1 (qDiff 1 b) k = α * diff2 a k := by
    intro k; simp only [qDiff, b, diff2, diff1]; grind
  have hb : det (hankel b (m + 1)) =
      intPow α (m + 1) * det (hankel a (m + 1)) + β * intPow α m * det (hankel (diff2 a) m) :=
    hankel_affine_shift a α β m
  rw [hankelA, det_hankel_eq a hsz, h1, hb, det_hankel_congr hq2 m, det_hankel_scale, intPow_two_mul]
  grind

/-- Exact 1-step decimation of `B_{2(m+1)}` via Operators C and A. -/
theorem hankelB_even (c α β : Int) (m : Nat) :
    hankelB c α β (2 * (m + 1)) =
      (intPow α (m + 1) * hankelA c α β (m + 1) + (β - c) * intPow α m * hankelC c α β m) *
      (intPow α (m + 1) * hankelB c α β (m + 1)) := by
  let a := ecSeq c α β
  let d : Nat → Int := fun k => α * a k + (β - c)
  have hC := hankel_r_pair (diff1 a) d (-1)
    (fun k => by simp only [diff1, d, a]; rw [ecSeq_odd, ecSeq_even]; grind)
    (fun k => by
      simp only [diff1, d, a]
      have h2 : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
      rw [h2, ecSeq_even, ecSeq_odd]; grind)
    (2 * (m + 1))
  have h0 : (2 * (m + 1) + 1) / 2 = m + 1 := by omega
  have h1 : (2 * (m + 1)) / 2 = m + 1 := by omega
  have hsub : ∀ k, d (k + 1) - (-1) * (-1) * d k = α * diff1 a k := by
    intro k; simp only [d, diff1]; grind
  have hd : det (hankel d (m + 1)) =
      intPow α (m + 1) * det (hankel a (m + 1)) + (β - c) * intPow α m * det (hankel (diff2 a) m) :=
    hankel_affine_shift a α (β - c) m
  rw [hankelB, hC, det_hankel_eq d h0, det_hankel_eq _ h1, hd, det_hankel_congr hsub (m + 1), det_hankel_scale]

/-- Exact 1-step decimation of `B_{2m+1}` via Operators C and A. -/
theorem hankelB_odd (c α β : Int) (m : Nat) :
    hankelB c α β (2 * m + 1) =
      (intPow α (m + 1) * hankelA c α β (m + 1) + (β - c) * intPow α m * hankelC c α β m) *
      (intPow α m * hankelB c α β m) := by
  let a := ecSeq c α β
  let d : Nat → Int := fun k => α * a k + (β - c)
  have hC := hankel_r_pair (diff1 a) d (-1)
    (fun k => by simp only [diff1, d, a]; rw [ecSeq_odd, ecSeq_even]; grind)
    (fun k => by
      simp only [diff1, d, a]
      have h2 : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
      rw [h2, ecSeq_even, ecSeq_odd]; grind)
    (2 * m + 1)
  have h0 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
  have h1 : (2 * m + 1) / 2 = m := by omega
  have hsub : ∀ k, d (k + 1) - (-1) * (-1) * d k = α * diff1 a k := by
    intro k; simp only [d, diff1]; grind
  have hd : det (hankel d (m + 1)) =
      intPow α (m + 1) * det (hankel a (m + 1)) + (β - c) * intPow α m * det (hankel (diff2 a) m) :=
    hankel_affine_shift a α (β - c) m
  rw [hankelB, hC, det_hankel_eq d h0, det_hankel_eq _ h1, hd, det_hankel_congr hsub m, det_hankel_scale]

/-- Exact 1-step decimation of `C_{2m}` via Operator D1. -/
theorem hankelC_even (c α β : Int) (m : Nat) :
    hankelC c α β (2 * m) =
      altSign m * intPow α (2 * m) * (hankelB c α β m * hankelB c α β m) := by
  let a := ecSeq c α β
  let d : Nat → Int := fun k => α * a k + (β - c)
  have hD := hankel_level2_even (diff2 a) d
    (fun k => by
      simp only [diff2, diff1, d, a]
      have h2 : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
      rw [h2, ecSeq_even, ecSeq_odd, ecSeq_even]; grind)
    (fun k => by
      simp only [diff2, diff1, d, a]
      have h2 : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
      have h3 : 2 * k + 1 + 1 + 1 = 2 * (k + 1) + 1 := by omega
      rw [h3, h2, ecSeq_odd, ecSeq_even, ecSeq_odd]; grind)
    m
  have hsz : 2 * m = m + m := by omega
  have hd1 : ∀ k, diff1 d k = α * diff1 a k := by
    intro k; simp only [diff1, d]; grind
  rw [hankelC, det_hankel_eq (diff2 a) hsz, hD, det_hankel_congr hd1 m, det_hankel_scale, intPow_two_mul]
  grind

/-- Exact 1-step decimation of `C_{2m+1}` via Operators D2 and A. -/
theorem hankelC_odd (c α β : Int) (m : Nat) :
    hankelC c α β (2 * m + 1) =
      altSign (m + 1) * 2 *
        (intPow α (m + 1) * hankelA c α β (m + 1) + (β - c) * intPow α m * hankelC c α β m) *
        (intPow α m * hankelC c α β m) := by
  let a := ecSeq c α β
  let d : Nat → Int := fun k => α * a k + (β - c)
  have hD := hankel_level2_odd (diff2 a) d
    (fun k => by
      simp only [diff2, diff1, d, a]
      have h2 : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
      rw [h2, ecSeq_even, ecSeq_odd, ecSeq_even]; grind)
    (fun k => by
      simp only [diff2, diff1, d, a]
      have h2 : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
      have h3 : 2 * k + 1 + 1 + 1 = 2 * (k + 1) + 1 := by omega
      rw [h3, h2, ecSeq_odd, ecSeq_even, ecSeq_odd]; grind)
    m
  have hsz : 2 * m + 1 = (m + 1) + m := by omega
  have hd2 : ∀ k, diff2 d k = α * diff2 a k := by
    intro k; simp only [diff2, diff1, d]; grind
  have hd : det (hankel d (m + 1)) =
      intPow α (m + 1) * det (hankel a (m + 1)) + (β - c) * intPow α m * det (hankel (diff2 a) m) :=
    hankel_affine_shift a α (β - c) m
  rw [hankelC, det_hankel_eq (diff2 a) hsz, hD, hd, det_hankel_congr hd2 m, det_hankel_scale]

/-- **THEOREM 1 (Closed 3-State Bit-Slice Automaton):**
    For EVERY `(c, α, β) ∈ Int³` and EVERY `m : Nat`, the Hankel determinant triple
    `(A_n, B_n, C_n) = (det H_n(a), det H_n(Δ a), det H_n(Δ² a))` satisfies all six exact
    integer bit-slice recurrences simultaneously. -/
theorem ecSeq_closed_system (c α β : Int) (m : Nat) :
    (hankelA c α β (2 * m + 1) =
        altSign m * c * intPow α (2 * m) * (hankelB c α β m * hankelB c α β m)) ∧
    (hankelA c α β (2 * (m + 1)) =
        altSign (m + 1) *
          ((intPow α (m + 1) * hankelA c α β (m + 1) + β * intPow α m * hankelC c α β m) *
           (intPow α (m + 1) * hankelA c α β (m + 1) + β * intPow α m * hankelC c α β m)) +
        altSign m * (c * c) * intPow α (2 * m) * (hankelC c α β m * hankelC c α β m)) ∧
    (hankelB c α β (2 * (m + 1)) =
        (intPow α (m + 1) * hankelA c α β (m + 1) + (β - c) * intPow α m * hankelC c α β m) *
        (intPow α (m + 1) * hankelB c α β (m + 1))) ∧
    (hankelB c α β (2 * m + 1) =
        (intPow α (m + 1) * hankelA c α β (m + 1) + (β - c) * intPow α m * hankelC c α β m) *
        (intPow α m * hankelB c α β m)) ∧
    (hankelC c α β (2 * m) =
        altSign m * intPow α (2 * m) * (hankelB c α β m * hankelB c α β m)) ∧
    (hankelC c α β (2 * m + 1) =
        altSign (m + 1) * 2 *
          (intPow α (m + 1) * hankelA c α β (m + 1) + (β - c) * intPow α m * hankelC c α β m) *
          (intPow α m * hankelC c α β m)) :=
  ⟨hankelA_odd c α β m, hankelA_even c α β m, hankelB_even c α β m,
   hankelB_odd c α β m, hankelC_even c α β m, hankelC_odd c α β m⟩

/-! ### Theorem 2: Universal Sharp Mod-8 Period-8 & Non-Singularity Theorem -/

theorem int_mul_odd (a b : Int) (ha : a % 2 = 1) (hb : b % 2 = 1) : (a * b) % 2 = 1 := by
  rw [Int.mul_emod, ha, hb]; rfl

theorem int_odd_sq_mod8 (x : Int) (hx : x % 2 = 1) : (x * x) % 8 = 1 := by
  have h8 : x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7 := by omega
  rw [Int.mul_emod]; rcases h8 with h | h | h | h <;> rw [h] <;> decide

theorem int_even0_sq_mod8 (x : Int) (hx : x % 4 = 0) : (x * x) % 8 = 0 := by
  have h8 : x % 8 = 0 ∨ x % 8 = 4 := by omega
  rw [Int.mul_emod]; rcases h8 with h | h <;> rw [h] <;> decide

theorem int_even2_sq_mod8 (x : Int) (hx : x % 4 = 2) : (x * x) % 8 = 4 := by
  have h8 : x % 8 = 2 ∨ x % 8 = 6 := by omega
  rw [Int.mul_emod]; rcases h8 with h | h <;> rw [h] <;> decide

theorem int_mod4_lin_iff (c α β : Int) (hc : c % 2 = 1) (hα : α % 2 = 1) (hβ : β % 2 = 1) :
    ((α * c + β) % 4 = 2 ↔ (c * α * β) % 4 = 1) ∧
    ((α * c + β) % 4 = 0 ↔ (c * α * β) % 4 = 3) := by
  have hc4 : c % 4 = 1 ∨ c % 4 = 3 := by omega
  have hα4 : α % 4 = 1 ∨ α % 4 = 3 := by omega
  have hβ4 : β % 4 = 1 ∨ β % 4 = 3 := by omega
  have h1 : (α * c + β) % 4 = ((α % 4) * (c % 4) + (β % 4)) % 4 := by
    rw [Int.add_emod, Int.mul_emod]; simp
  have h2 : (c * α * β) % 4 = (((c % 4) * (α % 4)) % 4 * (β % 4)) % 4 := by
    rw [Int.mul_emod, Int.mul_emod c α]
  rw [h1, h2]
  rcases hc4 with hc4 | hc4 <;> rcases hα4 with hα4 | hα4 <;> rcases hβ4 with hβ4 | hβ4 <;>
    simp [hc4, hα4, hβ4]

theorem mod8Pattern_odd (c α β : Int) (hc : c % 2 = 1) (r : Nat) :
    mod8Pattern c α β r % 2 = 1 := by
  match r with
  | 1 | 5 => simp only [mod8Pattern]; omega
  | 3 | 7 => simp only [mod8Pattern]; omega
  | 2 | 6 => simp only [mod8Pattern]; split <;> rfl
  | 4 => rfl
  | 0 => rfl
  | _ + 8 => rfl

/-- Master simultaneous mod-2 / mod-4 / mod-8 inductive invariant for ALL odd `(c, α, β)`. -/
theorem ecSeq_odd_master_invariant (c α β : Int)
    (hc : c % 2 = 1) (hα : α % 2 = 1) (hβ : β % 2 = 1) (n : Nat) :
    (hankelA c α β n % 2 = 1) ∧
    (hankelB c α β n % 2 = 1) ∧
    (n % 2 = 0 → hankelC c α β n % 8 = altSign (n / 2) % 8) ∧
    (n % 4 = 1 → hankelC c α β n % 4 = 2) ∧
    (n % 4 = 3 → hankelC c α β n % 4 = 0) ∧
    (1 ≤ n → hankelA c α β n % 8 = mod8Pattern c α β (n % 8)) := by
  induction n using nat_strong_ind with
  | h n ih =>
    match n with
    | 0 =>
      refine ⟨rfl, rfl, fun _ => rfl, fun h => by omega, fun h => by omega, fun h => by omega⟩
    | 1 =>
      have hA1 : hankelA c α β 1 = c := by
        have := hankelA_odd c α β 0
        simp [hankelB_zero, altSign, intPow] at this; exact this
      have hB1 : hankelB c α β 1 = α * c + (β - c) := by
        have := hankelB_odd c α β 0
        simp [hA1, hankelB_zero, hankelC_zero, intPow] at this; exact this
      have hC1 : hankelC c α β 1 = -2 * (α * c + (β - c)) := by
        have := hankelC_odd c α β 0
        simp [hA1, hankelC_zero, altSign, intPow] at this; grind
      have hoddS : (α * c + (β - c)) % 2 = 1 := by
        have hαc := int_mul_odd α c hα hc
        omega
      refine ⟨by rw [hA1]; exact hc,
              by rw [hB1]; exact hoddS,
              fun h => by omega,
              fun _ => by rw [hC1, Int.mul_emod]; omega,
              fun h => by omega,
              fun _ => by rw [hA1]; rfl⟩
    | n + 2 =>
      by_cases hpar : (n + 2) % 2 = 1
      · -- Odd case: n + 2 = 2 * m + 1 with m ≥ 1 (so m + 1 < n + 2!)
        let m := (n + 2) / 2
        have hnm : n + 2 = 2 * m + 1 := by omega
        have hm_pos : 1 ≤ m := by omega
        have hm_lt : m < n + 2 := by omega
        have hm1_lt : m + 1 < n + 2 := by omega
        have ihm := ih m hm_lt
        have ihm1 := ih (m + 1) hm1_lt
        -- A_{2m+1} mod 8
        have hA_mod8 : hankelA c α β (n + 2) % 8 = mod8Pattern c α β ((n + 2) % 8) := by
          rw [hnm, hankelA_odd, intPow_two_mul]
          have hsq : ((intPow α m * hankelB c α β m) * (intPow α m * hankelB c α β m)) % 8 = 1 :=
            int_odd_sq_mod8 _ (int_mul_odd _ _ (intPow_odd α hα m) ihm.2.1)
          have hrw : altSign m * c * (intPow α m * intPow α m) * (hankelB c α β m * hankelB c α β m) =
              (altSign m * c) * ((intPow α m * hankelB c α β m) * (intPow α m * hankelB c α β m)) := by grind
          rw [hrw, Int.mul_emod, hsq, Int.mul_one, Int.emod_emod]
          by_cases hm2 : m % 2 = 0
          · have hs : altSign m = 1 := by unfold altSign; simp [hm2]
            have hr : (2 * m + 1) % 8 = 1 ∨ (2 * m + 1) % 8 = 5 := by omega
            rw [hs, Int.one_mul]
            rcases hr with hr | hr <;> rw [hr] <;> rfl
          · have hs : altSign m = -1 := by unfold altSign; simp [hm2]
            have hr : (2 * m + 1) % 8 = 3 ∨ (2 * m + 1) % 8 = 7 := by omega
            rw [hs, show (-1 : Int) * c = -c by omega]
            rcases hr with hr | hr <;> rw [hr] <;> rfl
        have hA_odd : hankelA c α β (n + 2) % 2 = 1 := by
          have := mod8Pattern_odd c α β hc ((n + 2) % 8)
          omega
        -- S_B is odd (since β - c is even and α^{m+1} * A_{m+1} is odd)
        let SB := intPow α (m + 1) * hankelA c α β (m + 1) + (β - c) * intPow α m * hankelC c α β m
        have hSB_odd : SB % 2 = 1 := by
          have ht1 : (intPow α (m + 1) * hankelA c α β (m + 1)) % 2 = 1 :=
            int_mul_odd _ _ (intPow_odd α hα (m + 1)) ihm1.1
          have ht2 : ((β - c) * intPow α m * hankelC c α β m) % 2 = 0 := by
            have hbc : (β - c) % 2 = 0 := by omega
            rw [Int.mul_emod, Int.mul_emod (β - c), hbc, Int.zero_mul, Int.zero_emod, Int.zero_mul]; rfl
          dsimp only [SB]; omega
        have hB_odd : hankelB c α β (n + 2) % 2 = 1 := by
          rw [hnm, hankelB_odd]
          exact int_mul_odd _ _ hSB_odd (int_mul_odd _ _ (intPow_odd α hα m) ihm.2.1)
        refine ⟨hA_odd, hB_odd, fun he => by omega, ?_, ?_, fun _ => hA_mod8⟩
        · intro hm4
          have hm2 : m % 2 = 0 := by omega
          have hCm_mod8 : hankelC c α β m % 8 = altSign (m / 2) % 8 := ihm.2.2.1 hm2
          have hCm_odd : hankelC c α β m % 2 = 1 := by
            unfold altSign at hCm_mod8; split at hCm_mod8 <;> omega
          have hs_odd : (altSign (m + 1)) % 2 = 1 := by unfold altSign; split <;> decide
          rw [hnm, hankelC_odd]
          have hprod : (altSign (m + 1) * SB * (intPow α m * hankelC c α β m)) % 2 = 1 :=
            int_mul_odd _ _ (int_mul_odd _ _ hs_odd hSB_odd) (int_mul_odd _ _ (intPow_odd α hα m) hCm_odd)
          have hrw : altSign (m + 1) * 2 * SB * (intPow α m * hankelC c α β m) =
              2 * (altSign (m + 1) * SB * (intPow α m * hankelC c α β m)) := by grind
          rw [hrw]; omega
        · intro hm4
          have hm_evenC : hankelC c α β m % 2 = 0 := by
            by_cases h1 : m % 4 = 1
            · have := ihm.2.2.2.1 h1; omega
            · have h3 : m % 4 = 3 := by omega
              have := ihm.2.2.2.2.1 h3; omega
          rw [hnm, hankelC_odd]
          have hrw : altSign (m + 1) * 2 * SB * (intPow α m * hankelC c α β m) =
              (altSign (m + 1) * SB * intPow α m) * (2 * hankelC c α β m) := by grind
          have h2C : (2 * hankelC c α β m) % 4 = 0 := by omega
          rw [hrw, Int.mul_emod, h2C, Int.mul_zero]; rfl
      · -- Even case: n + 2 = 2 * (m + 1) with m ≥ 0 (m < m + 1 < n + 2!)
        let m := n / 2
        have hnm : n + 2 = 2 * (m + 1) := by omega
        have hm_lt : m < n + 2 := by omega
        have hm1_lt : m + 1 < n + 2 := by omega
        have ihm := ih m hm_lt
        have ihm1 := ih (m + 1) hm1_lt
        -- B_{2(m+1)} is odd
        have hB_odd : hankelB c α β (n + 2) % 2 = 1 := by
          rw [hnm, hankelB_even]
          have ht1 : (intPow α (m + 1) * hankelA c α β (m + 1)) % 2 = 1 :=
            int_mul_odd _ _ (intPow_odd α hα (m + 1)) ihm1.1
          have ht2 : ((β - c) * intPow α m * hankelC c α β m) % 2 = 0 := by
            have hbc : (β - c) % 2 = 0 := by omega
            rw [Int.mul_emod, Int.mul_emod (β - c), hbc, Int.zero_mul, Int.zero_emod, Int.zero_mul]; rfl
          have hSB : (intPow α (m + 1) * hankelA c α β (m + 1) + (β - c) * intPow α m * hankelC c α β m) % 2 = 1 := by omega
          exact int_mul_odd _ _ hSB (int_mul_odd _ _ (intPow_odd α hα (m + 1)) ihm1.2.1)
        -- C_{2(m+1)} mod 8 = altSign (m + 1) mod 8
        have hC_mod8 : hankelC c α β (n + 2) % 8 = altSign ((n + 2) / 2) % 8 := by
          have hdiv : (n + 2) / 2 = m + 1 := by omega
          rw [hdiv, hnm, hankelC_even, intPow_two_mul]
          have hsq : ((intPow α (m + 1) * hankelB c α β (m + 1)) * (intPow α (m + 1) * hankelB c α β (m + 1))) % 8 = 1 :=
            int_odd_sq_mod8 _ (int_mul_odd _ _ (intPow_odd α hα (m + 1)) ihm1.2.1)
          have hrw : altSign (m + 1) * (intPow α (m + 1) * intPow α (m + 1)) *
              (hankelB c α β (m + 1) * hankelB c α β (m + 1)) =
              altSign (m + 1) * ((intPow α (m + 1) * hankelB c α β (m + 1)) * (intPow α (m + 1) * hankelB c α β (m + 1))) := by grind
          rw [hrw, Int.mul_emod, hsq, Int.mul_one, Int.emod_emod]
        -- A_{2(m+1)} mod 8
        have hA_mod8 : hankelA c α β (n + 2) % 8 = mod8Pattern c α β ((n + 2) % 8) := by
          rw [hnm, hankelA_even, intPow_two_mul]
          let SA := intPow α (m + 1) * hankelA c α β (m + 1) + β * intPow α m * hankelC c α β m
          let T := c * intPow α m * hankelC c α β m
          have hrw : altSign (m + 1) * (SA * SA) +
              altSign m * (c * c) * (intPow α m * intPow α m) * (hankelC c α β m * hankelC c α β m) =
              altSign (m + 1) * (SA * SA) + altSign m * (T * T) := by dsimp only [T]; grind
          rw [hrw]
          by_cases hm2 : m % 2 = 0
          · -- Subcase m = 2*k (even): 2*(m+1) % 8 ∈ {2, 6}
            have hs0 : altSign m = 1 := by unfold altSign; simp [hm2]
            have hs1 : altSign (m + 1) = -1 := by rw [altSign_succ, hs0]
            have hCm8 : hankelC c α β m % 8 = altSign (m / 2) % 8 := ihm.2.2.1 hm2
            have hAm1_8 : hankelA c α β (m + 1) % 8 = mod8Pattern c α β ((m + 1) % 8) := ihm1.2.2.2.2.2 (by omega)
            have hAm1_4 : hankelA c α β (m + 1) % 4 = (altSign (m / 2) * c) % 4 := by
              by_cases hk2 : (m / 2) % 2 = 0
              · have hsk : altSign (m / 2) = 1 := by unfold altSign; simp [hk2]
                have hr : (m + 1) % 8 = 1 ∨ (m + 1) % 8 = 5 := by omega
                rcases hr with hr | hr <;> (rw [hr] at hAm1_8; simp only [mod8Pattern] at hAm1_8; rw [hsk, Int.one_mul]; omega)
              · have hsk : altSign (m / 2) = -1 := by unfold altSign; simp [hk2]
                have hr : (m + 1) % 8 = 3 ∨ (m + 1) % 8 = 7 := by omega
                rcases hr with hr | hr <;> (rw [hr] at hAm1_8; simp only [mod8Pattern] at hAm1_8; rw [hsk, show (-1 : Int) * c = -c by omega]; omega)
            have hCm_odd : hankelC c α β m % 2 = 1 := by
              unfold altSign at hCm8; split at hCm8 <;> omega
            have hTsq : (T * T) % 8 = 1 :=
              int_odd_sq_mod8 T (int_mul_odd _ _ (int_mul_odd _ _ hc (intPow_odd α hα m)) hCm_odd)
            have hSA_eq : SA = intPow α m * (α * hankelA c α β (m + 1) + β * hankelC c α β m) := by
              dsimp only [SA]; rw [intPow]; grind
            have hlin4 : (α * hankelA c α β (m + 1) + β * hankelC c α β m) % 4 =
                (altSign (m / 2) * (α * c + β)) % 4 := by
              have hCm4 : hankelC c α β m % 4 = altSign (m / 2) % 4 := by omega
              rw [Int.add_emod, Int.mul_emod α, Int.mul_emod β, hAm1_4, hCm4]
              rw [← Int.mul_emod α, ← Int.mul_emod β, ← Int.add_emod]
              congr 1; grind
            have hαm_odd : intPow α m % 2 = 1 := intPow_odd α hα m
            have hSA4_mod : SA % 4 = (intPow α m * (altSign (m / 2) * (α * c + β))) % 4 := by
              rw [hSA_eq, Int.mul_emod, hlin4, ← Int.mul_emod]
            have hiff := int_mod4_lin_iff c α β hc hα hβ
            have hr26 : (2 * (m + 1)) % 8 = 2 ∨ (2 * (m + 1)) % 8 = 6 := by omega
            by_cases hcab : (c * α * β) % 4 = 1
            · have hlin2 : (α * c + β) % 4 = 2 := hiff.1.mpr hcab
              have hSA2 : SA % 4 = 2 := by
                have hsk_odd : altSign (m / 2) % 2 = 1 := by unfold altSign; split <;> decide
                rw [hSA4_mod, Int.mul_emod, Int.mul_emod (altSign (m / 2)), hlin2]
                have h1 : intPow α m % 4 = 1 ∨ intPow α m % 4 = 3 := by omega
                have h2 : altSign (m / 2) % 4 = 1 ∨ altSign (m / 2) % 4 = 3 := by omega
                rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp [h1, h2]
              have hSAsq : (SA * SA) % 8 = 4 := int_even2_sq_mod8 SA hSA2
              rw [hs1, hs0, Int.add_emod, Int.mul_emod (-1), hSAsq, Int.one_mul, hTsq]
              rcases hr26 with hr | hr <;> (rw [hr]; simp [mod8Pattern, hcab])
            · have hcab3 : (c * α * β) % 4 = 3 := by
                have hodd3 : (c * α * β) % 2 = 1 := int_mul_odd _ _ (int_mul_odd _ _ hc hα) hβ
                omega
              have hlin0 : (α * c + β) % 4 = 0 := hiff.2.mpr hcab3
              have hSA0 : SA % 4 = 0 := by
                rw [hSA4_mod, Int.mul_emod, Int.mul_emod (altSign (m / 2)), hlin0]; simp
              have hSAsq : (SA * SA) % 8 = 0 := int_even0_sq_mod8 SA hSA0
              rw [hs1, hs0, Int.add_emod, Int.mul_emod (-1), hSAsq, Int.one_mul, hTsq]
              rcases hr26 with hr | hr <;> (rw [hr]; simp [mod8Pattern, hcab])
          · -- Subcase m is odd: either m % 4 = 1 (n+2 % 8 = 4) or m % 4 = 3 (n+2 % 8 = 0)
            have hm1 : m % 2 = 1 := by omega
            have hs0 : altSign m = -1 := by unfold altSign; simp [hm1]
            have hs1 : altSign (m + 1) = 1 := by rw [altSign_succ, hs0]; rfl
            have hT_factor : T = (c * intPow α m) * hankelC c α β m := rfl
            have hca_odd : (c * intPow α m) % 2 = 1 := int_mul_odd _ _ hc (intPow_odd α hα m)
            by_cases hm4 : m % 4 = 1
            · have hCm4 : hankelC c α β m % 4 = 2 := ihm.2.2.2.1 hm4
              have hSA_odd : SA % 2 = 1 := by
                have ht1 := int_mul_odd _ _ (intPow_odd α hα (m + 1)) ihm1.1
                have hC2 : hankelC c α β m % 2 = 0 := by omega
                have ht2 : (β * intPow α m * hankelC c α β m) % 2 = 0 := by
                  rw [Int.mul_emod, hC2, Int.mul_zero]; rfl
                dsimp only [SA]; omega
              have hSAsq : (SA * SA) % 8 = 1 := int_odd_sq_mod8 SA hSA_odd
              have hT4 : T % 4 = 2 := by
                rw [hT_factor, Int.mul_emod, hCm4]
                have h1 : (c * intPow α m) % 4 = 1 ∨ (c * intPow α m) % 4 = 3 := by omega
                rcases h1 with h1 | h1 <;> simp [h1]
              have hTsq : (T * T) % 8 = 4 := int_even2_sq_mod8 T hT4
              have hr4 : (2 * (m + 1)) % 8 = 4 := by omega
              rw [hs1, hs0, Int.one_mul, Int.add_emod, hSAsq, Int.mul_emod (-1), hTsq, hr4]
              rfl
            · have hm43 : m % 4 = 3 := by omega
              have hCm4 : hankelC c α β m % 4 = 0 := ihm.2.2.2.2.1 hm43
              have hSA_odd : SA % 2 = 1 := by
                have ht1 := int_mul_odd _ _ (intPow_odd α hα (m + 1)) ihm1.1
                have hC2 : hankelC c α β m % 2 = 0 := by omega
                have ht2 : (β * intPow α m * hankelC c α β m) % 2 = 0 := by
                  rw [Int.mul_emod, hC2, Int.mul_zero]; rfl
                dsimp only [SA]; omega
              have hSAsq : (SA * SA) % 8 = 1 := int_odd_sq_mod8 SA hSA_odd
              have hT4 : T % 4 = 0 := by
                rw [hT_factor, Int.mul_emod, hCm4]; simp
              have hTsq : (T * T) % 8 = 0 := int_even0_sq_mod8 T hT4
              have hr0 : (2 * (m + 1)) % 8 = 0 := by omega
              rw [hs1, hs0, Int.one_mul, Int.add_emod, hSAsq, Int.mul_emod (-1), hTsq, hr0]
              rfl
        have hA_odd : hankelA c α β (n + 2) % 2 = 1 := by
          have := mod8Pattern_odd c α β hc ((n + 2) % 8)
          omega
        refine ⟨hA_odd, hB_odd, fun _ => hC_mod8, fun h => by omega, fun h => by omega, fun _ => hA_mod8⟩

/-- **THEOREM 2a (Universal Exact Period-8 Mod-8 Law):**
    For EVERY odd `(c, α, β) ∈ Int³` and EVERY `n ≥ 1`:
    `det H_{n+8}(ecSeq c α β) ≡ det H_n(ecSeq c α β) (mod 8)`. -/
theorem ecSeq_odd_mod8_periodic (c α β : Int)
    (hc : c % 2 = 1) (hα : α % 2 = 1) (hβ : β % 2 = 1) (n : Nat) (hn : 1 ≤ n) :
    det (hankel (ecSeq c α β) (n + 8)) % 8 = det (hankel (ecSeq c α β) n) % 8 := by
  have h1 := (ecSeq_odd_master_invariant c α β hc hα hβ (n + 8)).2.2.2.2.2 (by omega)
  have h2 := (ecSeq_odd_master_invariant c α β hc hα hβ n).2.2.2.2.2 hn
  have hmod : (n + 8) % 8 = n % 8 := by omega
  change hankelA c α β (n + 8) % 8 = hankelA c α β n % 8
  rw [h1, h2, hmod]

/-- **THEOREM 2b (Universal Infinite Non-Singularity):**
    For EVERY odd `(c, α, β) ∈ Int³` and EVERY `n ≥ 1`, `det H_n(ecSeq c α β) ≠ 0`. -/
theorem ecSeq_odd_nonsingular (c α β : Int)
    (hc : c % 2 = 1) (hα : α % 2 = 1) (hβ : β % 2 = 1) (n : Nat) :
    det (hankel (ecSeq c α β) n) ≠ 0 := by
  have hodd := (ecSeq_odd_master_invariant c α β hc hα hβ n).1
  intro hz; rw [hankelA, hz] at hodd; omega

/-- **THEOREM 2c (Strictness of Period 8 — Period 4 ALWAYS Fails Mod 8):**
    For EVERY odd `(c, α, β) ∈ Int³`, `det H_4 ≡ 5 ≢ 1 ≡ det H_8 (mod 8)`. -/
theorem ecSeq_odd_period4_fails_mod8 (c α β : Int)
    (hc : c % 2 = 1) (hα : α % 2 = 1) (hβ : β % 2 = 1) :
    det (hankel (ecSeq c α β) 4) % 8 = 5 ∧
    det (hankel (ecSeq c α β) 8) % 8 = 1 ∧
    det (hankel (ecSeq c α β) 4) % 8 ≠ det (hankel (ecSeq c α β) 8) % 8 := by
  have h4 := (ecSeq_odd_master_invariant c α β hc hα hβ 4).2.2.2.2.2 (by omega)
  have h8 := (ecSeq_odd_master_invariant c α β hc hα hβ 8).2.2.2.2.2 (by omega)
  change hankelA c α β 4 % 8 = 5 ∧ hankelA c α β 8 % 8 = 1 ∧ hankelA c α β 4 % 8 ≠ hankelA c α β 8 % 8
  rw [h4, h8]; exact ⟨rfl, rfl, by change (5 : Int) ≠ 1; decide⟩

/-! ### Theorem 3: Ruler Family (`c = 0`) Exact Vanishing, Signed Squares & Mod-8 Law -/

/-- **THEOREM 3a:** For ALL `α β : Int` and ALL `m : Nat`, `det H_{2m+1}(ecSeq 0 α β) = 0`. -/
theorem ruler_family_odd_zero (α β : Int) (m : Nat) :
    det (hankel (ecSeq 0 α β) (2 * m + 1)) = 0 := by
  change hankelA 0 α β (2 * m + 1) = 0
  rw [hankelA_odd]; simp

/-- **THEOREM 3b:** For ALL `α β : Int` and ALL `m : Nat`, `det H_{2(m+1)}(ecSeq 0 α β)`
    is an exact signed perfect square `(-1)^{m+1} * s^2`. -/
theorem ruler_family_even_signed_square (α β : Int) (m : Nat) :
    ∃ s : Int, det (hankel (ecSeq 0 α β) (2 * (m + 1))) = altSign (m + 1) * (s * s) := by
  refine ⟨intPow α (m + 1) * hankelA 0 α β (m + 1) + β * intPow α m * hankelC 0 α β m, ?_⟩
  change hankelA 0 α β (2 * (m + 1)) = _
  rw [hankelA_even]; simp

theorem ruler_family_parity_invariant (α β : Int)
    (hα : α % 2 = 1) (hβ : β % 2 = 1) (n : Nat) :
    (n % 2 = 0 → hankelA 0 α β n % 2 = 1) ∧
    (hankelB 0 α β n % 2 = 1) ∧
    (n % 2 = 0 → hankelC 0 α β n % 2 = 1) ∧
    (n % 2 = 1 → hankelC 0 α β n % 2 = 0) := by
  induction n using nat_strong_ind with
  | h n ih =>
    match n with
    | 0 => refine ⟨fun _ => rfl, rfl, fun _ => rfl, fun h => by omega⟩
    | 1 =>
      have hA1 : hankelA 0 α β 1 = 0 := ruler_family_odd_zero α β 0
      have hB1 : hankelB 0 α β 1 = β := by
        have := hankelB_odd 0 α β 0
        simp [hA1, hankelB_zero, hankelC_zero, intPow] at this; exact this
      have hC1 : hankelC 0 α β 1 = -2 * β := by
        have := hankelC_odd 0 α β 0
        simp [hA1, hankelC_zero, altSign, intPow] at this; grind
      refine ⟨fun h => by omega, by rw [hB1]; exact hβ, fun h => by omega, fun _ => by rw [hC1]; omega⟩
    | n + 2 =>
      by_cases hpar : (n + 2) % 2 = 1
      · let m := (n + 2) / 2
        have hnm : n + 2 = 2 * m + 1 := by omega
        have ihm := ih m (by omega)
        have ihm1 := ih (m + 1) (by omega)
        have hS_odd : (intPow α (m + 1) * hankelA 0 α β (m + 1) + (β - 0) * intPow α m * hankelC 0 α β m) % 2 = 1 := by
          by_cases hm2 : m % 2 = 0
          · have hA0 : hankelA 0 α β (m + 1) = 0 := by
              have : m + 1 = 2 * (m / 2) + 1 := by omega
              rw [this]; exact ruler_family_odd_zero α β (m / 2)
            have ht2 := int_mul_odd _ _ (int_mul_odd _ _ (by omega : (β - 0) % 2 = 1) (intPow_odd α hα m)) (ihm.2.2.1 hm2)
            rw [hA0, Int.mul_zero, Int.zero_add]; exact ht2
          · have hAodd := ihm1.1 (by omega)
            have hCev := ihm.2.2.2 (by omega)
            have ht1 := int_mul_odd _ _ (intPow_odd α hα (m + 1)) hAodd
            have ht2 : ((β - 0) * intPow α m * hankelC 0 α β m) % 2 = 0 := by
              rw [Int.mul_emod, hCev, Int.mul_zero]; rfl
            omega
        have hB_odd : hankelB 0 α β (n + 2) % 2 = 1 := by
          rw [hnm, hankelB_odd]
          exact int_mul_odd _ _ hS_odd (int_mul_odd _ _ (intPow_odd α hα m) ihm.2.1)
        have hC_ev : hankelC 0 α β (n + 2) % 2 = 0 := by
          rw [hnm, hankelC_odd]
          have hrw : altSign (m + 1) * 2 *
              (intPow α (m + 1) * hankelA 0 α β (m + 1) + (β - 0) * intPow α m * hankelC 0 α β m) *
              (intPow α m * hankelC 0 α β m) =
              2 * (altSign (m + 1) *
                (intPow α (m + 1) * hankelA 0 α β (m + 1) + (β - 0) * intPow α m * hankelC 0 α β m) *
                (intPow α m * hankelC 0 α β m)) := by grind
          rw [hrw]; omega
        refine ⟨fun h => by omega, hB_odd, fun h => by omega, fun _ => hC_ev⟩
      · let m := n / 2
        have hnm : n + 2 = 2 * (m + 1) := by omega
        have ihm := ih m (by omega)
        have ihm1 := ih (m + 1) (by omega)
        have hS_odd : (intPow α (m + 1) * hankelA 0 α β (m + 1) + β * intPow α m * hankelC 0 α β m) % 2 = 1 := by
          by_cases hm2 : m % 2 = 0
          · have hA0 : hankelA 0 α β (m + 1) = 0 := by
              have : m + 1 = 2 * (m / 2) + 1 := by omega
              rw [this]; exact ruler_family_odd_zero α β (m / 2)
            have ht2 := int_mul_odd _ _ (int_mul_odd _ _ hβ (intPow_odd α hα m)) (ihm.2.2.1 hm2)
            rw [hA0, Int.mul_zero, Int.zero_add]; exact ht2
          · have hAodd := ihm1.1 (by omega)
            have hCev := ihm.2.2.2 (by omega)
            have ht1 := int_mul_odd _ _ (intPow_odd α hα (m + 1)) hAodd
            have ht2 : (β * intPow α m * hankelC 0 α β m) % 2 = 0 := by
              rw [Int.mul_emod, hCev, Int.mul_zero]; rfl
            omega
        have hs_odd : altSign (m + 1) % 2 = 1 := by unfold altSign; split <;> decide
        have hA_odd : hankelA 0 α β (n + 2) % 2 = 1 := by
          rw [hnm, hankelA_even]; simp only [Int.mul_zero, Int.zero_mul, Int.add_zero]
          exact int_mul_odd _ _ hs_odd (int_mul_odd _ _ hS_odd hS_odd)
        have hB_odd : hankelB 0 α β (n + 2) % 2 = 1 := by
          rw [hnm, hankelB_even, show β - 0 = β by omega]
          exact int_mul_odd _ _ hS_odd (int_mul_odd _ _ (intPow_odd α hα (m + 1)) ihm1.2.1)
        have hC_odd : hankelC 0 α β (n + 2) % 2 = 1 := by
          rw [hnm, hankelC_even]
          exact int_mul_odd _ _ (int_mul_odd _ _ hs_odd (intPow_odd α hα (2 * (m + 1))))
            (int_mul_odd _ _ ihm1.2.1 ihm1.2.1)
        refine ⟨fun _ => hA_odd, hB_odd, fun _ => hC_odd, fun h => by omega⟩

/-- **THEOREM 3c (Ruler Family Exact Mod-8 Period-4 & Even Non-Singularity):**
    For ALL odd `α β : Int` and ALL `m : Nat` (including the exact ruler `v2(n+1)` at `α = β = 1`):
    `det H_{2(m+1)}(ecSeq 0 α β) ≡ (-1)^{m+1} (mod 8)` and `det H_{2(m+1)}(ecSeq 0 α β) ≠ 0`. -/
theorem ruler_family_odd_params_mod8 (α β : Int)
    (hα : α % 2 = 1) (hβ : β % 2 = 1) (m : Nat) :
    det (hankel (ecSeq 0 α β) (2 * (m + 1))) % 8 = altSign (m + 1) % 8 ∧
    det (hankel (ecSeq 0 α β) (2 * (m + 1))) ≠ 0 := by
  obtain ⟨s, hs⟩ := ruler_family_even_signed_square α β m
  have hodd := (ruler_family_parity_invariant α β hα hβ (2 * (m + 1))).1 (by omega)
  have hs_odd : s % 2 = 1 := by
    change det (hankel (ecSeq 0 α β) (2 * (m + 1))) % 2 = 1 at hodd
    rw [hs, Int.mul_emod] at hodd
    have ha : altSign (m + 1) % 2 = 1 := by unfold altSign; split <;> decide
    rw [ha, Int.one_mul, Int.emod_emod] at hodd
    rw [Int.mul_emod] at hodd
    have hs2 : s % 2 = 0 ∨ s % 2 = 1 := by omega
    rcases hs2 with hs2 | hs2
    · rw [hs2] at hodd; simp at hodd
    · exact hs2
  have hsq8 := int_odd_sq_mod8 s hs_odd
  refine ⟨?_, ?_⟩
  · rw [hs, Int.mul_emod, hsq8, Int.mul_one, Int.emod_emod]
  · intro hz; change det (hankel (ecSeq 0 α β) (2 * (m + 1))) % 2 = 1 at hodd; rw [hz] at hodd; omega

/-! ### Theorem 4: Signed Ruler `(-1)^{v2(n+1)}` Exact Vanishing & Exact 2-Adic Valuation -/

/-- **THEOREM 4a (Exact Vanishing at `n = 4k + 2`):**
    For ALL `k : Nat`, `det H_{4k+2}((-1)^{v2(n+1)}) = 0`. -/
theorem signed_ruler_vanish_mod4_eq2 (k : Nat) :
    det (hankel (fun n => altSign (v2 (n + 1))) (4 * k + 2)) = 0 := by
  rw [det_hankel_congr (fun n => (ecSeq_signed_ruler_eq_v2 n).symm)]
  have hsz : 4 * k + 2 = 2 * (2 * k + 1) := by omega
  change hankelA 1 (-1) 0 (4 * k + 2) = 0
  rw [hsz, hankelA_even]
  have hAC : hankelA 1 (-1) 0 (2 * k + 1) = hankelC 1 (-1) 0 (2 * k) := by
    rw [hankelA_odd, hankelC_even]; simp
  rw [hAC, show 2 * (2 * k) = 4 * k from by omega]
  have h4k : intPow (-1) (4 * k) = 1 := by
    rw [show 4 * k = 2 * (2 * k) by omega, intPow_neg_one_even]
  rw [h4k, intPow_neg_one (2 * k + 1)]
  have hs1 : altSign (2 * k + 1) = -1 := by unfold altSign; simp
  have hs0 : altSign (2 * k) = 1 := by unfold altSign; simp
  rw [hs1, hs0]; grind

theorem intPow_two_dvd_mul_odd (k : Nat) (u : Int) (hu : u % 2 = 1) :
    (intPow 2 k ∣ intPow 2 k * u) ∧
    ¬ (intPow 2 (k + 1) ∣ intPow 2 k * u) ∧
    intPow 2 k * u ≠ 0 := by
  have hpos := intPow_two_pos k
  have hne : intPow 2 k ≠ 0 := by omega
  refine ⟨⟨u, rfl⟩, ?_, ?_⟩
  · intro ⟨q, hq⟩
    rw [intPow] at hq
    have hmul : intPow 2 k * u = intPow 2 k * (2 * q) := by
      rw [hq]; grind
    have huq : u = 2 * q := Int.eq_of_mul_eq_mul_left hne hmul
    omega
  · intro hz
    have hu0 : u = 0 := Int.eq_of_mul_eq_mul_left hne (by rw [hz, Int.mul_zero])
    omega

/-- **THEOREM 4b (Exact 2-Adic Valuation `v_2(det H_n) = 2 * floor(n/2)` for `n % 4 ≠ 2`):**
    Proved by chaining Operator A (`2 * pd - 1`) with Theorem 2's mod-4 invariant on `C_pd`! -/
theorem signed_ruler_v2_exact (n : Nat) (hn : 1 ≤ n) (hmod : n % 4 ≠ 2) :
    (intPow 2 (2 * (n / 2)) ∣ det (hankel (fun k => altSign (v2 (k + 1))) n)) ∧
    ¬ (intPow 2 (2 * (n / 2) + 1) ∣ det (hankel (fun k => altSign (v2 (k + 1))) n)) ∧
    det (hankel (fun k => altSign (v2 (k + 1))) n) ≠ 0 := by
  rw [det_hankel_congr (fun k => (ecSeq_signed_ruler_eq_v2 k).symm)]
  rw [det_hankel_congr ecSeq_signed_ruler_eq_pd]
  have hn1 : n = (n - 1) + 1 := by omega
  rw [det_hankel_eq _ hn1, hankel_affine_shift (ecSeq 1 (-1) 1) 2 (-1) (n - 1)]
  rw [← det_hankel_eq _ hn1, intPow]
  have hfact : 2 * intPow 2 (n - 1) * det (hankel (ecSeq 1 (-1) 1) n) +
      -1 * intPow 2 (n - 1) * det (hankel (diff2 (ecSeq 1 (-1) 1)) (n - 1)) =
      intPow 2 (n - 1) * (2 * hankelA 1 (-1) 1 n - hankelC 1 (-1) 1 (n - 1)) := by
    dsimp only [hankelA, hankelC]; grind
  rw [hfact]
  have hpd_n := ecSeq_odd_master_invariant 1 (-1) 1 (by decide) (by decide) (by decide) n
  have hpd_m := ecSeq_odd_master_invariant 1 (-1) 1 (by decide) (by decide) (by decide) (n - 1)
  by_cases hpar : n % 2 = 1
  · -- n is odd: n - 1 = 2 * (n / 2) is even, so C_pd(n - 1) is odd -> 2*A_pd(n) - C_pd(n-1) is odd!
    have heq : n - 1 = 2 * (n / 2) := by omega
    have hCm8 : hankelC 1 (-1) 1 (n - 1) % 8 = altSign ((n - 1) / 2) % 8 := hpd_m.2.2.1 (by omega)
    have hCm_odd : hankelC 1 (-1) 1 (n - 1) % 2 = 1 := by
      unfold altSign at hCm8; split at hCm8 <;> omega
    have hu_odd : (2 * hankelA 1 (-1) 1 n - hankelC 1 (-1) 1 (n - 1)) % 2 = 1 := by omega
    rw [heq] at hu_odd ⊢
    exact intPow_two_dvd_mul_odd (2 * (n / 2)) _ hu_odd
  · -- n % 4 = 0 (and n ≥ 4): (n - 1) % 4 = 3, so C_pd(n-1) % 4 = 0, A_pd(n) odd -> 2*A - C = 2 * u with u odd!
    have hm43 : (n - 1) % 4 = 3 := by omega
    have hCm4 : hankelC 1 (-1) 1 (n - 1) % 4 = 0 := hpd_m.2.2.2.2.1 hm43
    have hAn_odd : hankelA 1 (-1) 1 n % 2 = 1 := hpd_n.1
    let u := hankelA 1 (-1) 1 n - hankelC 1 (-1) 1 (n - 1) / 2
    have hu_eq : 2 * hankelA 1 (-1) 1 n - hankelC 1 (-1) 1 (n - 1) = 2 * u := by
      dsimp only [u]; omega
    have hu_odd : u % 2 = 1 := by dsimp only [u]; omega
    have heq : 2 * (n / 2) = (n - 1) + 1 := by omega
    rw [hu_eq, show intPow 2 (n - 1) * (2 * u) = intPow 2 ((n - 1) + 1) * u by rw [intPow]; grind, ← heq]
    exact intPow_two_dvd_mul_odd (2 * (n / 2)) u hu_odd

/-! ### Theorem 5: Cross-Family Reuse of Operators B & C (Thue-Morse, Gould, Paperfolding, Lacunary) -/

theorem popPow_even (r : Int) (k : Nat) : popPow r (2 * k) = popPow r k := by
  unfold popPow; rw [popcount_even]

theorem popPow_odd (r : Int) (k : Nat) : popPow r (2 * k + 1) = r * popPow r k := by
  unfold popPow; rw [popcount_odd]
  have h1 : 1 + popcount k = popcount k + 1 := by omega
  rw [h1, intPow]

/-- **THEOREM 5a (Exact Bit-Slice Hankel Factorization for Thue-Morse & Gould `r^{popcount(n)}`):**
    Direct reuse of Operator C (`hankel_r_pair`) for EVERY `r : Int` and EVERY `n : Nat`. -/
theorem popPow_hankel_factorization (r : Int) (n : Nat) :
    det (hankel (popPow r) n) =
      det (hankel (popPow r) ((n + 1) / 2)) *
      det (hankel (fun k => popPow r (k + 1) - r * r * popPow r k) (n / 2)) :=
  hankel_r_pair (popPow r) (popPow r) r (popPow_even r) (popPow_odd r) n

theorem shiftedPaperfolding_even (k : Nat) : shiftedPaperfolding (2 * k) = altSign k := by
  rw [shiftedPaperfolding]
  by_cases hk : k = 0
  · subst hk; rfl
  · have hne : 2 * k ≠ 0 := by omega
    have hm : (2 * k) % 2 = 0 := by omega
    have hd : (2 * k) / 2 = k := by omega
    simp [hne, hm, hd]

theorem shiftedPaperfolding_odd (k : Nat) : shiftedPaperfolding (2 * k + 1) = shiftedPaperfolding k := by
  rw [shiftedPaperfolding]
  have hd : (2 * k + 1) / 2 = k := by omega
  simp [hd]

/-- **THEOREM 5b (Exact Bit-Slice Hankel Decimation for Shifted Paperfolding, `q = -1`):**
    Direct reuse of Operators B1 & B2 at `c = 1, q = -1`. -/
theorem shiftedPaperfolding_decimation (m : Nat) :
    (det (hankel shiftedPaperfolding (2 * (m + 1))) =
        altSign (m + 1) * (det (hankel shiftedPaperfolding (m + 1)) * det (hankel shiftedPaperfolding (m + 1))) -
        altSign m * (det (hankel (qDiff (-1) (qDiff (-1) shiftedPaperfolding)) m) *
                     det (hankel (qDiff (-1) (qDiff (-1) shiftedPaperfolding)) m))) ∧
    (det (hankel shiftedPaperfolding (2 * m + 1)) =
        altSign m * (det (hankel (qDiff (-1) shiftedPaperfolding) m) *
                     det (hankel (qDiff (-1) shiftedPaperfolding) m))) := by
  have heven : ∀ k, shiftedPaperfolding (2 * k) = 1 * intPow (-1) k := fun k => by
    rw [Int.one_mul, intPow_neg_one]; exact shiftedPaperfolding_even k
  have hB1 := hankel_geom_even_even shiftedPaperfolding shiftedPaperfolding 1 (-1) heven shiftedPaperfolding_odd m
  have hB2 := hankel_geom_even_odd shiftedPaperfolding shiftedPaperfolding 1 (-1) heven shiftedPaperfolding_odd m
  refine ⟨?_, ?_⟩
  · rw [det_hankel_eq _ (show 2 * (m + 1) = (m + 1) + (m + 1) by omega), hB1]; grind
  · rw [det_hankel_eq _ (show 2 * m + 1 = (m + 1) + m by omega), hB2]; grind

/-- **THEOREM 5c (Exact Square Decimation for Arbitrary Lacunary `q = 0` Sequences):**
    Direct reuse of Operators B1 & B2 at `q = 0`. -/
theorem sparsePow2m1_decimation (c : Int) (b : Nat → Int) (m : Nat) :
    (det (hankel (sparsePow2m1 c b) (2 * (m + 1))) =
        altSign (m + 1) * (det (hankel b (m + 1)) * det (hankel b (m + 1)))) ∧
    (det (hankel (sparsePow2m1 c b) (2 * m + 1)) =
        altSign m * c * (det (hankel (shiftSeq b) m) * det (hankel (shiftSeq b) m))) := by
  have heven : ∀ k, sparsePow2m1 c b (2 * k) = c * intPow 0 k := by
    intro k
    cases k with
    | zero => simp [sparsePow2m1, intPow]
    | succ k =>
      have hne : 2 * (k + 1) ≠ 0 := by omega
      have hm : (2 * (k + 1)) % 2 = 0 := by omega
      simp [sparsePow2m1, hne, hm, intPow]
  have hodd : ∀ k, sparsePow2m1 c b (2 * k + 1) = b k := by
    intro k
    have hd : (2 * k + 1) / 2 = k := by omega
    simp [sparsePow2m1, hd]
  have hB1 := hankel_geom_even_even (sparsePow2m1 c b) b c 0 heven hodd m
  have hB2 := hankel_geom_even_odd (sparsePow2m1 c b) b c 0 heven hodd m
  have hq0 : ∀ k, qDiff 0 b k = shiftSeq b k := fun k => by simp [qDiff, shiftSeq]
  refine ⟨?_, ?_⟩
  · rw [det_hankel_eq _ (show 2 * (m + 1) = (m + 1) + (m + 1) by omega), hB1]; grind
  · rw [det_hankel_eq _ (show 2 * m + 1 = (m + 1) + m by omega), hB2, det_hankel_congr hq0 m]

/-! ============================================================================
    PART 4: KERNEL-CHECKED NON-VACUITY WITNESSES & SHARPNESS COUNTEREXAMPLES
    ============================================================================ -/

/-- Non-vacuity witness 1: Period-doubling `(1,-1,1)` satisfies Theorem 2 for all `n ≥ 1`. -/
theorem witness_period_doubling_nonsingular (n : Nat) :
    det (hankel (ecSeq 1 (-1) 1) n) ≠ 0 :=
  ecSeq_odd_nonsingular 1 (-1) 1 (by decide) (by decide) (by decide) n

/-- Non-vacuity witness 2: Shifted ruler `1 + v2(n+1)` satisfies Theorem 2 for all `n ≥ 1`. -/
theorem witness_shifted_ruler_nonsingular (n : Nat) :
    det (hankel (fun k => 1 + (v2 (k + 1) : Int)) n) ≠ 0 := by
  rw [det_hankel_congr (fun k => (ecSeq_shifted_ruler_eq_v2 k).symm)]
  exact ecSeq_odd_nonsingular 1 1 1 (by decide) (by decide) (by decide) n

/-- Sharpness counterexample 1 (Mod-16 Breakdown on Period-Doubling):
    Evaluated in milliseconds via our kernel-verified Theorem 1 engine (avoiding `15! ~ 10^12` Laplace terms!).
    Proves `det H_7(pd) = -1` and `det H_15(pd) = -9`, so period-8 periodicity FAILS mod 16! -/
theorem witness_period_doubling_mod16_fails :
    det (hankel (ecSeq 1 (-1) 1) 7) = -1 ∧
    det (hankel (ecSeq 1 (-1) 1) 15) = -9 ∧
    det (hankel (ecSeq 1 (-1) 1) 7) % 16 ≠ det (hankel (ecSeq 1 (-1) 1) 15) % 16 := by
  have hA1 : hankelA 1 (-1) 1 1 = 1 := by
    have := hankelA_odd 1 (-1) 1 0; simp [hankelB_zero, altSign, intPow] at this; exact this
  have hB1 : hankelB 1 (-1) 1 1 = -1 := by
    have := hankelB_odd 1 (-1) 1 0; simp [hA1, hankelB_zero, hankelC_zero, intPow] at this; exact this
  have hC1 : hankelC 1 (-1) 1 1 = 2 := by
    have := hankelC_odd 1 (-1) 1 0; simp [hA1, hankelC_zero, altSign, intPow] at this; exact this
  have hA2 : hankelA 1 (-1) 1 2 = 1 := by
    have := hankelA_even 1 (-1) 1 0; simp [hA1, hankelC_zero, altSign, intPow] at this; exact this
  have hB3 : hankelB 1 (-1) 1 3 = 1 := by
    have := hankelB_odd 1 (-1) 1 1; simp [hA2, hB1, intPow] at this; exact this
  have hA4 : hankelA 1 (-1) 1 4 = -3 := by
    have := hankelA_even 1 (-1) 1 1; simp [hA2, hC1, altSign, intPow] at this; exact this
  have hB7 : hankelB 1 (-1) 1 7 = 3 := by
    have := hankelB_odd 1 (-1) 1 3; simp [hA4, hB3, intPow] at this; exact this
  have hA7 : hankelA 1 (-1) 1 7 = -1 := by
    have := hankelA_odd 1 (-1) 1 3; simp [hB3, altSign, intPow] at this; exact this
  have hA15 : hankelA 1 (-1) 1 15 = -9 := by
    have := hankelA_odd 1 (-1) 1 7; simp [hB7, altSign, intPow] at this; exact this
  refine ⟨hA7, hA15, ?_⟩
  change hankelA 1 (-1) 1 7 % 16 ≠ hankelA 1 (-1) 1 15 % 16
  rw [hA7, hA15]; decide

/-- Sharpness counterexample 2 (Mod-16 Breakdown on Shifted Ruler `1 + v2(n+1)`):
    Proves `det H_1 = 1` and `det H_9 = 9`, so period-8 periodicity FAILS mod 16! -/
theorem witness_shifted_ruler_mod16_fails :
    det (hankel (ecSeq 1 1 1) 1) = 1 ∧
    det (hankel (ecSeq 1 1 1) 9) = 9 ∧
    det (hankel (ecSeq 1 1 1) 1) % 16 ≠ det (hankel (ecSeq 1 1 1) 9) % 16 := by
  have hA1 : hankelA 1 1 1 1 = 1 := by
    have := hankelA_odd 1 1 1 0; simp [hankelB_zero, altSign, intPow] at this; exact this
  have hB1 : hankelB 1 1 1 1 = 1 := by
    have := hankelB_odd 1 1 1 0; simp [hA1, hankelB_zero, hankelC_zero, intPow] at this; exact this
  have hA2 : hankelA 1 1 1 2 = -3 := by
    have := hankelA_even 1 1 1 0; simp [hA1, hankelC_zero, altSign, intPow] at this; exact this
  have hB2 : hankelB 1 1 1 2 = 1 := by
    have := hankelB_even 1 1 1 0; simp [hA1, hB1, intPow] at this; exact this
  have hB4 : hankelB 1 1 1 4 = -3 := by
    have := hankelB_even 1 1 1 1; simp [hA2, hB2, intPow] at this; exact this
  have hA9 : hankelA 1 1 1 9 = 9 := by
    have := hankelA_odd 1 1 1 4; simp [hB4, altSign, intPow] at this; exact this
  refine ⟨hA1, hA9, ?_⟩
  change hankelA 1 1 1 1 % 16 ≠ hankelA 1 1 1 9 % 16
  rw [hA1, hA9]; decide

/-- Sharpness counterexample 3 (Dropping oddness of `c`, `α`, or `β` breaks non-singularity):
    - Even `c = 0`: `det H_1(ecSeq 0 1 1) = 0`.
    - Even `α = 0`: `det H_2(ecSeq 1 0 1) = 0`.
    - Even `β = 2`: `det H_2(ecSeq 1 (-1) 2) = 0`. -/
theorem witness_oddness_hypotheses_sharp :
    det (hankel (ecSeq 0 1 1) 1) = 0 ∧
    det (hankel (ecSeq 1 0 1) 2) = 0 ∧
    det (hankel (ecSeq 1 (-1) 2) 2) = 0 := by
  refine ⟨ruler_family_odd_zero 1 1 0, ?_, ?_⟩
  · change hankelA 1 0 1 2 = 0
    have hA1 : hankelA 1 0 1 1 = 1 := by
      have := hankelA_odd 1 0 1 0; simp [hankelB_zero, altSign, intPow] at this; exact this
    have := hankelA_even 1 0 1 0; simp [hA1, hankelC_zero, altSign, intPow] at this; exact this
  · change hankelA 1 (-1) 2 2 = 0
    have hA1 : hankelA 1 (-1) 2 1 = 1 := by
      have := hankelA_odd 1 (-1) 2 0; simp [hankelB_zero, altSign, intPow] at this; exact this
    have := hankelA_even 1 (-1) 2 0; simp [hA1, hankelC_zero, altSign, intPow] at this; exact this

/-- Concrete witness for Theorem 4 (Signed Ruler): `H_2 = 0`, `H_6 = 0`, and `H_4 = -16` (exact `v_2 = 4`). -/
theorem witness_signed_ruler_concrete :
    det (hankel (fun n => altSign (v2 (n + 1))) 2) = 0 ∧
    det (hankel (fun n => altSign (v2 (n + 1))) 6) = 0 ∧
    det (hankel (fun n => altSign (v2 (n + 1))) 4) = -16 := by
  refine ⟨signed_ruler_vanish_mod4_eq2 0, signed_ruler_vanish_mod4_eq2 1, ?_⟩
  rw [det_hankel_congr (fun k => (ecSeq_signed_ruler_eq_v2 k).symm)]
  change hankelA 1 (-1) 0 4 = -16
  have hA1 : hankelA 1 (-1) 0 1 = 1 := by
    have := hankelA_odd 1 (-1) 0 0; simp [hankelB_zero, altSign, intPow] at this; exact this
  have hC1 : hankelC 1 (-1) 0 1 = 4 := by
    have := hankelC_odd 1 (-1) 0 0; simp [hA1, hankelC_zero, altSign, intPow] at this; exact this
  have hA2 : hankelA 1 (-1) 0 2 = 0 := by
    have := hankelA_even 1 (-1) 0 0; simp [hA1, hankelC_zero, altSign, intPow] at this; exact this
  have := hankelA_even 1 (-1) 0 1; simp [hA2, hC1, altSign, intPow] at this; exact this

end BitwiseHankelLDU
