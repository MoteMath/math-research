/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BooleanTropicalKleeneStarEngine.Defs

/-!
# Theorems (`boolean-tropical-kleene-star-engine`)

Full proofs of the headline infinite theorems of Boolean and Tropical-Bitwise Semiring Kleene-Star Infinite Engine.
-/

namespace BSKSE

namespace KleeneSemiring

variable {α : Type u} [KleeneSemiring α]

theorem zero_add (a : α) : add zero a = a := by
  rw [add_comm, add_zero]

theorem le_refl (a : α) : le a a := add_idem a

theorem le_antisymm {a b : α} (h1 : le a b) (h2 : le b a) : a = b := by
  unfold le at h1 h2
  rw [← h1, add_comm, h2]

theorem le_trans {a b c : α} (h1 : le a b) (h2 : le b c) : le a c := by
  unfold le at *
  rw [← h2, ← add_assoc, h1]

theorem zero_le (a : α) : le zero a := zero_add a

theorem le_add_left (a b : α) : le a (add a b) := by
  unfold le; rw [← add_assoc, add_idem]

theorem le_add_right (a b : α) : le b (add a b) := by
  rw [add_comm]; exact le_add_left b a

theorem add_le {a b c : α} (ha : le a c) (hb : le b c) : le (add a b) c := by
  unfold le at *
  rw [add_assoc, hb, ha]

theorem add_le_iff {a b c : α} : le (add a b) c ↔ le a c ∧ le b c :=
  ⟨fun h => ⟨le_trans (le_add_left a b) h, le_trans (le_add_right a b) h⟩,
   fun ⟨ha, hb⟩ => add_le ha hb⟩

theorem add_mono {a b c d : α} (h1 : le a b) (h2 : le c d) : le (add a c) (add b d) :=
  add_le (le_trans h1 (le_add_left b d)) (le_trans h2 (le_add_right b d))

theorem mul_mono_left {a b c : α} (h : le a b) : le (mul c a) (mul c b) := by
  unfold le at *
  rw [← left_distrib, h]

theorem mul_mono_right {a b c : α} (h : le a b) : le (mul a c) (mul b c) := by
  unfold le at *
  rw [← right_distrib, h]

theorem mul_mono {a b c d : α} (h1 : le a b) (h2 : le c d) : le (mul a c) (mul b d) :=
  le_trans (mul_mono_right h1) (mul_mono_left h2)

theorem le_star_one (a : α) : le one (star a) := one_le_star a

theorem le_star_mul_left (a : α) : le (mul a (star a)) (star a) := mul_star_le a

theorem le_star_mul_right (a : α) : le (mul (star a) a) (star a) := star_mul_le a

theorem star_ind_left' {a b c : α} (hb : le b c) (hac : le (mul a c) c) :
    le (mul (star a) b) c :=
  star_ind_left a b c (add_le hb hac)

theorem star_ind_right' {a b c : α} (hb : le b c) (hca : le (mul c a) c) :
    le (mul b (star a)) c :=
  star_ind_right a b c (add_le hb hca)

theorem star_idem (a : α) : mul (star a) (star a) = star a := by
  apply le_antisymm
  · exact star_ind_left' (le_refl _) (le_star_mul_left a)
  · have h := mul_mono_right (c := star a) (le_star_one a)
    rw [one_mul] at h; exact h

theorem star_eq_one_of_le_one {a : α} (h : le a one) : star a = one := by
  apply le_antisymm
  · have h1 := star_ind_left' (a := a) (b := one) (c := one) (le_refl one) (by rw [mul_one]; exact h)
    rw [mul_one] at h1; exact h1
  · exact le_star_one a

end KleeneSemiring

section FinSum

variable {α : Type u} [KleeneSemiring α]

open KleeneSemiring

theorem finSum_congr {n : Nat} {f g : Fin n → α} (h : ∀ i, f i = g i) :
    finSum n f = finSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finSum]
    rw [ih (fun i => h _), h]

theorem finSum_zero (n : Nat) : finSum n (fun _ => (zero : α)) = zero := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [finSum, ih, add_zero]

theorem finSum_add {n : Nat} (f g : Fin n → α) :
    finSum n (fun i => add (f i) (g i)) = add (finSum n f) (finSum n g) := by
  induction n with
  | zero => simp only [finSum, add_zero]
  | succ n ih =>
    simp only [finSum]
    rw [ih (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)]
    rw [add_assoc, ← add_assoc (finSum n (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)),
        add_comm (finSum n (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)), add_assoc, ← add_assoc]

theorem mul_finSum {n : Nat} (c : α) (f : Fin n → α) :
    mul c (finSum n f) = finSum n (fun i => mul c (f i)) := by
  induction n with
  | zero => simp only [finSum, mul_zero]
  | succ n ih => simp only [finSum, left_distrib, ih]

theorem finSum_mul {n : Nat} (f : Fin n → α) (c : α) :
    mul (finSum n f) c = finSum n (fun i => mul (f i) c) := by
  induction n with
  | zero => simp only [finSum, zero_mul]
  | succ n ih => simp only [finSum, right_distrib, ih]

theorem finSum_swap {m n : Nat} (f : Fin m → Fin n → α) :
    finSum m (fun i => finSum n (fun j => f i j)) =
    finSum n (fun j => finSum m (fun i => f i j)) := by
  induction m with
  | zero => simp only [finSum, finSum_zero]
  | succ m ih =>
    simp only [finSum]
    rw [ih (fun i j => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ j), ← finSum_add]

theorem le_finSum {n : Nat} (f : Fin n → α) (k : Fin n) : le (f k) (finSum n f) := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    simp only [finSum]
    by_cases hk : k.val < n
    · exact le_trans (ih (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) ⟨k.val, hk⟩) (le_add_left _ _)
    · have hk_lt := k.isLt
      have heq : k = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext (by dsimp; omega)
      rw [heq]; exact le_add_right _ _

theorem finSum_le {n : Nat} {f : Fin n → α} {c : α} (h : ∀ i, le (f i) c) :
    le (finSum n f) c := by
  induction n with
  | zero => exact zero_le c
  | succ n ih =>
    simp only [finSum]
    exact add_le (ih (fun i => h _)) (h _)

theorem finSum_mono {n : Nat} {f g : Fin n → α} (h : ∀ i, le (f i) (g i)) :
    le (finSum n f) (finSum n g) :=
  finSum_le (fun i => le_trans (h i) (le_finSum g i))

theorem finSum_single {n : Nat} (k : Fin n) (f : Fin n → α)
    (h : ∀ i, i ≠ k → f i = zero) : finSum n f = f k := by
  apply le_antisymm
  · apply finSum_le
    intro i
    by_cases hik : i = k
    · rw [hik]; exact le_refl _
    · rw [h i hik]; exact zero_le _
  · exact le_finSum f k

/-- Splitting `finSum (n + m)` into lower `n` and upper `m` terms. -/
theorem finSum_append {n m : Nat} (f : Fin (n + m) → α) :
    finSum (n + m) f =
      add (finSum n (fun i => f ⟨i.val, by omega⟩))
          (finSum m (fun j => f ⟨n + j.val, by omega⟩)) := by
  induction m with
  | zero =>
    simp only [finSum, add_zero]
    exact finSum_congr (fun i => rfl)
  | succ m ih =>
    have hstep : finSum (n + (m + 1)) f =
        add (finSum (n + m) (fun i => f ⟨i.val, by omega⟩))
            (f ⟨n + m, by omega⟩) := rfl
    rw [hstep, ih (fun i => f ⟨i.val, by omega⟩)]
    simp only [finSum]
    rw [add_assoc]

/-- Exact split of `finSum (n * 2)` into lower half `[0, n)` and upper half `[n, 2n)`. -/
theorem finSum_mul_two {n : Nat} (f : Fin (n * 2) → α) :
    finSum (n * 2) f =
      add (finSum n (fun i => f ⟨i.val, by omega⟩))
          (finSum n (fun j => f ⟨n + j.val, by omega⟩)) := by
  have heq : n * 2 = n + n := by omega
  -- Prove directly via finSum_append using cast on n*2 = n+n
  let g : Fin (n + n) → α := fun i => f ⟨i.val, by omega⟩
  have h1 : finSum (n * 2) f = finSum (n + n) g := by
    have aux : ∀ (a b : Nat) (hab : a = b) (fa : Fin a → α) (fb : Fin b → α),
        (∀ i (hi : i < a), fa ⟨i, hi⟩ = fb ⟨i, hab ▸ hi⟩) → finSum a fa = finSum b fb := by
      intro a b hab
      subst hab
      intro fa fb h
      exact finSum_congr (fun i => h i.val i.isLt)
    exact aux (n * 2) (n + n) heq f g (fun i hi => rfl)
  rw [h1, finSum_append]

end FinSum

section MatrixAlgebra

variable {α : Type u} [KleeneSemiring α]

open KleeneSemiring

theorem matLe_refl {n : Nat} (A : Mat α n) : matLe A A := fun _ _ => le_refl _

theorem matLe_antisymm {n : Nat} {A B : Mat α n} (h1 : matLe A B) (h2 : matLe B A) : A = B := by
  funext i j; exact le_antisymm (h1 i j) (h2 i j)

theorem matLe_trans {n : Nat} {A B C : Mat α n} (h1 : matLe A B) (h2 : matLe B C) : matLe A C :=
  fun i j => le_trans (h1 i j) (h2 i j)

theorem matAdd_le {n : Nat} {A B C : Mat α n} (h1 : matLe A C) (h2 : matLe B C) :
    matLe (matAdd A B) C := fun i j => add_le (h1 i j) (h2 i j)

theorem matLe_add_left {n : Nat} (A B : Mat α n) : matLe A (matAdd A B) :=
  fun _ _ => le_add_left _ _

theorem matLe_add_right {n : Nat} (A B : Mat α n) : matLe B (matAdd A B) :=
  fun _ _ => le_add_right _ _

theorem matMul_mono {n : Nat} {A B C D : Mat α n} (h1 : matLe A B) (h2 : matLe C D) :
    matLe (matMul A C) (matMul B D) :=
  fun i j => finSum_mono (fun k => mul_mono (h1 i k) (h2 k j))

theorem matMul_id_left {n : Nat} (A : Mat α n) : matMul (matId n) A = A := by
  funext i j
  simp only [matMul, matId]
  rw [finSum_single i]
  · simp [one_mul]
  · intro k hk
    have : i ≠ k := fun h => hk h.symm
    simp [this, zero_mul]

theorem matMul_id_right {n : Nat} (A : Mat α n) : matMul A (matId n) = A := by
  funext i j
  simp only [matMul, matId]
  rw [finSum_single j]
  · simp [mul_one]
  · intro k hk
    simp [hk, mul_zero]

theorem matMul_assoc {n : Nat} (A B C : Mat α n) :
    matMul (matMul A B) C = matMul A (matMul B C) := by
  funext i j
  simp only [matMul]
  calc finSum n (fun k => mul (finSum n (fun l => mul (A i l) (B l k))) (C k j))
      = finSum n (fun k => finSum n (fun l => mul (mul (A i l) (B l k)) (C k j))) :=
        finSum_congr (fun k => finSum_mul _ _)
    _ = finSum n (fun l => finSum n (fun k => mul (mul (A i l) (B l k)) (C k j))) :=
        finSum_swap _
    _ = finSum n (fun l => finSum n (fun k => mul (A i l) (mul (B l k) (C k j)))) :=
        finSum_congr (fun l => finSum_congr (fun k => mul_assoc _ _ _))
    _ = finSum n (fun l => mul (A i l) (finSum n (fun k => mul (B l k) (C k j)))) :=
        finSum_congr (fun l => (mul_finSum _ _).symm)

theorem matMul_add_left {n : Nat} (A B C : Mat α n) :
    matMul A (matAdd B C) = matAdd (matMul A B) (matMul A C) := by
  funext i j
  simp only [matMul, matAdd]
  rw [← finSum_add]
  exact finSum_congr (fun k => left_distrib _ _ _)

theorem matMul_add_right {n : Nat} (A B C : Mat α n) :
    matMul (matAdd A B) C = matAdd (matMul A C) (matMul B C) := by
  funext i j
  simp only [matMul, matAdd]
  rw [← finSum_add]
  exact finSum_congr (fun k => right_distrib _ _ _)

theorem matMul_single_left {n : Nat} (p q : Fin n) (c : α) (B : Mat α n) (i j : Fin n) :
    matMul (matSingle p q c) B i j = if i = p then mul c (B q j) else zero := by
  simp only [matMul, matSingle]
  by_cases hip : i = p
  · subst hip
    simp only [true_and, ↓reduceIte]
    rw [finSum_single q]
    · simp
    · intro k hk; simp [hk, zero_mul]
  · simp only [hip, false_and, ↓reduceIte]
    have h0 : (fun k : Fin n => mul (zero : α) (B k j)) = fun _ => zero := by
      funext k; exact zero_mul _
    rw [h0, finSum_zero]

theorem matMul_single_right {n : Nat} (A : Mat α n) (p q : Fin n) (c : α) (i j : Fin n) :
    matMul A (matSingle p q c) i j = if j = q then mul (A i p) c else zero := by
  simp only [matMul, matSingle]
  by_cases hjq : j = q
  · subst hjq
    simp only [and_true, ↓reduceIte]
    rw [finSum_single p]
    · simp
    · intro k hk; simp [hk, mul_zero]
  · simp only [hjq, and_false, ↓reduceIte]
    have h0 : (fun k : Fin n => mul (A i k) (zero : α)) = fun _ => zero := by
      funext k; exact mul_zero _
    rw [h0, finSum_zero]

theorem IsMatStar.unique {n : Nat} {M S₁ S₂ : Mat α n}
    (h1 : IsMatStar M S₁) (h2 : IsMatStar M S₂) : S₁ = S₂ := by
  apply matLe_antisymm
  · have := h1.ind_left (matId n) S₂ h2.one_le h2.mul_left
    rwa [matMul_id_right] at this
  · have := h2.ind_left (matId n) S₁ h1.one_le h1.mul_left
    rwa [matMul_id_right] at this

theorem IsMatStar.star_mul_star {n : Nat} {M S : Mat α n} (h : IsMatStar M S) :
    matMul S S = S := by
  apply matLe_antisymm
  · exact h.ind_left S S (matLe_refl S) h.mul_left
  · have := matMul_mono h.one_le (matLe_refl S)
    rwa [matMul_id_left] at this

theorem IsMatStar.le_self {n : Nat} {M S : Mat α n} (h : IsMatStar M S) :
    matLe M S := by
  have := matMul_mono (matLe_refl M) h.one_le
  rw [matMul_id_right] at this
  exact matLe_trans this h.mul_left

theorem IsMatStar.pow_le {n : Nat} {M S : Mat α n} (h : IsMatStar M S) :
    ∀ t : Nat, matLe (matPow M t) S
  | 0 => h.one_le
  | t + 1 => matLe_trans (matMul_mono (h.pow_le t) (matLe_refl M)) h.mul_right

theorem IsMatStar.trans {n : Nat} {M S : Mat α n} (h : IsMatStar M S) (i k j : Fin n) :
    le (mul (S i k) (S k j)) (S i j) := by
  have hmul : matLe (matMul S S) S := by rw [h.star_mul_star]; exact matLe_refl S
  exact le_trans (le_finSum (fun l => mul (S i l) (S l j)) k) (hmul i j)

/-! ============================================================================
    SECTION 2: ENGINE THEOREM A — GENERAL 2x2 BLOCK CONWAY-SCHUR KLEENE STAR
    ============================================================================ -/

theorem blockMat_eta {n : Nat} (M : Mat α (n * 2)) :
    M = blockMat (blkTL M) (blkTR M) (blkBL M) (blkBR M) := by
  funext i j
  simp only [blockMat, blkTL, blkTR, blkBL, blkBR]
  split
  · split
    · rfl
    · congr 1; apply Fin.ext; dsimp; omega
  · split
    · congr 1; apply Fin.ext; dsimp; omega
    · congr 1 <;> (apply Fin.ext; dsimp; omega)

omit [KleeneSemiring α] in

theorem blkTL_blockMat {n : Nat} (A B C D : Mat α n) : blkTL (blockMat A B C D) = A := by
  funext i j; simp [blkTL, blockMat, i.isLt, j.isLt]

omit [KleeneSemiring α] in

theorem blkTR_blockMat {n : Nat} (A B C D : Mat α n) : blkTR (blockMat A B C D) = B := by
  funext i j
  have h1 : ¬ (n + j.val < n) := by omega
  simp [blkTR, blockMat, i.isLt, h1]

omit [KleeneSemiring α] in

theorem blkBL_blockMat {n : Nat} (A B C D : Mat α n) : blkBL (blockMat A B C D) = C := by
  funext i j
  have h1 : ¬ (n + i.val < n) := by omega
  simp [blkBL, blockMat, j.isLt, h1]

omit [KleeneSemiring α] in

theorem blkBR_blockMat {n : Nat} (A B C D : Mat α n) : blkBR (blockMat A B C D) = D := by
  funext i j
  have h1 : ¬ (n + i.val < n) := by omega
  have h2 : ¬ (n + j.val < n) := by omega
  simp [blkBR, blockMat, h1, h2]

theorem blockMat_le_iff {n : Nat} {A₁ B₁ C₁ D₁ A₂ B₂ C₂ D₂ : Mat α n} :
    matLe (blockMat A₁ B₁ C₁ D₁) (blockMat A₂ B₂ C₂ D₂) ↔
      matLe A₁ A₂ ∧ matLe B₁ B₂ ∧ matLe C₁ C₂ ∧ matLe D₁ D₂ := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i j; have := h ⟨i.val, by omega⟩ ⟨j.val, by omega⟩
      simpa [blockMat, i.isLt, j.isLt] using this
    · intro i j; have := h ⟨i.val, by omega⟩ ⟨n + j.val, by omega⟩
      have hj : ¬ (n + j.val < n) := by omega
      simpa [blockMat, i.isLt, hj] using this
    · intro i j; have := h ⟨n + i.val, by omega⟩ ⟨j.val, by omega⟩
      have hi : ¬ (n + i.val < n) := by omega
      simpa [blockMat, hi, j.isLt] using this
    · intro i j; have := h ⟨n + i.val, by omega⟩ ⟨n + j.val, by omega⟩
      have hi : ¬ (n + i.val < n) := by omega
      have hj : ¬ (n + j.val < n) := by omega
      simpa [blockMat, hi, hj] using this
  · rintro ⟨hA, hB, hC, hD⟩ i j
    simp only [blockMat]
    split
    · split
      · exact hA _ _
      · exact hB _ _
    · split
      · exact hC _ _
      · exact hD _ _

theorem blockMat_id (n : Nat) :
    (matId (n * 2) : Mat α (n * 2)) = blockMat (matId n) (matZero n) (matZero n) (matId n) := by
  funext i j
  simp only [matId, blockMat, matZero]
  by_cases hi : i.val < n <;> by_cases hj : j.val < n
  · simp only [hi, hj, ↓reduceDIte]
    by_cases h : i = j
    · subst h; simp
    · have h' : (⟨i.val, hi⟩ : Fin n) ≠ ⟨j.val, hj⟩ := by
        intro he; apply h; apply Fin.ext; have hv := congrArg Fin.val he; exact hv
      simp [h, h']
  · simp only [hi, hj, ↓reduceDIte]
    have h : i ≠ j := fun he => by subst he; omega
    simp [h]
  · simp only [hi, hj, ↓reduceDIte]
    have h : i ≠ j := fun he => by subst he; omega
    simp [h]
  · simp only [hi, hj, ↓reduceDIte]
    by_cases h : i = j
    · subst h; simp
    · have h' : (⟨i.val - n, by omega⟩ : Fin n) ≠ ⟨j.val - n, by omega⟩ := by
        intro he; apply h; apply Fin.ext; have := congrArg Fin.val he; dsimp at this; omega
      simp [h, h']

theorem blockMat_mul {n : Nat} (A₁ B₁ C₁ D₁ A₂ B₂ C₂ D₂ : Mat α n) :
    matMul (blockMat A₁ B₁ C₁ D₁) (blockMat A₂ B₂ C₂ D₂) =
      blockMat
        (matAdd (matMul A₁ A₂) (matMul B₁ C₂))
        (matAdd (matMul A₁ B₂) (matMul B₁ D₂))
        (matAdd (matMul C₁ A₂) (matMul D₁ C₂))
        (matAdd (matMul C₁ B₂) (matMul D₁ D₂)) := by
  funext i j
  simp only [matMul]
  rw [finSum_mul_two]
  simp only [blockMat, matAdd, matMul]
  by_cases hi : i.val < n <;> by_cases hj : j.val < n
  · simp only [hi, hj, ↓reduceDIte]
    congr 1
    · exact finSum_congr (fun k => by simp [k.isLt])
    · exact finSum_congr (fun k => by
        have hk : ¬ (n + k.val < n) := by omega
        simp [hk])
  · simp only [hi, hj, ↓reduceDIte]
    congr 1
    · exact finSum_congr (fun k => by simp [k.isLt])
    · exact finSum_congr (fun k => by
        have hk : ¬ (n + k.val < n) := by omega
        simp [hk])
  · simp only [hi, hj, ↓reduceDIte]
    congr 1
    · exact finSum_congr (fun k => by simp [k.isLt])
    · exact finSum_congr (fun k => by
        have hk : ¬ (n + k.val < n) := by omega
        simp [hk])
  · simp only [hi, hj, ↓reduceDIte]
    congr 1
    · exact finSum_congr (fun k => by simp [k.isLt])
    · exact finSum_congr (fun k => by
        have hk : ¬ (n + k.val < n) := by omega
        simp [hk])

/-- **Engine Theorem A (General 2×2 Block Conway-Schur Kleene Star):**
    For any `KleeneSemiring α` and any `n × n` blocks `A, B, C, D`, if `Ds = D*`
    and `S = (A + B * Ds * C)*`, then the exact Kleene star of `[[A, B], [C, D]]` is
    `[[S, S * B * Ds], [Ds * C * S, Ds + Ds * C * S * B * Ds]]`. -/
theorem block_conway_schur_star {n : Nat} {A B C D Ds S : Mat α n}
    (hD : IsMatStar D Ds)
    (hS : IsMatStar (matAdd A (matMul (matMul B Ds) C)) S) :
    IsMatStar (blockMat A B C D)
      (blockMat S
                (matMul (matMul S B) Ds)
                (matMul (matMul Ds C) S)
                (matAdd Ds (matMul (matMul (matMul (matMul Ds C) S) B) Ds))) := by
  -- Useful abbreviations for inequalities from hS and hD
  have hA_S : matLe (matMul A S) S := by
    have := hS.mul_left
    rw [matMul_add_right] at this
    exact matLe_trans (matLe_add_left _ _) this
  have hBDC_S : matLe (matMul (matMul (matMul B Ds) C) S) S := by
    have := hS.mul_left
    rw [matMul_add_right] at this
    exact matLe_trans (matLe_add_right _ _) this
  have hS_A : matLe (matMul S A) S := by
    have := hS.mul_right
    rw [matMul_add_left] at this
    exact matLe_trans (matLe_add_left _ _) this
  have hS_BDC : matLe (matMul S (matMul (matMul B Ds) C)) S := by
    have := hS.mul_right
    rw [matMul_add_left] at this
    exact matLe_trans (matLe_add_right _ _) this
  constructor
  · -- 1. I ≤ Star
    rw [blockMat_id, blockMat_le_iff]
    refine ⟨hS.one_le, fun _ _ => zero_le _, fun _ _ => zero_le _,
            matLe_trans hD.one_le (matLe_add_left _ _)⟩
  · -- 2. M * Star ≤ Star
    rw [blockMat_mul, blockMat_le_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply matAdd_le hA_S
      simpa [matMul_assoc] using hBDC_S
    · apply matAdd_le
      · have := matMul_mono hA_S (matLe_refl (matMul B Ds))
        simpa [matMul_assoc] using this
      · rw [matMul_add_left]
        apply matAdd_le
        · have := matMul_mono hS.one_le (matLe_refl (matMul B Ds))
          rw [matMul_id_left] at this
          simpa [matMul_assoc] using this
        · have := matMul_mono hBDC_S (matLe_refl (matMul B Ds))
          simpa [matMul_assoc] using this
    · apply matAdd_le
      · have := matMul_mono hD.one_le (matLe_refl (matMul C S))
        rw [matMul_id_left] at this
        simpa [matMul_assoc] using this
      · have := matMul_mono hD.mul_left (matLe_refl (matMul C S))
        simpa [matMul_assoc] using this
    · apply matAdd_le
      · have := matMul_mono hD.one_le (matLe_refl (matMul C (matMul (matMul S B) Ds)))
        rw [matMul_id_left] at this
        exact matLe_trans (by simpa [matMul_assoc] using this) (matLe_add_right _ _)
      · rw [matMul_add_left]
        apply matAdd_le
        · exact matLe_trans hD.mul_left (matLe_add_left _ _)
        · have := matMul_mono hD.mul_left (matLe_refl (matMul C (matMul (matMul S B) Ds)))
          exact matLe_trans (by simpa [matMul_assoc] using this) (matLe_add_right _ _)
  · -- 3. Star * M ≤ Star
    rw [blockMat_mul, blockMat_le_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply matAdd_le hS_A
      simpa [matMul_assoc] using hS_BDC
    · apply matAdd_le
      · have := matMul_mono (matLe_refl (matMul S B)) hD.one_le
        rwa [matMul_id_right] at this
      · have := matMul_mono (matLe_refl (matMul S B)) hD.mul_right
        simpa [matMul_assoc] using this
    · apply matAdd_le
      · have := matMul_mono (matLe_refl (matMul Ds C)) hS_A
        simpa [matMul_assoc] using this
      · rw [matMul_add_right]
        apply matAdd_le
        · have := matMul_mono (matLe_refl (matMul Ds C)) hS.one_le
          rwa [matMul_id_right] at this
        · have := matMul_mono (matLe_refl (matMul Ds C)) hS_BDC
          simpa [matMul_assoc] using this
    · apply matAdd_le
      · have := matMul_mono (matLe_refl (matMul (matMul (matMul Ds C) S) B)) hD.one_le
        rw [matMul_id_right] at this
        exact matLe_trans this (matLe_add_right _ _)
      · rw [matMul_add_right]
        apply matAdd_le
        · exact matLe_trans hD.mul_right (matLe_add_left _ _)
        · have := matMul_mono (matLe_refl (matMul (matMul (matMul Ds C) S) B)) hD.mul_right
          exact matLe_trans (by simpa [matMul_assoc] using this) (matLe_add_right _ _)
  · -- 4. ind_left: B_in ≤ X ∧ M * X ≤ X → Star * B_in ≤ X
    intro Bin X hBX hMX
    rw [blockMat_eta Bin] at hBX ⊢
    rw [blockMat_eta X] at hBX hMX ⊢
    rw [blockMat_mul, blockMat_le_iff] at hMX
    rw [blockMat_le_iff] at hBX
    rw [blockMat_mul, blockMat_le_iff]
    let B1 := blkTL Bin; let B2 := blkTR Bin; let B3 := blkBL Bin; let B4 := blkBR Bin
    let X1 := blkTL X;   let X2 := blkTR X;   let X3 := blkBL X;   let X4 := blkBR X
    rcases hBX with ⟨hB1, hB2, hB3, hB4⟩
    rcases hMX with ⟨hMX1, hMX2, hMX3, hMX4⟩
    have solveCol : ∀ (P Q Bt Bb : Mat α n),
        matLe Bt P → matLe Bb Q →
        matLe (matAdd (matMul A P) (matMul B Q)) P →
        matLe (matAdd (matMul C P) (matMul D Q)) Q →
        matLe (matAdd (matMul S Bt) (matMul (matMul (matMul S B) Ds) Bb)) P ∧
        matLe (matAdd (matMul (matMul (matMul Ds C) S) Bt)
                      (matMul (matAdd Ds (matMul (matMul (matMul (matMul Ds C) S) B) Ds)) Bb)) Q := by
      intro P Q Bt Bb hBt hBb hTop hBot
      have hAP : matLe (matMul A P) P := matLe_trans (matLe_add_left _ _) hTop
      have hBQ : matLe (matMul B Q) P := matLe_trans (matLe_add_right _ _) hTop
      have hCP : matLe (matMul C P) Q := matLe_trans (matLe_add_left _ _) hBot
      have hDQ : matLe (matMul D Q) Q := matLe_trans (matLe_add_right _ _) hBot
      have hDsBb : matLe (matMul Ds Bb) Q := hD.ind_left Bb Q hBb hDQ
      have hDsCP : matLe (matMul Ds (matMul C P)) Q := hD.ind_left (matMul C P) Q hCP hDQ
      have hSchurP : matLe (matMul (matAdd A (matMul (matMul B Ds) C)) P) P := by
        rw [matMul_add_right]
        apply matAdd_le hAP
        have := matLe_trans (matMul_mono (matLe_refl B) hDsCP) hBQ
        simpa [matMul_assoc] using this
      have hBDsBb : matLe (matMul B (matMul Ds Bb)) P :=
        matLe_trans (matMul_mono (matLe_refl B) hDsBb) hBQ
      have hSBt : matLe (matMul S Bt) P := hS.ind_left Bt P hBt hSchurP
      have hSBDsBb : matLe (matMul S (matMul B (matMul Ds Bb))) P :=
        hS.ind_left _ P hBDsBb hSchurP
      constructor
      · apply matAdd_le hSBt
        simpa [matMul_assoc] using hSBDsBb
      · apply matAdd_le
        · have h1 := matLe_trans (matMul_mono (matLe_refl (matMul Ds C)) hSBt) (by simpa [matMul_assoc] using hDsCP)
          simpa [matMul_assoc] using h1
        · rw [matMul_add_right]
          apply matAdd_le hDsBb
          have h2 := matLe_trans (matMul_mono (matLe_refl (matMul Ds C)) hSBDsBb) (by simpa [matMul_assoc] using hDsCP)
          simpa [matMul_assoc] using h2
    have col1 := solveCol X1 X3 B1 B3 hB1 hB3 hMX1 hMX3
    have col2 := solveCol X2 X4 B2 B4 hB2 hB4 hMX2 hMX4
    exact ⟨col1.1, col2.1, col1.2, col2.2⟩
  · -- 5. ind_right: B_in ≤ X ∧ X * M ≤ X → B_in * Star ≤ X
    intro Bin X hBX hXM
    rw [blockMat_eta Bin] at hBX ⊢
    rw [blockMat_eta X] at hBX hXM ⊢
    rw [blockMat_mul, blockMat_le_iff] at hXM
    rw [blockMat_le_iff] at hBX
    rw [blockMat_mul, blockMat_le_iff]
    let B1 := blkTL Bin; let B2 := blkTR Bin; let B3 := blkBL Bin; let B4 := blkBR Bin
    let X1 := blkTL X;   let X2 := blkTR X;   let X3 := blkBL X;   let X4 := blkBR X
    rcases hBX with ⟨hB1, hB2, hB3, hB4⟩
    rcases hXM with ⟨hXM1, hXM2, hXM3, hXM4⟩
    have solveRow : ∀ (P Q Bl Br : Mat α n),
        matLe Bl P → matLe Br Q →
        matLe (matAdd (matMul P A) (matMul Q C)) P →
        matLe (matAdd (matMul P B) (matMul Q D)) Q →
        matLe (matAdd (matMul Bl S) (matMul Br (matMul (matMul Ds C) S))) P ∧
        matLe (matAdd (matMul Bl (matMul (matMul S B) Ds))
                      (matMul Br (matAdd Ds (matMul (matMul (matMul (matMul Ds C) S) B) Ds)))) Q := by
      intro P Q Bl Br hBl hBr hLeft hRight
      have hPA : matLe (matMul P A) P := matLe_trans (matLe_add_left _ _) hLeft
      have hQC : matLe (matMul Q C) P := matLe_trans (matLe_add_right _ _) hLeft
      have hPB : matLe (matMul P B) Q := matLe_trans (matLe_add_left _ _) hRight
      have hQD : matLe (matMul Q D) Q := matLe_trans (matLe_add_right _ _) hRight
      have hBrDs : matLe (matMul Br Ds) Q := hD.ind_right Br Q hBr hQD
      have hPBDs : matLe (matMul (matMul P B) Ds) Q := hD.ind_right (matMul P B) Q hPB hQD
      have hPSchur : matLe (matMul P (matAdd A (matMul (matMul B Ds) C))) P := by
        rw [matMul_add_left]
        apply matAdd_le hPA
        have := matLe_trans (matMul_mono hPBDs (matLe_refl C)) hQC
        simpa [matMul_assoc] using this
      have hBrDsC : matLe (matMul (matMul Br Ds) C) P :=
        matLe_trans (matMul_mono hBrDs (matLe_refl C)) hQC
      have hBlS : matLe (matMul Bl S) P := hS.ind_right Bl P hBl hPSchur
      have hBrDsCS : matLe (matMul (matMul (matMul Br Ds) C) S) P :=
        hS.ind_right _ P hBrDsC hPSchur
      constructor
      · apply matAdd_le hBlS
        simpa [matMul_assoc] using hBrDsCS
      · apply matAdd_le
        · have h1 := matLe_trans (matMul_mono hBlS (matLe_refl (matMul B Ds))) (by simpa [matMul_assoc] using hPBDs)
          simpa [matMul_assoc] using h1
        · rw [matMul_add_left]
          apply matAdd_le hBrDs
          have h2 := matLe_trans (matMul_mono hBrDsCS (matLe_refl (matMul B Ds))) (by simpa [matMul_assoc] using hPBDs)
          simpa [matMul_assoc] using h2
    have row1 := solveRow X1 X2 B1 B2 hB1 hB2 hXM1 hXM2
    have row2 := solveRow X3 X4 B3 B4 hB3 hB4 hXM3 hXM4
    exact ⟨row1.1, row1.2, row2.1, row2.2⟩

/-! ============================================================================
    SECTION 3: ENGINE THEOREM B — RANK-1 KLEENE SHERMAN-MORRISON-WOODBURY
               & ENGINE THEOREM C — CORNER-BRIDGE RENORMALIZATION + COLLAPSE
    ============================================================================ -/

/-- **Engine Theorem B (Rank-1 Kleene Sherman-Morrison-Woodbury):**
    In ANY `KleeneSemiring α`, if `IsMatStar A U`, then the exact Kleene star of
    `A + c · E_{p, s}` is `(smUpdate U p s c)_{i,j} = U_{i,j} + U_{i,p} · c · (U_{s,p} · c)* · U_{s,j}`. -/
theorem rank1_sherman_morrison_star {n : Nat} {A U : Mat α n}
    (hU : IsMatStar A U) (p s : Fin n) (c : α) :
    IsMatStar (matAdd A (matSingle p s c)) (smUpdate U p s c) := by
  let sc := star (mul (U s p) c)
  have hAU : matLe (matMul A U) U := hU.mul_left
  have hUA : matLe (matMul U A) U := hU.mul_right
  constructor
  · -- 1. I ≤ U'
    intro i j
    exact le_trans (hU.one_le i j) (le_add_left _ _)
  · -- 2. (A + E) * U' ≤ U'
    rw [matMul_add_right]
    apply matAdd_le
    · -- A * U' ≤ U'
      intro i j
      simp only [matMul, smUpdate]
      apply finSum_le
      intro k
      rw [left_distrib]
      apply add_le
      · exact le_trans (le_trans (le_finSum (fun l => mul (A i l) (U l j)) k) (hAU i j))
                       (le_add_left _ _)
      · have hAk : le (mul (A i k) (U k p)) (U i p) :=
          le_trans (le_finSum (fun l => mul (A i l) (U l p)) k) (hAU i p)
        have := mul_mono_right (c := mul (mul c sc) (U s j)) hAk
        have hrew : mul (A i k) (mul (mul (mul (U k p) c) sc) (U s j)) =
                    mul (mul (A i k) (U k p)) (mul (mul c sc) (U s j)) := by
          simp only [mul_assoc]
        rw [hrew]
        exact le_trans (by simpa [mul_assoc] using this) (le_add_right _ _)
    · -- E_{p,s}(c) * U' ≤ U'
      intro i j
      rw [matMul_single_left]
      by_cases hip : i = p
      · rw [hip]
        simp only [↓reduceIte, smUpdate]
        rw [left_distrib]
        have h1 : le (mul c (U s j)) (mul (mul (mul (U p p) c) sc) (U s j)) := by
          have hpp : le one (U p p) := by simpa [matId] using hU.one_le p p
          have hsc : le one sc := le_star_one _
          have hcore : le c (mul (mul (U p p) c) sc) := by
            have := mul_mono (mul_mono hpp (le_refl c)) hsc
            simpa [one_mul, mul_one] using this
          exact mul_mono_right hcore
        have h2 : le (mul c (mul (mul (mul (U s p) c) sc) (U s j)))
                     (mul (mul (mul (U p p) c) sc) (U s j)) := by
          have hpp : le one (U p p) := by simpa [matId] using hU.one_le p p
          have hstep : le (mul (mul (U s p) c) sc) sc := le_star_mul_left _
          have hcore : le (mul c (mul (mul (U s p) c) sc)) (mul (mul (U p p) c) sc) := by
            have ha := mul_mono_left (c := c) hstep
            have hb := mul_mono_right (c := sc) (mul_mono_right (c := c) hpp)
            rw [one_mul] at hb
            exact le_trans ha hb
          have hrew : mul c (mul (mul (mul (U s p) c) sc) (U s j)) =
                      mul (mul c (mul (mul (U s p) c) sc)) (U s j) := by
            simp only [mul_assoc]
          rw [hrew]
          exact mul_mono_right hcore
        exact le_trans (add_le h1 h2) (le_add_right _ _)
      · simp [hip, zero_le]
  · -- 3. U' * (A + E) ≤ U'
    rw [matMul_add_left]
    apply matAdd_le
    · -- U' * A ≤ U'
      intro i j
      simp only [matMul, smUpdate]
      apply finSum_le
      intro k
      rw [right_distrib]
      apply add_le
      · exact le_trans (le_trans (le_finSum (fun l => mul (U i l) (A l j)) k) (hUA i j))
                       (le_add_left _ _)
      · have hUk : le (mul (U s k) (A k j)) (U s j) :=
          le_trans (le_finSum (fun l => mul (U s l) (A l j)) k) (hUA s j)
        have := mul_mono_left (c := mul (mul (U i p) c) sc) hUk
        rw [mul_assoc]
        exact le_trans this (le_add_right _ _)
    · -- U' * E_{p,s}(c) ≤ U'
      intro i j
      rw [matMul_single_right]
      by_cases hjs : j = s
      · rw [hjs]
        simp only [↓reduceIte, smUpdate]
        rw [right_distrib]
        have hss : le one (U s s) := by simpa [matId] using hU.one_le s s
        have hsc : le one sc := le_star_one _
        have h1 : le (mul (U i p) c) (mul (mul (mul (U i p) c) sc) (U s s)) := by
          have := mul_mono (mul_mono_left (c := mul (U i p) c) hsc) hss
          simpa [mul_one] using this
        have h2 : le (mul (mul (mul (mul (U i p) c) sc) (U s p)) c)
                     (mul (mul (mul (U i p) c) sc) (U s s)) := by
          have hstep : le (mul sc (mul (U s p) c)) sc := le_star_mul_right _
          have hcore : le (mul (mul (U i p) c) (mul sc (mul (U s p) c)))
                          (mul (mul (U i p) c) sc) := mul_mono_left hstep
          have hcore2 := mul_mono hcore hss
          rw [mul_one] at hcore2
          simpa [mul_assoc] using hcore2
        exact le_trans (add_le h1 h2) (le_add_right _ _)
      · simp [hjs, zero_le]
  · -- 4. ind_left: B ≤ X ∧ (A + E) * X ≤ X → U' * B ≤ X
    intro B X hBX hMX
    rw [matMul_add_right] at hMX
    have hAX : matLe (matMul A X) X := matLe_trans (matLe_add_left _ _) hMX
    have hEX : matLe (matMul (matSingle p s c) X) X := matLe_trans (matLe_add_right _ _) hMX
    have hUB : matLe (matMul U B) X := hU.ind_left B X hBX hAX
    have hUX : matLe (matMul U X) X := hU.ind_left X X (matLe_refl X) hAX
    have hcX : ∀ j, le (mul c (X s j)) (X p j) := by
      intro j; have := hEX p j; rw [matMul_single_left] at this; simpa using this
    have hUXe : ∀ i k j, le (mul (U i k) (X k j)) (X i j) := by
      intro i k j; exact le_trans (le_finSum (fun l => mul (U i l) (X l j)) k) (hUX i j)
    intro i j
    simp only [matMul, smUpdate]
    apply finSum_le
    intro k
    rw [right_distrib]
    apply add_le
    · exact le_trans (le_finSum (fun l => mul (U i l) (B l j)) k) (hUB i j)
    · have hUsB : le (mul (U s k) (B k j)) (X s j) :=
        le_trans (le_finSum (fun l => mul (U s l) (B l j)) k) (hUB s j)
      have hloop : le (mul (mul (U s p) c) (X s j)) (X s j) := by
        rw [mul_assoc]
        exact le_trans (mul_mono_left (hcX j)) (hUXe s p j)
      have hsc_le : le (mul sc (mul (U s k) (B k j))) (X s j) :=
        star_ind_left' hUsB hloop
      have hstep1 : le (mul c (mul sc (mul (U s k) (B k j)))) (X p j) :=
        le_trans (mul_mono_left hsc_le) (hcX j)
      have hstep2 : le (mul (U i p) (mul c (mul sc (mul (U s k) (B k j))))) (X i j) :=
        le_trans (mul_mono_left hstep1) (hUXe i p j)
      simpa [mul_assoc] using hstep2
  · -- 5. ind_right: B ≤ X ∧ X * (A + E) ≤ X → B * U' ≤ X
    intro B X hBX hXM
    rw [matMul_add_left] at hXM
    have hXA : matLe (matMul X A) X := matLe_trans (matLe_add_left _ _) hXM
    have hXE : matLe (matMul X (matSingle p s c)) X := matLe_trans (matLe_add_right _ _) hXM
    have hBU : matLe (matMul B U) X := hU.ind_right B X hBX hXA
    have hXU : matLe (matMul X U) X := hU.ind_right X X (matLe_refl X) hXA
    have hXc : ∀ i, le (mul (X i p) c) (X i s) := by
      intro i; have := hXE i s; rw [matMul_single_right] at this; simpa using this
    have hXUe : ∀ i k j, le (mul (X i k) (U k j)) (X i j) := by
      intro i k j; exact le_trans (le_finSum (fun l => mul (X i l) (U l j)) k) (hXU i j)
    intro i j
    simp only [matMul, smUpdate]
    apply finSum_le
    intro k
    rw [left_distrib]
    apply add_le
    · exact le_trans (le_finSum (fun l => mul (B i l) (U l j)) k) (hBU i j)
    · have hBUp : le (mul (B i k) (U k p)) (X i p) :=
        le_trans (le_finSum (fun l => mul (B i l) (U l p)) k) (hBU i p)
      have hBUc : le (mul (mul (B i k) (U k p)) c) (X i s) :=
        le_trans (mul_mono_right hBUp) (hXc i)
      have hloop : le (mul (X i s) (mul (U s p) c)) (X i s) := by
        rw [← mul_assoc]
        exact le_trans (mul_mono_right (hXUe i s p)) (hXc i)
      have hsc_le : le (mul (mul (mul (B i k) (U k p)) c) sc) (X i s) :=
        star_ind_right' hBUc hloop
      have hstep : le (mul (mul (mul (mul (B i k) (U k p)) c) sc) (U s j)) (X i j) :=
        le_trans (mul_mono_right hsc_le) (hXUe i s j)
      simpa [mul_assoc] using hstep

/-- Helper: Product of two rank-1 corner bridges through `V` is a rank-1 single entry! -/
theorem corner_schur_product {n : Nat} (p q r s : Fin n) (wp wm : α) (V : Mat α n) :
    matMul (matMul (matSingle p q wp) V) (matSingle r s wm) =
      matSingle p s (mul (mul wp (V q r)) wm) := by
  funext i j
  rw [matMul_single_right, matMul_single_left]
  simp only [matSingle]
  by_cases hjs : j = s
  · subst hjs
    by_cases hip : i = p
    · subst hip; simp
    · simp [hip, zero_mul]
  · simp [hjs]

/-- Helper: sandwich product `A * (c · E_{p, q}) * B` is rank-1 `(A_{i,p} · c) · B_{q,j}`. -/
theorem matMul_single_mid {n : Nat} (A B : Mat α n) (p q : Fin n) (c : α) :
    matMul (matMul A (matSingle p q c)) B = fun i j => mul (mul (A i p) c) (B q j) := by
  funext i j
  change finSum n (fun k => mul (matMul A (matSingle p q c) i k) (B k j)) = _
  rw [finSum_single q]
  · rw [matMul_single_right]; simp
  · intro k hk; rw [matMul_single_right]; simp [hk, zero_mul]

/-- **Engine Theorem C1 (General Active Corner-Bridge 2×2 Renormalization):**
    For `M = [[A, wp·E_{p,q}], [wm·E_{r,s}, D]]` with `U = A*` and `V = D*`,
    let `c = wp · V_{q,r} · wm` and `S = smUpdate U p s c`.
    Then the exact Kleene star of `M` is computed in closed form with ZERO matrix inversion! -/
theorem cornerBridge_star {n : Nat} {A D U V : Mat α n}
    (hU : IsMatStar A U) (hV : IsMatStar D V)
    (p q r s : Fin n) (wp wm : α) :
    let c := mul (mul wp (V q r)) wm
    let S := smUpdate U p s c
    IsMatStar (blockMat A (matSingle p q wp) (matSingle r s wm) D)
      (blockMat S
                (fun i j => mul (mul (S i p) wp) (V q j))
                (fun i j => mul (mul (V i r) wm) (S s j))
                (fun i j => add (V i j) (mul (mul (mul (mul (V i r) wm) (S s p)) wp) (V q j)))) := by
  intro c S
  have hS : IsMatStar (matAdd A (matMul (matMul (matSingle p q wp) V) (matSingle r s wm))) S := by
    rw [corner_schur_product]
    exact rank1_sherman_morrison_star hU p s c
  have hMain := block_conway_schur_star hV hS
  have hTR : matMul (matMul S (matSingle p q wp)) V =
      fun i j => mul (mul (S i p) wp) (V q j) := matMul_single_mid S V p q wp
  have hBL : matMul (matMul V (matSingle r s wm)) S =
      fun i j => mul (mul (V i r) wm) (S s j) := matMul_single_mid V S r s wm
  have hBR : matAdd V (matMul (matMul (fun i j => mul (mul (V i r) wm) (S s j)) (matSingle p q wp)) V) =
      fun i j => add (V i j) (mul (mul (mul (mul (V i r) wm) (S s p)) wp) (V q j)) := by
    rw [matMul_single_mid]
    rfl
  rw [hTR, hBL] at hMain
  rwa [hBR] at hMain

/-- **Engine Theorem C2 (Exact Scalar Collapse Corollary):**
    When the two scalar bridge absorption conditions hold:
    - `wp · V_{q,r} · wm ≤ U_{p,s}` and `U_{s,p} · (wp · V_{q,r} · wm) ≤ 1`
    - `wm · U_{s,p} · wp ≤ V_{r,q}`
    then `S` collapses identically to `U` and the bottom-right block collapses to `V`! -/
theorem cornerBridge_collapse_star {n : Nat} {A D U V : Mat α n}
    (hU : IsMatStar A U) (hV : IsMatStar D V)
    (p q r s : Fin n) (wp wm : α)
    (hTopAbs : le (mul (mul wp (V q r)) wm) (U p s))
    (hLoop   : le (mul (U s p) (mul (mul wp (V q r)) wm)) one)
    (hBotAbs : le (mul (mul wm (U s p)) wp) (V r q)) :
    IsMatStar (blockMat A (matSingle p q wp) (matSingle r s wm) D)
      (blockMat U
                (fun i j => mul (mul (U i p) wp) (V q j))
                (fun i j => mul (mul (V i r) wm) (U s j))
                V) := by
  have hGen := cornerBridge_star hU hV p q r s wp wm
  let c := mul (mul wp (V q r)) wm
  have hstar1 : star (mul (U s p) c) = one := star_eq_one_of_le_one hLoop
  have hSeqU : smUpdate U p s c = U := by
    funext i j
    simp only [smUpdate, hstar1, mul_one]
    apply le_antisymm
    · apply add_le (le_refl _)
      have h1 : le (mul (mul (U i p) c) (U s j)) (mul (mul (U i p) (U p s)) (U s j)) :=
        mul_mono_right (mul_mono_left hTopAbs)
      have h2 : le (mul (U i p) (U p s)) (U i s) := hU.trans i p s
      exact le_trans h1 (le_trans (mul_mono_right h2) (hU.trans i s j))
    · exact le_add_left _ _
  have hBRV : (fun i j => add (V i j) (mul (mul (mul (mul (V i r) wm) (U s p)) wp) (V q j))) = V := by
    funext i j
    apply le_antisymm
    · apply add_le (le_refl _)
      have hrew : mul (mul (mul (mul (V i r) wm) (U s p)) wp) (V q j) =
                  mul (mul (V i r) (mul (mul wm (U s p)) wp)) (V q j) := by
        simp only [mul_assoc]
      rw [hrew]
      have h1 := mul_mono_right (c := V q j) (mul_mono_left (c := V i r) hBotAbs)
      exact le_trans h1 (le_trans (mul_mono_right (hV.trans i r q)) (hV.trans i q j))
    · exact le_add_left _ _
  dsimp only at hGen
  rw [hSeqU, hBRV] at hGen
  exact hGen

end MatrixAlgebra

theorem trop_le_fin_iff (a b : Nat) :
    KleeneSemiring.le (TropNat.fin a) (TropNat.fin b) ↔ b ≤ a := by
  change TropNat.minT (TropNat.fin a) (TropNat.fin b) = TropNat.fin b ↔ b ≤ a
  simp only [TropNat.minT, TropNat.fin.injEq, Nat.min_def]
  split <;> omega

theorem trop_le_one (a : TropNat) : KleeneSemiring.le a (KleeneSemiring.one : TropNat) := by
  cases a <;> simp [KleeneSemiring.le, KleeneSemiring.add, KleeneSemiring.one, TropNat.minT]

/-- **Sharpness Impossibility Lemma:** Naive `(Nat, max, ^^^)` does NOT form a semiring
    because bitwise XOR fails to distribute over `max` (hence Max-XOR optimization MUST
    lift to `XorSet` before projecting by `max`). -/
theorem naive_max_xor_not_distributive :
    ¬ (∀ a b c : Nat, a ^^^ (Nat.max b c) = Nat.max (a ^^^ b) (a ^^^ c)) := by
  intro h
  have h1 := h 1 0 1
  simp at h1

section BitDoublingTower

variable {α : Type u} [KleeneSemiring α]

open KleeneSemiring

/-- Base `1 × 1` Kleene star: `(0_{1×1})* = I_{1×1}`. -/
theorem matZero_one_star : IsMatStar (matZero 1 : Mat α 1) (matId 1) := by
  constructor
  · exact matLe_refl _
  · intro i j
    simp only [matMul, matZero]
    have h0 : (fun k : Fin 1 => mul (zero : α) (matId 1 k j)) = fun _ => zero := by
      funext k; exact zero_mul _
    rw [h0, finSum_zero]; exact zero_le _
  · intro i j
    simp only [matMul, matZero]
    have h0 : (fun k : Fin 1 => mul (matId 1 i k) (zero : α)) = fun _ => zero := by
      funext k; exact mul_zero _
    rw [h0, finSum_zero]; exact zero_le _
  · intro B X hBX _; rwa [matMul_id_left]
  · intro B X hBX _; rwa [matMul_id_right]

/-- **Reusable Inductive Lift Engine Theorem:**
    If the three scalar corner-bridge absorption inequalities hold for all `k`, then
    `spec.starCand k` is the EXACT `2^k × 2^k` Kleene star of `spec.mat k` for ALL `k ∈ ℕ`! -/
theorem BitDoublingCollapseSpec.sound (spec : BitDoublingCollapseSpec α)
    (hTop  : ∀ k, le (mul (mul (spec.wp k) (spec.starCand k (spec.q k) (spec.r k))) (spec.wm k))
                     (spec.starCand k (spec.p k) (spec.s k)))
    (hLoop : ∀ k, le (mul (spec.starCand k (spec.s k) (spec.p k))
                          (mul (mul (spec.wp k) (spec.starCand k (spec.q k) (spec.r k))) (spec.wm k)))
                     one)
    (hBot  : ∀ k, le (mul (mul (spec.wm k) (spec.starCand k (spec.s k) (spec.p k))) (spec.wp k))
                     (spec.starCand k (spec.r k) (spec.q k))) :
    ∀ k : Nat, IsMatStar (spec.mat k) (spec.starCand k)
  | 0 => matZero_one_star
  | k + 1 =>
    cornerBridge_collapse_star
      (spec.sound hTop hLoop hBot k)
      (spec.sound hTop hLoop hBot k)
      (spec.p k) (spec.q k) (spec.r k) (spec.s k) (spec.wp k) (spec.wm k)
      (hTop k) (hLoop k) (hBot k)

end BitDoublingTower

section CollapseSharpness

open KleeneSemiring

theorem sharpA_star : IsMatStar sharpA sharpU := by
  constructor
  · intro i j
    match i, j with
    | ⟨0, _⟩, ⟨0, _⟩ => rfl
    | ⟨0, _⟩, ⟨1, _⟩ => rfl
    | ⟨1, _⟩, ⟨0, _⟩ => rfl
    | ⟨1, _⟩, ⟨1, _⟩ => rfl
  · intro i j
    match i, j with
    | ⟨0, _⟩, ⟨0, _⟩ => rfl
    | ⟨0, _⟩, ⟨1, _⟩ => rfl
    | ⟨1, _⟩, ⟨0, _⟩ => rfl
    | ⟨1, _⟩, ⟨1, _⟩ => rfl
  · intro i j
    match i, j with
    | ⟨0, _⟩, ⟨0, _⟩ => rfl
    | ⟨0, _⟩, ⟨1, _⟩ => rfl
    | ⟨1, _⟩, ⟨0, _⟩ => rfl
    | ⟨1, _⟩, ⟨1, _⟩ => rfl
  · intro B X hBX hAX i j
    have hAstep : ∀ u v, le (mul (sharpA u v) (X v j)) (X u j) := fun u v =>
      le_trans (le_finSum (fun k => mul (sharpA u k) (X k j)) v) (hAX u j)
    match i with
    | ⟨0, _⟩ =>
      change le (add (add zero (mul (TropNat.fin 0) (B ⟨0, by omega⟩ j)))
                     (mul (TropNat.fin 10) (B ⟨1, by omega⟩ j))) (X ⟨0, by omega⟩ j)
      rw [zero_add]; change le (add (TropNat.addT (TropNat.fin 0) (B ⟨0, by omega⟩ j)) _) _
      rw [TropNat.zero_addT]
      apply add_le (hBX ⟨0, by omega⟩ j)
      exact le_trans (mul_mono_left (hBX ⟨1, by omega⟩ j)) (hAstep ⟨0, by omega⟩ ⟨1, by omega⟩)
    | ⟨1, _⟩ =>
      change le (add (add zero (mul (TropNat.fin 10) (B ⟨0, by omega⟩ j)))
                     (mul (TropNat.fin 0) (B ⟨1, by omega⟩ j))) (X ⟨1, by omega⟩ j)
      rw [zero_add]; change le (add _ (TropNat.addT (TropNat.fin 0) (B ⟨1, by omega⟩ j))) _
      rw [TropNat.zero_addT]
      apply add_le (le_trans (mul_mono_left (hBX ⟨0, by omega⟩ j)) (hAstep ⟨1, by omega⟩ ⟨0, by omega⟩))
                   (hBX ⟨1, by omega⟩ j)
  · intro B X hBX hXA i j
    have hXstep : ∀ u v, le (mul (X i u) (sharpA u v)) (X i v) := fun u v =>
      le_trans (le_finSum (fun k => mul (X i k) (sharpA k v)) u) (hXA i v)
    match j with
    | ⟨0, _⟩ =>
      change le (add (add zero (mul (B i ⟨0, by omega⟩) (TropNat.fin 0)))
                     (mul (B i ⟨1, by omega⟩) (TropNat.fin 10))) (X i ⟨0, by omega⟩)
      rw [zero_add]; change le (add (TropNat.addT (B i ⟨0, by omega⟩) (TropNat.fin 0)) _) _
      rw [TropNat.addT_zero]
      apply add_le (hBX i ⟨0, by omega⟩)
      exact le_trans (mul_mono_right (hBX i ⟨1, by omega⟩)) (hXstep ⟨1, by omega⟩ ⟨0, by omega⟩)
    | ⟨1, _⟩ =>
      change le (add (add zero (mul (B i ⟨0, by omega⟩) (TropNat.fin 10)))
                     (mul (B i ⟨1, by omega⟩) (TropNat.fin 0))) (X i ⟨1, by omega⟩)
      rw [zero_add]; change le (add _ (TropNat.addT (B i ⟨1, by omega⟩) (TropNat.fin 0))) _
      rw [TropNat.addT_zero]
      apply add_le (le_trans (mul_mono_right (hBX i ⟨0, by omega⟩)) (hXstep ⟨0, by omega⟩ ⟨1, by omega⟩))
                   (hBX i ⟨1, by omega⟩)

/-- **Sharpness Witness for Collapse vs Active Sherman-Morrison:**
    When the bridge shortcut `c = 1 + 0 + 1 = 2 < 10 = U_{0,1}` violates `hTopAbs`,
    naive collapse fails (`S_naive[0,1] = 10`, `¬ IsMatStar M S_naive`),
    while Engine Theorem C1 (`cornerBridge_star`) gives the EXACT Kleene star (`2`)! -/
theorem trop_collapse_hypothesis_sharp :
    let p : Fin 2 := ⟨0, by omega⟩
    let q : Fin 2 := ⟨0, by omega⟩
    let r : Fin 2 := ⟨0, by omega⟩
    let s : Fin 2 := ⟨1, by omega⟩
    let c := mul (mul (TropNat.fin 1) (sharpU q r)) (TropNat.fin 1)
    let M := blockMat sharpA (matSingle p q (TropNat.fin 1)) (matSingle r s (TropNat.fin 1)) sharpA
    let S_exact := blockMat
      (smUpdate sharpU p s c)
      (fun i j => mul (mul (smUpdate sharpU p s c i p) (TropNat.fin 1)) (sharpU q j))
      (fun i j => mul (mul (sharpU i r) (TropNat.fin 1)) (smUpdate sharpU p s c s j))
      (fun i j => add (sharpU i j) (mul (mul (mul (mul (sharpU i r) (TropNat.fin 1)) (smUpdate sharpU p s c s p)) (TropNat.fin 1)) (sharpU q j)))
    let S_naive := blockMat sharpU
      (fun i j => mul (mul (sharpU i p) (TropNat.fin 1)) (sharpU q j))
      (fun i j => mul (mul (sharpU i r) (TropNat.fin 1)) (sharpU s j))
      sharpU
    IsMatStar M S_exact ∧
    S_exact ⟨0, by omega⟩ ⟨1, by omega⟩ = TropNat.fin 2 ∧
    S_naive ⟨0, by omega⟩ ⟨1, by omega⟩ = TropNat.fin 10 ∧
    ¬ IsMatStar M S_naive := by
  intro p q r s c M S_exact S_naive
  have hEx : IsMatStar M S_exact := cornerBridge_star sharpA_star sharpA_star p q r s (TropNat.fin 1) (TropNat.fin 1)
  have hValEx : S_exact ⟨0, by omega⟩ ⟨1, by omega⟩ = TropNat.fin 2 := rfl
  have hValNa : S_naive ⟨0, by omega⟩ ⟨1, by omega⟩ = TropNat.fin 10 := rfl
  refine ⟨hEx, hValEx, hValNa, ?_⟩
  intro hNa
  have heq := hEx.unique hNa
  have h01 := congrFun (congrFun heq ⟨0, by omega⟩) ⟨1, by omega⟩
  rw [hValEx, hValNa] at h01
  cases h01

end CollapseSharpness

theorem popcount_zero : popcount 0 = 0 := by unfold popcount; rfl

theorem popcount_eq (n : Nat) : popcount n = n % 2 + popcount (n / 2) := by
  cases n with
  | zero => rw [popcount_zero]
  | succ m => conv => lhs; unfold popcount

theorem popcount_one : popcount 1 = 1 := by
  rw [popcount_eq]; simp [popcount_zero]

theorem popcount_add_pow2 {k x : Nat} (hx : x < 2 ^ k) :
    popcount (2 ^ k + x) = 1 + popcount x := by
  induction k generalizing x with
  | zero =>
    have hx0 : x = 0 := by omega
    subst hx0; simp [popcount_zero, popcount_one]
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
    have hx2 : x / 2 < 2 ^ k := by omega
    rw [popcount_eq (2 ^ (k + 1) + x), popcount_eq x]
    have hm : (2 ^ (k + 1) + x) % 2 = x % 2 := by omega
    have hd : (2 ^ (k + 1) + x) / 2 = 2 ^ k + x / 2 := by omega
    rw [hm, hd, ih hx2]
    omega

theorem popcount_pow2_sub_one (k : Nat) : popcount (2 ^ k - 1) = k := by
  induction k with
  | zero => simp [popcount_zero]
  | succ k ih =>
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    have heq : 2 ^ (k + 1) - 1 = 2 ^ k + (2 ^ k - 1) := by rw [Nat.pow_succ]; omega
    rw [heq, popcount_add_pow2 (by omega), ih]
    omega

theorem popcount_compl {k x : Nat} (hx : x < 2 ^ k) :
    popcount (2 ^ k - 1 - x) + popcount x = k := by
  induction k generalizing x with
  | zero =>
    have hx0 : x = 0 := by omega
    subst hx0; simp [popcount_zero]
  | succ k ih =>
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    by_cases h : x < 2 ^ k
    · have h1 : 2 ^ (k + 1) - 1 - x = 2 ^ k + (2 ^ k - 1 - x) := by omega
      rw [h1, popcount_add_pow2 (by omega)]
      have := ih h; omega
    · let x' := x - 2 ^ k
      have hx' : x' < 2 ^ k := by omega
      have h2 : x = 2 ^ k + x' := by omega
      have h3 : 2 ^ (k + 1) - 1 - x = 2 ^ k - 1 - x' := by omega
      rw [h3, h2, popcount_add_pow2 hx']
      have := ih hx'; omega

theorem ctzNat_one : ctzNat 1 = 0 := by unfold ctzNat; simp

theorem ctzNat_pow2 (k : Nat) : ctzNat (2 ^ k) = k := by
  induction k with
  | zero => exact ctzNat_one
  | succ k ih =>
    have hpos : 0 < 2 ^ (k + 1) := Nat.two_pow_pos (k + 1)
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
    conv => lhs; unfold ctzNat
    cases h : 2 ^ (k + 1) with
    | zero => omega
    | succ m =>
      have hm1 : (m + 1) % 2 = 0 := by omega
      have hm2 : (m + 1) / 2 = 2 ^ k := by omega
      simp [hm1, hm2, ih]; omega

theorem ctzNat_add_pow2 {k x : Nat} (hx0 : 0 < x) (hx : x < 2 ^ k) :
    ctzNat (2 ^ k + x) = ctzNat x := by
  induction k generalizing x with
  | zero => omega
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
    cases hx_eq : x with
    | zero => omega
    | succ x' =>
      conv => lhs; unfold ctzNat
      conv => rhs; unfold ctzNat
      cases hL : 2 ^ (k + 1) + (x' + 1) with
      | zero => omega
      | succ m =>
        have hmod : (m + 1) % 2 = (x' + 1) % 2 := by omega
        have hdiv : (m + 1) / 2 = 2 ^ k + (x' + 1) / 2 := by omega
        rw [hmod]
        split
        · rfl
        · rw [hdiv]
          have hxdiv_pos : 0 < (x' + 1) / 2 := by omega
          have hxdiv_lt : (x' + 1) / 2 < 2 ^ k := by omega
          rw [ih hxdiv_pos hxdiv_lt]

theorem ctzZeroNat_pow2_sub_one (k : Nat) : ctzZeroNat (2 ^ k - 1) = k := by
  unfold ctzZeroNat
  have h : 2 ^ k - 1 + 1 = 2 ^ k := by have := Nat.two_pow_pos k; omega
  rw [h, ctzNat_pow2]

theorem ctzZeroNat_add_pow2 {k x : Nat} (hx : x + 1 < 2 ^ k) :
    ctzZeroNat (2 ^ k + x) = ctzZeroNat x := by
  unfold ctzZeroNat
  have h : 2 ^ k + x + 1 = 2 ^ k + (x + 1) := by omega
  rw [h]
  exact ctzNat_add_pow2 (by omega) hx

/-- Exact testBit of `2^k + x` when `x < 2^k`. -/
theorem testBit_add_pow2 {k x : Nat} (hx : x < 2 ^ k) (j : Nat) :
    (2 ^ k + x).testBit j = (decide (k = j) || x.testBit j) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  by_cases hj : j < k
  · have hkj : decide (k = j) = false := by simp; omega
    rw [hkj, Bool.false_or]
    have hdvd : 2 ^ k = 2 ^ (k - j) * 2 ^ j := by
      rw [← Nat.pow_add]; congr 1; omega
    have heven : 2 ∣ 2 ^ (k - j) := by
      have : k - j = (k - j - 1) + 1 := by omega
      rw [this, Nat.pow_succ]; exact Nat.dvd_mul_left 2 _
    rcases heven with ⟨q, hq⟩
    have hdiv : (2 ^ k + x) / 2 ^ j = 2 * q + x / 2 ^ j := by
      have h1 : 2 ^ k + x = x + (2 * q) * 2 ^ j := by rw [hdvd, hq]; omega
      rw [h1, Nat.add_mul_div_right _ _ (Nat.two_pow_pos j)]; omega
    rw [hdiv]
    have hmod : (2 * q + x / 2 ^ j) % 2 = (x / 2 ^ j) % 2 := by omega
    rw [hmod]
  · by_cases hjk : k = j
    · subst hjk
      have hxdiv : x / 2 ^ k = 0 := Nat.div_eq_of_lt hx
      have hdiv : (2 ^ k + x) / 2 ^ k = 1 := by
        have h1 : 2 ^ k + x = x + 1 * 2 ^ k := by omega
        rw [h1, Nat.add_mul_div_right _ _ (Nat.two_pow_pos k), hxdiv]
      simp [hdiv]
    · have hlt : k < j := by omega
      have hkj : decide (k = j) = false := by simp; omega
      have h2le : 2 ^ (k + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
      have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
      have h1 : (2 ^ k + x) / 2 ^ j = 0 := Nat.div_eq_of_lt (by omega)
      have h2 : x / 2 ^ j = 0 := Nat.div_eq_of_lt (by omega)
      simp [hkj, h1, h2]

/-- Exact testBit of complement `(2^k - 1 - x)` for `x < 2^k` and `j < k`. -/
theorem testBit_compl {k x : Nat} (hx : x < 2 ^ k) {j : Nat} (hj : j < k) :
    (2 ^ k - 1 - x).testBit j = !(x.testBit j) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  have hpj : 0 < 2 ^ j := Nat.two_pow_pos j
  have hdvd : 2 ^ k = 2 ^ (k - j) * 2 ^ j := by
    rw [← Nat.pow_add]; congr 1; omega
  have hpos_kj : 0 < 2 ^ (k - j) := Nat.two_pow_pos (k - j)
  have hdiv_x_lt : x / 2 ^ j < 2 ^ (k - j) := by
    rw [Nat.div_lt_iff_lt_mul hpj]; rw [← hdvd]; exact hx
  have hrem_lt : x % 2 ^ j < 2 ^ j := Nat.mod_lt x hpj
  have hdecomp : x = (x / 2 ^ j) * 2 ^ j + x % 2 ^ j := by
    rw [Nat.mul_comm]; exact (Nat.div_add_mod x (2 ^ j)).symm
  have hsub : 2 ^ k - 1 - x =
      (2 ^ j - 1 - x % 2 ^ j) + (2 ^ (k - j) - 1 - x / 2 ^ j) * 2 ^ j := by
    have h1 : 2 ^ k = 2 ^ j + (2 ^ (k - j) - 1) * 2 ^ j := by
      rw [hdvd]; cases h : 2 ^ (k - j) with
      | zero => omega
      | succ m => simp [Nat.succ_mul]; omega
    have h2 : (2 ^ (k - j) - 1 - x / 2 ^ j) * 2 ^ j + (x / 2 ^ j) * 2 ^ j =
              (2 ^ (k - j) - 1) * 2 ^ j := by
      rw [← Nat.add_mul]; congr 1; omega
    omega
  have hdiv_compl : (2 ^ k - 1 - x) / 2 ^ j = 2 ^ (k - j) - 1 - x / 2 ^ j := by
    rw [hsub, Nat.add_mul_div_right _ _ hpj, Nat.div_eq_of_lt (by omega)]; omega
  rw [hdiv_compl]
  have heven : 2 ∣ 2 ^ (k - j) := by
    have : k - j = (k - j - 1) + 1 := by omega
    rw [this, Nat.pow_succ]; exact Nat.dvd_mul_left 2 _
  rcases heven with ⟨q, hq⟩
  have hmod_flip : (2 ^ (k - j) - 1 - x / 2 ^ j) % 2 = 1 - (x / 2 ^ j) % 2 := by omega
  rw [hmod_flip]
  cases h : (x / 2 ^ j) % 2 with
  | zero => decide
  | succ m =>
    have hm : m = 0 := by omega
    subst hm; decide

/-- Adding `2^k` commutes with `x ||| (x + 1)` when `x + 1 < 2^k`. -/
theorem bor_inc_add_pow2 {k x : Nat} (hx : x + 1 < 2 ^ k) :
    (2 ^ k + x) ||| (2 ^ k + x + 1) = 2 ^ k + (x ||| (x + 1)) := by
  have h3 : x ||| (x + 1) < 2 ^ k := Nat.or_lt_two_pow (by omega) hx
  have h2eq : 2 ^ k + x + 1 = 2 ^ k + (x + 1) := by omega
  rw [h2eq]
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_or, testBit_add_pow2 (by omega : x < 2 ^ k),
             testBit_add_pow2 hx, testBit_add_pow2 h3]
  cases decide (k = j) <;> cases x.testBit j <;> cases (x + 1).testBit j <;> rfl

/-- Corner carry-OR identity: `(2^k - 1) ||| 2^k = 2^k + (2^k - 1)`. -/
theorem bor_inc_corner (k : Nat) : (2 ^ k - 1) ||| (2 ^ k - 1 + 1) = 2 ^ k + (2 ^ k - 1) := by
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have h1 : 2 ^ k - 1 + 1 = 2 ^ k := by omega
  rw [h1]
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_or, Nat.testBit_two_pow, testBit_add_pow2 (by omega : 2 ^ k - 1 < 2 ^ k)]
  cases decide (k = j) <;> cases (2 ^ k - 1).testBit j <;> rfl

/-- Adding `2^k` commutes with `x &&& (x - 1)` when `0 < x < 2^k`. -/
theorem band_dec_add_pow2 {k x : Nat} (hx0 : 0 < x) (hx : x < 2 ^ k) :
    (2 ^ k + x) &&& (2 ^ k + x - 1) = 2 ^ k + (x &&& (x - 1)) := by
  have h3 : x &&& (x - 1) < 2 ^ k := Nat.lt_of_le_of_lt Nat.and_le_left hx
  have h2eq : 2 ^ k + x - 1 = 2 ^ k + (x - 1) := by omega
  rw [h2eq]
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_and, testBit_add_pow2 hx,
             testBit_add_pow2 (by omega : x - 1 < 2 ^ k), testBit_add_pow2 h3]
  cases decide (k = j) <;> cases x.testBit j <;> cases (x - 1).testBit j <;> rfl

/-- Corner borrow-AND identity: `2^k &&& (2^k - 1) = 0`. -/
theorem band_dec_corner (k : Nat) : (2 ^ k) &&& (2 ^ k - 1) = 0 := by
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
  by_cases hj : k = j
  · subst hj; simp [Nat.testBit_lt_two_pow (by have := Nat.two_pow_pos k; omega : 2 ^ k - 1 < 2 ^ k)]
  · simp [hj]

/-! ============================================================================
    SECTION 7: THEOREM 1 — BMI1 BIT-TWIDDLE GRAPH TROPICAL KLEENE STAR,
               BINARY GRAY-CODE CLOSED FORM, AND GENERALIZED DIAMETER
    ============================================================================ -/

/-- **Bitwise Faithfulness Theorem:**
    For ALL `k : Nat` and ALL bit-cost schedules `c`, the recursive block-matrix
    `bmiTropMat k c` equals the hardware BMI1 instruction matrix `bmiBitwiseMat k c`! -/
theorem bmiTropMat_eq_bitwise (k : Nat) (c : Nat → Nat) :
    bmiTropMat k c = bmiBitwiseMat k c := by
  induction k with
  | zero =>
    funext x y
    simp [bmiTropMat, BitDoublingCollapseSpec.mat, matZero, bmiBitwiseMat, KleeneSemiring.zero]
  | succ k ih =>
    funext x y
    change blockMat (bmiTropMat k c)
                    (matSingle (finMax k) (finMax k) (TropNat.fin (c k)))
                    (matSingle (finZero k) (finZero k) (TropNat.fin (c k)))
                    (bmiTropMat k c) x y = bmiBitwiseMat (k + 1) c x y
    rw [ih]
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    simp only [blockMat, matSingle, finMax, finZero, bmiBitwiseMat, KleeneSemiring.zero]
    by_cases hx : x.val < 2 ^ k <;> by_cases hy : y.val < 2 ^ k
    · -- Quadrant (0, 0)
      simp only [hx, hy, ↓reduceDIte]
      by_cases hx1 : x.val + 1 < 2 ^ k
      · have hx1' : x.val + 1 < 2 ^ (k + 1) := by omega
        simp only [hx1, hx1', true_and]
      · have hxeq : x.val = 2 ^ k - 1 := by omega
        have hbor : x.val ||| (x.val + 1) = 2 ^ k + (2 ^ k - 1) := by rw [hxeq]; exact bor_inc_corner k
        have hne : y.val ≠ x.val ||| (x.val + 1) := by omega
        simp only [hx1, ↓reduceIte, hne, and_false]
    · -- Quadrant (0, 1)
      simp only [hx, hy, ↓reduceDIte]
      have hband_lt : x.val &&& (x.val - 1) < 2 ^ k := Nat.lt_of_le_of_lt Nat.and_le_left hx
      have hband_ne : y.val ≠ x.val &&& (x.val - 1) := by omega
      by_cases hxeq : x.val = 2 ^ k - 1
      · have hbor : x.val ||| (x.val + 1) = 2 ^ k + (2 ^ k - 1) := by rw [hxeq]; exact bor_inc_corner k
        have hctz : ctzZeroNat x.val = k := by rw [hxeq]; exact ctzZeroNat_pow2_sub_one k
        have hx1 : x.val + 1 < 2 ^ (k + 1) := by omega
        by_cases hyeq : y.val = 2 ^ k + (2 ^ k - 1)
        · have hL1 : (⟨x.val, hx⟩ : Fin (2 ^ k)) = ⟨2 ^ k - 1, by omega⟩ := Fin.ext hxeq
          have hL2 : (⟨y.val - 2 ^ k, by omega⟩ : Fin (2 ^ k)) = ⟨2 ^ k - 1, by omega⟩ := Fin.ext (by dsimp; omega)
          simp [hL1, hx1, hbor, hyeq, hctz]
        · have hne2 : y.val - 2 ^ k ≠ 2 ^ k - 1 := by omega
          have hL2 : ¬ ((⟨y.val - 2 ^ k, by omega⟩ : Fin (2 ^ k)) = ⟨2 ^ k - 1, by omega⟩) := by
            intro h; exact hne2 (congrArg Fin.val h)
          simp [hL2, hbor, hyeq, hband_ne]
      · have hL1 : ¬ ((⟨x.val, hx⟩ : Fin (2 ^ k)) = ⟨2 ^ k - 1, by omega⟩) := by
          intro h; exact hxeq (congrArg Fin.val h)
        have hbor_lt : x.val ||| (x.val + 1) < 2 ^ k := Nat.or_lt_two_pow hx (by omega)
        have hbor_ne : y.val ≠ x.val ||| (x.val + 1) := by omega
        simp [hL1, hbor_ne, hband_ne]
    · -- Quadrant (1, 0)
      simp only [hx, hy, ↓reduceDIte]
      have hbor_ge : 2 ^ k ≤ x.val ||| (x.val + 1) := Nat.le_trans (by omega) Nat.left_le_or
      have hbor_ne : y.val ≠ x.val ||| (x.val + 1) := by omega
      by_cases hxeq : x.val = 2 ^ k
      · have hband : x.val &&& (x.val - 1) = 0 := by rw [hxeq]; exact band_dec_corner k
        have hctz : ctzNat x.val = k := by rw [hxeq]; exact ctzNat_pow2 k
        have hxpos : 0 < x.val := by omega
        by_cases hyeq : y.val = 0
        · have hL1 : (⟨x.val - 2 ^ k, by omega⟩ : Fin (2 ^ k)) = ⟨0, hpos⟩ := Fin.ext (by dsimp; omega)
          have hne0 : 0 ≠ x.val ||| (x.val + 1) := by omega
          simp [hL1, hyeq, hne0, hxpos, hband, hctz]
        · have hL2 : ¬ ((⟨y.val, hy⟩ : Fin (2 ^ k)) = ⟨0, hpos⟩) := by
            intro h; exact hyeq (congrArg Fin.val h)
          simp [hL2, hbor_ne, hband, hyeq]
      · have hne1 : x.val - 2 ^ k ≠ 0 := by omega
        have hL1 : ¬ ((⟨x.val - 2 ^ k, by omega⟩ : Fin (2 ^ k)) = ⟨0, hpos⟩) := by
          intro h; exact hne1 (congrArg Fin.val h)
        let x' := x.val - 2 ^ k
        have hx' : 0 < x' := by omega
        have hxlt : x' < 2 ^ k := by have := x.isLt; omega
        have hxeq2 : x.val = 2 ^ k + x' := by omega
        have hband : x.val &&& (x.val - 1) = 2 ^ k + (x' &&& (x' - 1)) := by
          rw [hxeq2]; exact band_dec_add_pow2 hx' hxlt
        have hband_ne : y.val ≠ x.val &&& (x.val - 1) := by omega
        simp [hL1, hbor_ne, hband_ne]
    · -- Quadrant (1, 1)
      simp only [hx, hy, ↓reduceDIte]
      let x' := x.val - 2 ^ k
      let y' := y.val - 2 ^ k
      have hxlt : x' < 2 ^ k := by have := x.isLt; omega
      have hylt : y' < 2 ^ k := by have := y.isLt; omega
      have hxeq : x.val = 2 ^ k + x' := by omega
      have hyeq : y.val = 2 ^ k + y' := by omega
      have hiff1 : (x' + 1 < 2 ^ k ∧ y' = x' ||| (x' + 1)) ↔
                   (x.val + 1 < 2 ^ (k + 1) ∧ y.val = x.val ||| (x.val + 1)) := by
        constructor
        · rintro ⟨ha, hb⟩
          refine ⟨by omega, ?_⟩
          rw [hyeq, hxeq, bor_inc_add_pow2 ha, hb]
        · rintro ⟨ha, hb⟩
          have ha' : x' + 1 < 2 ^ k := by omega
          refine ⟨ha', ?_⟩
          rw [hyeq, hxeq, bor_inc_add_pow2 ha'] at hb
          omega
      have hiff2 : (0 < x' ∧ y' = x' &&& (x' - 1)) ↔
                   (0 < x.val ∧ y.val = x.val &&& (x.val - 1)) := by
        constructor
        · rintro ⟨ha, hb⟩
          refine ⟨by omega, ?_⟩
          rw [hyeq, hxeq, band_dec_add_pow2 ha hxlt, hb]
        · rintro ⟨ha, hb⟩
          by_cases hz : x' = 0
          · have hxk : x.val = 2 ^ k := by omega
            have h0 : x.val &&& (x.val - 1) = 0 := by rw [hxk]; exact band_dec_corner k
            omega
          · have ha' : 0 < x' := by omega
            refine ⟨ha', ?_⟩
            rw [hyeq, hxeq, band_dec_add_pow2 ha' hxlt] at hb
            omega
      by_cases h1 : x' + 1 < 2 ^ k ∧ y' = x' ||| (x' + 1)
      · have h1' := hiff1.mp h1
        have hctz := ctzZeroNat_add_pow2 h1.1
        rw [← hxeq] at hctz
        have hL : (if x.val - 2 ^ k + 1 < 2 ^ k ∧ y.val - 2 ^ k = (x.val - 2 ^ k) ||| (x.val - 2 ^ k + 1) then
                     TropNat.fin (c (ctzZeroNat (x.val - 2 ^ k)))
                   else if 0 < x.val - 2 ^ k ∧ y.val - 2 ^ k = (x.val - 2 ^ k) &&& (x.val - 2 ^ k - 1) then
                     TropNat.fin (c (ctzNat (x.val - 2 ^ k))) else TropNat.inf) =
                  TropNat.fin (c (ctzZeroNat (x.val - 2 ^ k))) := by split; rfl; exact absurd h1 ‹_›
        have hR : (if x.val + 1 < 2 ^ (k + 1) ∧ y.val = x.val ||| (x.val + 1) then
                     TropNat.fin (c (ctzZeroNat x.val))
                   else if 0 < x.val ∧ y.val = x.val &&& (x.val - 1) then
                     TropNat.fin (c (ctzNat x.val)) else TropNat.inf) =
                  TropNat.fin (c (ctzZeroNat x.val)) := by split; rfl; exact absurd h1' ‹_›
        rw [hL, hR, hctz]
      · have h1' : ¬ (x.val + 1 < 2 ^ (k + 1) ∧ y.val = x.val ||| (x.val + 1)) := mt hiff1.mpr h1
        have hL1 : (if x.val - 2 ^ k + 1 < 2 ^ k ∧ y.val - 2 ^ k = (x.val - 2 ^ k) ||| (x.val - 2 ^ k + 1) then
                      TropNat.fin (c (ctzZeroNat (x.val - 2 ^ k)))
                    else if 0 < x.val - 2 ^ k ∧ y.val - 2 ^ k = (x.val - 2 ^ k) &&& (x.val - 2 ^ k - 1) then
                      TropNat.fin (c (ctzNat (x.val - 2 ^ k))) else TropNat.inf) =
                   (if 0 < x.val - 2 ^ k ∧ y.val - 2 ^ k = (x.val - 2 ^ k) &&& (x.val - 2 ^ k - 1) then
                      TropNat.fin (c (ctzNat (x.val - 2 ^ k))) else TropNat.inf) := by split; exact absurd ‹_› h1; rfl
        have hR1 : (if x.val + 1 < 2 ^ (k + 1) ∧ y.val = x.val ||| (x.val + 1) then
                      TropNat.fin (c (ctzZeroNat x.val))
                    else if 0 < x.val ∧ y.val = x.val &&& (x.val - 1) then
                      TropNat.fin (c (ctzNat x.val)) else TropNat.inf) =
                   (if 0 < x.val ∧ y.val = x.val &&& (x.val - 1) then
                      TropNat.fin (c (ctzNat x.val)) else TropNat.inf) := by split; exact absurd ‹_› h1'; rfl
        rw [hL1, hR1]
        by_cases h2 : 0 < x' ∧ y' = x' &&& (x' - 1)
        · have h2' := hiff2.mp h2
          have hctz := ctzNat_add_pow2 h2.1 hxlt
          rw [← hxeq] at hctz
          have hL2 : (if 0 < x.val - 2 ^ k ∧ y.val - 2 ^ k = (x.val - 2 ^ k) &&& (x.val - 2 ^ k - 1) then
                        TropNat.fin (c (ctzNat (x.val - 2 ^ k))) else TropNat.inf) =
                     TropNat.fin (c (ctzNat (x.val - 2 ^ k))) := by split; rfl; exact absurd h2 ‹_›
          have hR2 : (if 0 < x.val ∧ y.val = x.val &&& (x.val - 1) then
                        TropNat.fin (c (ctzNat x.val)) else TropNat.inf) =
                     TropNat.fin (c (ctzNat x.val)) := by split; rfl; exact absurd h2' ‹_›
          rw [hL2, hR2, hctz]
        · have h2' : ¬ (0 < x.val ∧ y.val = x.val &&& (x.val - 1)) := mt hiff2.mpr h2
          have hL2 : (if 0 < x.val - 2 ^ k ∧ y.val - 2 ^ k = (x.val - 2 ^ k) &&& (x.val - 2 ^ k - 1) then
                        TropNat.fin (c (ctzNat (x.val - 2 ^ k))) else TropNat.inf) = TropNat.inf := by
            split; exact absurd ‹_› h2; rfl
          have hR2 : (if 0 < x.val ∧ y.val = x.val &&& (x.val - 1) then
                        TropNat.fin (c (ctzNat x.val)) else TropNat.inf) = TropNat.inf := by
            split; exact absurd ‹_› h2'; rfl
          rw [hL2, hR2]

theorem bmiStarCand_eq_fin (k : Nat) (c : Nat → Nat) :
    (bmiTropSpec c).starCand k = fun i j => TropNat.fin (bmiDist k c i j) := by
  induction k with
  | zero =>
    funext i j
    have hi : i = j := Fin.ext (by have := i.isLt; have := j.isLt; omega)
    subst hi
    simp [BitDoublingCollapseSpec.starCand, matId, bmiDist, KleeneSemiring.one]
  | succ k ih =>
    funext i j
    unfold BitDoublingCollapseSpec.starCand
    dsimp only
    rw [ih]
    simp only [blockMat, bmiDist, bmiTropSpec, KleeneSemiring.mul, TropNat.addT]
    by_cases hi : i.val < 2 ^ k <;> by_cases hj : j.val < 2 ^ k <;> simp [hi, hj]

/-- **THEOREM 1A (Exact Infinite-Width Tropical Kleene Star of `B_k^(c)`):**
    For EVERY bit-width `k : Nat` and EVERY arbitrary bit-cost schedule `c : Nat → Nat`,
    `TropNat.fin (bmiDist k c i j)` is the EXACT `2^k × 2^k` Kleene star of `bmiBitwiseMat k c`! -/
theorem bmi_trop_star_exact (k : Nat) (c : Nat → Nat) :
    IsMatStar (bmiBitwiseMat k c) (fun i j => TropNat.fin (bmiDist k c i j)) := by
  rw [← bmiTropMat_eq_bitwise, ← bmiStarCand_eq_fin]
  apply (bmiTropSpec c).sound
  · intro m
    rw [bmiStarCand_eq_fin]
    change KleeneSemiring.le (TropNat.fin (c m + bmiDist m c (finMax m) (finZero m) + c m))
                             (TropNat.fin (bmiDist m c (finMax m) (finZero m)))
    rw [trop_le_fin_iff]; omega
  · intro m; exact trop_le_one _
  · intro m
    rw [bmiStarCand_eq_fin]
    change KleeneSemiring.le (TropNat.fin (c m + bmiDist m c (finZero m) (finMax m) + c m))
                             (TropNat.fin (bmiDist m c (finZero m) (finMax m)))
    rw [trop_le_fin_iff]; omega

/-! ### Exact Closed-Form Bitwise Evaluation: Binary Gray-Code Suffix-Popcount Law! -/

theorem altWord_lt (k : Nat) : altWord k < 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    simp only [altWord]
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    omega

theorem bmiDist_compl (k : Nat) (c : Nat → Nat) (x y : Fin (2 ^ k)) :
    bmiDist k c (finCompl x) (finCompl y) = bmiDist k c x y := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    have hxlt := x.isLt
    have hylt := y.isLt
    simp only [bmiDist, finCompl]
    by_cases hx : x.val < 2 ^ k <;> by_cases hy : y.val < 2 ^ k
    · have hcx : ¬ (2 ^ (k + 1) - 1 - x.val < 2 ^ k) := by omega
      have hcy : ¬ (2 ^ (k + 1) - 1 - y.val < 2 ^ k) := by omega
      simp only [hx, hy, hcx, hcy, ↓reduceDIte]
      have eqx : (⟨2 ^ (k + 1) - 1 - x.val - 2 ^ k, by omega⟩ : Fin (2 ^ k)) = finCompl ⟨x.val, hx⟩ :=
        Fin.ext (by dsimp [finCompl]; omega)
      have eqy : (⟨2 ^ (k + 1) - 1 - y.val - 2 ^ k, by omega⟩ : Fin (2 ^ k)) = finCompl ⟨y.val, hy⟩ :=
        Fin.ext (by dsimp [finCompl]; omega)
      rw [eqx, eqy]; exact ih _ _
    · have hcx : ¬ (2 ^ (k + 1) - 1 - x.val < 2 ^ k) := by omega
      have hcy : 2 ^ (k + 1) - 1 - y.val < 2 ^ k := by omega
      simp only [hx, hy, hcx, hcy, ↓reduceDIte]
      have eqx : (⟨2 ^ (k + 1) - 1 - x.val - 2 ^ k, by omega⟩ : Fin (2 ^ k)) = finCompl ⟨x.val, hx⟩ :=
        Fin.ext (by dsimp [finCompl]; omega)
      have eqy : (⟨2 ^ (k + 1) - 1 - y.val, hcy⟩ : Fin (2 ^ k)) = finCompl ⟨y.val - 2 ^ k, by omega⟩ :=
        Fin.ext (by dsimp [finCompl]; omega)
      have eqz : finZero k = finCompl (finMax k) := Fin.ext (by dsimp [finZero, finMax, finCompl]; omega)
      rw [eqx, eqy, eqz, ih, ih]
    · have hcx : 2 ^ (k + 1) - 1 - x.val < 2 ^ k := by omega
      have hcy : ¬ (2 ^ (k + 1) - 1 - y.val < 2 ^ k) := by omega
      simp only [hx, hy, hcx, hcy, ↓reduceDIte]
      have eqx : (⟨2 ^ (k + 1) - 1 - x.val, hcx⟩ : Fin (2 ^ k)) = finCompl ⟨x.val - 2 ^ k, by omega⟩ :=
        Fin.ext (by dsimp [finCompl]; omega)
      have eqy : (⟨2 ^ (k + 1) - 1 - y.val - 2 ^ k, by omega⟩ : Fin (2 ^ k)) = finCompl ⟨y.val, hy⟩ :=
        Fin.ext (by dsimp [finCompl]; omega)
      have eqm : finMax k = finCompl (finZero k) := Fin.ext (by dsimp [finZero, finMax, finCompl])
      rw [eqx, eqy, eqm, ih, ih]
    · have hcx : 2 ^ (k + 1) - 1 - x.val < 2 ^ k := by omega
      have hcy : 2 ^ (k + 1) - 1 - y.val < 2 ^ k := by omega
      simp only [hx, hy, hcx, hcy, ↓reduceDIte]
      have eqx : (⟨2 ^ (k + 1) - 1 - x.val, hcx⟩ : Fin (2 ^ k)) = finCompl ⟨x.val - 2 ^ k, by omega⟩ :=
        Fin.ext (by dsimp [finCompl]; omega)
      have eqy : (⟨2 ^ (k + 1) - 1 - y.val, hcy⟩ : Fin (2 ^ k)) = finCompl ⟨y.val - 2 ^ k, by omega⟩ :=
        Fin.ext (by dsimp [finCompl]; omega)
      rw [eqx, eqy]; exact ih _ _

theorem oneBitCost_zero (c : Nat → Nat) (k : Nat) : oneBitCost c k 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [oneBitCost, ih]

theorem oneBitCost_le_sumCost (c : Nat → Nat) (k x : Nat) :
    oneBitCost c k x ≤ sumCost c k := by
  induction k with
  | zero => exact Nat.le_refl 0
  | succ k ih =>
    simp only [oneBitCost, sumCost]
    split <;> omega

theorem oneBitCost_mod_le (c : Nat → Nat) (m k x : Nat) (hmk : m ≤ k) :
    oneBitCost c m (x % 2 ^ k) = oneBitCost c m x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [oneBitCost, Nat.testBit_mod_two_pow]
    have hlt : m < k := by omega
    simp [hlt, ih (by omega)]

theorem bmiDist_to_zero (k : Nat) (c : Nat → Nat) (x : Fin (2 ^ k)) :
    bmiDist k c x (finZero k) = oneBitCost c k x.val := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    have hzero_lt : (finZero (k + 1)).val < 2 ^ k := hpos
    simp only [bmiDist, hzero_lt, ↓reduceDIte]
    by_cases hx : x.val < 2 ^ k
    · simp only [hx, ↓reduceDIte]
      have htb : x.val.testBit k = false := Nat.testBit_lt_two_pow hx
      simp only [oneBitCost, htb, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      exact ih ⟨x.val, hx⟩
    · simp only [hx, ↓reduceDIte]
      have hxlt : x.val - 2 ^ k < 2 ^ k := by have := x.isLt; omega
      have htb : x.val.testBit k = true := by
        rw [Nat.testBit_eq_decide_div_mod_eq]
        have hd : x.val / 2 ^ k = 1 := Nat.div_eq_of_lt_le (by omega) (by have := x.isLt; omega)
        rw [hd]; decide
      have hmod : x.val - 2 ^ k = x.val % 2 ^ k := by
        have h1 : x.val = (x.val - 2 ^ k) + 1 * 2 ^ k := by omega
        conv => rhs; rw [h1]
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hxlt]
      have hdiag : bmiDist k c (finZero k) (finZero k) = 0 := by
        rw [ih (finZero k)]; exact oneBitCost_zero c k
      have hfz : (⟨(finZero (k + 1)).val, hzero_lt⟩ : Fin (2 ^ k)) = finZero k := rfl
      rw [hfz, hdiag, Nat.add_zero, ih ⟨x.val - 2 ^ k, hxlt⟩]
      dsimp only
      rw [hmod, oneBitCost_mod_le c k k x.val (Nat.le_refl k)]
      simp [oneBitCost, htb]

theorem bmiDist_to_zero_le_sumCost (k : Nat) (c : Nat → Nat) (x : Fin (2 ^ k)) :
    bmiDist k c x (finZero k) ≤ sumCost c k := by
  rw [bmiDist_to_zero]; exact oneBitCost_le_sumCost c k x.val

theorem bmiDist_to_max_le_sumCost (k : Nat) (c : Nat → Nat) (x : Fin (2 ^ k)) :
    bmiDist k c x (finMax k) ≤ sumCost c k := by
  have h := bmiDist_compl k c x (finMax k)
  have hm : finCompl (finMax k) = finZero k := Fin.ext (by dsimp [finCompl, finMax, finZero]; omega)
  rw [hm] at h
  rw [← h]
  exact bmiDist_to_zero_le_sumCost k c (finCompl x)

theorem oneBitCost_pow2_sub_one (c : Nat → Nat) (k : Nat) :
    oneBitCost c k (2 ^ k - 1) = sumCost c k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    simp only [oneBitCost, sumCost]
    have htb : (2 ^ (k + 1) - 1).testBit k = true := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      have hd : (2 ^ (k + 1) - 1) / 2 ^ k = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
      rw [hd]; decide
    have hmod : (2 ^ (k + 1) - 1) % 2 ^ k = 2 ^ k - 1 := by
      have h1 : 2 ^ (k + 1) - 1 = (2 ^ k - 1) + 1 * 2 ^ k := by omega
      rw [h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    rw [← oneBitCost_mod_le c k k (2 ^ (k + 1) - 1) (Nat.le_refl k), hmod, ih]
    simp [htb]

theorem bmiDist_zero_to_max (k : Nat) (c : Nat → Nat) :
    bmiDist k c (finZero k) (finMax k) = sumCost c k := by
  have h := bmiDist_compl k c (finZero k) (finMax k)
  have hm : finCompl (finMax k) = finZero k := Fin.ext (by dsimp [finCompl, finMax, finZero]; omega)
  have hz : finCompl (finZero k) = finMax k := Fin.ext (by dsimp [finCompl, finMax, finZero])
  rw [hm, hz, bmiDist_to_zero] at h
  rw [← h]
  exact oneBitCost_pow2_sub_one c k

/-- Exact Gray-code bit-inversion identity:
    For `y < 2^k`, `gray(2^k + y) = 2^k + gray((2^k - 1) - y)`. -/
theorem gray_add_pow2 {k y : Nat} (hy : y < 2 ^ k) :
    (2 ^ k + y) ^^^ ((2 ^ k + y) >>> 1) =
    2 ^ k + ((2 ^ k - 1 - y) ^^^ ((2 ^ k - 1 - y) >>> 1)) := by
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hcompl_lt : 2 ^ k - 1 - y < 2 ^ k := by omega
  have hgray_c_lt : (2 ^ k - 1 - y) ^^^ ((2 ^ k - 1 - y) >>> 1) < 2 ^ k :=
    Nat.xor_lt_two_pow hcompl_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ 1) hcompl_lt)
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_xor, Nat.testBit_shiftRight, testBit_add_pow2 hy, testBit_add_pow2 hgray_c_lt]
  by_cases hj1 : j < k
  · have hkj : decide (k = j) = false := by simp; omega
    simp only [hkj, Bool.false_or]
    by_cases hj2 : 1 + j < k
    · have hkj1 : decide (k = 1 + j) = false := by simp; omega
      simp only [hkj1, Bool.false_or]
      rw [testBit_compl hy hj1, testBit_compl hy hj2]
      cases y.testBit j <;> cases y.testBit (1 + j) <;> rfl
    · have hjeq : 1 + j = k := by omega
      have hkj1 : decide (k = 1 + j) = true := by simp [hjeq]
      have hy1 : y.testBit (1 + j) = false := Nat.testBit_lt_two_pow (by rw [hjeq]; exact hy)
      have hc1 : (2 ^ k - 1 - y).testBit (1 + j) = false :=
        Nat.testBit_lt_two_pow (by rw [hjeq]; exact hcompl_lt)
      simp only [hkj1, Bool.true_or, hy1, hc1, Bool.xor_false]
      rw [testBit_compl hy hj1]
      cases y.testBit j <;> rfl
  · by_cases hjk : k = j
    · subst hjk
      have hyk : y.testBit k = false := Nat.testBit_lt_two_pow hy
      have hpow : 2 ^ k ≤ 2 ^ (1 + k) := Nat.pow_le_pow_right (by omega) (by omega)
      have hyk1 : y.testBit (1 + k) = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy hpow)
      simp [hyk, hyk1]
    · have hjgt : k < j := by omega
      have hkj : decide (k = j) = false := by simp; omega
      have hkj1 : decide (k = 1 + j) = false := by simp; omega
      have h2le : 2 ^ k ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
      have h2le1 : 2 ^ k ≤ 2 ^ (1 + j) := Nat.pow_le_pow_right (by omega) (by omega)
      simp [hkj, hkj1,
            Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy h2le),
            Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy h2le1),
            Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hcompl_lt h2le),
            Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hcompl_lt h2le1)]

theorem graySuffixCost_shift_add_pow2 {m k z : Nat} (hm : m ≤ k) (hz : z < 2 ^ k) :
    (∀ b, b < m → popcount ((2 ^ k + z) >>> b) = 1 + popcount (z >>> b)) := by
  intro b hb
  have hdvd : 2 ^ k = 2 ^ (k - b) * 2 ^ b := by rw [← Nat.pow_add]; congr 1; omega
  have h1 : (2 ^ k + z) >>> b = 2 ^ (k - b) + (z >>> b) := by
    simp only [Nat.shiftRight_eq_div_pow]
    have h2 : 2 ^ k + z = z + 2 ^ (k - b) * 2 ^ b := by rw [hdvd]; omega
    rw [h2, Nat.add_mul_div_right _ _ (Nat.two_pow_pos b)]; omega
  rw [h1]
  have hz_sh : z >>> b < 2 ^ (k - b) := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos b), ← hdvd]; exact hz
  exact popcount_add_pow2 hz_sh

/-- **THEOREM 1B (Binary Gray-Code Suffix-Popcount Law, ∀ k, ∀ c, ∀ y < 2^k):**
    In the BMI1 Bit-Twiddle graph `B_k^(c)`, the exact tropical Kleene-star distance from `0`
    to ANY `y < 2^k` equals the weighted suffix-popcount of the Binary Gray Code `y ^^^ (y >>> 1)`! -/
theorem bmiDist_zero_eq_gray (k : Nat) (c : Nat → Nat) (y : Fin (2 ^ k)) :
    bmiDist k c (finZero k) y = graySuffixCost c k y.val := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    have hzero_lt : (finZero (k + 1)).val < 2 ^ k := hpos
    simp only [bmiDist, hzero_lt, ↓reduceDIte]
    by_cases hy : y.val < 2 ^ k
    · simp only [hy, ↓reduceDIte]
      have hgray_lt : y.val ^^^ (y.val >>> 1) < 2 ^ k :=
        Nat.xor_lt_two_pow hy (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ 1) hy)
      have hsh0 : (y.val ^^^ (y.val >>> 1)) >>> k = 0 := by
        rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt hgray_lt
      simp only [graySuffixCost, hsh0, popcount_zero, Nat.mul_zero, Nat.add_zero]
      exact ih ⟨y.val, hy⟩
    · simp only [hy, ↓reduceDIte]
      let y' := y.val - 2 ^ k
      have hy' : y' < 2 ^ k := by have := y.isLt; omega
      have hyeq : y.val = 2 ^ k + y' := by omega
      have hgray_eq := gray_add_pow2 hy'
      let gc := (2 ^ k - 1 - y') ^^^ ((2 ^ k - 1 - y') >>> 1)
      have hgc_lt : gc < 2 ^ k :=
        Nat.xor_lt_two_pow (by omega) (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ 1) (by omega))
      -- Show graySuffixCost c k (2^k + y') = sumCost c k + graySuffixCost c k (2^k - 1 - y')
      have hsum_part : ∀ m, m ≤ k →
          graySuffixCost c m (2 ^ k + y') = sumCost c m + graySuffixCost c m (2 ^ k - 1 - y') := by
        intro m hm
        induction m with
        | zero => rfl
        | succ m ihm =>
          simp only [graySuffixCost, sumCost]
          rw [ihm (by omega), hgray_eq]
          have hpop := graySuffixCost_shift_add_pow2 (Nat.le_refl k) hgc_lt m (by omega)
          dsimp only [gc] at hpop
          rw [hpop, Nat.mul_add, Nat.mul_one]
          omega
      have htop_sh : (2 ^ k + gc) >>> k = 1 := by
        rw [Nat.shiftRight_eq_div_pow]
        have h1 : 2 ^ k + gc = gc + 1 * 2 ^ k := by omega
        rw [h1, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hgc_lt]
      have hcompl_dist : bmiDist k c (finMax k) ⟨y', hy'⟩ = bmiDist k c (finZero k) (finCompl ⟨y', hy'⟩) := by
        have h := bmiDist_compl k c (finMax k) ⟨y', hy'⟩
        have hm : finCompl (finMax k) = finZero k := Fin.ext (by dsimp [finCompl, finMax, finZero]; omega)
        rw [hm] at h; exact h.symm
      have hfz : (⟨(finZero (k + 1)).val, hzero_lt⟩ : Fin (2 ^ k)) = finZero k := rfl
      rw [hfz, bmiDist_zero_to_max, hcompl_dist, ih (finCompl ⟨y', hy'⟩)]
      simp only [finCompl, graySuffixCost]
      rw [hyeq, hsum_part k (Nat.le_refl k), hgray_eq, htop_sh, popcount_one, Nat.mul_one]
      omega

/-- **THEOREM 1C (Exact Generalized Weighted Diameter of `B_k^(c)`, ∀ k, ∀ c : ℕ → ℕ):**
    1. Upper bound: `∀ x y : Fin (2^k), bmiDist k c x y ≤ weightedDiam c k`
    2. Exact attainment: `bmiDist k c 0 (altWord k) = weightedDiam c k`. -/
theorem bmiDist_le_weightedDiam (k : Nat) (c : Nat → Nat) (x y : Fin (2 ^ k)) :
    bmiDist k c x y ≤ weightedDiam c k := by
  induction k with
  | zero => exact Nat.le_refl 0
  | succ k ih =>
    simp only [bmiDist, weightedDiam, sumCost]
    by_cases hx : x.val < 2 ^ k <;> by_cases hy : y.val < 2 ^ k
    · simp only [hx, hy, ↓reduceDIte]
      exact Nat.le_trans (ih _ _) (by omega)
    · simp only [hx, hy, ↓reduceDIte]
      have h1 := bmiDist_to_max_le_sumCost k c ⟨x.val, hx⟩
      have h2 := ih (finMax k) ⟨y.val - 2 ^ k, by omega⟩
      omega
    · simp only [hx, hy, ↓reduceDIte]
      have h1 := bmiDist_to_zero_le_sumCost k c ⟨x.val - 2 ^ k, by omega⟩
      have h2 := ih (finZero k) ⟨y.val, hy⟩
      omega
    · simp only [hx, hy, ↓reduceDIte]
      exact Nat.le_trans (ih _ _) (by omega)

theorem bmiDist_altWord_eq_weightedDiam (k : Nat) (c : Nat → Nat) :
    bmiDist k c (finZero k) ⟨altWord k, altWord_lt k⟩ = weightedDiam c k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    have hzero_lt : (finZero (k + 1)).val < 2 ^ k := hpos
    have halt_ge : ¬ (altWord (k + 1) < 2 ^ k) := by simp [altWord]
    have halt_sub_lt : altWord (k + 1) - 2 ^ k < 2 ^ k := by
      have := altWord_lt (k + 1); omega
    simp only [bmiDist, hzero_lt, halt_ge, ↓reduceDIte, weightedDiam, sumCost]
    have hfz : (⟨(finZero (k + 1)).val, hzero_lt⟩ : Fin (2 ^ k)) = finZero k := rfl
    have hsub : (⟨altWord (k + 1) - 2 ^ k, halt_sub_lt⟩ : Fin (2 ^ k)) =
                finCompl ⟨altWord k, altWord_lt k⟩ := by
      apply Fin.ext; simp [altWord, finCompl]
    rw [hfz, bmiDist_zero_to_max, hsub]
    have hc := bmiDist_compl k c (finMax k) (finCompl ⟨altWord k, altWord_lt k⟩)
    have hm : finCompl (finMax k) = finZero k := Fin.ext (by dsimp [finCompl, finMax, finZero]; omega)
    have hcc : finCompl (finCompl ⟨altWord k, altWord_lt k⟩) = ⟨altWord k, altWord_lt k⟩ := by
      apply Fin.ext; simp [finCompl]; have := altWord_lt k; omega
    rw [hm, hcc] at hc
    rw [← hc, ih]
    omega

/-- Corollary 1 (Unit bit-cost `c(b) = 1`): Triangular numbers `k(k+1)/2`. -/
theorem weightedDiam_unit (k : Nat) :
    2 * weightedDiam (fun _ => 1) k = k * (k + 1) := by
  have hsum : ∀ m, sumCost (fun _ => 1) m = m := by
    intro m; induction m with | zero => rfl | succ m ih => simp [sumCost, ih]
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [weightedDiam, hsum]
    have h1 : 2 * (weightedDiam (fun _ => 1) k + (k + 1)) = 2 * weightedDiam (fun _ => 1) k + 2 * (k + 1) := by omega
    rw [h1, ih]
    have : k * (k + 1) + 2 * (k + 1) = (k + 1) * (k + 2) := by
      rw [← Nat.add_mul, Nat.mul_comm]
    exact this

/-- Corollary 2 (Linear bit-index cost `c(b) = b + 1`): Tetrahedral numbers `k(k+1)(k+2)/6`. -/
theorem weightedDiam_linear (k : Nat) :
    6 * weightedDiam (fun b => b + 1) k = k * (k + 1) * (k + 2) := by
  have hsum : ∀ m, 2 * sumCost (fun b => b + 1) m = m * (m + 1) := by
    intro m; induction m with
    | zero => rfl
    | succ m ih =>
      simp only [sumCost]
      have h1 : 2 * (sumCost (fun b => b + 1) m + (m + 1)) = 2 * sumCost (fun b => b + 1) m + 2 * (m + 1) := by omega
      rw [h1, ih, ← Nat.add_mul, Nat.mul_comm]
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [weightedDiam]
    have h1 : 6 * (weightedDiam (fun b => b + 1) k + sumCost (fun b => b + 1) (k + 1)) =
              6 * weightedDiam (fun b => b + 1) k + 3 * (2 * sumCost (fun b => b + 1) (k + 1)) := by omega
    rw [h1, ih, hsum (k + 1)]
    -- k*(k+1)*(k+2) + 3*(k+1)*(k+2) = (k+1)*(k+2)*(k+3)
    have ha : k * (k + 1) * (k + 2) = k * ((k + 1) * (k + 2)) := Nat.mul_assoc _ _ _
    have hb : 3 * ((k + 1) * (k + 2)) = 3 * ((k + 1) * (k + 2)) := rfl
    have hc : (k + 1) * (k + 2) * (k + 3) = (k + 3) * ((k + 1) * (k + 2)) := Nat.mul_comm _ _
    rw [ha, hc, ← Nat.add_mul]

/-- Corollary 3 (Exponential bit-value cost `c(b) = 2^b`): Eulerian numbers `2^(k+1) - k - 2`. -/
theorem weightedDiam_pow2 (k : Nat) (hk : 1 ≤ k) :
    weightedDiam (fun b => 2 ^ b) k + k + 2 = 2 ^ (k + 1) := by
  have hsum : ∀ m, sumCost (fun b => 2 ^ b) m + 1 = 2 ^ m := by
    intro m; induction m with
    | zero => rfl
    | succ m ih =>
      simp only [sumCost]
      have hpow : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [Nat.pow_succ]; omega
      omega
  induction k with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => decide
    | succ k' =>
      have ih' : weightedDiam (fun b => 2 ^ b) (k' + 1) + (k' + 1) + 2 = 2 ^ (k' + 2) := ih (by omega)
      have hstep : weightedDiam (fun b => 2 ^ b) (k' + 2) =
                   weightedDiam (fun b => 2 ^ b) (k' + 1) + sumCost (fun b => 2 ^ b) (k' + 2) := rfl
      have hs : sumCost (fun b => 2 ^ b) (k' + 2) + 1 = 2 ^ (k' + 2) := hsum (k' + 2)
      have hpow : 2 ^ (k' + 3) = 2 ^ (k' + 2) + 2 ^ (k' + 2) := by rw [Nat.pow_succ]; omega
      show weightedDiam (fun b => 2 ^ b) (k' + 2) + (k' + 2) + 2 = 2 ^ (k' + 3)
      omega

/-! ============================================================================
    SECTION 8: THEOREM 2 — BOOLEAN `(|, &)` EXACT MATRIX-POWER PERIODICITY,
               SHARP INDEX `k(k+1)/2 - 1`, AND EXACT KLEENE STABILIZATION
    ============================================================================ -/

/-- **THEOREM 2A (Boolean Kleene Star of `B_k` is All-Ones `J_{2^k}` for all `k`):** -/
theorem bmi_bool_star_eq_allTrue (k : Nat) :
    IsMatStar (bmiBoolMat k) (matAllTrue (2 ^ k)) := by
  have hcand : ∀ m, bmiBoolSpec.starCand m = matAllTrue (2 ^ m) := by
    intro m
    induction m with
    | zero =>
      funext i j
      have : i = j := Fin.ext (by have := i.isLt; have := j.isLt; omega)
      subst this
      simp [BitDoublingCollapseSpec.starCand, matId, matAllTrue, KleeneSemiring.one]
    | succ m ihm =>
      funext i j
      unfold BitDoublingCollapseSpec.starCand
      dsimp only
      rw [ihm]
      simp only [blockMat, matAllTrue, bmiBoolSpec, KleeneSemiring.mul]
      by_cases hi : i.val < 2 ^ m <;> by_cases hj : j.val < 2 ^ m <;> simp [hi, hj]
  rw [← hcand k]
  apply bmiBoolSpec.sound
  · intro m; rw [hcand m]; rfl
  · intro m; rw [hcand m]; rfl
  · intro m; rw [hcand m]; rfl

/-- Helper: Boolean matrix multiplication corresponds to existential witness. -/
theorem bool_finSum_eq_true_iff {n : Nat} {f : Fin n → Bool} :
    finSum n f = true ↔ ∃ k : Fin n, f k = true := by
  induction n with
  | zero =>
    simp only [finSum, KleeneSemiring.zero]
    exact ⟨fun h => Bool.noConfusion h, fun ⟨k, _⟩ => Fin.elim0 k⟩
  | succ n ih =>
    simp only [finSum, KleeneSemiring.add, Bool.or_eq_true]
    rw [ih]
    constructor
    · rintro (⟨k, hk⟩ | hn)
      · exact ⟨⟨k.val, Nat.lt_succ_of_lt k.isLt⟩, hk⟩
      · exact ⟨⟨n, Nat.lt_succ_self n⟩, hn⟩
    · rintro ⟨k, hk⟩
      by_cases hkn : k.val < n
      · exact Or.inl ⟨⟨k.val, hkn⟩, hk⟩
      · have heq : k = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext (by have := k.isLt; dsimp; omega)
        rw [heq] at hk; exact Or.inr hk

theorem bool_matMul_eq_true_iff {n : Nat} {A B : Mat Bool n} {i j : Fin n} :
    matMul A B i j = true ↔ ∃ k : Fin n, A i k = true ∧ B k j = true := by
  simp only [matMul, bool_finSum_eq_true_iff, KleeneSemiring.mul, Bool.and_eq_true]

theorem bool_matPow_add {n : Nat} (M : Mat Bool n) (a b : Nat) :
    matPow M (a + b) = matMul (matPow M a) (matPow M b) := by
  induction b with
  | zero => simp [matPow, matMul_id_right]
  | succ b ih =>
    have h : a + (b + 1) = (a + b) + 1 := by omega
    rw [h, matPow, ih, matMul_assoc]; rfl

/-- Every edge of `bmiBoolMat k` flips popcount parity! -/
theorem bmiBoolMat_parity (k : Nat) (x y : Fin (2 ^ k)) :
    bmiBoolMat k x y = true → (popcount x.val + popcount y.val) % 2 = 1 := by
  induction k with
  | zero =>
    intro h; simp [bmiBoolMat, BitDoublingCollapseSpec.mat, matZero, KleeneSemiring.zero] at h
  | succ k ih =>
    intro h
    change blockMat (bmiBoolMat k) (matSingle (finMax k) (finMax k) true)
                    (matSingle (finZero k) (finZero k) true) (bmiBoolMat k) x y = true at h
    simp only [blockMat, matSingle, finMax, finZero, KleeneSemiring.zero] at h
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    by_cases hx : x.val < 2 ^ k <;> by_cases hy : y.val < 2 ^ k
    · simp only [hx, hy, ↓reduceDIte] at h
      exact ih ⟨x.val, hx⟩ ⟨y.val, hy⟩ h
    · simp only [hx, hy, ↓reduceDIte] at h
      simp at h
      rcases h with ⟨h1, h2⟩
      have hyeq : y.val = 2 ^ k + (2 ^ k - 1) := by omega
      rw [h1, hyeq, popcount_add_pow2 (by have := Nat.two_pow_pos k; omega)]
      omega
    · simp only [hx, hy, ↓reduceDIte] at h
      simp at h
      rcases h with ⟨h1, h2⟩
      have hxeq : x.val = 2 ^ k + 0 := by omega
      have h2' : y.val = 0 := congrArg Fin.val h2
      rw [hxeq, h2', popcount_add_pow2 (Nat.two_pow_pos k), popcount_zero]
    · simp only [hx, hy, ↓reduceDIte] at h
      have hxlt : x.val - 2 ^ k < 2 ^ k := by have := x.isLt; omega
      have hylt : y.val - 2 ^ k < 2 ^ k := by have := y.isLt; omega
      have hxeq : x.val = 2 ^ k + (x.val - 2 ^ k) := by omega
      have hyeq : y.val = 2 ^ k + (y.val - 2 ^ k) := by omega
      have hp := ih ⟨x.val - 2 ^ k, hxlt⟩ ⟨y.val - 2 ^ k, hylt⟩ h
      dsimp only at hp
      rw [hxeq, hyeq, popcount_add_pow2 hxlt, popcount_add_pow2 hylt]
      omega

theorem bmiBoolPow_parity (k t : Nat) (x y : Fin (2 ^ k)) :
    matPow (bmiBoolMat k) t x y = true → (popcount x.val + popcount y.val + t) % 2 = 0 := by
  induction t generalizing y with
  | zero =>
    intro h
    simp only [matPow, matId, KleeneSemiring.one, KleeneSemiring.zero] at h
    split at h
    · rename_i hxy; subst hxy; omega
    · cases h
  | succ t ih =>
    intro h
    rw [matPow, bool_matMul_eq_true_iff] at h
    rcases h with ⟨z, hz1, hz2⟩
    have h1 := ih z hz1
    have h2 := bmiBoolMat_parity k z y hz2
    omega

/-- Every edge of `bmiBoolMat k` has weight `1` in `bmiTropMat k (fun _ => 1)`. -/
theorem bmiBool_to_trop_edge (k : Nat) (x y : Fin (2 ^ k)) :
    bmiBoolMat k x y = true → bmiTropMat k (fun _ => 1) x y = TropNat.fin 1 := by
  induction k with
  | zero =>
    intro h; simp [bmiBoolMat, BitDoublingCollapseSpec.mat, matZero, KleeneSemiring.zero] at h
  | succ k ih =>
    intro h
    change blockMat (bmiBoolMat k) (matSingle (finMax k) (finMax k) true)
                    (matSingle (finZero k) (finZero k) true) (bmiBoolMat k) x y = true at h
    change blockMat (bmiTropMat k (fun _ => 1)) (matSingle (finMax k) (finMax k) (TropNat.fin 1))
                    (matSingle (finZero k) (finZero k) (TropNat.fin 1)) (bmiTropMat k (fun _ => 1)) x y = TropNat.fin 1
    simp only [blockMat, matSingle, KleeneSemiring.zero] at h ⊢
    by_cases hx : x.val < 2 ^ k <;> by_cases hy : y.val < 2 ^ k
    · simp only [hx, hy, ↓reduceDIte] at h ⊢; exact ih _ _ h
    · simp only [hx, hy, ↓reduceDIte] at h ⊢
      split at h
      · rename_i he; simp [he]
      · cases h
    · simp only [hx, hy, ↓reduceDIte] at h ⊢
      split at h
      · rename_i he; simp [he]
      · cases h
    · simp only [hx, hy, ↓reduceDIte] at h ⊢; exact ih _ _ h

/-- Tropical lower bound: any Boolean `t`-step walk has `bmiDist k 1 x y ≤ t`! -/
theorem bmiBoolPow_dist_le (k t : Nat) (x y : Fin (2 ^ k)) :
    matPow (bmiBoolMat k) t x y = true → bmiDist k (fun _ => 1) x y ≤ t := by
  have hpow : ∀ m a b, matPow (bmiBoolMat k) m a b = true →
      KleeneSemiring.le (TropNat.fin m) (matPow (bmiTropMat k (fun _ => 1)) m a b) := by
    intro m
    induction m with
    | zero =>
      intro a b h
      simp only [matPow, matId, KleeneSemiring.one, KleeneSemiring.zero] at h ⊢
      split at h
      · rename_i hab; subst hab; simp [KleeneSemiring.le_refl]
      · cases h
    | succ m ihm =>
      intro a b h
      rw [matPow, bool_matMul_eq_true_iff] at h
      rcases h with ⟨z, hz1, hz2⟩
      have h1 := ihm a z hz1
      have h2 := bmiBool_to_trop_edge k z b hz2
      have hstep : KleeneSemiring.le
          (KleeneSemiring.mul (TropNat.fin m) (TropNat.fin 1))
          (KleeneSemiring.mul (matPow (bmiTropMat k (fun _ => 1)) m a z) (bmiTropMat k (fun _ => 1) z b)) :=
        KleeneSemiring.mul_mono h1 (by rw [h2]; exact KleeneSemiring.le_refl _)
      exact KleeneSemiring.le_trans hstep
        (le_finSum (fun l => KleeneSemiring.mul (matPow (bmiTropMat k (fun _ => 1)) m a l) (bmiTropMat k (fun _ => 1) l b)) z)
  intro h
  have h1 := hpow t x y h
  have hstar := bmi_trop_star_exact k (fun _ => 1)
  rw [← bmiTropMat_eq_bitwise] at hstar
  have h2 := hstar.pow_le t x y
  have h3 := KleeneSemiring.le_trans h1 h2
  exact (trop_le_fin_iff t (bmiDist k (fun _ => 1) x y)).mp h3

theorem lt_two_pow_succ {k x : Nat} (h : x < 2 ^ k) : x < 2 ^ (k + 1) := by
  have : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
  omega

theorem add_lt_two_pow_succ {k x : Nat} (h : x < 2 ^ k) : 2 ^ k + x < 2 ^ (k + 1) := by
  have : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
  omega

/-- Lifting a Boolean walk from `B_k` into the lower or upper half of `B_{k+1}`. -/
theorem bmiBoolPow_lift_lo (k t : Nat) (x y : Fin (2 ^ k)) :
    matPow (bmiBoolMat k) t x y = true →
    matPow (bmiBoolMat (k + 1)) t ⟨x.val, lt_two_pow_succ x.isLt⟩ ⟨y.val, lt_two_pow_succ y.isLt⟩ = true := by
  induction t generalizing y with
  | zero =>
    intro h
    simp only [matPow, matId, KleeneSemiring.one, KleeneSemiring.zero] at h ⊢
    split at h
    · rename_i hxy; subst hxy; simp
    · cases h
  | succ t ih =>
    intro h
    rw [matPow, bool_matMul_eq_true_iff] at h
    rcases h with ⟨z, hz1, hz2⟩
    rw [matPow, bool_matMul_eq_true_iff]
    refine ⟨⟨z.val, lt_two_pow_succ z.isLt⟩, ih z hz1, ?_⟩
    change blockMat (bmiBoolMat k) _ _ (bmiBoolMat k) _ _ = true
    simp [blockMat, z.isLt, y.isLt, hz2]

theorem bmiBoolPow_lift_hi (k t : Nat) (x y : Fin (2 ^ k)) :
    matPow (bmiBoolMat k) t x y = true →
    matPow (bmiBoolMat (k + 1)) t ⟨2 ^ k + x.val, add_lt_two_pow_succ x.isLt⟩ ⟨2 ^ k + y.val, add_lt_two_pow_succ y.isLt⟩ = true := by
  induction t generalizing y with
  | zero =>
    intro h
    simp only [matPow, matId, KleeneSemiring.one, KleeneSemiring.zero] at h ⊢
    split at h
    · rename_i hxy; subst hxy; simp
    · cases h
  | succ t ih =>
    intro h
    rw [matPow, bool_matMul_eq_true_iff] at h
    rcases h with ⟨z, hz1, hz2⟩
    rw [matPow, bool_matMul_eq_true_iff]
    refine ⟨⟨2 ^ k + z.val, add_lt_two_pow_succ z.isLt⟩, ih z hz1, ?_⟩
    change blockMat (bmiBoolMat k) _ _ (bmiBoolMat k) _ _ = true
    have h1 : ¬ (2 ^ k + z.val < 2 ^ k) := by omega
    have h2 : ¬ (2 ^ k + y.val < 2 ^ k) := by omega
    simp [blockMat, h1, h2, hz2]

/-- Exact walk realization: there EXISTS a Boolean walk of length `bmiDist k 1 x y`! -/
theorem bmiBoolPow_realize_dist (k : Nat) (x y : Fin (2 ^ k)) :
    matPow (bmiBoolMat k) (bmiDist k (fun _ => 1) x y) x y = true := by
  induction k with
  | zero =>
    have hxy : x = y := Fin.ext (by have := x.isLt; have := y.isLt; omega)
    subst hxy; simp [bmiDist, matPow, matId, KleeneSemiring.one]
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    simp only [bmiDist]
    by_cases hx : x.val < 2 ^ k <;> by_cases hy : y.val < 2 ^ k
    · simp only [hx, hy, ↓reduceDIte]
      exact bmiBoolPow_lift_lo k _ ⟨x.val, hx⟩ ⟨y.val, hy⟩ (ih _ _)
    · simp only [hx, hy, ↓reduceDIte]
      let x' : Fin (2 ^ k) := ⟨x.val, hx⟩
      let y' : Fin (2 ^ k) := ⟨y.val - 2 ^ k, by have := y.isLt; omega⟩
      have h1 := bmiBoolPow_lift_lo k _ x' (finMax k) (ih x' (finMax k))
      have h2 := bmiBoolPow_lift_hi k _ (finMax k) y' (ih (finMax k) y')
      have hbridge : bmiBoolMat (k + 1) ⟨(finMax k).val, by omega⟩ ⟨2 ^ k + (finMax k).val, by omega⟩ = true := by
        change blockMat (bmiBoolMat k) (matSingle (finMax k) (finMax k) true) _ _ _ _ = true
        have hlt : (finMax k).val < 2 ^ k := (finMax k).isLt
        have hge : ¬ (2 ^ k + (finMax k).val < 2 ^ k) := by omega
        simp [blockMat, hlt, hge, matSingle]
      have hstep1 : matPow (bmiBoolMat (k + 1)) (bmiDist k (fun _ => 1) x' (finMax k) + 1)
                      x ⟨2 ^ k + (finMax k).val, by omega⟩ = true := by
        rw [matPow, bool_matMul_eq_true_iff]
        exact ⟨⟨(finMax k).val, by omega⟩, h1, hbridge⟩
      rw [bool_matPow_add, bool_matMul_eq_true_iff]
      refine ⟨⟨2 ^ k + (finMax k).val, by omega⟩, hstep1, ?_⟩
      have hyeq : (⟨2 ^ k + y'.val, by omega⟩ : Fin (2 ^ (k + 1))) = y := Fin.ext (by dsimp [y']; omega)
      rwa [hyeq] at h2
    · simp only [hx, hy, ↓reduceDIte]
      let x' : Fin (2 ^ k) := ⟨x.val - 2 ^ k, by have := x.isLt; omega⟩
      let y' : Fin (2 ^ k) := ⟨y.val, hy⟩
      have h1 := bmiBoolPow_lift_hi k _ x' (finZero k) (ih x' (finZero k))
      have h2 := bmiBoolPow_lift_lo k _ (finZero k) y' (ih (finZero k) y')
      have hbridge : bmiBoolMat (k + 1) ⟨2 ^ k + (finZero k).val, by omega⟩ ⟨(finZero k).val, by omega⟩ = true := by
        change blockMat (bmiBoolMat k) _ (matSingle (finZero k) (finZero k) true) _ _ _ = true
        have hlt : (finZero k).val < 2 ^ k := (finZero k).isLt
        have hge : ¬ (2 ^ k + (finZero k).val < 2 ^ k) := by omega
        simp [blockMat, hlt, hge, matSingle]
      have hxeq : (⟨2 ^ k + x'.val, by omega⟩ : Fin (2 ^ (k + 1))) = x := Fin.ext (by dsimp [x']; omega)
      rw [hxeq] at h1
      have hstep1 : matPow (bmiBoolMat (k + 1)) (bmiDist k (fun _ => 1) x' (finZero k) + 1)
                      x ⟨(finZero k).val, by omega⟩ = true := by
        rw [matPow, bool_matMul_eq_true_iff]
        exact ⟨⟨2 ^ k + (finZero k).val, by omega⟩, h1, hbridge⟩
      rw [bool_matPow_add, bool_matMul_eq_true_iff]
      exact ⟨⟨(finZero k).val, by omega⟩, hstep1, h2⟩
    · simp only [hx, hy, ↓reduceDIte]
      let x' : Fin (2 ^ k) := ⟨x.val - 2 ^ k, by have := x.isLt; omega⟩
      let y' : Fin (2 ^ k) := ⟨y.val - 2 ^ k, by have := y.isLt; omega⟩
      have h := bmiBoolPow_lift_hi k _ x' y' (ih x' y')
      have hxeq : (⟨2 ^ k + x'.val, by omega⟩ : Fin (2 ^ (k + 1))) = x := Fin.ext (by dsimp [x']; omega)
      have hyeq : (⟨2 ^ k + y'.val, by omega⟩ : Fin (2 ^ (k + 1))) = y := Fin.ext (by dsimp [y']; omega)
      rwa [hxeq, hyeq] at h

/-- Every vertex in `B_k` (`k ≥ 1`) has a 2-cycle (`x ↔ x ^^^ 1`), so `B_k^2 ≥ I`! -/
theorem bmiBoolPow_two_diag (k : Nat) (hk : 1 ≤ k) (x : Fin (2 ^ k)) :
    matPow (bmiBoolMat k) 2 x x = true := by
  induction k with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      match x with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
    | succ k' =>
      have hpow : 2 ^ (k' + 2) = 2 ^ (k' + 1) + 2 ^ (k' + 1) := by rw [Nat.pow_succ]; omega
      by_cases hx : x.val < 2 ^ (k' + 1)
      · exact bmiBoolPow_lift_lo (k' + 1) 2 ⟨x.val, hx⟩ ⟨x.val, hx⟩ (ih (by omega) ⟨x.val, hx⟩)
      · let x' : Fin (2 ^ (k' + 1)) := ⟨x.val - 2 ^ (k' + 1), by have := x.isLt; omega⟩
        have h := bmiBoolPow_lift_hi (k' + 1) 2 x' x' (ih (by omega) x')
        have hxeq : (⟨2 ^ (k' + 1) + x'.val, by omega⟩ : Fin (2 ^ (k' + 2))) = x := Fin.ext (by dsimp [x']; omega)
        rwa [hxeq] at h

/-- **THEOREM 2B (Exact All-Powers Boolean Characterization of `B_k`, ∀ k ≥ 1, ∀ t, x, y):**
    `(B_k^t)_{x, y} = true ↔ bmiDist k 1 x y ≤ t ∧ (popcount x + popcount y + t) % 2 = 0`! -/
theorem bmiBoolPow_iff (k : Nat) (hk : 1 ≤ k) (t : Nat) (x y : Fin (2 ^ k)) :
    matPow (bmiBoolMat k) t x y = true ↔
      bmiDist k (fun _ => 1) x y ≤ t ∧ (popcount x.val + popcount y.val + t) % 2 = 0 := by
  constructor
  · intro h
    exact ⟨bmiBoolPow_dist_le k t x y h, bmiBoolPow_parity k t x y h⟩
  · rintro ⟨hle, hpar⟩
    have hreal := bmiBoolPow_realize_dist k x y
    have hpar_d := bmiBoolPow_parity k _ x y hreal
    -- t - d is even! Write t = d + 2 * m
    let d := bmiDist k (fun _ => 1) x y
    have heven : (t - d) % 2 = 0 := by omega
    let m := (t - d) / 2
    have ht_eq : t = d + 2 * m := by omega
    rw [ht_eq]
    -- Show by induction on m that matPow (bmiBoolMat k) (d + 2*m) x y = true
    clear hle hpar hpar_d heven ht_eq
    induction m with
    | zero => simpa using hreal
    | succ m ihm =>
      have hadd : d + 2 * (m + 1) = (d + 2 * m) + 2 := by omega
      rw [hadd, bool_matPow_add, bool_matMul_eq_true_iff]
      exact ⟨y, ihm, bmiBoolPow_two_diag k hk y⟩

/-- **THEOREM 2C (Exact Boolean Matrix-Power Periodicity of `B_k`, ∀ k ≥ 2):**
    For EVERY `k ≥ 2` and EVERY `t ≥ k*(k+1)/2 - 1`, `B_k^{t + 2} = B_k^t`! -/
theorem bmiBoolPow_periodic (k : Nat) (hk : 2 ≤ k) (t : Nat)
    (ht : k * (k + 1) / 2 - 1 ≤ t) :
    matPow (bmiBoolMat k) (t + 2) = matPow (bmiBoolMat k) t := by
  have hk1 : 1 ≤ k := by omega
  have hdiam : weightedDiam (fun _ => 1) k = k * (k + 1) / 2 := by
    have := weightedDiam_unit k; omega
  funext x y
  apply Bool.eq_iff_iff.mpr
  rw [bmiBoolPow_iff k hk1 (t + 2) x y, bmiBoolPow_iff k hk1 t x y]
  constructor
  · rintro ⟨_, hpar2⟩
    have hpar : (popcount x.val + popcount y.val + t) % 2 = 0 := by omega
    refine ⟨?_, hpar⟩
    have hle_diam : bmiDist k (fun _ => 1) x y ≤ k * (k + 1) / 2 := by
      rw [← hdiam]; exact bmiDist_le_weightedDiam k (fun _ => 1) x y
    by_cases hgt : k * (k + 1) / 2 ≤ t
    · omega
    · -- Critical sharp boundary: t = k*(k+1)/2 - 1!
      -- If bmiDist = k*(k+1)/2, then its parity contradicts hpar!
      have ht_eq : t = k * (k + 1) / 2 - 1 := by omega
      have hpar_d := bmiBoolPow_parity k _ x y (bmiBoolPow_realize_dist k x y)
      have hne : bmiDist k (fun _ => 1) x y ≠ k * (k + 1) / 2 := by
        intro heq; rw [heq] at hpar_d; omega
      omega
  · rintro ⟨hle, hpar⟩
    exact ⟨by omega, by omega⟩

/-- **THEOREM 2D (Sharpness of Matrix-Power Index, ∀ k ≥ 2):**
    At `t = k*(k+1)/2 - 2`, `B_k^{t + 2} ≠ B_k^t` (explicitly witnessed at `(0, altWord k)`)! -/
theorem bmiBoolPow_index_sharp (k : Nat) (hk : 2 ≤ k) :
    let t0 := k * (k + 1) / 2 - 2
    matPow (bmiBoolMat k) (t0 + 2) ≠ matPow (bmiBoolMat k) t0 := by
  intro t0 heq
  have hk1 : 1 ≤ k := by omega
  have hdiam_ge : 3 ≤ k * (k + 1) / 2 := by
    have : 2 * 3 ≤ k * (k + 1) := Nat.mul_le_mul hk (by omega)
    omega
  have hdiam : weightedDiam (fun _ => 1) k = k * (k + 1) / 2 := by
    have := weightedDiam_unit k; omega
  have hdist : bmiDist k (fun _ => 1) (finZero k) ⟨altWord k, altWord_lt k⟩ = k * (k + 1) / 2 := by
    rw [bmiDist_altWord_eq_weightedDiam, hdiam]
  have hreal := bmiBoolPow_realize_dist k (finZero k) ⟨altWord k, altWord_lt k⟩
  rw [hdist] at hreal
  have ht2 : t0 + 2 = k * (k + 1) / 2 := by omega
  rw [← ht2] at hreal
  have hcontra := congrFun (congrFun heq (finZero k)) ⟨altWord k, altWord_lt k⟩
  rw [hreal] at hcontra
  have hle := bmiBoolPow_dist_le k t0 (finZero k) ⟨altWord k, altWord_lt k⟩ hcontra.symm
  rw [hdist] at hle
  omega

/-- **THEOREM 2E (Sharpness of Period `p = 2`, ∀ k ≥ 1, ∀ t):**
    `B_k^{t + 1} ≠ B_k^t` for EVERY `t : Nat` (witnessed by diagonal entry `(0, 0)`)! -/
theorem bmiBoolPow_period_sharp (k : Nat) (hk : 1 ≤ k) (t : Nat) :
    matPow (bmiBoolMat k) (t + 1) ≠ matPow (bmiBoolMat k) t := by
  intro heq
  have h00 := congrFun (congrFun heq (finZero k)) (finZero k)
  have hdist0 : bmiDist k (fun _ => 1) (finZero k) (finZero k) = 0 := by
    rw [bmiDist_to_zero]; exact oneBitCost_zero _ k
  have hiff1 := bmiBoolPow_iff k hk (t + 1) (finZero k) (finZero k)
  have hiff0 := bmiBoolPow_iff k hk t (finZero k) (finZero k)
  by_cases hp : t % 2 = 0
  · have htrue : matPow (bmiBoolMat k) t (finZero k) (finZero k) = true := by
      rw [hiff0]; refine ⟨by omega, ?_⟩; simp [finZero, popcount_zero]; omega
    rw [htrue] at h00
    have hpar1 := (hiff1.mp h00).2
    simp [finZero, popcount_zero] at hpar1; omega
  · have htrue : matPow (bmiBoolMat k) (t + 1) (finZero k) (finZero k) = true := by
      rw [hiff1]; refine ⟨by omega, ?_⟩; simp [finZero, popcount_zero]; omega
    rw [htrue] at h00
    have hpar0 := (hiff0.mp h00.symm).2
    simp [finZero, popcount_zero] at hpar0; omega

/-- **Bitwise Faithfulness Theorem for `A_k`:**
    For ALL `k : Nat`, `aluTropMat k` equals the hardware ALU matrix `aluBitwiseMat k`! -/
theorem aluTropMat_eq_bitwise (k : Nat) : aluTropMat k = aluBitwiseMat k := by
  induction k with
  | zero =>
    funext x y
    simp [aluTropMat, BitDoublingCollapseSpec.mat, matZero, aluBitwiseMat, KleeneSemiring.zero]
  | succ k ih =>
    funext x y
    change blockMat (aluTropMat k)
                    (matSingle (finMax k) (finZero k) (TropNat.fin (k + 1)))
                    (matSingle (finZero k) (finZero k) (TropNat.fin 1))
                    (aluTropMat k) x y = aluBitwiseMat (k + 1) x y
    rw [ih]
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    simp only [blockMat, matSingle, finMax, finZero, aluBitwiseMat, KleeneSemiring.zero]
    by_cases hx : x.val < 2 ^ k <;> by_cases hy : y.val < 2 ^ k
    · -- Quadrant (0, 0)
      simp only [hx, hy, ↓reduceDIte]
      by_cases hx1 : x.val + 1 < 2 ^ k
      · have hx1' : x.val + 1 < 2 ^ (k + 1) := by omega
        simp only [hx1, hx1', true_and]
      · have hne : y.val ≠ x.val + 1 := by omega
        simp only [hx1, ↓reduceIte, hne, and_false]
    · -- Quadrant (0, 1)
      simp only [hx, hy, ↓reduceDIte]
      have hband_lt : x.val &&& (x.val - 1) < 2 ^ k := Nat.lt_of_le_of_lt Nat.and_le_left hx
      have hband_ne : y.val ≠ x.val &&& (x.val - 1) := by omega
      by_cases hxeq : x.val = 2 ^ k - 1
      · have hctz : ctzZeroNat x.val = k := by rw [hxeq]; exact ctzZeroNat_pow2_sub_one k
        have hx1 : x.val + 1 < 2 ^ (k + 1) := by omega
        by_cases hyeq : y.val = 2 ^ k
        · have hadd : y.val = x.val + 1 := by omega
          have hc1 : (⟨x.val, hx⟩ : Fin (2 ^ k)) = ⟨2 ^ k - 1, by omega⟩ ∧
                     (⟨y.val - 2 ^ k, by omega⟩ : Fin (2 ^ k)) = ⟨0, hpos⟩ :=
            ⟨Fin.ext hxeq, Fin.ext (by dsimp; omega)⟩
          have hc2 : x.val + 1 < 2 ^ (k + 1) ∧ y.val = x.val + 1 := ⟨hx1, hadd⟩
          have hL : (if (⟨x.val, hx⟩ : Fin (2 ^ k)) = ⟨2 ^ k - 1, by omega⟩ ∧
                        (⟨y.val - 2 ^ k, by omega⟩ : Fin (2 ^ k)) = ⟨0, hpos⟩
                     then TropNat.fin (k + 1) else TropNat.inf) = TropNat.fin (k + 1) := by
            simp [hc1]
          have hR : (if x.val + 1 < 2 ^ (k + 1) ∧ y.val = x.val + 1
                     then TropNat.fin (1 + ctzZeroNat x.val)
                     else if 0 < x.val ∧ y.val = x.val &&& (x.val - 1)
                     then TropNat.fin 1 else TropNat.inf) = TropNat.fin (1 + k) := by
            simp [hc2, hctz]
          change (if (⟨x.val, hx⟩ : Fin (2 ^ k)) = ⟨2 ^ k - 1, by omega⟩ ∧
                     (⟨y.val - 2 ^ k, by omega⟩ : Fin (2 ^ k)) = ⟨0, hpos⟩
                  then TropNat.fin (k + 1) else TropNat.inf) = _
          rw [hL, hR, Nat.add_comm]
        · have hne2 : y.val - 2 ^ k ≠ 0 := by omega
          have hL2 : ¬ ((⟨y.val - 2 ^ k, by omega⟩ : Fin (2 ^ k)) = ⟨0, hpos⟩) := by
            intro h; exact hne2 (congrArg Fin.val h)
          have hadd_ne : y.val ≠ x.val + 1 := by omega
          simp [hL2, hadd_ne, hband_ne]
      · have hL1 : ¬ ((⟨x.val, hx⟩ : Fin (2 ^ k)) = ⟨2 ^ k - 1, by omega⟩) := by
          intro h; exact hxeq (congrArg Fin.val h)
        have hadd_ne : y.val ≠ x.val + 1 := by omega
        simp [hL1, hadd_ne, hband_ne]
    · -- Quadrant (1, 0)
      simp only [hx, hy, ↓reduceDIte]
      have hadd_ne : y.val ≠ x.val + 1 := by omega
      by_cases hxeq : x.val = 2 ^ k
      · have hband : x.val &&& (x.val - 1) = 0 := by rw [hxeq]; exact band_dec_corner k
        have hxpos : 0 < x.val := by omega
        by_cases hyeq : y.val = 0
        · have hL1 : (⟨x.val - 2 ^ k, by omega⟩ : Fin (2 ^ k)) = ⟨0, hpos⟩ := Fin.ext (by dsimp; omega)
          simp [hL1, hxpos, hband, hyeq]
        · have hL2 : ¬ ((⟨y.val, hy⟩ : Fin (2 ^ k)) = ⟨0, hpos⟩) := by
            intro h; exact hyeq (congrArg Fin.val h)
          simp [hL2, hadd_ne, hband, hyeq]
      · have hne1 : x.val - 2 ^ k ≠ 0 := by omega
        have hL1 : ¬ ((⟨x.val - 2 ^ k, by omega⟩ : Fin (2 ^ k)) = ⟨0, hpos⟩) := by
          intro h; exact hne1 (congrArg Fin.val h)
        let x' := x.val - 2 ^ k
        have hx' : 0 < x' := by omega
        have hxlt : x' < 2 ^ k := by have := x.isLt; omega
        have hxeq2 : x.val = 2 ^ k + x' := by omega
        have hband : x.val &&& (x.val - 1) = 2 ^ k + (x' &&& (x' - 1)) := by
          rw [hxeq2]; exact band_dec_add_pow2 hx' hxlt
        have hband_ne : y.val ≠ x.val &&& (x.val - 1) := by omega
        simp [hL1, hadd_ne, hband_ne]
    · -- Quadrant (1, 1)
      simp only [hx, hy, ↓reduceDIte]
      let x' := x.val - 2 ^ k
      let y' := y.val - 2 ^ k
      have hxlt : x' < 2 ^ k := by have := x.isLt; omega
      have hylt : y' < 2 ^ k := by have := y.isLt; omega
      have hxeq : x.val = 2 ^ k + x' := by omega
      have hyeq : y.val = 2 ^ k + y' := by omega
      have hiff1 : (x' + 1 < 2 ^ k ∧ y' = x' + 1) ↔ (x.val + 1 < 2 ^ (k + 1) ∧ y.val = x.val + 1) := by
        dsimp only [x', y']; omega
      have hiff2 : (0 < x' ∧ y' = x' &&& (x' - 1)) ↔ (0 < x.val ∧ y.val = x.val &&& (x.val - 1)) := by
        constructor
        · rintro ⟨ha, hb⟩
          refine ⟨by omega, ?_⟩
          rw [hyeq, hxeq, band_dec_add_pow2 ha hxlt, hb]
        · rintro ⟨ha, hb⟩
          by_cases hz : x' = 0
          · have hxk : x.val = 2 ^ k := by omega
            have h0 : x.val &&& (x.val - 1) = 0 := by rw [hxk]; exact band_dec_corner k
            omega
          · have ha' : 0 < x' := by omega
            refine ⟨ha', ?_⟩
            rw [hyeq, hxeq, band_dec_add_pow2 ha' hxlt] at hb
            omega
      by_cases h1 : x' + 1 < 2 ^ k ∧ y' = x' + 1
      · have h1' := hiff1.mp h1
        have hctz := ctzZeroNat_add_pow2 h1.1
        rw [← hxeq] at hctz
        have hL : (if x.val - 2 ^ k + 1 < 2 ^ k ∧ y.val - 2 ^ k = x.val - 2 ^ k + 1 then
                     TropNat.fin (1 + ctzZeroNat (x.val - 2 ^ k))
                   else if 0 < x.val - 2 ^ k ∧ y.val - 2 ^ k = (x.val - 2 ^ k) &&& (x.val - 2 ^ k - 1) then
                     TropNat.fin 1 else TropNat.inf) =
                  TropNat.fin (1 + ctzZeroNat (x.val - 2 ^ k)) := by split; rfl; exact absurd h1 ‹_›
        have hR : (if x.val + 1 < 2 ^ (k + 1) ∧ y.val = x.val + 1 then
                     TropNat.fin (1 + ctzZeroNat x.val)
                   else if 0 < x.val ∧ y.val = x.val &&& (x.val - 1) then
                     TropNat.fin 1 else TropNat.inf) =
                  TropNat.fin (1 + ctzZeroNat x.val) := by split; rfl; exact absurd h1' ‹_›
        rw [hL, hR, hctz]
      · have h1' : ¬ (x.val + 1 < 2 ^ (k + 1) ∧ y.val = x.val + 1) := mt hiff1.mpr h1
        have hL1 : (if x.val - 2 ^ k + 1 < 2 ^ k ∧ y.val - 2 ^ k = x.val - 2 ^ k + 1 then
                      TropNat.fin (1 + ctzZeroNat (x.val - 2 ^ k))
                    else if 0 < x.val - 2 ^ k ∧ y.val - 2 ^ k = (x.val - 2 ^ k) &&& (x.val - 2 ^ k - 1) then
                      TropNat.fin 1 else TropNat.inf) =
                   (if 0 < x.val - 2 ^ k ∧ y.val - 2 ^ k = (x.val - 2 ^ k) &&& (x.val - 2 ^ k - 1) then
                      TropNat.fin 1 else TropNat.inf) := by split; exact absurd ‹_› h1; rfl
        have hR1 : (if x.val + 1 < 2 ^ (k + 1) ∧ y.val = x.val + 1 then
                      TropNat.fin (1 + ctzZeroNat x.val)
                    else if 0 < x.val ∧ y.val = x.val &&& (x.val - 1) then
                      TropNat.fin 1 else TropNat.inf) =
                   (if 0 < x.val ∧ y.val = x.val &&& (x.val - 1) then
                      TropNat.fin 1 else TropNat.inf) := by split; exact absurd ‹_› h1'; rfl
        rw [hL1, hR1]
        by_cases h2 : 0 < x' ∧ y' = x' &&& (x' - 1)
        · have h2' := hiff2.mp h2
          have hL2 : (if 0 < x.val - 2 ^ k ∧ y.val - 2 ^ k = (x.val - 2 ^ k) &&& (x.val - 2 ^ k - 1) then
                        TropNat.fin 1 else TropNat.inf) = TropNat.fin 1 := by split; rfl; exact absurd h2 ‹_›
          have hR2 : (if 0 < x.val ∧ y.val = x.val &&& (x.val - 1) then
                        TropNat.fin 1 else TropNat.inf) = TropNat.fin 1 := by split; rfl; exact absurd h2' ‹_›
          rw [hL2, hR2]
        · have h2' : ¬ (0 < x.val ∧ y.val = x.val &&& (x.val - 1)) := mt hiff2.mpr h2
          have hL2 : (if 0 < x.val - 2 ^ k ∧ y.val - 2 ^ k = (x.val - 2 ^ k) &&& (x.val - 2 ^ k - 1) then
                        TropNat.fin 1 else TropNat.inf) = TropNat.inf := by split; exact absurd ‹_› h2; rfl
          have hR2 : (if 0 < x.val ∧ y.val = x.val &&& (x.val - 1) then
                        TropNat.fin 1 else TropNat.inf) = TropNat.inf := by split; exact absurd ‹_› h2'; rfl
          rw [hL2, hR2]

theorem aluStarCand_eq_fin (k : Nat) :
    aluTropSpec.starCand k = fun i j => TropNat.fin (aluDist k i j) := by
  induction k with
  | zero =>
    funext i j
    have : i = j := Fin.ext (by have := i.isLt; have := j.isLt; omega)
    subst this
    simp [BitDoublingCollapseSpec.starCand, matId, aluDist, KleeneSemiring.one]
  | succ k ih =>
    funext i j
    unfold BitDoublingCollapseSpec.starCand
    dsimp only
    rw [ih]
    simp only [blockMat, aluDist, aluTropSpec, KleeneSemiring.mul, TropNat.addT]
    by_cases hi : i.val < 2 ^ k <;> by_cases hj : j.val < 2 ^ k <;> simp [hi, hj]

theorem aluDist_zero_zero (k : Nat) : aluDist k (finZero k) (finZero k) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    have hlt : (finZero (k + 1)).val < 2 ^ k := hpos
    simp only [aluDist, hlt, ↓reduceDIte]
    exact ih

/-- Exact reverse-corner law: `D_k(x, 0) = popcount(x)`! -/
theorem aluDist_to_zero (k : Nat) (x : Fin (2 ^ k)) :
    aluDist k x (finZero k) = popcount x.val := by
  induction k with
  | zero =>
    simp [aluDist, popcount_zero]
  | succ k ih =>
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    have hlt : (finZero (k + 1)).val < 2 ^ k := hpos
    simp only [aluDist, hlt, ↓reduceDIte]
    by_cases hx : x.val < 2 ^ k
    · simp only [hx, ↓reduceDIte]; exact ih ⟨x.val, hx⟩
    · simp only [hx, ↓reduceDIte]
      let x' := x.val - 2 ^ k
      have hx' : x' < 2 ^ k := by have := x.isLt; omega
      have hxeq : x.val = 2 ^ k + x' := by omega
      have hfz : (⟨(finZero (k + 1)).val, hlt⟩ : Fin (2 ^ k)) = finZero k := rfl
      rw [hfz, aluDist_zero_zero, Nat.add_zero, ih ⟨x', hx'⟩]
      dsimp only
      rw [hxeq, popcount_add_pow2 hx']; omega

/-- **THEOREM 3A (Exact Infinite-Width Tropical Kleene Star of Ripple-Carry ALU Graph `A_k`):**
    Proved by directly reusing `BitDoublingCollapseSpec.sound`! -/
theorem alu_trop_star_exact (k : Nat) :
    IsMatStar (aluBitwiseMat k) (fun i j => TropNat.fin (aluDist k i j)) := by
  rw [← aluTropMat_eq_bitwise, ← aluStarCand_eq_fin]
  apply aluTropSpec.sound
  · intro m
    rw [aluStarCand_eq_fin]
    change KleeneSemiring.le (TropNat.fin ((m + 1) + aluDist m (finZero m) (finZero m) + 1))
                             (TropNat.fin (aluDist m (finMax m) (finZero m)))
    rw [trop_le_fin_iff, aluDist_zero_zero, aluDist_to_zero]
    simp only [finMax, popcount_pow2_sub_one]; omega
  · intro m; exact trop_le_one _
  · intro m
    rw [aluStarCand_eq_fin]
    change KleeneSemiring.le (TropNat.fin (1 + aluDist m (finZero m) (finMax m) + (m + 1)))
                             (TropNat.fin (aluDist m (finZero m) (finZero m)))
    rw [trop_le_fin_iff, aluDist_zero_zero]; omega

/-- Exact forward-corner telescoping law: `D_k(0, y) + popcount(y) = 2 * y`! -/
theorem aluDist_from_zero (k : Nat) (y : Fin (2 ^ k)) :
    aluDist k (finZero k) y + popcount y.val = 2 * y.val := by
  induction k with
  | zero =>
    simp [aluDist, popcount_zero]
  | succ k ih =>
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    have hlt : (finZero (k + 1)).val < 2 ^ k := hpos
    simp only [aluDist, hlt, ↓reduceDIte]
    by_cases hy : y.val < 2 ^ k
    · simp only [hy, ↓reduceDIte]; exact ih ⟨y.val, hy⟩
    · simp only [hy, ↓reduceDIte]
      let y' := y.val - 2 ^ k
      have hy' : y' < 2 ^ k := by have := y.isLt; omega
      have hyeq : y.val = 2 ^ k + y' := by omega
      have hfz : (⟨(finZero (k + 1)).val, hlt⟩ : Fin (2 ^ k)) = finZero k := rfl
      rw [hfz]
      have hmax : aluDist k (finZero k) (finMax k) + k = 2 * (2 ^ k - 1) := by
        have h := ih (finMax k); rwa [show (finMax k).val = 2 ^ k - 1 from rfl, popcount_pow2_sub_one] at h
      have hy'_eq : aluDist k (finZero k) ⟨y.val - 2 ^ k, hy'⟩ + popcount y' = 2 * y' :=
        ih ⟨y.val - 2 ^ k, hy'⟩
      have hpop : popcount y.val = 1 + popcount y' := by
        rw [hyeq]; exact popcount_add_pow2 hy'
      rw [hpop]
      omega

/-- Exact upper bound: `D_k(x, y) + k + 2 ≤ 2^(k+1)`. -/
theorem aluDist_le_diam (k : Nat) (x y : Fin (2 ^ k)) :
    aluDist k x y + k + 2 ≤ 2 ^ (k + 1) := by
  have htoMax : ∀ m (u : Fin (2 ^ m)), aluDist m u (finMax m) + m + 2 ≤ 2 ^ (m + 1) := by
    intro m
    induction m with
    | zero => intro u; simp [aluDist]
    | succ m ihm =>
      intro u
      have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
      have hpow1 : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [Nat.pow_succ]; omega
      have hpow2 : 2 ^ (m + 2) = 2 ^ (m + 1) + 2 ^ (m + 1) := by rw [Nat.pow_succ]; omega
      have hm_ge : ¬ ((finMax (m + 1)).val < 2 ^ m) := by simp [finMax]; omega
      simp only [aluDist, hm_ge, ↓reduceDIte]
      have hmsub : (⟨(finMax (m + 1)).val - 2 ^ m, by simp [finMax]; omega⟩ : Fin (2 ^ m)) = finMax m :=
        Fin.ext (by simp [finMax]; omega)
      by_cases hu : u.val < 2 ^ m
      · simp only [hu, ↓reduceDIte]
        rw [hmsub]
        have h1 := ihm ⟨u.val, hu⟩
        have h2 : aluDist m (finZero m) (finMax m) + m = 2 * (2 ^ m - 1) := by
          have h := aluDist_from_zero m (finMax m)
          rwa [show (finMax m).val = 2 ^ m - 1 from rfl, popcount_pow2_sub_one] at h
        omega
      · simp only [hu, ↓reduceDIte]
        rw [hmsub]
        have h1 := ihm ⟨u.val - 2 ^ m, by have := u.isLt; omega⟩
        omega
  induction k with
  | zero => simp [aluDist]
  | succ k ih =>
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    have hpow1 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    have hpow2 : 2 ^ (k + 2) = 2 ^ (k + 1) + 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
    simp only [aluDist]
    by_cases hx : x.val < 2 ^ k <;> by_cases hy : y.val < 2 ^ k
    · simp only [hx, hy, ↓reduceDIte]
      have := ih ⟨x.val, hx⟩ ⟨y.val, hy⟩; omega
    · simp only [hx, hy, ↓reduceDIte]
      have h1 := htoMax k ⟨x.val, hx⟩
      have h2 := ih (finZero k) ⟨y.val - 2 ^ k, by have := y.isLt; omega⟩
      omega
    · simp only [hx, hy, ↓reduceDIte]
      have h1 := aluDist_to_zero k ⟨x.val - 2 ^ k, by have := x.isLt; omega⟩
      have hpop : popcount (x.val - 2 ^ k) ≤ k := by
        have := popcount_compl (by have := x.isLt; omega : x.val - 2 ^ k < 2 ^ k); omega
      have h2 := ih (finZero k) ⟨y.val, hy⟩
      dsimp only at h1
      omega
    · simp only [hx, hy, ↓reduceDIte]
      have := ih ⟨x.val - 2 ^ k, by have := x.isLt; omega⟩ ⟨y.val - 2 ^ k, by have := y.isLt; omega⟩; omega

/-- **THEOREM 3B (Exact Exponential Diameter & Linear Reverse Asymmetry of `A_k`, ∀ k):**
    - Exact diameter: `D_k(0, 2^k - 1) + k + 2 = 2^(k+1)` (attains `aluDist_le_diam`!)
    - Exact reverse cost: `D_k(2^k - 1, 0) = k`! -/
theorem alu_exact_diameter_and_asymmetry (k : Nat) :
    (∀ x y : Fin (2 ^ k), aluDist k x y + k + 2 ≤ 2 ^ (k + 1)) ∧
    aluDist k (finZero k) (finMax k) + k + 2 = 2 ^ (k + 1) ∧
    aluDist k (finMax k) (finZero k) = k := by
  refine ⟨aluDist_le_diam k, ?_, ?_⟩
  · have h : aluDist k (finZero k) (finMax k) + k = 2 * (2 ^ k - 1) := by
      have h0 := aluDist_from_zero k (finMax k)
      rwa [show (finMax k).val = 2 ^ k - 1 from rfl, popcount_pow2_sub_one] at h0
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    omega
  · rw [aluDist_to_zero]; simp [finMax, popcount_pow2_sub_one]

/-! ============================================================================
    SECTION 10: THEOREM 4 — NON-COLLAPSING ACTIVE SHERMAN-MORRISON ENGINE:
                BITWISE XOR-WALK KLEENE STAR & EXACT MAX-XOR BOTTLENECK ON `B_k`
    ============================================================================ -/

section ActiveXorEngine

open KleeneSemiring

theorem gaugeConj_entry {n : Nat} (g : Fin n → Nat) (M : Mat XorSet n) (i j : Fin n) (v : Nat) :
    gaugeConj g M i j v ↔ M i j (v ^^^ g i ^^^ g j) := by
  simp only [gaugeConj, XorSet.minkXor, XorSet.single]
  constructor
  · rintro ⟨a, b, rfl, hb, rfl⟩
    have hrew : (g i ^^^ g j) ^^^ b ^^^ g i ^^^ g j = b := by
      apply Nat.eq_of_testBit_eq; intro t; simp only [Nat.testBit_xor]
      cases (g i).testBit t <;> cases (g j).testBit t <;> cases b.testBit t <;> rfl
    rwa [hrew]
  · intro hv
    refine ⟨g i ^^^ g j, v ^^^ g i ^^^ g j, rfl, hv, ?_⟩
    apply Nat.eq_of_testBit_eq; intro t; simp only [Nat.testBit_xor]
    cases (g i).testBit t <;> cases (g j).testBit t <;> cases v.testBit t <;> rfl

theorem gaugeConj_invol {n : Nat} (g : Fin n → Nat) (M : Mat XorSet n) :
    gaugeConj g (gaugeConj g M) = M := by
  funext i j v
  apply propext
  rw [gaugeConj_entry, gaugeConj_entry]
  have hrew : v ^^^ g i ^^^ g j ^^^ g i ^^^ g j = v := by
    rw [Nat.xor_assoc (v ^^^ g i), Nat.xor_comm (g j) (g i),
        ← Nat.xor_assoc (v ^^^ g i) (g i) (g j), Nat.xor_assoc v (g i) (g i), Nat.xor_self, Nat.xor_zero,
        Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  rw [hrew]

theorem gaugeConj_id {n : Nat} (g : Fin n → Nat) :
    gaugeConj g (matId n : Mat XorSet n) = matId n := by
  funext i j v
  apply propext
  rw [gaugeConj_entry]
  by_cases h : i = j
  · subst h
    simp only [matId, ↓reduceIte, KleeneSemiring.one, XorSet.single, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  · simp [matId, h, KleeneSemiring.zero]

theorem gaugeConj_le_iff {n : Nat} (g : Fin n → Nat) (A B : Mat XorSet n) :
    matLe (gaugeConj g A) (gaugeConj g B) ↔ matLe A B := by
  have hle_iff : ∀ (X Y : XorSet), le X Y ↔ ∀ v, X v → Y v := fun X Y => by
    constructor
    · intro h v hv; have := congrFun h v; rw [← this]; exact Or.inl hv
    · intro h; funext v; apply propext; constructor
      · rintro (hx | hy); exact h v hx; exact hy
      · exact Or.inr
  constructor
  · intro h i j
    rw [hle_iff]; intro v hv
    have hij := (hle_iff _ _).mp (h i j) (v ^^^ g i ^^^ g j)
    rw [gaugeConj_entry, gaugeConj_entry] at hij
    have hrew : v ^^^ g i ^^^ g j ^^^ g i ^^^ g j = v := by
      rw [Nat.xor_assoc (v ^^^ g i), Nat.xor_comm (g j) (g i),
          ← Nat.xor_assoc (v ^^^ g i) (g i) (g j), Nat.xor_assoc v (g i) (g i), Nat.xor_self, Nat.xor_zero,
          Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    rw [hrew] at hij
    exact hij hv
  · intro h i j
    rw [hle_iff]; intro v hv
    rw [gaugeConj_entry] at hv ⊢
    exact (hle_iff _ _).mp (h i j) _ hv

theorem xorSet_finSum_iff {n : Nat} (f : Fin n → XorSet) (v : Nat) :
    finSum n f v ↔ ∃ k : Fin n, f k v := by
  induction n with
  | zero =>
    simp only [finSum, KleeneSemiring.zero]
    exact ⟨False.elim, fun ⟨k, _⟩ => Fin.elim0 k⟩
  | succ n ih =>
    simp only [finSum, KleeneSemiring.add, XorSet.union]
    rw [ih]
    constructor
    · rintro (⟨k, hk⟩ | hn)
      · exact ⟨⟨k.val, Nat.lt_succ_of_lt k.isLt⟩, hk⟩
      · exact ⟨⟨n, Nat.lt_succ_self n⟩, hn⟩
    · rintro ⟨k, hk⟩
      by_cases hkn : k.val < n
      · exact Or.inl ⟨⟨k.val, hkn⟩, hk⟩
      · have heq : k = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext (by have := k.isLt; dsimp; omega)
        rw [heq] at hk; exact Or.inr hk

theorem gaugeConj_mul {n : Nat} (g : Fin n → Nat) (A B : Mat XorSet n) :
    matMul (gaugeConj g A) (gaugeConj g B) = gaugeConj g (matMul A B) := by
  funext i j v
  apply propext
  rw [gaugeConj_entry]
  simp only [matMul, xorSet_finSum_iff, KleeneSemiring.mul, XorSet.minkXor]
  constructor
  · rintro ⟨k, a, b, ha, hb, rfl⟩
    rw [gaugeConj_entry] at ha hb
    refine ⟨k, a ^^^ g i ^^^ g k, b ^^^ g k ^^^ g j, ha, hb, ?_⟩
    -- (a ^ gi ^ gk) ^ (b ^ gk ^ gj) = (a ^ b) ^ gi ^ gj
    have h1 : (a ^^^ g i ^^^ g k) ^^^ (b ^^^ g k ^^^ g j) = (a ^^^ b) ^^^ g i ^^^ g j := by
      -- pure Nat.xor AC via testBit!
      apply Nat.eq_of_testBit_eq; intro t
      simp only [Nat.testBit_xor]
      cases a.testBit t <;> cases b.testBit t <;> cases (g i).testBit t <;>
        cases (g k).testBit t <;> cases (g j).testBit t <;> rfl
    exact h1
  · rintro ⟨k, a, b, ha, hb, heq⟩
    refine ⟨k, a ^^^ g i ^^^ g k, b ^^^ g k ^^^ g j, ?_, ?_, ?_⟩
    · rw [gaugeConj_entry]
      have hrew : a ^^^ g i ^^^ g k ^^^ g i ^^^ g k = a := by
        apply Nat.eq_of_testBit_eq; intro t; simp only [Nat.testBit_xor]
        cases a.testBit t <;> cases (g i).testBit t <;> cases (g k).testBit t <;> rfl
      rwa [hrew]
    · rw [gaugeConj_entry]
      have hrew : b ^^^ g k ^^^ g j ^^^ g k ^^^ g j = b := by
        apply Nat.eq_of_testBit_eq; intro t; simp only [Nat.testBit_xor]
        cases b.testBit t <;> cases (g k).testBit t <;> cases (g j).testBit t <;> rfl
      rwa [hrew]
    · apply Nat.eq_of_testBit_eq; intro t
      have ht := congrArg (fun z => z.testBit t) heq
      simp only [Nat.testBit_xor] at ht ⊢
      cases ha_t : a.testBit t <;> cases hb_t : b.testBit t <;> cases hv_t : v.testBit t <;>
        cases hgi_t : (g i).testBit t <;> cases hgk_t : (g k).testBit t <;> cases hgj_t : (g j).testBit t <;>
        simp [ha_t, hb_t, hv_t, hgi_t, hgj_t] at ht ⊢

/-- **Gauge Similarity Theorem:** Diagonal XOR gauge conjugation preserves `IsMatStar`! -/
theorem gaugeConj_star {n : Nat} (g : Fin n → Nat) {M U : Mat XorSet n}
    (hU : IsMatStar M U) : IsMatStar (gaugeConj g M) (gaugeConj g U) := by
  constructor
  · rw [← gaugeConj_id g, gaugeConj_le_iff]; exact hU.one_le
  · rw [gaugeConj_mul, gaugeConj_le_iff]; exact hU.mul_left
  · rw [gaugeConj_mul, gaugeConj_le_iff]; exact hU.mul_right
  · intro B X hBX hMX
    rw [← gaugeConj_invol g B] at hBX ⊢
    rw [← gaugeConj_invol g X] at hBX hMX ⊢
    rw [gaugeConj_le_iff] at hBX
    rw [gaugeConj_mul, gaugeConj_le_iff] at hMX
    rw [gaugeConj_mul, gaugeConj_le_iff]
    exact hU.ind_left _ _ hBX hMX
  · intro B X hBX hXM
    rw [← gaugeConj_invol g B] at hBX ⊢
    rw [← gaugeConj_invol g X] at hBX hXM ⊢
    rw [gaugeConj_le_iff] at hBX
    rw [gaugeConj_mul, gaugeConj_le_iff] at hXM
    rw [gaugeConj_mul, gaugeConj_le_iff]
    exact hU.ind_right _ _ hBX hXM

/-- **Bitwise Faithfulness for `bmiXorMat`:**
    `bmiXorMat k = bmiXorBitwiseMat k` for ALL `k : Nat`! -/
theorem bmiXorMat_eq_bitwise (k : Nat) : bmiXorMat k = bmiXorBitwiseMat k := by
  induction k with
  | zero =>
    funext x y v
    simp [bmiXorMat, bmiXorBitwiseMat, bmiBoolMat, BitDoublingCollapseSpec.mat, matZero, KleeneSemiring.zero]
  | succ k ih =>
    funext x y
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    have hL_def : bmiXorMat (k + 1) x y =
        blockMat (bmiXorBitwiseMat k)
                 (matSingle (finMax k) (finMax k) (XorSet.single (2 ^ k - 1)))
                 (matSingle (finZero k) (finZero k) (XorSet.single 0))
                 (gaugeConj (parGauge k) (bmiXorBitwiseMat k)) x y := by
      unfold bmiXorMat; rw [ih]
    have hR_def : bmiXorBitwiseMat (k + 1) x y =
        (if blockMat (bmiBoolMat k) (matSingle (finMax k) (finMax k) true)
                     (matSingle (finZero k) (finZero k) true) (bmiBoolMat k) x y
         then XorSet.single (x.val &&& y.val) else fun _ => False) := rfl
    rw [hL_def, hR_def]
    simp only [blockMat, matSingle, finMax, finZero, bmiXorBitwiseMat, KleeneSemiring.zero]
    by_cases hx : x.val < 2 ^ k <;> by_cases hy : y.val < 2 ^ k
    · simp only [hx, hy, ↓reduceDIte]
    · simp only [hx, hy, ↓reduceDIte, Fin.mk.injEq]
      by_cases hEq : x.val = 2 ^ k - 1 ∧ y.val - 2 ^ k = 2 ^ k - 1
      · have hyeq : y.val = 2 ^ k + (2 ^ k - 1) := by omega
        have hand : x.val &&& y.val = 2 ^ k - 1 := by
          rw [hEq.1, hyeq]
          apply Nat.eq_of_testBit_eq; intro j
          simp only [Nat.testBit_and, testBit_add_pow2 (by omega : 2 ^ k - 1 < 2 ^ k)]
          by_cases hkj : k = j
          · subst hkj; simp [Nat.testBit_lt_two_pow (by omega : 2 ^ k - 1 < 2 ^ k)]
          · simp [hkj]
        simp [hEq]
        rw [← hEq.1, hand, hEq.1]
      · simp only [hEq, ↓reduceIte, Bool.false_eq_true]
    · simp only [hx, hy, ↓reduceDIte, Fin.mk.injEq]
      by_cases hEq : x.val - 2 ^ k = 0 ∧ y.val = 0
      · simp [hEq]
      · simp only [hEq, ↓reduceIte, Bool.false_eq_true]
    · simp only [hx, hy, ↓reduceDIte]
      let x' : Fin (2 ^ k) := ⟨x.val - 2 ^ k, by have := x.isLt; omega⟩
      let y' : Fin (2 ^ k) := ⟨y.val - 2 ^ k, by have := y.isLt; omega⟩
      have hxeq : x.val = 2 ^ k + x'.val := by dsimp [x']; omega
      have hyeq : y.val = 2 ^ k + y'.val := by dsimp [y']; omega
      funext v; apply propext
      change gaugeConj (parGauge k) (bmiXorBitwiseMat k) x' y' v ↔
             (if bmiBoolMat k x' y' = true then XorSet.single (x.val &&& y.val) else fun _ => False) v
      rw [gaugeConj_entry]
      dsimp only [bmiXorBitwiseMat]
      by_cases hedge : bmiBoolMat k x' y' = true
      · simp only [hedge, ↓reduceIte, XorSet.single]
        have hpar := bmiBoolMat_parity k x' y' hedge
        have hgx : parGauge k x' ^^^ parGauge k y' = 2 ^ k := by
          unfold parGauge
          by_cases hp : popcount x'.val % 2 = 1
          · have hp2 : ¬ (popcount y'.val % 2 = 1) := by omega
            simp [hp, hp2]
          · have hp2 : popcount y'.val % 2 = 1 := by omega
            simp [hp, hp2]
        have hand : x.val &&& y.val = (parGauge k x' ^^^ parGauge k y') ^^^ (x'.val &&& y'.val) := by
          rw [hgx, hxeq, hyeq]
          apply Nat.eq_of_testBit_eq; intro j
          simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow,
                     testBit_add_pow2 x'.isLt, testBit_add_pow2 y'.isLt]
          by_cases hkj : k = j
          · subst hkj
            simp [Nat.testBit_lt_two_pow x'.isLt, Nat.testBit_lt_two_pow y'.isLt]
          · simp [hkj]
        constructor
        · intro hv
          rw [hand]
          apply Nat.eq_of_testBit_eq; intro t
          have ht := congrArg (fun z => z.testBit t) hv
          simp only [Nat.testBit_xor] at ht ⊢
          cases hv_t : v.testBit t <;> cases h1_t : (parGauge k x').testBit t <;>
            cases h2_t : (parGauge k y').testBit t <;> cases h3_t : (x'.val &&& y'.val).testBit t <;>
            simp [hv_t, h1_t, h2_t, h3_t] at ht ⊢
        · intro hv
          rw [hv, hand]
          apply Nat.eq_of_testBit_eq; intro t
          simp only [Nat.testBit_xor]
          cases (parGauge k x').testBit t <;> cases (parGauge k y').testBit t <;>
            cases (x'.val &&& y'.val).testBit t <;> rfl
      · simp [hedge]

theorem inVk_zero (k : Nat) : inVk k 0 := by
  refine ⟨Nat.two_pow_pos k, fun _ _ => by simp, fun _ => Nat.zero_testBit _⟩

theorem inVk_xor {k a b : Nat} (ha : inVk k a) (hb : inVk k b) : inVk k (a ^^^ b) := by
  refine ⟨Nat.xor_lt_two_pow ha.1 hb.1, ?_, ?_⟩
  · intro j hj; simp only [Nat.testBit_xor, ha.2.1 j hj, hb.2.1 j hj]
  · intro hodd; simp only [Nat.testBit_xor, ha.2.2 hodd, hb.2.2 hodd]; rfl

theorem phiBit_lt (k x : Nat) : phiBit k x < 2 ^ k := by
  induction k generalizing x with
  | zero => exact Nat.two_pow_pos 0
  | succ k ih =>
    simp only [phiBit]
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    have h1 : phiBit k (x % 2 ^ k) < 2 ^ (k + 1) := Nat.lt_trans (ih _) (by omega)
    split
    · exact Nat.xor_lt_two_pow h1 (by omega)
    · rw [Nat.xor_zero]; exact h1

theorem phiBit_lo {k x : Nat} (hx : x < 2 ^ k) : phiBit (k + 1) x = phiBit k x := by
  simp [phiBit, Nat.mod_eq_of_lt hx, Nat.testBit_lt_two_pow hx]

theorem phiBit_hi {k x : Nat} (hx : x < 2 ^ k) :
    phiBit (k + 1) (2 ^ k + x) = phiBit k x ^^^ parGauge k ⟨x, hx⟩ := by
  have hmod : (2 ^ k + x) % 2 ^ k = x := by
    have h1 : 2 ^ k + x = x + 1 * 2 ^ k := by omega
    rw [h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
  have htb : (2 ^ k + x).testBit k = true := by
    rw [testBit_add_pow2 hx]; simp
  simp only [phiBit, hmod, htb, Bool.true_and, parGauge]
  by_cases hp : popcount x % 2 = 1
  · simp [hp]
  · simp [hp]

theorem phiBit_zero (k : Nat) : phiBit k 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [phiBit_lo (Nat.two_pow_pos k), ih]

/-- Key algebraic lemma: `2^k - 1` modulo `V_k` is `0` when `k` is even, and `2^(k-1)` when `k` is odd! -/
theorem mask_mod_Vk (k : Nat) :
    inVk k ((2 ^ k - 1) ^^^ (if k % 2 = 1 then 2 ^ (k - 1) else 0)) := by
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hlt_rhs : (if k % 2 = 1 then 2 ^ (k - 1) else 0) < 2 ^ k := by
    split
    · exact Nat.pow_lt_pow_right (by omega) (by omega)
    · exact hpos
  refine ⟨Nat.xor_lt_two_pow (by omega) hlt_rhs, ?_, ?_⟩
  · intro j hj
    have h2j : 2 * j < k := by omega
    have h2j1 : 2 * j + 1 < k := by omega
    have tb1 : (2 ^ k - 1).testBit (2 * j) = true := by
      have := testBit_compl (k := k) (x := 0) hpos h2j; simpa using this
    have tb2 : (2 ^ k - 1).testBit (2 * j + 1) = true := by
      have := testBit_compl (k := k) (x := 0) hpos h2j1; simpa using this
    simp only [Nat.testBit_xor, tb1, tb2]
    split
    · rename_i hodd
      have hne1 : k - 1 ≠ 2 * j := by omega
      have hne2 : k - 1 ≠ 2 * j + 1 := by omega
      simp [hne1, hne2]
    · simp
  · intro hodd
    have hlt1 : k - 1 < k := by omega
    have tb : (2 ^ k - 1).testBit (k - 1) = true := by
      have := testBit_compl (k := k) (x := 0) hpos hlt1; simpa using this
    simp [Nat.testBit_xor, hodd, tb]

/-- Key generator lemma: `inVk k v → inVk (k + 1) v`, and for odd `k`, `3 * 2^(k-1) ∈ V_{k+1}`! -/
theorem inVk_lift {k v : Nat} (hv : inVk k v) : inVk (k + 1) v := by
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
  have hvlt := hv.1
  refine ⟨by omega, ?_, ?_⟩
  · intro j hj
    by_cases hjk : j < k / 2
    · exact hv.2.1 j hjk
    · have hodd : k % 2 = 1 := by omega
      have h2j : 2 * j = k - 1 := by omega
      have h2j1 : 2 * j + 1 = k := by omega
      rw [h2j1, h2j, hv.2.2 hodd, Nat.testBit_lt_two_pow hv.1]
  · intro hodd1
    have hkeq : k + 1 - 1 = k := by omega
    rw [hkeq]; exact Nat.testBit_lt_two_pow hv.1

theorem inVk_new_gen {k : Nat} (hodd : k % 2 = 1) :
    inVk (k + 1) (2 ^ k ^^^ 2 ^ (k - 1)) := by
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
  have hlt1 : 2 ^ (k - 1) < 2 ^ k := Nat.pow_lt_pow_right (by omega) (by omega)
  refine ⟨Nat.xor_lt_two_pow (by omega) (by omega), ?_, ?_⟩
  · intro j hj
    simp only [Nat.testBit_xor, Nat.testBit_two_pow]
    by_cases htop : 2 * j + 1 = k
    · have h2j : 2 * j = k - 1 := by omega
      have hne1 : k ≠ k - 1 := by omega
      have hne2 : k - 1 ≠ k := by omega
      rw [htop, h2j]; simp [hne1, hne2]
    · have hne1 : k ≠ 2 * j := by omega
      have hne2 : k ≠ 2 * j + 1 := by omega
      have hne3 : k - 1 ≠ 2 * j := by omega
      have hne4 : k - 1 ≠ 2 * j + 1 := by omega
      simp [hne1, hne2, hne3, hne4]
  · intro hcontra; omega

/-- Helper: `inVk (k + 1) v` iff either `inVk k v` OR (`k % 2 = 1` and `inVk k (v ^^^ 2^k ^^^ 2^(k-1))`)! -/
theorem inVk_succ_iff (k v : Nat) :
    inVk (k + 1) v ↔
      inVk k v ∨ (k % 2 = 1 ∧ inVk k (v ^^^ (2 ^ k ^^^ 2 ^ (k - 1)))) := by
  constructor
  · intro hv
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    by_cases hbit : v.testBit k = false
    · left
      have hvlt : v < 2 ^ k := Nat.lt_of_not_le (fun hge => by
        have h1 : v / 2 ^ k = 1 := Nat.div_eq_of_lt_le (by omega) (by have := hv.1; omega)
        rw [Nat.testBit_eq_decide_div_mod_eq, h1] at hbit
        cases hbit)
      refine ⟨hvlt, fun j hj => hv.2.1 j (by omega), fun hodd => ?_⟩
      have hj : (k - 1) / 2 < (k + 1) / 2 := by omega
      have hpair := hv.2.1 ((k - 1) / 2) hj
      have h1 : 2 * ((k - 1) / 2) = k - 1 := by omega
      have h2 : 2 * ((k - 1) / 2) + 1 = k := by omega
      rw [h2, h1, hbit] at hpair
      exact hpair
    · have hbit_t : v.testBit k = true := by cases h : v.testBit k <;> simp_all
      have hodd : k % 2 = 1 := by
        cases hmod : k % 2 with
        | zero =>
          have hodd1 : (k + 1) % 2 = 1 := by omega
          have hf := hv.2.2 hodd1
          have hkeq : k + 1 - 1 = k := by omega
          rw [hkeq, hbit_t] at hf
          cases hf
        | succ m => omega
      right
      refine ⟨hodd, ?_⟩
      have hgen := inVk_new_gen hodd
      have hw := inVk_xor hv hgen
      have hw_bit : (v ^^^ (2 ^ k ^^^ 2 ^ (k - 1))).testBit k = false := by
        simp only [Nat.testBit_xor, Nat.testBit_two_pow, hbit_t]
        have hne : k - 1 ≠ k := by omega
        simp [hne]
      have hw_lt : v ^^^ (2 ^ k ^^^ 2 ^ (k - 1)) < 2 ^ k := Nat.lt_of_not_le (fun hge => by
        have h1 : (v ^^^ (2 ^ k ^^^ 2 ^ (k - 1))) / 2 ^ k = 1 := Nat.div_eq_of_lt_le (by omega) (by have := hw.1; omega)
        rw [Nat.testBit_eq_decide_div_mod_eq, h1] at hw_bit
        cases hw_bit)
      refine ⟨hw_lt, fun j hj => hw.2.1 j (by omega), fun _ => ?_⟩
      have hj : (k - 1) / 2 < (k + 1) / 2 := by omega
      have hpair := hw.2.1 ((k - 1) / 2) hj
      have h1 : 2 * ((k - 1) / 2) = k - 1 := by omega
      have h2 : 2 * ((k - 1) / 2) + 1 = k := by omega
      rw [h2, h1, hw_bit] at hpair
      exact hpair
  · rintro (hv | ⟨hodd, hv⟩)
    · exact inVk_lift hv
    · have h1 := inVk_xor (inVk_lift hv) (inVk_new_gen hodd)
      rwa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at h1

/-- Key bridge lemma: `phiBit k (2^k - 1) ^^^ (2^k - 1)` — actually we ONLY need
    `inVk (k + 1) ((2^k - 1) ^^^ parGauge k (finMax k))`!
    CHECK THAT!!
    - `popcount (2^k - 1) = k`, so `parGauge k (finMax k) = if k % 2 = 1 then 2^k else 0`!
    - When `k` is EVEN: `(2^k - 1) ^^^ 0 ∈ V_k ⊆ V_{k+1}`!
    - When `k` is ODD: `(2^k - 1) ^^^ 2^k = ((2^k - 1) ^^^ 2^(k-1)) ^^^ (2^k ^^^ 2^(k-1)) ∈ V_k ⊕ (3·2^(k-1)) ⊆ V_{k+1}`!!
    **IT IS IN `V_{k+1}` FOR EVERY `k` — BOTH EVEN AND ODD!!** -/
theorem bridge_in_Vk_succ (k : Nat) :
    inVk (k + 1) ((2 ^ k - 1) ^^^ parGauge k (finMax k)) := by
  have hmask := mask_mod_Vk k
  have hpg : parGauge k (finMax k) = if k % 2 = 1 then 2 ^ k else 0 := by
    simp [parGauge, finMax, popcount_pow2_sub_one]
  rw [hpg]
  by_cases hodd : k % 2 = 1
  · simp only [hodd, ↓reduceIte] at hmask ⊢
    have h1 := inVk_xor (inVk_lift hmask) (inVk_new_gen hodd)
    have hrew : ((2 ^ k - 1) ^^^ 2 ^ (k - 1)) ^^^ (2 ^ k ^^^ 2 ^ (k - 1)) = (2 ^ k - 1) ^^^ 2 ^ k := by
      apply Nat.eq_of_testBit_eq; intro t; simp only [Nat.testBit_xor]
      cases (2 ^ k - 1).testBit t <;> cases (2 ^ (k - 1)).testBit t <;> cases (2 ^ k).testBit t <;> rfl
    rwa [hrew] at h1
  · simp only [hodd, ↓reduceIte, Nat.xor_zero] at hmask ⊢
    exact inVk_lift hmask

/-- **THEOREM 4A (Non-Collapsing Active-Schur XOR-Walk Kleene Star of `B_k`, ∀ k : ℕ):**
    Using Engine Theorem C1 (`cornerBridge_star` — ACTIVE Kleene Sherman-Morrison!),
    for EVERY bit-width `k : Nat`, the exact `XorSet` Kleene star of the bitwise-AND
    weighted BMI1 graph `bmiXorBitwiseMat k` is `bmiXorStar k`:
    `(B_k^{XOR,*})_{x, y} = { v | (v ^^^ phiBit k x ^^^ phiBit k y) ∈ V_k }`! -/
theorem bmi_xor_star_exact (k : Nat) :
    IsMatStar (bmiXorBitwiseMat k) (bmiXorStar k) := by
  rw [← bmiXorMat_eq_bitwise]
  induction k with
  | zero =>
    have heq : bmiXorStar 0 = matId 1 := by
      funext x y v
      have hx : x.val = 0 := by have := x.isLt; omega
      have hy : y.val = 0 := by have := y.isLt; omega
      have hxy : x = y := Fin.ext (by omega)
      subst hxy
      apply propext
      simp only [bmiXorStar, phiBit, Nat.xor_zero, matId, ↓reduceIte, KleeneSemiring.one, XorSet.single, inVk]
      constructor
      · rintro ⟨hv, _, _⟩; omega
      · rintro rfl; exact ⟨by decide, fun _ h => by omega, fun h => by omega⟩
    rw [heq]; exact matZero_one_star
  | succ k ih =>
    -- Step 1: Apply Engine Theorem C1 (ACTIVE cornerBridge_star) with hU = ih and hV = gaugeConj_star ih!
    let U := bmiXorStar k
    let V := gaugeConj (parGauge k) U
    have hV : IsMatStar (gaugeConj (parGauge k) (bmiXorMat k)) V := gaugeConj_star (parGauge k) ih
    have hGen := cornerBridge_star ih hV (finMax k) (finMax k) (finZero k) (finZero k)
                   (XorSet.single (2 ^ k - 1)) (XorSet.single 0)
    -- Step 2: Compute the active Schur scalar `c = {2^k - 1} · V_{m, 0} · {0}` and `U_{0, m} · c`!
    let c : XorSet := mul (mul (XorSet.single (2 ^ k - 1)) (V (finMax k) (finZero k))) (XorSet.single 0)
    -- Characterize `c v`: `inVk k (v ^^^ (2^k - 1) ^^^ parGauge k (finMax k) ^^^ phiBit k (2^k - 1))`!
    have hc_iff : ∀ v, c v ↔
        inVk k (v ^^^ (2 ^ k - 1) ^^^ parGauge k (finMax k) ^^^ phiBit k (finMax k).val) := by
      intro v
      dsimp only [c, V, U]
      change XorSet.minkXor (XorSet.minkXor (XorSet.single (2 ^ k - 1))
               (gaugeConj (parGauge k) (bmiXorStar k) (finMax k) (finZero k))) (XorSet.single 0) v ↔ _
      rw [XorSet.minkXor_single_zero]
      simp only [XorSet.minkXor, XorSet.single, gaugeConj_entry, bmiXorStar]
      have hpg0 : parGauge k (finZero k) = 0 := by simp [parGauge, finZero, popcount_zero]
      have hpb0 : phiBit k (finZero k).val = 0 := phiBit_zero k
      simp only [hpg0, hpb0, Nat.xor_zero]
      constructor
      · rintro ⟨a, b, rfl, hb, rfl⟩
        have hrew : ((2 ^ k - 1) ^^^ b) ^^^ (2 ^ k - 1) ^^^ parGauge k (finMax k) ^^^ phiBit k (finMax k).val =
                    b ^^^ parGauge k (finMax k) ^^^ phiBit k (finMax k).val := by
          apply Nat.eq_of_testBit_eq; intro t; simp only [Nat.testBit_xor]
          cases (2 ^ k - 1).testBit t <;> cases b.testBit t <;>
            cases (parGauge k (finMax k)).testBit t <;> cases (phiBit k (finMax k).val).testBit t <;> rfl
        rwa [hrew]
      · intro hv
        refine ⟨2 ^ k - 1, (2 ^ k - 1) ^^^ v, rfl, ?_, ?_⟩
        · have hrew : ((2 ^ k - 1) ^^^ v) ^^^ parGauge k (finMax k) ^^^ phiBit k (finMax k).val =
                      v ^^^ (2 ^ k - 1) ^^^ parGauge k (finMax k) ^^^ phiBit k (finMax k).val := by
            apply Nat.eq_of_testBit_eq; intro t; simp only [Nat.testBit_xor]
            cases (2 ^ k - 1).testBit t <;> cases v.testBit t <;>
              cases (parGauge k (finMax k)).testBit t <;> cases (phiBit k (finMax k).val).testBit t <;> rfl
          rwa [hrew]
        · rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
    let loop : XorSet := mul (U (finZero k) (finMax k)) c
    have hpb0 : phiBit k (finZero k).val = 0 := phiBit_zero k
    have hloop_iff : ∀ v, loop v ↔ inVk k (v ^^^ (2 ^ k - 1) ^^^ parGauge k (finMax k)) := by
      intro v
      simp only [loop, KleeneSemiring.mul, XorSet.minkXor, U, bmiXorStar, hpb0, Nat.xor_zero]
      constructor
      · rintro ⟨a, b, ha, hb, rfl⟩
        rw [hc_iff] at hb
        have hxor := inVk_xor ha hb
        have hrew : (a ^^^ phiBit k (finMax k).val) ^^^ (b ^^^ (2 ^ k - 1) ^^^ parGauge k (finMax k) ^^^ phiBit k (finMax k).val) =
                    (a ^^^ b) ^^^ (2 ^ k - 1) ^^^ parGauge k (finMax k) := by
          apply Nat.eq_of_testBit_eq; intro t; simp only [Nat.testBit_xor]
          cases a.testBit t <;> cases b.testBit t <;> cases (phiBit k (finMax k).val).testBit t <;>
            cases (2 ^ k - 1).testBit t <;> cases (parGauge k (finMax k)).testBit t <;> rfl
        rwa [hrew] at hxor
      · intro hv
        refine ⟨phiBit k (finMax k).val, v ^^^ phiBit k (finMax k).val, ?_, ?_, ?_⟩
        · rw [Nat.xor_self]; exact inVk_zero k
        · rw [hc_iff]
          have hrew : (v ^^^ phiBit k (finMax k).val) ^^^ (2 ^ k - 1) ^^^ parGauge k (finMax k) ^^^ phiBit k (finMax k).val =
                      v ^^^ (2 ^ k - 1) ^^^ parGauge k (finMax k) := by
            apply Nat.eq_of_testBit_eq; intro t; simp only [Nat.testBit_xor]
            cases v.testBit t <;> cases (phiBit k (finMax k).val).testBit t <;>
              cases (2 ^ k - 1).testBit t <;> cases (parGauge k (finMax k)).testBit t <;> rfl
          rwa [hrew]
        · rw [Nat.xor_comm (phiBit k (finMax k).val), Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    -- Step 4: The ACTIVE Sherman-Morrison Kleene Star `star loop = XorSet.Span loop` equals `inVk (k + 1)`!
    have hstar_loop : ∀ v, XorSet.Span loop v ↔ inVk (k + 1) v := by
      intro v
      constructor
      · intro hs
        induction hs with
        | zero => exact inVk_zero (k + 1)
        | @step a b ha _ ihb =>
          rw [hloop_iff] at ha
          have h1 := inVk_xor (inVk_lift ha) (bridge_in_Vk_succ k)
          have hrew : (a ^^^ (2 ^ k - 1) ^^^ parGauge k (finMax k)) ^^^ ((2 ^ k - 1) ^^^ parGauge k (finMax k)) = a := by
            apply Nat.eq_of_testBit_eq; intro t; simp only [Nat.testBit_xor]
            cases a.testBit t <;> cases (2 ^ k - 1).testBit t <;> cases (parGauge k (finMax k)).testBit t <;> rfl
          rw [hrew] at h1
          exact inVk_xor h1 ihb
      · intro hv
        rw [inVk_succ_iff] at hv
        rcases hv with hvk | ⟨hodd, hvk⟩
        · -- Even/unchanged part: v ∈ V_k. Since `g0 = (2^k-1) ^^^ parGauge k m` is in `loop`,
          -- `v = (v ^^^ g0) ^^^ g0` (two steps in Span loop!)
          have hg0 : loop ((2 ^ k - 1) ^^^ parGauge k (finMax k)) := by
            rw [hloop_iff]
            have hrew : ((2 ^ k - 1) ^^^ parGauge k (finMax k)) ^^^ (2 ^ k - 1) ^^^ parGauge k (finMax k) = 0 := by
              apply Nat.eq_of_testBit_eq; intro t; simp only [Nat.testBit_xor, Nat.zero_testBit]
              cases (2 ^ k - 1).testBit t <;> cases (parGauge k (finMax k)).testBit t <;> rfl
            rw [hrew]; exact inVk_zero k
          have hvg0 : loop (v ^^^ ((2 ^ k - 1) ^^^ parGauge k (finMax k))) := by
            rw [hloop_iff]
            have hrew : (v ^^^ ((2 ^ k - 1) ^^^ parGauge k (finMax k))) ^^^ (2 ^ k - 1) ^^^ parGauge k (finMax k) = v := by
              apply Nat.eq_of_testBit_eq; intro t; simp only [Nat.testBit_xor]
              cases v.testBit t <;> cases (2 ^ k - 1).testBit t <;> cases (parGauge k (finMax k)).testBit t <;> rfl
            rwa [hrew]
          have h2 := XorSet.Span.step hvg0 (XorSet.Span.step hg0 XorSet.Span.zero)
          have hrew : (v ^^^ ((2 ^ k - 1) ^^^ parGauge k (finMax k))) ^^^ (((2 ^ k - 1) ^^^ parGauge k (finMax k)) ^^^ 0) = v := by
            apply Nat.eq_of_testBit_eq; intro t; simp only [Nat.testBit_xor, Nat.zero_testBit]
            cases v.testBit t <;> cases (2 ^ k - 1).testBit t <;> cases (parGauge k (finMax k)).testBit t <;> rfl
          rwa [hrew] at h2
        · -- Odd k NEW GENERATOR branch: v ∈ (2^k ^^^ 2^(k-1)) ⊕ V_k ⊆ loop!
          have hvloop : loop v := by
            rw [hloop_iff]
            have hmask := mask_mod_Vk k
            simp only [hodd, ↓reduceIte] at hmask
            have hpg : parGauge k (finMax k) = 2 ^ k := by
              simp [parGauge, finMax, popcount_pow2_sub_one, hodd]
            rw [hpg]
            have hxor := inVk_xor hvk hmask
            have hrew : (v ^^^ (2 ^ k ^^^ 2 ^ (k - 1))) ^^^ ((2 ^ k - 1) ^^^ 2 ^ (k - 1)) =
                        v ^^^ (2 ^ k - 1) ^^^ 2 ^ k := by
              apply Nat.eq_of_testBit_eq; intro t; simp only [Nat.testBit_xor]
              cases v.testBit t <;> cases (2 ^ k).testBit t <;>
                cases (2 ^ (k - 1)).testBit t <;> cases (2 ^ k - 1).testBit t <;> rfl
            rwa [hrew] at hxor
          have h1 := XorSet.Span.step hvloop XorSet.Span.zero
          rwa [Nat.xor_zero] at h1
    -- Step 5: Show `smUpdate U (finMax k) (finZero k) c i j v ↔ inVk (k + 1) (v ^^^ phiBit k i ^^^ phiBit k j)`!
    let S := smUpdate U (finMax k) (finZero k) c
    have hS_iff : ∀ (i j : Fin (2 ^ k)) (v : Nat),
        S i j v ↔ inVk (k + 1) (v ^^^ phiBit k i.val ^^^ phiBit k j.val) := by
      intro i j v
      simp only [S, smUpdate, KleeneSemiring.add, XorSet.union, KleeneSemiring.mul, XorSet.minkXor,
                 KleeneSemiring.star]
      constructor
      · rintro (hu | ⟨ab, d, ⟨a, b, ⟨u1, c1, hu1, hc1, rfl⟩, hb, rfl⟩, hd, rfl⟩)
        · exact inVk_lift hu
        · rw [hc_iff] at hc1
          change XorSet.Span loop b at hb
          rw [hstar_loop] at hb
          have hu1' : inVk (k + 1) (u1 ^^^ phiBit k i.val ^^^ phiBit k (finMax k).val) := inVk_lift hu1
          have hc1' : inVk (k + 1) (c1 ^^^ (2 ^ k - 1) ^^^ parGauge k (finMax k) ^^^ phiBit k (finMax k).val) := inVk_lift hc1
          have hd' : inVk (k + 1) (d ^^^ phiBit k j.val) := by
            have := inVk_lift hd; simpa [U, bmiXorStar, hpb0, Nat.xor_zero] using this
          have hbr := bridge_in_Vk_succ k
          have hall := inVk_xor (inVk_xor (inVk_xor hu1' hc1') (inVk_xor hb hd')) hbr
          have hrew : (((u1 ^^^ phiBit k i.val ^^^ phiBit k (finMax k).val) ^^^
                        (c1 ^^^ (2 ^ k - 1) ^^^ parGauge k (finMax k) ^^^ phiBit k (finMax k).val)) ^^^
                       (b ^^^ (d ^^^ phiBit k j.val))) ^^^
                      ((2 ^ k - 1) ^^^ parGauge k (finMax k)) =
                      (((u1 ^^^ c1) ^^^ b) ^^^ d) ^^^ phiBit k i.val ^^^ phiBit k j.val := by
            apply Nat.eq_of_testBit_eq; intro t; simp only [Nat.testBit_xor]
            cases u1.testBit t <;> cases c1.testBit t <;> cases b.testBit t <;> cases d.testBit t <;>
              cases (phiBit k i.val).testBit t <;> cases (phiBit k j.val).testBit t <;>
              cases (phiBit k (finMax k).val).testBit t <;>
              cases (2 ^ k - 1).testBit t <;> cases (parGauge k (finMax k)).testBit t <;> rfl
          rwa [hrew] at hall
      · intro hv
        right
        -- Witness: u1 = phiBit k i ^^^ phiBit k m (in U i m), c1 = (2^k-1) ^^^ parGauge k m ^^^ phiBit k m (in c),
        -- d = phiBit k j (in U 0 j), and b = v ^^^ phiBit k i ^^^ phiBit k j ^^^ ((2^k-1) ^^^ parGauge k m) (in V_{k+1} = Span loop)!
        let u1 := phiBit k i.val ^^^ phiBit k (finMax k).val
        let c1 := (2 ^ k - 1) ^^^ parGauge k (finMax k) ^^^ phiBit k (finMax k).val
        let b  := (v ^^^ phiBit k i.val ^^^ phiBit k j.val) ^^^ ((2 ^ k - 1) ^^^ parGauge k (finMax k))
        let d  := phiBit k j.val
        refine ⟨(u1 ^^^ c1) ^^^ b, d, ⟨u1 ^^^ c1, b, ⟨u1, c1, ?_, ?_, rfl⟩, ?_, rfl⟩, ?_, ?_⟩
        · change inVk k (u1 ^^^ phiBit k i.val ^^^ phiBit k (finMax k).val)
          have : u1 ^^^ phiBit k i.val ^^^ phiBit k (finMax k).val = 0 := by
            apply Nat.eq_of_testBit_eq; intro t; simp only [u1, Nat.testBit_xor, Nat.zero_testBit]
            cases (phiBit k i.val).testBit t <;> cases (phiBit k (finMax k).val).testBit t <;> rfl
          rw [this]; exact inVk_zero k
        · rw [hc_iff]
          have : c1 ^^^ (2 ^ k - 1) ^^^ parGauge k (finMax k) ^^^ phiBit k (finMax k).val = 0 := by
            apply Nat.eq_of_testBit_eq; intro t; simp only [c1, Nat.testBit_xor, Nat.zero_testBit]
            cases (2 ^ k - 1).testBit t <;> cases (parGauge k (finMax k)).testBit t <;>
              cases (phiBit k (finMax k).val).testBit t <;> rfl
          rw [this]; exact inVk_zero k
        · change XorSet.Span loop b; rw [hstar_loop]; exact inVk_xor hv (bridge_in_Vk_succ k)
        · change inVk k (d ^^^ phiBit k (finZero k).val ^^^ phiBit k j.val)
          rw [hpb0, Nat.xor_zero]; dsimp only [d]; rw [Nat.xor_self]; exact inVk_zero k
        · apply Nat.eq_of_testBit_eq; intro t; simp only [u1, c1, b, d, Nat.testBit_xor]
          cases v.testBit t <;> cases (phiBit k i.val).testBit t <;> cases (phiBit k j.val).testBit t <;>
            cases (phiBit k (finMax k).val).testBit t <;>
            cases (2 ^ k - 1).testBit t <;> cases (parGauge k (finMax k)).testBit t <;> rfl
    -- Step 6: Show all 4 blocks of `hGen` equal `bmiXorStar (k + 1)`!
    have hEqMat :
        blockMat S
          (fun i j => mul (mul (S i (finMax k)) (XorSet.single (2 ^ k - 1))) (V (finMax k) j))
          (fun i j => mul (mul (V i (finZero k)) (XorSet.single 0)) (S (finZero k) j))
          (fun i j => add (V i j) (mul (mul (mul (mul (V i (finZero k)) (XorSet.single 0))
            (S (finZero k) (finMax k))) (XorSet.single (2 ^ k - 1))) (V (finMax k) j))) =
        bmiXorStar (k + 1) := by
      have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
      funext x y v; apply propext
      simp only [blockMat, bmiXorStar]
      by_cases hx : x.val < 2 ^ k <;> by_cases hy : y.val < 2 ^ k
      · -- TL: (0, x') → (0, y')
        simp only [hx, hy, ↓reduceDIte]
        rw [hS_iff, phiBit_lo hx, phiBit_lo hy]
      · -- TR: (0, x') → (1, y')
        simp only [hx, hy, ↓reduceDIte]
        let x' : Fin (2 ^ k) := ⟨x.val, hx⟩
        let y' : Fin (2 ^ k) := ⟨y.val - 2 ^ k, by have := y.isLt; omega⟩
        have hyeq : y.val = 2 ^ k + y'.val := by dsimp [y']; omega
        have hpy : phiBit (k + 1) y.val = phiBit k y'.val ^^^ parGauge k y' := by
          rw [hyeq]; exact phiBit_hi y'.isLt
        rw [phiBit_lo hx, hpy]
        simp only [KleeneSemiring.mul, XorSet.minkXor, XorSet.single, V, gaugeConj_entry, U, bmiXorStar]
        constructor
        · rintro ⟨sm, vj, ⟨s1, w1, hs1, rfl, rfl⟩, hvj, rfl⟩
          rw [hS_iff] at hs1
          have hvj' := inVk_lift hvj
          have hbr := bridge_in_Vk_succ k
          have hall := inVk_xor (inVk_xor hs1 hvj') hbr
          have hrew : ((s1 ^^^ phiBit k x'.val ^^^ phiBit k (finMax k).val) ^^^
                       (vj ^^^ parGauge k (finMax k) ^^^ parGauge k y' ^^^ phiBit k (finMax k).val ^^^ phiBit k y'.val)) ^^^
                      ((2 ^ k - 1) ^^^ parGauge k (finMax k)) =
                      ((s1 ^^^ (2 ^ k - 1)) ^^^ vj) ^^^ phiBit k x'.val ^^^ (phiBit k y'.val ^^^ parGauge k y') := by
            apply Nat.eq_of_testBit_eq; intro t; simp only [Nat.testBit_xor]
            cases s1.testBit t <;> cases vj.testBit t <;> cases (phiBit k x'.val).testBit t <;>
              cases (phiBit k y'.val).testBit t <;> cases (phiBit k (finMax k).val).testBit t <;>
              cases (parGauge k (finMax k)).testBit t <;> cases (parGauge k y').testBit t <;>
              cases (2 ^ k - 1).testBit t <;> rfl
          rwa [hrew] at hall
        · intro hv
          let vj := parGauge k (finMax k) ^^^ parGauge k y' ^^^ phiBit k (finMax k).val ^^^ phiBit k y'.val
          let s1 := v ^^^ (2 ^ k - 1) ^^^ vj
          refine ⟨s1 ^^^ (2 ^ k - 1), vj, ⟨s1, 2 ^ k - 1, ?_, rfl, rfl⟩, ?_, ?_⟩
          · rw [hS_iff]
            have h1 := inVk_xor hv (bridge_in_Vk_succ k)
            have hrew : (v ^^^ phiBit k x'.val ^^^ (phiBit k y'.val ^^^ parGauge k y')) ^^^
                        ((2 ^ k - 1) ^^^ parGauge k (finMax k)) =
                        s1 ^^^ phiBit k x'.val ^^^ phiBit k (finMax k).val := by
              apply Nat.eq_of_testBit_eq; intro t; simp only [s1, vj, Nat.testBit_xor]
              cases v.testBit t <;> cases (phiBit k x'.val).testBit t <;> cases (phiBit k y'.val).testBit t <;>
                cases (phiBit k (finMax k).val).testBit t <;> cases (parGauge k (finMax k)).testBit t <;>
                cases (parGauge k y').testBit t <;> cases (2 ^ k - 1).testBit t <;> rfl
            rwa [hrew] at h1
          · have h0 : vj ^^^ parGauge k (finMax k) ^^^ parGauge k y' ^^^ phiBit k (finMax k).val ^^^ phiBit k y'.val = 0 := by
              apply Nat.eq_of_testBit_eq; intro t; simp only [vj, Nat.testBit_xor, Nat.zero_testBit]
              cases (parGauge k (finMax k)).testBit t <;> cases (parGauge k y').testBit t <;>
                cases (phiBit k (finMax k).val).testBit t <;> cases (phiBit k y'.val).testBit t <;> rfl
            rw [h0]; exact inVk_zero k
          · apply Nat.eq_of_testBit_eq; intro t; simp only [s1, Nat.testBit_xor]
            cases v.testBit t <;> cases (2 ^ k - 1).testBit t <;> cases vj.testBit t <;> rfl
      · -- BL: (1, x') → (0, y')
        simp only [hx, hy, ↓reduceDIte]
        let x' : Fin (2 ^ k) := ⟨x.val - 2 ^ k, by have := x.isLt; omega⟩
        let y' : Fin (2 ^ k) := ⟨y.val, hy⟩
        have hxeq : x.val = 2 ^ k + x'.val := by dsimp [x']; omega
        have hpx : phiBit (k + 1) x.val = phiBit k x'.val ^^^ parGauge k x' := by
          rw [hxeq]; exact phiBit_hi x'.isLt
        rw [hpx, phiBit_lo hy]
        change XorSet.minkXor (XorSet.minkXor (V x' (finZero k)) (XorSet.single 0)) (S (finZero k) y') v ↔ _
        rw [XorSet.minkXor_single_zero]
        simp only [XorSet.minkXor, V, gaugeConj_entry, U, bmiXorStar]
        have hpg0 : parGauge k (finZero k) = 0 := by simp [parGauge, finZero, popcount_zero]
        simp only [hpg0, hpb0, Nat.xor_zero]
        constructor
        · rintro ⟨a, b, ha, hb, rfl⟩
          rw [hS_iff, hpb0, Nat.xor_zero] at hb
          have hall := inVk_xor (inVk_lift ha) hb
          have hrew : (a ^^^ parGauge k x' ^^^ phiBit k x'.val) ^^^ (b ^^^ phiBit k y'.val) =
                      (a ^^^ b) ^^^ (phiBit k x'.val ^^^ parGauge k x') ^^^ phiBit k y'.val := by
            apply Nat.eq_of_testBit_eq; intro t; simp only [Nat.testBit_xor]
            cases a.testBit t <;> cases b.testBit t <;> cases (parGauge k x').testBit t <;>
              cases (phiBit k x'.val).testBit t <;> cases (phiBit k y'.val).testBit t <;> rfl
          rwa [hrew] at hall
        · intro hv
          let a := parGauge k x' ^^^ phiBit k x'.val
          refine ⟨a, v ^^^ a, ?_, ?_, ?_⟩
          · have h0 : a ^^^ parGauge k x' ^^^ phiBit k x'.val = 0 := by
              apply Nat.eq_of_testBit_eq; intro t; simp only [a, Nat.testBit_xor, Nat.zero_testBit]
              cases (parGauge k x').testBit t <;> cases (phiBit k x'.val).testBit t <;> rfl
            rw [h0]; exact inVk_zero k
          · rw [hS_iff, hpb0, Nat.xor_zero]
            have hrew : (v ^^^ a) ^^^ phiBit k y'.val = v ^^^ (phiBit k x'.val ^^^ parGauge k x') ^^^ phiBit k y'.val := by
              apply Nat.eq_of_testBit_eq; intro t; simp only [a, Nat.testBit_xor]
              cases v.testBit t <;> cases (parGauge k x').testBit t <;>
                cases (phiBit k x'.val).testBit t <;> cases (phiBit k y'.val).testBit t <;> rfl
            rwa [hrew]
          · rw [Nat.xor_comm a, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      · -- BR: (1, x') → (1, y')
        simp only [hx, hy, ↓reduceDIte]
        let x' : Fin (2 ^ k) := ⟨x.val - 2 ^ k, by have := x.isLt; omega⟩
        let y' : Fin (2 ^ k) := ⟨y.val - 2 ^ k, by have := y.isLt; omega⟩
        have hxeq : x.val = 2 ^ k + x'.val := by dsimp [x']; omega
        have hyeq : y.val = 2 ^ k + y'.val := by dsimp [y']; omega
        have hpx : phiBit (k + 1) x.val = phiBit k x'.val ^^^ parGauge k x' := by
          rw [hxeq]; exact phiBit_hi x'.isLt
        have hpy : phiBit (k + 1) y.val = phiBit k y'.val ^^^ parGauge k y' := by
          rw [hyeq]; exact phiBit_hi y'.isLt
        rw [hpx, hpy]
        have hpg0 : parGauge k (finZero k) = 0 := by simp [parGauge, finZero, popcount_zero]
        change XorSet.union (V x' y')
          (XorSet.minkXor (XorSet.minkXor (XorSet.minkXor (XorSet.minkXor (V x' (finZero k)) (XorSet.single 0))
            (S (finZero k) (finMax k))) (XorSet.single (2 ^ k - 1))) (V (finMax k) y')) v ↔ _
        rw [XorSet.minkXor_single_zero]
        simp only [XorSet.union, XorSet.minkXor, XorSet.single, V, gaugeConj_entry, U, bmiXorStar, hpg0, hpb0, Nat.xor_zero]
        constructor
        · rintro (hv0 | ⟨ab, vj, ⟨a1, w1, ⟨v1, s1, hv1, hs1, rfl⟩, rfl, rfl⟩, hvj, rfl⟩)
          · have hv0' := inVk_lift hv0
            have hrew : v ^^^ parGauge k x' ^^^ parGauge k y' ^^^ phiBit k x'.val ^^^ phiBit k y'.val =
                        v ^^^ (phiBit k x'.val ^^^ parGauge k x') ^^^ (phiBit k y'.val ^^^ parGauge k y') := by
              apply Nat.eq_of_testBit_eq; intro t; simp only [Nat.testBit_xor]
              cases v.testBit t <;> cases (parGauge k x').testBit t <;> cases (parGauge k y').testBit t <;>
                cases (phiBit k x'.val).testBit t <;> cases (phiBit k y'.val).testBit t <;> rfl
            rwa [hrew] at hv0'
          · rw [hS_iff, hpb0, Nat.xor_zero] at hs1
            have hall := inVk_xor (inVk_xor (inVk_lift hv1) hs1) (inVk_xor (inVk_lift hvj) (bridge_in_Vk_succ k))
            have hrew : ((v1 ^^^ parGauge k x' ^^^ phiBit k x'.val) ^^^ (s1 ^^^ phiBit k (finMax k).val)) ^^^
                        ((vj ^^^ parGauge k (finMax k) ^^^ parGauge k y' ^^^ phiBit k (finMax k).val ^^^ phiBit k y'.val) ^^^
                         ((2 ^ k - 1) ^^^ parGauge k (finMax k))) =
                        (((v1 ^^^ s1) ^^^ (2 ^ k - 1)) ^^^ vj) ^^^
                        (phiBit k x'.val ^^^ parGauge k x') ^^^ (phiBit k y'.val ^^^ parGauge k y') := by
              apply Nat.eq_of_testBit_eq; intro t; simp only [Nat.testBit_xor]
              cases v1.testBit t <;> cases s1.testBit t <;> cases vj.testBit t <;>
                cases (parGauge k x').testBit t <;> cases (parGauge k y').testBit t <;>
                cases (parGauge k (finMax k)).testBit t <;> cases (phiBit k x'.val).testBit t <;>
                cases (phiBit k y'.val).testBit t <;> cases (phiBit k (finMax k).val).testBit t <;>
                cases (2 ^ k - 1).testBit t <;> rfl
            rwa [hrew] at hall
        · intro hv
          right
          let v1 := parGauge k x' ^^^ phiBit k x'.val
          let vj := parGauge k (finMax k) ^^^ parGauge k y' ^^^ phiBit k (finMax k).val ^^^ phiBit k y'.val
          let s1 := v ^^^ v1 ^^^ vj ^^^ (2 ^ k - 1)
          refine ⟨(v1 ^^^ s1) ^^^ (2 ^ k - 1), vj, ⟨v1 ^^^ s1, 2 ^ k - 1, ⟨v1, s1, ?_, ?_, rfl⟩, rfl, rfl⟩, ?_, ?_⟩
          · have h0 : v1 ^^^ parGauge k x' ^^^ phiBit k x'.val = 0 := by
              apply Nat.eq_of_testBit_eq; intro t; simp only [v1, Nat.testBit_xor, Nat.zero_testBit]
              cases (parGauge k x').testBit t <;> cases (phiBit k x'.val).testBit t <;> rfl
            rw [h0]; exact inVk_zero k
          · rw [hS_iff, hpb0, Nat.xor_zero]
            have h1 := inVk_xor hv (bridge_in_Vk_succ k)
            have hrew : (v ^^^ (phiBit k x'.val ^^^ parGauge k x') ^^^ (phiBit k y'.val ^^^ parGauge k y')) ^^^
                        ((2 ^ k - 1) ^^^ parGauge k (finMax k)) = s1 ^^^ phiBit k (finMax k).val := by
              apply Nat.eq_of_testBit_eq; intro t; simp only [s1, v1, vj, Nat.testBit_xor]
              cases v.testBit t <;> cases (parGauge k x').testBit t <;> cases (parGauge k y').testBit t <;>
                cases (parGauge k (finMax k)).testBit t <;> cases (phiBit k x'.val).testBit t <;>
                cases (phiBit k y'.val).testBit t <;> cases (phiBit k (finMax k).val).testBit t <;>
                cases (2 ^ k - 1).testBit t <;> rfl
            rwa [hrew] at h1
          · have h0 : vj ^^^ parGauge k (finMax k) ^^^ parGauge k y' ^^^ phiBit k (finMax k).val ^^^ phiBit k y'.val = 0 := by
              apply Nat.eq_of_testBit_eq; intro t; simp only [vj, Nat.testBit_xor, Nat.zero_testBit]
              cases (parGauge k (finMax k)).testBit t <;> cases (parGauge k y').testBit t <;>
                cases (phiBit k (finMax k).val).testBit t <;> cases (phiBit k y'.val).testBit t <;> rfl
            rw [h0]; exact inVk_zero k
          · apply Nat.eq_of_testBit_eq; intro t; simp only [s1, Nat.testBit_xor]
            cases v.testBit t <;> cases v1.testBit t <;> cases vj.testBit t <;> cases (2 ^ k - 1).testBit t <;> rfl
    dsimp only at hGen
    rwa [hEqMat] at hGen

/-- Exact cycle subspace corollary: `(B_k^{XOR,*})_{0, 0} = V_k`! -/
theorem bmi_xor_cycle_subspace (k : Nat) (v : Nat) :
    bmiXorStar k (finZero k) (finZero k) v ↔ inVk k v := by
  simp [bmiXorStar, finZero, phiBit_zero, Nat.xor_zero]

theorem altEvenMask_closed_form (m : Nat) :
    3 * altEvenMask m + 2 = 2 * 4 ^ m := by
  induction m with
  | zero => decide
  | succ m ih =>
    simp only [altEvenMask]
    have hpow1 : 4 ^ (m + 1) = 4 * 4 ^ m := by rw [Nat.pow_succ]; omega
    have hpow2 : 2 ^ (2 * m + 1) = 2 * 4 ^ m := by
      have h4 : 4 ^ m = 2 ^ (2 * m) := by
        clear ih hpow1; induction m with
        | zero => rfl
        | succ n ihn =>
          have h1 : 2 * (n + 1) = 2 * n + 2 := by omega
          rw [h1, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, ← ihn]; omega
      rw [Nat.pow_succ, ← h4]; omega
    omega

theorem greedyMaxXor_mem (k r : Nat) :
    inVk k (greedyMaxXor k r ^^^ r) := by
  unfold greedyMaxXor
  have hgen : ∀ j, j < k / 2 → inVk k (2 ^ (2 * j + 1) ^^^ 2 ^ (2 * j)) := by
    intro j hj
    have hlt1 : 2 ^ (2 * j + 1) < 2 ^ k := Nat.pow_lt_pow_right (by omega) (by omega)
    have hlt2 : 2 ^ (2 * j) < 2 ^ k := Nat.pow_lt_pow_right (by omega) (by omega)
    refine ⟨Nat.xor_lt_two_pow hlt1 hlt2, ?_, ?_⟩
    · intro l hl
      simp only [Nat.testBit_xor, Nat.testBit_two_pow]
      by_cases hlj : l = j
      · subst hlj
        simp
      · have h1 : 2 * j + 1 ≠ 2 * l := by omega
        have h2 : 2 * j ≠ 2 * l := by omega
        have h4 : 2 * j ≠ 2 * l + 1 := by omega
        simp [h1, h2, h4]
    · intro hodd
      have h1 : 2 * j + 1 ≠ k - 1 := by omega
      have h2 : 2 * j ≠ k - 1 := by omega
      simp [Nat.testBit_xor, h1, h2]
  have hgo : ∀ m (_hm : m ≤ k / 2) acc, inVk k (acc ^^^ r) → inVk k (greedyMaxXor.go m acc ^^^ r) := by
    intro m
    induction m with
    | zero => intro _ acc h; exact h
    | succ m ih =>
      intro hm acc hacc
      simp only [greedyMaxXor.go]
      apply ih (by omega)
      split
      · exact hacc
      · have h1 := inVk_xor hacc (hgen m (by omega))
        have hrew : (acc ^^^ r) ^^^ (2 ^ (2 * m + 1) ^^^ 2 ^ (2 * m)) =
                    (acc ^^^ (2 ^ (2 * m + 1) ^^^ 2 ^ (2 * m))) ^^^ r := by
          apply Nat.eq_of_testBit_eq; intro t; simp only [Nat.testBit_xor]
          cases acc.testBit t <;> cases r.testBit t <;> cases (2 ^ (2 * m + 1)).testBit t <;>
            cases (2 ^ (2 * m)).testBit t <;> rfl
        rwa [hrew] at h1
  exact hgo (k / 2) (Nat.le_refl _) r (by rw [Nat.xor_self]; exact inVk_zero k)

theorem greedyMaxXor_ge_altEvenMask (k r : Nat) :
    altEvenMask (k / 2) ≤ greedyMaxXor k r := by
  have hbits : ∀ m acc j, j < m → (greedyMaxXor.go m acc).testBit (2 * j + 1) = true := by
    intro m
    induction m with
    | zero => intro _ _ hj; omega
    | succ m ih =>
      intro acc j hj
      simp only [greedyMaxXor.go]
      by_cases hjm : j < m
      · exact ih _ j hjm
      · have hjeq : j = m := by omega
        rw [hjeq]
        have hinv : ∀ n (_hn : n ≤ m) a,
            (greedyMaxXor.go n a).testBit (2 * m + 1) = a.testBit (2 * m + 1) := by
          intro n
          induction n with
          | zero => intro _ _; rfl
          | succ n ihn =>
            intro hn a
            simp only [greedyMaxXor.go]
            rw [ihn (by omega)]
            split
            · rfl
            · have hne1 : 2 * n ≠ 2 * m := by omega
              have hne2 : 2 * n ≠ 2 * m + 1 := by omega
              simp [Nat.testBit_xor, hne1, hne2]
        rw [hinv m (Nat.le_refl m)]
        split
        · assumption
        · rename_i hf
          have hbf : acc.testBit (2 * m + 1) = false := by
            cases h : acc.testBit (2 * m + 1) <;> simp_all
          simp [Nat.testBit_xor, hbf]
  have hge_of_bits : ∀ m w, (∀ j, j < m → w.testBit (2 * j + 1) = true) → altEvenMask m ≤ w := by
    intro m
    induction m with
    | zero => intro w _; exact Nat.zero_le w
    | succ m ih =>
      intro w hw
      simp only [altEvenMask]
      have htop : w.testBit (2 * m + 1) = true := hw m (Nat.lt_succ_self m)
      have hdiv_odd : (w / 2 ^ (2 * m + 1)) % 2 = 1 := by
        rw [Nat.testBit_eq_decide_div_mod_eq] at htop
        exact of_decide_eq_true htop
      have hdiv_ge1 : 1 ≤ w / 2 ^ (2 * m + 1) := by
        cases hq : w / 2 ^ (2 * m + 1) with
        | zero => rw [hq] at hdiv_odd; cases hdiv_odd
        | succ _ => exact Nat.succ_le_succ (Nat.zero_le _)
      have hrem_bits : ∀ j, j < m → (w % 2 ^ (2 * m + 1)).testBit (2 * j + 1) = true := by
        intro j hj
        rw [Nat.testBit_mod_two_pow]
        have hlt : 2 * j + 1 < 2 * m + 1 := by omega
        simp [hlt, hw j (by omega)]
      have hrem_ge := ih (w % 2 ^ (2 * m + 1)) hrem_bits
      have hdecomp : w = 2 ^ (2 * m + 1) * (w / 2 ^ (2 * m + 1)) + w % 2 ^ (2 * m + 1) :=
        (Nat.div_add_mod w (2 ^ (2 * m + 1))).symm
      have hmul_ge : 2 ^ (2 * m + 1) ≤ 2 ^ (2 * m + 1) * (w / 2 ^ (2 * m + 1)) := by
        calc 2 ^ (2 * m + 1) = 2 ^ (2 * m + 1) * 1 := (Nat.mul_one _).symm
          _ ≤ 2 ^ (2 * m + 1) * (w / 2 ^ (2 * m + 1)) := Nat.mul_le_mul_left _ hdiv_ge1
      omega
  exact hge_of_bits (k / 2) (greedyMaxXor k r) (hbits (k / 2) r)

/-- Exact evaluation: for `2*m ≤ k`, `phiBit k (2^(2*m) - 1) = altEvenMask m`! -/
theorem phiBit_even_ones (m : Nat) :
    ∀ k, 2 * m ≤ k → phiBit k (2 ^ (2 * m) - 1) = altEvenMask m := by
  intro k hk
  have hred : phiBit k (2 ^ (2 * m) - 1) = phiBit (2 * m) (2 ^ (2 * m) - 1) := by
    have hlt : 2 ^ (2 * m) - 1 < 2 ^ (2 * m) := by have := Nat.two_pow_pos (2 * m); omega
    induction k with
    | zero =>
      have hm0 : m = 0 := by omega
      subst hm0; rfl
    | succ k ih =>
      by_cases hle : 2 * m ≤ k
      · have hlt_k : 2 ^ (2 * m) - 1 < 2 ^ k :=
          Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) hle)
        rw [phiBit_lo hlt_k, ih hle]
      · have heq : k + 1 = 2 * m := by omega
        rw [heq]
  rw [hred]
  clear hk hred k
  induction m with
  | zero => rfl
  | succ m ih =>
    have hpow1 : 2 ^ (2 * m + 1) = 2 ^ (2 * m) + 2 ^ (2 * m) := by rw [Nat.pow_succ]; omega
    have hpow2 : 2 ^ (2 * m + 2) = 2 ^ (2 * m + 1) + 2 ^ (2 * m + 1) := by rw [Nat.pow_succ]; omega
    have hpos : 0 < 2 ^ (2 * m) := Nat.two_pow_pos (2 * m)
    have h2m : 2 * (m + 1) = 2 * m + 2 := by omega
    have hstep1 : 2 ^ (2 * m + 2) - 1 = 2 ^ (2 * m + 1) + (2 ^ (2 * m + 1) - 1) := by omega
    have hstep2 : 2 ^ (2 * m + 1) - 1 = 2 ^ (2 * m) + (2 ^ (2 * m) - 1) := by omega
    rw [h2m, hstep1, phiBit_hi (by omega : 2 ^ (2 * m + 1) - 1 < 2 ^ (2 * m + 1))]
    have hpg2 : parGauge (2 * m + 1) ⟨2 ^ (2 * m + 1) - 1, by omega⟩ = 2 ^ (2 * m + 1) := by
      simp [parGauge, popcount_pow2_sub_one]
    rw [hpg2, hstep2, phiBit_hi (by omega : 2 ^ (2 * m) - 1 < 2 ^ (2 * m))]
    have hpg1 : parGauge (2 * m) ⟨2 ^ (2 * m) - 1, by omega⟩ = 0 := by
      simp [parGauge, popcount_pow2_sub_one]
    rw [hpg1, Nat.xor_zero, ih]
    simp only [altEvenMask]
    have halt_lt : altEvenMask m < 2 ^ (2 * m + 1) := by
      have hc := altEvenMask_closed_form m
      have h4 : ∀ n, 4 ^ n = 2 ^ (2 * n) := by
        intro n; induction n with
        | zero => rfl
        | succ n ihn =>
          have : 2 * (n + 1) = 2 * n + 2 := by omega
          rw [this, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, ← ihn]; omega
      have h4m := h4 m
      omega
    apply Nat.eq_of_testBit_eq; intro t
    rw [Nat.add_comm (altEvenMask m) (2 ^ (2 * m + 1)), testBit_add_pow2 halt_lt, Nat.testBit_xor, Nat.testBit_two_pow]
    by_cases ht : 2 * m + 1 = t
    · subst ht; simp [Nat.testBit_lt_two_pow halt_lt]
    · simp [ht]

/-- Any `v` in the coset `altEvenMask (k / 2) ⊕ V_k` satisfies `v ≤ altEvenMask (k / 2)`! -/
theorem le_altEvenMask_of_inVk_xor (k v : Nat) (h : inVk k (v ^^^ altEvenMask (k / 2))) :
    v ≤ altEvenMask (k / 2) := by
  have halt_lt_2m : ∀ m, altEvenMask m < 2 ^ (2 * m) := by
    intro m
    have hc := altEvenMask_closed_form m
    have h4 : ∀ n, 4 ^ n = 2 ^ (2 * n) := by
      intro n; induction n with
      | zero => rfl
      | succ n ihn =>
        have : 2 * (n + 1) = 2 * n + 2 := by omega
        rw [this, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, ← ihn]; omega
    have h4m := h4 m
    omega
  have halt_bit_hi : ∀ m t, 2 * m ≤ t → (altEvenMask m).testBit t = false := fun m t ht =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (halt_lt_2m m) (Nat.pow_le_pow_right (by omega) ht))
  have hv_lt_2m : v < 2 ^ (2 * (k / 2)) := by
    by_cases hodd : k % 2 = 1
    · have hk1 : k = 2 * (k / 2) + 1 := by omega
      have hpow : 2 ^ k = 2 ^ (2 * (k / 2)) + 2 ^ (2 * (k / 2)) := by
        conv => lhs; rw [hk1]
        rw [Nat.pow_succ]; omega
      have hv_lt_k : v < 2 ^ k := by
        have halt_k : altEvenMask (k / 2) < 2 ^ k :=
          Nat.lt_of_lt_of_le (halt_lt_2m (k / 2)) (Nat.pow_le_pow_right (by omega) (by omega))
        have hx := Nat.xor_lt_two_pow h.1 halt_k
        rwa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at hx
      have hbit : v.testBit (2 * (k / 2)) = false := by
        have hf := h.2.2 hodd
        have hkeq : k - 1 = 2 * (k / 2) := by omega
        rw [hkeq, Nat.testBit_xor, halt_bit_hi (k / 2) (2 * (k / 2)) (Nat.le_refl _), Bool.xor_false] at hf
        exact hf
      exact Nat.lt_of_not_le (fun hge => by
        have hd : v / 2 ^ (2 * (k / 2)) = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
        rw [Nat.testBit_eq_decide_div_mod_eq, hd] at hbit
        cases hbit)
    · have hkeq : 2 * (k / 2) = k := by omega
      have halt_k : altEvenMask (k / 2) < 2 ^ k := by
        have h0 := halt_lt_2m (k / 2); rwa [hkeq] at h0
      have hx := Nat.xor_lt_two_pow h.1 halt_k
      rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at hx
      rwa [hkeq]
  have hpair_ne : ∀ j, j < k / 2 → v.testBit (2 * j) ≠ v.testBit (2 * j + 1) := by
    intro j hj
    have hpeq := h.2.1 j hj
    simp only [Nat.testBit_xor] at hpeq
    have hmask_bits : ∀ m i, i < m →
        (altEvenMask m).testBit (2 * i) = false ∧ (altEvenMask m).testBit (2 * i + 1) = true := by
      intro m
      induction m with
      | zero => intro _ hi; omega
      | succ m ihm =>
        intro i hi
        simp only [altEvenMask]
        have hlt := Nat.lt_trans (halt_lt_2m m) (Nat.pow_lt_pow_right (by omega) (by omega : 2 * m < 2 * m + 1))
        rw [Nat.add_comm, testBit_add_pow2 hlt, testBit_add_pow2 hlt]
        by_cases him : i < m
        · have h1 : 2 * m + 1 ≠ 2 * i := by omega
          simp [h1, ihm i him]
        · have hieq : i = m := by omega
          subst hieq
          simp [halt_bit_hi i (2 * i) (Nat.le_refl _)]
    have ⟨hb0, hb1⟩ := hmask_bits (k / 2) j hj
    rw [hb0, hb1] at hpeq
    cases h0 : v.testBit (2 * j) <;> cases h1 : v.testBit (2 * j + 1) <;> simp_all
  have hmain : ∀ m w, w < 2 ^ (2 * m) → (∀ j, j < m → w.testBit (2 * j) ≠ w.testBit (2 * j + 1)) →
      w ≤ altEvenMask m := by
    intro m
    induction m with
    | zero => intro w hw _; omega
    | succ m ihm =>
      intro w hw hne
      simp only [altEvenMask]
      have hrem_lt : w % 2 ^ (2 * m) < 2 ^ (2 * m) := Nat.mod_lt w (Nat.two_pow_pos (2 * m))
      have hrem_ne : ∀ j, j < m → (w % 2 ^ (2 * m)).testBit (2 * j) ≠ (w % 2 ^ (2 * m)).testBit (2 * j + 1) := by
        intro j hj
        rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
        have h1 : 2 * j < 2 * m := by omega
        have h2 : 2 * j + 1 < 2 * m := by omega
        simp [h1, h2, hne j (by omega)]
      have hrem_le := ihm (w % 2 ^ (2 * m)) hrem_lt hrem_ne
      have hq_lt : w / 2 ^ (2 * m) < 4 := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos (2 * m))]
        have hpow : 2 ^ (2 * (m + 1)) = 4 * 2 ^ (2 * m) := by
          have : 2 * (m + 1) = 2 * m + 2 := by omega
          rw [this, Nat.pow_succ, Nat.pow_succ]; omega
        omega
      have htop_ne := hne m (Nat.lt_succ_self m)
      have hq_ne3 : w / 2 ^ (2 * m) ≠ 3 := by
        intro hq3
        have hb0 : w.testBit (2 * m) = true := by
          rw [Nat.testBit_eq_decide_div_mod_eq, hq3]; decide
        have hb1 : w.testBit (2 * m + 1) = true := by
          rw [Nat.testBit_eq_decide_div_mod_eq]
          have hdiv1 : w / 2 ^ (2 * m + 1) = (w / 2 ^ (2 * m)) / 2 := by
            rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
          rw [hdiv1, hq3]; decide
        exact htop_ne (by rw [hb0, hb1])
      have hq_le2 : w / 2 ^ (2 * m) ≤ 2 := by omega
      have hdecomp : w = 2 ^ (2 * m) * (w / 2 ^ (2 * m)) + w % 2 ^ (2 * m) :=
        (Nat.div_add_mod w (2 ^ (2 * m))).symm
      have hpow1 : 2 ^ (2 * m + 1) = 2 ^ (2 * m) * 2 := Nat.pow_succ _ _
      have hmul : 2 ^ (2 * m) * (w / 2 ^ (2 * m)) ≤ 2 ^ (2 * m + 1) := by
        rw [hpow1]; exact Nat.mul_le_mul_left _ hq_le2
      omega
  exact hmain (k / 2) v hv_lt_2m hpair_ne

/-- **THEOREM 4B (Exact All-Pairs Max-XOR Bottleneck Theorem on `B_k`, ∀ k : ℕ):**
    1. Universal lower bound: for EVERY `x, y : Fin (2^k)`, there exists an achievable XOR
       walk weight `v ∈ (B_k^{XOR,*})_{x, y}` with `v ≥ altEvenMask (k / 2) = 2*(4^(k/2) - 1)/3`!
    2. Exact attainment: at `(0, 2^(2*(k/2)) - 1)`, `altEvenMask (k / 2)` is achieved AND
       every achievable XOR walk weight `v` satisfies `v ≤ altEvenMask (k / 2)`! -/
theorem bmi_xor_max_bottleneck_exact (k : Nat) :
    (∀ x y : Fin (2 ^ k), ∃ v, bmiXorStar k x y v ∧ altEvenMask (k / 2) ≤ v) ∧
    (let yMin : Fin (2 ^ k) := ⟨2 ^ (2 * (k / 2)) - 1,
        Nat.lt_of_lt_of_le (by have := Nat.two_pow_pos (2 * (k / 2)); omega : 2 ^ (2 * (k / 2)) - 1 < 2 ^ (2 * (k / 2)))
                           (Nat.pow_le_pow_right (by omega) (by omega))⟩
     bmiXorStar k (finZero k) yMin (altEvenMask (k / 2)) ∧
     ∀ v, bmiXorStar k (finZero k) yMin v → v ≤ altEvenMask (k / 2)) := by
  constructor
  · intro x y
    let r := phiBit k x.val ^^^ phiBit k y.val
    refine ⟨greedyMaxXor k r, ?_, greedyMaxXor_ge_altEvenMask k r⟩
    change inVk k (greedyMaxXor k r ^^^ phiBit k x.val ^^^ phiBit k y.val)
    rw [Nat.xor_assoc]
    exact greedyMaxXor_mem k r
  · intro yMin
    have hphi : phiBit k yMin.val = altEvenMask (k / 2) :=
      phiBit_even_ones (k / 2) k (by omega)
    constructor
    · simp only [bmiXorStar, finZero, phiBit_zero, Nat.xor_zero, hphi, Nat.xor_self]
      exact inVk_zero k
    · intro v hv
      simp only [bmiXorStar, finZero, phiBit_zero, Nat.xor_zero, hphi] at hv
      exact le_altEvenMask_of_inVk_xor k v hv

/-- **Sharpness Witness for Theorem 4 (`k = 3` Hypercube Extra-Edge Obstruction):**
    Adding ONE non-BMI1 hypercube edge `001 → 101` (flipping bit 2 while lower bits `01`
    have ODD parity, weight `1 &&& 5 = 1`) creates the 4-cycle `1 → 5 → 4 → 0 → 1` whose
    XOR weight `1 ^^^ 4 ^^^ 0 ^^^ 0 = 5` lies strictly OUTSIDE `V_3 = {0, 3}`! -/
theorem hypercube_extra_edge_breaks_V3 :
    let w_cycle := (1 &&& 5) ^^^ (5 &&& 4) ^^^ (4 &&& 0) ^^^ (0 &&& 1)
    w_cycle = 5 ∧ ¬ inVk 3 w_cycle := by
  intro w_cycle
  refine ⟨rfl, ?_⟩
  intro h
  have hbit := h.2.2 (by decide)
  change (5 : Nat).testBit 2 = false at hbit
  cases hbit

end ActiveXorEngine


/-! ============================================================================
    SECTION 11: KERNEL-CHECKED NON-VACUITY WITNESSES & AXIOM RECEIPTS
    ============================================================================ -/

/-- Non-vacuity witness 1: `B_4` unit & linear & pow2 diameters (`10, 20, 26`) + Gray code at `y = 10 = 1010₂`. -/
theorem witness_bmi_k4 :
    bmiDist 4 (fun _ => 1) (finZero 4) ⟨altWord 4, altWord_lt 4⟩ = 10 ∧
    bmiDist 4 (fun b => b + 1) (finZero 4) ⟨altWord 4, altWord_lt 4⟩ = 20 ∧
    bmiDist 4 (fun b => 2 ^ b) (finZero 4) ⟨altWord 4, altWord_lt 4⟩ = 26 ∧
    altWord 4 = 10 := by
  refine ⟨?_, ?_, ?_, rfl⟩
  · have h1 := bmiDist_altWord_eq_weightedDiam 4 (fun _ => 1)
    have h2 := weightedDiam_unit 4; omega
  · have h1 := bmiDist_altWord_eq_weightedDiam 4 (fun b => b + 1)
    have h2 := weightedDiam_linear 4; omega
  · have h1 := bmiDist_altWord_eq_weightedDiam 4 (fun b => 2 ^ b)
    have h2 := weightedDiam_pow2 4 (by omega); omega

/-- Non-vacuity witness 2: `B_4` Boolean matrix-power periodicity (`B_4^11 = B_4^9` and `B_4^10 ≠ B_4^8`). -/
theorem witness_bmi_bool_k4 :
    matPow (bmiBoolMat 4) 11 = matPow (bmiBoolMat 4) 9 ∧
    matPow (bmiBoolMat 4) 10 ≠ matPow (bmiBoolMat 4) 8 :=
  ⟨bmiBoolPow_periodic 4 (by omega) 9 (by omega), bmiBoolPow_index_sharp 4 (by omega)⟩

/-- Non-vacuity witness 3: `A_4` ALU exact exponential asymmetry (`D_4(0, 15) = 26` vs `D_4(15, 0) = 4`). -/
theorem witness_alu_k4 :
    aluDist 4 (finZero 4) (finMax 4) = 26 ∧ aluDist 4 (finMax 4) (finZero 4) = 4 := by
  have ⟨_, h1, h2⟩ := alu_exact_diameter_and_asymmetry 4
  exact ⟨by omega, h2⟩

/-- Non-vacuity witness 4: `B_4` Active-Schur XOR bottleneck (`altEvenMask 2 = 10 = 1010₂`, `V_4` contains `12` and rejects `5`). -/
theorem witness_xor_k4 :
    altEvenMask 2 = 10 ∧
    bmiXorStar 4 (finZero 4) (finZero 4) 12 ∧
    ¬ bmiXorStar 4 (finZero 4) (finZero 4) 5 := by
  refine ⟨rfl, ?_, ?_⟩
  · rw [bmi_xor_cycle_subspace]
    refine ⟨by decide, fun j hj => ?_, fun h => by omega⟩
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl <;> decide
  · rw [bmi_xor_cycle_subspace]
    intro h
    have h0 := h.2.1 0 (by omega)
    change (5 : Nat).testBit 0 = (5 : Nat).testBit 1 at h0
    cases h0

end BSKSE
