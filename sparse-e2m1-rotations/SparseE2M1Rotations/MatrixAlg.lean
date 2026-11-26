/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SparseE2M1Rotations.Defs

/-!
# Pure-`Init` Matrix, Kronecker, Sparsity, and Walsh–Hadamard Algebra

Reusable foundational lemmas for `sumFin`, `matMul`, `transpose`, `kron`,
2:4-sparsity preservation under Kronecker products, and Walsh–Hadamard orthogonality.
-/

namespace SparseE2M1Rotations

/-! ### 1. Finite sums over `Fin n` -/

theorem sumFin_congr {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i = g i) :
    sumFin n f = sumFin n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumFin]
    rw [ih (fun i => h i.castSucc), h (Fin.last n)]

theorem sumFin_cast {m n : Nat} (h : m = n) (f : Fin m → Int) :
    sumFin m f = sumFin n (fun i => f ⟨i.val, h ▸ i.isLt⟩) := by
  subst h
  rfl

theorem sumFin_zero_fun (n : Nat) : sumFin n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumFin]
    rw [ih]
    omega

theorem sumFin_add {n : Nat} (f g : Fin n → Int) :
    sumFin n (fun i => f i + g i) = sumFin n f + sumFin n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumFin]
    rw [ih]
    omega

theorem sumFin_neg {n : Nat} (f : Fin n → Int) :
    sumFin n (fun i => -f i) = -(sumFin n f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumFin]
    rw [ih]
    omega

theorem sumFin_mul_left {n : Nat} (c : Int) (f : Fin n → Int) :
    sumFin n (fun i => c * f i) = c * sumFin n f := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih =>
    simp only [sumFin]
    rw [ih, Int.mul_add]

theorem sumFin_mul_right {n : Nat} (f : Fin n → Int) (c : Int) :
    sumFin n (fun i => f i * c) = sumFin n f * c := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih =>
    simp only [sumFin]
    rw [ih, Int.add_mul]

theorem sumFin_const (n : Nat) (c : Int) :
    sumFin n (fun _ => c) = (n : Int) * c := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih =>
    simp only [sumFin]
    rw [ih]
    have hcast : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by omega
    rw [hcast, Int.add_mul, Int.one_mul]

theorem sumFin_le {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i ≤ g i) :
    sumFin n f ≤ sumFin n g := by
  induction n with
  | zero => exact Int.le_refl 0
  | succ n ih =>
    simp only [sumFin]
    have h1 := ih (fun i => h i.castSucc)
    have h2 := h (Fin.last n)
    omega

theorem sumFin_single_eq {n : Nat} (j : Fin n) (v : Int) :
    sumFin n (fun i => if i = j then v else 0) = v := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    simp only [sumFin]
    by_cases hj : j.val < n
    · let j' : Fin n := ⟨j.val, hj⟩
      have hlast : Fin.last n ≠ j := by
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      simp only [hlast, ↓reduceIte, Int.add_zero]
      have hcongr : ∀ i : Fin n, (if i.castSucc = j then v else 0) = (if i = j' then v else 0) := by
        intro i
        by_cases h : i = j'
        · subst h
          have heq : j'.castSucc = j := Fin.ext rfl
          simp [heq]
        · have hne : i.castSucc ≠ j := by
            intro heq
            apply h
            have hv : i.castSucc.val = j.val := congrArg Fin.val heq
            exact Fin.ext (by simpa [j'] using hv)
          simp [h, hne]
      rw [sumFin_congr hcongr, ih j']
    · have hjlast : j = Fin.last n := Fin.ext (by simp; omega)
      subst hjlast
      simp only [↓reduceIte]
      have hcongr : ∀ i : Fin n, (if i.castSucc = Fin.last n then v else 0) = 0 := by
        intro i
        have hne : i.castSucc ≠ Fin.last n := by
          intro h
          have := congrArg Fin.val h
          simp at this
          omega
        simp [hne]
      rw [sumFin_congr hcongr, sumFin_zero_fun, Int.zero_add]

theorem sumFin_single_eq' {n : Nat} (j : Fin n) (v : Int) :
    sumFin n (fun i => if j = i then v else 0) = v := by
  have h : ∀ i : Fin n, (if j = i then v else 0) = (if i = j then v else 0) := by
    intro i
    by_cases hij : i = j
    · subst hij; simp
    · have hji : j ≠ i := Ne.symm hij
      simp [hij, hji]
  rw [sumFin_congr h, sumFin_single_eq]

theorem sumFin_add_split (p q : Nat) (f : Fin (p + q) → Int) :
    sumFin (p + q) f =
      sumFin p (fun i => f ⟨i.val, by omega⟩) +
      sumFin q (fun j => f ⟨p + j.val, by omega⟩) := by
  induction q with
  | zero =>
    simp only [Nat.add_zero, sumFin, Int.add_zero]
    exact sumFin_congr (fun _ => rfl)
  | succ q ih =>
    have hstep : sumFin (p + (q + 1)) f =
        sumFin (p + q) (fun i => f ⟨i.val, by omega⟩) + f ⟨p + q, by omega⟩ := rfl
    rw [hstep, ih (fun i => f ⟨i.val, by omega⟩)]
    have hrhs : sumFin (q + 1) (fun j => f ⟨p + j.val, by omega⟩) =
        sumFin q (fun j => f ⟨p + j.val, by omega⟩) + f ⟨p + q, by omega⟩ := by
      simp only [sumFin]
      rfl
    rw [hrhs, Int.add_assoc]

theorem sumFin_prod (a b : Nat) (f : Fin (a * b) → Int) :
    sumFin (a * b) f =
      sumFin a (fun i => sumFin b (fun j => f ⟨i.val * b + j.val, by
        have hi := i.isLt
        have hj := j.isLt
        have h1 : (i.val + 1) * b ≤ a * b := Nat.mul_le_mul_right b hi
        rw [Nat.add_mul, Nat.one_mul] at h1
        omega⟩)) := by
  induction a with
  | zero =>
    have h0 : 0 * b = 0 := Nat.zero_mul b
    rw [sumFin_cast h0]
    rfl
  | succ a ih =>
    have hmul : (a + 1) * b = a * b + b := by rw [Nat.add_mul, Nat.one_mul]
    rw [sumFin_cast hmul, sumFin_add_split (a * b) b]
    rw [ih (fun i => f ⟨i.val, by omega⟩)]
    simp only [sumFin]
    rfl

/-! ### 2. Basic Matrix Algebra -/

theorem transpose_idMat (n : Nat) : transpose (idMat n) = idMat n := by
  funext i j
  simp only [transpose, idMat]
  by_cases h : i = j
  · subst h; simp
  · have h' : j ≠ i := Ne.symm h
    simp [h, h']

theorem transpose_scaleMat {m n : Nat} (c : Int) (A : IntMat m n) :
    transpose (scaleMat c A) = scaleMat c (transpose A) := rfl

theorem transpose_addMat {m n : Nat} (A B : IntMat m n) :
    transpose (addMat A B) = addMat (transpose A) (transpose B) := rfl

theorem transpose_negMat {m n : Nat} (A : IntMat m n) :
    transpose (negMat A) = negMat (transpose A) := rfl

theorem transpose_kron {m1 n1 m2 n2 : Nat} (A : IntMat m1 n1) (B : IntMat m2 n2) :
    transpose (kron A B) = kron (transpose A) (transpose B) := rfl

theorem matMul_idMat_right {m n : Nat} (A : IntMat m n) :
    matMul A (idMat n) = A := by
  funext i j
  simp only [matMul, idMat]
  have h : ∀ t : Fin n, A i t * (if t = j then 1 else 0) = if t = j then A i j else 0 := by
    intro t
    by_cases ht : t = j
    · subst ht; simp
    · simp [ht]
  rw [sumFin_congr h, sumFin_single_eq]

theorem matMul_idMat_left {m n : Nat} (A : IntMat m n) :
    matMul (idMat m) A = A := by
  funext i j
  simp only [matMul, idMat]
  have h : ∀ t : Fin m, (if i = t then 1 else 0) * A t j = if i = t then A i j else 0 := by
    intro t
    by_cases ht : i = t
    · subst ht; simp
    · simp [ht]
  rw [sumFin_congr h, sumFin_single_eq']

theorem matMul_scaleMat_left {m k n : Nat} (c : Int) (A : IntMat m k) (B : IntMat k n) :
    matMul (scaleMat c A) B = scaleMat c (matMul A B) := by
  funext i j
  simp only [matMul, scaleMat]
  have h : ∀ t : Fin k, (c * A i t) * B t j = c * (A i t * B t j) := fun t => Int.mul_assoc _ _ _
  rw [sumFin_congr h, sumFin_mul_left]

theorem matMul_scaleMat_right {m k n : Nat} (c : Int) (A : IntMat m k) (B : IntMat k n) :
    matMul A (scaleMat c B) = scaleMat c (matMul A B) := by
  funext i j
  simp only [matMul, scaleMat]
  have h : ∀ t : Fin k, A i t * (c * B t j) = c * (A i t * B t j) := by
    intro t
    rw [← Int.mul_assoc, Int.mul_comm (A i t) c, Int.mul_assoc]
  rw [sumFin_congr h, sumFin_mul_left]

theorem matMul_add_left {m k n : Nat} (A1 A2 : IntMat m k) (B : IntMat k n) :
    matMul (addMat A1 A2) B = addMat (matMul A1 B) (matMul A2 B) := by
  funext i j
  simp only [matMul, addMat]
  have h : ∀ t : Fin k, (A1 i t + A2 i t) * B t j = A1 i t * B t j + A2 i t * B t j :=
    fun t => Int.add_mul _ _ _
  rw [sumFin_congr h, sumFin_add]

theorem matMul_add_right {m k n : Nat} (A : IntMat m k) (B1 B2 : IntMat k n) :
    matMul A (addMat B1 B2) = addMat (matMul A B1) (matMul A B2) := by
  funext i j
  simp only [matMul, addMat]
  have h : ∀ t : Fin k, A i t * (B1 t j + B2 t j) = A i t * B1 t j + A i t * B2 t j :=
    fun t => Int.mul_add _ _ _
  rw [sumFin_congr h, sumFin_add]

theorem matMul_neg_left {m k n : Nat} (A : IntMat m k) (B : IntMat k n) :
    matMul (negMat A) B = negMat (matMul A B) := by
  funext i j
  simp only [matMul, negMat]
  have h : ∀ t : Fin k, (-A i t) * B t j = -(A i t * B t j) := fun t => Int.neg_mul _ _
  rw [sumFin_congr h, sumFin_neg]

theorem matMul_neg_right {m k n : Nat} (A : IntMat m k) (B : IntMat k n) :
    matMul A (negMat B) = negMat (matMul A B) := by
  funext i j
  simp only [matMul, negMat]
  have h : ∀ t : Fin k, A i t * (-B t j) = -(A i t * B t j) := fun t => Int.mul_neg _ _
  rw [sumFin_congr h, sumFin_neg]

/-! ### 3. Kronecker Product Algebra -/

theorem kron_idMat (m n : Nat) : kron (idMat m) (idMat n) = idMat (m * n) := by
  funext i j
  simp only [kron, idMat]
  have hn : 0 < n := pos_right_of_fin_mul i
  by_cases hij : i = j
  · subst hij
    simp
  · have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    by_cases hdiv : i.val / n = j.val / n
    · have hmod : i.val % n ≠ j.val % n := by
        intro hm
        apply hne
        have hi := Nat.div_add_mod i.val n
        have hj := Nat.div_add_mod j.val n
        rw [hdiv, hm] at hi
        omega
      have hfmod : (⟨i.val % n, Nat.mod_lt _ hn⟩ : Fin n) ≠ ⟨j.val % n, Nat.mod_lt _ (pos_right_of_fin_mul j)⟩ := by
        intro h
        exact hmod (congrArg Fin.val h)
      simp [hij, hfmod]
    · have hfdiv : (⟨i.val / n, div_lt_left_of_fin_mul i⟩ : Fin m) ≠
                   ⟨j.val / n, div_lt_left_of_fin_mul j⟩ := by
        intro h
        exact hdiv (congrArg Fin.val h)
      simp [hij, hfdiv]

theorem kron_scaleMat {m1 n1 m2 n2 : Nat} (c1 c2 : Int)
    (A : IntMat m1 n1) (B : IntMat m2 n2) :
    kron (scaleMat c1 A) (scaleMat c2 B) = scaleMat (c1 * c2) (kron A B) := by
  funext i j
  simp only [kron, scaleMat]
  have h : ∀ (x y : Int), (c1 * x) * (c2 * y) = (c1 * c2) * (x * y) := by
    intro x y
    rw [Int.mul_assoc, ← Int.mul_assoc x c2 y, Int.mul_comm x c2, Int.mul_assoc c2 x y, ← Int.mul_assoc]
  exact h _ _

/-- Universal Kronecker mixed-product law: `(A ⊗ B) (C ⊗ D) = (A C) ⊗ (B D)`. -/
theorem kron_matMul {m1 k1 n1 m2 k2 n2 : Nat}
    (A : IntMat m1 k1) (B : IntMat m2 k2) (C : IntMat k1 n1) (D : IntMat k2 n2) :
    matMul (kron A B) (kron C D) = kron (matMul A C) (matMul B D) := by
  funext i j
  simp only [matMul, kron]
  have hm2 : 0 < m2 := pos_right_of_fin_mul i
  have hn2 : 0 < n2 := pos_right_of_fin_mul j
  by_cases hk2 : k2 = 0
  · subst hk2
    have h0 : k1 * 0 = 0 := Nat.mul_zero k1
    rw [sumFin_cast h0]
    simp [sumFin]
  · have hk2pos : 0 < k2 := Nat.pos_of_ne_zero hk2
    rw [sumFin_prod k1 k2]
    have hinner : ∀ t1 : Fin k1,
        sumFin k2 (fun t2 =>
          (A ⟨i.val / m2, div_lt_left_of_fin_mul i⟩
             ⟨(t1.val * k2 + t2.val) / k2, div_lt_left_of_fin_mul (⟨t1.val * k2 + t2.val, by
               have hi := t1.isLt; have hj := t2.isLt
               have h1 : (t1.val + 1) * k2 ≤ k1 * k2 := Nat.mul_le_mul_right k2 hi
               rw [Nat.add_mul, Nat.one_mul] at h1; omega⟩ : Fin (k1 * k2))⟩ *
           B ⟨i.val % m2, Nat.mod_lt _ hm2⟩
             ⟨(t1.val * k2 + t2.val) % k2, Nat.mod_lt _ hk2pos⟩) *
          (C ⟨(t1.val * k2 + t2.val) / k2, div_lt_left_of_fin_mul (⟨t1.val * k2 + t2.val, by
               have hi := t1.isLt; have hj := t2.isLt
               have h1 : (t1.val + 1) * k2 ≤ k1 * k2 := Nat.mul_le_mul_right k2 hi
               rw [Nat.add_mul, Nat.one_mul] at h1; omega⟩ : Fin (k1 * k2))⟩
             ⟨j.val / n2, div_lt_left_of_fin_mul j⟩ *
           D ⟨(t1.val * k2 + t2.val) % k2, Nat.mod_lt _ hk2pos⟩
             ⟨j.val % n2, Nat.mod_lt _ hn2⟩)) =
        (A ⟨i.val / m2, div_lt_left_of_fin_mul i⟩ t1 *
         C t1 ⟨j.val / n2, div_lt_left_of_fin_mul j⟩) *
        sumFin k2 (fun t2 =>
          B ⟨i.val % m2, Nat.mod_lt _ hm2⟩ t2 * D t2 ⟨j.val % n2, Nat.mod_lt _ hn2⟩) := by
      intro t1
      rw [← sumFin_mul_left]
      apply sumFin_congr
      intro t2
      have hdiv : (t1.val * k2 + t2.val) / k2 = t1.val := by
        rw [Nat.mul_comm, Nat.mul_add_div hk2pos, Nat.div_eq_of_lt t2.isLt, Nat.add_zero]
      have hmod : (t1.val * k2 + t2.val) % k2 = t2.val := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt t2.isLt]
      have hlt : t1.val * k2 + t2.val < k1 * k2 := by
        have hi := t1.isLt; have hj := t2.isLt
        have h1 : (t1.val + 1) * k2 ≤ k1 * k2 := Nat.mul_le_mul_right k2 hi
        rw [Nat.add_mul, Nat.one_mul] at h1; omega
      have hf1 : (⟨(t1.val * k2 + t2.val) / k2,
          div_lt_left_of_fin_mul (⟨t1.val * k2 + t2.val, hlt⟩ : Fin (k1 * k2))⟩ : Fin k1) = t1 :=
        Fin.ext hdiv
      have hf2 : (⟨(t1.val * k2 + t2.val) % k2, Nat.mod_lt _ hk2pos⟩ : Fin k2) = t2 :=
        Fin.ext hmod
      rw [hf1, hf2]
      have hring : ∀ (a b c d : Int), (a * b) * (c * d) = (a * c) * (b * d) := by
        intro a b c d
        rw [Int.mul_assoc, ← Int.mul_assoc b c d, Int.mul_comm b c, Int.mul_assoc c b d, ← Int.mul_assoc]
      exact hring _ _ _ _
    rw [sumFin_congr hinner, sumFin_mul_right]

theorem kron_isOrthogonal {n1 n2 : Nat} {A : IntMat n1 n1} {B : IntMat n2 n2} {c1 c2 : Int}
    (hA : isOrthogonal A c1) (hB : isOrthogonal B c2) :
    isOrthogonal (kron A B) (c1 * c2) := by
  unfold isOrthogonal at *
  rw [transpose_kron, kron_matMul, hA, hB, kron_scaleMat, kron_idMat]

theorem kron_isRowOrthogonal {n1 n2 : Nat} {A : IntMat n1 n1} {B : IntMat n2 n2} {c1 c2 : Int}
    (hA : isRowOrthogonal A c1) (hB : isRowOrthogonal B c2) :
    isRowOrthogonal (kron A B) (c1 * c2) := by
  unfold isRowOrthogonal at *
  rw [transpose_kron, kron_matMul, hA, hB, kron_scaleMat, kron_idMat]

/-! ### 4. 2:4-Sparsity and Entry-Set Preservation -/

theorem nzCount4_scale_le (c a b d e : Int) :
    nzCount4 (c * a) (c * b) (c * d) (c * e) ≤ nzCount4 a b d e := by
  have h1 : ∀ x : Int, (if (c * x != 0) then (1 : Nat) else 0) ≤ (if (x != 0) then 1 else 0) := by
    intro x
    by_cases hx : x = 0
    · subst hx; simp
    · simp [hx]
      split <;> omega
  unfold nzCount4
  have ha := h1 a; have hb := h1 b; have hd := h1 d; have he := h1 e
  omega

theorem kron_is24SparseRows {r m : Nat} (A : IntMat r m) (B : IntMat 4 4)
    (hB : ∀ i : Fin 4, nzCount4 (B i ⟨0, by omega⟩) (B i ⟨1, by omega⟩)
                                (B i ⟨2, by omega⟩) (B i ⟨3, by omega⟩) ≤ 2) :
    is24SparseRows (kron A B) := by
  intro i g
  simp only [kron]
  have hdiv : ∀ k : Nat, k < 4 → (g.val * 4 + k) / 4 = g.val := by
    intro k hk; omega
  have hmod : ∀ k : Nat, k < 4 → (g.val * 4 + k) % 4 = k := by
    intro k hk; omega
  have hf0 : (⟨(g.val * 4 + 0) / 4, div_lt_left_of_fin_mul (⟨g.val * 4 + 0, by omega⟩ : Fin (m * 4))⟩ : Fin m) = g :=
    Fin.ext (hdiv 0 (by omega))
  have hf1 : (⟨(g.val * 4 + 1) / 4, div_lt_left_of_fin_mul (⟨g.val * 4 + 1, by omega⟩ : Fin (m * 4))⟩ : Fin m) = g :=
    Fin.ext (hdiv 1 (by omega))
  have hf2 : (⟨(g.val * 4 + 2) / 4, div_lt_left_of_fin_mul (⟨g.val * 4 + 2, by omega⟩ : Fin (m * 4))⟩ : Fin m) = g :=
    Fin.ext (hdiv 2 (by omega))
  have hf3 : (⟨(g.val * 4 + 3) / 4, div_lt_left_of_fin_mul (⟨g.val * 4 + 3, by omega⟩ : Fin (m * 4))⟩ : Fin m) = g :=
    Fin.ext (hdiv 3 (by omega))
  have hm0 : (⟨(g.val * 4 + 0) % 4, Nat.mod_lt _ (pos_right_of_fin_mul (⟨g.val * 4 + 0, by omega⟩ : Fin (m * 4)))⟩ : Fin 4) = ⟨0, by omega⟩ :=
    Fin.ext (hmod 0 (by omega))
  have hm1 : (⟨(g.val * 4 + 1) % 4, Nat.mod_lt _ (pos_right_of_fin_mul (⟨g.val * 4 + 1, by omega⟩ : Fin (m * 4)))⟩ : Fin 4) = ⟨1, by omega⟩ :=
    Fin.ext (hmod 1 (by omega))
  have hm2 : (⟨(g.val * 4 + 2) % 4, Nat.mod_lt _ (pos_right_of_fin_mul (⟨g.val * 4 + 2, by omega⟩ : Fin (m * 4)))⟩ : Fin 4) = ⟨2, by omega⟩ :=
    Fin.ext (hmod 2 (by omega))
  have hm3 : (⟨(g.val * 4 + 3) % 4, Nat.mod_lt _ (pos_right_of_fin_mul (⟨g.val * 4 + 3, by omega⟩ : Fin (m * 4)))⟩ : Fin 4) = ⟨3, by omega⟩ :=
    Fin.ext (hmod 3 (by omega))
  rw [hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3]
  exact Nat.le_trans (nzCount4_scale_le _ _ _ _ _) (hB ⟨i.val % 4, Nat.mod_lt _ (pos_right_of_fin_mul i)⟩)

theorem kron_isDoubly24Sparse {m : Nat} (A : IntMat m m) (B : IntMat 4 4)
    (hBr : ∀ i : Fin 4, nzCount4 (B i ⟨0, by omega⟩) (B i ⟨1, by omega⟩)
                                 (B i ⟨2, by omega⟩) (B i ⟨3, by omega⟩) ≤ 2)
    (hBc : ∀ i : Fin 4, nzCount4 (transpose B i ⟨0, by omega⟩) (transpose B i ⟨1, by omega⟩)
                                 (transpose B i ⟨2, by omega⟩) (transpose B i ⟨3, by omega⟩) ≤ 2) :
    isDoubly24Sparse (kron A B) := by
  refine ⟨kron_is24SparseRows A B hBr, ?_⟩
  rw [transpose_kron]
  exact kron_is24SparseRows (transpose A) (transpose B) hBc

theorem isTernary_mul {x y : Int} (hx : isTernary x) (hy : isTernary y) :
    isTernary (x * y) := by
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> simp [isTernary]

theorem isDoubledE2M1_mul_ternary {x y : Int} (hx : isTernary x) (hy : isDoubledE2M1 y) :
    isDoubledE2M1 (x * y) := by
  rcases hx with rfl | rfl | rfl
  · rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [isDoubledE2M1]
  · simp [isDoubledE2M1]
  · simpa using hy

theorem kron_matEntriesIn_ternary {m1 n1 m2 n2 : Nat} {A : IntMat m1 n1} {B : IntMat m2 n2}
    (hA : matEntriesIn isTernary A) (hB : matEntriesIn isTernary B) :
    matEntriesIn isTernary (kron A B) := by
  intro i j
  exact isTernary_mul (hA _ _) (hB _ _)

theorem kron_matEntriesIn_e2m1 {m1 n1 m2 n2 : Nat} {A : IntMat m1 n1} {B : IntMat m2 n2}
    (hA : matEntriesIn isTernary A) (hB : matEntriesIn isDoubledE2M1 B) :
    matEntriesIn isDoubledE2M1 (kron A B) := by
  intro i j
  exact isDoubledE2M1_mul_ternary (hA _ _) (hB _ _)

/-! ### 5. Walsh–Hadamard Matrix Algebra -/

theorem bitParityFuel_eq (f1 f2 n : Nat) (h1 : n ≤ f1) (h2 : n ≤ f2) :
    bitParityFuel f1 n = bitParityFuel f2 n := by
  induction f1 generalizing f2 n with
  | zero =>
    have hn : n = 0 := by omega
    subst hn
    cases f2 <;> rfl
  | succ f1 ih =>
    cases f2 with
    | zero =>
      have hn : n = 0 := by omega
      subst hn
      rfl
    | succ f2 =>
      simp only [bitParityFuel]
      by_cases hn : n = 0
      · simp [hn]
      · simp only [hn, ↓reduceIte]
        rw [ih f2 (n / 2) (by omega) (by omega)]

theorem bitParity_mul_two_add (q r : Nat) (hr : r < 2) :
    bitParity (q * 2 + r) = xor (r == 1) (bitParity q) := by
  unfold bitParity
  by_cases h0 : q * 2 + r = 0
  · have hq : q = 0 := by omega
    have hr0 : r = 0 := by omega
    subst hq; subst hr0
    rfl
  · cases hqr : q * 2 + r with
    | zero => exact absurd hqr h0
    | succ m =>
      simp only [bitParityFuel]
      have hne : m + 1 ≠ 0 := Nat.succ_ne_zero m
      simp only [hne, ↓reduceIte]
      have hmod : (m + 1) % 2 = r := by omega
      have hdiv : (m + 1) / 2 = q := by omega
      rw [hmod, hdiv, bitParityFuel_eq m q q (by omega) (Nat.le_refl q)]

theorem and_mul_two_add (a b r s : Nat) (hr : r < 2) (hs : s < 2) :
    (a * 2 + r) &&& (b * 2 + s) = (a &&& b) * 2 + (r &&& s) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and]
  have hrs : r &&& s < 2 := by
    cases r with
    | zero => simp
    | succ r =>
      have : r = 0 := by omega
      subst this
      cases s with
      | zero => simp
      | succ s =>
        have : s = 0 := by omega
        subst this; simp
  cases k with
  | zero =>
    have h1 : ∀ x t, t < 2 → (x * 2 + t).testBit 0 = (t == 1) := by
      intro x t ht
      rw [Nat.testBit_zero]
      have : (x * 2 + t) % 2 = t := by omega
      rw [this]
      cases t with
      | zero => rfl
      | succ t =>
        have : t = 0 := by omega
        subst this; rfl
    rw [h1 a r hr, h1 b s hs, h1 (a &&& b) (r &&& s) hrs]
    cases r with
    | zero => simp
    | succ r =>
      have : r = 0 := by omega
      subst this
      cases s with
      | zero => simp
      | succ s =>
        have : s = 0 := by omega
        subst this; simp
  | succ k =>
    have h1 : ∀ x t, t < 2 → (x * 2 + t).testBit (k + 1) = x.testBit k := by
      intro x t ht
      rw [Nat.testBit_succ]
      have : (x * 2 + t) / 2 = x := by omega
      rw [this]
    rw [h1 a r hr, h1 b s hs, h1 (a &&& b) (r &&& s) hrs, Nat.testBit_and]

theorem walshEntry_mul_two_add (a b r s : Nat) (hr : r < 2) (hs : s < 2) :
    walshEntry (a * 2 + r) (b * 2 + s) = walshEntry a b * walshEntry r s := by
  unfold walshEntry
  rw [and_mul_two_add a b r s hr hs]
  have hrs : r &&& s < 2 := by
    cases r with
    | zero => simp
    | succ r =>
      have : r = 0 := by omega
      subst this
      cases s with
      | zero => simp
      | succ s =>
        have : s = 0 := by omega
        subst this; simp
  rw [bitParity_mul_two_add (a &&& b) (r &&& s) hrs]
  have hbp : bitParity (r &&& s) = ((r &&& s) == 1) := by
    cases r with
    | zero => simp [bitParity, bitParityFuel]
    | succ r =>
      have : r = 0 := by omega
      subst this
      cases s with
      | zero => simp [bitParity, bitParityFuel]
      | succ s =>
        have : s = 0 := by omega
        subst this; decide
  rw [hbp]
  cases bitParity (a &&& b) <;> cases ((r &&& s) == 1) <;> rfl

theorem walshEntry_mul_four_add (a b r s : Nat) (hr : r < 4) (hs : s < 4) :
    walshEntry (a * 4 + r) (b * 4 + s) = walshEntry a b * walshEntry r s := by
  have ha : a * 4 + r = (a * 2 + r / 2) * 2 + r % 2 := by omega
  have hb : b * 4 + s = (b * 2 + s / 2) * 2 + s % 2 := by omega
  have hr' : r = (r / 2) * 2 + r % 2 := by omega
  have hs' : s = (s / 2) * 2 + s % 2 := by omega
  rw [ha, hb, walshEntry_mul_two_add _ _ _ _ (by omega) (by omega),
      walshEntry_mul_two_add _ _ _ _ (by omega) (by omega)]
  have hrs : walshEntry r s = walshEntry (r / 2) (s / 2) * walshEntry (r % 2) (s % 2) := by
    have := walshEntry_mul_two_add (r / 2) (s / 2) (r % 2) (s % 2) (by omega) (by omega)
    rw [← hr', ← hs'] at this
    exact this
  rw [hrs, Int.mul_assoc]

theorem walshHadamard_succ (k : Nat) :
    walshHadamard (k + 1) = kron (walshHadamard k) (walshHadamardOf 2) := by
  funext i j
  simp only [walshHadamard, walshHadamardOf, kron]
  have hi : i.val = (i.val / 2) * 2 + i.val % 2 := by omega
  have hj : j.val = (j.val / 2) * 2 + j.val % 2 := by omega
  have h := walshEntry_mul_two_add (i.val / 2) (j.val / 2) (i.val % 2) (j.val % 2) (by omega) (by omega)
  rw [← hi, ← hj] at h
  exact h

theorem walshHadamardOf_mul_four (k : Nat) :
    walshHadamardOf (2 ^ k * 4) = kron (walshHadamard k) (walshHadamardOf 4) := by
  funext i j
  simp only [walshHadamard, walshHadamardOf, kron]
  have hi : i.val = (i.val / 4) * 4 + i.val % 4 := by omega
  have hj : j.val = (j.val / 4) * 4 + j.val % 4 := by omega
  have h := walshEntry_mul_four_add (i.val / 4) (j.val / 4) (i.val % 4) (j.val % 4) (by omega) (by omega)
  rw [← hi, ← hj] at h
  exact h

theorem walshHadamardOf_two_orthogonal : isOrthogonal (walshHadamardOf 2) 2 := by
  funext i j
  revert i j
  decide

theorem walshHadamardOf_two_rowOrthogonal : isRowOrthogonal (walshHadamardOf 2) 2 := by
  funext i j
  revert i j
  decide

theorem walshHadamard_orthogonal (k : Nat) :
    isOrthogonal (walshHadamard k) ((2 ^ k : Nat) : Int) := by
  induction k with
  | zero =>
    funext i j
    revert i j
    decide
  | succ k ih =>
    rw [walshHadamard_succ]
    have h := kron_isOrthogonal ih walshHadamardOf_two_orthogonal
    have hpow : (((2 ^ (k + 1) : Nat) : Int)) = ((2 ^ k : Nat) : Int) * 2 := by
      rw [Nat.pow_succ]; omega
    rw [hpow]
    exact h

theorem walshHadamard_rowOrthogonal (k : Nat) :
    isRowOrthogonal (walshHadamard k) ((2 ^ k : Nat) : Int) := by
  induction k with
  | zero =>
    funext i j
    revert i j
    decide
  | succ k ih =>
    rw [walshHadamard_succ]
    have h := kron_isRowOrthogonal ih walshHadamardOf_two_rowOrthogonal
    have hpow : (((2 ^ (k + 1) : Nat) : Int)) = ((2 ^ k : Nat) : Int) * 2 := by
      rw [Nat.pow_succ]; omega
    rw [hpow]
    exact h

theorem walshHadamard_ternary (k : Nat) : matEntriesIn isTernary (walshHadamard k) := by
  intro i j
  simp only [walshHadamard, walshHadamardOf, walshEntry, isTernary]
  cases bitParity (i.val &&& j.val) <;> simp

end SparseE2M1Rotations
