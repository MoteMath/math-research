/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions (`bitwise-smith-normal-form-lifter`)

Exact Smith Normal Form Bit-Slice Lifting Engine: definitions and sorry-free helper lemmas (pure Lean 4 `Init`, zero Mathlib).
-/

namespace SiliconSNF


-- ============================================================================
-- PART I: FINITE INTEGER MATRIX RING, CONSTRUCTIVE GL_n(Z), AND CANONICAL SNF
-- ============================================================================

/-- Finite integer sum over `Fin n`, defined recursively for clean induction. -/
def sumFin : (n : Nat) → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumFin n (fun i => f i.castSucc) + f (Fin.last n)

theorem sumFin_congr {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i = g i) :
    sumFin n f = sumFin n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumFin]
    rw [ih (fun i => h i.castSucc), h (Fin.last n)]

theorem sumFin_zero (n : Nat) : sumFin n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumFin, ih]

theorem sumFin_add {n : Nat} (f g : Fin n → Int) :
    sumFin n (fun i => f i + g i) = sumFin n f + sumFin n g := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih =>
    simp only [sumFin]
    rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc)]
    omega

theorem sumFin_neg {n : Nat} (f : Fin n → Int) :
    sumFin n (fun i => -f i) = -sumFin n f := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih =>
    simp only [sumFin]
    rw [ih (fun i => f i.castSucc)]
    omega

theorem sumFin_mul_left {n : Nat} (c : Int) (f : Fin n → Int) :
    sumFin n (fun i => c * f i) = c * sumFin n f := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih =>
    simp only [sumFin]
    rw [ih (fun i => f i.castSucc), Int.mul_add]

theorem sumFin_mul_right {n : Nat} (f : Fin n → Int) (c : Int) :
    sumFin n (fun i => f i * c) = sumFin n f * c := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih =>
    simp only [sumFin]
    rw [ih (fun i => f i.castSucc), Int.add_mul]

theorem sumFin_comm {m n : Nat} (f : Fin m → Fin n → Int) :
    sumFin m (fun i => sumFin n (fun j => f i j)) =
    sumFin n (fun j => sumFin m (fun i => f i j)) := by
  induction m with
  | zero =>
    simp only [sumFin]
    exact (sumFin_zero n).symm
  | succ m ih =>
    simp only [sumFin]
    rw [ih (fun i j => f i.castSucc j), ← sumFin_add]

theorem sumFin_single {n : Nat} (k : Fin n) (v : Int) :
    sumFin n (fun i => if i = k then v else 0) = v := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    simp only [sumFin]
    by_cases hk : k.1 < n
    · have hne : Fin.last n ≠ k := by
        intro h; rw [← h] at hk; exact Nat.lt_irrefl n hk
      simp only [hne, ↓reduceIte, Int.add_zero]
      have hsub : sumFin n (fun i : Fin n => if i.castSucc = k then v else 0) =
                  sumFin n (fun i : Fin n => if i = ⟨k.1, hk⟩ then v else 0) := by
        apply sumFin_congr; intro i
        have hiff : (i.castSucc = k) ↔ (i = ⟨k.1, hk⟩) := by
          constructor
          · intro h; apply Fin.ext; exact (congrArg Fin.val h : i.1 = k.1)
          · intro h; apply Fin.ext; exact (congrArg Fin.val h : i.1 = k.1)
        by_cases h : i = ⟨k.1, hk⟩
        · simp [h]
        · simp [h, hiff]
      rw [hsub, ih ⟨k.1, hk⟩]
    · have hkeq : k = Fin.last n := by
        apply Fin.ext; simp [Fin.last]; omega
      subst hkeq
      simp only [↓reduceIte]
      have hzero : sumFin n (fun i : Fin n => if i.castSucc = Fin.last n then v else 0) = 0 := by
        calc sumFin n (fun i : Fin n => if i.castSucc = Fin.last n then v else 0)
            = sumFin n (fun _ => 0) := by
              apply sumFin_congr; intro i
              have hne : i.castSucc ≠ Fin.last n := by
                intro h; have := congrArg Fin.val h; simp [Fin.last] at this; omega
              simp [hne]
          _ = 0 := sumFin_zero n
      rw [hzero, Int.zero_add]

theorem sumFin_single_eq {n : Nat} (k : Fin n) (f : Fin n → Int) :
    sumFin n (fun i => if i = k then f i else 0) = f k := by
  have h : sumFin n (fun i => if i = k then f i else 0) =
           sumFin n (fun i => if i = k then f k else 0) := by
    apply sumFin_congr; intro i
    by_cases hi : i = k <;> simp [hi]
  rw [h, sumFin_single]

theorem sumFin_single_symm {n : Nat} (k : Fin n) (f : Fin n → Int) :
    sumFin n (fun i => if k = i then f i else 0) = f k := by
  have h : sumFin n (fun i => if k = i then f i else 0) =
           sumFin n (fun i => if i = k then f i else 0) := by
    apply sumFin_congr; intro i
    by_cases hi : i = k
    · subst hi; simp
    · simp [hi, Ne.symm hi]
  rw [h, sumFin_single_eq]

/-- Splitting a sum over `m + k` into the first `m` terms and the remaining `k` terms. -/
theorem sumFin_split (m k : Nat) (f : Fin (m + k) → Int) :
    sumFin (m + k) f =
      sumFin m (fun i => f ⟨i.1, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right m k)⟩) +
      sumFin k (fun j => f ⟨m + j.1, Nat.add_lt_add_left j.isLt m⟩) := by
  induction k with
  | zero =>
    simp only [sumFin, Int.add_zero]
    apply sumFin_congr; intro i; rfl
  | succ k ih =>
    have hstep : sumFin (m + (k + 1)) f =
        sumFin (m + k) (fun i => f i.castSucc) + f (Fin.last (m + k)) := rfl
    rw [hstep, ih (fun i => f i.castSucc)]
    simp only [sumFin]
    have h1 : sumFin m (fun i => f (Fin.castSucc ⟨i.1, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right m k)⟩)) =
              sumFin m (fun i => f ⟨i.1, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right m (k + 1))⟩) := by
      apply sumFin_congr; intro i; rfl
    have h2 : sumFin k (fun j => f (Fin.castSucc ⟨m + j.1, Nat.add_lt_add_left j.isLt m⟩)) =
              sumFin k (fun j => f ⟨m + j.castSucc.1, Nat.add_lt_add_left j.castSucc.isLt m⟩) := by
      apply sumFin_congr; intro j; rfl
    have h3 : f (Fin.last (m + k)) = f ⟨m + (Fin.last k).1, Nat.add_lt_add_left (Fin.last k).isLt m⟩ := rfl
    rw [h1, h2, h3]
    omega

/-- Bijection structure on `Fin n`. -/
structure Perm (n : Nat) where
  toFun : Fin n → Fin n
  invFun : Fin n → Fin n
  left_inv : ∀ i, invFun (toFun i) = i
  right_inv : ∀ i, toFun (invFun i) = i

def Perm.id (n : Nat) : Perm n where
  toFun := fun i => i
  invFun := fun i => i
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

def Perm.symm {n : Nat} (p : Perm n) : Perm n where
  toFun := p.invFun
  invFun := p.toFun
  left_inv := p.right_inv
  right_inv := p.left_inv

def Perm.comp {n : Nat} (p q : Perm n) : Perm n where
  toFun := fun i => p.toFun (q.toFun i)
  invFun := fun i => q.invFun (p.invFun i)
  left_inv := fun i => by simp [p.left_inv, q.left_inv]
  right_inv := fun i => by simp [p.right_inv, q.right_inv]

/-- Transposition swapping two elements of `Fin n`. -/
def Perm.swap {n : Nat} (a b : Fin n) : Perm n where
  toFun := fun i => if i = a then b else if i = b then a else i
  invFun := fun i => if i = a then b else if i = b then a else i
  left_inv := fun i => by
    by_cases h1 : i = a
    · subst h1; by_cases h2 : b = i <;> simp [h2]
    · by_cases h2 : i = b
      · subst h2; simp [h1]
      · simp [h1, h2]
  right_inv := fun i => by
    by_cases h1 : i = a
    · subst h1; by_cases h2 : b = i <;> simp [h2]
    · by_cases h2 : i = b
      · subst h2; simp [h1]
      · simp [h1, h2]

abbrev Mat (n : Nat) := Fin n → Fin n → Int

def matId (n : Nat) : Mat n := fun i j => if i = j then 1 else 0

def matZero (n : Nat) : Mat n := fun _ _ => 0

def onesMat (n : Nat) : Mat n := fun _ _ => 1

def diagMat {n : Nat} (d : Fin n → Int) : Mat n := fun i j => if i = j then d i else 0

def diagMatNat {n : Nat} (d : Fin n → Nat) : Mat n := fun i j => if i = j then (d i : Int) else 0

def matAdd {n : Nat} (A B : Mat n) : Mat n := fun i j => A i j + B i j

def matSub {n : Nat} (A B : Mat n) : Mat n := fun i j => A i j - B i j

def matNeg {n : Nat} (A : Mat n) : Mat n := fun i j => -A i j

def matSmul {n : Nat} (c : Int) (A : Mat n) : Mat n := fun i j => c * A i j

def matTranspose {n : Nat} (A : Mat n) : Mat n := fun i j => A j i

def matMul {n : Nat} (A B : Mat n) : Mat n := fun i j => sumFin n (fun k => A i k * B k j)

def matVec {n : Nat} (A : Mat n) (v : Fin n → Int) : Fin n → Int :=
  fun i => sumFin n (fun j => A i j * v j)

theorem matExt {n : Nat} {A B : Mat n} (h : ∀ i j, A i j = B i j) : A = B := by
  funext i j; exact h i j

theorem matMul_assoc {n : Nat} (A B C : Mat n) :
    matMul (matMul A B) C = matMul A (matMul B C) := by
  apply matExt; intro i j
  simp only [matMul]
  calc sumFin n (fun k => sumFin n (fun r => A i r * B r k) * C k j)
      = sumFin n (fun k => sumFin n (fun r => (A i r * B r k) * C k j)) := by
        apply sumFin_congr; intro k; rw [← sumFin_mul_right]
    _ = sumFin n (fun r => sumFin n (fun k => (A i r * B r k) * C k j)) := sumFin_comm _
    _ = sumFin n (fun r => sumFin n (fun k => A i r * (B r k * C k j))) := by
        apply sumFin_congr; intro r; apply sumFin_congr; intro k; exact Int.mul_assoc _ _ _
    _ = sumFin n (fun r => A i r * sumFin n (fun k => B r k * C k j)) := by
        apply sumFin_congr; intro r; rw [sumFin_mul_left]

theorem matId_mul {n : Nat} (A : Mat n) : matMul (matId n) A = A := by
  apply matExt; intro i j
  simp only [matMul, matId]
  have h : sumFin n (fun k => (if i = k then 1 else 0) * A k j) =
           sumFin n (fun k => if i = k then A k j else 0) := by
    apply sumFin_congr; intro k; by_cases hk : i = k <;> simp [hk]
  rw [h, sumFin_single_symm]

theorem mul_matId {n : Nat} (A : Mat n) : matMul A (matId n) = A := by
  apply matExt; intro i j
  simp only [matMul, matId]
  have h : sumFin n (fun k => A i k * (if k = j then 1 else 0)) =
           sumFin n (fun k => if k = j then A i k else 0) := by
    apply sumFin_congr; intro k; by_cases hk : k = j <;> simp [hk]
  rw [h, sumFin_single_eq]

theorem matZero_mul {n : Nat} (A : Mat n) : matMul (matZero n) A = matZero n := by
  apply matExt; intro i j
  simp only [matMul, matZero, Int.zero_mul]; exact sumFin_zero n

theorem mul_matZero {n : Nat} (A : Mat n) : matMul A (matZero n) = matZero n := by
  apply matExt; intro i j
  simp only [matMul, matZero, Int.mul_zero]; exact sumFin_zero n

theorem matMul_neg {n : Nat} (A B : Mat n) : matMul A (matNeg B) = matNeg (matMul A B) := by
  apply matExt; intro i j
  simp only [matMul, matNeg]
  rw [← sumFin_neg]
  apply sumFin_congr; intro k; exact Int.mul_neg _ _

theorem neg_matMul {n : Nat} (A B : Mat n) : matMul (matNeg A) B = matNeg (matMul A B) := by
  apply matExt; intro i j
  simp only [matMul, matNeg]
  rw [← sumFin_neg]
  apply sumFin_congr; intro k; exact Int.neg_mul _ _

theorem matTranspose_mul {n : Nat} (A B : Mat n) :
    matTranspose (matMul A B) = matMul (matTranspose B) (matTranspose A) := by
  apply matExt; intro i j
  simp only [matTranspose, matMul]
  apply sumFin_congr; intro k; exact Int.mul_comm _ _

/-- A unimodular integer matrix `U ∈ GL_n(Z)`, witnessed constructively by its exact
    two-sided integer inverse `inv`. No determinant library or rational arithmetic needed! -/
structure Unimod (n : Nat) where
  val : Mat n
  inv : Mat n
  mul_inv : matMul val inv = matId n
  inv_mul : matMul inv val = matId n

def Unimod.id (n : Nat) : Unimod n where
  val := matId n
  inv := matId n
  mul_inv := matId_mul _
  inv_mul := matId_mul _

def Unimod.mul {n : Nat} (U V : Unimod n) : Unimod n where
  val := matMul U.val V.val
  inv := matMul V.inv U.inv
  mul_inv := by
    rw [matMul_assoc, ← matMul_assoc V.val V.inv U.inv, V.mul_inv, matId_mul, U.mul_inv]
  inv_mul := by
    rw [matMul_assoc, ← matMul_assoc U.inv U.val V.val, U.inv_mul, matId_mul, V.inv_mul]

def Unimod.symm {n : Nat} (U : Unimod n) : Unimod n where
  val := U.inv
  inv := U.val
  mul_inv := U.inv_mul
  inv_mul := U.mul_inv

def Unimod.transpose {n : Nat} (U : Unimod n) : Unimod n where
  val := matTranspose U.val
  inv := matTranspose U.inv
  mul_inv := by
    rw [← matTranspose_mul, U.inv_mul]
    apply matExt; intro i j; simp only [matTranspose, matId]
    by_cases h : j = i
    · subst h; simp
    · simp [h, Ne.symm h]
  inv_mul := by
    rw [← matTranspose_mul, U.mul_inv]
    apply matExt; intro i j; simp only [matTranspose, matId]
    by_cases h : j = i
    · subst h; simp
    · simp [h, Ne.symm h]

/-- Unimodular matrix associated to a permutation `p : Perm n`: `(P_p)_{i,j} = δ_{p(i), j}`. -/
def permMat {n : Nat} (p : Perm n) : Mat n :=
  fun i j => if p.toFun i = j then 1 else 0

theorem permMat_mul_left {n : Nat} (p : Perm n) (A : Mat n) :
    matMul (permMat p) A = fun i j => A (p.toFun i) j := by
  apply matExt; intro i j
  simp only [matMul, permMat]
  have h : sumFin n (fun k => (if p.toFun i = k then 1 else 0) * A k j) =
           sumFin n (fun k => if p.toFun i = k then A k j else 0) := by
    apply sumFin_congr; intro k; by_cases hk : p.toFun i = k <;> simp [hk]
  rw [h, sumFin_single_symm]

theorem mul_permMat_symm {n : Nat} (A : Mat n) (p : Perm n) :
    matMul A (permMat p.symm) = fun i j => A i (p.toFun j) := by
  apply matExt; intro i j
  simp only [matMul, permMat]
  have h : sumFin n (fun k => A i k * (if p.symm.toFun k = j then 1 else 0)) =
           sumFin n (fun k => if k = p.toFun j then A i k else 0) := by
    apply sumFin_congr; intro k
    have hiff : p.symm.toFun k = j ↔ k = p.toFun j := by
      simp only [Perm.symm]
      constructor
      · intro h; rw [← h, p.right_inv]
      · intro h; rw [h, p.left_inv]
    by_cases hk : k = p.toFun j
    · subst hk; simp [Perm.symm, p.left_inv]
    · simp [hk, mt hiff.mp hk]
  rw [h, sumFin_single_eq]

def permUnimod {n : Nat} (p : Perm n) : Unimod n where
  val := permMat p
  inv := permMat p.symm
  mul_inv := by
    rw [permMat_mul_left]
    apply matExt; intro i j; simp only [permMat, Perm.symm, matId, p.left_inv]
  inv_mul := by
    rw [permMat_mul_left]
    apply matExt; intro i j; simp only [permMat, Perm.symm, matId, p.right_inv]

/-- Diagonal sign-flip unimodular matrix (`s i ∈ {-1, +1}`). -/
def signUnimod {n : Nat} (s : Fin n → Int) (hs : ∀ i, s i * s i = 1) : Unimod n where
  val := diagMat s
  inv := diagMat s
  mul_inv := by
    apply matExt; intro i j; simp only [matMul, diagMat, matId]
    have h : sumFin n (fun k => (if i = k then s i else 0) * (if k = j then s k else 0)) =
             sumFin n (fun k => if i = k then (if k = j then s i * s k else 0) else 0) := by
      apply sumFin_congr; intro k
      by_cases h1 : i = k
      · subst h1; by_cases h2 : i = j <;> simp [h2]
      · simp [h1]
    rw [h, sumFin_single_symm]
    by_cases hij : i = j
    · subst hij; simp [hs]
    · simp [hij]
  inv_mul := by
    apply matExt; intro i j; simp only [matMul, diagMat, matId]
    have h : sumFin n (fun k => (if i = k then s i else 0) * (if k = j then s k else 0)) =
             sumFin n (fun k => if i = k then (if k = j then s i * s k else 0) else 0) := by
      apply sumFin_congr; intro k
      by_cases h1 : i = k
      · subst h1; by_cases h2 : i = j <;> simp [h2]
      · simp [h1]
    rw [h, sumFin_single_symm]
    by_cases hij : i = j
    · subst hij; simp [hs]
    · simp [hij]

/-- Two `n × n` integer matrices are unimodularly equivalent iff `U * A * V = B` for `U, V ∈ GL_n(Z)`. -/
def UnimodEquiv {n : Nat} (A B : Mat n) : Prop :=
  ∃ U V : Unimod n, matMul (matMul U.val A) V.val = B

theorem UnimodEquiv.symm {n : Nat} {A B : Mat n} (h : UnimodEquiv A B) : UnimodEquiv B A := by
  rcases h with ⟨U, V, hUV⟩
  refine ⟨U.symm, V.symm, ?_⟩
  rw [← hUV]
  simp only [Unimod.symm]
  rw [← matMul_assoc, ← matMul_assoc, U.inv_mul, matId_mul, matMul_assoc, V.mul_inv, mul_matId]

theorem UnimodEquiv.trans {n : Nat} {A B C : Mat n}
    (h1 : UnimodEquiv A B) (h2 : UnimodEquiv B C) : UnimodEquiv A C := by
  rcases h1 with ⟨U1, V1, h1⟩
  rcases h2 with ⟨U2, V2, h2⟩
  refine ⟨Unimod.mul U2 U1, Unimod.mul V1 V2, ?_⟩
  simp only [Unimod.mul]
  calc matMul (matMul (matMul U2.val U1.val) A) (matMul V1.val V2.val)
      = matMul (matMul U2.val (matMul (matMul U1.val A) V1.val)) V2.val := by
        simp only [matMul_assoc]
    _ = matMul (matMul U2.val B) V2.val := by rw [h1]
    _ = C := h2

/-- Canonical Smith Normal Form predicate:
    `M` is unimodularly equivalent to `diag(d_0, ..., d_{n-1})` with `d_i ∈ Nat`
    and canonical divisibility chain `d_0 | d_1 | ... | d_{n-1}`. -/
def HasSNF {n : Nat} (M : Mat n) (d : Fin n → Nat) : Prop :=
  UnimodEquiv M (diagMatNat d) ∧
  ∀ (i : Fin n) (h : i.1 + 1 < n), d i ∣ d ⟨i.1 + 1, h⟩

-- ============================================================================
-- Algebraic Soundness of HasSNF (Cokernel / Kernel / Unimodularity Semantics)
-- ============================================================================

def castMat {m n : Nat} (h : m = n) (A : Mat m) : Mat n :=
  fun i j => A ⟨i.1, h ▸ i.isLt⟩ ⟨j.1, h ▸ j.isLt⟩

def castUnimod {m n : Nat} (h : m = n) (U : Unimod m) : Unimod n := by
  subst h; exact U

def blockMat {m : Nat} (A B C D : Mat m) : Mat (m + m) :=
  fun i j =>
    if hi : i.1 < m then
      if hj : j.1 < m then A ⟨i.1, hi⟩ ⟨j.1, hj⟩
      else B ⟨i.1, hi⟩ ⟨j.1 - m, by omega⟩
    else
      if hj : j.1 < m then C ⟨i.1 - m, by omega⟩ ⟨j.1, hj⟩
      else D ⟨i.1 - m, by omega⟩ ⟨j.1 - m, by omega⟩

theorem blockMat_id (m : Nat) :
    blockMat (matId m) (matZero m) (matZero m) (matId m) = matId (m + m) := by
  apply matExt; intro i j
  simp only [blockMat, matId, matZero]
  split
  · rename_i hi
    split
    · rename_i hj
      by_cases hij : i = j
      · subst hij; simp
      · have hne : (⟨i.1, hi⟩ : Fin m) ≠ ⟨j.1, hj⟩ := fun h => hij (Fin.ext (Fin.mk.inj h))
        simp [hij, hne]
    · rename_i hj
      have hij : i ≠ j := fun h => hj (h ▸ hi)
      simp [hij]
  · rename_i hi
    split
    · rename_i hj
      have hij : i ≠ j := fun h => hi (h.symm ▸ hj)
      simp [hij]
    · rename_i hj
      by_cases hij : i = j
      · subst hij; simp
      · have hne : (⟨i.1 - m, by omega⟩ : Fin m) ≠ ⟨j.1 - m, by omega⟩ := by
          intro h; have hval := Fin.mk.inj h; exact hij (Fin.ext (by omega))
        simp [hij, hne]

theorem blockMat_mul {m : Nat} (A1 B1 C1 D1 A2 B2 C2 D2 : Mat m) :
    matMul (blockMat A1 B1 C1 D1) (blockMat A2 B2 C2 D2) =
      blockMat (matAdd (matMul A1 A2) (matMul B1 C2))
               (matAdd (matMul A1 B2) (matMul B1 D2))
               (matAdd (matMul C1 A2) (matMul D1 C2))
               (matAdd (matMul C1 B2) (matMul D1 D2)) := by
  apply matExt; intro i j
  simp only [matMul]
  rw [sumFin_split m m]
  simp only [blockMat, matAdd, matMul]
  split
  · rename_i hi
    split
    · rename_i hj
      congr 1
      · apply sumFin_congr; intro k; simp [k.isLt]
      · apply sumFin_congr; intro k
        have hk : ¬(m + k.1 < m) := by omega
        have hsub : m + k.1 - m = k.1 := by omega
        simp [hk, hsub]
    · rename_i hj
      congr 1
      · apply sumFin_congr; intro k; simp [k.isLt]
      · apply sumFin_congr; intro k
        have hk : ¬(m + k.1 < m) := by omega
        have hsub : m + k.1 - m = k.1 := by omega
        simp [hk, hsub]
  · rename_i hi
    split
    · rename_i hj
      congr 1
      · apply sumFin_congr; intro k; simp [k.isLt]
      · apply sumFin_congr; intro k
        have hk : ¬(m + k.1 < m) := by omega
        have hsub : m + k.1 - m = k.1 := by omega
        simp [hk, hsub]
    · rename_i hj
      congr 1
      · apply sumFin_congr; intro k; simp [k.isLt]
      · apply sumFin_congr; intro k
        have hk : ¬(m + k.1 < m) := by omega
        have hsub : m + k.1 - m = k.1 := by omega
        simp [hk, hsub]

theorem matAdd_zero_right {n : Nat} (A : Mat n) : matAdd A (matZero n) = A := by
  apply matExt; intro i j; simp [matAdd, matZero]

theorem matAdd_zero_left {n : Nat} (A : Mat n) : matAdd (matZero n) A = A := by
  apply matExt; intro i j; simp [matAdd, matZero]

theorem matAdd_neg_self {n : Nat} (A : Mat n) : matAdd A (matNeg A) = matZero n := by
  apply matExt; intro i j; simp only [matAdd, matNeg, matZero]; omega

theorem matAdd_self_neg {n : Nat} (A : Mat n) : matAdd (matNeg A) A = matZero n := by
  apply matExt; intro i j; simp only [matAdd, matNeg, matZero]; omega

/-- Block-diagonal unimodular matrix `diag(U, V) ∈ GL_{2m}(Z)`. -/
def blockDiagUnimod {m : Nat} (U V : Unimod m) : Unimod (m + m) where
  val := blockMat U.val (matZero m) (matZero m) V.val
  inv := blockMat U.inv (matZero m) (matZero m) V.inv
  mul_inv := by
    simp only [blockMat_mul, U.mul_inv, V.mul_inv, matZero_mul, mul_matZero,
               matAdd_zero_right, matAdd_zero_left, blockMat_id]
  inv_mul := by
    simp only [blockMat_mul, U.inv_mul, V.inv_mul, matZero_mul, mul_matZero,
               matAdd_zero_right, matAdd_zero_left, blockMat_id]

/-- Block upper-triangular unimodular matrix `[[A, B], [0, D]] ∈ GL_{2m}(Z)` whenever
    `A, D ∈ GL_m(Z)`, with explicit exact integer inverse `[[A⁻¹, -A⁻¹ B D⁻¹], [0, D⁻¹]]`. -/
def blockUpperTriUnimod {m : Nat} (A : Unimod m) (B : Mat m) (D : Unimod m) : Unimod (m + m) where
  val := blockMat A.val B (matZero m) D.val
  inv := blockMat A.inv (matNeg (matMul (matMul A.inv B) D.inv)) (matZero m) D.inv
  mul_inv := by
    rw [blockMat_mul]
    have h12 : matAdd (matMul A.val (matNeg (matMul (matMul A.inv B) D.inv))) (matMul B D.inv) = matZero m := by
      rw [matMul_neg, ← matMul_assoc A.val (matMul A.inv B) D.inv, ← matMul_assoc A.val A.inv B,
          A.mul_inv, matId_mul, matAdd_self_neg]
    simp only [A.mul_inv, D.mul_inv, mul_matZero, matZero_mul, matAdd_zero_right, matAdd_zero_left,
               h12, blockMat_id]
  inv_mul := by
    rw [blockMat_mul]
    have h12 : matAdd (matMul A.inv B) (matMul (matNeg (matMul (matMul A.inv B) D.inv)) D.val) = matZero m := by
      rw [neg_matMul, matMul_assoc (matMul A.inv B) D.inv D.val, D.inv_mul, mul_matId, matAdd_neg_self]
    simp only [A.inv_mul, D.inv_mul, mul_matZero, matZero_mul, matAdd_zero_right, matAdd_zero_left,
               h12, blockMat_id]

/-- Elementary lower-block unimodular matrix `[[I, 0], [Q, I]] ∈ GL_{2m}(Z)`. -/
def blockLowerElemUnimod {m : Nat} (Q : Mat m) : Unimod (m + m) where
  val := blockMat (matId m) (matZero m) Q (matId m)
  inv := blockMat (matId m) (matZero m) (matNeg Q) (matId m)
  mul_inv := by
    simp only [blockMat_mul, matId_mul, mul_matId, mul_matZero, matZero_mul,
               matAdd_zero_right, matAdd_zero_left, matAdd_neg_self, blockMat_id]
  inv_mul := by
    simp only [blockMat_mul, matId_mul, mul_matId, mul_matZero, matZero_mul,
               matAdd_zero_right, matAdd_zero_left, matAdd_self_neg, blockMat_id]

/-- Elementary upper-block unimodular matrix `[[I, R], [0, I]] ∈ GL_{2m}(Z)`. -/
def blockUpperElemUnimod {m : Nat} (R : Mat m) : Unimod (m + m) where
  val := blockMat (matId m) R (matZero m) (matId m)
  inv := blockMat (matId m) (matNeg R) (matZero m) (matId m)
  mul_inv := by
    simp only [blockMat_mul, matId_mul, mul_matId, mul_matZero, matZero_mul,
               matAdd_zero_right, matAdd_zero_left, matAdd_self_neg, blockMat_id]
  inv_mul := by
    simp only [blockMat_mul, matId_mul, mul_matId, mul_matZero, matZero_mul,
               matAdd_zero_right, matAdd_zero_left, matAdd_neg_self, blockMat_id]

/-- LSB bit-stride permutation on `m + m`:
    maps lower block `(0, q)` to even index `2*q` and upper block `(1, q)` to odd index `2*q + 1`. -/
def lsbPerm (m : Nat) : Perm (m + m) where
  toFun := fun i =>
    if hi : i.1 < m then ⟨2 * i.1, by omega⟩
    else ⟨2 * (i.1 - m) + 1, by omega⟩
  invFun := fun j =>
    if j.1 % 2 = 0 then ⟨j.1 / 2, by omega⟩
    else ⟨m + j.1 / 2, by omega⟩
  left_inv := fun i => by
    apply Fin.ext
    split
    · rename_i hi
      have h0 : 2 * i.1 % 2 = 0 := by omega
      simp [h0]
    · rename_i hi
      simp; omega
  right_inv := fun j => by
    apply Fin.ext
    split
    · rename_i hj
      have hlt : j.1 / 2 < m := by omega
      simp [hlt]; omega
    · rename_i hj
      have hge : ¬(m + j.1 / 2 < m) := by omega
      simp [hge]; omega

/-- Conjugating any `(m + m) × (m + m)` matrix by `lsbPerm m` decomposes it into its exact
    2×2 LSB block matrix `(a, b) ↦ (x, y ↦ M(2x + a, 2y + b))`. -/
theorem lsbPerm_conj_eq_blockMat {m : Nat} (M : Mat (m + m)) :
    matMul (matMul (permMat (lsbPerm m)) M) (permMat (lsbPerm m).symm) =
      blockMat
        (fun x y => M ⟨2 * x.1, by omega⟩ ⟨2 * y.1, by omega⟩)
        (fun x y => M ⟨2 * x.1, by omega⟩ ⟨2 * y.1 + 1, by omega⟩)
        (fun x y => M ⟨2 * x.1 + 1, by omega⟩ ⟨2 * y.1, by omega⟩)
        (fun x y => M ⟨2 * x.1 + 1, by omega⟩ ⟨2 * y.1 + 1, by omega⟩) := by
  rw [permMat_mul_left, mul_permMat_symm]
  apply matExt; intro i j
  simp only [blockMat, lsbPerm]
  split <;> split <;> rfl

-- ----------------------------------------------------------------------------
-- LIFTER 3: Constructive 2x2 Bezout Unimodular Lifter
-- ----------------------------------------------------------------------------

/-- Self-contained Extended Euclidean Algorithm over `Nat` producing Bezout coefficients `(u, v)`
    with `(Nat.gcd a b : Int) = (a : Int) * u + (b : Int) * v`. -/
def extGcd (a b : Nat) : Int × Int :=
  if _h : b = 0 then (1, 0)
  else
    let uv := extGcd b (a % b)
    (uv.2, uv.1 - ((a / b : Nat) : Int) * uv.2)
termination_by b
decreasing_by exact Nat.mod_lt a (Nat.pos_of_ne_zero _h)

/-- Embed a 2×2 integer matrix `[[m00, m01], [m10, m11]]` at distinct coordinates `(p, q)`
    and identity elsewhere. -/
def emb2Mat {n : Nat} (p q : Fin n) (m00 m01 m10 m11 : Int) : Mat n :=
  fun i j =>
    if i = p then (if j = p then m00 else if j = q then m01 else 0)
    else if i = q then (if j = p then m10 else if j = q then m11 else 0)
    else if i = j then 1 else 0

/-- Elementary unimodular matrix subtracting row 0 from rows `1..m-1`. -/
def subRow0Unimod (m : Nat) : Unimod m where
  val := fun i j => if i = j then 1 else if j.1 = 0 then -1 else 0
  inv := fun i j => if i = j then 1 else if j.1 = 0 then 1 else 0
  mul_inv := by
    apply matExt; intro i j
    simp only [matMul, matId]
    by_cases hi0 : i.1 = 0
    · have hsum : sumFin m (fun k => (if i = k then 1 else if k.1 = 0 then -1 else 0) *
                                      (if k = j then 1 else if j.1 = 0 then 1 else 0)) =
                  sumFin m (fun k => if i = k then (if i = j then 1 else 0) else 0) := by
        apply sumFin_congr; intro k
        by_cases hik : i = k
        · subst hik
          by_cases hij : i = j
          · subst hij; simp
          · have hj0 : j.1 ≠ 0 := fun h => hij (Fin.ext (hi0.trans h.symm))
            simp [hij, hj0]
        · have hk0 : k.1 ≠ 0 := fun h => hik (Fin.ext (hi0.trans h.symm))
          simp [hik, hk0]
      rw [hsum, sumFin_single_symm]
    · have hm : 0 < m := Nat.pos_of_ne_zero (fun h => by omega)
      let z0 : Fin m := ⟨0, hm⟩
      have hne0 : i ≠ z0 := fun h => hi0 (congrArg Fin.val h)
      have hsum : sumFin m (fun k => (if i = k then 1 else if k.1 = 0 then -1 else 0) *
                                      (if k = j then 1 else if j.1 = 0 then 1 else 0)) =
                  sumFin m (fun k =>
                    (if k = i then (if i = j then 1 else if j.1 = 0 then 1 else 0) else 0) +
                    (if k = z0 then -(if z0 = j then 1 else if j.1 = 0 then 1 else 0) else 0)) := by
        apply sumFin_congr; intro k
        by_cases hki : k = i
        · subst hki; simp [hne0]
        · by_cases hkz : k = z0
          · subst hkz; have hz0 : z0.1 = 0 := rfl; simp [hne0, Ne.symm hne0, hz0]
          · have hk0 : k.1 ≠ 0 := fun h => hkz (Fin.ext h)
            simp [Ne.symm hki, hki, hkz, hk0]
      rw [hsum, sumFin_add, sumFin_single, sumFin_single]
      by_cases hij : i = j
      · subst hij; simp [hi0, Ne.symm hne0]
      · by_cases hj0 : j.1 = 0
        · have hzj : z0 = j := Fin.ext hj0.symm
          simp [hij, hj0, hzj]
        · have hzj : z0 ≠ j := fun h => hj0 (congrArg Fin.val h.symm)
          simp [hij, hj0, hzj]
  inv_mul := by
    apply matExt; intro i j
    simp only [matMul, matId]
    by_cases hi0 : i.1 = 0
    · have hsum : sumFin m (fun k => (if i = k then 1 else if k.1 = 0 then 1 else 0) *
                                      (if k = j then 1 else if j.1 = 0 then -1 else 0)) =
                  sumFin m (fun k => if i = k then (if i = j then 1 else 0) else 0) := by
        apply sumFin_congr; intro k
        by_cases hik : i = k
        · subst hik
          by_cases hij : i = j
          · subst hij; simp
          · have hj0 : j.1 ≠ 0 := fun h => hij (Fin.ext (hi0.trans h.symm))
            simp [hij, hj0]
        · have hk0 : k.1 ≠ 0 := fun h => hik (Fin.ext (hi0.trans h.symm))
          simp [hik, hk0]
      rw [hsum, sumFin_single_symm]
    · have hm : 0 < m := Nat.pos_of_ne_zero (fun h => by omega)
      let z0 : Fin m := ⟨0, hm⟩
      have hne0 : i ≠ z0 := fun h => hi0 (congrArg Fin.val h)
      have hsum : sumFin m (fun k => (if i = k then 1 else if k.1 = 0 then 1 else 0) *
                                      (if k = j then 1 else if j.1 = 0 then -1 else 0)) =
                  sumFin m (fun k =>
                    (if k = i then (if i = j then 1 else if j.1 = 0 then -1 else 0) else 0) +
                    (if k = z0 then (if z0 = j then 1 else if j.1 = 0 then -1 else 0) else 0)) := by
        apply sumFin_congr; intro k
        by_cases hki : k = i
        · subst hki; simp [hne0]
        · by_cases hkz : k = z0
          · subst hkz; have hz0 : z0.1 = 0 := rfl; simp [hne0, Ne.symm hne0, hz0]
          · have hk0 : k.1 ≠ 0 := fun h => hkz (Fin.ext h)
            simp [Ne.symm hki, hki, hkz, hk0]
      rw [hsum, sumFin_add, sumFin_single, sumFin_single]
      by_cases hij : i = j
      · subst hij; simp [hi0, Ne.symm hne0]
      · by_cases hj0 : j.1 = 0
        · have hzj : z0 = j := Fin.ext hj0.symm
          simp [hij, hj0, hzj]
        · have hzj : z0 ≠ j := fun h => hj0 (congrArg Fin.val h.symm)
          simp [hij, hj0, hzj]

def finDiv {m n : Nat} (i : Fin (m * n)) : Fin m :=
  ⟨i.1 / n, Nat.div_lt_of_lt_mul (Nat.mul_comm m n ▸ i.isLt)⟩

def finMod {m n : Nat} (i : Fin (m * n)) : Fin n :=
  have hn : 0 < n := by
    cases n with
    | zero =>
      have : m * 0 = 0 := Nat.mul_zero m
      have := i.isLt
      omega
    | succ _ => exact Nat.zero_lt_succ _
  ⟨i.1 % n, Nat.mod_lt _ hn⟩

def finPair {m n : Nat} (a : Fin m) (b : Fin n) : Fin (m * n) :=
  ⟨a.1 * n + b.1, by
    have h1 : a.1 * n + b.1 < a.1 * n + n := Nat.add_lt_add_left b.isLt (a.1 * n)
    have h2 : (a.1 + 1) * n ≤ m * n := Nat.mul_le_mul_right n a.isLt
    rw [Nat.add_mul, Nat.one_mul] at h2
    omega⟩

theorem finDiv_finPair {m n : Nat} (a : Fin m) (b : Fin n) :
    finDiv (finPair a b) = a := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) b.isLt
  apply Fin.ext; simp only [finDiv, finPair]
  rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt b.isLt, Nat.zero_add]

theorem finMod_finPair {m n : Nat} (a : Fin m) (b : Fin n) :
    finMod (finPair a b) = b := by
  apply Fin.ext; simp only [finMod, finPair]
  rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.isLt]

/-- Kronecker product `A ⊗ B : Mat (m * n)` indexed in row-major order `(q, r) ↔ q * n + r`. -/
def kronMat {m n : Nat} (A : Mat m) (B : Mat n) : Mat (m * n) :=
  fun i j => A (finDiv i) (finDiv j) * B (finMod i) (finMod j)

theorem sumFin_cast {p q : Nat} (h : p = q) (f : Fin p → Int) :
    sumFin p f = sumFin q (fun i => f ⟨i.1, h ▸ i.isLt⟩) := by
  subst h; rfl

theorem sumFin_mul_grid (m n : Nat) (f : Fin (m * n) → Int) :
    sumFin (m * n) f = sumFin m (fun a => sumFin n (fun b => f (finPair a b))) := by
  induction m with
  | zero =>
    rw [sumFin_cast (Nat.zero_mul n)]; rfl
  | succ m ih =>
    have hmn : (m + 1) * n = m * n + n := by rw [Nat.add_mul, Nat.one_mul]
    rw [sumFin_cast hmn, sumFin_split]
    rw [ih (fun i => f ⟨i.1, by omega⟩)]
    simp only [sumFin, Fin.last]
    congr 1

theorem kronMat_mul {m n : Nat} (A1 A2 : Mat m) (B1 B2 : Mat n) :
    matMul (kronMat A1 B1) (kronMat A2 B2) = kronMat (matMul A1 A2) (matMul B1 B2) := by
  apply matExt; intro i j
  simp only [matMul, kronMat]
  rw [sumFin_mul_grid m n]
  have h1 : sumFin m (fun a => sumFin n (fun b =>
      (A1 (finDiv i) (finDiv (finPair a b)) * B1 (finMod i) (finMod (finPair a b))) *
      (A2 (finDiv (finPair a b)) (finDiv j) * B2 (finMod (finPair a b)) (finMod j)))) =
      sumFin m (fun a => (A1 (finDiv i) a * A2 a (finDiv j)) *
        sumFin n (fun b => B1 (finMod i) b * B2 b (finMod j))) := by
    apply sumFin_congr; intro a
    rw [← sumFin_mul_left]
    apply sumFin_congr; intro b
    rw [finDiv_finPair, finMod_finPair]
    rw [Int.mul_assoc, ← Int.mul_assoc (B1 _ _), Int.mul_comm (B1 _ _) (A2 _ _),
        Int.mul_assoc (A2 _ _), ← Int.mul_assoc]
  rw [h1, sumFin_mul_right]

theorem kronMat_id (m n : Nat) : kronMat (matId m) (matId n) = matId (m * n) := by
  apply matExt; intro i j
  simp only [kronMat, matId]
  by_cases hij : i = j
  · subst hij; simp
  · simp only [hij, ↓reduceIte]
    by_cases hdiv : finDiv i = finDiv j
    · have hmod : finMod i ≠ finMod j := by
        intro hm; apply hij; apply Fin.ext
        have hd : i.1 / n = j.1 / n := congrArg Fin.val hdiv
        have hmd : i.1 % n = j.1 % n := congrArg Fin.val hm
        rw [← Nat.div_add_mod i.1 n, ← Nat.div_add_mod j.1 n, hd, hmd]
      simp [hmod]
    · simp [hdiv]

def kronUnimod {m n : Nat} (U : Unimod m) (V : Unimod n) : Unimod (m * n) where
  val := kronMat U.val V.val
  inv := kronMat U.inv V.inv
  mul_inv := by rw [kronMat_mul, U.mul_inv, V.mul_inv, kronMat_id]
  inv_mul := by rw [kronMat_mul, U.inv_mul, V.inv_mul, kronMat_id]

/-- Extend a permutation on `Fin n` to `Fin (n + 1)` by fixing `Fin.last n`. -/
def Perm.extendLast {n : Nat} (p : Perm n) : Perm (n + 1) where
  toFun := fun i => if h : i.1 < n then (p.toFun ⟨i.1, h⟩).castSucc else Fin.last n
  invFun := fun i => if h : i.1 < n then (p.invFun ⟨i.1, h⟩).castSucc else Fin.last n
  left_inv := fun i => by
    apply Fin.ext
    split
    · rename_i h
      simp [p.left_inv]
    · rename_i h
      simp [Fin.last]; omega
  right_inv := fun i => by
    apply Fin.ext
    split
    · rename_i h
      simp [p.right_inv]
    · rename_i h
      simp [Fin.last]; omega

/-- Find index of a maximum element of `f : Fin (n + 1) → Nat`. -/
def argMax : (n : Nat) → (Fin (n + 1) → Nat) → Fin (n + 1)
  | 0, _ => ⟨0, by omega⟩
  | n + 1, f =>
    let m := argMax n (fun i => f i.castSucc)
    if f m.castSucc ≤ f (Fin.last (n + 1)) then Fin.last (n + 1) else m.castSucc

/-- Constructive Selection-Sort Permutation on `Fin n` sorting `f : Fin n → Nat` into
    monotone non-decreasing order! -/
def sortPerm : (n : Nat) → (Fin n → Nat) → Perm n
  | 0, _ => Perm.id 0
  | n + 1, f =>
    let k := argMax n f
    let sw := Perm.swap k (Fin.last n)
    let f' : Fin n → Nat := fun i => f (sw.toFun i.castSucc)
    Perm.comp sw (Perm.extendLast (sortPerm n f'))

/-- Count of elements in `Fin n` satisfying predicate `P`. -/
def countFin : (n : Nat) → (Fin n → Bool) → Nat
  | 0, _ => 0
  | n + 1, P => countFin n (fun i => P i.castSucc) + if P (Fin.last n) then 1 else 0

/-- Binary popcount (Hamming weight) of a natural number. -/
def popcount (n : Nat) : Nat :=
  if _h : n = 0 then 0 else n % 2 + popcount (n / 2)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero _h) (by decide)

/-- Exact number of binary carries generated in adding `x + y + c` across `k` bit-positions. -/
def carriesK : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _ => 0
  | k + 1, x, y, c =>
    let cout := (x % 2 + y % 2 + c) / 2
    cout + carriesK k (x / 2) (y / 2) cout

theorem pow2_add_self (k : Nat) : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by
  rw [Nat.pow_succ]; omega

theorem carriesK_succ_bit (k x y a b c : Nat) (ha : a < 2) (hb : b < 2) :
    carriesK (k + 1) (2 * x + a) (2 * y + b) c =
    (a + b + c) / 2 + carriesK k x y ((a + b + c) / 2) := by
  simp only [carriesK]
  have hma : (2 * x + a) % 2 = a := by omega
  have hmb : (2 * y + b) % 2 = b := by omega
  have hda : (2 * x + a) / 2 = x := by omega
  have hdb : (2 * y + b) / 2 = y := by omega
  rw [hma, hmb, hda, hdb]

-- ============================================================================
-- THEOREM 1 (FLAGSHIP NON-KRONECKER #1):
-- BINARY CARRY-PARITY, CARRY-COUPLING UNIMODULARITY, PARITY DICHOTOMY, AND
-- TWO-PARAMETER AFFINE CARRY-PARITY EXACT SNF FAMILY (∀ k ≥ 1, ∀ a b : Int)
-- ============================================================================

/-- Binary carry-parity matrix `C_k^(c)(x, y) = carries(x, y, c) mod 2 ∈ {0, 1}`. -/
def carryParMat (k c : Nat) : Mat (2 ^ k) :=
  fun x y => ((carriesK k x.1 y.1 c % 2 : Nat) : Int)

/-- Carry-coupling matrix `S_k = C_k^(0) + C_k^(1) - J_k ∈ {-1, 0, 1}^{2^k × 2^k}`. -/
def carryCouplingMat (k : Nat) : Mat (2 ^ k) :=
  fun x y => carryParMat k 0 x y + carryParMat k 1 x y - 1

/-- Carry-difference matrix `R_k = C_k^(1) - C_k^(0)`. -/
def carryDiffMat (k : Nat) : Mat (2 ^ k) :=
  fun x y => carryParMat k 1 x y - carryParMat k 0 x y

/-- Two-parameter affine carry-parity matrix `M_k(a, b)(x, y) = a + b · (carries(x, y) mod 2)`. -/
def affineCarryParMat (k : Nat) (a b : Int) : Mat (2 ^ k) :=
  fun x y => a + b * carryParMat k 0 x y

/-- Binary carry-parity sign matrix `H_k^carry(x, y) = (-1)^{carries(x, y)}`. -/
def carrySignMat (k : Nat) : Mat (2 ^ k) :=
  fun x y => if carriesK k x.1 y.1 0 % 2 = 0 then 1 else -1

/-- Negation of a unimodular matrix is unimodular. -/
def Unimod.neg {n : Nat} (U : Unimod n) : Unimod n where
  val := matNeg U.val
  inv := matNeg U.inv
  mul_inv := by
    rw [neg_matMul, matMul_neg, U.mul_inv]
    apply matExt; intro i j; simp [matNeg]
  inv_mul := by
    rw [neg_matMul, matMul_neg, U.inv_mul]
    apply matExt; intro i j; simp [matNeg]

/-- Key Coupled-State Block-Triangular Elimination Identity for `S_{k+1}`:
    `E · (P_lsb · S_{k+1} · P_lsb^T) · E = [[S_k, -R_k], [0, -S_k]]`
    where `E = [[I, 0], [-I, I]] ∈ GL_{2^{k+1}}(Z)`. -/
theorem carryCouplingMat_block_tri (k : Nat) :
    let E := blockLowerElemUnimod (matNeg (matId (2 ^ k)))
    let P := permUnimod (lsbPerm (2 ^ k))
    matMul (matMul (matMul E.val P.val) (castMat (pow2_add_self k).symm (carryCouplingMat (k + 1))))
           (matMul P.inv E.val) =
    blockMat (carryCouplingMat k) (matNeg (carryDiffMat k))
             (matZero (2 ^ k)) (matNeg (carryCouplingMat k)) := by
  intro E P
  have hPS : matMul (matMul P.val (castMat (pow2_add_self k).symm (carryCouplingMat (k + 1)))) P.inv =
      blockMat (matSub (carryCouplingMat k) (carryDiffMat k))
               (matNeg (carryDiffMat k))
               (matNeg (carryDiffMat k))
               (matSub (matNeg (carryCouplingMat k)) (carryDiffMat k)) := by
    simp only [P, permUnimod]
    rw [lsbPerm_conj_eq_blockMat]
    apply matExt; intro i j
    simp only [blockMat, castMat, carryCouplingMat, carryDiffMat, carryParMat, matSub, matNeg]
    split <;> split
    · have h0 := carriesK_succ_bit k i.1 j.1 0 0 0 (by decide) (by decide)
      have h1 := carriesK_succ_bit k i.1 j.1 0 0 1 (by decide) (by decide)
      simp only [Nat.add_zero] at h0 h1; rw [h0, h1]
      simp only [show (0 + 0 + 0) / 2 = 0 by rfl, Nat.zero_add]; omega
    · have h0 := carriesK_succ_bit k i.1 (j.1 - 2 ^ k) 0 1 0 (by decide) (by decide)
      have h1 := carriesK_succ_bit k i.1 (j.1 - 2 ^ k) 0 1 1 (by decide) (by decide)
      simp only [Nat.add_zero] at h0 h1; rw [h0, h1]
      simp only [show (0 + 1 + 0) / 2 = 0 by rfl, show (0 + 1 + 1) / 2 = 1 by rfl, Nat.zero_add]; omega
    · have h0 := carriesK_succ_bit k (i.1 - 2 ^ k) j.1 1 0 0 (by decide) (by decide)
      have h1 := carriesK_succ_bit k (i.1 - 2 ^ k) j.1 1 0 1 (by decide) (by decide)
      simp only [Nat.add_zero] at h0 h1; rw [h0, h1]
      simp only [show (1 + 0 + 0) / 2 = 0 by rfl, show (1 + 0 + 1) / 2 = 1 by rfl, Nat.zero_add]; omega
    · have h0 := carriesK_succ_bit k (i.1 - 2 ^ k) (j.1 - 2 ^ k) 1 1 0 (by decide) (by decide)
      have h1 := carriesK_succ_bit k (i.1 - 2 ^ k) (j.1 - 2 ^ k) 1 1 1 (by decide) (by decide)
      rw [h0, h1]
      simp only [show (1 + 1 + 0) / 2 = 1 by rfl]; omega
  calc matMul (matMul (matMul E.val P.val) (castMat (pow2_add_self k).symm (carryCouplingMat (k + 1))))
              (matMul P.inv E.val)
      = matMul (matMul E.val (matMul (matMul P.val (castMat (pow2_add_self k).symm (carryCouplingMat (k + 1)))) P.inv))
               E.val := by simp only [matMul_assoc]
    _ = matMul (matMul E.val (blockMat (matSub (carryCouplingMat k) (carryDiffMat k))
               (matNeg (carryDiffMat k)) (matNeg (carryDiffMat k))
               (matSub (matNeg (carryCouplingMat k)) (carryDiffMat k)))) E.val := by rw [hPS]
    _ = blockMat (carryCouplingMat k) (matNeg (carryDiffMat k))
                 (matZero (2 ^ k)) (matNeg (carryCouplingMat k)) := by
        simp only [E, blockLowerElemUnimod, blockMat_mul, matId_mul, mul_matId, matZero_mul,
                   mul_matZero, neg_matMul, matMul_neg, matAdd_zero_right, matAdd_zero_left]
        apply matExt; intro i j
        simp only [blockMat, matAdd, matSub, matNeg, matZero]
        split <;> split <;> omega

/-- **Theorem 1.0 (Constructive Unimodularity of Carry-Coupling Matrix `S_k ∈ GL_{2^k}(Z)`)**:
    For EVERY `k ≥ 0`, `S_k = C_k^(0) + C_k^(1) - J_k` is unimodular over `Z`, witnessed by an
    explicit recursive inverse built purely from block-triangular bit-slice lifting! -/
def carryCouplingUnimod : (k : Nat) → { U : Unimod (2 ^ k) // U.val = carryCouplingMat k }
  | 0 =>
    ⟨{ val := carryCouplingMat 0
       inv := carryCouplingMat 0
       mul_inv := by
         apply matExt; intro i j
         have hi : i = ⟨0, by decide⟩ := Fin.ext (by omega)
         have hj : j = ⟨0, by decide⟩ := Fin.ext (by omega)
         subst hi; subst hj
         simp [matMul, sumFin, carryCouplingMat, carryParMat, carriesK, matId]
       inv_mul := by
         apply matExt; intro i j
         have hi : i = ⟨0, by decide⟩ := Fin.ext (by omega)
         have hj : j = ⟨0, by decide⟩ := Fin.ext (by omega)
         subst hi; subst hj
         simp [matMul, sumFin, carryCouplingMat, carryParMat, carriesK, matId] }, rfl⟩
  | k + 1 =>
    let ⟨Sk, hSk⟩ := carryCouplingUnimod k
    let T : Unimod (2 ^ k + 2 ^ k) :=
      blockUpperTriUnimod Sk (matNeg (carryDiffMat k)) Sk.neg
    let E := blockLowerElemUnimod (matNeg (matId (2 ^ k)))
    let P := permUnimod (lsbPerm (2 ^ k))
    -- From (E P) S_{k+1} (P⁻¹ E) = T, we get S_{k+1} = (E P)⁻¹ T (P⁻¹ E)⁻¹
    let L := Unimod.mul E P
    let R := Unimod.mul P.symm E
    let Ucast : Unimod (2 ^ k + 2 ^ k) := Unimod.mul (Unimod.mul L.symm T) R.symm
    let U : Unimod (2 ^ (k + 1)) := castUnimod (pow2_add_self k) Ucast
    ⟨U, by
      have htri := carryCouplingMat_block_tri k
      have hTval : T.val = blockMat (carryCouplingMat k) (matNeg (carryDiffMat k))
                                    (matZero (2 ^ k)) (matNeg (carryCouplingMat k)) := by
        simp only [T, blockUpperTriUnimod, Unimod.neg, hSk]
      have hLTR : matMul (matMul L.val (castMat (pow2_add_self k).symm (carryCouplingMat (k + 1)))) R.val = T.val := by
        rw [hTval]; exact htri
      have hUcast_val : Ucast.val = castMat (pow2_add_self k).symm (carryCouplingMat (k + 1)) := by
        simp only [Ucast, Unimod.mul, Unimod.symm]
        rw [← hLTR]
        calc matMul (matMul L.inv (matMul (matMul L.val (castMat (pow2_add_self k).symm (carryCouplingMat (k + 1)))) R.val)) R.inv
            = matMul (matMul (matMul L.inv L.val) (castMat (pow2_add_self k).symm (carryCouplingMat (k + 1)))) (matMul R.val R.inv) := by
              simp only [matMul_assoc]
          _ = castMat (pow2_add_self k).symm (carryCouplingMat (k + 1)) := by
              rw [L.inv_mul, R.mul_inv, matId_mul, mul_matId]
      -- Transport equality through castUnimod (pow2_add_self k)
      have hcast_eq : ∀ (m n : Nat) (h : m = n) (A : Unimod m) (B : Mat n),
          A.val = castMat h.symm B → (castUnimod h A).val = B := by
        intro m n h A B hAB; subst h; exact hAB
      exact hcast_eq _ _ (pow2_add_self k) Ucast (carryCouplingMat (k + 1)) hUcast_val⟩

/-- Canonical SNF diagonal of `M_k(a, b) = a + b · (carries(x, y) mod 2)`:
    `[gcd(|a|, |b|), |b|, |b|, ..., |b|, lcm(|a|, |b|)]`. -/
def affineCarrySNFDiag (k : Nat) (a b : Int) (i : Fin (2 ^ k)) : Nat :=
  if i.1 = 0 then Nat.gcd a.natAbs b.natAbs
  else if i.1 + 1 = 2 ^ k then Nat.lcm a.natAbs b.natAbs
  else b.natAbs

/-- Untruncated Add-XOR matrix `T_k^(1)(x, y) = (x + y + 1) ^^^ x`. -/
def T1Mat (k : Nat) : Mat (2 ^ k) :=
  fun x y => (((x.1 + y.1 + 1) ^^^ x.1 : Nat) : Int)

/-- Add-XOR Carry-Difference matrix `D_k(x, y) = ((x + y + 1) ^^^ x) - ((x + y) ^^^ x)`. -/
def DMat (k : Nat) : Mat (2 ^ k) :=
  fun x y => (((x.1 + y.1 + 1) ^^^ x.1 : Nat) : Int) - (((x.1 + y.1) ^^^ x.1 : Nat) : Int)

/-- Truncated k-bit Add-XOR matrix `T_{k,mod}^(1)(x, y) = ((x + y + 1) ^^^ x) % 2^k`. -/
def T1ModMat (k : Nat) : Mat (2 ^ k) :=
  fun x y => ((((x.1 + y.1 + 1) ^^^ x.1) % 2 ^ k : Nat) : Int)

/-- Truncated k-bit Add-XOR Carry-Difference matrix `D_{k,mod}(x, y)`. -/
def DModMat (k : Nat) : Mat (2 ^ k) :=
  fun x y => ((((x.1 + y.1 + 1) ^^^ x.1) % 2 ^ k : Nat) : Int) -
             ((((x.1 + y.1) ^^^ x.1) % 2 ^ k : Nat) : Int)

/-- Universal stabilizing SNF diagonal for `D_k` and `T_k^(1)`:
    `1, 4, 8, 8, 16, 16, 16, 16, 32, ...` (`d(0) = 1`, `d(i) = 2^{⌊log2 i⌋ + 2}` for `i ≥ 1`). -/
def addXorSNFDiag (i : Nat) : Nat :=
  if i = 0 then 1 else 2 ^ (Nat.log2 i + 2)

/-- Anti-diagonal permutation on `Fin m`: `i ↦ m - 1 - i`. -/
def antiDiagPerm (m : Nat) : Perm m where
  toFun := fun i => ⟨m - 1 - i.1, by omega⟩
  invFun := fun i => ⟨m - 1 - i.1, by omega⟩
  left_inv := fun i => Fin.ext (by dsimp; omega)
  right_inv := fun i => Fin.ext (by dsimp; omega)

/-- Upper-bidiagonal unimodular difference matrix `Δ_n` (`Δ_{i,i}=1, Δ_{i,i+1}=-1`)
    with explicit exact integer inverse (upper-triangular all-ones prefix-sum matrix). -/
def deltaUnimod (n : Nat) : Unimod n where
  val := fun i j => if i = j then 1 else if i.1 + 1 = j.1 then -1 else 0
  inv := fun i j => if i.1 ≤ j.1 then 1 else 0
  mul_inv := by
    apply matExt; intro i j
    simp only [matMul, matId]
    by_cases hlast : i.1 + 1 < n
    · let next : Fin n := ⟨i.1 + 1, hlast⟩
      have hne : i ≠ next := by intro h; have := congrArg Fin.val h; simp [next] at this
      have hsum : sumFin n (fun k => (if i = k then (1 : Int) else if i.1 + 1 = k.1 then -1 else 0) *
                                      (if k.1 ≤ j.1 then 1 else 0)) =
                  sumFin n (fun k => (if k = i then (if i.1 ≤ j.1 then (1 : Int) else 0) else 0) +
                                     (if k = next then -(if next.1 ≤ j.1 then (1 : Int) else 0) else 0)) := by
        apply sumFin_congr; intro k
        by_cases hki : k = i
        · subst hki; simp [hne]
        · by_cases hkn : k = next
          · subst hkn; have hnv : next.1 = i.1 + 1 := rfl; simp [hne, Ne.symm hne, hnv]
          · have hkval : i.1 + 1 ≠ k.1 := fun h => hkn (Fin.ext h.symm)
            simp [Ne.symm hki, hki, hkn, hkval]
      rw [hsum, sumFin_add, sumFin_single, sumFin_single]
      simp only [next]
      by_cases hij : i = j
      · subst hij
        have hgt : ¬(i.1 + 1 ≤ i.1) := by omega
        simp [hgt]
      · have hne_val : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
        by_cases hle : i.1 ≤ j.1
        · have hle2 : i.1 + 1 ≤ j.1 := by omega
          simp [hij, hle, hle2]
        · have hle2 : ¬(i.1 + 1 ≤ j.1) := by omega
          simp [hij, hle, hle2]
    · have hsum : sumFin n (fun k => (if i = k then (1 : Int) else if i.1 + 1 = k.1 then -1 else 0) *
                                      (if k.1 ≤ j.1 then 1 else 0)) =
                  sumFin n (fun k => if k = i then (if i.1 ≤ j.1 then (1 : Int) else 0) else 0) := by
        apply sumFin_congr; intro k
        by_cases hki : k = i
        · subst hki; simp
        · have hkval : i.1 + 1 ≠ k.1 := by omega
          simp [Ne.symm hki, hki, hkval]
      rw [hsum, sumFin_single]
      by_cases hij : i = j
      · subst hij; simp
      · have hgt : ¬(i.1 ≤ j.1) := by have := Fin.val_ne_of_ne hij; omega
        simp [hij, hgt]
  inv_mul := by
    apply matExt; intro i j
    simp only [matMul, matId]
    by_cases hj0 : 0 < j.1
    · let prev : Fin n := ⟨j.1 - 1, by omega⟩
      have hne : prev ≠ j := by intro h; have := congrArg Fin.val h; simp [prev] at this; omega
      have hsum : sumFin n (fun k => (if i.1 ≤ k.1 then (1 : Int) else 0) *
                                      (if k = j then 1 else if k.1 + 1 = j.1 then -1 else 0)) =
                  sumFin n (fun k => (if k = j then (if i.1 ≤ j.1 then (1 : Int) else 0) else 0) +
                                     (if k = prev then -(if i.1 ≤ prev.1 then (1 : Int) else 0) else 0)) := by
        apply sumFin_congr; intro k
        by_cases hkj : k = j
        · subst hkj; simp [Ne.symm hne]
        · by_cases hkp : k = prev
          · subst hkp; have hadd : prev.1 + 1 = j.1 := by simp [prev]; omega
            simp [hne, hadd]
          · have hkval : k.1 + 1 ≠ j.1 := fun h => hkp (Fin.ext (by simp [prev]; omega))
            simp [hkj, hkp, hkval]
      rw [hsum, sumFin_add, sumFin_single, sumFin_single]
      simp only [prev]
      by_cases hij : i = j
      · subst hij; simp; omega
      · have hne_val : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
        by_cases hle : i.1 ≤ j.1
        · have hle2 : i.1 ≤ j.1 - 1 := by omega
          simp [hij, hle, hle2]
        · have hle2 : ¬(i.1 ≤ j.1 - 1) := by omega
          simp [hij, hle, hle2]
    · have hjz : j.1 = 0 := by omega
      have hsum : sumFin n (fun k => (if i.1 ≤ k.1 then (1 : Int) else 0) *
                                      (if k = j then 1 else if k.1 + 1 = j.1 then -1 else 0)) =
                  sumFin n (fun k => if k = j then (if i.1 ≤ j.1 then (1 : Int) else 0) else 0) := by
        apply sumFin_congr; intro k
        by_cases hkj : k = j
        · subst hkj; simp
        · have hkval : k.1 + 1 ≠ j.1 := by omega
          simp [hkj, hkval]
      rw [hsum, sumFin_single]
      by_cases hij : i = j
      · subst hij; simp
      · have hgt : ¬(i.1 ≤ j.1) := by have := Fin.val_ne_of_ne hij; omega
        simp [hij, hgt]

/-- Weighted bitwise-AND matrix: `(weightedAndMat k w)(x, y) = ∑_{r=0}^{k-1} w(r) · bit_r(x & y)`. -/
def weightedAndMat : (k : Nat) → (Nat → Nat) → Mat (2 ^ k)
  | 0, _ => matZero (2 ^ 0)
  | k + 1, w =>
    castMat (pow2_add_self k)
      (blockMat (weightedAndMat k w) (weightedAndMat k w)
                (weightedAndMat k w)
                (matAdd (weightedAndMat k w) (matSmul (w k : Int) (onesMat (2 ^ k)))))

/-- Parametric multiplicative bitwise matrix `K_k(q)(x, y) = q ^ popcount(x &&& y)`. -/
def qPopAndMat (k : Nat) (q : Int) : Mat (2 ^ k) :=
  fun x y => q ^ popcount (x.1 &&& y.1)

/-- 2×2 base matrix `[[1, 1], [1, q]]`. -/
def baseQMat (q : Int) : Mat 2 :=
  fun i j => if i.1 = 1 ∧ j.1 = 1 then q else 1

/-- Self-contained binomial coefficient `binom k j = C(k, j)`. -/
def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

def carriesMod3Mat2 : Mat 4 :=
  fun x y => ((carriesK 2 x.1 y.1 0 % 3 : Nat) : Int)

def nonDivSchurMat : Mat (2 + 2) :=
  blockMat (diagMatNat (fun i : Fin 2 => if i.1 = 0 then 1 else 4))
           (matZero 2)
           (matSmul 2 (matId 2))
           (matZero 2)

end SiliconSNF
