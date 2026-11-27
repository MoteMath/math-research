/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions (`f2-rank-bitwise-matrix-automata`)

Exact F2-Rank and Corank Block-Elimination Automaton Engine: definitions and sorry-free helper lemmas (pure Lean 4 `Init`, zero Mathlib).
-/

namespace F2RankAutomaton


/-! ## Section 1: Pure-Silicon F_2 Vector & Matrix Algebra -/

abbrev Vec (n : Nat) := Fin n → Bool

abbrev Mat (m n : Nat) := Fin m → Fin n → Bool

def vzero (n : Nat) : Vec n := fun _ => false

def vxor {n : Nat} (u v : Vec n) : Vec n := fun i => xor (u i) (v i)

@[simp] theorem xor_false_left (b : Bool) : xor false b = b := by cases b <;> rfl
@[simp] theorem xor_false_right (b : Bool) : xor b false = b := by cases b <;> rfl
@[simp] theorem xor_self (b : Bool) : xor b b = false := by cases b <;> rfl
theorem xor_comm (a b : Bool) : xor a b = xor b a := by cases a <;> cases b <;> rfl

theorem xor_assoc (a b c : Bool) : xor (xor a b) c = xor a (xor b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem and_xor_left (a b c : Bool) : (a && xor b c) = xor (a && b) (a && c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem and_xor_right (a b c : Bool) : (xor a b && c) = xor (a && c) (b && c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem vxor_zero_right {n : Nat} (v : Vec n) : vxor v (vzero n) = v := by
  funext i; simp [vxor, vzero]

theorem vxor_self {n : Nat} (v : Vec n) : vxor v v = vzero n := by
  funext i; simp [vxor, vzero]

theorem vxor_assoc {n : Nat} (u v w : Vec n) : vxor (vxor u v) w = vxor u (vxor v w) := by
  funext i; exact xor_assoc (u i) (v i) (w i)

def foldXor : (n : Nat) → (Fin n → Bool) → Bool
  | 0, _ => false
  | n + 1, f => xor (foldXor n (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
                    (f ⟨n, Nat.lt_succ_self n⟩)

theorem foldXor_congr {n : Nat} {f g : Fin n → Bool} (h : ∀ i, f i = g i) :
    foldXor n f = foldXor n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [foldXor]
    rw [ih (fun i => h _), h]

theorem foldXor_zero (n : Nat) : foldXor n (fun _ => false) = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [foldXor, ih]

theorem foldXor_xor (n : Nat) (f g : Fin n → Bool) :
    foldXor n (fun i => xor (f i) (g i)) = xor (foldXor n f) (foldXor n g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [foldXor]
    rw [ih]
    cases foldXor n (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) <;>
    cases foldXor n (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) <;>
    cases f ⟨n, Nat.lt_succ_self n⟩ <;> cases g ⟨n, Nat.lt_succ_self n⟩ <;> rfl

theorem foldXor_and_left (n : Nat) (b : Bool) (f : Fin n → Bool) :
    foldXor n (fun i => b && f i) = (b && foldXor n f) := by
  induction n with
  | zero => cases b <;> rfl
  | succ n ih =>
    simp only [foldXor]
    rw [ih, ← and_xor_left]

theorem foldXor_and_right (n : Nat) (f : Fin n → Bool) (b : Bool) :
    foldXor n (fun i => f i && b) = (foldXor n f && b) := by
  induction n with
  | zero => cases b <;> rfl
  | succ n ih =>
    simp only [foldXor]
    rw [ih, ← and_xor_right]

theorem foldXor_swap (m n : Nat) (f : Fin m → Fin n → Bool) :
    foldXor m (fun i => foldXor n (fun j => f i j)) =
    foldXor n (fun j => foldXor m (fun i => f i j)) := by
  induction m with
  | zero =>
    simp only [foldXor]
    symm
    exact foldXor_zero n
  | succ m ih =>
    simp only [foldXor]
    rw [ih, ← foldXor_xor]

theorem foldXor_single {n : Nat} (k : Fin n) (f : Fin n → Bool)
    (h : ∀ i, i ≠ k → f i = false) :
    foldXor n f = f k := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    simp only [foldXor]
    by_cases hk : k.val = n
    · have hk_eq : k = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hk
      rw [hk_eq]
      have h0 : foldXor n (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) = false := by
        rw [foldXor_congr (g := fun _ => false)]
        · exact foldXor_zero n
        · intro i
          apply h
          intro heq
          have : i.val = n := by
            have := congrArg Fin.val heq
            simpa [hk] using this
          omega
      rw [h0, xor_false_left]
    · have hklt : k.val < n := by omega
      have hlast : f ⟨n, Nat.lt_succ_self n⟩ = false := by
        apply h
        intro heq
        exact hk (congrArg Fin.val heq).symm
      rw [hlast, xor_false_right]
      exact ih ⟨k.val, hklt⟩ (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) (fun i hi => by
        apply h
        intro heq
        apply hi
        have hv : i.val = k.val := congrArg Fin.val heq
        exact Fin.ext hv)

def vdot {n : Nat} (u v : Vec n) : Bool := foldXor n (fun i => u i && v i)

def matVec {m n : Nat} (M : Mat m n) (v : Vec n) : Vec m :=
  fun i => foldXor n (fun j => M i j && v j)

def matMul {m k n : Nat} (A : Mat m k) (B : Mat k n) : Mat m n :=
  fun i j => foldXor k (fun t => A i t && B t j)

def matId (n : Nat) : Mat n n := fun i j => i.val == j.val

def matZero (m n : Nat) : Mat m n := fun _ _ => false

def matDiagRank (m n r : Nat) : Mat m n :=
  fun i j => (i.val == j.val) && (i.val < r)

theorem matVec_xor {m n : Nat} (M : Mat m n) (u v : Vec n) :
    matVec M (vxor u v) = vxor (matVec M u) (matVec M v) := by
  funext i
  simp only [matVec, vxor]
  rw [← foldXor_xor]
  apply foldXor_congr
  intro j
  exact and_xor_left (M i j) (u j) (v j)

theorem matVec_mul {m k n : Nat} (A : Mat m k) (B : Mat k n) (v : Vec n) :
    matVec (matMul A B) v = matVec A (matVec B v) := by
  funext i
  simp only [matVec, matMul]
  have h1 : foldXor n (fun j => foldXor k (fun t => A i t && B t j) && v j) =
            foldXor n (fun j => foldXor k (fun t => A i t && (B t j && v j))) := by
    apply foldXor_congr
    intro j
    rw [← foldXor_and_right]
    apply foldXor_congr
    intro t
    cases A i t <;> cases B t j <;> cases v j <;> rfl
  rw [h1, foldXor_swap]
  apply foldXor_congr
  intro t
  exact foldXor_and_left n (A i t) (fun j => B t j && v j)

theorem matVec_id {n : Nat} (v : Vec n) : matVec (matId n) v = v := by
  funext i
  simp only [matVec, matId]
  rw [foldXor_single i]
  · simp
  · intro j hj
    have hne : (i.val == j.val) = false := by
      simp only [beq_eq_false_iff_ne]
      intro heq
      exact hj (Fin.ext heq.symm)
    simp [hne]

theorem matVec_diagRank {m n r : Nat} (hr : r ≤ n) (v : Vec n) :
    matVec (matDiagRank m n r) v =
    fun i => if h : i.val < r then v ⟨i.val, Nat.lt_of_lt_of_le h hr⟩ else false := by
  funext i
  simp only [matVec, matDiagRank]
  by_cases hi : i.val < r
  · have hi_n : i.val < n := Nat.lt_of_lt_of_le hi hr
    rw [foldXor_single ⟨i.val, hi_n⟩]
    · simp [hi]
    · intro j hj
      have hne : (i.val == j.val) = false := by
        simp only [beq_eq_false_iff_ne]
        intro heq
        exact hj (Fin.ext heq.symm)
      simp [hne]
  · simp only [hi, decide_false, Bool.and_false, Bool.false_and, ↓reduceDIte]
    exact foldXor_zero n

/-! ## Section 2: Invertible F_2-Linear Equivalences, Rank, Nullity & Kernel Cardinality -/

structure LinEquiv (m n : Nat) where
  toFun : Vec m → Vec n
  invFun : Vec n → Vec m
  map_xor : ∀ u v, toFun (vxor u v) = vxor (toFun u) (toFun v)
  left_inv : ∀ u, invFun (toFun u) = u
  right_inv : ∀ v, toFun (invFun v) = v

namespace LinEquiv

theorem inv_map_xor {m n : Nat} (e : LinEquiv m n) (u v : Vec n) :
    e.invFun (vxor u v) = vxor (e.invFun u) (e.invFun v) := by
  have h := e.map_xor (e.invFun u) (e.invFun v)
  rw [e.right_inv, e.right_inv] at h
  have := congrArg e.invFun h
  rw [e.left_inv] at this
  exact this.symm

def refl (n : Nat) : LinEquiv n n where
  toFun := id
  invFun := id
  map_xor _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def symm {m n : Nat} (e : LinEquiv m n) : LinEquiv n m where
  toFun := e.invFun
  invFun := e.toFun
  map_xor := e.inv_map_xor
  left_inv := e.right_inv
  right_inv := e.left_inv

def trans {a b c : Nat} (e1 : LinEquiv a b) (e2 : LinEquiv b c) : LinEquiv a c where
  toFun u := e2.toFun (e1.toFun u)
  invFun w := e1.invFun (e2.invFun w)
  map_xor u v := by rw [e1.map_xor, e2.map_xor]
  left_inv u := by rw [e2.left_inv, e1.left_inv]
  right_inv w := by rw [e1.right_inv, e2.right_inv]

def cast {m n : Nat} (h : m = n) : LinEquiv m n := by
  cases h; exact refl m

def ofMatInv {n : Nat} (A B : Mat n n)
    (hAB : matMul A B = matId n) (hBA : matMul B A = matId n) : LinEquiv n n where
  toFun := matVec A
  invFun := matVec B
  map_xor := matVec_xor A
  left_inv u := by rw [← matVec_mul, hBA, matVec_id]
  right_inv v := by rw [← matVec_mul, hAB, matVec_id]

end LinEquiv


/-- Canonical F_2-rank predicate: M is linearly equivalent to the rank-r normal form J(m,n,r). -/
structure HasRank {m n : Nat} (M : Mat m n) (r : Nat) : Prop where
  le_rows : r ≤ m
  le_cols : r ≤ n
  equiv : ∃ (P : LinEquiv m m) (Q : LinEquiv n n),
    ∀ v, P.toFun (matVec M (Q.toFun v)) = matVec (matDiagRank m n r) v

def HasNullity {m n : Nat} (M : Mat m n) (ν : Nat) : Prop :=
  ν ≤ n ∧ HasRank M (n - ν)

/-! ### Exact 2^n Vector Enumeration & Kernel Cardinality Soundness -/

def vecToNat : {n : Nat} → Vec n → Nat
  | 0, _ => 0
  | n + 1, v =>
    vecToNat (fun i : Fin n => v ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) +
    if v ⟨n, Nat.lt_succ_self n⟩ then 2 ^ n else 0

def natToVec : (n : Nat) → Nat → Vec n
  | 0, _ => fun i => Fin.elim0 i
  | n + 1, x => fun i =>
    if h : i.val < n then natToVec n (x % 2 ^ n) ⟨i.val, h⟩
    else (x / 2 ^ n) % 2 == 1

def vecEqZero : {n : Nat} → Vec n → Bool
  | 0, _ => true
  | n + 1, v => vecEqZero (fun i : Fin n => v ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) &&
                !(v ⟨n, Nat.lt_succ_self n⟩)

def countPred : (N : Nat) → (Fin N → Bool) → Nat
  | 0, _ => 0
  | N + 1, p => countPred N (fun i => p ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) +
                if p ⟨N, Nat.lt_succ_self N⟩ then 1 else 0

/-- Exact count of all vectors v ∈ F_2^n satisfying M * v = 0. -/
def kerCount {m n : Nat} (M : Mat m n) : Nat :=
  countPred (2 ^ n) (fun x => vecEqZero (matVec M (natToVec n x.val)))

/-- Nonconstructive extraction of LinEquiv from full square rank (only uses Classical.choice). -/
noncomputable def LinEquiv.ofHasRankFull {n : Nat} {A : Mat n n} (h : HasRank A n) : LinEquiv n n := by
  let P := Classical.choose h.equiv
  let hP := Classical.choose_spec h.equiv
  let Q := Classical.choose hP
  let hPQ := Classical.choose_spec hP
  have hPQ' : ∀ v, P.toFun (matVec A (Q.toFun v)) = v := by
    intro v
    have hv := hPQ v
    rw [matVec_diagRank (Nat.le_refl n)] at hv
    rw [hv]
    funext i
    simp [i.isLt]
  exact {
    toFun := matVec A
    invFun := fun u => Q.toFun (P.toFun u)
    map_xor := matVec_xor A
    left_inv := fun u => by
      have h1 := hPQ' (Q.invFun u)
      rw [Q.right_inv] at h1
      rw [h1, Q.right_inv]
    right_inv := fun v => by
      have h1 := hPQ' (P.toFun v)
      have h2 := congrArg P.invFun h1
      rw [P.left_inv, P.left_inv] at h2
      exact h2
  }

/-! ## Section 3: Reusable Pure-Silicon Block-Elimination Combinators -/

def splitLeft {a b : Nat} (v : Vec (a + b)) : Vec a :=
  fun i => v ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right a b)⟩

def splitRight {a b : Nat} (v : Vec (a + b)) : Vec b :=
  fun j => v ⟨a + j.val, Nat.add_lt_add_left j.isLt a⟩

def joinVec {a b : Nat} (u : Vec a) (v : Vec b) : Vec (a + b) :=
  fun i => if h : i.val < a then u ⟨i.val, h⟩ else v ⟨i.val - a, by omega⟩

@[simp] theorem splitLeft_joinVec {a b : Nat} (u : Vec a) (v : Vec b) :
    splitLeft (joinVec u v) = u := by
  funext i; simp [splitLeft, joinVec, i.isLt]

@[simp] theorem splitRight_joinVec {a b : Nat} (u : Vec a) (v : Vec b) :
    splitRight (joinVec u v) = v := by
  funext j
  simp only [splitRight, joinVec]
  have hnot : ¬ (a + j.val < a) := by omega
  simp only [hnot, ↓reduceDIte]
  congr 1; apply Fin.ext; dsimp; omega

@[simp] theorem joinVec_split {a b : Nat} (w : Vec (a + b)) :
    joinVec (splitLeft w) (splitRight w) = w := by
  funext i
  simp only [joinVec, splitLeft, splitRight]
  by_cases h : i.val < a
  · simp [h]
  · simp only [h, ↓reduceDIte]
    congr 1; apply Fin.ext; dsimp; omega

theorem joinVec_vxor {a b : Nat} (u1 u2 : Vec a) (v1 v2 : Vec b) :
    joinVec (vxor u1 u2) (vxor v1 v2) = vxor (joinVec u1 v1) (joinVec u2 v2) := by
  funext i
  simp only [joinVec, vxor]
  by_cases h : i.val < a <;> simp [h]

theorem splitLeft_vxor {a b : Nat} (u v : Vec (a + b)) :
    splitLeft (vxor u v) = vxor (splitLeft u) (splitLeft v) := rfl

theorem splitRight_vxor {a b : Nat} (u v : Vec (a + b)) :
    splitRight (vxor u v) = vxor (splitRight u) (splitRight v) := rfl

def blockMat {a b c d : Nat} (A : Mat a c) (B : Mat a d) (C : Mat b c) (D : Mat b d) :
    Mat (a + b) (c + d) :=
  fun i j =>
    if hi : i.val < a then
      if hj : j.val < c then A ⟨i.val, hi⟩ ⟨j.val, hj⟩
      else B ⟨i.val, hi⟩ ⟨j.val - c, by omega⟩
    else
      if hj : j.val < c then C ⟨i.val - a, by omega⟩ ⟨j.val, hj⟩
      else D ⟨i.val - a, by omega⟩ ⟨j.val - c, by omega⟩

def matXor {m n : Nat} (A B : Mat m n) : Mat m n := fun i j => xor (A i j) (B i j)

def outerMat {a b : Nat} (u : Vec a) (v : Vec b) : Mat a b := fun i j => u i && v j

def LinEquiv.blockDiag {a b c d : Nat} (e1 : LinEquiv a c) (e2 : LinEquiv b d) :
    LinEquiv (a + b) (c + d) where
  toFun w := joinVec (e1.toFun (splitLeft w)) (e2.toFun (splitRight w))
  invFun w := joinVec (e1.invFun (splitLeft w)) (e2.invFun (splitRight w))
  map_xor u v := by
    simp only [splitLeft_vxor, splitRight_vxor, e1.map_xor, e2.map_xor, joinVec_vxor]
  left_inv u := by
    simp only [splitLeft_joinVec, splitRight_joinVec, e1.left_inv, e2.left_inv, joinVec_split]
  right_inv v := by
    simp only [splitLeft_joinVec, splitRight_joinVec, e1.right_inv, e2.right_inv, joinVec_split]

def LinEquiv.rowShearDown {a b : Nat} (f : Vec a → Vec b)
    (hf : ∀ u1 u2, f (vxor u1 u2) = vxor (f u1) (f u2)) : LinEquiv (a + b) (a + b) where
  toFun w := joinVec (splitLeft w) (vxor (splitRight w) (f (splitLeft w)))
  invFun w := joinVec (splitLeft w) (vxor (splitRight w) (f (splitLeft w)))
  map_xor u v := by
    rw [splitLeft_vxor, splitRight_vxor, hf, ← joinVec_vxor]
    congr 1
    funext i; simp only [vxor]
    cases splitRight u i <;> cases splitRight v i <;> cases f (splitLeft u) i <;> cases f (splitLeft v) i <;> rfl
  left_inv u := by
    simp only [splitLeft_joinVec, splitRight_joinVec]
    rw [vxor_assoc, vxor_self, vxor_zero_right, joinVec_split]
  right_inv v := by
    simp only [splitLeft_joinVec, splitRight_joinVec]
    rw [vxor_assoc, vxor_self, vxor_zero_right, joinVec_split]

def LinEquiv.rowShearUp {a b : Nat} (g : Vec b → Vec a)
    (hg : ∀ v1 v2, g (vxor v1 v2) = vxor (g v1) (g v2)) : LinEquiv (a + b) (a + b) where
  toFun w := joinVec (vxor (splitLeft w) (g (splitRight w))) (splitRight w)
  invFun w := joinVec (vxor (splitLeft w) (g (splitRight w))) (splitRight w)
  map_xor u v := by
    rw [splitLeft_vxor, splitRight_vxor, hg, ← joinVec_vxor]
    congr 1
    funext i; simp only [vxor]
    cases splitLeft u i <;> cases splitLeft v i <;> cases g (splitRight u) i <;> cases g (splitRight v) i <;> rfl
  left_inv u := by
    simp only [splitLeft_joinVec, splitRight_joinVec]
    rw [vxor_assoc, vxor_self, vxor_zero_right, joinVec_split]
  right_inv v := by
    simp only [splitLeft_joinVec, splitRight_joinVec]
    rw [vxor_assoc, vxor_self, vxor_zero_right, joinVec_split]

def LinEquiv.swapBlocks (a b : Nat) : LinEquiv (a + b) (b + a) where
  toFun w := joinVec (splitRight w) (splitLeft w)
  invFun w := joinVec (splitRight w) (splitLeft w)
  map_xor u v := by rw [splitLeft_vxor, splitRight_vxor, joinVec_vxor]
  left_inv u := by simp only [splitLeft_joinVec, splitRight_joinVec, joinVec_split]
  right_inv v := by simp only [splitLeft_joinVec, splitRight_joinVec, joinVec_split]

def LinEquiv.ofFinBij {m n : Nat} (f : Fin m → Fin n) (g : Fin n → Fin m)
    (hfg : ∀ i, g (f i) = i) (hgf : ∀ j, f (g j) = j) : LinEquiv m n where
  toFun u j := u (g j)
  invFun v i := v (f i)
  map_xor _ _ := rfl
  left_inv u := by funext i; exact congrArg u (hfg i)
  right_inv v := by funext j; exact congrArg v (hgf j)

/-- Canonical LSB parity-split equivalence permuting evens (0,2,4,...) before odds (1,3,5,...). -/
def LinEquiv.paritySplit (n : Nat) : LinEquiv n ((n + 1) / 2 + n / 2) where
  toFun u := joinVec (fun a : Fin ((n + 1) / 2) => u ⟨2 * a.val, by omega⟩)
                     (fun b : Fin (n / 2) => u ⟨2 * b.val + 1, by omega⟩)
  invFun w i :=
    if h : i.val % 2 = 0 then splitLeft w ⟨i.val / 2, by omega⟩
    else splitRight w ⟨i.val / 2, by omega⟩
  map_xor u v := by
    rw [← joinVec_vxor]; rfl
  left_inv u := by
    funext i
    simp only [splitLeft_joinVec, splitRight_joinVec]
    by_cases h : i.val % 2 = 0
    · simp only [h, ↓reduceDIte]; congr 1; apply Fin.ext; dsimp; omega
    · simp only [h, ↓reduceDIte]; congr 1; apply Fin.ext; dsimp; omega
  right_inv w := by
    rw [← joinVec_split w]
    congr 1
    · funext a
      have h : (2 * a.val) % 2 = 0 := by omega
      simp only [h, ↓reduceDIte, splitLeft_joinVec]
      congr 1; apply Fin.ext; dsimp; omega
    · funext b
      have h : ¬ ((2 * b.val + 1) % 2 = 0) := by omega
      simp only [h, ↓reduceDIte, splitRight_joinVec]
      congr 1; apply Fin.ext; dsimp; omega

/-- Canonical permutation moving {0..r1-1} ∪ {a..a+r2-1} to {0..r1+r2-1}. -/
def LinEquiv.packDirectSum (a b r1 r2 : Nat) (h1 : r1 ≤ a) (h2 : r2 ≤ b) :
    LinEquiv (a + b) (a + b) :=
  let fwd : Fin (a + b) → Fin (a + b) := fun i =>
    if hc1 : i.val < r1 then ⟨i.val, by omega⟩
    else if hc2 : i.val < a then ⟨r2 + i.val, by omega⟩
    else if hc3 : i.val < a + r2 then ⟨r1 + (i.val - a), by omega⟩
    else ⟨i.val, i.isLt⟩
  let bwd : Fin (a + b) → Fin (a + b) := fun j =>
    if hc1 : j.val < r1 then ⟨j.val, by omega⟩
    else if hc2 : j.val < r1 + r2 then ⟨a + (j.val - r1), by omega⟩
    else if hc3 : j.val < a + r2 then ⟨j.val - r2, by omega⟩
    else ⟨j.val, j.isLt⟩
  LinEquiv.ofFinBij fwd bwd
    (fun i => by
      apply Fin.ext; simp only [fwd, bwd]
      by_cases c1 : i.val < r1
      · simp [c1]
      · by_cases c2 : i.val < a
        · simp only [c1, c2, ↓reduceDIte]
          have n1 : ¬ (r2 + i.val < r1) := by omega
          have n2 : ¬ (r2 + i.val < r1 + r2) := by omega
          have c3 : r2 + i.val < a + r2 := by omega
          simp only [n1, n2, c3, ↓reduceDIte]; omega
        · by_cases c3 : i.val < a + r2
          · simp only [c1, c2, c3, ↓reduceDIte]
            have n1 : ¬ (r1 + (i.val - a) < r1) := by omega
            have c2' : r1 + (i.val - a) < r1 + r2 := by omega
            simp only [n1, c2', ↓reduceDIte]; omega
          · simp only [c1, c2, c3, ↓reduceDIte]
            have n2 : ¬ (i.val < r1 + r2) := by omega
            simp [n2])
    (fun j => by
      apply Fin.ext; simp only [fwd, bwd]
      by_cases c1 : j.val < r1
      · simp [c1]
      · by_cases c2 : j.val < r1 + r2
        · simp only [c1, c2, ↓reduceDIte]
          have n1 : ¬ (a + (j.val - r1) < r1) := by omega
          have n2 : ¬ (a + (j.val - r1) < a) := by omega
          have c3 : a + (j.val - r1) < a + r2 := by omega
          simp only [n1, n2, c3, ↓reduceDIte]; omega
        · by_cases c3 : j.val < a + r2
          · simp only [c1, c2, c3, ↓reduceDIte]
            have n1 : ¬ (j.val - r2 < r1) := by omega
            have c2' : j.val - r2 < a := by omega
            simp only [n1, c2', ↓reduceDIte]; omega
          · simp only [c1, c2, c3, ↓reduceDIte]
            have n2 : ¬ (j.val < a) := by omega
            simp [n2])

def popcountAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n == 0 then 0 else (n % 2) + popcountAux fuel (n / 2)

def popcount (n : Nat) : Nat := popcountAux n n

def popParityAux : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, n => if n == 0 then false else xor (n % 2 == 1) (popParityAux fuel (n / 2))

def popParity (n : Nat) : Bool := popParityAux n n

def ctzParityAux : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, n => if n == 0 then false else if n % 2 == 1 then false else !(ctzParityAux fuel (n / 2))

def ctzParity (n : Nat) : Bool := ctzParityAux n n

def gray (m : Nat) : Nat := m ^^^ (m / 2)

/-- Carry-free XOR-sum parity entry (carry-in c = 0): popcount((i+j) & (i^j)) mod 2. -/
def M0Entry (i j : Nat) : Bool := popParity ((i + j) &&& (i ^^^ j))

/-- Carry-in c = 1 companion entry: popcount((i+j+1) & (i^j)) mod 2. -/
def M1Entry (i j : Nat) : Bool := popParity ((i + j + 1) &&& (i ^^^ j))

/-- Carry-defect entry: D(i,j) = M0(i,j) ⊕ M1(i,j). -/
def DEntry (i j : Nat) : Bool := xor (M0Entry i j) (M1Entry i j)

/-- Complement carry-defect entry: Dbar(i,j) = !D(i,j). -/
def DbarEntry (i j : Nat) : Bool := !(DEntry i j)

def M0Mat (n : Nat) : Mat n n := fun i j => M0Entry i.val j.val

def M1Mat (n : Nat) : Mat n n := fun i j => M1Entry i.val j.val

def DMat (n : Nat) : Mat n n := fun i j => DEntry i.val j.val

def DbarMat (n : Nat) : Mat n n := fun i j => DbarEntry i.val j.val

def m0Nullity (n : Nat) : Nat :=
  if n = 0 then 0
  else if n = 1 then 1
  else popcount (gray (n - 1)) - 1

/-- Induced hypercube adjacency (d = false) and closed-neighborhood (d = true) matrix over F_2. -/
def HEntry (d : Bool) (i j : Nat) : Bool :=
  xor (popcount (i ^^^ j) == 1) (d && (i == j))

def HMat (d : Bool) (n : Nat) : Mat n n := fun i j => HEntry d i.val j.val

def bitLenAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n == 0 then 0 else 1 + bitLenAux fuel (n / 2)

def bitLen (n : Nat) : Nat := bitLenAux n n

def hcNullityAux : Nat → Bool → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, d, n =>
    if n == 0 then 0
    else if n == 1 then if d then 0 else 1
    else
      let k := bitLen n - 1
      let r := n - 2 ^ k
      if (k % 2 == 1) != d then r
      else
        let half := 2 ^ (k - 1)
        if r ≤ half then half - r
        else hcNullityAux fuel d (r - half)

def hcNullity (d : Bool) (n : Nat) : Nat := hcNullityAux n d n

/-- Exact 2-state Base-4 DFA recognizing invertible induced hypercubes H(0, n):
    n = 0, or n is even and n/2 in base 4 matches (0 | 3)* (1 | ε) 0*. -/
def base4RestAux : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, m =>
    if m == 0 then true
    else ((m % 4 == 0) || (m % 4 == 3)) && base4RestAux fuel (m / 4)

def base4StartAux : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, m =>
    if m == 0 then false
    else if m % 4 == 0 then base4StartAux fuel (m / 4)
    else if (m % 4 == 1) || (m % 4 == 3) then base4RestAux fuel (m / 4)
    else false

def hc0Base4Accept (n : Nat) : Bool :=
  if n == 0 then true
  else if n % 2 == 1 then false
  else base4StartAux n (n / 2)

def MOrMat (n : Nat) : Mat n n := fun i j => popParity ((i.val + j.val) ||| (i.val ^^^ j.val))

def H2Mat (n : Nat) : Mat n n := fun i j => popcount (i.val ^^^ j.val) == 2

end F2RankAutomaton
