/-
  Pure-Silicon Binary Math:
  The Walsh–Defect, Weyl–Heisenberg & Hyperplane-Rotation Spectral Conjugacy Engine
  (Standalone Core Lean 4.34.1 — Self-Contained Pure Integer/Boolean Arithmetic)

  Campaign: silicon-infinite-mechanisms-20261126 / specmat-16
-/

set_option autoImplicit false

namespace SiliconSpectral

-- ============================================================================
-- SECTION 1: PURE-SILICON BIT VECTORS, DOT PRODUCT, PARITY & EXACT SUMMATION
-- ============================================================================

abbrev Vec (k : Nat) := Fin k -> Bool

def zeroVec (k : Nat) : Vec k := fun _ => false

def consVec {k : Nat} (b : Bool) (v : Vec k) : Vec (k + 1)
  | ⟨0, _⟩ => b
  | ⟨i + 1, h⟩ => v ⟨i, Nat.lt_of_succ_lt_succ h⟩

def tailVec {k : Nat} (v : Vec (k + 1)) : Vec k :=
  fun i => v ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩

def xorVec {k : Nat} (x y : Vec k) : Vec k :=
  fun i => x i ^^ y i

def eVec (k : Nat) (j : Fin k) : Vec k :=
  fun i => decide (i.val = j.val)

theorem consVec_head_tail {k : Nat} (v : Vec (k + 1)) :
    consVec (v ⟨0, Nat.zero_lt_succ k⟩) (tailVec v) = v := by
  funext ⟨i, h⟩
  cases i <;> rfl

theorem vec0_eq (x y : Vec 0) : x = y := by
  funext i
  exact False.elim (Nat.not_lt_zero i.val i.isLt)

def decEqVec : (k : Nat) -> DecidableEq (Vec k)
  | 0, x, y => isTrue (vec0_eq x y)
  | k + 1, x, y =>
      match decEq (x ⟨0, Nat.zero_lt_succ k⟩) (y ⟨0, Nat.zero_lt_succ k⟩),
            decEqVec k (tailVec x) (tailVec y) with
      | isTrue h0, isTrue ht =>
          isTrue (by
            rw [← consVec_head_tail x, ← consVec_head_tail y, h0, ht])
      | isFalse h0, _ => isFalse (fun h => h0 (congrFun h ⟨0, Nat.zero_lt_succ k⟩))
      | _, isFalse ht => isFalse (fun h => ht (congrArg tailVec h))

instance (k : Nat) : DecidableEq (Vec k) := decEqVec k

def sgn (b : Bool) : Int := if b then -1 else 1

def dot : (k : Nat) -> Vec k -> Vec k -> Bool
  | 0, _, _ => false
  | k + 1, x, y =>
      (x ⟨0, Nat.zero_lt_succ k⟩ && y ⟨0, Nat.zero_lt_succ k⟩) ^^
        dot k (tailVec x) (tailVec y)

theorem dot_comm : (k : Nat) -> (x y : Vec k) -> dot k x y = dot k y x
  | 0, _, _ => rfl
  | k + 1, x, y => by
      simp [dot, Bool.and_comm, dot_comm k (tailVec x) (tailVec y)]

def parity : (k : Nat) -> Vec k -> Bool
  | 0, _ => false
  | k + 1, x => x ⟨0, Nat.zero_lt_succ k⟩ ^^ parity k (tailVec x)

def sumVec : (k : Nat) -> (Vec k -> Int) -> Int
  | 0, f => f (fun i => False.elim (Nat.not_lt_zero i.val i.isLt))
  | k + 1, f =>
      sumVec k (fun v => f (consVec false v)) +
      sumVec k (fun v => f (consVec true v))

def allVecs : (k : Nat) -> List (Vec k)
  | 0 => [zeroVec 0]
  | k + 1 => (allVecs k).map (consVec false) ++ (allVecs k).map (consVec true)

def listSum : List Int -> Int
  | [] => 0
  | a :: t => a + listSum t

def countPred (k : Nat) (p : Vec k -> Bool) : Int :=
  sumVec k (fun x => if p x then 1 else 0)

abbrev Mat (k : Nat) := Vec k -> Vec k -> Int

def idMat (k : Nat) : Mat k := fun x y => if x = y then 1 else 0
def zeroMat (k : Nat) : Mat k := fun _ _ => 0
def addMat {k : Nat} (A B : Mat k) : Mat k := fun x y => A x y + B x y
def subMat {k : Nat} (A B : Mat k) : Mat k := fun x y => A x y - B x y
def negMat {k : Nat} (A : Mat k) : Mat k := fun x y => -(A x y)
def smulMat {k : Nat} (c : Int) (A : Mat k) : Mat k := fun x y => c * A x y

def mulMat {k : Nat} (A B : Mat k) : Mat k :=
  fun x y => sumVec k (fun z => A x z * B z y)

def matPow {k : Nat} (A : Mat k) : Nat -> Mat k
  | 0 => idMat k
  | n + 1 => mulMat (matPow A n) A

def traceMat {k : Nat} (A : Mat k) : Int :=
  sumVec k (fun x => A x x)

def applyVec {k : Nat} (A : Mat k) (v : Vec k -> Int) : Vec k -> Int :=
  fun x => sumVec k (fun y => A x y * v y)

-- Core silicon operators
def walshMat (k : Nat) : Mat k :=
  fun x y => sgn (dot k x y)

def permMat {k : Nat} (f : Vec k -> Vec k) : Mat k :=
  fun x y => if f y = x then 1 else 0

def diagPhaseMat {k : Nat} (a : Vec k) : Mat k :=
  fun x y => if x = y then sgn (dot k a x) else 0

def transMat {k : Nat} (b : Vec k) : Mat k :=
  permMat (fun x => xorVec x b)

-- Basic matrix algebra laws
def iterFn {α : Type} (f : α -> α) : Nat -> α -> α
  | 0, x => x
  | n + 1, x => f (iterFn f n x)

/-- Finite-width silicon operator certificate for an invertible F_2-linear map
    A ∈ GL_k(F_2), bundling its circuit, inverse, adjoint (A^T), and inverse-adjoint. -/
structure LinIso (k : Nat) where
  fwd        : Vec k -> Vec k
  inv        : Vec k -> Vec k
  adj        : Vec k -> Vec k
  adjInv     : Vec k -> Vec k
  fwd_inv    : ∀ x, fwd (inv x) = x
  inv_fwd    : ∀ x, inv (fwd x) = x
  adj_adjInv : ∀ x, adj (adjInv x) = x
  adjInv_adj : ∀ x, adjInv (adj x) = x
  dot_adj    : ∀ x y, dot k x (fwd y) = dot k (adj x) y

namespace LinIso

def id (k : Nat) : LinIso k where
  fwd := fun x => x
  inv := fun x => x
  adj := fun x => x
  adjInv := fun x => x
  fwd_inv := fun _ => rfl
  inv_fwd := fun _ => rfl
  adj_adjInv := fun _ => rfl
  adjInv_adj := fun _ => rfl
  dot_adj := fun _ _ => rfl

def comp {k : Nat} (A B : LinIso k) : LinIso k where
  fwd := fun x => A.fwd (B.fwd x)
  inv := fun x => B.inv (A.inv x)
  adj := fun x => B.adj (A.adj x)
  adjInv := fun x => A.adjInv (B.adjInv x)
  fwd_inv := fun x => by rw [B.fwd_inv, A.fwd_inv]
  inv_fwd := fun x => by rw [A.inv_fwd, B.inv_fwd]
  adj_adjInv := fun x => by rw [A.adj_adjInv, B.adj_adjInv]
  adjInv_adj := fun x => by rw [B.adjInv_adj, A.adjInv_adj]
  dot_adj := fun x y => by rw [A.dot_adj, B.dot_adj]

def symm {k : Nat} (A : LinIso k) : LinIso k where
  fwd := A.inv
  inv := A.fwd
  adj := A.adjInv
  adjInv := A.adj
  fwd_inv := A.inv_fwd
  inv_fwd := A.fwd_inv
  adj_adjInv := A.adjInv_adj
  adjInv_adj := A.adj_adjInv
  dot_adj := fun x y => by
    have h := A.dot_adj (A.adjInv x) (A.inv y)
    rw [A.fwd_inv, A.adj_adjInv] at h
    exact h.symm

def transpose {k : Nat} (A : LinIso k) : LinIso k where
  fwd := A.adj
  inv := A.adjInv
  adj := A.fwd
  adjInv := A.inv
  fwd_inv := A.adj_adjInv
  inv_fwd := A.adjInv_adj
  adj_adjInv := A.fwd_inv
  adjInv_adj := A.inv_fwd
  dot_adj := fun x y => by
    rw [dot_comm k x (A.adj y), ← A.dot_adj y x, dot_comm k y (A.fwd x)]

/-- Symmetry defect operator Δ(A) := (A^T)^{-1} ∘ A ∈ GL_k(F_2). -/
def defect {k : Nat} (A : LinIso k) : LinIso k :=
  A.transpose.symm.comp A

end LinIso

-- ----------------------------------------------------------------------------
-- PILLAR 1: WALSH CONTRAGREDIENT & SYMMETRY-DEFECT SPECTRAL ENGINE
-- ----------------------------------------------------------------------------

def weylOp {k : Nat} (a b : Vec k) : Mat k :=
  mulMat (diagPhaseMat a) (transMat b)

/-- Cyclic rotation by +1 index on Vec n: (rot1 n u)_i = u_{(i + 1) mod n}. -/
def rot1 (n : Nat) (u : Vec n) : Vec n :=
  fun i => u ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

/-- Certificate intertwining Δ(A) on Vec k with (rot1 n on even-parity H_{n-1}) × id_r. -/
structure HyperplaneRotCert (k n r : Nat) (A : LinIso k) where
  hn     : 1 ≤ n
  toU    : Vec k -> Vec n
  toS    : Vec k -> Vec r
  fromUS : Vec n -> Vec r -> Vec k
  even_U : ∀ x, parity n (toU x) = false
  left_inv  : ∀ x, fromUS (toU x) (toS x) = x
  right_inv_U : ∀ u s, parity n u = false -> toU (fromUS u s) = u
  right_inv_S : ∀ u s, parity n u = false -> toS (fromUS u s) = s
  conj_U : ∀ x, toU (A.defect.fwd x) = rot1 n (toU x)
  conj_S : ∀ x, toS (A.defect.fwd x) = toS x

/-- Two-bit even-parity witness e_0 ⊕ e_1 ∈ H_{n-1}. -/
def twoBitWitness (n : Nat) : Vec n :=
  fun i => decide (i.val = 0 ∨ i.val = 1)

def xorRange (f : Nat -> Bool) : Nat -> Bool
  | 0 => false
  | k + 1 => xorRange f k ^^ f k

theorem xorRange_add (f : Nat -> Bool) (a b : Nat) :
    xorRange f (a + b) = (xorRange f a ^^ xorRange (fun i => f (a + i)) b) := by
  induction b with
  | zero => simp [xorRange]
  | succ b ih =>
      rw [Nat.add_succ, xorRange, xorRange, ih, Bool.xor_assoc]

theorem xorRange_congr (f g : Nat -> Bool) (n : Nat) (h : ∀ i, i < n -> f i = g i) :
    xorRange f n = xorRange g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [xorRange, xorRange, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

theorem parity_eq_xorRange : (n : Nat) -> (u : Vec n) ->
    parity n u = xorRange (fun i => if h : i < n then u ⟨i, h⟩ else false) n
  | 0, _ => rfl
  | n + 1, u => by
      let f : Nat -> Bool := fun i => if h : i < n + 1 then u ⟨i, h⟩ else false
      have hsplit : xorRange f (n + 1) = (xorRange f 1 ^^ xorRange (fun i => f (1 + i)) n) := by
        have hadd : n + 1 = 1 + n := Nat.add_comm n 1
        rw [hadd]
        exact xorRange_add f 1 n
      change parity (n + 1) u = xorRange f (n + 1)
      rw [hsplit]
      simp only [parity, xorRange, f, Nat.zero_lt_succ, dite_true, Bool.false_xor]
      congr 1
      rw [parity_eq_xorRange n (tailVec u)]
      apply xorRange_congr
      intro i hi
      have hi' : 1 + i < n + 1 := by omega
      simp only [hi, hi', dite_true, tailVec]
      congr 1; apply Fin.ext; dsimp; omega

def prodList {α β : Type} (la : List α) (lb : List β) : List (α × β) :=
  la.flatMap (fun a => lb.map (fun b => (a, b)))

def padVec (k : Nat) (x : Vec k) (j : Nat) : Bool :=
  if h : j < k then x ⟨j, h⟩ else false

theorem xorRange_split (f : Nat -> Bool) {m a b : Nat} (h : m = a + b) :
    xorRange f m = (xorRange f a ^^ xorRange (fun i => f (a + i)) b) := by
  subst h; exact xorRange_add f a b

theorem xorRange_xor (f g : Nat -> Bool) (n : Nat) :
    xorRange (fun i => f i ^^ g i) n = (xorRange f n ^^ xorRange g n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [xorRange, ih]
      cases xorRange f n <;> cases xorRange g n <;> cases f n <;> cases g n <;> rfl

theorem xorRange_rev (f : Nat -> Bool) : (n : Nat) ->
    xorRange (fun i => f (n - 1 - i)) n = xorRange f n
  | 0 => rfl
  | n + 1 => by
      rw [xorRange_split (fun i => f (n + 1 - 1 - i)) (Nat.add_comm n 1)]
      have h0 : xorRange (fun i => f (n + 1 - 1 - i)) 1 = f n := by
        simp [xorRange]
      have hrest : xorRange (fun i => f (n + 1 - 1 - (1 + i))) n =
                   xorRange (fun i => f (n - 1 - i)) n := by
        apply xorRange_congr
        intro i _
        have heq : n + 1 - 1 - (1 + i) = n - 1 - i := by omega
        rw [heq]
      rw [h0, hrest, xorRange_rev f n, xorRange, Bool.xor_comm]

theorem dot_eq_xorRange : (k : Nat) -> (x y : Vec k) ->
    dot k x y = xorRange (fun i => padVec k x i && padVec k y i) k
  | 0, _, _ => rfl
  | k + 1, x, y => by
      rw [xorRange_split _ (Nat.add_comm k 1)]
      simp only [dot, xorRange, padVec, Nat.zero_lt_succ, dite_true, Bool.false_xor]
      congr 1
      rw [dot_eq_xorRange k (tailVec x) (tailVec y)]
      apply xorRange_congr
      intro i hi
      have hi' : 1 + i < k + 1 := by omega
      simp only [padVec, hi, hi', dite_true, tailVec]
      congr 1 <;> (congr 1; apply Fin.ext; dsimp; omega)

-- ----------------------------------------------------------------------------
-- 4.1 Bit-Reversal R_k
-- ----------------------------------------------------------------------------

def bitrevVec (k : Nat) (x : Vec k) : Vec k :=
  fun i => x ⟨k - 1 - i.val, by omega⟩

theorem bitrevVec_invol (k : Nat) (x : Vec k) : bitrevVec k (bitrevVec k x) = x := by
  funext ⟨i, hi⟩
  simp only [bitrevVec]
  congr 1; apply Fin.ext; dsimp; omega

theorem dot_bitrev (k : Nat) (x y : Vec k) :
    dot k x (bitrevVec k y) = dot k (bitrevVec k x) y := by
  rw [dot_eq_xorRange, dot_eq_xorRange]
  rw [← xorRange_rev (fun i => padVec k (bitrevVec k x) i && padVec k y i) k]
  apply xorRange_congr
  intro i hi
  have hrev : k - 1 - i < k := by omega
  simp only [padVec, hi, hrev, dite_true, bitrevVec]
  congr 1
  congr 1; apply Fin.ext; dsimp; omega

theorem parity_bitrev (k : Nat) (x : Vec k) : parity k (bitrevVec k x) = parity k x := by
  rw [parity_eq_xorRange, parity_eq_xorRange]
  rw [← xorRange_rev (fun i => if h : i < k then x ⟨i, h⟩ else false) k]
  apply xorRange_congr
  intro i hi
  have hrev : k - 1 - i < k := by omega
  simp only [hi, hrev, dite_true, bitrevVec]

def bitrevIso (k : Nat) : LinIso k where
  fwd := bitrevVec k
  inv := bitrevVec k
  adj := bitrevVec k
  adjInv := bitrevVec k
  fwd_inv := bitrevVec_invol k
  inv_fwd := bitrevVec_invol k
  adj_adjInv := bitrevVec_invol k
  adjInv_adj := bitrevVec_invol k
  dot_adj := dot_bitrev k

-- ----------------------------------------------------------------------------
-- 4.2 Gray Code G_k, Inverse Gray G_k^{-1}, and Adjoint G_k^T
-- ----------------------------------------------------------------------------

def grayFwd (k : Nat) (x : Vec k) : Vec k :=
  fun i => x i ^^ padVec k x (i.val + 1)

def grayInv (k : Nat) (x : Vec k) : Vec k :=
  fun i => xorRange (fun t => padVec k x (i.val + t)) (k - i.val)

def grayAdj (k : Nat) (x : Vec k) : Vec k :=
  fun i => x i ^^ (if i.val = 0 then false else padVec k x (i.val - 1))

def grayAdjInv (k : Nat) (x : Vec k) : Vec k :=
  fun i => xorRange (padVec k x) (i.val + 1)

theorem grayFwd_inv (k : Nat) (x : Vec k) : grayFwd k (grayInv k x) = x := by
  funext ⟨i, hi⟩
  simp only [grayFwd]
  by_cases hi1 : i + 1 < k
  · have hpad : padVec k (grayInv k x) (i + 1) = grayInv k x ⟨i + 1, hi1⟩ := by
      simp [padVec, hi1]
    rw [hpad]
    simp only [grayInv]
    rw [xorRange_split _ (by omega : k - i = 1 + (k - (i + 1)))]
    have h1 : xorRange (fun t => padVec k x (i + t)) 1 = x ⟨i, hi⟩ := by
      simp [xorRange, padVec, hi]
    have h2 : xorRange (fun t => padVec k x (i + (1 + t))) (k - (i + 1)) =
              xorRange (fun t => padVec k x (i + 1 + t)) (k - (i + 1)) :=
      xorRange_congr _ _ _ (fun t _ => by congr 1; omega)
    rw [h1, h2]
    cases x ⟨i, hi⟩ <;> cases xorRange (fun t => padVec k x (i + 1 + t)) (k - (i + 1)) <;> rfl
  · have hpad : padVec k (grayInv k x) (i + 1) = false := by simp [padVec, hi1]
    rw [hpad, Bool.xor_false]
    simp only [grayInv]
    have h1 : k - i = 1 := by omega
    rw [h1]
    simp [xorRange, padVec, hi]

theorem grayInv_fwd (k : Nat) (x : Vec k) : grayInv k (grayFwd k x) = x := by
  have htele : ∀ (j m : Nat),
      xorRange (fun t => padVec k (grayFwd k x) (j + t)) m =
      (padVec k x j ^^ padVec k x (j + m)) := by
    intro j m
    induction m with
    | zero => simp [xorRange]
    | succ m ih =>
        rw [xorRange, ih]
        have hstep : padVec k (grayFwd k x) (j + m) =
                     (padVec k x (j + m) ^^ padVec k x (j + (m + 1))) := by
          by_cases hlt : j + m < k
          · simp only [padVec, hlt, dite_true, grayFwd]
            have heq : j + m + 1 = j + (m + 1) := by omega
            rw [heq]
          · have hlt1 : ¬(j + (m + 1) < k) := by omega
            simp [padVec, hlt, hlt1]
        rw [hstep]
        cases padVec k x j <;> cases padVec k x (j + m) <;> cases padVec k x (j + (m + 1)) <;> rfl
  funext ⟨i, hi⟩
  simp only [grayInv]
  rw [htele i (k - i)]
  have hsum : i + (k - i) = k := by omega
  rw [hsum]
  simp [padVec, hi]

theorem grayAdj_inv (k : Nat) (x : Vec k) : grayAdj k (grayAdjInv k x) = x := by
  funext ⟨i, hi⟩
  simp only [grayAdj]
  cases i with
  | zero =>
      simp [grayAdjInv, xorRange, padVec, hi]
  | succ i' =>
      have hi'_lt : i' < k := by omega
      have hpad : padVec k (grayAdjInv k x) (i' + 1 - 1) = grayAdjInv k x ⟨i', hi'_lt⟩ := by
        simp [padVec, hi'_lt]
      simp only [Nat.succ_ne_zero, ite_false, hpad, grayAdjInv]
      rw [xorRange]
      simp only [padVec, hi, dite_true]
      cases xorRange (padVec k x) (i' + 1) <;> cases x ⟨i' + 1, hi⟩ <;> rfl

theorem grayAdjInv_adj (k : Nat) (x : Vec k) : grayAdjInv k (grayAdj k x) = x := by
  have htele : ∀ m : Nat, (hm : m < k) ->
      xorRange (padVec k (grayAdj k x)) (m + 1) = x ⟨m, hm⟩ := by
    intro m
    induction m with
    | zero =>
        intro hm
        simp [xorRange, padVec, hm, grayAdj]
    | succ m ih =>
        intro hm
        have hm' : m < k := by omega
        rw [xorRange, ih hm']
        simp only [padVec, hm, hm', dite_true, grayAdj, Nat.succ_ne_zero, ite_false,
                   Nat.add_sub_cancel]
        cases x ⟨m, hm'⟩ <;> cases x ⟨m + 1, hm⟩ <;> rfl
  funext ⟨i, hi⟩
  exact htele i hi

theorem dot_gray_adj (k : Nat) (x y : Vec k) :
    dot k x (grayFwd k y) = dot k (grayAdj k x) y := by
  rw [dot_eq_xorRange, dot_eq_xorRange]
  have hL : xorRange (fun i => padVec k x i && padVec k (grayFwd k y) i) k =
            (xorRange (fun i => padVec k x i && padVec k y i) k ^^
             xorRange (fun i => padVec k x i && padVec k y (i + 1)) k) := by
    rw [← xorRange_xor]
    apply xorRange_congr
    intro i hi
    have hp1 : padVec k x i = x ⟨i, hi⟩ := by simp [padVec, hi]
    have hp2 : padVec k (grayFwd k y) i = (y ⟨i, hi⟩ ^^ padVec k y (i + 1)) := by
      simp [padVec, hi, grayFwd]
    have hp3 : padVec k y i = y ⟨i, hi⟩ := by simp [padVec, hi]
    rw [hp1, hp2, hp3]
    cases x ⟨i, hi⟩ <;> cases y ⟨i, hi⟩ <;> cases padVec k y (i + 1) <;> rfl
  have hR : xorRange (fun i => padVec k (grayAdj k x) i && padVec k y i) k =
            (xorRange (fun i => padVec k x i && padVec k y i) k ^^
             xorRange (fun i => (if i = 0 then false else padVec k x (i - 1)) && padVec k y i) k) := by
    rw [← xorRange_xor]
    apply xorRange_congr
    intro i hi
    have hp1 : padVec k x i = x ⟨i, hi⟩ := by simp [padVec, hi]
    have hp2 : padVec k (grayAdj k x) i = (x ⟨i, hi⟩ ^^ (if i = 0 then false else padVec k x (i - 1))) := by
      simp [padVec, hi, grayAdj]
    have hp3 : padVec k y i = y ⟨i, hi⟩ := by simp [padVec, hi]
    rw [hp1, hp2, hp3]
    cases x ⟨i, hi⟩ <;> cases (if i = 0 then false else padVec k x (i - 1)) <;> cases y ⟨i, hi⟩ <;> rfl
  rw [hL, hR]
  congr 1
  cases k with
  | zero => rfl
  | succ k' =>
      have hL1 : xorRange (fun i => padVec (k' + 1) x i && padVec (k' + 1) y (i + 1)) (k' + 1) =
                 xorRange (fun i => padVec (k' + 1) x i && padVec (k' + 1) y (i + 1)) k' := by
        rw [xorRange]
        have hlast : padVec (k' + 1) y (k' + 1) = false := by simp [padVec]
        simp [hlast]
      have hR1 : xorRange (fun i => (if i = 0 then false else padVec (k' + 1) x (i - 1)) &&
                            padVec (k' + 1) y i) (k' + 1) =
                 xorRange (fun i => padVec (k' + 1) x i && padVec (k' + 1) y (i + 1)) k' := by
        rw [xorRange_split _ (Nat.add_comm k' 1)]
        have h0 : xorRange (fun i => (if i = 0 then false else padVec (k' + 1) x (i - 1)) &&
                            padVec (k' + 1) y i) 1 = false := by
          simp [xorRange]
        rw [h0, Bool.false_xor]
        apply xorRange_congr
        intro i _
        have hadd1 : 1 + i = i + 1 := by omega
        simp [hadd1]
      rw [hL1, hR1]

def grayIso (k : Nat) : LinIso k where
  fwd := grayFwd k
  inv := grayInv k
  adj := grayAdj k
  adjInv := grayAdjInv k
  fwd_inv := grayFwd_inv k
  inv_fwd := grayInv_fwd k
  adj_adjInv := grayAdj_inv k
  adjInv_adj := grayAdjInv_adj k
  dot_adj := dot_gray_adj k

-- ----------------------------------------------------------------------------
-- 4.3 Cyclic Butterfly Rotation C_k (left shift by 1 bit)
-- ----------------------------------------------------------------------------

def rotL1 (k : Nat) (x : Vec k) : Vec k :=
  fun i => x ⟨(i.val + k - 1) % k, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

theorem rotL1_rot1 (k : Nat) (x : Vec k) : rotL1 k (rot1 k x) = x := by
  funext ⟨i, hi⟩
  simp only [rotL1, rot1]
  congr 1; apply Fin.ext; dsimp
  have h1 : ((i + k - 1) % k + 1) % k = (i + k) % k := by
    rw [Nat.mod_add_mod]
    congr 1; omega
  rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hi]

theorem rot1_rotL1 (k : Nat) (x : Vec k) : rot1 k (rotL1 k x) = x := by
  funext ⟨i, hi⟩
  simp only [rotL1, rot1]
  congr 1; apply Fin.ext; dsimp
  cases i with
  | zero =>
      by_cases hk : k = 1
      · subst hk; rfl
      · have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
        rw [h1]
        have h2 : (1 + k - 1) % k = 0 := by
          have : 1 + k - 1 = k := by omega
          rw [this, Nat.mod_self]
        exact h2
  | succ i' =>
      by_cases hlt : i' + 2 < k
      · have h1 : (i' + 1 + 1) % k = i' + 2 := Nat.mod_eq_of_lt hlt
        rw [h1]
        have h2 : i' + 2 + k - 1 = (i' + 1) + k := by omega
        rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
      · have heq : i' + 2 = k := by omega
        have h1 : (i' + 1 + 1) % k = 0 := by
          have : i' + 1 + 1 = k := by omega
          rw [this, Nat.mod_self]
        rw [h1]
        have h2 : 0 + k - 1 = i' + 1 := by omega
        rw [h2, Nat.mod_eq_of_lt hi]

theorem dot_rotL1_adj (k : Nat) (x y : Vec k) :
    dot k x (rotL1 k y) = dot k (rot1 k x) y := by
  rw [dot_eq_xorRange, dot_eq_xorRange]
  cases k with
  | zero => rfl
  | succ k' =>
      have hL : xorRange (fun i => padVec (k' + 1) x i && padVec (k' + 1) (rotL1 (k' + 1) y) i) (k' + 1) =
                ((x ⟨0, Nat.zero_lt_succ k'⟩ && y ⟨k', Nat.lt_succ_self k'⟩) ^^
                 xorRange (fun i => padVec (k' + 1) x (i + 1) && padVec (k' + 1) y i) k') := by
        rw [xorRange_split _ (Nat.add_comm k' 1)]
        have h0 : xorRange (fun i => padVec (k' + 1) x i && padVec (k' + 1) (rotL1 (k' + 1) y) i) 1 =
                  (x ⟨0, Nat.zero_lt_succ k'⟩ && y ⟨k', Nat.lt_succ_self k'⟩) := by
          simp only [xorRange, padVec, Nat.zero_lt_succ, dite_true, rotL1, Bool.false_xor]
          congr 1; congr 1; apply Fin.ext; dsimp
          have hmod : (0 + (k' + 1) - 1) % (k' + 1) = k' := by
            have : 0 + (k' + 1) - 1 = k' := by omega
            rw [this]; exact Nat.mod_eq_of_lt (Nat.lt_succ_self k')
          exact hmod
        rw [h0]
        congr 1
        apply xorRange_congr
        intro i hi
        have hi0 : i < k' + 1 := by omega
        have hi1 : 1 + i < k' + 1 := by omega
        have hi1' : i + 1 < k' + 1 := by omega
        simp only [padVec, hi0, hi1, hi1', dite_true, rotL1]
        congr 1
        · congr 1; apply Fin.ext; dsimp; omega
        · congr 1; apply Fin.ext; dsimp
          have hsub : 1 + i + k' = i + (k' + 1) := by omega
          rw [hsub, Nat.add_mod_right, Nat.mod_eq_of_lt hi0]
      have hR : xorRange (fun i => padVec (k' + 1) (rot1 (k' + 1) x) i && padVec (k' + 1) y i) (k' + 1) =
                (xorRange (fun i => padVec (k' + 1) x (i + 1) && padVec (k' + 1) y i) k' ^^
                 (x ⟨0, Nat.zero_lt_succ k'⟩ && y ⟨k', Nat.lt_succ_self k'⟩)) := by
        rw [xorRange]
        congr 1
        · apply xorRange_congr
          intro i hi
          have hi0 : i < k' + 1 := by omega
          have hi1 : i + 1 < k' + 1 := by omega
          simp only [padVec, hi0, hi1, dite_true, rot1]
          congr 1; congr 1; apply Fin.ext; dsimp
          exact Nat.mod_eq_of_lt hi1
        · simp only [padVec, Nat.lt_succ_self, dite_true, rot1]
          congr 1; congr 1; apply Fin.ext; dsimp
          exact Nat.mod_self (k' + 1)
      rw [hL, hR, Bool.xor_comm]

def rotL1Iso (k : Nat) : LinIso k where
  fwd := rotL1 k
  inv := rot1 k
  adj := rot1 k
  adjInv := rotL1 k
  fwd_inv := rotL1_rot1 k
  inv_fwd := rot1_rotL1 k
  adj_adjInv := rot1_rotL1 k
  adjInv_adj := rotL1_rot1 k
  dot_adj := dot_rotL1_adj k

-- ----------------------------------------------------------------------------
-- 4.4 Theorem A: Gray–Walsh (k+1)-Cycle Collapse, Exact Trace, Mod-4 Symmetry,
--                and Even-Width Half-Power Block-Gray Symplectic Law
-- ----------------------------------------------------------------------------

def grayToU (k : Nat) (x : Vec k) : Vec (k + 1) :=
  fun i => padVec k x i.val ^^ (if i.val = 0 then false else padVec k x (i.val - 1))

def grayFromU (k : Nat) (u : Vec (k + 1)) : Vec k :=
  fun i => xorRange (padVec (k + 1) u) (i.val + 1)

theorem grayToU_prefix_xor (k : Nat) (x : Vec k) (m : Nat) (hm : m ≤ k) :
    xorRange (padVec (k + 1) (grayToU k x)) (m + 1) = padVec k x m := by
  induction m with
  | zero =>
      simp [xorRange, padVec, grayToU]
  | succ m ih =>
      rw [xorRange, ih (by omega)]
      have hm1 : m + 1 < k + 1 := by omega
      have hp : padVec (k + 1) (grayToU k x) (m + 1) = (padVec k x (m + 1) ^^ padVec k x m) := by
        simp [padVec, hm1, grayToU]
      rw [hp]
      cases padVec k x m <;> cases padVec k x (m + 1) <;> rfl

theorem grayToU_even (k : Nat) (x : Vec k) : parity (k + 1) (grayToU k x) = false := by
  rw [parity_eq_xorRange]
  have h1 : xorRange (fun i => if h : i < k + 1 then grayToU k x ⟨i, h⟩ else false) (k + 1) =
            xorRange (padVec (k + 1) (grayToU k x)) (k + 1) :=
    xorRange_congr _ _ _ (fun _ _ => rfl)
  rw [h1, grayToU_prefix_xor k x k (Nat.le_refl k)]
  simp [padVec]

theorem grayFromU_toU (k : Nat) (x : Vec k) : grayFromU k (grayToU k x) = x := by
  funext ⟨i, hi⟩
  simp only [grayFromU]
  rw [grayToU_prefix_xor k x i (by omega)]
  simp [padVec, hi]

theorem grayToU_fromU (k : Nat) (u : Vec (k + 1)) (heven : parity (k + 1) u = false) :
    grayToU k (grayFromU k u) = u := by
  funext ⟨i, hi⟩
  by_cases hik : i < k
  · simp only [grayToU, padVec, hik, dite_true, grayFromU]
    cases i with
    | zero =>
        simp [xorRange, padVec]
    | succ i' =>
        have hi'_lt : i' < k := by omega
        simp only [Nat.succ_ne_zero, ite_false, hi'_lt, dite_true, Nat.add_sub_cancel]
        rw [xorRange]
        simp only [padVec, hi, dite_true]
        cases xorRange (padVec (k + 1) u) (i' + 1) <;> cases u ⟨i' + 1, hi⟩ <;> rfl
  · have hik_eq : i = k := by omega
    subst i
    have hpar : xorRange (padVec (k + 1) u) (k + 1) = false := by
      rw [parity_eq_xorRange] at heven
      exact heven
    rw [xorRange] at hpar
    simp only [padVec, Nat.lt_succ_self, dite_true] at hpar
    cases k with
    | zero =>
        simp only [grayToU, padVec, Nat.lt_irrefl, dite_false, ite_true, Bool.false_xor]
        simp [xorRange] at hpar
        exact hpar.symm
    | succ k' =>
        simp only [grayToU, padVec, Nat.lt_irrefl, dite_false, Nat.succ_ne_zero, ite_false,
                   Nat.add_sub_cancel, Nat.lt_succ_self, dite_true, grayFromU, Bool.false_xor]
        cases hpref : xorRange (padVec (k' + 2) u) (k' + 1) <;>
          cases hu : u ⟨k' + 1, Nat.lt_succ_self _⟩ <;> simp [hpref, hu] at hpar ⊢

/-- Concrete Hyperplane-Rotation Certificate for Gray code G_k (n = k+1, r = 0). -/
def grayHyperplaneCert (k : Nat) : HyperplaneRotCert k (k + 1) 0 (grayIso k) where
  hn := Nat.succ_le_succ (Nat.zero_le k)
  toU := grayToU k
  toS := fun _ => zeroVec 0
  fromUS := fun u _ => grayFromU k u
  even_U := grayToU_even k
  left_inv := grayFromU_toU k
  right_inv_U := fun u _ h => grayToU_fromU k u h
  right_inv_S := fun _ s _ => vec0_eq (zeroVec 0) s
  conj_U := fun x => by
    let y : Vec k := (grayIso k).defect.fwd x
    have hgy : grayAdj k y = grayFwd k x := (grayIso k).adj_adjInv (grayFwd k x)
    funext ⟨i, hi⟩
    by_cases hik : i < k
    · have h1 : grayToU k y ⟨i, hi⟩ = grayAdj k y ⟨i, hik⟩ := by
        simp [grayToU, grayAdj, padVec, hik]
      have h2 : rot1 (k + 1) (grayToU k x) ⟨i, hi⟩ = grayFwd k x ⟨i, hik⟩ := by
        simp only [rot1, grayToU, grayFwd]
        have hmod : (i + 1) % (k + 1) = i + 1 := Nat.mod_eq_of_lt (by omega)
        simp only [hmod, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel, padVec, hik, dite_true]
        exact Bool.xor_comm _ _
      rw [h1, hgy, h2]
    · have hik_eq : i = k := by omega
      subst i
      have hparY : xorRange (padVec (k + 1) (grayToU k y)) (k + 1) = false := by
        have h := grayToU_even k y; rw [parity_eq_xorRange] at h; exact h
      have hparX : xorRange (padVec (k + 1) (grayToU k x)) (k + 1) = false := by
        have h := grayToU_even k x; rw [parity_eq_xorRange] at h; exact h
      rw [xorRange] at hparY
      rw [xorRange_split _ (Nat.add_comm k 1)] at hparX
      have hfirst : xorRange (padVec (k + 1) (grayToU k x)) 1 = grayToU k x ⟨0, Nat.zero_lt_succ k⟩ := by
        simp [xorRange, padVec]
      rw [hfirst] at hparX
      have hmid : xorRange (padVec (k + 1) (grayToU k y)) k =
                  xorRange (fun j => padVec (k + 1) (grayToU k x) (1 + j)) k := by
        apply xorRange_congr
        intro j hj
        have hj1 : 1 + j < k + 1 := by omega
        have hj0 : j < k + 1 := by omega
        simp only [padVec, hj0, hj1, dite_true]
        have h1 : grayToU k y ⟨j, hj0⟩ = grayAdj k y ⟨j, hj⟩ := by
          simp [grayToU, grayAdj, padVec, hj]
        have h2 : grayToU k x ⟨1 + j, hj1⟩ = grayFwd k x ⟨j, hj⟩ := by
          have h1j : 1 + j = j + 1 := by omega
          have hfin : (⟨1 + j, hj1⟩ : Fin (k + 1)) = ⟨j + 1, by omega⟩ := Fin.ext h1j
          rw [hfin]
          simp only [grayToU, grayFwd, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel,
                     padVec, hj, dite_true]
          exact Bool.xor_comm _ _
        rw [h1, hgy, h2]
      rw [hmid] at hparY
      have hpLast : padVec (k + 1) (grayToU k y) k = grayToU k y ⟨k, Nat.lt_succ_self k⟩ := by
        simp [padVec]
      rw [hpLast] at hparY
      have hmod0 : (k + 1) % (k + 1) = 0 := Nat.mod_self (k + 1)
      have hrot : rot1 (k + 1) (grayToU k x) ⟨k, Nat.lt_succ_self k⟩ =
                  grayToU k x ⟨0, Nat.zero_lt_succ k⟩ := by
        simp only [rot1]
        congr 1; apply Fin.ext; dsimp; exact hmod0
      rw [hrot]
      have hY : (xorRange (fun j => padVec (k + 1) (grayToU k x) (1 + j)) k ^^
                 grayToU k y ⟨k, Nat.lt_succ_self k⟩) = false := hparY
      have hX : (grayToU k x ⟨0, Nat.zero_lt_succ k⟩ ^^
                 xorRange (fun j => padVec (k + 1) (grayToU k x) (1 + j)) k) = false := hparX
      revert hY hX
      cases xorRange (fun j => padVec (k + 1) (grayToU k x) (1 + j)) k <;>
        cases grayToU k y ⟨k, Nat.lt_succ_self k⟩ <;>
        cases grayToU k x ⟨0, Nat.zero_lt_succ k⟩ <;> decide
  conj_S := fun _ => rfl

/-- Alternating-bit vector b_i = (i % 2 == 0) for k = 4r + 1. -/
def altVec (k : Nat) : Vec k := fun i => decide (i.val % 2 = 0)

def loHalf {r : Nat} (x : Vec (2 * r)) : Vec r := fun i => x ⟨i.val, by omega⟩
def hiHalf {r : Nat} (x : Vec (2 * r)) : Vec r := fun i => x ⟨r + i.val, by omega⟩

def blockGrayFwd (r : Nat) (x : Vec (2 * r)) : Vec (2 * r) :=
  fun i =>
    if h : i.val < r then grayFwd r (hiHalf x) ⟨i.val, h⟩
    else grayAdj r (loHalf x) ⟨i.val - r, by omega⟩

def blockGrayInv (r : Nat) (x : Vec (2 * r)) : Vec (2 * r) :=
  fun i =>
    if h : i.val < r then grayAdjInv r (hiHalf x) ⟨i.val, h⟩
    else grayInv r (loHalf x) ⟨i.val - r, by omega⟩

theorem blockGray_fwd_inv (r : Nat) (x : Vec (2 * r)) :
    blockGrayFwd r (blockGrayInv r x) = x := by
  funext ⟨i, hi⟩
  by_cases hir : i < r
  · simp only [blockGrayFwd, hir, dite_true]
    have hhi : hiHalf (blockGrayInv r x) = grayInv r (loHalf x) := by
      funext ⟨j, hj⟩
      have hge : ¬(r + j < r) := by omega
      have hsub : r + j - r = j := by omega
      simp only [hiHalf, blockGrayInv, hge, dite_false, hsub]
    rw [hhi, grayFwd_inv]; rfl
  · simp only [blockGrayFwd, hir, dite_false]
    have hlo : loHalf (blockGrayInv r x) = grayAdjInv r (hiHalf x) := by
      funext ⟨j, hj⟩
      simp only [loHalf, blockGrayInv, hj, dite_true]
    rw [hlo, grayAdj_inv]
    simp only [hiHalf]
    congr 1; apply Fin.ext; dsimp; omega

theorem blockGray_inv_fwd (r : Nat) (x : Vec (2 * r)) :
    blockGrayInv r (blockGrayFwd r x) = x := by
  funext ⟨i, hi⟩
  by_cases hir : i < r
  · simp only [blockGrayInv, hir, dite_true]
    have hhi : hiHalf (blockGrayFwd r x) = grayAdj r (loHalf x) := by
      funext ⟨j, hj⟩
      have hge : ¬(r + j < r) := by omega
      have hsub : r + j - r = j := by omega
      simp only [hiHalf, blockGrayFwd, hge, dite_false, hsub]
    rw [hhi, grayAdjInv_adj]; rfl
  · simp only [blockGrayInv, hir, dite_false]
    have hlo : loHalf (blockGrayFwd r x) = grayFwd r (hiHalf x) := by
      funext ⟨j, hj⟩
      simp only [loHalf, blockGrayFwd, hj, dite_true]
    rw [hlo, grayInv_fwd]
    simp only [hiHalf]
    congr 1; apply Fin.ext; dsimp; omega

theorem dot_split_halves (r : Nat) (x y : Vec (2 * r)) :
    dot (2 * r) x y = (dot r (loHalf x) (loHalf y) ^^ dot r (hiHalf x) (hiHalf y)) := by
  rw [dot_eq_xorRange, dot_eq_xorRange, dot_eq_xorRange]
  rw [xorRange_split _ (Nat.two_mul r)]
  congr 1
  · apply xorRange_congr
    intro i hi
    have hi2 : i < 2 * r := by omega
    simp [padVec, hi, hi2, loHalf]
  · apply xorRange_congr
    intro i hi
    have hi2 : r + i < 2 * r := by omega
    simp [padVec, hi, hi2, hiHalf]

theorem dot_blockGray_sym (r : Nat) (x y : Vec (2 * r)) :
    dot (2 * r) x (blockGrayFwd r y) = dot (2 * r) (blockGrayFwd r x) y := by
  rw [dot_split_halves, dot_split_halves]
  have hlo : ∀ z : Vec (2 * r), loHalf (blockGrayFwd r z) = grayFwd r (hiHalf z) := by
    intro z; funext ⟨j, hj⟩; simp [loHalf, blockGrayFwd, hj]
  have hhi : ∀ z : Vec (2 * r), hiHalf (blockGrayFwd r z) = grayAdj r (loHalf z) := by
    intro z; funext ⟨j, hj⟩
    have hge : ¬(r + j < r) := by omega
    have hsub : r + j - r = j := by omega
    simp [hiHalf, blockGrayFwd, hge, hsub]
  rw [hlo y, hhi y, hlo x, hhi x, dot_gray_adj r (loHalf x) (hiHalf y),
      dot_comm r (hiHalf x) (grayAdj r (loHalf y)), ← dot_gray_adj r (loHalf y) (hiHalf x),
      dot_comm r (loHalf y) (grayFwd r (hiHalf x)), Bool.xor_comm]

def blockGrayIso (r : Nat) : LinIso (2 * r) where
  fwd := blockGrayFwd r
  inv := blockGrayInv r
  adj := blockGrayFwd r
  adjInv := blockGrayInv r
  fwd_inv := blockGray_fwd_inv r
  inv_fwd := blockGray_inv_fwd r
  adj_adjInv := blockGray_fwd_inv r
  adjInv_adj := blockGray_inv_fwd r
  dot_adj := dot_blockGray_sym r

def grayBitrevIso (k : Nat) : LinIso k :=
  (grayIso k).comp (bitrevIso k)

def grayRotIso (k : Nat) : LinIso k :=
  (grayIso k).comp (rotL1Iso k)

/-- Explicit coordinate formula for Δ(G_k C_k) at width k = n + 2 (k ≥ 2):
    y_0 = x_n,  y_i = x_{i-1} ^^ x_n ^^ x_{n+1} (1 ≤ i ≤ n),  y_{n+1} = x_{n+1}. -/
def grayRotDefectExplicit (n : Nat) (x : Vec (n + 2)) : Vec (n + 2) :=
  fun i =>
    if i.val = 0 then x ⟨n, by omega⟩
    else if i.val ≤ n then x ⟨i.val - 1, by omega⟩ ^^ x ⟨n, by omega⟩ ^^ x ⟨n + 1, by omega⟩
    else x ⟨n + 1, by omega⟩

theorem rotL1_eval (k : Nat) (x : Vec k) (j : Nat) (hj : j < k) :
    rotL1 k x ⟨j, hj⟩ =
    if j = 0 then x ⟨k - 1, by omega⟩ else x ⟨j - 1, by omega⟩ := by
  simp only [rotL1]
  cases j with
  | zero =>
      simp only [ite_true]
      congr 1; apply Fin.ext; dsimp
      have h1 : 0 + k - 1 = k - 1 := by omega
      rw [h1]; exact Nat.mod_eq_of_lt (by omega)
  | succ j' =>
      simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
      congr 1; apply Fin.ext; dsimp
      have h1 : j' + 1 + k - 1 = j' + k := by omega
      rw [h1, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)

theorem grayRot_defect_eq_explicit (n : Nat) (x : Vec (n + 2)) :
    (grayRotIso (n + 2)).defect.fwd x = grayRotDefectExplicit n x := by
  let y := grayRotDefectExplicit n x
  have hcheck : grayAdj (n + 2) y = rotL1 (n + 2) (grayFwd (n + 2) (rotL1 (n + 2) x)) := by
    funext ⟨i, hi⟩
    rw [rotL1_eval (n + 2) (grayFwd (n + 2) (rotL1 (n + 2) x)) i hi]
    cases i with
    | zero =>
        simp only [grayAdj, ite_true, Bool.xor_false, y, grayRotDefectExplicit, grayFwd]
        have hge : ¬(n + 2 - 1 + 1 < n + 2) := by omega
        simp only [padVec, hge, dite_false, Bool.xor_false]
        rw [rotL1_eval (n + 2) x (n + 2 - 1) (by omega)]
        have hne : n + 2 - 1 ≠ 0 := by omega
        simp only [hne, ite_false]
        exact congrArg x (Fin.ext rfl)
    | succ i' =>
        simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
        have hi'_lt : i' < n + 2 := by omega
        simp only [grayAdj, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel,
                   padVec, hi'_lt, hi, dite_true, grayFwd]
        rw [rotL1_eval (n + 2) x i' hi'_lt, rotL1_eval (n + 2) x (i' + 1) hi]
        simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
        cases i' with
        | zero =>
            simp only [ite_true]
            by_cases hn0 : 1 ≤ n
            · simp only [y, grayRotDefectExplicit, Nat.succ_ne_zero, ite_false, hn0, ite_true]
              have hlast : x ⟨n + 2 - 1, by omega⟩ = x ⟨n + 1, by omega⟩ :=
                congrArg x (Fin.ext rfl)
              rw [hlast]
              cases x ⟨0, by omega⟩ <;> cases x ⟨n, by omega⟩ <;> cases x ⟨n + 1, by omega⟩ <;> rfl
            · have hn_eq : n = 0 := by omega
              subst hn_eq
              simp only [y, grayRotDefectExplicit]
              have h10 : ¬(1 ≤ 0) := by omega
              simp only [Nat.succ_ne_zero, ite_false, ite_true, h10]
        | succ i'' =>
            have hne1 : i'' + 1 ≠ 0 := by omega
            simp only [hne1, ite_false, Nat.add_sub_cancel]
            by_cases hle : i'' + 2 ≤ n
            · have hle' : i'' + 1 ≤ n := by omega
              simp only [y, grayRotDefectExplicit, Nat.succ_ne_zero, ite_false, hle, hle', ite_true,
                         Nat.add_sub_cancel]
              cases x ⟨i'' + 1, by omega⟩ <;> cases x ⟨i'', by omega⟩ <;>
                cases x ⟨n, by omega⟩ <;> cases x ⟨n + 1, by omega⟩ <;> rfl
            · have hi''_eq : i'' + 1 = n := by omega
              have hle' : i'' + 1 ≤ n := by omega
              simp only [y, grayRotDefectExplicit, Nat.succ_ne_zero, ite_false, hle, hle', ite_true,
                         Nat.add_sub_cancel]
              have hx_eq : x ⟨i'' + 1, hi'_lt⟩ = x ⟨n, by omega⟩ :=
                congrArg x (Fin.ext hi''_eq)
              rw [hx_eq]
              cases x ⟨i'', by omega⟩ <;> cases x ⟨n, by omega⟩ <;>
                cases x ⟨n + 1, by omega⟩ <;> rfl
  show grayAdjInv (n + 2) (rotL1 (n + 2) (grayFwd (n + 2) (rotL1 (n + 2) x))) = y
  rw [← hcheck, grayAdjInv_adj]

/-- Hyperplane-Rotation Certificate for Gray ∘ Cyclic Butterfly Rotation at width k = n + 2:
    intertwines Δ(G_{n+2} C_{n+2}) with (rot1 (n+2) on even-parity H_{n+1}) × id_1! -/
def grayRotToU (n : Nat) (x : Vec (n + 2)) : Vec (n + 2) :=
  bitrevVec (n + 2) (grayToU (n + 1) (fun j => x ⟨j.val, by omega⟩ ^^ x ⟨n + 1, by omega⟩))

def grayRotToS (n : Nat) (x : Vec (n + 2)) : Vec 1 :=
  fun _ => x ⟨n + 1, by omega⟩

def grayRotFromUS (n : Nat) (u : Vec (n + 2)) (s : Vec 1) : Vec (n + 2) :=
  let x' := grayFromU (n + 1) (bitrevVec (n + 2) u)
  let s0 := s ⟨0, Nat.zero_lt_one⟩
  fun i => if h : i.val < n + 1 then x' ⟨i.val, h⟩ ^^ s0 else s0

def grayRotHyperplaneCert (n : Nat) : HyperplaneRotCert (n + 2) (n + 2) 1 (grayRotIso (n + 2)) where
  hn := by omega
  toU := grayRotToU n
  toS := grayRotToS n
  fromUS := grayRotFromUS n
  even_U := fun x => by
    unfold grayRotToU
    rw [parity_bitrev]
    exact grayToU_even (n + 1) _
  left_inv := fun x => by
    funext ⟨i, hi⟩
    simp only [grayRotFromUS, grayRotToU, grayRotToS, bitrevVec_invol, grayFromU_toU]
    by_cases hlt : i < n + 1
    · simp only [hlt, dite_true]
      cases x ⟨i, hi⟩ <;> cases x ⟨n + 1, by omega⟩ <;> rfl
    · have heq : i = n + 1 := by omega
      subst heq
      simp only [hlt, dite_false]
  right_inv_U := fun u s heven => by
    unfold grayRotToU
    have hpar : parity (n + 2) (bitrevVec (n + 2) u) = false := by
      rw [parity_bitrev]; exact heven
    have hinner : (fun j : Fin (n + 1) =>
        grayRotFromUS n u s ⟨j.val, by omega⟩ ^^ grayRotFromUS n u s ⟨n + 1, by omega⟩) =
        grayFromU (n + 1) (bitrevVec (n + 2) u) := by
      funext ⟨j, hj⟩
      have hge : ¬(n + 1 < n + 1) := Nat.lt_irrefl _
      simp only [grayRotFromUS, hj, hge, dite_true, dite_false]
      cases grayFromU (n + 1) (bitrevVec (n + 2) u) ⟨j, hj⟩ <;>
        cases s ⟨0, Nat.zero_lt_one⟩ <;> rfl
    rw [hinner, grayToU_fromU (n + 1) (bitrevVec (n + 2) u) hpar, bitrevVec_invol]
  right_inv_S := fun u s _ => by
    funext ⟨i, hi⟩
    have hi0 : i = 0 := by omega
    subst hi0
    have hge : ¬(n + 1 < n + 1) := Nat.lt_irrefl _
    simp [grayRotToS, grayRotFromUS, hge]
  conj_U := fun x => by
    rw [grayRot_defect_eq_explicit n x]
    let y := grayRotDefectExplicit n x
    -- Let u_x = grayToU (n+1) (x_j ^^ x_{n+1}), u_y = grayToU (n+1) (y_j ^^ y_{n+1}).
    -- Show u_y = rotL1 (n+2) u_x, then bitrev reverses rotL1 into rot1!
    let ux := grayToU (n + 1) (fun j => x ⟨j.val, by omega⟩ ^^ x ⟨n + 1, by omega⟩)
    let uy := grayToU (n + 1) (fun j => y ⟨j.val, by omega⟩ ^^ y ⟨n + 1, by omega⟩)
    have huy : uy = rotL1 (n + 2) ux := by
      funext ⟨j, hj⟩
      have hy_last : y ⟨n + 1, by omega⟩ = x ⟨n + 1, by omega⟩ := by
        have hgt : ¬(n + 1 ≤ n) := by omega
        simp [y, grayRotDefectExplicit, hgt]
      cases j with
      | zero =>
          have hm : (0 + (n + 2) - 1) % (n + 2) = n + 1 := by
            have : 0 + (n + 2) - 1 = n + 1 := by omega
            rw [this]; exact Nat.mod_eq_of_lt (by omega)
          simp only [uy, ux, rotL1, hm, grayToU, padVec, Nat.zero_lt_succ, dite_true,
                     ite_true, Bool.xor_false, Nat.lt_irrefl, dite_false,
                     Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel, Nat.lt_succ_self,
                     Bool.false_xor, hy_last]
          simp [y, grayRotDefectExplicit]
      | succ j' =>
          have hm : (j' + 1 + (n + 2) - 1) % (n + 2) = j' := by
            have : j' + 1 + (n + 2) - 1 = j' + (n + 2) := by omega
            rw [this, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
          by_cases hj'n : j' < n
          · have hj_lt : j' + 1 < n + 1 := by omega
            have hj'_lt : j' < n + 1 := by omega
            have hj_le : j' + 1 ≤ n := by omega
            simp only [uy, ux, rotL1, hm, grayToU, padVec, hj_lt, hj'_lt, dite_true,
                       Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel, hy_last]
            cases j' with
            | zero =>
                simp only [ite_true, Bool.xor_false, y, grayRotDefectExplicit,
                           Nat.succ_ne_zero, ite_false, hj_le, Nat.add_sub_cancel]
                cases x ⟨0, by omega⟩ <;> cases x ⟨n, by omega⟩ <;> cases x ⟨n + 1, by omega⟩ <;> rfl
            | succ j'' =>
                have hj''_le : j'' + 1 ≤ n := by omega
                have hj''_lt : j'' < n + 1 := by omega
                simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel, hj''_lt, dite_true,
                           y, grayRotDefectExplicit, hj_le, hj''_le]
                cases x ⟨j'' + 1, by omega⟩ <;> cases x ⟨j'', by omega⟩ <;>
                  cases x ⟨n, by omega⟩ <;> cases x ⟨n + 1, by omega⟩ <;> rfl
          · have hj'_eq : j' = n := by omega
            subst j'
            simp only [uy, ux, rotL1, hm, grayToU, padVec, Nat.lt_irrefl, dite_false,
                       Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel, Nat.lt_succ_self,
                       dite_true, Bool.false_xor, hy_last]
            cases n with
            | zero =>
                simp [y, grayRotDefectExplicit]
            | succ n' =>
                have hn'_lt : n' < n' + 2 := by omega
                simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel, hn'_lt, dite_true,
                           y, grayRotDefectExplicit, Nat.le_refl]
                cases x ⟨n', by omega⟩ <;> cases x ⟨n' + 1, by omega⟩ <;>
                  cases x ⟨n' + 2, by omega⟩ <;> rfl
    show bitrevVec (n + 2) uy = rot1 (n + 2) (bitrevVec (n + 2) ux)
    rw [huy]
    funext ⟨i, hi⟩
    simp only [bitrevVec, rotL1, rot1]
    congr 1; apply Fin.ext; dsimp
    by_cases hlt : i + 1 < n + 2
    · have h1 : (i + 1) % (n + 2) = i + 1 := Nat.mod_eq_of_lt hlt
      have h2 : n + 1 - i + (n + 1) = (n + 1 - (i + 1)) + (n + 2) := by omega
      rw [h1, h2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · have heq : i = n + 1 := by omega
      subst i
      have h1 : (n + 1 + 1) % (n + 2) = 0 := Nat.mod_self (n + 2)
      have h2 : n + 1 - (n + 1) + (n + 1) = n + 1 := by omega
      rw [h1, h2, Nat.mod_eq_of_lt (by omega)]
      omega
  conj_S := fun x => by
    rw [grayRot_defect_eq_explicit n x]
    funext ⟨i, hi⟩
    have hgt : ¬(n + 1 ≤ n) := by omega
    simp [grayRotToS, grayRotDefectExplicit, hgt]

def inc2Vec (x : Vec 2) : Vec 2 :=
  fun i =>
    match i with
    | ⟨0, _⟩ => !x ⟨0, by omega⟩
    | ⟨1, _⟩ => x ⟨0, by omega⟩ ^^ x ⟨1, by omega⟩

end SiliconSpectral

-- ============================================================================
-- AXIOM AUDIT (#print axioms on EVERY main engine & concrete theorem)
-- ============================================================================
