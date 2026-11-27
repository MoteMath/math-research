/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions (`two-group-ryser-permanent-congruences`)

Permanent Mod 2^r and Ryser-Bitmask Exact Congruence Engine: definitions and sorry-free helper lemmas (pure Lean 4 `Init`, zero Mathlib).
-/

set_option autoImplicit false
namespace SpecMat9


-- ============================================================================
-- SECTION 1: Core List Sums, Products, Permutations, and Bijections
-- ============================================================================

def sumInt {α : Type} (l : List α) (f : α → Int) : Int :=
  l.foldr (fun x acc => f x + acc) 0

def prodInt {α : Type} (l : List α) (f : α → Int) : Int :=
  l.foldr (fun x acc => f x * acc) 1

@[simp] theorem sumInt_nil {α : Type} (f : α → Int) : sumInt [] f = 0 := rfl
@[simp] theorem sumInt_cons {α : Type} (x : α) (xs : List α) (f : α → Int) :
    sumInt (x :: xs) f = f x + sumInt xs f := rfl

@[simp] theorem prodInt_nil {α : Type} (f : α → Int) : prodInt [] f = 1 := rfl
@[simp] theorem prodInt_cons {α : Type} (x : α) (xs : List α) (f : α → Int) :
    prodInt (x :: xs) f = f x * prodInt xs f := rfl

theorem sumInt_append {α : Type} (l₁ l₂ : List α) (f : α → Int) :
    sumInt (l₁ ++ l₂) f = sumInt l₁ f + sumInt l₂ f := by
  induction l₁ with
  | nil => simp
  | cons x xs ih => simp [ih]; omega

instance instDecidableEqFinFun {n : Nat} {α : Type} [DecidableEq α] :
    DecidableEq (Fin n → α) := fun f g =>
  if h : (List.finRange n).all (fun i => decide (f i = g i)) = true then
    isTrue (by
      funext i
      have hi : i ∈ List.finRange n := List.mem_finRange i
      have hall := List.all_eq_true.mp h i hi
      exact of_decide_eq_true hall)
  else
    isFalse (by
      intro hfg
      apply h
      rw [List.all_eq_true]
      intro i _
      exact decide_eq_true (congrFun hfg i))

def consFinFun {m : Nat} {α : Type} (a : α) (f : Fin m → α) : Fin (m + 1) → α :=
  fun i => if h : i.val = 0 then a else f ⟨i.val - 1, by omega⟩

def allFnsToList {α : Type} (dom : List α) : (m : Nat) → List (Fin m → α)
  | 0 => [fun i => Fin.elim0 i]
  | m + 1 => dom.flatMap (fun a => (allFnsToList dom m).map (consFinFun a))

abbrev Mask (n : Nat) := Fin n → Bool

abbrev Mat (n : Nat) := Fin n → Fin n → Int

def allMasks (n : Nat) : List (Mask n) := allFnsToList [false, true] n

def allFns (m n : Nat) : List (Fin m → Fin n) := allFnsToList (List.finRange n) m

def isSurjective (n : Nat) (f : Fin n → Fin n) : Bool :=
  (List.finRange n).all (fun j => (List.finRange n).any (fun i => decide (f i = j)))

def dedup {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => if x ∈ xs then dedup xs else x :: dedup xs

/-- Genuine permanent of an n×n integer matrix: sum over all bijections Fin n → Fin n. -/
def perm (n : Nat) (A : Mat n) : Int :=
  sumInt ((allFns n n).filter (isSurjective n))
    (fun f => prodInt (List.finRange n) (fun i => A i (f i)))

def maskCard (n : Nat) (S : Mask n) : Nat :=
  ((List.finRange n).filter S).length

def rowSum (n : Nat) (A : Mat n) (S : Mask n) (i : Fin n) : Int :=
  sumInt ((List.finRange n).filter S) (fun j => A i j)

def rowProd (n : Nat) (A : Mat n) (S : Mask n) : Int :=
  prodInt (List.finRange n) (rowSum n A S)

def ryserSign (n : Nat) (S : Mask n) : Int :=
  if (n - maskCard n S) % 2 = 0 then 1 else -1

def ryserSum (n : Nat) (A : Mat n) : Int :=
  sumInt (allMasks n) (fun S => ryserSign n S * rowProd n A S)

def fnInMask {m n : Nat} (S : Mask n) (f : Fin m → Fin n) : Bool :=
  (List.finRange m).all (fun i => S (f i))

def flipMask {n : Nat} (j₀ : Fin n) (S : Mask n) : Mask n :=
  fun j => if j = j₀ then !S j else S j

structure Fin2Group (k : Nat) where
  G : Type
  [decEq : DecidableEq G]
  elems : List G
  nodup : elems.Nodup
  complete : ∀ g : G, g ∈ elems
  card : elems.length = 2 ^ k
  one : G
  mul : G → G → G
  inv : G → G
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  inv_mul : ∀ a, mul (inv a) a = one

attribute [instance] Fin2Group.decEq

namespace Fin2Group

variable {k : Nat} (Gr : Fin2Group k)

theorem mul_left_cancel {a b c : Gr.G} (h : Gr.mul a b = Gr.mul a c) : b = c := by
  have h1 := congrArg (Gr.mul (Gr.inv a)) h
  rw [← Gr.mul_assoc, ← Gr.mul_assoc, Gr.inv_mul, Gr.one_mul, Gr.one_mul] at h1
  exact h1

theorem mul_inv (a : Gr.G) : Gr.mul a (Gr.inv a) = Gr.one := by
  let x := Gr.mul a (Gr.inv a)
  have hxx : Gr.mul x x = x := by
    calc Gr.mul (Gr.mul a (Gr.inv a)) (Gr.mul a (Gr.inv a))
        = Gr.mul a (Gr.mul (Gr.inv a) (Gr.mul a (Gr.inv a))) := Gr.mul_assoc _ _ _
      _ = Gr.mul a (Gr.mul (Gr.mul (Gr.inv a) a) (Gr.inv a)) := by rw [Gr.mul_assoc]
      _ = Gr.mul a (Gr.mul Gr.one (Gr.inv a)) := by rw [Gr.inv_mul]
      _ = Gr.mul a (Gr.inv a) := by rw [Gr.one_mul]
  have h1 := congrArg (Gr.mul (Gr.inv x)) hxx
  rw [← Gr.mul_assoc, Gr.inv_mul, Gr.one_mul] at h1
  exact h1

theorem mul_one (a : Gr.G) : Gr.mul a Gr.one = a := by
  rw [← Gr.inv_mul a, ← Gr.mul_assoc, Gr.mul_inv, Gr.one_mul]

theorem inv_inv (a : Gr.G) : Gr.inv (Gr.inv a) = a := by
  apply Gr.mul_left_cancel (a := Gr.inv a)
  rw [Gr.mul_inv, Gr.inv_mul]

theorem inv_one : Gr.inv Gr.one = Gr.one := by
  rw [← Gr.mul_one (Gr.inv Gr.one), Gr.inv_mul]

theorem inv_mul_rev (a b : Gr.G) : Gr.inv (Gr.mul a b) = Gr.mul (Gr.inv b) (Gr.inv a) := by
  apply Gr.mul_left_cancel (a := Gr.mul a b)
  rw [Gr.mul_inv, Gr.mul_assoc, ← Gr.mul_assoc b, Gr.mul_inv, Gr.one_mul, Gr.mul_inv]

end Fin2Group


structure GroupAction {k : Nat} (Gr : Fin2Group k) (X : Type) where
  act : Gr.G → X → X
  act_one : ∀ x, act Gr.one x = x
  act_mul : ∀ g h x, act (Gr.mul g h) x = act g (act h x)

def orbit {k : Nat} (Gr : Fin2Group k) {X : Type} [DecidableEq X]
    (A : GroupAction Gr X) (x : X) : List X :=
  dedup (Gr.elems.map (fun g => A.act g x))

def stab {k : Nat} (Gr : Fin2Group k) {X : Type} [DecidableEq X]
    (A : GroupAction Gr X) (x : X) : List Gr.G :=
  Gr.elems.filter (fun g => decide (A.act g x = x))

theorem mem_stab {k : Nat} (Gr : Fin2Group k) {X : Type} [DecidableEq X]
    (A : GroupAction Gr X) (x : X) (g : Gr.G) :
    g ∈ stab Gr A x ↔ A.act g x = x := by
  unfold stab
  simp [Gr.complete g]

theorem nodup_stab {k : Nat} (Gr : Fin2Group k) {X : Type} [DecidableEq X]
    (A : GroupAction Gr X) (x : X) : (stab Gr A x).Nodup :=
  Gr.nodup.filter _

theorem one_mem_stab {k : Nat} (Gr : Fin2Group k) {X : Type} [DecidableEq X]
    (A : GroupAction Gr X) (x : X) : Gr.one ∈ stab Gr A x :=
  (mem_stab Gr A x Gr.one).mpr (A.act_one x)

theorem mul_mem_stab {k : Nat} (Gr : Fin2Group k) {X : Type} [DecidableEq X]
    (A : GroupAction Gr X) (x : X) {g h : Gr.G}
    (hg : g ∈ stab Gr A x) (hh : h ∈ stab Gr A x) : Gr.mul g h ∈ stab Gr A x := by
  rw [mem_stab] at hg hh ⊢
  rw [A.act_mul, hh, hg]

theorem inv_mem_stab {k : Nat} (Gr : Fin2Group k) {X : Type} [DecidableEq X]
    (A : GroupAction Gr X) (x : X) {g : Gr.G} (hg : g ∈ stab Gr A x) :
    Gr.inv g ∈ stab Gr A x := by
  rw [mem_stab] at hg ⊢
  calc A.act (Gr.inv g) x
      = A.act (Gr.inv g) (A.act g x) := by rw [hg]
    _ = A.act (Gr.mul (Gr.inv g) g) x := (A.act_mul _ _ _).symm
    _ = x := by rw [Gr.inv_mul, A.act_one]

structure Subgroup {k : Nat} (Gr : Fin2Group k) where
  elems : List Gr.G
  nodup : elems.Nodup
  one_mem : Gr.one ∈ elems
  mul_mem : ∀ a b, a ∈ elems → b ∈ elems → Gr.mul a b ∈ elems
  inv_mem : ∀ a, a ∈ elems → Gr.inv a ∈ elems

def stabSubgroup {k : Nat} (Gr : Fin2Group k) {X : Type} [DecidableEq X]
    (A : GroupAction Gr X) (x : X) : Subgroup Gr where
  elems := stab Gr A x
  nodup := nodup_stab Gr A x
  one_mem := one_mem_stab Gr A x
  mul_mem := fun _ _ ha hb => mul_mem_stab Gr A x ha hb
  inv_mem := fun _ ha => inv_mem_stab Gr A x ha

structure FreeBiAction {k : Nat} (Gr : Fin2Group k) (n : Nat) where
  rowAct : GroupAction Gr (Fin n)
  colAct : GroupAction Gr (Fin n)
  row_free : ∀ g i, rowAct.act g i = i → g = Gr.one
  col_free : ∀ g j, colAct.act g j = j → g = Gr.one

def IsEquivariant {k n : Nat} {Gr : Fin2Group k} (BA : FreeBiAction Gr n) (A : Mat n) : Prop :=
  ∀ g i j, A (BA.rowAct.act g i) (BA.colAct.act g j) = A i j

def maskAct {k n : Nat} {Gr : Fin2Group k} (BA : FreeBiAction Gr n) : GroupAction Gr (Mask n) where
  act := fun g S j => S (BA.colAct.act (Gr.inv g) j)
  act_one := fun S => by funext j; rw [Gr.inv_one, BA.colAct.act_one]
  act_mul := fun g h S => by funext j; rw [Gr.inv_mul_rev, BA.colAct.act_mul]

def rowProdOdd (n : Nat) (A : Mat n) (S : Mask n) : Bool :=
  decide (rowProd n A S % 2 ≠ 0)

def oddSolCount (n : Nat) (A : Mat n) : Nat :=
  ((allMasks n).filter (rowProdOdd n A)).length

/-- Bitwise XOR on Fin (2^k) defined via core BitVec k. -/
def xorFin (k : Nat) (a b : Fin (2 ^ k)) : Fin (2 ^ k) :=
  ⟨(BitVec.ofNat k a.val ^^^ BitVec.ofNat k b.val).toNat, BitVec.isLt _⟩

theorem xorFin_toBitVec (k : Nat) (a b : Fin (2 ^ k)) :
    BitVec.ofNat k (xorFin k a b).val = BitVec.ofNat k a.val ^^^ BitVec.ofNat k b.val := by
  unfold xorFin
  simp

theorem fin_eq_of_bitvec_eq {k : Nat} {a b : Fin (2 ^ k)}
    (h : BitVec.ofNat k a.val = BitVec.ofNat k b.val) : a = b := by
  have hval := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at hval
  exact Fin.ext hval

def finZero (k : Nat) : Fin (2 ^ k) := ⟨0, Nat.two_pow_pos k⟩

theorem xorFin_assoc (k : Nat) (a b c : Fin (2 ^ k)) :
    xorFin k (xorFin k a b) c = xorFin k a (xorFin k b c) := by
  apply fin_eq_of_bitvec_eq
  rw [xorFin_toBitVec, xorFin_toBitVec, xorFin_toBitVec, xorFin_toBitVec, BitVec.xor_assoc]

theorem xorFin_comm (k : Nat) (a b : Fin (2 ^ k)) :
    xorFin k a b = xorFin k b a := by
  apply fin_eq_of_bitvec_eq
  rw [xorFin_toBitVec, xorFin_toBitVec, BitVec.xor_comm]

theorem xorFin_zero_left (k : Nat) (a : Fin (2 ^ k)) :
    xorFin k (finZero k) a = a := by
  apply fin_eq_of_bitvec_eq
  rw [xorFin_toBitVec]
  exact BitVec.zero_xor

theorem xorFin_zero_right (k : Nat) (a : Fin (2 ^ k)) :
    xorFin k a (finZero k) = a := by
  rw [xorFin_comm, xorFin_zero_left]

theorem xorFin_self (k : Nat) (a : Fin (2 ^ k)) :
    xorFin k a a = finZero k := by
  apply fin_eq_of_bitvec_eq
  rw [xorFin_toBitVec]
  exact BitVec.xor_self

theorem xorFin_eq_right_iff (k : Nat) (g x : Fin (2 ^ k)) :
    xorFin k g x = x ↔ g = finZero k := by
  constructor
  · intro h
    have h1 := congrArg (fun z => xorFin k z x) h
    rw [xorFin_assoc, xorFin_self, xorFin_zero_right] at h1
    exact h1
  · intro h; subst h; exact xorFin_zero_left k x

/-- Family 1: Elementary abelian 2-group (F_2^k, XOR) of order 2^k. -/
def xorGroup (k : Nat) : Fin2Group k where
  G := Fin (2 ^ k)
  elems := List.finRange (2 ^ k)
  nodup := List.nodup_finRange _
  complete := List.mem_finRange
  card := List.length_finRange
  one := finZero k
  mul := xorFin k
  inv := id
  mul_assoc := xorFin_assoc k
  one_mul := xorFin_zero_left k
  inv_mul := xorFin_self k

def xorFreeBiAction (k : Nat) : FreeBiAction (xorGroup k) (2 ^ k) where
  rowAct := {
    act := xorFin k
    act_one := xorFin_zero_left k
    act_mul := xorFin_assoc k
  }
  colAct := {
    act := xorFin k
    act_one := xorFin_zero_left k
    act_mul := xorFin_assoc k
  }
  row_free := fun g x h => (xorFin_eq_right_iff k g x).mp h
  col_free := fun g x h => (xorFin_eq_right_iff k g x).mp h

def xorCirc (k : Nat) (f : Fin (2 ^ k) → Int) : Mat (2 ^ k) :=
  fun i j => f (xorFin k i j)

/-- Family 2: Cyclic 2-group (Z / 2^k Z, +) of order 2^k. -/
def addFin (k : Nat) (a b : Fin (2 ^ k)) : Fin (2 ^ k) :=
  ⟨(a.val + b.val) % 2 ^ k, Nat.mod_lt _ (Nat.two_pow_pos k)⟩

def negFin (k : Nat) (a : Fin (2 ^ k)) : Fin (2 ^ k) :=
  ⟨(2 ^ k - a.val) % 2 ^ k, Nat.mod_lt _ (Nat.two_pow_pos k)⟩

theorem addFin_assoc (k : Nat) (a b c : Fin (2 ^ k)) :
    addFin k (addFin k a b) c = addFin k a (addFin k b c) := by
  apply Fin.ext
  change ((a.val + b.val) % 2 ^ k + c.val) % 2 ^ k = (a.val + (b.val + c.val) % 2 ^ k) % 2 ^ k
  have h1 : ((a.val + b.val) % 2 ^ k + c.val) % 2 ^ k = (a.val + b.val + c.val) % 2 ^ k := by
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have h2 : (a.val + (b.val + c.val) % 2 ^ k) % 2 ^ k = (a.val + (b.val + c.val)) % 2 ^ k := by
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  rw [h1, h2, Nat.add_assoc]

theorem addFin_zero_left (k : Nat) (a : Fin (2 ^ k)) :
    addFin k (finZero k) a = a := by
  apply Fin.ext
  change (0 + a.val) % 2 ^ k = a.val
  simp [Nat.mod_eq_of_lt a.isLt]

theorem addFin_neg_left (k : Nat) (a : Fin (2 ^ k)) :
    addFin k (negFin k a) a = finZero k := by
  apply Fin.ext
  change ((2 ^ k - a.val) % 2 ^ k + a.val) % 2 ^ k = 0
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.sub_add_cancel (Nat.le_of_lt a.isLt), Nat.mod_self]

theorem addFin_eq_right_iff (k : Nat) (g x : Fin (2 ^ k)) :
    addFin k g x = x ↔ g = finZero k := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    change (g.val + x.val) % 2 ^ k = x.val at hv
    apply Fin.ext
    change g.val = 0
    have hg := g.isLt
    have hx := x.isLt
    by_cases hsum : g.val + x.val < 2 ^ k
    · rw [Nat.mod_eq_of_lt hsum] at hv; omega
    · have hlt2 : g.val + x.val - 2 ^ k < 2 ^ k := by omega
      have hmod : (g.val + x.val) % 2 ^ k = g.val + x.val - 2 ^ k := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt2]
      rw [hmod] at hv; omega
  · intro h; subst h; exact addFin_zero_left k x

def cycGroup (k : Nat) : Fin2Group k where
  G := Fin (2 ^ k)
  elems := List.finRange (2 ^ k)
  nodup := List.nodup_finRange _
  complete := List.mem_finRange
  card := List.length_finRange
  one := finZero k
  mul := addFin k
  inv := negFin k
  mul_assoc := addFin_assoc k
  one_mul := addFin_zero_left k
  inv_mul := addFin_neg_left k

def cycFreeBiAction (k : Nat) : FreeBiAction (cycGroup k) (2 ^ k) where
  rowAct := {
    act := addFin k
    act_one := addFin_zero_left k
    act_mul := addFin_assoc k
  }
  colAct := {
    act := addFin k
    act_one := addFin_zero_left k
    act_mul := addFin_assoc k
  }
  row_free := fun g x h => (addFin_eq_right_iff k g x).mp h
  col_free := fun g x h => (addFin_eq_right_iff k g x).mp h

def cycCirc (k : Nat) (f : Fin (2 ^ k) → Int) : Mat (2 ^ k) :=
  fun i j => f (addFin k i (negFin k j))

theorem addFin_comm (k : Nat) (a b : Fin (2 ^ k)) :
    addFin k a b = addFin k b a := by
  apply Fin.ext
  change (a.val + b.val) % 2 ^ k = (b.val + a.val) % 2 ^ k
  rw [Nat.add_comm]

theorem negFin_addFin (k : Nat) (a b : Fin (2 ^ k)) :
    negFin k (addFin k a b) = addFin k (negFin k a) (negFin k b) := by
  have hrev := (cycGroup k).inv_mul_rev b a
  change negFin k (addFin k b a) = addFin k (negFin k a) (negFin k b) at hrev
  rw [addFin_comm k b a] at hrev
  exact hrev

/-- Family 3: Modular anti-circulant / carry-wrap matrices A_{i,j} = f((i + j) mod 2^k),
    with genuinely DISTINCT row action (i + g) and column action (j - g). -/
def antiCycFreeBiAction (k : Nat) : FreeBiAction (cycGroup k) (2 ^ k) where
  rowAct := {
    act := addFin k
    act_one := addFin_zero_left k
    act_mul := addFin_assoc k
  }
  colAct := {
    act := fun g j => addFin k (negFin k g) j
    act_one := fun j => by
      change addFin k (negFin k (finZero k)) j = j
      have h0 : negFin k (finZero k) = finZero k := by apply Fin.ext; simp [negFin, finZero]
      rw [h0, addFin_zero_left]
    act_mul := fun (g : Fin (2 ^ k)) (h : Fin (2 ^ k)) j => by
      change addFin k (negFin k (addFin k g h)) j = addFin k (negFin k g) (addFin k (negFin k h) j)
      rw [negFin_addFin k g h, addFin_assoc k]
  }
  row_free := fun g x h => (addFin_eq_right_iff k g x).mp h
  col_free := fun (g : Fin (2 ^ k)) x h => by
    have hneg : negFin k g = finZero k := (addFin_eq_right_iff k (negFin k g) x).mp h
    have hinv := (cycGroup k).inv_inv g
    change negFin k (negFin k g) = g at hinv
    rw [hneg] at hinv
    have h0 : negFin k (finZero k) = finZero k := by apply Fin.ext; simp [negFin, finZero]
    rw [h0] at hinv
    exact hinv.symm

def antiCyc (k : Nat) (f : Fin (2 ^ k) → Int) : Mat (2 ^ k) :=
  fun i j => f (addFin k i j)

/-- Family 4: Block XOR-circulant matrices of size (m * 2^k) × (m * 2^k), for all m ≥ 1, k ≥ 1. -/
theorem div_lt_two_pow_of_lt_mul {m k v : Nat} (hv : v < m * 2 ^ k) : v / m < 2 ^ k :=
  Nat.div_lt_of_lt_mul hv

def blockXorIdx (m k : Nat) (hm : 1 ≤ m) (g : Fin (2 ^ k)) (x : Fin (m * 2 ^ k)) : Fin (m * 2 ^ k) :=
  let blk : Fin (2 ^ k) := ⟨x.val / m, div_lt_two_pow_of_lt_mul x.isLt⟩
  let blk' := xorFin k g blk
  ⟨blk'.val * m + x.val % m, by
    have h1 : blk'.val + 1 ≤ 2 ^ k := blk'.isLt
    have h2 : x.val % m < m := Nat.mod_lt _ (by omega)
    have h3 : (blk'.val + 1) * m ≤ 2 ^ k * m := Nat.mul_le_mul_right m h1
    rw [Nat.add_mul, Nat.one_mul] at h3
    have hcomm : 2 ^ k * m = m * 2 ^ k := Nat.mul_comm _ _
    omega⟩

theorem blockXorIdx_div_mod (m k : Nat) (hm : 1 ≤ m) (g : Fin (2 ^ k)) (x : Fin (m * 2 ^ k)) :
    (blockXorIdx m k hm g x).val / m = (xorFin k g ⟨x.val / m, div_lt_two_pow_of_lt_mul x.isLt⟩).val ∧
    (blockXorIdx m k hm g x).val % m = x.val % m := by
  unfold blockXorIdx
  simp only []
  have hmod : x.val % m < m := Nat.mod_lt _ (by omega)
  have hmpos : 0 < m := by omega
  constructor
  · rw [Nat.mul_comm _ m, Nat.mul_add_div hmpos, Nat.div_eq_of_lt hmod, Nat.add_zero]
  · rw [Nat.mul_comm _ m, Nat.mul_add_mod, Nat.mod_eq_of_lt hmod]

theorem blockXorIdx_one (m k : Nat) (hm : 1 ≤ m) (x : Fin (m * 2 ^ k)) :
    blockXorIdx m k hm (finZero k) x = x := by
  apply Fin.ext
  have ⟨hd, hmod⟩ := blockXorIdx_div_mod m k hm (finZero k) x
  rw [xorFin_zero_left] at hd
  have hdiv_eq := (Nat.div_add_mod (blockXorIdx m k hm (finZero k) x).val m).symm
  rw [hdiv_eq, hd, hmod, Nat.div_add_mod]

theorem blockXorIdx_mul (m k : Nat) (hm : 1 ≤ m) (g h : Fin (2 ^ k)) (x : Fin (m * 2 ^ k)) :
    blockXorIdx m k hm (xorFin k g h) x = blockXorIdx m k hm g (blockXorIdx m k hm h x) := by
  apply Fin.ext
  have ⟨hd1, hm1⟩ := blockXorIdx_div_mod m k hm (xorFin k g h) x
  have ⟨hd2, hm2⟩ := blockXorIdx_div_mod m k hm g (blockXorIdx m k hm h x)
  have ⟨hd3, hm3⟩ := blockXorIdx_div_mod m k hm h x
  have hblk_eq : (⟨(blockXorIdx m k hm h x).val / m, div_lt_two_pow_of_lt_mul (blockXorIdx m k hm h x).isLt⟩ : Fin (2 ^ k)) =
      xorFin k h ⟨x.val / m, div_lt_two_pow_of_lt_mul x.isLt⟩ := Fin.ext hd3
  rw [hblk_eq, ← xorFin_assoc] at hd2
  have hL := (Nat.div_add_mod (blockXorIdx m k hm (xorFin k g h) x).val m).symm
  have hR := (Nat.div_add_mod (blockXorIdx m k hm g (blockXorIdx m k hm h x)).val m).symm
  rw [hL, hR, hd1, hm1, hd2, hm2, hm3]

def blockXorFreeBiAction (m k : Nat) (hm : 1 ≤ m) : FreeBiAction (xorGroup k) (m * 2 ^ k) where
  rowAct := {
    act := blockXorIdx m k hm
    act_one := blockXorIdx_one m k hm
    act_mul := blockXorIdx_mul m k hm
  }
  colAct := {
    act := blockXorIdx m k hm
    act_one := blockXorIdx_one m k hm
    act_mul := blockXorIdx_mul m k hm
  }
  row_free := fun (g : Fin (2 ^ k)) x h => by
    have ⟨hd, _⟩ := blockXorIdx_div_mod m k hm g x
    change blockXorIdx m k hm g x = x at h
    rw [h] at hd
    exact (xorFin_eq_right_iff k g _).mp (Fin.ext hd.symm)
  col_free := fun (g : Fin (2 ^ k)) x h => by
    have ⟨hd, _⟩ := blockXorIdx_div_mod m k hm g x
    change blockXorIdx m k hm g x = x at h
    rw [h] at hd
    exact (xorFin_eq_right_iff k g _).mp (Fin.ext hd.symm)

-- Concrete Corollaries of Theorem 1 for all 3 circulant/anti-circulant families:

def rowSumAll (k : Nat) (f : Fin (2 ^ k) → Int) : Int :=
  sumInt (List.finRange (2 ^ k)) f

def conv2 (k : Nat) (f : Fin (2 ^ k) → Int) (S : Mask (2 ^ k)) : Mask (2 ^ k) :=
  fun i => decide (rowSum (2 ^ k) (xorCirc k f) S i % 2 ≠ 0)

def xorMask {n : Nat} (S₁ S₂ : Mask n) : Mask n :=
  fun i => xor (S₁ i) (S₂ i)

def allTrueMask (n : Nat) : Mask n := fun _ => true

def allFalseMask (n : Nat) : Mask n := fun _ => false

def oddCount (k : Nat) (f : Fin (2 ^ k) → Int) : Nat :=
  ((List.finRange (2 ^ k)).filter (fun z => decide (f z % 2 ≠ 0))).length

def evenSum (k : Nat) (f : Fin (2 ^ k) → Int) : Int :=
  sumInt ((List.finRange (2 ^ k)).filter (fun z => decide (f z % 2 = 0))) f

def oddSum (k : Nat) (f : Fin (2 ^ k) → Int) : Int :=
  sumInt ((List.finRange (2 ^ k)).filter (fun z => decide (f z % 2 ≠ 0))) f

def evenRowMask (k : Nat) (f : Fin (2 ^ k) → Int) (S : Mask (2 ^ k)) : Mask (2 ^ k) :=
  fun i => !(conv2 k f S i)

def evenRowList (k : Nat) (f : Fin (2 ^ k) → Int) (S : Mask (2 ^ k)) : List (Fin (2 ^ k)) :=
  (List.finRange (2 ^ k)).filter (evenRowMask k f S)

def maskOfEvenRows (k : Nat) (f : Fin (2 ^ k) → Int) (E : Mask (2 ^ k)) : Mask (2 ^ k) :=
  xorMask (allTrueMask (2 ^ k)) (conv2 k f E)

/-- Defect-correction term for the mod-2^(k+2) Ryser collapse engine. -/
def defectCorr (k : Nat) (f : Fin (2 ^ k) → Int) (S : Mask (2 ^ k)) : Int :=
  match evenRowList k f S with
  | [] => 1
  | [_] => evenSum k f
  | [x, _] => 2 * rowSum (2 ^ k) (xorCirc k f) S x
  | _ => 0

def singleRowMask (k : Nat) (x : Fin (2 ^ k)) : Mask (2 ^ k) :=
  fun i => decide (i = x)

def pairRowMask (k : Nat) (x y : Fin (2 ^ k)) : Mask (2 ^ k) :=
  fun i => decide (i = x ∨ i = y)

def isPow2Nat (n : Nat) : Bool :=
  n != 0 && (n &&& (n - 1)) == 0

/-- Hypercube adjacency generator: f(z) = 1 iff z = 2^b for some bit b < k (popcount(z) = 1). -/
def hypercubeGen (k : Nat) (z : Fin (2 ^ k)) : Int :=
  if isPow2Nat z.val then 1 else 0

/-- Hypercube biadjacency generator (for Q_{k+1}, matrix size 2^k × 2^k):
    f(z) = 1 iff z = 0 or z = 2^b (gives exact perfect matching count M_{k+1} = perm(B_{k+1})). -/
def hypercubeBiadjGen (k : Nat) (z : Fin (2 ^ k)) : Int :=
  if z.val = 0 || isPow2Nat z.val then 1 else 0

def hypercubeAdj (k : Nat) : Mat (2 ^ k) := xorCirc k (hypercubeGen k)

def hypercubeBiadj (k : Nat) : Mat (2 ^ k) := xorCirc k (hypercubeBiadjGen k)

def derang4Gen : Fin (2 ^ 2) → Int := fun z => if z.val = 0 then 0 else 1

def diag1Gen : Fin (2 ^ 2) → Int := fun z => if z.val = 0 then 1 else 0

def diag3Gen : Fin (2 ^ 2) → Int := fun z => if z.val = 0 then 3 else 0

/-- SHARPNESS 4: Equivariance is SHARP — perturbing ONE entry of D_4 by +2 (leaving A mod 2
    completely unchanged!) destroys the mod-2^(k+1) congruence (perm = 13 ≡ 5 ≢ 1 mod 8). -/
def derang4Pert : Mat 4 := fun i j =>
  if i.val = 0 ∧ j.val = 0 then 2 else xorCirc 2 derang4Gen i j

/-- SHARPNESS 5: The 2-group hypothesis is SHARP — the 3×3 cyclic circulant circ(3, 2, 0)
    (under odd-order group Z/3Z) has odd row sum 5 and unique odd-row-sum subset, yet
    perm = 35 ≡ 3 ≢ 1 (mod 4). -/
def z3Circ320 : Mat 3 := fun i j =>
  match (i.val + 3 - j.val) % 3 with
  | 0 => 3
  | 1 => 2
  | _ => 0

end SpecMat9
