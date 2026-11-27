/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions (`boolean-tropical-kleene-star-engine`)

Boolean and Tropical-Bitwise Semiring Kleene-Star Infinite Engine: definitions and sorry-free helper lemmas (pure Lean 4 `Init`, zero Mathlib).
-/

namespace BSKSE


/-! ============================================================================
    SECTION 1: ABSTRACT KOZEN KLEENE SEMIRING & MATRIX KLEENE ALGEBRA
    ============================================================================ -/

/-- A Kozen Kleene algebra (idempotent semiring with least-fixpoint Kleene star).
    Order is defined algebraically by `le a b := add a b = b`. -/
class KleeneSemiring (α : Type u) where
  zero : α
  one  : α
  add  : α → α → α
  mul  : α → α → α
  star : α → α
  add_assoc     : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm      : ∀ a b, add a b = add b a
  add_zero      : ∀ a, add a zero = a
  add_idem      : ∀ a, add a a = a
  mul_assoc     : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul       : ∀ a, mul one a = a
  mul_one       : ∀ a, mul a one = a
  zero_mul      : ∀ a, mul zero a = zero
  mul_zero      : ∀ a, mul a zero = zero
  left_distrib  : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  right_distrib : ∀ a b c, mul (add a b) c = add (mul a c) (mul b c)
  one_le_star   : ∀ a, add one (star a) = star a
  mul_star_le   : ∀ a, add (mul a (star a)) (star a) = star a
  star_mul_le   : ∀ a, add (mul (star a) a) (star a) = star a
  star_ind_left : ∀ a b c, add (add b (mul a c)) c = c → add (mul (star a) b) c = c
  star_ind_right : ∀ a b c, add (add b (mul c a)) c = c → add (mul b (star a)) c = c

namespace KleeneSemiring

variable {α : Type u} [KleeneSemiring α]

/-- Natural join-semilattice partial order: `a ≤ b ↔ a + b = b`. -/
def le (a b : α) : Prop := add a b = b

end KleeneSemiring

section FinSum

variable {α : Type u} [KleeneSemiring α]

open KleeneSemiring

/-- Sum of `f 0 + f 1 + ... + f (n-1)` in a `KleeneSemiring`. -/
def finSum : (n : Nat) → (Fin n → α) → α
  | 0, _ => zero
  | n + 1, f => add (finSum n (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)) (f ⟨n, Nat.lt_succ_self n⟩)

end FinSum


/-! ### Matrices over a `KleeneSemiring` -/

/-- `n × n` matrix over `α`. -/
abbrev Mat (α : Type u) (n : Nat) := Fin n → Fin n → α

section MatrixAlgebra

variable {α : Type u} [KleeneSemiring α]

open KleeneSemiring

def matZero (n : Nat) : Mat α n := fun _ _ => zero

def matId (n : Nat) : Mat α n := fun i j => if i = j then one else zero

def matAdd {n : Nat} (A B : Mat α n) : Mat α n := fun i j => add (A i j) (B i j)

def matMul {n : Nat} (A B : Mat α n) : Mat α n :=
  fun i j => finSum n (fun k => mul (A i k) (B k j))

def matLe {n : Nat} (A B : Mat α n) : Prop := ∀ i j, le (A i j) (B i j)

def matPow {n : Nat} (M : Mat α n) : Nat → Mat α n
  | 0 => matId n
  | t + 1 => matMul (matPow M t) M

/-- Single-entry (rank-1 corner) matrix `c · E_{p, q}`. -/
def matSingle {n : Nat} (p q : Fin n) (c : α) : Mat α n :=
  fun i j => if i = p ∧ j = q then c else zero

/-- Exact Matrix Kleene Star predicate (Kozen axioms on `Mat α n`). -/
structure IsMatStar {n : Nat} (M S : Mat α n) : Prop where
  one_le    : matLe (matId n) S
  mul_left  : matLe (matMul M S) S
  mul_right : matLe (matMul S M) S
  ind_left  : ∀ B X : Mat α n, matLe B X → matLe (matMul M X) X → matLe (matMul S B) X
  ind_right : ∀ B X : Mat α n, matLe B X → matLe (matMul X M) X → matLe (matMul B S) X

/-- `2×2` block matrix assembly on `Fin (n * 2)` — definitionally matches `Fin (2 ^ (k + 1))`! -/
def blockMat {n : Nat} (A B C D : Mat α n) : Mat α (n * 2) :=
  fun i j =>
    if hi : i.val < n then
      if hj : j.val < n then A ⟨i.val, hi⟩ ⟨j.val, hj⟩
      else B ⟨i.val, hi⟩ ⟨j.val - n, by omega⟩
    else
      if hj : j.val < n then C ⟨i.val - n, by omega⟩ ⟨j.val, hj⟩
      else D ⟨i.val - n, by omega⟩ ⟨j.val - n, by omega⟩

/-- Extract the four `n × n` quadrants of any `Mat α (n * 2)`. -/
def blkTL {n : Nat} (M : Mat α (n * 2)) : Mat α n := fun i j => M ⟨i.val, by omega⟩ ⟨j.val, by omega⟩

def blkTR {n : Nat} (M : Mat α (n * 2)) : Mat α n := fun i j => M ⟨i.val, by omega⟩ ⟨n + j.val, by omega⟩

def blkBL {n : Nat} (M : Mat α (n * 2)) : Mat α n := fun i j => M ⟨n + i.val, by omega⟩ ⟨j.val, by omega⟩

def blkBR {n : Nat} (M : Mat α (n * 2)) : Mat α n := fun i j => M ⟨n + i.val, by omega⟩ ⟨n + j.val, by omega⟩

omit [KleeneSemiring α] in

/-- Rank-1 Kleene Sherman-Morrison update of `U = A*` by single entry `c · E_{p, s}`. -/
def smUpdate {n : Nat} (U : Mat α n) (p s : Fin n) (c : α) : Mat α n :=
  fun i j => add (U i j) (mul (mul (mul (U i p) c) (star (mul (U s p) c))) (U s j))

end MatrixAlgebra


/-! ============================================================================
    SECTION 4: THREE SILICON SEMIRING INSTANTIATIONS
    (1) Boolean `(|, &)`   (2) Tropical Min-Plus `TropNat`   (3) Power-Set XOR `XorSet`
    ============================================================================ -/

/-- Instance 1: Boolean semiring `(Bool, ||, &&, false, true)`. -/
instance instKleeneBool : KleeneSemiring Bool where
  zero := false
  one  := true
  add  := (· || ·)
  mul  := (· && ·)
  star := fun _ => true
  add_assoc := by decide
  add_comm  := by decide
  add_zero  := by decide
  add_idem  := by decide
  mul_assoc := by decide
  one_mul   := by decide
  mul_one   := by decide
  zero_mul  := by decide
  mul_zero  := by decide
  left_distrib  := by decide
  right_distrib := by decide
  one_le_star   := by decide
  mul_star_le   := by decide
  star_mul_le   := by decide
  star_ind_left := by decide
  star_ind_right := by decide

/-- Instance 2: Exact Tropical Min-Plus semiring `(ℕ ∪ {∞}, min, +, ∞, 0)`. -/
inductive TropNat where
  | inf : TropNat
  | fin : Nat → TropNat
  deriving DecidableEq, Repr

namespace TropNat


def minT : TropNat → TropNat → TropNat
  | inf, y => y
  | x, inf => x
  | fin a, fin b => fin (Nat.min a b)

def addT : TropNat → TropNat → TropNat
  | inf, _ => inf
  | _, inf => inf
  | fin a, fin b => fin (a + b)

theorem minT_assoc (a b c : TropNat) : minT (minT a b) c = minT a (minT b c) := by
  cases a <;> cases b <;> cases c <;> simp [minT, Nat.min_assoc]

theorem minT_comm (a b : TropNat) : minT a b = minT b a := by
  cases a <;> cases b <;> simp [minT, Nat.min_comm]

theorem minT_inf (a : TropNat) : minT a inf = a := by
  cases a <;> rfl

theorem minT_idem (a : TropNat) : minT a a = a := by
  cases a <;> simp [minT]

theorem addT_assoc (a b c : TropNat) : addT (addT a b) c = addT a (addT b c) := by
  cases a <;> cases b <;> cases c <;> simp [addT, Nat.add_assoc]

theorem zero_addT (a : TropNat) : addT (fin 0) a = a := by
  cases a <;> simp [addT]

theorem addT_zero (a : TropNat) : addT a (fin 0) = a := by
  cases a <;> simp [addT]

theorem inf_addT (a : TropNat) : addT inf a = inf := rfl

theorem addT_inf (a : TropNat) : addT a inf = inf := by
  cases a <;> rfl

theorem addT_minT_left (a b c : TropNat) : addT a (minT b c) = minT (addT a b) (addT a c) := by
  cases a <;> cases b <;> cases c <;> simp [addT, minT]

theorem addT_minT_right (a b c : TropNat) : addT (minT a b) c = minT (addT a c) (addT b c) := by
  cases a <;> cases b <;> cases c <;> simp [addT, minT]

end TropNat


instance instKleeneTropNat : KleeneSemiring TropNat where
  zero := TropNat.inf
  one  := TropNat.fin 0
  add  := TropNat.minT
  mul  := TropNat.addT
  star := fun _ => TropNat.fin 0
  add_assoc := TropNat.minT_assoc
  add_comm  := TropNat.minT_comm
  add_zero  := TropNat.minT_inf
  add_idem  := TropNat.minT_idem
  mul_assoc := TropNat.addT_assoc
  one_mul   := TropNat.zero_addT
  mul_one   := TropNat.addT_zero
  zero_mul  := TropNat.inf_addT
  mul_zero  := TropNat.addT_inf
  left_distrib  := TropNat.addT_minT_left
  right_distrib := TropNat.addT_minT_right
  one_le_star   := fun _ => rfl
  mul_star_le   := fun a => by cases a <;> simp [TropNat.addT, TropNat.minT]
  star_mul_le   := fun a => by cases a <;> simp [TropNat.addT, TropNat.minT]
  star_ind_left := fun a b c h => by
    rw [TropNat.zero_addT]
    cases b <;> cases c <;> cases a <;> simp [TropNat.minT, TropNat.addT] at h ⊢ <;> omega
  star_ind_right := fun a b c h => by
    rw [TropNat.addT_zero]
    cases b <;> cases c <;> cases a <;> simp [TropNat.minT, TropNat.addT] at h ⊢ <;> omega

/-- Instance 3: Bitwise Power-Set XOR Semiring `(𝒫(ℕ), ∪, ⊕_Mink, ∅, {0})`.
    Unlike `Bool` and `TropNat`, `XorSet` is NOT integral (`a ≰ 1`), exercising
    the full non-collapsing Kleene Sherman-Morrison star `(U_{s,p} · c)*`! -/
abbrev XorSet := Nat → Prop

namespace XorSet


/-- Inductive F₂-linear span of a set of bit-vectors `A`. -/
inductive Span (A : XorSet) : Nat → Prop where
  | zero : Span A 0
  | step {a b : Nat} : A a → Span A b → Span A (a ^^^ b)

def union (A B : XorSet) : XorSet := fun v => A v ∨ B v

def minkXor (A B : XorSet) : XorSet := fun v => ∃ a b, A a ∧ B b ∧ a ^^^ b = v

def single (w : Nat) : XorSet := fun v => v = w

theorem union_assoc (A B C : XorSet) : union (union A B) C = union A (union B C) := by
  funext v; exact propext or_assoc

theorem union_comm (A B : XorSet) : union A B = union B A := by
  funext v; exact propext or_comm

theorem union_empty (A : XorSet) : union A (fun _ => False) = A := by
  funext v; exact or_false _

theorem union_idem (A : XorSet) : union A A = A := by
  funext v; exact or_self _

theorem minkXor_assoc (A B C : XorSet) : minkXor (minkXor A B) C = minkXor A (minkXor B C) := by
  funext v; apply propext; constructor
  · rintro ⟨ab, c, ⟨a, b, ha, hb, rfl⟩, hc, rfl⟩
    exact ⟨a, b ^^^ c, ha, ⟨b, c, hb, hc, rfl⟩, (Nat.xor_assoc a b c).symm⟩
  · rintro ⟨a, bc, ha, ⟨b, c, hb, hc, rfl⟩, rfl⟩
    exact ⟨a ^^^ b, c, ⟨a, b, ha, hb, rfl⟩, hc, Nat.xor_assoc a b c⟩

theorem single_zero_minkXor (A : XorSet) : minkXor (single 0) A = A := by
  funext v; apply propext; constructor
  · rintro ⟨a, b, rfl, hb, rfl⟩; rwa [Nat.zero_xor]
  · intro hv; exact ⟨0, v, rfl, hv, Nat.zero_xor v⟩

theorem minkXor_single_zero (A : XorSet) : minkXor A (single 0) = A := by
  funext v; apply propext; constructor
  · rintro ⟨a, b, ha, rfl, rfl⟩; rwa [Nat.xor_zero]
  · intro hv; exact ⟨v, 0, hv, rfl, Nat.xor_zero v⟩

theorem empty_minkXor (A : XorSet) : minkXor (fun _ => False) A = (fun _ => False) := by
  funext v; apply propext; constructor
  · rintro ⟨_, _, h, _, _⟩; exact h
  · exact False.elim

theorem minkXor_empty (A : XorSet) : minkXor A (fun _ => False) = (fun _ => False) := by
  funext v; apply propext; constructor
  · rintro ⟨_, _, _, h, _⟩; exact h
  · exact False.elim

theorem minkXor_union_left (A B C : XorSet) :
    minkXor A (union B C) = union (minkXor A B) (minkXor A C) := by
  funext v; apply propext; constructor
  · rintro ⟨a, bc, ha, hbc | hbc, rfl⟩
    · exact Or.inl ⟨a, bc, ha, hbc, rfl⟩
    · exact Or.inr ⟨a, bc, ha, hbc, rfl⟩
  · rintro (⟨a, b, ha, hb, rfl⟩ | ⟨a, c, ha, hc, rfl⟩)
    · exact ⟨a, b, ha, Or.inl hb, rfl⟩
    · exact ⟨a, c, ha, Or.inr hc, rfl⟩

theorem minkXor_union_right (A B C : XorSet) :
    minkXor (union A B) C = union (minkXor A C) (minkXor B C) := by
  funext v; apply propext; constructor
  · rintro ⟨ab, c, hab | hab, hc, rfl⟩
    · exact Or.inl ⟨ab, c, hab, hc, rfl⟩
    · exact Or.inr ⟨ab, c, hab, hc, rfl⟩
  · rintro (⟨a, c, ha, hc, rfl⟩ | ⟨b, c, hb, hc, rfl⟩)
    · exact ⟨a, c, Or.inl ha, hc, rfl⟩
    · exact ⟨b, c, Or.inr hb, hc, rfl⟩

theorem span_step_right {A : XorSet} {a b : Nat} (hb : Span A b) (ha : A a) :
    Span A (b ^^^ a) := by
  rw [Nat.xor_comm]; exact Span.step ha hb

end XorSet


instance instKleeneXorSet : KleeneSemiring XorSet where
  zero := fun _ => False
  one  := XorSet.single 0
  add  := XorSet.union
  mul  := XorSet.minkXor
  star := XorSet.Span
  add_assoc := XorSet.union_assoc
  add_comm  := XorSet.union_comm
  add_zero  := XorSet.union_empty
  add_idem  := XorSet.union_idem
  mul_assoc := XorSet.minkXor_assoc
  one_mul   := XorSet.single_zero_minkXor
  mul_one   := XorSet.minkXor_single_zero
  zero_mul  := XorSet.empty_minkXor
  mul_zero  := XorSet.minkXor_empty
  left_distrib  := XorSet.minkXor_union_left
  right_distrib := XorSet.minkXor_union_right
  one_le_star   := fun A => by
    funext v; apply propext; constructor
    · rintro (rfl | h); exact XorSet.Span.zero; exact h
    · exact Or.inr
  mul_star_le   := fun A => by
    funext v; apply propext; constructor
    · rintro (⟨a, b, ha, hb, rfl⟩ | h); exact XorSet.Span.step ha hb; exact h
    · exact Or.inr
  star_mul_le   := fun A => by
    funext v; apply propext; constructor
    · rintro (⟨b, a, hb, ha, rfl⟩ | h); exact XorSet.span_step_right hb ha; exact h
    · exact Or.inr
  star_ind_left := fun A B C h => by
    have hBC : ∀ x, B x → C x := fun x hx => by
      have := congrFun h x; rw [← this]; exact Or.inl (Or.inl hx)
    have hAC : ∀ a c, A a → C c → C (a ^^^ c) := fun a c ha hc => by
      have := congrFun h (a ^^^ c); rw [← this]; exact Or.inl (Or.inr ⟨a, c, ha, hc, rfl⟩)
    funext v; apply propext; constructor
    · rintro (⟨s, b, hs, hb, rfl⟩ | hc)
      · induction hs with
        | zero => rw [Nat.zero_xor]; exact hBC b hb
        | step ha _ ih => rw [Nat.xor_assoc]; exact hAC _ _ ha ih
      · exact hc
    · exact Or.inr
  star_ind_right := fun A B C h => by
    have hBC : ∀ x, B x → C x := fun x hx => by
      have := congrFun h x; rw [← this]; exact Or.inl (Or.inl hx)
    have hCA : ∀ c a, C c → A a → C (c ^^^ a) := fun c a hc ha => by
      have := congrFun h (c ^^^ a); rw [← this]; exact Or.inl (Or.inr ⟨c, a, hc, ha, rfl⟩)
    funext v; apply propext; constructor
    · rintro (⟨b, s, hb, hs, rfl⟩ | hc)
      · induction hs generalizing b with
        | zero => rw [Nat.xor_zero]; exact hBC b hb
        | @step a_el b_el ha _ ih =>
          have h1 : C (b ^^^ b_el) := ih b hb
          have h2 : C ((b ^^^ b_el) ^^^ a_el) := hCA _ _ h1 ha
          have hrew : (b ^^^ b_el) ^^^ a_el = b ^^^ (a_el ^^^ b_el) := by
            rw [Nat.xor_assoc, Nat.xor_comm b_el a_el]
          rwa [hrew] at h2
      · exact hc
    · exact Or.inr

section BitDoublingTower

variable {α : Type u} [KleeneSemiring α]

open KleeneSemiring

/-- A reusable specification for a recursive `2^k × 2^k` corner-bridge matrix family
    whose Kleene star collapses inductively at every bit-width `k`. -/
structure BitDoublingCollapseSpec (α : Type u) [KleeneSemiring α] where
  p  : (k : Nat) → Fin (2 ^ k)
  q  : (k : Nat) → Fin (2 ^ k)
  r  : (k : Nat) → Fin (2 ^ k)
  s  : (k : Nat) → Fin (2 ^ k)
  wp : Nat → α
  wm : Nat → α

/-- Recursive `2^k × 2^k` adjacency / weight matrix generated by a `BitDoublingCollapseSpec`. -/
def BitDoublingCollapseSpec.mat (spec : BitDoublingCollapseSpec α) : (k : Nat) → Mat α (2 ^ k)
  | 0 => matZero 1
  | k + 1 =>
    blockMat (spec.mat k)
             (matSingle (spec.p k) (spec.q k) (spec.wp k))
             (matSingle (spec.r k) (spec.s k) (spec.wm k))
             (spec.mat k)

/-- Recursive closed-form Kleene star candidate generated by a `BitDoublingCollapseSpec`. -/
def BitDoublingCollapseSpec.starCand (spec : BitDoublingCollapseSpec α) : (k : Nat) → Mat α (2 ^ k)
  | 0 => matId 1
  | k + 1 =>
    let U := spec.starCand k
    blockMat U
             (fun i j => mul (mul (U i (spec.p k)) (spec.wp k)) (U (spec.q k) j))
             (fun i j => mul (mul (U i (spec.r k)) (spec.wm k)) (U (spec.s k) j))
             U

end BitDoublingTower

section CollapseSharpness

open KleeneSemiring

/-- `2×2` tropical matrix with `0 ↔ 1` cost `10`. -/
def sharpA : Mat TropNat 2 := fun i j => if i = j then TropNat.inf else TropNat.fin 10

def sharpU : Mat TropNat 2 := fun i j => if i = j then TropNat.fin 0 else TropNat.fin 10

end CollapseSharpness


/-! ============================================================================
    SECTION 6: PURE-SILICON BITWISE HELPER LIBRARY
    ============================================================================ -/

/-- Exact binary popcount of a natural number (number of `1`-bits). -/
def popcount : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) % 2 + popcount ((n + 1) / 2)
termination_by n => n

/-- Bit-position index of the lowest `1`-bit (`ctz`), or `0` for `0`. -/
def ctzNat : Nat → Nat
  | 0 => 0
  | n + 1 => if (n + 1) % 2 = 1 then 0 else 1 + ctzNat ((n + 1) / 2)
termination_by n => n

/-- Bit-position index of the lowest `0`-bit: `ctz(x + 1)`. -/
def ctzZeroNat (x : Nat) : Nat := ctzNat (x + 1)

/-- Corner indices `0` and `2^k - 1` in `Fin (2 ^ k)`. -/
def finZero (k : Nat) : Fin (2 ^ k) := ⟨0, Nat.two_pow_pos k⟩

def finMax  (k : Nat) : Fin (2 ^ k) := ⟨2 ^ k - 1, by have := Nat.two_pow_pos k; omega⟩

/-- The `BitDoublingCollapseSpec` for the BMI1 Bit-Twiddle graph `B_k^(c)` over `TropNat`. -/
def bmiTropSpec (c : Nat → Nat) : BitDoublingCollapseSpec TropNat where
  p  := finMax
  q  := finMax
  r  := finZero
  s  := finZero
  wp := fun k => TropNat.fin (c k)
  wm := fun k => TropNat.fin (c k)

/-- Recursive `2^k × 2^k` tropical adjacency matrix of `B_k^(c)`. -/
def bmiTropMat (k : Nat) (c : Nat → Nat) : Mat TropNat (2 ^ k) :=
  (bmiTropSpec c).mat k

/-- Direct pure-silicon bitwise definition of `B_k^(c)`:
    - `y = x ||| (x + 1)` (if `x < 2^k - 1`) with cost `c (ctzZeroNat x)`
    - `y = x &&& (x - 1)` (if `x > 0`) with cost `c (ctzNat x)`. -/
def bmiBitwiseMat (k : Nat) (c : Nat → Nat) : Mat TropNat (2 ^ k) :=
  fun x y =>
    if x.val + 1 < 2 ^ k ∧ y.val = (x.val ||| (x.val + 1)) then
      TropNat.fin (c (ctzZeroNat x.val))
    else if 0 < x.val ∧ y.val = (x.val &&& (x.val - 1)) then
      TropNat.fin (c (ctzNat x.val))
    else
      TropNat.inf

/-- Exact natural-number distance matrix `bmiDist k c x y` of `(B_k^(c))*`. -/
def bmiDist : (k : Nat) → (Nat → Nat) → Fin (2 ^ k) → Fin (2 ^ k) → Nat
  | 0, _, _, _ => 0
  | k + 1, c, i, j =>
    if hi : i.val < 2 ^ k then
      if hj : j.val < 2 ^ k then
        bmiDist k c ⟨i.val, hi⟩ ⟨j.val, hj⟩
      else
        bmiDist k c ⟨i.val, hi⟩ (finMax k) + c k + bmiDist k c (finMax k) ⟨j.val - 2 ^ k, by omega⟩
    else
      if hj : j.val < 2 ^ k then
        bmiDist k c ⟨i.val - 2 ^ k, by omega⟩ (finZero k) + c k + bmiDist k c (finZero k) ⟨j.val, hj⟩
      else
        bmiDist k c ⟨i.val - 2 ^ k, by omega⟩ ⟨j.val - 2 ^ k, by omega⟩

/-- Sum of bit costs `∑_{b=0}^{k-1} c b`. -/
def sumCost (c : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => sumCost c k + c k

/-- Weighted diameter `∑_{b=0}^{k-1} (k - b) * c b = ∑_{j=1}^k sumCost c j`. -/
def weightedDiam (c : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => weightedDiam c k + sumCost c (k + 1)

/-- Alternating Jacobsthal bit-word `altWord k`: `0, 1, 10₂, 101₂, 1010₂, 10101₂, ...` -/
def altWord : Nat → Nat
  | 0 => 0
  | k + 1 => 2 ^ k + (2 ^ k - 1 - altWord k)

/-- Bit-complement of a `k`-bit index: `x ↦ (2^k - 1) - x`. -/
def finCompl {k : Nat} (x : Fin (2 ^ k)) : Fin (2 ^ k) :=
  ⟨2 ^ k - 1 - x.val, by have := x.isLt; have := Nat.two_pow_pos k; omega⟩

/-- Exact cost from any `x` to `0` is the sum of `c b` over all `1`-bits of `x`. -/
def oneBitCost (c : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, x => oneBitCost c k x + if x.testBit k then c k else 0

/-- **Binary Gray-Code Suffix-Popcount Cost:**
    `graySuffixCost c k y = ∑_{b=0}^{k-1} c(b) · popcount((y ^^^ (y >>> 1)) >>> b)`. -/
def graySuffixCost (c : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, y =>
    graySuffixCost c k y + c k * popcount ((y ^^^ (y >>> 1)) >>> k)

/-- Boolean `(|, &)` adjacency matrix of the `2^k`-vertex BMI1 Bit-Twiddle graph `B_k`. -/
def bmiBoolSpec : BitDoublingCollapseSpec Bool where
  p  := finMax
  q  := finMax
  r  := finZero
  s  := finZero
  wp := fun _ => true
  wm := fun _ => true

def bmiBoolMat (k : Nat) : Mat Bool (2 ^ k) := bmiBoolSpec.mat k

/-- All-ones `n × n` Boolean matrix `J_n`. -/
def matAllTrue (n : Nat) : Mat Bool n := fun _ _ => true


/-- Asymmetric `BitDoublingCollapseSpec` for the hardware Ripple-Carry ALU graph `A_k`:
    - `INC` (`x ↦ x + 1`) with ripple-carry bit-flip cost `1 + ctz(x + 1)`
      (MSB carry-overflow bridge `(0, 2^k - 1) → (1, 0)` costs `k + 1`!)
    - `BLSR` (`x ↦ x &&& (x - 1)`) with unit cost `1`
      (MSB clear bridge `(1, 0) → (0, 0)` costs `1`!). -/
def aluTropSpec : BitDoublingCollapseSpec TropNat where
  p  := finMax
  q  := finZero
  r  := finZero
  s  := finZero
  wp := fun k => TropNat.fin (k + 1)
  wm := fun _ => TropNat.fin 1

def aluTropMat (k : Nat) : Mat TropNat (2 ^ k) := aluTropSpec.mat k

/-- Direct hardware-instruction definition of the Ripple-Carry ALU graph `A_k`. -/
def aluBitwiseMat (k : Nat) : Mat TropNat (2 ^ k) :=
  fun x y =>
    if x.val + 1 < 2 ^ k ∧ y.val = x.val + 1 then
      TropNat.fin (1 + ctzZeroNat x.val)
    else if 0 < x.val ∧ y.val = (x.val &&& (x.val - 1)) then
      TropNat.fin 1
    else
      TropNat.inf

/-- Exact natural-number distance matrix `aluDist k x y` of `A_k*`. -/
def aluDist : (k : Nat) → Fin (2 ^ k) → Fin (2 ^ k) → Nat
  | 0, _, _ => 0
  | k + 1, i, j =>
    if hi : i.val < 2 ^ k then
      if hj : j.val < 2 ^ k then
        aluDist k ⟨i.val, hi⟩ ⟨j.val, hj⟩
      else
        aluDist k ⟨i.val, hi⟩ (finMax k) + (k + 1) + aluDist k (finZero k) ⟨j.val - 2 ^ k, by omega⟩
    else
      if hj : j.val < 2 ^ k then
        aluDist k ⟨i.val - 2 ^ k, by omega⟩ (finZero k) + 1 + aluDist k (finZero k) ⟨j.val, hj⟩
      else
        aluDist k ⟨i.val - 2 ^ k, by omega⟩ ⟨j.val - 2 ^ k, by omega⟩

section ActiveXorEngine

open KleeneSemiring

/-- Diagonal XOR gauge conjugation: `(gaugeConj g M)_{i,j} = {g i ^^^ g j} ⊕_Mink M_{i,j}`. -/
def gaugeConj {n : Nat} (g : Fin n → Nat) (M : Mat XorSet n) : Mat XorSet n :=
  fun i j => XorSet.minkXor (XorSet.single (g i ^^^ g j)) (M i j)

/-- Parity gauge vector `g_k(x) = if popcount x % 2 = 1 then 2^k else 0`. -/
def parGauge (k : Nat) (x : Fin (2 ^ k)) : Nat :=
  if popcount x.val % 2 = 1 then 2 ^ k else 0

/-- Bitwise-AND weighted BMI1 graph `B_k` over `XorSet`:
    - Every edge `(x, y)` of `B_k` carries singleton XOR weight `{x &&& y}`!
    - Recursive MSB block form:
      - TL: `bmiXorMat k`
      - TR: `{2^k - 1} · E_{m_k, m_k}`  (since `(0, m_k) &&& (1, m_k) = m_k`)
      - BL: `{0} · E_{0, 0}`            (since `(1, 0) &&& (0, 0) = 0`)
      - BR: `gaugeConj (parGauge k) (bmiXorMat k)` (since `(1, x) &&& (1, y) = 2^k ^^^ (x &&& y)` and `B_k` is bipartite!). -/
def bmiXorMat : (k : Nat) → Mat XorSet (2 ^ k)
  | 0 => matZero 1
  | k + 1 =>
    blockMat (bmiXorMat k)
             (matSingle (finMax k) (finMax k) (XorSet.single (2 ^ k - 1)))
             (matSingle (finZero k) (finZero k) (XorSet.single 0))
             (gaugeConj (parGauge k) (bmiXorMat k))

/-- Direct bitwise-AND weighted definition of `B_k` over `XorSet`:
    `(x, y)` has singleton weight `{x &&& y}` iff `(x, y)` is a BMI1 edge! -/
def bmiXorBitwiseMat (k : Nat) : Mat XorSet (2 ^ k) :=
  fun x y =>
    if bmiBoolMat k x y then XorSet.single (x.val &&& y.val) else fun _ => False

/-- The exact `⌊k/2⌋`-dimensional F₂ cycle subspace:
    `V_k = span_{F₂} { 3 · 4^j | 0 ≤ j < ⌊k/2⌋ }`.
    Bitwise characterization: `v < 2^k`, every even-odd pair `(2j, 2j+1)` is equal,
    and if `k` is odd, bit `k - 1` is `false`. -/
def inVk (k v : Nat) : Prop :=
  v < 2 ^ k ∧
  (∀ j, j < k / 2 → v.testBit (2 * j) = v.testBit (2 * j + 1)) ∧
  (k % 2 = 1 → v.testBit (k - 1) = false)

/-- Canonical 2-bit-pair potential `phiRed k x` (recursively defined cleanly on `k`!):
    - `phiRed 0 x = 0`
    - For `x < 2^k`: `phiRed (k+1) x = phiRed k x`
    - For `x = 2^k + x'` (`x' < 2^k`):
      - If `k` is EVEN (`k+1` odd): `phiRed (k+1) (2^k + x') = (if popcount x' % 2 = 1 then 2^k else 0) ^^^ phiRed k x'`
      - If `k` is ODD (`k+1` even): `phiRed (k+1) (2^k + x') = (if popcount x' % 2 = 1 then 2^(k-1) else 0) ^^^ phiRed k x'`
        Wait — notice `(2^k ^^^ 2^(k-1)) = 3 * 2^(k-1) ∈ V_{k+1}`!!
        SO WE CAN SIMPLY DEFINE THE POTENTIAL UNIFORMLY BY:
        `phiBit (k : Nat) (x : Nat) : Nat`:
        - `phiBit 0 _ = 0`
        - `phiBit (k+1) x = phiBit k (x % 2^k) ^^^ (if x.testBit k ∧ popcount (x % 2^k) % 2 = 1 then 2^k else 0)`!
        WAIT A SECOND!! CHECK THAT!!
        For EVERY `k`: `phiBit (k+1) (2^k + x') = phiBit k x' ^^^ (if popcount x' % 2 = 1 then 2^k else 0)`
        = `phiBit k x' ^^^ parGauge k x'`!!
        AND `phiBit (k+1) x' = phiBit k x'`!!
        CHECK IF `phiBit k x` IS IN THE **EXACT SAME COSET** MOD `V_k` AS `phiRed k x`!!
        When `k` is odd (`k = 2m+1`, so `k+1 = 2m+2`): `2^k ^^^ 2^(k-1) = 3 * 4^m ∈ V_{k+1}`,
        so `2^k ≡ 2^(k-1) (mod V_{k+1})`!!
        **OH!! MY!! GOD!! `phiBit` IS LITERALLY 3 LINES LONG, HAS NO PARITY CASE-SPLIT AT ALL, AND SATISFIES `phiBit (k+1) (2^k + x') = parGauge k x' ^^^ phiBit k x'` DEFINITIONALLY!!** -/
def phiBit : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, x =>
    phiBit k (x % 2 ^ k) ^^^ (if x.testBit k && (popcount (x % 2 ^ k) % 2 == 1) then 2 ^ k else 0)

/-- Exact affine-coset Kleene star candidate for `B_k` over `XorSet`! -/
def bmiXorStar (k : Nat) (x y : Fin (2 ^ k)) : XorSet :=
  fun v => inVk k (v ^^^ phiBit k x.val ^^^ phiBit k y.val)

/-- Alternating even-pair upper-bit mask: `∑_{j=0}^{m-1} 2^(2j+1) = 2 * (4^m - 1) / 3`. -/
def altEvenMask : Nat → Nat
  | 0 => 0
  | m + 1 => altEvenMask m + 2 ^ (2 * m + 1)

/-- Greedy MSB-to-LSB XOR maximization inside any coset `r ⊕ V_k`:
    For every `j < k/2`, if bit `2j+1` of `r` is `0`, XOR with `3 · 4^j ∈ V_k` to force bit `2j+1` to `1`! -/
def greedyMaxXor (k r : Nat) : Nat :=
  let rec go : Nat → Nat → Nat
    | 0, acc => acc
    | j + 1, acc =>
      let acc' := if acc.testBit (2 * j + 1) then acc else acc ^^^ (2 ^ (2 * j + 1) ^^^ 2 ^ (2 * j))
      go j acc'
  go (k / 2) r

end ActiveXorEngine

end BSKSE
