/-
  Exact Dyadic-Rational (Z[1/2]) Infinite Positive-Definite Form Engine
  Worker: adic-10 (Thread 4: 2-Adic, Nimber, Carry-Arithmetic & Number-Theoretic Infinite Mechanisms)
  Standalone Lean 4.34.1 — zero Mathlib, zero Float, zero sorry, zero custom axioms.
-/

namespace DyadicPDEngine

/-! ## Section 1: Exact Pure-Silicon Dyadic Rationals Z[1/2] -/

structure Dyadic where
  mant : Int
  shift : Nat
  deriving Repr

namespace Dyadic

def pow2Int (n : Nat) : Int := (2 : Int) ^ n

theorem pow2Int_zero : pow2Int 0 = 1 := rfl

theorem pow2Int_succ (n : Nat) : pow2Int (n + 1) = pow2Int n * 2 :=
  Int.pow_succ 2 n

theorem pow2Int_pos (n : Nat) : 0 < pow2Int n := by
  induction n with
  | zero => decide
  | succ k ih =>
    rw [pow2Int_succ]
    omega

theorem pow2Int_ne_zero (n : Nat) : pow2Int n ≠ 0 := by
  have h := pow2Int_pos n
  omega

theorem pow2Int_add (a b : Nat) : pow2Int (a + b) = pow2Int a * pow2Int b :=
  Int.pow_add 2 a b

def eqv (a b : Dyadic) : Prop :=
  a.mant * pow2Int b.shift = b.mant * pow2Int a.shift

instance (a b : Dyadic) : Decidable (eqv a b) :=
  inferInstanceAs (Decidable (a.mant * pow2Int b.shift = b.mant * pow2Int a.shift))

theorem eqv_refl (a : Dyadic) : eqv a a := rfl

theorem eqv_symm {a b : Dyadic} (h : eqv a b) : eqv b a := h.symm

theorem eqv_trans {a b c : Dyadic} (hab : eqv a b) (hbc : eqv b c) : eqv a c := by
  unfold eqv at *
  have hpb : pow2Int b.shift ≠ 0 := pow2Int_ne_zero b.shift
  have h1 : a.mant * pow2Int c.shift * pow2Int b.shift =
            c.mant * pow2Int a.shift * pow2Int b.shift := by
    calc a.mant * pow2Int c.shift * pow2Int b.shift
        = (a.mant * pow2Int b.shift) * pow2Int c.shift := by
            rw [Int.mul_assoc, Int.mul_comm (pow2Int c.shift), ← Int.mul_assoc]
      _ = (b.mant * pow2Int a.shift) * pow2Int c.shift := by rw [hab]
      _ = (b.mant * pow2Int c.shift) * pow2Int a.shift := by
            rw [Int.mul_assoc, Int.mul_comm (pow2Int a.shift), ← Int.mul_assoc]
      _ = (c.mant * pow2Int b.shift) * pow2Int a.shift := by rw [hbc]
      _ = c.mant * pow2Int a.shift * pow2Int b.shift := by
            rw [Int.mul_assoc, Int.mul_comm (pow2Int b.shift), ← Int.mul_assoc]
  exact Int.eq_of_mul_eq_mul_right hpb h1

instance instSetoid : Setoid Dyadic where
  r := eqv
  iseqv := ⟨eqv_refl, eqv_symm, eqv_trans⟩

def add (a b : Dyadic) : Dyadic :=
  if a.shift ≤ b.shift then
    ⟨a.mant * pow2Int (b.shift - a.shift) + b.mant, b.shift⟩
  else
    ⟨a.mant + b.mant * pow2Int (a.shift - b.shift), a.shift⟩

def neg (a : Dyadic) : Dyadic := ⟨-a.mant, a.shift⟩

def mul (a b : Dyadic) : Dyadic := ⟨a.mant * b.mant, a.shift + b.shift⟩

def le (a b : Dyadic) : Prop :=
  a.mant * pow2Int b.shift ≤ b.mant * pow2Int a.shift

def lt (a b : Dyadic) : Prop :=
  a.mant * pow2Int b.shift < b.mant * pow2Int a.shift

instance (a b : Dyadic) : Decidable (le a b) :=
  inferInstanceAs (Decidable (a.mant * pow2Int b.shift ≤ b.mant * pow2Int a.shift))

instance (a b : Dyadic) : Decidable (lt a b) :=
  inferInstanceAs (Decidable (a.mant * pow2Int b.shift < b.mant * pow2Int a.shift))

theorem add_scale (a b : Dyadic) :
    (add a b).mant * pow2Int (a.shift + b.shift) =
    (a.mant * pow2Int b.shift + b.mant * pow2Int a.shift) * pow2Int (add a b).shift := by
  unfold add
  split
  case isTrue h =>
    have hsub : b.shift - a.shift + a.shift = b.shift := Nat.sub_add_cancel h
    simp only
    calc (a.mant * pow2Int (b.shift - a.shift) + b.mant) * pow2Int (a.shift + b.shift)
        = (a.mant * pow2Int (b.shift - a.shift) + b.mant) * (pow2Int a.shift * pow2Int b.shift) := by
            rw [pow2Int_add]
      _ = ((a.mant * pow2Int (b.shift - a.shift) + b.mant) * pow2Int a.shift) * pow2Int b.shift := by
            rw [Int.mul_assoc]
      _ = (a.mant * (pow2Int (b.shift - a.shift) * pow2Int a.shift) + b.mant * pow2Int a.shift) * pow2Int b.shift := by
            rw [Int.add_mul, Int.mul_assoc]
      _ = (a.mant * pow2Int b.shift + b.mant * pow2Int a.shift) * pow2Int b.shift := by
            rw [← pow2Int_add, hsub]
  case isFalse h =>
    have hlt : b.shift ≤ a.shift := Nat.le_of_not_le h
    have hsub : a.shift - b.shift + b.shift = a.shift := Nat.sub_add_cancel hlt
    simp only
    calc (a.mant + b.mant * pow2Int (a.shift - b.shift)) * pow2Int (a.shift + b.shift)
        = (a.mant + b.mant * pow2Int (a.shift - b.shift)) * (pow2Int b.shift * pow2Int a.shift) := by
            rw [pow2Int_add, Int.mul_comm (pow2Int a.shift)]
      _ = ((a.mant + b.mant * pow2Int (a.shift - b.shift)) * pow2Int b.shift) * pow2Int a.shift := by
            rw [Int.mul_assoc]
      _ = (a.mant * pow2Int b.shift + b.mant * (pow2Int (a.shift - b.shift) * pow2Int b.shift)) * pow2Int a.shift := by
            rw [Int.add_mul, Int.mul_assoc]
      _ = (a.mant * pow2Int b.shift + b.mant * pow2Int a.shift) * pow2Int a.shift := by
            rw [← pow2Int_add, hsub]

theorem add_eqv_raw (a b : Dyadic) :
    eqv (add a b) ⟨a.mant * pow2Int b.shift + b.mant * pow2Int a.shift, a.shift + b.shift⟩ :=
  add_scale a b

theorem add_respects {a1 a2 b1 b2 : Dyadic} (ha : eqv a1 a2) (hb : eqv b1 b2) :
    eqv (add a1 b1) (add a2 b2) := by
  apply eqv_trans (add_eqv_raw a1 b1)
  apply eqv_symm
  apply eqv_trans (add_eqv_raw a2 b2)
  apply eqv_symm
  unfold eqv at *
  simp only [pow2Int_add]
  have hL : (a1.mant * pow2Int b1.shift + b1.mant * pow2Int a1.shift) *
            (pow2Int a2.shift * pow2Int b2.shift) =
            (a1.mant * pow2Int a2.shift) * (pow2Int b1.shift * pow2Int b2.shift) +
            (b1.mant * pow2Int b2.shift) * (pow2Int a1.shift * pow2Int a2.shift) := by
    rw [Int.add_mul]
    congr 1
    · rw [Int.mul_assoc, Int.mul_assoc, Int.mul_left_comm (pow2Int b1.shift)]
    · rw [Int.mul_assoc, Int.mul_comm (pow2Int a2.shift) (pow2Int b2.shift),
          Int.mul_left_comm (pow2Int a1.shift), ← Int.mul_assoc]
  have hR : (a2.mant * pow2Int b2.shift + b2.mant * pow2Int a2.shift) *
            (pow2Int a1.shift * pow2Int b1.shift) =
            (a2.mant * pow2Int a1.shift) * (pow2Int b1.shift * pow2Int b2.shift) +
            (b2.mant * pow2Int b1.shift) * (pow2Int a1.shift * pow2Int a2.shift) := by
    rw [Int.add_mul]
    congr 1
    · rw [Int.mul_assoc, Int.mul_assoc, Int.mul_left_comm (pow2Int b2.shift),
          Int.mul_comm (pow2Int b2.shift) (pow2Int b1.shift)]
    · rw [Int.mul_assoc, Int.mul_comm (pow2Int a1.shift) (pow2Int b1.shift),
          Int.mul_left_comm (pow2Int a2.shift), ← Int.mul_assoc,
          Int.mul_comm (pow2Int a2.shift) (pow2Int a1.shift)]
  rw [hL, hR, ha, hb]

theorem neg_respects {a1 a2 : Dyadic} (ha : eqv a1 a2) : eqv (neg a1) (neg a2) := by
  unfold eqv neg at *
  simp only [Int.neg_mul]
  rw [ha]

theorem mul_respects {a1 a2 b1 b2 : Dyadic} (ha : eqv a1 a2) (hb : eqv b1 b2) :
    eqv (mul a1 b1) (mul a2 b2) := by
  unfold eqv mul at *
  simp only [pow2Int_add]
  calc (a1.mant * b1.mant) * (pow2Int a2.shift * pow2Int b2.shift)
      = (a1.mant * pow2Int a2.shift) * (b1.mant * pow2Int b2.shift) := by
          rw [Int.mul_assoc, Int.mul_left_comm b1.mant, ← Int.mul_assoc]
    _ = (a2.mant * pow2Int a1.shift) * (b2.mant * pow2Int b1.shift) := by
          rw [ha, hb]
    _ = (a2.mant * b2.mant) * (pow2Int a1.shift * pow2Int b1.shift) := by
          rw [Int.mul_assoc, Int.mul_left_comm (pow2Int a1.shift), ← Int.mul_assoc]

theorem le_respects_imp {a1 a2 b1 b2 : Dyadic} (ha : eqv a1 a2) (hb : eqv b1 b2)
    (h : le a1 b1) : le a2 b2 := by
  unfold eqv le at *
  have hp : 0 < pow2Int a1.shift * pow2Int b1.shift :=
    Int.mul_pos (pow2Int_pos a1.shift) (pow2Int_pos b1.shift)
  have h1 : (a2.mant * pow2Int b2.shift) * (pow2Int a1.shift * pow2Int b1.shift) ≤
            (b2.mant * pow2Int a2.shift) * (pow2Int a1.shift * pow2Int b1.shift) := by
    have lhs : (a2.mant * pow2Int b2.shift) * (pow2Int a1.shift * pow2Int b1.shift) =
               (a1.mant * pow2Int b1.shift) * (pow2Int a2.shift * pow2Int b2.shift) := by
      calc (a2.mant * pow2Int b2.shift) * (pow2Int a1.shift * pow2Int b1.shift)
          = (a2.mant * pow2Int a1.shift) * (pow2Int b2.shift * pow2Int b1.shift) := by
              rw [Int.mul_assoc, Int.mul_left_comm (pow2Int b2.shift), ← Int.mul_assoc]
        _ = (a1.mant * pow2Int a2.shift) * (pow2Int b2.shift * pow2Int b1.shift) := by rw [← ha]
        _ = (a1.mant * pow2Int b1.shift) * (pow2Int a2.shift * pow2Int b2.shift) := by
              rw [Int.mul_comm (pow2Int b2.shift) (pow2Int b1.shift),
                  Int.mul_assoc, Int.mul_left_comm (pow2Int a2.shift), ← Int.mul_assoc]
    have rhs : (b2.mant * pow2Int a2.shift) * (pow2Int a1.shift * pow2Int b1.shift) =
               (b1.mant * pow2Int a1.shift) * (pow2Int a2.shift * pow2Int b2.shift) := by
      calc (b2.mant * pow2Int a2.shift) * (pow2Int a1.shift * pow2Int b1.shift)
          = (b2.mant * pow2Int b1.shift) * (pow2Int a2.shift * pow2Int a1.shift) := by
              rw [Int.mul_comm (pow2Int a1.shift) (pow2Int b1.shift),
                  Int.mul_assoc, Int.mul_left_comm (pow2Int a2.shift), ← Int.mul_assoc]
        _ = (b1.mant * pow2Int b2.shift) * (pow2Int a2.shift * pow2Int a1.shift) := by rw [← hb]
        _ = (b1.mant * pow2Int a1.shift) * (pow2Int a2.shift * pow2Int b2.shift) := by
              rw [Int.mul_comm (pow2Int a2.shift) (pow2Int a1.shift),
                  Int.mul_assoc, Int.mul_left_comm (pow2Int b2.shift), ← Int.mul_assoc,
                  Int.mul_comm (pow2Int b2.shift) (pow2Int a2.shift)]
    rw [lhs, rhs]
    have hp2 : 0 ≤ pow2Int a2.shift * pow2Int b2.shift :=
      Int.le_of_lt (Int.mul_pos (pow2Int_pos a2.shift) (pow2Int_pos b2.shift))
    exact Int.mul_le_mul_of_nonneg_right h hp2
  exact Int.le_of_mul_le_mul_right h1 hp

theorem le_respects {a1 a2 b1 b2 : Dyadic} (ha : eqv a1 a2) (hb : eqv b1 b2) :
    le a1 b1 = le a2 b2 :=
  propext ⟨le_respects_imp ha hb, le_respects_imp (eqv_symm ha) (eqv_symm hb)⟩

theorem lt_respects_imp {a1 a2 b1 b2 : Dyadic} (ha : eqv a1 a2) (hb : eqv b1 b2)
    (h : lt a1 b1) : lt a2 b2 := by
  unfold eqv lt at *
  have hp : 0 < pow2Int a1.shift * pow2Int b1.shift :=
    Int.mul_pos (pow2Int_pos a1.shift) (pow2Int_pos b1.shift)
  have h1 : (a2.mant * pow2Int b2.shift) * (pow2Int a1.shift * pow2Int b1.shift) <
            (b2.mant * pow2Int a2.shift) * (pow2Int a1.shift * pow2Int b1.shift) := by
    have lhs : (a2.mant * pow2Int b2.shift) * (pow2Int a1.shift * pow2Int b1.shift) =
               (a1.mant * pow2Int b1.shift) * (pow2Int a2.shift * pow2Int b2.shift) := by
      calc (a2.mant * pow2Int b2.shift) * (pow2Int a1.shift * pow2Int b1.shift)
          = (a2.mant * pow2Int a1.shift) * (pow2Int b2.shift * pow2Int b1.shift) := by
              rw [Int.mul_assoc, Int.mul_left_comm (pow2Int b2.shift), ← Int.mul_assoc]
        _ = (a1.mant * pow2Int a2.shift) * (pow2Int b2.shift * pow2Int b1.shift) := by rw [← ha]
        _ = (a1.mant * pow2Int b1.shift) * (pow2Int a2.shift * pow2Int b2.shift) := by
              rw [Int.mul_comm (pow2Int b2.shift) (pow2Int b1.shift),
                  Int.mul_assoc, Int.mul_left_comm (pow2Int a2.shift), ← Int.mul_assoc]
    have rhs : (b2.mant * pow2Int a2.shift) * (pow2Int a1.shift * pow2Int b1.shift) =
               (b1.mant * pow2Int a1.shift) * (pow2Int a2.shift * pow2Int b2.shift) := by
      calc (b2.mant * pow2Int a2.shift) * (pow2Int a1.shift * pow2Int b1.shift)
          = (b2.mant * pow2Int b1.shift) * (pow2Int a2.shift * pow2Int a1.shift) := by
              rw [Int.mul_comm (pow2Int a1.shift) (pow2Int b1.shift),
                  Int.mul_assoc, Int.mul_left_comm (pow2Int a2.shift), ← Int.mul_assoc]
        _ = (b1.mant * pow2Int b2.shift) * (pow2Int a2.shift * pow2Int a1.shift) := by rw [← hb]
        _ = (b1.mant * pow2Int a1.shift) * (pow2Int a2.shift * pow2Int b2.shift) := by
              rw [Int.mul_comm (pow2Int a2.shift) (pow2Int a1.shift),
                  Int.mul_assoc, Int.mul_left_comm (pow2Int b2.shift), ← Int.mul_assoc,
                  Int.mul_comm (pow2Int b2.shift) (pow2Int a2.shift)]
    rw [lhs, rhs]
    have hp2 : 0 < pow2Int a2.shift * pow2Int b2.shift :=
      Int.mul_pos (pow2Int_pos a2.shift) (pow2Int_pos b2.shift)
    exact Int.mul_lt_mul_of_pos_right h hp2
  exact Int.lt_of_mul_lt_mul_right h1 (Int.le_of_lt hp)

theorem lt_respects {a1 a2 b1 b2 : Dyadic} (ha : eqv a1 a2) (hb : eqv b1 b2) :
    lt a1 b1 = lt a2 b2 :=
  propext ⟨lt_respects_imp ha hb, lt_respects_imp (eqv_symm ha) (eqv_symm hb)⟩

end Dyadic

abbrev ZHalf := Quotient Dyadic.instSetoid

namespace ZHalf

def dyad (m : Int) (e : Nat) : ZHalf := Quotient.mk Dyadic.instSetoid ⟨m, e⟩
def ofInt (m : Int) : ZHalf := dyad m 0
def ofNat (n : Nat) : ZHalf := dyad (Int.ofNat n) 0
def pow2Neg (e : Nat) : ZHalf := dyad 1 e
def pow2Nat (e : Nat) : ZHalf := dyad (Dyadic.pow2Int e) 0

instance : Zero ZHalf := ⟨ofInt 0⟩
instance : One ZHalf := ⟨ofInt 1⟩
instance (n : Nat) : OfNat ZHalf n := ⟨ofNat n⟩

def add : ZHalf → ZHalf → ZHalf :=
  Quotient.lift₂ (fun a b => Quotient.mk Dyadic.instSetoid (Dyadic.add a b))
    (fun _ _ _ _ ha hb => Quotient.sound (Dyadic.add_respects ha hb))

def neg : ZHalf → ZHalf :=
  Quotient.lift (fun a => Quotient.mk Dyadic.instSetoid (Dyadic.neg a))
    (fun _ _ ha => Quotient.sound (Dyadic.neg_respects ha))

def sub (a b : ZHalf) : ZHalf := add a (neg b)

def mul : ZHalf → ZHalf → ZHalf :=
  Quotient.lift₂ (fun a b => Quotient.mk Dyadic.instSetoid (Dyadic.mul a b))
    (fun _ _ _ _ ha hb => Quotient.sound (Dyadic.mul_respects ha hb))

def le : ZHalf → ZHalf → Prop :=
  Quotient.lift₂ Dyadic.le (fun _ _ _ _ ha hb => Dyadic.le_respects ha hb)

def lt : ZHalf → ZHalf → Prop :=
  Quotient.lift₂ Dyadic.lt (fun _ _ _ _ ha hb => Dyadic.lt_respects ha hb)

instance : Add ZHalf := ⟨add⟩
instance : Neg ZHalf := ⟨neg⟩
instance : Sub ZHalf := ⟨sub⟩
instance : Mul ZHalf := ⟨mul⟩
instance : LE ZHalf := ⟨le⟩
instance : LT ZHalf := ⟨lt⟩

def beqAux (a b : Dyadic) : Bool := decide (Dyadic.eqv a b)
def bleAux (a b : Dyadic) : Bool := decide (Dyadic.le a b)
def bltAux (a b : Dyadic) : Bool := decide (Dyadic.lt a b)

theorem decide_eq_of_iff {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    decide p = decide q := by
  by_cases hp : p
  · simp [hp, h.mp hp]
  · simp [hp, mt h.mpr hp]

def beq : ZHalf → ZHalf → Bool :=
  Quotient.lift₂ beqAux (fun _ _ _ _ ha hb => decide_eq_of_iff
    ⟨fun h => Dyadic.eqv_trans (Dyadic.eqv_symm ha) (Dyadic.eqv_trans h hb),
     fun h => Dyadic.eqv_trans ha (Dyadic.eqv_trans h (Dyadic.eqv_symm hb))⟩)

def ble : ZHalf → ZHalf → Bool :=
  Quotient.lift₂ bleAux (fun _ _ _ _ ha hb => decide_eq_of_iff
    ⟨Dyadic.le_respects_imp ha hb, Dyadic.le_respects_imp (Dyadic.eqv_symm ha) (Dyadic.eqv_symm hb)⟩)

def blt : ZHalf → ZHalf → Bool :=
  Quotient.lift₂ bltAux (fun _ _ _ _ ha hb => decide_eq_of_iff
    ⟨Dyadic.lt_respects_imp ha hb, Dyadic.lt_respects_imp (Dyadic.eqv_symm ha) (Dyadic.eqv_symm hb)⟩)

theorem beq_iff (x y : ZHalf) : beq x y = true ↔ x = y := by
  refine Quotient.inductionOn₂ x y ?_
  intro a b
  change (decide (Dyadic.eqv a b) = true) ↔ (Quotient.mk Dyadic.instSetoid a = Quotient.mk Dyadic.instSetoid b)
  rw [decide_eq_true_iff]
  exact ⟨fun h => Quotient.sound h, fun h => Quotient.exact h⟩

theorem ble_iff (x y : ZHalf) : ble x y = true ↔ x ≤ y := by
  refine Quotient.inductionOn₂ x y ?_
  intro a b
  change (decide (Dyadic.le a b) = true) ↔ Dyadic.le a b
  exact decide_eq_true_iff

theorem blt_iff (x y : ZHalf) : blt x y = true ↔ x < y := by
  refine Quotient.inductionOn₂ x y ?_
  intro a b
  change (decide (Dyadic.lt a b) = true) ↔ Dyadic.lt a b
  exact decide_eq_true_iff

instance : DecidableEq ZHalf := fun x y =>
  if h : beq x y = true then isTrue ((beq_iff x y).mp h)
  else isFalse (fun heq => h ((beq_iff x y).mpr heq))

instance (x y : ZHalf) : Decidable (x ≤ y) :=
  if h : ble x y = true then isTrue ((ble_iff x y).mp h)
  else isFalse (fun hle => h ((ble_iff x y).mpr hle))

instance (x y : ZHalf) : Decidable (x < y) :=
  if h : blt x y = true then isTrue ((blt_iff x y).mp h)
  else isFalse (fun hlt => h ((blt_iff x y).mpr hlt))

-- Helper: raw addition equality in ZHalf
theorem mk_add_eq (a b : Dyadic) :
    Quotient.mk Dyadic.instSetoid a + Quotient.mk Dyadic.instSetoid b =
    Quotient.mk Dyadic.instSetoid ⟨a.mant * Dyadic.pow2Int b.shift + b.mant * Dyadic.pow2Int a.shift, a.shift + b.shift⟩ :=
  Quotient.sound (Dyadic.add_eqv_raw a b)

theorem zero_eq_mk : (0 : ZHalf) = Quotient.mk Dyadic.instSetoid ⟨0, 0⟩ := rfl
theorem one_eq_mk : (1 : ZHalf) = Quotient.mk Dyadic.instSetoid ⟨1, 0⟩ := rfl

-- Commutative ring axioms for ZHalf
theorem add_comm (x y : ZHalf) : x + y = y + x := by
  refine Quotient.inductionOn₂ x y fun a b => ?_
  rw [mk_add_eq, mk_add_eq]
  apply Quotient.sound
  show (a.mant * Dyadic.pow2Int b.shift + b.mant * Dyadic.pow2Int a.shift) * Dyadic.pow2Int (b.shift + a.shift) =
       (b.mant * Dyadic.pow2Int a.shift + a.mant * Dyadic.pow2Int b.shift) * Dyadic.pow2Int (a.shift + b.shift)
  rw [Int.add_comm (a.mant * _), Nat.add_comm b.shift a.shift]

theorem add_assoc (x y z : ZHalf) : (x + y) + z = x + (y + z) := by
  refine Quotient.inductionOn₃ x y z fun a b c => ?_
  rw [mk_add_eq, mk_add_eq, mk_add_eq, mk_add_eq]
  apply Quotient.sound
  show ((a.mant * Dyadic.pow2Int b.shift + b.mant * Dyadic.pow2Int a.shift) * Dyadic.pow2Int c.shift +
        c.mant * Dyadic.pow2Int (a.shift + b.shift)) * Dyadic.pow2Int (a.shift + (b.shift + c.shift)) =
       (a.mant * Dyadic.pow2Int (b.shift + c.shift) +
        (b.mant * Dyadic.pow2Int c.shift + c.mant * Dyadic.pow2Int b.shift) * Dyadic.pow2Int a.shift) *
       Dyadic.pow2Int (a.shift + b.shift + c.shift)
  rw [Nat.add_assoc a.shift b.shift c.shift]
  congr 1
  simp only [Dyadic.pow2Int_add, Int.add_mul, Int.mul_assoc]
  rw [Int.add_assoc]
  congr 1
  congr 1
  · rw [Int.mul_comm (Dyadic.pow2Int a.shift) (Dyadic.pow2Int c.shift)]
  · rw [Int.mul_comm (Dyadic.pow2Int a.shift) (Dyadic.pow2Int b.shift)]

theorem zero_add (x : ZHalf) : 0 + x = x := by
  refine Quotient.inductionOn x fun a => ?_
  rw [zero_eq_mk, mk_add_eq]
  apply Quotient.sound
  show (0 * Dyadic.pow2Int a.shift + a.mant * Dyadic.pow2Int 0) * Dyadic.pow2Int a.shift =
       a.mant * Dyadic.pow2Int (0 + a.shift)
  simp [Dyadic.pow2Int_zero]

theorem add_zero (x : ZHalf) : x + 0 = x := by
  rw [add_comm, zero_add]

theorem add_neg_cancel (x : ZHalf) : x + (-x) = 0 := by
  refine Quotient.inductionOn x fun a => ?_
  change Quotient.mk Dyadic.instSetoid a + Quotient.mk Dyadic.instSetoid ⟨-a.mant, a.shift⟩ =
         Quotient.mk Dyadic.instSetoid ⟨0, 0⟩
  rw [mk_add_eq]
  apply Quotient.sound
  show (a.mant * Dyadic.pow2Int a.shift + -a.mant * Dyadic.pow2Int a.shift) * Dyadic.pow2Int 0 =
       0 * Dyadic.pow2Int (a.shift + a.shift)
  rw [Int.neg_mul, Int.add_right_neg, Int.zero_mul, Int.zero_mul]

theorem neg_add_cancel (x : ZHalf) : (-x) + x = 0 := by
  rw [add_comm, add_neg_cancel]

theorem sub_eq_add_neg (x y : ZHalf) : x - y = x + (-y) := rfl

theorem sub_self (x : ZHalf) : x - x = 0 := add_neg_cancel x

theorem mul_comm (x y : ZHalf) : x * y = y * x := by
  refine Quotient.inductionOn₂ x y fun a b => ?_
  apply Quotient.sound
  show (a.mant * b.mant) * Dyadic.pow2Int (b.shift + a.shift) =
       (b.mant * a.mant) * Dyadic.pow2Int (a.shift + b.shift)
  rw [Int.mul_comm a.mant b.mant, Nat.add_comm b.shift a.shift]

theorem mul_assoc (x y z : ZHalf) : (x * y) * z = x * (y * z) := by
  refine Quotient.inductionOn₃ x y z fun a b c => ?_
  apply Quotient.sound
  show (a.mant * b.mant * c.mant) * Dyadic.pow2Int (a.shift + (b.shift + c.shift)) =
       (a.mant * (b.mant * c.mant)) * Dyadic.pow2Int (a.shift + b.shift + c.shift)
  rw [Int.mul_assoc a.mant b.mant c.mant, Nat.add_assoc a.shift b.shift c.shift]

theorem one_mul (x : ZHalf) : 1 * x = x := by
  refine Quotient.inductionOn x fun a => ?_
  apply Quotient.sound
  show (1 * a.mant) * Dyadic.pow2Int a.shift = a.mant * Dyadic.pow2Int (0 + a.shift)
  simp

theorem mul_one (x : ZHalf) : x * 1 = x := by
  rw [mul_comm, one_mul]

theorem zero_mul (x : ZHalf) : 0 * x = 0 := by
  refine Quotient.inductionOn x fun a => ?_
  apply Quotient.sound
  show (0 * a.mant) * Dyadic.pow2Int 0 = 0 * Dyadic.pow2Int (0 + a.shift)
  simp

theorem mul_zero (x : ZHalf) : x * 0 = 0 := by
  rw [mul_comm, zero_mul]

theorem mul_add (x y z : ZHalf) : x * (y + z) = x * y + x * z := by
  refine Quotient.inductionOn₃ x y z fun a b c => ?_
  rw [mk_add_eq]
  change Quotient.mk Dyadic.instSetoid (Dyadic.mul a ⟨b.mant * Dyadic.pow2Int c.shift + c.mant * Dyadic.pow2Int b.shift, b.shift + c.shift⟩) =
         Quotient.mk Dyadic.instSetoid (Dyadic.mul a b) + Quotient.mk Dyadic.instSetoid (Dyadic.mul a c)
  rw [mk_add_eq]
  apply Quotient.sound
  show (a.mant * (b.mant * Dyadic.pow2Int c.shift + c.mant * Dyadic.pow2Int b.shift)) *
       Dyadic.pow2Int ((a.shift + b.shift) + (a.shift + c.shift)) =
       ((a.mant * b.mant) * Dyadic.pow2Int (a.shift + c.shift) +
        (a.mant * c.mant) * Dyadic.pow2Int (a.shift + b.shift)) *
       Dyadic.pow2Int (a.shift + (b.shift + c.shift))
  simp only [Dyadic.pow2Int_add, Int.mul_add, Int.add_mul, Int.mul_assoc]
  congr 1
  · congr 1; congr 1
    have h1 : Dyadic.pow2Int c.shift * (Dyadic.pow2Int a.shift * (Dyadic.pow2Int b.shift * (Dyadic.pow2Int a.shift * Dyadic.pow2Int c.shift))) =
              Dyadic.pow2Int a.shift * (Dyadic.pow2Int c.shift * (Dyadic.pow2Int a.shift * (Dyadic.pow2Int b.shift * Dyadic.pow2Int c.shift))) := by
      rw [Int.mul_left_comm (Dyadic.pow2Int c.shift) (Dyadic.pow2Int a.shift)]
      congr 1
      rw [Int.mul_left_comm (Dyadic.pow2Int b.shift) (Dyadic.pow2Int a.shift),
          Int.mul_left_comm (Dyadic.pow2Int c.shift) (Dyadic.pow2Int a.shift)]
    exact h1
  · congr 1; congr 1
    have h2 : Dyadic.pow2Int b.shift * (Dyadic.pow2Int a.shift * (Dyadic.pow2Int b.shift * (Dyadic.pow2Int a.shift * Dyadic.pow2Int c.shift))) =
              Dyadic.pow2Int a.shift * (Dyadic.pow2Int b.shift * (Dyadic.pow2Int a.shift * (Dyadic.pow2Int b.shift * Dyadic.pow2Int c.shift))) := by
      rw [Int.mul_left_comm (Dyadic.pow2Int b.shift) (Dyadic.pow2Int a.shift)]
      congr 1; congr 1
      rw [Int.mul_left_comm (Dyadic.pow2Int b.shift) (Dyadic.pow2Int a.shift)]
    exact h2

theorem add_mul (x y z : ZHalf) : (x + y) * z = x * z + y * z := by
  rw [mul_comm, mul_add, mul_comm z x, mul_comm z y]

theorem neg_mul (x y : ZHalf) : (-x) * y = -(x * y) := by
  refine Quotient.inductionOn₂ x y fun a b => ?_
  apply Quotient.sound
  show (-a.mant * b.mant) * Dyadic.pow2Int (a.shift + b.shift) =
       -(a.mant * b.mant) * Dyadic.pow2Int (a.shift + b.shift)
  rw [Int.neg_mul]

theorem mul_neg (x y : ZHalf) : x * (-y) = -(x * y) := by
  rw [mul_comm, neg_mul, mul_comm]

theorem neg_neg (x : ZHalf) : -(-x) = x := by
  refine Quotient.inductionOn x fun a => ?_
  apply Quotient.sound
  show (- -a.mant) * Dyadic.pow2Int a.shift = a.mant * Dyadic.pow2Int a.shift
  rw [Int.neg_neg]

theorem neg_add (x y : ZHalf) : -(x + y) = (-x) + (-y) := by
  have h : (x + y) + ((-x) + (-y)) = 0 := by
    calc (x + y) + ((-x) + (-y))
        = (x + (-x)) + (y + (-y)) := by
            rw [add_assoc, ← add_assoc y (-x) (-y), add_comm y (-x), add_assoc (-x) y (-y), ← add_assoc]
      _ = 0 + 0 := by rw [add_neg_cancel, add_neg_cancel]
      _ = 0 := add_zero 0
  calc -(x + y) = -(x + y) + 0 := (add_zero _).symm
    _ = -(x + y) + ((x + y) + ((-x) + (-y))) := by rw [h]
    _ = (-(x + y) + (x + y)) + ((-x) + (-y)) := (add_assoc _ _ _).symm
    _ = 0 + ((-x) + (-y)) := by rw [neg_add_cancel]
    _ = (-x) + (-y) := zero_add _

theorem mul_sub (x y z : ZHalf) : x * (y - z) = x * y - x * z := by
  rw [sub_eq_add_neg, mul_add, mul_neg, ← sub_eq_add_neg]

theorem sub_mul (x y z : ZHalf) : (x - y) * z = x * z - y * z := by
  rw [sub_eq_add_neg, add_mul, neg_mul, ← sub_eq_add_neg]

theorem neg_zero : -(0 : ZHalf) = 0 := by decide

theorem add_left_cancel {x y z : ZHalf} (h : x + y = x + z) : y = z := by
  calc y = 0 + y := (zero_add y).symm
    _ = ((-x) + x) + y := by rw [neg_add_cancel]
    _ = (-x) + (x + y) := add_assoc _ _ _
    _ = (-x) + (x + z) := by rw [h]
    _ = ((-x) + x) + z := (add_assoc _ _ _).symm
    _ = 0 + z := by rw [neg_add_cancel]
    _ = z := zero_add z

theorem sub_eq_zero_iff (x y : ZHalf) : x - y = 0 ↔ x = y := by
  constructor
  · intro h
    have h2 : (x - y) + y = 0 + y := by rw [h]
    rw [sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero, zero_add] at h2
    exact h2
  · intro h; rw [h, sub_self]

theorem mul_eq_zero {x y : ZHalf} (h : x * y = 0) : x = 0 ∨ y = 0 := by
  refine Quotient.inductionOn₂ x y (fun a b hab => ?_) h
  have h1 : (a.mant * b.mant) * Dyadic.pow2Int 0 = 0 * Dyadic.pow2Int (a.shift + b.shift) :=
    Quotient.exact hab
  simp only [Dyadic.pow2Int_zero, Int.mul_one, Int.zero_mul] at h1
  rcases Int.mul_eq_zero.mp h1 with ha | hb
  · left; apply Quotient.sound; show a.mant * 1 = 0 * _; simp [ha]
  · right; apply Quotient.sound; show b.mant * 1 = 0 * _; simp [hb]

-- Order axioms for ZHalf
theorem le_refl (x : ZHalf) : x ≤ x := by
  refine Quotient.inductionOn x fun a => Int.le_refl _

theorem le_trans {x y z : ZHalf} (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  refine Quotient.inductionOn₃ x y z (fun a b c h1 h2 => ?_) hxy hyz
  change a.mant * Dyadic.pow2Int c.shift ≤ c.mant * Dyadic.pow2Int a.shift
  have hpb : 0 < Dyadic.pow2Int b.shift := Dyadic.pow2Int_pos b.shift
  have hpc : 0 ≤ Dyadic.pow2Int c.shift := Int.le_of_lt (Dyadic.pow2Int_pos c.shift)
  have hpa : 0 ≤ Dyadic.pow2Int a.shift := Int.le_of_lt (Dyadic.pow2Int_pos a.shift)
  have s1 : (a.mant * Dyadic.pow2Int b.shift) * Dyadic.pow2Int c.shift ≤
            (b.mant * Dyadic.pow2Int a.shift) * Dyadic.pow2Int c.shift :=
    Int.mul_le_mul_of_nonneg_right h1 hpc
  have s2 : (b.mant * Dyadic.pow2Int c.shift) * Dyadic.pow2Int a.shift ≤
            (c.mant * Dyadic.pow2Int b.shift) * Dyadic.pow2Int a.shift :=
    Int.mul_le_mul_of_nonneg_right h2 hpa
  have e1 : (a.mant * Dyadic.pow2Int c.shift) * Dyadic.pow2Int b.shift =
            (a.mant * Dyadic.pow2Int b.shift) * Dyadic.pow2Int c.shift := by
    rw [Int.mul_assoc, Int.mul_comm (Dyadic.pow2Int c.shift), ← Int.mul_assoc]
  have e2 : (b.mant * Dyadic.pow2Int a.shift) * Dyadic.pow2Int c.shift =
            (b.mant * Dyadic.pow2Int c.shift) * Dyadic.pow2Int a.shift := by
    rw [Int.mul_assoc, Int.mul_comm (Dyadic.pow2Int a.shift), ← Int.mul_assoc]
  have e3 : (c.mant * Dyadic.pow2Int b.shift) * Dyadic.pow2Int a.shift =
            (c.mant * Dyadic.pow2Int a.shift) * Dyadic.pow2Int b.shift := by
    rw [Int.mul_assoc, Int.mul_comm (Dyadic.pow2Int b.shift), ← Int.mul_assoc]
  rw [← e1, e2] at s1
  rw [e3] at s2
  exact Int.le_of_mul_le_mul_right (Int.le_trans s1 s2) hpb

theorem le_antisymm {x y : ZHalf} (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  refine Quotient.inductionOn₂ x y (fun a b h1 h2 => ?_) hxy hyx
  apply Quotient.sound
  exact Int.le_antisymm h1 h2

theorem le_of_lt {x y : ZHalf} (h : x < y) : x ≤ y := by
  refine Quotient.inductionOn₂ x y (fun a b h1 => Int.le_of_lt h1) h

theorem lt_irrefl (x : ZHalf) : ¬ (x < x) := by
  refine Quotient.inductionOn x fun a => Int.lt_irrefl _

theorem lt_of_le_of_lt {x y z : ZHalf} (hxy : x ≤ y) (hyz : y < z) : x < z := by
  refine Quotient.inductionOn₃ x y z (fun a b c h1 h2 => ?_) hxy hyz
  change a.mant * Dyadic.pow2Int c.shift < c.mant * Dyadic.pow2Int a.shift
  have hpb : 0 < Dyadic.pow2Int b.shift := Dyadic.pow2Int_pos b.shift
  have hpc : 0 ≤ Dyadic.pow2Int c.shift := Int.le_of_lt (Dyadic.pow2Int_pos c.shift)
  have hpa : 0 < Dyadic.pow2Int a.shift := Dyadic.pow2Int_pos a.shift
  have s1 : (a.mant * Dyadic.pow2Int b.shift) * Dyadic.pow2Int c.shift ≤
            (b.mant * Dyadic.pow2Int a.shift) * Dyadic.pow2Int c.shift :=
    Int.mul_le_mul_of_nonneg_right h1 hpc
  have s2 : (b.mant * Dyadic.pow2Int c.shift) * Dyadic.pow2Int a.shift <
            (c.mant * Dyadic.pow2Int b.shift) * Dyadic.pow2Int a.shift :=
    Int.mul_lt_mul_of_pos_right h2 hpa
  have e1 : (a.mant * Dyadic.pow2Int c.shift) * Dyadic.pow2Int b.shift =
            (a.mant * Dyadic.pow2Int b.shift) * Dyadic.pow2Int c.shift := by
    rw [Int.mul_assoc, Int.mul_comm (Dyadic.pow2Int c.shift), ← Int.mul_assoc]
  have e2 : (b.mant * Dyadic.pow2Int a.shift) * Dyadic.pow2Int c.shift =
            (b.mant * Dyadic.pow2Int c.shift) * Dyadic.pow2Int a.shift := by
    rw [Int.mul_assoc, Int.mul_comm (Dyadic.pow2Int a.shift), ← Int.mul_assoc]
  have e3 : (c.mant * Dyadic.pow2Int b.shift) * Dyadic.pow2Int a.shift =
            (c.mant * Dyadic.pow2Int a.shift) * Dyadic.pow2Int b.shift := by
    rw [Int.mul_assoc, Int.mul_comm (Dyadic.pow2Int b.shift), ← Int.mul_assoc]
  rw [← e1, e2] at s1
  rw [e3] at s2
  exact Int.lt_of_mul_lt_mul_right (Int.lt_of_le_of_lt s1 s2) (Int.le_of_lt hpb)

theorem lt_of_lt_of_le {x y z : ZHalf} (hxy : x < y) (hyz : y ≤ z) : x < z := by
  refine Quotient.inductionOn₃ x y z (fun a b c h1 h2 => ?_) hxy hyz
  change a.mant * Dyadic.pow2Int c.shift < c.mant * Dyadic.pow2Int a.shift
  have hpb : 0 < Dyadic.pow2Int b.shift := Dyadic.pow2Int_pos b.shift
  have hpc : 0 < Dyadic.pow2Int c.shift := Dyadic.pow2Int_pos c.shift
  have hpa : 0 ≤ Dyadic.pow2Int a.shift := Int.le_of_lt (Dyadic.pow2Int_pos a.shift)
  have s1 : (a.mant * Dyadic.pow2Int b.shift) * Dyadic.pow2Int c.shift <
            (b.mant * Dyadic.pow2Int a.shift) * Dyadic.pow2Int c.shift :=
    Int.mul_lt_mul_of_pos_right h1 hpc
  have s2 : (b.mant * Dyadic.pow2Int c.shift) * Dyadic.pow2Int a.shift ≤
            (c.mant * Dyadic.pow2Int b.shift) * Dyadic.pow2Int a.shift :=
    Int.mul_le_mul_of_nonneg_right h2 hpa
  have e1 : (a.mant * Dyadic.pow2Int c.shift) * Dyadic.pow2Int b.shift =
            (a.mant * Dyadic.pow2Int b.shift) * Dyadic.pow2Int c.shift := by
    rw [Int.mul_assoc, Int.mul_comm (Dyadic.pow2Int c.shift), ← Int.mul_assoc]
  have e2 : (b.mant * Dyadic.pow2Int a.shift) * Dyadic.pow2Int c.shift =
            (b.mant * Dyadic.pow2Int c.shift) * Dyadic.pow2Int a.shift := by
    rw [Int.mul_assoc, Int.mul_comm (Dyadic.pow2Int a.shift), ← Int.mul_assoc]
  have e3 : (c.mant * Dyadic.pow2Int b.shift) * Dyadic.pow2Int a.shift =
            (c.mant * Dyadic.pow2Int a.shift) * Dyadic.pow2Int b.shift := by
    rw [Int.mul_assoc, Int.mul_comm (Dyadic.pow2Int b.shift), ← Int.mul_assoc]
  rw [← e1, e2] at s1
  rw [e3] at s2
  exact Int.lt_of_mul_lt_mul_right (Int.lt_of_lt_of_le s1 s2) (Int.le_of_lt hpb)

theorem lt_trans {x y z : ZHalf} (hxy : x < y) (hyz : y < z) : x < z :=
  lt_of_le_of_lt (le_of_lt hxy) hyz

theorem nonneg_mk_iff (a : Dyadic) : (0 : ZHalf) ≤ Quotient.mk Dyadic.instSetoid a ↔ 0 ≤ a.mant := by
  change (0 * Dyadic.pow2Int a.shift ≤ a.mant * Dyadic.pow2Int 0) ↔ 0 ≤ a.mant
  simp [Dyadic.pow2Int_zero]

theorem pos_mk_iff (a : Dyadic) : (0 : ZHalf) < Quotient.mk Dyadic.instSetoid a ↔ 0 < a.mant := by
  change (0 * Dyadic.pow2Int a.shift < a.mant * Dyadic.pow2Int 0) ↔ 0 < a.mant
  simp [Dyadic.pow2Int_zero]

theorem add_nonneg {x y : ZHalf} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x + y := by
  refine Quotient.inductionOn₂ x y (fun a b ha hb => ?_) hx hy
  rw [mk_add_eq, nonneg_mk_iff]
  rw [nonneg_mk_iff] at ha hb
  exact Int.add_nonneg
    (Int.mul_nonneg ha (Int.le_of_lt (Dyadic.pow2Int_pos b.shift)))
    (Int.mul_nonneg hb (Int.le_of_lt (Dyadic.pow2Int_pos a.shift)))

theorem add_pos_of_pos_of_nonneg {x y : ZHalf} (hx : 0 < x) (hy : 0 ≤ y) : 0 < x + y := by
  refine Quotient.inductionOn₂ x y (fun a b ha hb => ?_) hx hy
  rw [mk_add_eq, pos_mk_iff]
  rw [pos_mk_iff] at ha
  rw [nonneg_mk_iff] at hb
  have h1 : 0 < a.mant * Dyadic.pow2Int b.shift := Int.mul_pos ha (Dyadic.pow2Int_pos b.shift)
  have h2 : 0 ≤ b.mant * Dyadic.pow2Int a.shift := Int.mul_nonneg hb (Int.le_of_lt (Dyadic.pow2Int_pos a.shift))
  show 0 < a.mant * Dyadic.pow2Int b.shift + b.mant * Dyadic.pow2Int a.shift
  omega

theorem add_pos_of_nonneg_of_pos {x y : ZHalf} (hx : 0 ≤ x) (hy : 0 < y) : 0 < x + y := by
  rw [add_comm]
  exact add_pos_of_pos_of_nonneg hy hx

theorem add_pos {x y : ZHalf} (hx : 0 < x) (hy : 0 < y) : 0 < x + y :=
  add_pos_of_pos_of_nonneg hx (le_of_lt hy)

theorem mul_nonneg {x y : ZHalf} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y := by
  refine Quotient.inductionOn₂ x y (fun a b ha hb => ?_) hx hy
  change 0 * Dyadic.pow2Int (a.shift + b.shift) ≤ (a.mant * b.mant) * Dyadic.pow2Int 0
  rw [nonneg_mk_iff] at ha hb
  simp only [Dyadic.pow2Int_zero, Int.zero_mul, Int.mul_one]
  exact Int.mul_nonneg ha hb

theorem mul_pos {x y : ZHalf} (hx : 0 < x) (hy : 0 < y) : 0 < x * y := by
  refine Quotient.inductionOn₂ x y (fun a b ha hb => ?_) hx hy
  change 0 * Dyadic.pow2Int (a.shift + b.shift) < (a.mant * b.mant) * Dyadic.pow2Int 0
  rw [pos_mk_iff] at ha hb
  simp only [Dyadic.pow2Int_zero, Int.zero_mul, Int.mul_one]
  exact Int.mul_pos ha hb

theorem sq_nonneg (x : ZHalf) : 0 ≤ x * x := by
  refine Quotient.inductionOn x fun a => ?_
  change 0 * Dyadic.pow2Int (a.shift + a.shift) ≤ (a.mant * a.mant) * Dyadic.pow2Int 0
  simp only [Dyadic.pow2Int_zero, Int.zero_mul, Int.mul_one]
  by_cases h : 0 ≤ a.mant
  · exact Int.mul_nonneg h h
  · have hn : 0 ≤ -a.mant := by omega
    have heq : a.mant * a.mant = (-a.mant) * (-a.mant) := by rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    rw [heq]
    exact Int.mul_nonneg hn hn

theorem sq_pos_of_ne_zero {x : ZHalf} (hx : x ≠ 0) : 0 < x * x := by
  refine Quotient.inductionOn x (fun a ha => ?_) hx
  change 0 * Dyadic.pow2Int (a.shift + a.shift) < (a.mant * a.mant) * Dyadic.pow2Int 0
  simp only [Dyadic.pow2Int_zero, Int.zero_mul, Int.mul_one]
  have hne : a.mant ≠ 0 := by
    intro hm
    apply ha
    apply Quotient.sound
    show a.mant * 1 = 0 * _
    simp [hm]
  by_cases h : 0 < a.mant
  · exact Int.mul_pos h h
  · have hn : 0 < -a.mant := by omega
    have heq : a.mant * a.mant = (-a.mant) * (-a.mant) := by rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    rw [heq]
    exact Int.mul_pos hn hn

theorem eq_zero_of_add_eq_zero_left {x y : ZHalf} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x + y = 0) :
    x = 0 := by
  by_cases h0 : x = 0
  · exact h0
  · exfalso
    have hpos : 0 < x := by
      refine Quotient.inductionOn x (fun a ha hne => ?_) hx h0
      rw [nonneg_mk_iff] at ha
      rw [pos_mk_iff]
      have hm : a.mant ≠ 0 := by
        intro hm0; apply hne; apply Quotient.sound; show a.mant * 1 = 0 * _; simp [hm0]
      omega
    have hsum : 0 < x + y := add_pos_of_pos_of_nonneg hpos hy
    rw [h] at hsum
    exact lt_irrefl 0 hsum

theorem eq_zero_of_add_eq_zero_right {x y : ZHalf} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x + y = 0) :
    y = 0 := by
  rw [add_comm] at h
  exact eq_zero_of_add_eq_zero_left hy hx h

theorem sub_pos_iff {x y : ZHalf} : 0 < x - y ↔ y < x := by
  refine Quotient.inductionOn₂ x y fun a b => ?_
  change 0 < Quotient.mk Dyadic.instSetoid a + Quotient.mk Dyadic.instSetoid ⟨-b.mant, b.shift⟩ ↔
         Dyadic.lt b a
  rw [mk_add_eq, pos_mk_iff]
  unfold Dyadic.lt
  simp only [Int.neg_mul]
  omega

theorem sub_nonneg_iff {x y : ZHalf} : 0 ≤ x - y ↔ y ≤ x := by
  refine Quotient.inductionOn₂ x y fun a b => ?_
  change 0 ≤ Quotient.mk Dyadic.instSetoid a + Quotient.mk Dyadic.instSetoid ⟨-b.mant, b.shift⟩ ↔
         Dyadic.le b a
  rw [mk_add_eq, nonneg_mk_iff]
  unfold Dyadic.le
  simp only [Int.neg_mul]
  omega

theorem pow2Neg_add (a b : Nat) : pow2Neg (a + b) = pow2Neg a * pow2Neg b := by
  apply Quotient.sound
  show (1 : Int) * Dyadic.pow2Int (a + b) = (1 * 1) * Dyadic.pow2Int (a + b)
  simp

theorem pow2Neg_pos (e : Nat) : 0 < pow2Neg e := by
  rw [pow2Neg, dyad, pos_mk_iff]
  show (0 : Int) < 1
  omega

theorem pow2Nat_pos (e : Nat) : 0 < pow2Nat e := by
  rw [pow2Nat, dyad, pos_mk_iff]
  exact Dyadic.pow2Int_pos e

theorem pow2Nat_mul_pow2Neg (e : Nat) : pow2Nat e * pow2Neg e = 1 := by
  apply Quotient.sound
  show (Dyadic.pow2Int e * 1) * Dyadic.pow2Int 0 = 1 * Dyadic.pow2Int (0 + e)
  simp [Dyadic.pow2Int_zero]

-- Helper ring rearrangement lemmas
theorem add_four_swap (a b c d : ZHalf) : (a + b) + (c + d) = (a + c) + (b + d) := by
  calc (a + b) + (c + d) = a + (b + (c + d)) := add_assoc a b (c + d)
    _ = a + ((b + c) + d) := by rw [add_assoc b c d]
    _ = a + ((c + b) + d) := by rw [add_comm b c]
    _ = a + (c + (b + d)) := by rw [add_assoc c b d]
    _ = (a + c) + (b + d) := (add_assoc a c (b + d)).symm

theorem add_mid_group (a b c d : ZHalf) : (a + b) + (c + d) = (a + (b + c)) + d := by
  calc (a + b) + (c + d) = ((a + b) + c) + d := (add_assoc (a + b) c d).symm
    _ = (a + (b + c)) + d := by rw [add_assoc a b c]

/-! ### Finite Sums over `Fin n` in `ZHalf` -/

def sumFinAux : (n : Nat) → (Fin n → ZHalf) → ZHalf
  | 0, _ => 0
  | n + 1, f => sumFinAux n (fun i => f i.castSucc) + f ⟨n, Nat.lt_succ_self n⟩

def sumFin {n : Nat} (f : Fin n → ZHalf) : ZHalf := sumFinAux n f

theorem sumFin_zero {n : Nat} : sumFin (fun _ : Fin n => (0 : ZHalf)) = 0 := by
  unfold sumFin
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumFinAux]
    rw [ih, add_zero]

theorem sumFin_congr {n : Nat} {f g : Fin n → ZHalf} (h : ∀ i, f i = g i) :
    sumFin f = sumFin g := by
  unfold sumFin
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumFinAux]
    rw [ih (fun i => h i.castSucc), h ⟨k, Nat.lt_succ_self k⟩]

theorem sumFin_add {n : Nat} (f g : Fin n → ZHalf) :
    sumFin (fun i => f i + g i) = sumFin f + sumFin g := by
  unfold sumFin
  induction n with
  | zero => simp [sumFinAux, add_zero]
  | succ k ih =>
    simp only [sumFinAux]
    rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc)]
    exact add_four_swap _ _ _ _

theorem sumFin_neg {n : Nat} (f : Fin n → ZHalf) :
    sumFin (fun i => -f i) = -sumFin f := by
  unfold sumFin
  induction n with
  | zero => simp [sumFinAux, neg_zero]
  | succ k ih =>
    simp only [sumFinAux]
    rw [ih (fun i => f i.castSucc), neg_add]

theorem sumFin_sub {n : Nat} (f g : Fin n → ZHalf) :
    sumFin (fun i => f i - g i) = sumFin f - sumFin g := by
  simp only [sub_eq_add_neg]
  rw [sumFin_add, sumFin_neg]

theorem sumFin_mul_left {n : Nat} (c : ZHalf) (f : Fin n → ZHalf) :
    sumFin (fun i => c * f i) = c * sumFin f := by
  unfold sumFin
  induction n with
  | zero => simp [sumFinAux, mul_zero]
  | succ k ih =>
    simp only [sumFinAux]
    rw [ih (fun i => f i.castSucc), mul_add]

theorem sumFin_mul_right {n : Nat} (f : Fin n → ZHalf) (c : ZHalf) :
    sumFin (fun i => f i * c) = sumFin f * c := by
  rw [mul_comm, ← sumFin_mul_left]
  exact sumFin_congr fun i => mul_comm (f i) c

theorem sumFin_swap {m n : Nat} (f : Fin m → Fin n → ZHalf) :
    sumFin (fun i => sumFin (fun j => f i j)) = sumFin (fun j => sumFin (fun i => f i j)) := by
  induction m with
  | zero =>
    change (0 : ZHalf) = sumFin (fun _ : Fin n => (0 : ZHalf))
    exact sumFin_zero.symm
  | succ k ih =>
    unfold sumFin
    simp only [sumFinAux]
    have h1 : sumFinAux k (fun i => sumFinAux n (fun j => f i.castSucc j)) =
              sumFinAux n (fun j => sumFinAux k (fun i => f i.castSucc j)) := ih (fun i j => f i.castSucc j)
    rw [h1]
    exact (sumFin_add (fun j => sumFinAux k (fun i => f i.castSucc j))
                      (fun j => f ⟨k, Nat.lt_succ_self k⟩ j)).symm

theorem sumFin_nonneg {n : Nat} {f : Fin n → ZHalf} (h : ∀ i, 0 ≤ f i) : 0 ≤ sumFin f := by
  unfold sumFin
  induction n with
  | zero => exact le_refl 0
  | succ k ih =>
    simp only [sumFinAux]
    exact add_nonneg (ih (fun i => h i.castSucc)) (h ⟨k, Nat.lt_succ_self k⟩)

theorem sumFin_split_two {m : Nat} (f : Fin (2 * m) → ZHalf) :
    sumFin f =
      sumFin (fun i : Fin m => f ⟨i.val, by omega⟩) +
      sumFin (fun i : Fin m => f ⟨m + i.val, by omega⟩) := by
  have gen : ∀ r (hr : r ≤ m) (g : Fin (m + r) → ZHalf),
      sumFin g =
        sumFin (fun i : Fin m => g ⟨i.val, by omega⟩) +
        sumFin (fun i : Fin r => g ⟨m + i.val, by omega⟩) := by
    intro r
    induction r with
    | zero =>
      intro _ g
      simp only [sumFin, sumFinAux, add_zero]
      rfl
    | succ r ih =>
      intro hr g
      change sumFinAux (m + r) (fun j => g j.castSucc) + g ⟨m + r, by omega⟩ =
             sumFinAux m (fun i => g ⟨i.val, by omega⟩) +
             (sumFinAux r (fun i => g ⟨m + i.val, by omega⟩) + g ⟨m + r, by omega⟩)
      have hsub := ih (by omega) (fun j => g j.castSucc)
      change sumFinAux (m + r) (fun j => g j.castSucc) =
             sumFinAux m (fun i => g ⟨i.val, by omega⟩) +
             sumFinAux r (fun i => g ⟨m + i.val, by omega⟩) at hsub
      rw [hsub, add_assoc]
  have h2m : 2 * m = m + m := by omega
  have hg := gen m (Nat.le_refl m) (fun j => f ⟨j.val, by omega⟩)
  have hcast : sumFin f = sumFin (fun j : Fin (m + m) => f ⟨j.val, by omega⟩) := by
    have haux : ∀ (a b : Nat) (hab : a = b) (fa : Fin a → ZHalf) (fb : Fin b → ZHalf),
        (∀ i : Fin a, fa i = fb ⟨i.val, hab ▸ i.isLt⟩) → sumFin fa = sumFin fb := by
      intro a b hab; subst hab; intro fa fb h; exact sumFin_congr h
    exact haux (2 * m) (m + m) h2m f (fun j => f ⟨j.val, by omega⟩) (fun _ => rfl)
  rw [hcast, hg]

theorem sumFin_even_odd {n : Nat} (f : Fin (2 * n) → ZHalf) :
    sumFin f =
      sumFin (fun i : Fin n => f ⟨2 * i.val, by omega⟩) +
      sumFin (fun i : Fin n => f ⟨2 * i.val + 1, by omega⟩) := by
  induction n with
  | zero => simp [sumFin, sumFinAux, add_zero]
  | succ k ih =>
    have hcast : sumFin f =
        sumFin (fun j : Fin (2 * k) => f ⟨j.val, by omega⟩) +
        f ⟨2 * k, by omega⟩ + f ⟨2 * k + 1, by omega⟩ := by
      have haux : ∀ (a b : Nat) (hab : a = b + 2) (fa : Fin a → ZHalf),
          sumFin fa = sumFin (fun j : Fin b => fa ⟨j.val, by omega⟩) +
                      fa ⟨b, by omega⟩ + fa ⟨b + 1, by omega⟩ := by
        intro a b hab; subst hab; intro fa; rfl
      exact haux (2 * (k + 1)) (2 * k) (by omega) f
    rw [hcast, ih (fun j : Fin (2 * k) => f ⟨j.val, by omega⟩)]
    unfold sumFin
    simp only [sumFinAux]
    have heq1 : sumFinAux k (fun i => f ⟨2 * i.val, by omega⟩) =
                sumFinAux k (fun i => f ⟨2 * i.castSucc.val, by omega⟩) := rfl
    have heq2 : sumFinAux k (fun i => f ⟨2 * i.val + 1, by omega⟩) =
                sumFinAux k (fun i => f ⟨2 * i.castSucc.val + 1, by omega⟩) := rfl
    rw [heq1, heq2, add_assoc]
    exact add_four_swap _ _ _ _

theorem sumFin_pow2_succ {k : Nat} (f : Fin (2 ^ (k + 1)) → ZHalf) :
    sumFin f =
      sumFin (fun i : Fin (2 ^ k) => f ⟨2 * i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩) +
      sumFin (fun i : Fin (2 ^ k) => f ⟨2 * i.val + 1, by have := i.isLt; rw [Nat.pow_succ]; omega⟩) := by
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
  have haux : ∀ (a b : Nat) (hab : a = b) (fa : Fin a → ZHalf) (fb : Fin b → ZHalf),
      (∀ i : Fin a, fa i = fb ⟨i.val, hab ▸ i.isLt⟩) → sumFin fa = sumFin fb := by
    intro a b hab; subst hab; intro fa fb h; exact sumFin_congr h
  rw [haux (2 ^ (k + 1)) (2 * 2 ^ k) hpow f (fun j => f ⟨j.val, by omega⟩) (fun _ => rfl)]
  exact sumFin_even_odd (fun j : Fin (2 * 2 ^ k) => f ⟨j.val, by omega⟩)

theorem sumFin_fin1 (f : Fin 1 → ZHalf) : sumFin f = f ⟨0, by omega⟩ := by
  unfold sumFin
  simp [sumFinAux, zero_add]

theorem sumFin_single {n : Nat} (k : Fin n) (f : Fin n → ZHalf)
    (h0 : ∀ i : Fin n, i ≠ k → f i = 0) : sumFin f = f k := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ m ih =>
    unfold sumFin
    simp only [sumFinAux]
    by_cases hk : k.val = m
    · have hkeq : k = ⟨m, Nat.lt_succ_self m⟩ := Fin.ext hk
      rw [hkeq]
      have hzero : sumFinAux m (fun i => f i.castSucc) = 0 := by
        rw [show sumFinAux m (fun i => f i.castSucc) = sumFin (fun i : Fin m => f i.castSucc) from rfl]
        rw [sumFin_congr (fun i => h0 i.castSucc (by intro h; have hv := congrArg Fin.val h; simp [hkeq] at hv; omega))]
        exact sumFin_zero
      rw [hzero, zero_add]
    · have hklt : k.val < m := by omega
      have hlast : f ⟨m, Nat.lt_succ_self m⟩ = 0 :=
        h0 ⟨m, Nat.lt_succ_self m⟩ (by intro h; have hv := congrArg Fin.val h; exact hk hv.symm)
      rw [hlast, add_zero]
      exact ih ⟨k.val, hklt⟩ (fun i => f i.castSucc) (fun i hi =>
        h0 i.castSucc (fun h => hi (Fin.ext (congrArg (Fin.val : Fin (m + 1) → Nat) h))))

end ZHalf

/-! ## Section 2: Binary Vectors, Finite Matrices & Weighted-SOS Gram Engine over Z[1/2] -/

open ZHalf

def vecZero (n : Nat) : Fin n → ZHalf := fun _ => 0
def vecAdd {n : Nat} (x y : Fin n → ZHalf) : Fin n → ZHalf := fun i => x i + y i
def vecSmul {n : Nat} (c : ZHalf) (x : Fin n → ZHalf) : Fin n → ZHalf := fun i => c * x i
def dotFin {n : Nat} (x y : Fin n → ZHalf) : ZHalf := sumFin (fun i => x i * y i)

def quadBilin {n : Nat} (M : Fin n → Fin n → ZHalf) (x y : Fin n → ZHalf) : ZHalf :=
  sumFin (fun i => sumFin (fun j => M i j * x i * y j))

def quadForm {n : Nat} (M : Fin n → Fin n → ZHalf) (x : Fin n → ZHalf) : ZHalf :=
  quadBilin M x x

def isSymmMat {n : Nat} (M : Fin n → Fin n → ZHalf) : Bool :=
  (List.finRange n).all fun i => (List.finRange n).all fun j => decide (M i j = M j i)

theorem isSymmMat_sound {n : Nat} {M : Fin n → Fin n → ZHalf} (h : isSymmMat M = true) :
    ∀ i j, M i j = M j i := by
  intro i j
  unfold isSymmMat at h
  rw [List.all_eq_true] at h
  have hi := h i (List.mem_finRange i)
  rw [List.all_eq_true] at hi
  exact of_decide_eq_true (hi j (List.mem_finRange j))

theorem quadBilin_symm {n : Nat} {M : Fin n → Fin n → ZHalf} (hM : ∀ i j, M i j = M j i)
    (x y : Fin n → ZHalf) : quadBilin M x y = quadBilin M y x := by
  unfold quadBilin
  rw [sumFin_swap]
  apply sumFin_congr; intro j
  apply sumFin_congr; intro i
  rw [hM i j, mul_assoc, mul_comm (x i) (y j), ← mul_assoc]

theorem quadBilin_add_left {n : Nat} (M : Fin n → Fin n → ZHalf) (x y z : Fin n → ZHalf) :
    quadBilin M (vecAdd x y) z = quadBilin M x z + quadBilin M y z := by
  unfold quadBilin vecAdd
  rw [← sumFin_add]
  apply sumFin_congr; intro i
  rw [← sumFin_add]
  apply sumFin_congr; intro j
  rw [mul_add, add_mul]

theorem quadBilin_smul_left {n : Nat} (M : Fin n → Fin n → ZHalf) (c : ZHalf) (x y : Fin n → ZHalf) :
    quadBilin M (vecSmul c x) y = c * quadBilin M x y := by
  unfold quadBilin vecSmul
  rw [← sumFin_mul_left]
  apply sumFin_congr; intro i
  rw [← sumFin_mul_left]
  apply sumFin_congr; intro j
  calc M i j * (c * x i) * y j
      = (M i j * c * x i) * y j := by rw [← mul_assoc (M i j) c (x i)]
    _ = (c * M i j * x i) * y j := by rw [mul_comm (M i j) c]
    _ = c * (M i j * x i * y j) := by rw [mul_assoc c (M i j) (x i), mul_assoc c (M i j * x i) (y j)]

theorem quadBilin_smul_right {n : Nat} (M : Fin n → Fin n → ZHalf) (c : ZHalf) (x y : Fin n → ZHalf) :
    quadBilin M x (vecSmul c y) = c * quadBilin M x y := by
  unfold quadBilin vecSmul
  rw [← sumFin_mul_left]
  apply sumFin_congr; intro i
  rw [← sumFin_mul_left]
  apply sumFin_congr; intro j
  calc M i j * x i * (c * y j)
      = (M i j * x i * c) * y j := (mul_assoc (M i j * x i) c (y j)).symm
    _ = (c * (M i j * x i)) * y j := by rw [mul_comm (M i j * x i) c]
    _ = c * (M i j * x i * y j) := mul_assoc c (M i j * x i) (y j)

theorem quadBilin_mat_add {n : Nat} (M1 M2 : Fin n → Fin n → ZHalf) (x y : Fin n → ZHalf) :
    quadBilin (fun i j => M1 i j + M2 i j) x y = quadBilin M1 x y + quadBilin M2 x y := by
  unfold quadBilin
  rw [← sumFin_add]
  apply sumFin_congr; intro i
  rw [← sumFin_add]
  apply sumFin_congr; intro j
  rw [add_mul, add_mul]

theorem quadBilin_mat_sub {n : Nat} (M1 M2 : Fin n → Fin n → ZHalf) (x y : Fin n → ZHalf) :
    quadBilin (fun i j => M1 i j - M2 i j) x y = quadBilin M1 x y - quadBilin M2 x y := by
  unfold quadBilin
  rw [← sumFin_sub]
  apply sumFin_congr; intro i
  rw [← sumFin_sub]
  apply sumFin_congr; intro j
  rw [sub_mul, sub_mul]

-- LSB even/odd binary half split for Fin (2^(k+1)) -> ZHalf
def evenHalf {k : Nat} (x : Fin (2 ^ (k + 1)) → ZHalf) : Fin (2 ^ k) → ZHalf :=
  fun i => x ⟨2 * i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩

def oddHalf {k : Nat} (x : Fin (2 ^ (k + 1)) → ZHalf) : Fin (2 ^ k) → ZHalf :=
  fun i => x ⟨2 * i.val + 1, by have := i.isLt; rw [Nat.pow_succ]; omega⟩

theorem ne_zero_split {k : Nat} {x : Fin (2 ^ (k + 1)) → ZHalf} (hx : ∃ i, x i ≠ 0) :
    (∃ i, evenHalf x i ≠ 0) ∨ (∃ i, oddHalf x i ≠ 0) := by
  rcases hx with ⟨⟨v, hv⟩, hne⟩
  have hv2 : v < 2 * 2 ^ k := by rw [Nat.pow_succ] at hv; omega
  by_cases hp : v % 2 = 0
  · left
    refine ⟨⟨v / 2, by omega⟩, ?_⟩
    unfold evenHalf
    have heq : (⟨2 * (v / 2), by rw [Nat.pow_succ]; omega⟩ : Fin (2 ^ (k + 1))) = ⟨v, hv⟩ :=
      Fin.ext (show 2 * (v / 2) = v by omega)
    rw [heq]; exact hne
  · right
    refine ⟨⟨v / 2, by omega⟩, ?_⟩
    unfold oddHalf
    have heq : (⟨2 * (v / 2) + 1, by rw [Nat.pow_succ]; omega⟩ : Fin (2 ^ (k + 1))) = ⟨v, hv⟩ :=
      Fin.ext (show 2 * (v / 2) + 1 = v by omega)
    rw [heq]; exact hne

-- Weighted SOS matrix evaluator & soundness
def sosMatrix {d : Nat} (terms : List (ZHalf × (Fin d → ZHalf))) (i j : Fin d) : ZHalf :=
  terms.foldr (fun t acc => t.1 * t.2 i * t.2 j + acc) 0

def sosEval {d : Nat} (terms : List (ZHalf × (Fin d → ZHalf))) (v : Fin d → ZHalf) : ZHalf :=
  terms.foldr (fun t acc => t.1 * (dotFin t.2 v * dotFin t.2 v) + acc) 0

theorem quadForm_sosMatrix {d : Nat} (terms : List (ZHalf × (Fin d → ZHalf))) (v : Fin d → ZHalf) :
    quadForm (sosMatrix terms) v = sosEval terms v := by
  induction terms with
  | nil =>
    unfold quadForm quadBilin sosMatrix sosEval
    simp only [List.foldr]
    have h0 : ∀ i : Fin d, sumFin (fun j : Fin d => (0 : ZHalf) * v i * v j) = 0 := fun i => by
      rw [sumFin_congr (fun j => by rw [zero_mul, zero_mul])]
      exact sumFin_zero
    rw [sumFin_congr h0]
    exact sumFin_zero
  | cons t ts ih =>
    rcases t with ⟨w, u⟩
    change quadForm (fun i j => (w * u i * u j) + sosMatrix ts i j) v =
           w * (dotFin u v * dotFin u v) + sosEval ts v
    unfold quadForm
    rw [quadBilin_mat_add]
    have hih : quadBilin (sosMatrix ts) v v = sosEval ts v := ih
    rw [hih]
    congr 1
    unfold quadBilin dotFin
    calc sumFin (fun i => sumFin (fun j => w * u i * u j * v i * v j))
        = sumFin (fun i => sumFin (fun j => (w * (u i * v i)) * (u j * v j))) := by
            apply sumFin_congr; intro i
            apply sumFin_congr; intro j
            calc w * u i * u j * v i * v j
                = w * u i * (u j * v i) * v j := by rw [mul_assoc (w * u i)]
              _ = w * u i * (v i * u j) * v j := by rw [mul_comm (u j) (v i)]
              _ = (w * (u i * v i)) * (u j * v j) := by simp only [mul_assoc]
      _ = sumFin (fun i => (w * (u i * v i)) * sumFin (fun j => u j * v j)) := by
            apply sumFin_congr; intro i
            exact sumFin_mul_left (w * (u i * v i)) (fun j => u j * v j)
      _ = sumFin (fun i => w * (u i * v i)) * sumFin (fun j => u j * v j) :=
            sumFin_mul_right _ _
      _ = w * sumFin (fun i => u i * v i) * sumFin (fun j => u j * v j) := by
            rw [sumFin_mul_left]
      _ = w * (sumFin (fun i => u i * v i) * sumFin (fun j => u j * v j)) := mul_assoc _ _ _

def allPosWeights {α : Type} (terms : List (ZHalf × α)) : Bool :=
  terms.all fun t => decide (0 < t.1)

theorem sosEval_nonneg {d : Nat} {terms : List (ZHalf × (Fin d → ZHalf))}
    (hw : allPosWeights terms = true) (v : Fin d → ZHalf) :
    0 ≤ sosEval terms v := by
  induction terms with
  | nil => exact le_refl 0
  | cons t ts ih =>
    unfold allPosWeights at hw
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hw
    rcases hw with ⟨ht, hts⟩
    unfold sosEval
    simp only [List.foldr]
    exact add_nonneg (mul_nonneg (le_of_lt ht) (sq_nonneg _)) (ih hts)

theorem sosEval_eq_zero_mem {d : Nat} {terms : List (ZHalf × (Fin d → ZHalf))}
    (hw : allPosWeights terms = true) {v : Fin d → ZHalf} (hz : sosEval terms v = 0)
    {w : ZHalf} {u : Fin d → ZHalf} (hmem : (w, u) ∈ terms) :
    dotFin u v = 0 := by
  induction terms with
  | nil => cases hmem
  | cons t ts ih =>
    unfold allPosWeights at hw
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hw
    rcases hw with ⟨ht, hts⟩
    unfold sosEval at hz
    simp only [List.foldr] at hz
    have h1 : 0 ≤ t.1 * (dotFin t.2 v * dotFin t.2 v) :=
      mul_nonneg (le_of_lt ht) (sq_nonneg _)
    have h2 : 0 ≤ sosEval ts v := sosEval_nonneg hts v
    rcases List.mem_cons.mp hmem with heq | htail
    · subst heq
      have hterm0 : w * (dotFin u v * dotFin u v) = 0 :=
        eq_zero_of_add_eq_zero_left h1 h2 hz
      rcases mul_eq_zero hterm0 with hw0 | hsq0
      · exfalso; rw [hw0] at ht; exact lt_irrefl 0 ht
      · rcases mul_eq_zero hsq0 with h0 | h0 <;> exact h0
    · have hrest0 : sosEval ts v = 0 := eq_zero_of_add_eq_zero_right h1 h2 hz
      exact ih hts hrest0 htail

def matEq {d : Nat} (A B : Fin d → Fin d → ZHalf) : Bool :=
  (List.finRange d).all fun i => (List.finRange d).all fun j => decide (A i j = B i j)

theorem matEq_sound {d : Nat} {A B : Fin d → Fin d → ZHalf} (h : matEq A B = true) :
    ∀ i j, A i j = B i j := by
  intro i j
  unfold matEq at h
  rw [List.all_eq_true] at h
  have hi := h i (List.mem_finRange i)
  rw [List.all_eq_true] at hi
  exact of_decide_eq_true (hi j (List.mem_finRange j))

/-! ## Section 3: Reusable Infinite Proof Mechanism — Exact Z[1/2] Hierarchical Bilinear-Schur SOS Lifter -/

/-- Pure-data specification of a binary-recursive quadratic form system over Z[1/2]
    with `m` interface linear functionals and arbitrary (possibly asymmetric, non-diagonal)
    2×2 child-transfer matrix `H = [[h00, h01], [h01, h11]]` and (possibly indefinite)
    2m×2m interface matrix `C`. -/
structure BQS (m : Nat) where
  q0  : ZHalf
  l0  : Fin m → ZHalf
  h00 : ZHalf
  h01 : ZHalf
  h11 : ZHalf
  U0  : Fin m → Fin m → ZHalf
  U1  : Fin m → Fin m → ZHalf
  C   : Fin (2 * m) → Fin (2 * m) → ZHalf

def pairVec {m : Nat} (a b : Fin m → ZHalf) : Fin (2 * m) → ZHalf :=
  fun idx =>
    if h : idx.val < m then a ⟨idx.val, h⟩
    else b ⟨idx.val - m, by omega⟩

/-- Recursive interface linear functionals `L sys k x : Fin m → ZHalf`. -/
def BQS.L {m : Nat} (sys : BQS m) : (k : Nat) → (Fin (2 ^ k) → ZHalf) → Fin m → ZHalf
  | 0, x => fun p => sys.l0 p * x ⟨0, by decide⟩
  | k + 1, x => fun p =>
    sumFin (fun q => sys.U0 p q * sys.L k (evenHalf x) q) +
    sumFin (fun q => sys.U1 p q * sys.L k (oddHalf x) q)

/-- Recursive symmetric bilinear form `B sys k x y : ZHalf`. -/
def BQS.B {m : Nat} (sys : BQS m) : (k : Nat) → (Fin (2 ^ k) → ZHalf) → (Fin (2 ^ k) → ZHalf) → ZHalf
  | 0, x, y => sys.q0 * x ⟨0, by decide⟩ * y ⟨0, by decide⟩
  | k + 1, x, y =>
    sys.h00 * sys.B k (evenHalf x) (evenHalf y) +
    sys.h01 * (sys.B k (evenHalf x) (oddHalf y) + sys.B k (oddHalf x) (evenHalf y)) +
    sys.h11 * sys.B k (oddHalf x) (oddHalf y) +
    quadBilin sys.C (pairVec (sys.L k (evenHalf x)) (sys.L k (oddHalf x)))
                    (pairVec (sys.L k (evenHalf y)) (sys.L k (oddHalf y)))

/-- Recursive quadratic form `Q sys k x := B sys k x x`. -/
def BQS.Q {m : Nat} (sys : BQS m) (k : Nat) (x : Fin (2 ^ k) → ZHalf) : ZHalf :=
  sys.B k x x

-- Linearity of L
theorem BQS.L_add {m : Nat} (sys : BQS m) (k : Nat) (x y : Fin (2 ^ k) → ZHalf) :
    sys.L k (vecAdd x y) = vecAdd (sys.L k x) (sys.L k y) := by
  induction k with
  | zero =>
    funext p
    unfold BQS.L vecAdd
    exact mul_add _ _ _
  | succ k ih =>
    funext p
    change sumFin (fun q => sys.U0 p q * sys.L k (vecAdd (evenHalf x) (evenHalf y)) q) +
           sumFin (fun q => sys.U1 p q * sys.L k (vecAdd (oddHalf x) (oddHalf y)) q) =
           (sumFin (fun q => sys.U0 p q * sys.L k (evenHalf x) q) +
            sumFin (fun q => sys.U1 p q * sys.L k (oddHalf x) q)) +
           (sumFin (fun q => sys.U0 p q * sys.L k (evenHalf y) q) +
            sumFin (fun q => sys.U1 p q * sys.L k (oddHalf y) q))
    rw [ih (evenHalf x) (evenHalf y), ih (oddHalf x) (oddHalf y)]
    unfold vecAdd
    have s0 : sumFin (fun q => sys.U0 p q * (sys.L k (evenHalf x) q + sys.L k (evenHalf y) q)) =
              sumFin (fun q => sys.U0 p q * sys.L k (evenHalf x) q) +
              sumFin (fun q => sys.U0 p q * sys.L k (evenHalf y) q) := by
      rw [← sumFin_add]
      exact sumFin_congr fun q => mul_add _ _ _
    have s1 : sumFin (fun q => sys.U1 p q * (sys.L k (oddHalf x) q + sys.L k (oddHalf y) q)) =
              sumFin (fun q => sys.U1 p q * sys.L k (oddHalf x) q) +
              sumFin (fun q => sys.U1 p q * sys.L k (oddHalf y) q) := by
      rw [← sumFin_add]
      exact sumFin_congr fun q => mul_add _ _ _
    rw [s0, s1]
    exact add_four_swap _ _ _ _

theorem BQS.L_smul {m : Nat} (sys : BQS m) (k : Nat) (c : ZHalf) (x : Fin (2 ^ k) → ZHalf) :
    sys.L k (vecSmul c x) = vecSmul c (sys.L k x) := by
  induction k with
  | zero =>
    funext p
    unfold BQS.L vecSmul
    rw [← mul_assoc, mul_comm (sys.l0 p) c, mul_assoc]
  | succ k ih =>
    funext p
    change sumFin (fun q => sys.U0 p q * sys.L k (vecSmul c (evenHalf x)) q) +
           sumFin (fun q => sys.U1 p q * sys.L k (vecSmul c (oddHalf x)) q) =
           c * (sumFin (fun q => sys.U0 p q * sys.L k (evenHalf x) q) +
                sumFin (fun q => sys.U1 p q * sys.L k (oddHalf x) q))
    rw [ih (evenHalf x), ih (oddHalf x)]
    unfold vecSmul
    have s0 : sumFin (fun q => sys.U0 p q * (c * sys.L k (evenHalf x) q)) =
              c * sumFin (fun q => sys.U0 p q * sys.L k (evenHalf x) q) := by
      rw [← sumFin_mul_left]
      exact sumFin_congr fun q => by rw [← mul_assoc, mul_comm (sys.U0 p q) c, mul_assoc]
    have s1 : sumFin (fun q => sys.U1 p q * (c * sys.L k (oddHalf x) q)) =
              c * sumFin (fun q => sys.U1 p q * sys.L k (oddHalf x) q) := by
      rw [← sumFin_mul_left]
      exact sumFin_congr fun q => by rw [← mul_assoc, mul_comm (sys.U1 p q) c, mul_assoc]
    rw [s0, s1, ← mul_add]

theorem pairVec_add {m : Nat} (a1 a2 b1 b2 : Fin m → ZHalf) :
    pairVec (vecAdd a1 a2) (vecAdd b1 b2) = vecAdd (pairVec a1 b1) (pairVec a2 b2) := by
  funext idx
  unfold pairVec vecAdd
  by_cases h : idx.val < m <;> simp [h]

theorem pairVec_smul {m : Nat} (c : ZHalf) (a b : Fin m → ZHalf) :
    pairVec (vecSmul c a) (vecSmul c b) = vecSmul c (pairVec a b) := by
  funext idx
  unfold pairVec vecSmul
  by_cases h : idx.val < m <;> simp [h]

-- Symmetry and bilinearity of B
theorem BQS.B_symm {m : Nat} (sys : BQS m) (hC : ∀ i j, sys.C i j = sys.C j i)
    (k : Nat) (x y : Fin (2 ^ k) → ZHalf) : sys.B k x y = sys.B k y x := by
  induction k with
  | zero =>
    unfold BQS.B
    rw [mul_assoc, mul_comm (x ⟨0, by decide⟩) (y ⟨0, by decide⟩), ← mul_assoc]
  | succ k ih =>
    unfold BQS.B
    rw [ih (evenHalf x) (evenHalf y), ih (oddHalf x) (oddHalf y),
        ih (evenHalf x) (oddHalf y), ih (oddHalf x) (evenHalf y),
        add_comm (sys.B k (oddHalf y) (evenHalf x)),
        quadBilin_symm hC]

theorem BQS.B_add_left {m : Nat} (sys : BQS m) (k : Nat) (x y z : Fin (2 ^ k) → ZHalf) :
    sys.B k (vecAdd x y) z = sys.B k x z + sys.B k y z := by
  induction k with
  | zero =>
    unfold BQS.B vecAdd
    rw [mul_add, add_mul]
  | succ k ih =>
    change sys.h00 * sys.B k (vecAdd (evenHalf x) (evenHalf y)) (evenHalf z) +
           sys.h01 * (sys.B k (vecAdd (evenHalf x) (evenHalf y)) (oddHalf z) +
                      sys.B k (vecAdd (oddHalf x) (oddHalf y)) (evenHalf z)) +
           sys.h11 * sys.B k (vecAdd (oddHalf x) (oddHalf y)) (oddHalf z) +
           quadBilin sys.C (pairVec (sys.L k (vecAdd (evenHalf x) (evenHalf y)))
                                    (sys.L k (vecAdd (oddHalf x) (oddHalf y))))
                           (pairVec (sys.L k (evenHalf z)) (sys.L k (oddHalf z))) =
           (sys.h00 * sys.B k (evenHalf x) (evenHalf z) +
            sys.h01 * (sys.B k (evenHalf x) (oddHalf z) + sys.B k (oddHalf x) (evenHalf z)) +
            sys.h11 * sys.B k (oddHalf x) (oddHalf z) +
            quadBilin sys.C (pairVec (sys.L k (evenHalf x)) (sys.L k (oddHalf x)))
                            (pairVec (sys.L k (evenHalf z)) (sys.L k (oddHalf z)))) +
           (sys.h00 * sys.B k (evenHalf y) (evenHalf z) +
            sys.h01 * (sys.B k (evenHalf y) (oddHalf z) + sys.B k (oddHalf y) (evenHalf z)) +
            sys.h11 * sys.B k (oddHalf y) (oddHalf z) +
            quadBilin sys.C (pairVec (sys.L k (evenHalf y)) (sys.L k (oddHalf y)))
                            (pairVec (sys.L k (evenHalf z)) (sys.L k (oddHalf z))))
    rw [ih, ih, ih, ih, sys.L_add, sys.L_add, pairVec_add, quadBilin_add_left]
    simp only [mul_add]
    rw [add_four_swap (sys.h01 * sys.B k (evenHalf x) (oddHalf z)),
        add_four_swap (sys.h00 * sys.B k (evenHalf x) (evenHalf z)),
        add_four_swap (sys.h00 * sys.B k (evenHalf x) (evenHalf z) + _),
        add_four_swap (sys.h00 * sys.B k (evenHalf x) (evenHalf z) + _ + _)]

theorem BQS.B_smul_left {m : Nat} (sys : BQS m) (k : Nat) (c : ZHalf) (x y : Fin (2 ^ k) → ZHalf) :
    sys.B k (vecSmul c x) y = c * sys.B k x y := by
  induction k with
  | zero =>
    unfold BQS.B vecSmul
    calc sys.q0 * (c * x ⟨0, by decide⟩) * y ⟨0, by decide⟩
        = (sys.q0 * c * x ⟨0, by decide⟩) * y ⟨0, by decide⟩ := by rw [← mul_assoc sys.q0 c]
      _ = (c * sys.q0 * x ⟨0, by decide⟩) * y ⟨0, by decide⟩ := by rw [mul_comm sys.q0 c]
      _ = c * (sys.q0 * x ⟨0, by decide⟩ * y ⟨0, by decide⟩) := by
            rw [mul_assoc c sys.q0, mul_assoc c (sys.q0 * x ⟨0, by decide⟩)]
  | succ k ih =>
    change sys.h00 * sys.B k (vecSmul c (evenHalf x)) (evenHalf y) +
           sys.h01 * (sys.B k (vecSmul c (evenHalf x)) (oddHalf y) +
                      sys.B k (vecSmul c (oddHalf x)) (evenHalf y)) +
           sys.h11 * sys.B k (vecSmul c (oddHalf x)) (oddHalf y) +
           quadBilin sys.C (pairVec (sys.L k (vecSmul c (evenHalf x)))
                                    (sys.L k (vecSmul c (oddHalf x))))
                           (pairVec (sys.L k (evenHalf y)) (sys.L k (oddHalf y))) =
           c * (sys.h00 * sys.B k (evenHalf x) (evenHalf y) +
                sys.h01 * (sys.B k (evenHalf x) (oddHalf y) + sys.B k (oddHalf x) (evenHalf y)) +
                sys.h11 * sys.B k (oddHalf x) (oddHalf y) +
                quadBilin sys.C (pairVec (sys.L k (evenHalf x)) (sys.L k (oddHalf x)))
                                (pairVec (sys.L k (evenHalf y)) (sys.L k (oddHalf y))))
    rw [ih, ih, ih, ih, sys.L_smul, sys.L_smul, pairVec_smul, quadBilin_smul_left]
    simp only [mul_add]
    have mc : ∀ a b : ZHalf, a * (c * b) = c * (a * b) := fun a b => by
      rw [← mul_assoc, mul_comm a c, mul_assoc]
    rw [mc, mc, mc, mc]

-- Augmented bilinear & quadratic form F_k = Q_k + L_k^T W L_k
def BQS.BF {m : Nat} (sys : BQS m) (W : Fin m → Fin m → ZHalf) (k : Nat)
    (x y : Fin (2 ^ k) → ZHalf) : ZHalf :=
  sys.B k x y + quadBilin W (sys.L k x) (sys.L k y)

def BQS.F {m : Nat} (sys : BQS m) (W : Fin m → Fin m → ZHalf) (k : Nat)
    (x : Fin (2 ^ k) → ZHalf) : ZHalf :=
  sys.BF W k x x

theorem BQS.BF_symm {m : Nat} (sys : BQS m) (W : Fin m → Fin m → ZHalf)
    (hC : ∀ i j, sys.C i j = sys.C j i) (hW : ∀ i j, W i j = W j i)
    (k : Nat) (x y : Fin (2 ^ k) → ZHalf) : sys.BF W k x y = sys.BF W k y x := by
  unfold BQS.BF
  rw [sys.B_symm hC, quadBilin_symm hW]

theorem BQS.BF_add_left {m : Nat} (sys : BQS m) (W : Fin m → Fin m → ZHalf)
    (k : Nat) (x y z : Fin (2 ^ k) → ZHalf) :
    sys.BF W k (vecAdd x y) z = sys.BF W k x z + sys.BF W k y z := by
  unfold BQS.BF
  rw [sys.B_add_left, sys.L_add, quadBilin_add_left]
  exact add_four_swap _ _ _ _

theorem BQS.BF_smul_left {m : Nat} (sys : BQS m) (W : Fin m → Fin m → ZHalf)
    (k : Nat) (c : ZHalf) (x y : Fin (2 ^ k) → ZHalf) :
    sys.BF W k (vecSmul c x) y = c * sys.BF W k x y := by
  unfold BQS.BF
  rw [sys.B_smul_left, sys.L_smul, quadBilin_smul_left, ← mul_add]

theorem BQS.BF_add_right {m : Nat} (sys : BQS m) (W : Fin m → Fin m → ZHalf)
    (hC : ∀ i j, sys.C i j = sys.C j i) (hW : ∀ i j, W i j = W j i)
    (k : Nat) (x y z : Fin (2 ^ k) → ZHalf) :
    sys.BF W k x (vecAdd y z) = sys.BF W k x y + sys.BF W k x z := by
  rw [sys.BF_symm W hC hW k x (vecAdd y z), sys.BF_add_left,
      sys.BF_symm W hC hW k y x, sys.BF_symm W hC hW k z x]

theorem BQS.BF_smul_right {m : Nat} (sys : BQS m) (W : Fin m → Fin m → ZHalf)
    (hC : ∀ i j, sys.C i j = sys.C j i) (hW : ∀ i j, W i j = W j i)
    (k : Nat) (c : ZHalf) (x y : Fin (2 ^ k) → ZHalf) :
    sys.BF W k x (vecSmul c y) = c * sys.BF W k x y := by
  rw [sys.BF_symm W hC hW k x (vecSmul c y), sys.BF_smul_left, sys.BF_symm W hC hW k y x]

/-- Exact bilinear expansion of `w * F_k(p*x0 + q*x1)`. -/
theorem BQS.F_linear_comb {m : Nat} (sys : BQS m) (W : Fin m → Fin m → ZHalf)
    (hC : ∀ i j, sys.C i j = sys.C j i) (hW : ∀ i j, W i j = W j i)
    (k : Nat) (w p q : ZHalf) (x0 x1 : Fin (2 ^ k) → ZHalf) :
    w * sys.F W k (vecAdd (vecSmul p x0) (vecSmul q x1)) =
    (w * p * p) * sys.F W k x0 +
    (w * p * q) * (sys.BF W k x0 x1 + sys.BF W k x1 x0) +
    (w * q * q) * sys.F W k x1 := by
  unfold BQS.F
  rw [sys.BF_add_left, sys.BF_add_right W hC hW, sys.BF_add_right W hC hW,
      sys.BF_smul_left, sys.BF_smul_left, sys.BF_smul_left, sys.BF_smul_left,
      sys.BF_smul_right W hC hW, sys.BF_smul_right W hC hW,
      sys.BF_smul_right W hC hW, sys.BF_smul_right W hC hW]
  simp only [mul_add]
  have h1 : w * (p * (p * sys.BF W k x0 x0)) = w * p * p * sys.BF W k x0 x0 := by simp [mul_assoc]
  have h2 : w * (p * (q * sys.BF W k x0 x1)) = w * p * q * sys.BF W k x0 x1 := by simp [mul_assoc]
  have h3 : w * (q * (p * sys.BF W k x1 x0)) = w * p * q * sys.BF W k x1 x0 := by
    calc w * (q * (p * sys.BF W k x1 x0))
        = w * ((q * p) * sys.BF W k x1 x0) := by rw [mul_assoc q p]
      _ = w * ((p * q) * sys.BF W k x1 x0) := by rw [mul_comm q p]
      _ = w * p * q * sys.BF W k x1 x0 := by simp [mul_assoc]
  have h4 : w * (q * (q * sys.BF W k x1 x1)) = w * q * q * sys.BF W k x1 x1 := by simp [mul_assoc]
  rw [h1, h2, h3, h4]
  exact add_mid_group _ _ _ _

/-- The exact finite 2m × 2m interface defect matrix
    `Δ = C + U^T W U - H ⊗ W` in Z[1/2]. -/
def UMat {m : Nat} (sys : BQS m) (p : Fin m) (j : Fin (2 * m)) : ZHalf :=
  if h : j.val < m then sys.U0 p ⟨j.val, h⟩
  else sys.U1 p ⟨j.val - m, by omega⟩

def UtWU {m : Nat} (sys : BQS m) (W : Fin m → Fin m → ZHalf) (i j : Fin (2 * m)) : ZHalf :=
  sumFin (fun p => sumFin (fun q => UMat sys p i * W p q * UMat sys q j))

def kronHW {m : Nat} (sys : BQS m) (W : Fin m → Fin m → ZHalf) (i j : Fin (2 * m)) : ZHalf :=
  if hi : i.val < m then
    if hj : j.val < m then sys.h00 * W ⟨i.val, hi⟩ ⟨j.val, hj⟩
    else sys.h01 * W ⟨i.val, hi⟩ ⟨j.val - m, by omega⟩
  else
    if hj : j.val < m then sys.h01 * W ⟨i.val - m, by omega⟩ ⟨j.val, hj⟩
    else sys.h11 * W ⟨i.val - m, by omega⟩ ⟨j.val - m, by omega⟩

def deltaMat {m : Nat} (sys : BQS m) (W : Fin m → Fin m → ZHalf) (i j : Fin (2 * m)) : ZHalf :=
  sys.C i j + UtWU sys W i j - kronHW sys W i j

-- Key algebraic lemma 1: L_{k+1}^T W L_{k+1} = Lpair^T (U^T W U) Lpair
theorem quadForm_UtWU {m : Nat} (sys : BQS m) (W : Fin m → Fin m → ZHalf)
    (a b : Fin m → ZHalf) :
    quadForm W (fun p => sumFin (fun q => sys.U0 p q * a q) + sumFin (fun q => sys.U1 p q * b q)) =
    quadForm (UtWU sys W) (pairVec a b) := by
  have hlin : ∀ p : Fin m,
      sumFin (fun j : Fin (2 * m) => UMat sys p j * pairVec a b j) =
      sumFin (fun q : Fin m => sys.U0 p q * a q) + sumFin (fun q : Fin m => sys.U1 p q * b q) := by
    intro p
    rw [sumFin_split_two]
    congr 1
    · apply sumFin_congr; intro q
      unfold UMat pairVec
      simp [q.isLt]
    · apply sumFin_congr; intro q
      unfold UMat pairVec
      have hnot : ¬ (m + q.val < m) := by omega
      have hsub : m + q.val - m = q.val := by omega
      simp [hnot, hsub]
  unfold quadForm quadBilin UtWU
  calc sumFin (fun p => sumFin (fun q => W p q *
          (sumFin (fun r => sys.U0 p r * a r) + sumFin (fun r => sys.U1 p r * b r)) *
          (sumFin (fun r => sys.U0 q r * a r) + sumFin (fun r => sys.U1 q r * b r))))
      = sumFin (fun p => sumFin (fun q => W p q *
          sumFin (fun i => UMat sys p i * pairVec a b i) *
          sumFin (fun j => UMat sys q j * pairVec a b j))) := by
          apply sumFin_congr; intro p; apply sumFin_congr; intro q
          rw [hlin p, hlin q]
    _ = sumFin (fun p => sumFin (fun q =>
          sumFin (fun i => sumFin (fun j => (UMat sys p i * W p q * UMat sys q j) *
            pairVec a b i * pairVec a b j)))) := by
          apply sumFin_congr; intro p; apply sumFin_congr; intro q
          rw [← sumFin_mul_left (W p q), ← sumFin_mul_right]
          apply sumFin_congr; intro i
          rw [← sumFin_mul_left]
          apply sumFin_congr; intro j
          calc W p q * (UMat sys p i * pairVec a b i) * (UMat sys q j * pairVec a b j)
              = (UMat sys p i * W p q) * pairVec a b i * (UMat sys q j * pairVec a b j) := by
                  rw [← mul_assoc (W p q), mul_comm (W p q) (UMat sys p i)]
            _ = (UMat sys p i * W p q) * (pairVec a b i * (UMat sys q j * pairVec a b j)) :=
                  mul_assoc _ _ _
            _ = (UMat sys p i * W p q) * (UMat sys q j * (pairVec a b i * pairVec a b j)) := by
                  rw [← mul_assoc (pairVec a b i), mul_comm (pairVec a b i) (UMat sys q j),
                      mul_assoc (UMat sys q j)]
            _ = UMat sys p i * W p q * UMat sys q j * pairVec a b i * pairVec a b j := by
                  rw [← mul_assoc (UMat sys p i * W p q) (UMat sys q j),
                      ← mul_assoc (UMat sys p i * W p q * UMat sys q j)]
    _ = sumFin (fun p => sumFin (fun i => sumFin (fun q => sumFin (fun j =>
          UMat sys p i * W p q * UMat sys q j * pairVec a b i * pairVec a b j)))) := by
          apply sumFin_congr; intro p; exact sumFin_swap _
    _ = sumFin (fun i => sumFin (fun p => sumFin (fun q => sumFin (fun j =>
          UMat sys p i * W p q * UMat sys q j * pairVec a b i * pairVec a b j)))) :=
          sumFin_swap _
    _ = sumFin (fun i => sumFin (fun p => sumFin (fun j => sumFin (fun q =>
          UMat sys p i * W p q * UMat sys q j * pairVec a b i * pairVec a b j)))) := by
          apply sumFin_congr; intro i; apply sumFin_congr; intro p; exact sumFin_swap _
    _ = sumFin (fun i => sumFin (fun j => sumFin (fun p => sumFin (fun q =>
          UMat sys p i * W p q * UMat sys q j * pairVec a b i * pairVec a b j)))) := by
          apply sumFin_congr; intro i; exact sumFin_swap _
    _ = sumFin (fun i => sumFin (fun j =>
          sumFin (fun p => sumFin (fun q => UMat sys p i * W p q * UMat sys q j)) *
          pairVec a b i * pairVec a b j)) := by
          apply sumFin_congr; intro i; apply sumFin_congr; intro j
          rw [← sumFin_mul_right, ← sumFin_mul_right]
          apply sumFin_congr; intro p
          rw [← sumFin_mul_right, ← sumFin_mul_right]

-- Key algebraic lemma 2: Lpair^T (H ⊗ W) Lpair = h00*W(a,a) + h01*(W(a,b)+W(b,a)) + h11*W(b,b)
theorem quadForm_kronHW {m : Nat} (sys : BQS m) (W : Fin m → Fin m → ZHalf)
    (a b : Fin m → ZHalf) :
    quadForm (kronHW sys W) (pairVec a b) =
    sys.h00 * quadBilin W a a +
    sys.h01 * (quadBilin W a b + quadBilin W b a) +
    sys.h11 * quadBilin W b b := by
  unfold quadForm quadBilin
  rw [sumFin_split_two]
  have splitInner : ∀ (f : Fin (2 * m) → ZHalf),
      sumFin f = sumFin (fun j : Fin m => f ⟨j.val, by omega⟩) +
                 sumFin (fun j : Fin m => f ⟨m + j.val, by omega⟩) :=
    fun f => sumFin_split_two f
  have hL : sumFin (fun i : Fin m => sumFin (fun j : Fin (2 * m) =>
              kronHW sys W ⟨i.val, by omega⟩ j * pairVec a b ⟨i.val, by omega⟩ * pairVec a b j)) =
            sys.h00 * sumFin (fun i => sumFin (fun j => W i j * a i * a j)) +
            sys.h01 * sumFin (fun i => sumFin (fun j => W i j * a i * b j)) := by
    rw [sumFin_congr (fun i => splitInner _), sumFin_add]
    congr 1
    · rw [← sumFin_mul_left]
      apply sumFin_congr; intro i
      rw [← sumFin_mul_left]
      apply sumFin_congr; intro j
      unfold kronHW pairVec
      simp only [i.isLt, j.isLt, ↓reduceDIte]
      simp [mul_assoc]
    · rw [← sumFin_mul_left]
      apply sumFin_congr; intro i
      rw [← sumFin_mul_left]
      apply sumFin_congr; intro j
      unfold kronHW pairVec
      have hj : ¬ (m + j.val < m) := by omega
      have hsub : m + j.val - m = j.val := by omega
      simp only [i.isLt, hj, hsub, ↓reduceDIte]
      simp [mul_assoc]
  have hR : sumFin (fun i : Fin m => sumFin (fun j : Fin (2 * m) =>
              kronHW sys W ⟨m + i.val, by omega⟩ j * pairVec a b ⟨m + i.val, by omega⟩ * pairVec a b j)) =
            sys.h01 * sumFin (fun i => sumFin (fun j => W i j * b i * a j)) +
            sys.h11 * sumFin (fun i => sumFin (fun j => W i j * b i * b j)) := by
    rw [sumFin_congr (fun i => splitInner _), sumFin_add]
    congr 1
    · rw [← sumFin_mul_left]
      apply sumFin_congr; intro i
      rw [← sumFin_mul_left]
      apply sumFin_congr; intro j
      unfold kronHW pairVec
      have hi : ¬ (m + i.val < m) := by omega
      have hsub : m + i.val - m = i.val := by omega
      simp only [hi, j.isLt, hsub, ↓reduceDIte]
      simp [mul_assoc]
    · rw [← sumFin_mul_left]
      apply sumFin_congr; intro i
      rw [← sumFin_mul_left]
      apply sumFin_congr; intro j
      unfold kronHW pairVec
      have hi : ¬ (m + i.val < m) := by omega
      have hj : ¬ (m + j.val < m) := by omega
      have hsubi : m + i.val - m = i.val := by omega
      have hsubj : m + j.val - m = j.val := by omega
      simp only [hi, hj, hsubi, hsubj, ↓reduceDIte]
      simp [mul_assoc]
  rw [hL, hR, mul_add]
  exact add_mid_group _ _ _ _

/-- MASTER RECURSIVE SCHUR-DEFECT IDENTITY:
    For EVERY `k` and EVERY `x : Fin (2^(k+1)) → ZHalf`:
    `F_{k+1}(x) = h00*F_k(x0) + h01*(BF_k(x0,x1) + BF_k(x1,x0)) + h11*F_k(x1) + Lpair^T Δ Lpair`. -/
theorem BQS.F_step_identity {m : Nat} (sys : BQS m) (W : Fin m → Fin m → ZHalf)
    (k : Nat) (x : Fin (2 ^ (k + 1)) → ZHalf) :
    sys.F W (k + 1) x =
      sys.h00 * sys.F W k (evenHalf x) +
      sys.h01 * (sys.BF W k (evenHalf x) (oddHalf x) + sys.BF W k (oddHalf x) (evenHalf x)) +
      sys.h11 * sys.F W k (oddHalf x) +
      quadForm (deltaMat sys W) (pairVec (sys.L k (evenHalf x)) (sys.L k (oddHalf x))) := by
  have hdelta : quadForm (deltaMat sys W) (pairVec (sys.L k (evenHalf x)) (sys.L k (oddHalf x))) =
      quadForm sys.C (pairVec (sys.L k (evenHalf x)) (sys.L k (oddHalf x))) +
      quadForm (UtWU sys W) (pairVec (sys.L k (evenHalf x)) (sys.L k (oddHalf x))) -
      quadForm (kronHW sys W) (pairVec (sys.L k (evenHalf x)) (sys.L k (oddHalf x))) := by
    unfold quadForm deltaMat
    rw [quadBilin_mat_sub, quadBilin_mat_add]
  unfold BQS.F BQS.BF
  change (sys.h00 * sys.B k (evenHalf x) (evenHalf x) +
          sys.h01 * (sys.B k (evenHalf x) (oddHalf x) + sys.B k (oddHalf x) (evenHalf x)) +
          sys.h11 * sys.B k (oddHalf x) (oddHalf x) +
          quadForm sys.C (pairVec (sys.L k (evenHalf x)) (sys.L k (oddHalf x)))) +
         quadForm W (sys.L (k + 1) x) = _
  have hUtWU : quadForm W (sys.L (k + 1) x) =
               quadForm (UtWU sys W) (pairVec (sys.L k (evenHalf x)) (sys.L k (oddHalf x))) :=
    quadForm_UtWU sys W (sys.L k (evenHalf x)) (sys.L k (oddHalf x))
  rw [hUtWU, hdelta, quadForm_kronHW sys W (sys.L k (evenHalf x)) (sys.L k (oddHalf x))]
  have hRHS1 :
      sys.h00 * (sys.B k (evenHalf x) (evenHalf x) + quadBilin W (sys.L k (evenHalf x)) (sys.L k (evenHalf x))) +
      sys.h01 * ((sys.B k (evenHalf x) (oddHalf x) + quadBilin W (sys.L k (evenHalf x)) (sys.L k (oddHalf x))) +
                 (sys.B k (oddHalf x) (evenHalf x) + quadBilin W (sys.L k (oddHalf x)) (sys.L k (evenHalf x)))) +
      sys.h11 * (sys.B k (oddHalf x) (oddHalf x) + quadBilin W (sys.L k (oddHalf x)) (sys.L k (oddHalf x))) =
      (sys.h00 * sys.B k (evenHalf x) (evenHalf x) +
       sys.h01 * (sys.B k (evenHalf x) (oddHalf x) + sys.B k (oddHalf x) (evenHalf x)) +
       sys.h11 * sys.B k (oddHalf x) (oddHalf x)) +
      (sys.h00 * quadBilin W (sys.L k (evenHalf x)) (sys.L k (evenHalf x)) +
       sys.h01 * (quadBilin W (sys.L k (evenHalf x)) (sys.L k (oddHalf x)) +
                  quadBilin W (sys.L k (oddHalf x)) (sys.L k (evenHalf x))) +
       sys.h11 * quadBilin W (sys.L k (oddHalf x)) (sys.L k (oddHalf x))) := by
    rw [add_four_swap (sys.B k (evenHalf x) (oddHalf x)), mul_add, mul_add, mul_add,
        add_four_swap (sys.h00 * sys.B k (evenHalf x) (evenHalf x)),
        add_four_swap (sys.h00 * sys.B k (evenHalf x) (evenHalf x) + _),
        mul_add, mul_add]
  rw [hRHS1, sub_eq_add_neg]
  generalize sys.h00 * sys.B k (evenHalf x) (evenHalf x) +
             sys.h01 * (sys.B k (evenHalf x) (oddHalf x) + sys.B k (oddHalf x) (evenHalf x)) +
             sys.h11 * sys.B k (oddHalf x) (oddHalf x) = Bsum
  generalize sys.h00 * quadBilin W (sys.L k (evenHalf x)) (sys.L k (evenHalf x)) +
             sys.h01 * (quadBilin W (sys.L k (evenHalf x)) (sys.L k (oddHalf x)) +
                        quadBilin W (sys.L k (oddHalf x)) (sys.L k (evenHalf x))) +
             sys.h11 * quadBilin W (sys.L k (oddHalf x)) (sys.L k (oddHalf x)) = K
  generalize quadForm sys.C (pairVec (sys.L k (evenHalf x)) (sys.L k (oddHalf x))) = cT
  generalize quadForm (UtWU sys W) (pairVec (sys.L k (evenHalf x)) (sys.L k (oddHalf x))) = uT
  calc (Bsum + cT) + uT = Bsum + (cT + uT) := add_assoc Bsum cT uT
    _ = Bsum + (cT + uT) + 0 := (add_zero _).symm
    _ = Bsum + (cT + uT) + (K + (-K)) := by rw [add_neg_cancel]
    _ = (Bsum + K) + ((cT + uT) + (-K)) := add_four_swap Bsum (cT + uT) K (-K)

/-! ### Pure-Data Finite Z[1/2] Positivity Certificate & Soundness Lifters -/

/-- Pure-data finite Z[1/2] Gram/SOS certificate (zero `Prop` fields!). -/
structure PDCert (m : Nat) where
  W            : Fin m → Fin m → ZHalf
  h1           : ZHalf × ZHalf × ZHalf
  h2           : ZHalf × ZHalf × ZHalf
  hExtra       : List (ZHalf × ZHalf × ZHalf)
  deltaTerms   : List (ZHalf × (Fin (2 * m) → ZHalf))
  surplusTerms : List (ZHalf × (Fin m → ZHalf))

def hTermsSum (terms : List (ZHalf × ZHalf × ZHalf)) : ZHalf × ZHalf × ZHalf :=
  terms.foldr (fun t acc =>
    (t.1 * t.2.1 * t.2.1 + acc.1,
     t.1 * t.2.1 * t.2.2 + acc.2.1,
     t.1 * t.2.2 * t.2.2 + acc.2.2)) (0, 0, 0)

def hTermsEval {m : Nat} (sys : BQS m) (W : Fin m → Fin m → ZHalf) (k : Nat)
    (terms : List (ZHalf × ZHalf × ZHalf)) (x0 x1 : Fin (2 ^ k) → ZHalf) : ZHalf :=
  terms.foldr (fun t acc =>
    t.1 * sys.F W k (vecAdd (vecSmul t.2.1 x0) (vecSmul t.2.2 x1)) + acc) 0

theorem hTermsEval_eq {m : Nat} (sys : BQS m) (W : Fin m → Fin m → ZHalf)
    (hC : ∀ i j, sys.C i j = sys.C j i) (hW : ∀ i j, W i j = W j i)
    (k : Nat) (terms : List (ZHalf × ZHalf × ZHalf)) (x0 x1 : Fin (2 ^ k) → ZHalf) :
    hTermsEval sys W k terms x0 x1 =
      (hTermsSum terms).1 * sys.F W k x0 +
      (hTermsSum terms).2.1 * (sys.BF W k x0 x1 + sys.BF W k x1 x0) +
      (hTermsSum terms).2.2 * sys.F W k x1 := by
  induction terms with
  | nil =>
    unfold hTermsEval hTermsSum
    simp [zero_mul, add_zero]
  | cons t ts ih =>
    rcases t with ⟨w, p, q⟩
    change w * sys.F W k (vecAdd (vecSmul p x0) (vecSmul q x1)) + hTermsEval sys W k ts x0 x1 =
           (w * p * p + (hTermsSum ts).1) * sys.F W k x0 +
           (w * p * q + (hTermsSum ts).2.1) * (sys.BF W k x0 x1 + sys.BF W k x1 x0) +
           (w * q * q + (hTermsSum ts).2.2) * sys.F W k x1
    rw [sys.F_linear_comb W hC hW k w p q x0 x1, ih]
    simp only [add_mul]
    rw [add_four_swap (w * p * p * sys.F W k x0 + _),
        add_four_swap (w * p * p * sys.F W k x0)]

theorem hTermsEval_nonneg {m : Nat} (sys : BQS m) (W : Fin m → Fin m → ZHalf) (k : Nat)
    (hF : ∀ u, 0 ≤ sys.F W k u)
    {terms : List (ZHalf × ZHalf × ZHalf)} (hw : allPosWeights terms = true)
    (x0 x1 : Fin (2 ^ k) → ZHalf) :
    0 ≤ hTermsEval sys W k terms x0 x1 := by
  induction terms with
  | nil => exact le_refl 0
  | cons t ts ih =>
    unfold allPosWeights at hw
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hw
    unfold hTermsEval
    simp only [List.foldr]
    exact add_nonneg (mul_nonneg (le_of_lt hw.1) (hF _)) (ih hw.2)

/-- Linear independence over Z[1/2]: if `p1*q2 - q1*p2 ≠ 0` and `(x0, x1) ≠ (0, 0)`,
    then at least one of `p1*x0 + q1*x1` or `p2*x0 + q2*x1` is nonzero. -/
theorem spanning_pair_nonzero {n : Nat} {p1 q1 p2 q2 : ZHalf}
    (hdet : p1 * q2 - q1 * p2 ≠ 0)
    {x0 x1 : Fin n → ZHalf} (hne : (∃ i, x0 i ≠ 0) ∨ (∃ i, x1 i ≠ 0)) :
    (∃ i, vecAdd (vecSmul p1 x0) (vecSmul q1 x1) i ≠ 0) ∨
    (∃ i, vecAdd (vecSmul p2 x0) (vecSmul q2 x1) i ≠ 0) := by
  by_cases h1 : ∃ i, vecAdd (vecSmul p1 x0) (vecSmul q1 x1) i ≠ 0
  · exact Or.inl h1
  · by_cases h2 : ∃ i, vecAdd (vecSmul p2 x0) (vecSmul q2 x1) i ≠ 0
    · exact Or.inr h2
    · exfalso
      have hz1 : ∀ i, p1 * x0 i + q1 * x1 i = 0 := fun i =>
        Classical.byContradiction (fun hc => h1 ⟨i, hc⟩)
      have hz2 : ∀ i, p2 * x0 i + q2 * x1 i = 0 := fun i =>
        Classical.byContradiction (fun hc => h2 ⟨i, hc⟩)
      have hsub_cancel : ∀ a b z : ZHalf, a - b = (a + z) - (b + z) := fun a b z => by
        rw [sub_eq_add_neg, sub_eq_add_neg, neg_add, add_four_swap a z (-b) (-z), add_neg_cancel, add_zero]
      have hboth : ∀ i, x0 i = 0 ∧ x1 i = 0 := fun i => by
        have eqx0 : (p1 * q2 - q1 * p2) * x0 i = 0 := by
          calc (p1 * q2 - q1 * p2) * x0 i
              = q2 * (p1 * x0 i + q1 * x1 i) - q1 * (p2 * x0 i + q2 * x1 i) := by
                  rw [mul_add, mul_add, sub_mul]
                  have t1 : q2 * (p1 * x0 i) = p1 * q2 * x0 i := by rw [← mul_assoc, mul_comm q2 p1]
                  have t2 : q1 * (p2 * x0 i) = q1 * p2 * x0 i := by rw [← mul_assoc]
                  have t3 : q2 * (q1 * x1 i) = q1 * (q2 * x1 i) := by rw [← mul_assoc, mul_comm q2 q1, mul_assoc]
                  rw [t1, t2, t3]
                  exact hsub_cancel (p1 * q2 * x0 i) (q1 * p2 * x0 i) (q1 * (q2 * x1 i))
            _ = q2 * 0 - q1 * 0 := by rw [hz1 i, hz2 i]
            _ = 0 := by rw [mul_zero, mul_zero, sub_self]
        have eqx1 : (p1 * q2 - q1 * p2) * x1 i = 0 := by
          calc (p1 * q2 - q1 * p2) * x1 i
              = p1 * (p2 * x0 i + q2 * x1 i) - p2 * (p1 * x0 i + q1 * x1 i) := by
                  rw [mul_add, mul_add, sub_mul]
                  have t1 : p1 * (p2 * x0 i) = p2 * (p1 * x0 i) := by rw [← mul_assoc, mul_comm p1 p2, mul_assoc]
                  have t2 : p1 * (q2 * x1 i) = p1 * q2 * x1 i := by rw [← mul_assoc]
                  have t3 : p2 * (q1 * x1 i) = q1 * p2 * x1 i := by rw [← mul_assoc, mul_comm p2 q1]
                  rw [t1, t2, t3, add_comm (p2 * (p1 * x0 i)) (p1 * q2 * x1 i),
                      add_comm (p2 * (p1 * x0 i)) (q1 * p2 * x1 i)]
                  exact hsub_cancel (p1 * q2 * x1 i) (q1 * p2 * x1 i) (p2 * (p1 * x0 i))
            _ = p1 * 0 - p2 * 0 := by rw [hz2 i, hz1 i]
            _ = 0 := by rw [mul_zero, mul_zero, sub_self]
        have hx0 : x0 i = 0 := (mul_eq_zero eqx0).resolve_left hdet
        have hx1 : x1 i = 0 := (mul_eq_zero eqx1).resolve_left hdet
        exact ⟨hx0, hx1⟩
      rcases hne with ⟨i, hi⟩ | ⟨i, hi⟩
      · exact hi (hboth i).1
      · exact hi (hboth i).2

/-- Base-case scalar `f0 = q0 + l0^T W l0`. -/
def baseScalar {m : Nat} (sys : BQS m) (W : Fin m → Fin m → ZHalf) : ZHalf :=
  sys.q0 + quadForm W sys.l0

theorem BQS.F_zero_eq {m : Nat} (sys : BQS m) (W : Fin m → Fin m → ZHalf)
    (x : Fin (2 ^ 0) → ZHalf) :
    sys.F W 0 x = baseScalar sys W * (x ⟨0, by decide⟩ * x ⟨0, by decide⟩) := by
  unfold BQS.F BQS.BF BQS.B BQS.L baseScalar
  have hq : quadBilin W (fun p => sys.l0 p * x ⟨0, by decide⟩)
                        (fun p => sys.l0 p * x ⟨0, by decide⟩) =
            quadForm W sys.l0 * (x ⟨0, by decide⟩ * x ⟨0, by decide⟩) := by
    unfold quadForm quadBilin
    rw [← sumFin_mul_right]
    apply sumFin_congr; intro i
    rw [← sumFin_mul_right]
    apply sumFin_congr; intro j
    calc W i j * (sys.l0 i * x ⟨0, by decide⟩) * (sys.l0 j * x ⟨0, by decide⟩)
        = (W i j * sys.l0 i) * (x ⟨0, by decide⟩ * (sys.l0 j * x ⟨0, by decide⟩)) := by simp [mul_assoc]
      _ = (W i j * sys.l0 i) * (sys.l0 j * (x ⟨0, by decide⟩ * x ⟨0, by decide⟩)) := by
            rw [← mul_assoc (x ⟨0, by decide⟩) (sys.l0 j), mul_comm (x ⟨0, by decide⟩) (sys.l0 j),
                mul_assoc (sys.l0 j)]
      _ = W i j * sys.l0 i * sys.l0 j * (x ⟨0, by decide⟩ * x ⟨0, by decide⟩) := by simp [mul_assoc]
  rw [hq, add_mul, mul_assoc]

/-- Common certificate-validity core (symmetry, H spanning SOS, Δ SOS, surplus SOS). -/
def checkCoreCert {m : Nat} (sys : BQS m) (Wtarget : Fin m → Fin m → ZHalf) (cert : PDCert m) : Bool :=
  let hAll := cert.h1 :: cert.h2 :: cert.hExtra
  let hs := hTermsSum hAll
  let det := cert.h1.2.1 * cert.h2.2.2 - cert.h1.2.2 * cert.h2.2.1
  isSymmMat sys.C &&
  isSymmMat cert.W &&
  isSymmMat Wtarget &&
  allPosWeights hAll &&
  decide (det ≠ 0) &&
  decide (hs.1 = sys.h00) &&
  decide (hs.2.1 = sys.h01) &&
  decide (hs.2.2 = sys.h11) &&
  allPosWeights cert.deltaTerms &&
  matEq (deltaMat sys cert.W) (sosMatrix cert.deltaTerms) &&
  allPosWeights cert.surplusTerms &&
  matEq (fun i j => Wtarget i j - cert.W i j) (sosMatrix cert.surplusTerms)

/-- Mode 1 Decidable Verifier (Base-Strictly-Positive Lifting). -/
def checkStrictPD {m : Nat} (sys : BQS m) (Wtarget : Fin m → Fin m → ZHalf) (cert : PDCert m) : Bool :=
  checkCoreCert sys Wtarget cert &&
  decide (0 < baseScalar sys cert.W)

def isLeftEigenvector {m : Nat} (sys : BQS m) (tau : ZHalf) : Bool :=
  decide (tau ≠ 0) &&
  (List.finRange m).all fun p =>
    decide (sumFin (fun q => sys.U0 p q * sys.l0 q) = tau * sys.l0 p)

def hasRightKiller {m : Nat} (sys : BQS m) (terms : List (ZHalf × (Fin (2 * m) → ZHalf))) : Bool :=
  let vL := pairVec sys.l0 (vecZero m)
  let vR := pairVec (vecZero m) sys.l0
  terms.any fun t => decide (dotFin t.2 vL = 0) && decide (dotFin t.2 vR ≠ 0)

/-- Mode 2 Decidable Verifier (Degenerate-Base / Boundary-Kernel-Collapse Lifting). -/
def checkBoundaryStrictPD {m : Nat} (sys : BQS m) (Wtarget : Fin m → Fin m → ZHalf)
    (cert : PDCert m) (tau : ZHalf) : Bool :=
  checkCoreCert sys Wtarget cert &&
  decide (0 ≤ baseScalar sys cert.W) &&
  isLeftEigenvector sys tau &&
  hasRightKiller sys cert.deltaTerms &&
  decide (0 < quadForm (fun i j => Wtarget i j - cert.W i j) sys.l0)

def powZHalf (c : ZHalf) : Nat → ZHalf
  | 0 => 1
  | k + 1 => c * powZHalf c k

theorem powZHalf_ne_zero {c : ZHalf} (hc : c ≠ 0) (k : Nat) : powZHalf c k ≠ 0 := by
  induction k with
  | zero => show (1 : ZHalf) ≠ 0; decide
  | succ k ih =>
    intro h
    rcases mul_eq_zero h with hc0 | hk0
    · exact hc hc0
    · exact ih hk0

theorem BQS.L_of_support_zero {m : Nat} (sys : BQS m) {tau : ZHalf}
    (heig : ∀ p, sumFin (fun q => sys.U0 p q * sys.l0 q) = tau * sys.l0 p) :
    ∀ (k : Nat) (x : Fin (2 ^ k) → ZHalf),
      (∀ i : Fin (2 ^ k), i.val ≠ 0 → x i = 0) →
      sys.L k x = vecSmul (powZHalf tau k * x ⟨0, Nat.two_pow_pos k⟩) sys.l0 := by
  intro k
  induction k with
  | zero =>
    intro x _
    funext p
    unfold BQS.L vecSmul powZHalf
    rw [one_mul, mul_comm]
  | succ k ih =>
    intro x hsupp
    have hx0 : ∀ i : Fin (2 ^ k), i.val ≠ 0 → evenHalf x i = 0 := fun i hi =>
      hsupp ⟨2 * i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ (show 2 * i.val ≠ 0 by omega)
    have hx1 : ∀ i : Fin (2 ^ k), oddHalf x i = 0 := fun i =>
      hsupp ⟨2 * i.val + 1, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ (show 2 * i.val + 1 ≠ 0 by omega)
    have hL0 := ih (evenHalf x) hx0
    have hL1 : sys.L k (oddHalf x) = vecZero m := by
      have hL1' := ih (oddHalf x) (fun i _ => hx1 i)
      rw [hL1', hx1 ⟨0, Nat.two_pow_pos k⟩, mul_zero]
      funext p; unfold vecSmul vecZero; exact zero_mul _
    funext p
    unfold BQS.L vecSmul powZHalf
    rw [hL0, hL1]
    have h1zero : sumFin (fun q => sys.U1 p q * vecZero m q) = 0 := by
      rw [sumFin_congr (fun q => by unfold vecZero; exact mul_zero _)]
      exact sumFin_zero
    rw [h1zero, add_zero]
    unfold vecSmul
    have hpull : sumFin (fun q => sys.U0 p q * (powZHalf tau k * evenHalf x ⟨0, Nat.two_pow_pos k⟩ * sys.l0 q)) =
                 (powZHalf tau k * evenHalf x ⟨0, Nat.two_pow_pos k⟩) * sumFin (fun q => sys.U0 p q * sys.l0 q) := by
      rw [← sumFin_mul_left]
      exact sumFin_congr fun q => by
        rw [← mul_assoc, mul_comm (sys.U0 p q), mul_assoc]
    rw [hpull, heig p]
    have hev0 : evenHalf x ⟨0, Nat.two_pow_pos k⟩ = x ⟨0, Nat.two_pow_pos (k + 1)⟩ := rfl
    rw [hev0]
    calc powZHalf tau k * x ⟨0, Nat.two_pow_pos (k + 1)⟩ * (tau * sys.l0 p)
        = (powZHalf tau k * x ⟨0, Nat.two_pow_pos (k + 1)⟩ * tau) * sys.l0 p := (mul_assoc _ _ _).symm
      _ = (tau * (powZHalf tau k * x ⟨0, Nat.two_pow_pos (k + 1)⟩)) * sys.l0 p := by
            rw [mul_comm (powZHalf tau k * x ⟨0, Nat.two_pow_pos (k + 1)⟩) tau]
      _ = tau * powZHalf tau k * x ⟨0, Nat.two_pow_pos (k + 1)⟩ * sys.l0 p := by
            rw [mul_assoc tau (powZHalf tau k)]

/-- Mode 2 UNIVERSAL INFINITE SOUNDNESS THEOREM (Boundary-Kernel-Collapse Lifting). -/
theorem soundness_boundary_strict_pd {m : Nat} (sys : BQS m) (Wtarget : Fin m → Fin m → ZHalf)
    (cert : PDCert m) (tau : ZHalf) (hcheck : checkBoundaryStrictPD sys Wtarget cert tau = true) :
    ∀ (k : Nat) (x : Fin (2 ^ k) → ZHalf), (∃ i, x i ≠ 0) →
      0 < sys.Q k x + quadForm Wtarget (sys.L k x) := by
  unfold checkBoundaryStrictPD checkCoreCert isLeftEigenvector hasRightKiller at hcheck
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hCsym, hWsym⟩, _⟩, hHpos⟩, hdet⟩, hh00⟩, hh01⟩, hh11⟩, hDpos⟩, hDeq⟩, hSpos⟩, hSeq⟩, hf0⟩, ⟨htau, heigRaw⟩⟩, hkill⟩, hSurpPos⟩
  have hC : ∀ i j, sys.C i j = sys.C j i := isSymmMat_sound hCsym
  have hW : ∀ i j, cert.W i j = cert.W j i := isSymmMat_sound hWsym
  have hDm := matEq_sound hDeq
  have hSm := matEq_sound hSeq
  have heig : ∀ p, sumFin (fun q => sys.U0 p q * sys.l0 q) = tau * sys.l0 p := fun p => by
    rw [List.all_eq_true] at heigRaw
    exact of_decide_eq_true (heigRaw p (List.mem_finRange p))
  rw [List.any_eq_true] at hkill
  rcases hkill with ⟨⟨wk, uk⟩, hkMem, hkProps⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hkProps
  rcases hkProps with ⟨hkL, hkR⟩
  unfold allPosWeights at hHpos
  simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hHpos
  rcases hHpos with ⟨hw1, hw2, hwExtra⟩
  have hF_ind : ∀ k : Nat,
      (∀ x : Fin (2 ^ k) → ZHalf, 0 ≤ sys.F cert.W k x) ∧
      (∀ x : Fin (2 ^ k) → ZHalf, sys.F cert.W k x = 0 → ∀ i : Fin (2 ^ k), i.val ≠ 0 → x i = 0) := by
    intro k
    induction k with
    | zero =>
      constructor
      · intro x; rw [sys.F_zero_eq]; exact mul_nonneg hf0 (sq_nonneg _)
      · intro x _ i hi; exfalso; have := i.isLt; omega
    | succ k ih =>
      rcases ih with ⟨ih_ge, ih_ker⟩
      have hStep : ∀ x : Fin (2 ^ (k + 1)) → ZHalf,
          sys.F cert.W (k + 1) x =
            (cert.h1.1 * sys.F cert.W k (vecAdd (vecSmul cert.h1.2.1 (evenHalf x)) (vecSmul cert.h1.2.2 (oddHalf x))) +
             cert.h2.1 * sys.F cert.W k (vecAdd (vecSmul cert.h2.2.1 (evenHalf x)) (vecSmul cert.h2.2.2 (oddHalf x))) +
             hTermsEval sys cert.W k cert.hExtra (evenHalf x) (oddHalf x)) +
            sosEval cert.deltaTerms (pairVec (sys.L k (evenHalf x)) (sys.L k (oddHalf x))) := by
        intro x
        rw [sys.F_step_identity cert.W k x]
        have hHT := hTermsEval_eq sys cert.W hC hW k (cert.h1 :: cert.h2 :: cert.hExtra) (evenHalf x) (oddHalf x)
        rw [hh00, hh01, hh11] at hHT
        rw [← hHT]
        have hDval : quadForm (deltaMat sys cert.W) (pairVec (sys.L k (evenHalf x)) (sys.L k (oddHalf x))) =
                     sosEval cert.deltaTerms (pairVec (sys.L k (evenHalf x)) (sys.L k (oddHalf x))) := by
          rw [← quadForm_sosMatrix cert.deltaTerms]
          unfold quadForm quadBilin
          apply sumFin_congr; intro i
          apply sumFin_congr; intro j
          rw [hDm i j]
        rw [hDval]
        change (cert.h1.1 * sys.F cert.W k (vecAdd (vecSmul cert.h1.2.1 (evenHalf x)) (vecSmul cert.h1.2.2 (oddHalf x))) +
                (cert.h2.1 * sys.F cert.W k (vecAdd (vecSmul cert.h2.2.1 (evenHalf x)) (vecSmul cert.h2.2.2 (oddHalf x))) +
                 hTermsEval sys cert.W k cert.hExtra (evenHalf x) (oddHalf x))) +
               sosEval cert.deltaTerms (pairVec (sys.L k (evenHalf x)) (sys.L k (oddHalf x))) = _
        rw [← add_assoc (cert.h1.1 * _)]
      constructor
      · intro x
        rw [hStep x]
        refine add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_
        · exact mul_nonneg (le_of_lt hw1) (ih_ge _)
        · exact mul_nonneg (le_of_lt hw2) (ih_ge _)
        · exact hTermsEval_nonneg sys cert.W k ih_ge hwExtra _ _
        · exact sosEval_nonneg hDpos _
      · intro x hFx0
        rw [hStep x] at hFx0
        have t1ge := mul_nonneg (le_of_lt hw1) (ih_ge (vecAdd (vecSmul cert.h1.2.1 (evenHalf x)) (vecSmul cert.h1.2.2 (oddHalf x))))
        have t2ge := mul_nonneg (le_of_lt hw2) (ih_ge (vecAdd (vecSmul cert.h2.2.1 (evenHalf x)) (vecSmul cert.h2.2.2 (oddHalf x))))
        have tEge := hTermsEval_nonneg sys cert.W k ih_ge hwExtra (evenHalf x) (oddHalf x)
        have tDge := sosEval_nonneg hDpos (pairVec (sys.L k (evenHalf x)) (sys.L k (oddHalf x)))
        have hD0 : sosEval cert.deltaTerms (pairVec (sys.L k (evenHalf x)) (sys.L k (oddHalf x))) = 0 :=
          eq_zero_of_add_eq_zero_right (add_nonneg (add_nonneg t1ge t2ge) tEge) tDge hFx0
        have hH0 := eq_zero_of_add_eq_zero_left (add_nonneg (add_nonneg t1ge t2ge) tEge) tDge hFx0
        have h120 := eq_zero_of_add_eq_zero_left (add_nonneg t1ge t2ge) tEge hH0
        have h10 := eq_zero_of_add_eq_zero_left t1ge t2ge h120
        have h20 := eq_zero_of_add_eq_zero_right t1ge t2ge h120
        have hF10 : sys.F cert.W k (vecAdd (vecSmul cert.h1.2.1 (evenHalf x)) (vecSmul cert.h1.2.2 (oddHalf x))) = 0 :=
          (mul_eq_zero h10).resolve_left (fun h => by rw [h] at hw1; exact lt_irrefl 0 hw1)
        have hF20 : sys.F cert.W k (vecAdd (vecSmul cert.h2.2.1 (evenHalf x)) (vecSmul cert.h2.2.2 (oddHalf x))) = 0 :=
          (mul_eq_zero h20).resolve_left (fun h => by rw [h] at hw2; exact lt_irrefl 0 hw2)
        have hsupp01 : ∀ j : Fin (2 ^ k), j.val ≠ 0 → evenHalf x j = 0 ∧ oddHalf x j = 0 := fun j hj => by
          have hz1 : cert.h1.2.1 * evenHalf x j + cert.h1.2.2 * oddHalf x j = 0 := ih_ker _ hF10 j hj
          have hz2 : cert.h2.2.1 * evenHalf x j + cert.h2.2.2 * oddHalf x j = 0 := ih_ker _ hF20 j hj
          have hpair : ¬ ((∃ _ : Fin 1, evenHalf x j ≠ 0) ∨ (∃ _ : Fin 1, oddHalf x j ≠ 0)) := by
            intro hne
            rcases spanning_pair_nonzero hdet hne with ⟨_, hc⟩ | ⟨_, hc⟩
            · exact hc hz1
            · exact hc hz2
          constructor
          · exact Classical.byContradiction (fun hc => hpair (Or.inl ⟨⟨0, by decide⟩, hc⟩))
          · exact Classical.byContradiction (fun hc => hpair (Or.inr ⟨⟨0, by decide⟩, hc⟩))
        have hL0 := sys.L_of_support_zero heig k (evenHalf x) (fun j hj => (hsupp01 j hj).1)
        have hL1 := sys.L_of_support_zero heig k (oddHalf x) (fun j hj => (hsupp01 j hj).2)
        have huk0 : dotFin uk (pairVec (sys.L k (evenHalf x)) (sys.L k (oddHalf x))) = 0 :=
          sosEval_eq_zero_mem hDpos hD0 hkMem
        rw [hL0, hL1] at huk0
        let ca := powZHalf tau k * evenHalf x ⟨0, Nat.two_pow_pos k⟩
        let cb := powZHalf tau k * oddHalf x ⟨0, Nat.two_pow_pos k⟩
        have hdotDecomp : dotFin uk (pairVec (vecSmul ca sys.l0) (vecSmul cb sys.l0)) =
            ca * dotFin uk (pairVec sys.l0 (vecZero m)) +
            cb * dotFin uk (pairVec (vecZero m) sys.l0) := by
          unfold dotFin
          rw [sumFin_split_two, sumFin_split_two, sumFin_split_two]
          have hLzero : sumFin (fun i : Fin m => uk ⟨m + i.val, by omega⟩ * pairVec sys.l0 (vecZero m) ⟨m + i.val, by omega⟩) = 0 := by
            rw [sumFin_congr (fun i => by
              unfold pairVec vecZero
              have hn : ¬ (m + i.val < m) := by omega
              simp only [hn, ↓reduceDIte]
              exact mul_zero _)]
            exact sumFin_zero
          have hRzero : sumFin (fun i : Fin m => uk ⟨i.val, by omega⟩ * pairVec (vecZero m) sys.l0 ⟨i.val, by omega⟩) = 0 := by
            rw [sumFin_congr (fun i => by unfold pairVec vecZero; simp only [i.isLt, ↓reduceDIte]; exact mul_zero _)]
            exact sumFin_zero
          rw [hLzero, add_zero, hRzero, zero_add]
          congr 1
          · rw [← sumFin_mul_left]
            apply sumFin_congr; intro i
            unfold pairVec vecSmul
            simp only [i.isLt, ↓reduceDIte]
            rw [← mul_assoc, mul_comm (uk _) ca, mul_assoc]
          · rw [← sumFin_mul_left]
            apply sumFin_congr; intro i
            unfold pairVec vecSmul
            have hn : ¬ (m + i.val < m) := by omega
            have hs : m + i.val - m = i.val := by omega
            simp only [hn, hs, ↓reduceDIte]
            rw [← mul_assoc, mul_comm (uk _) cb, mul_assoc]
        have huk0' : dotFin uk (pairVec (vecSmul ca sys.l0) (vecSmul cb sys.l0)) = 0 := huk0
        rw [hdotDecomp, hkL, mul_zero, zero_add] at huk0'
        have hcb0 : cb = 0 := (mul_eq_zero huk0').resolve_right hkR
        have hx1_0 : oddHalf x ⟨0, Nat.two_pow_pos k⟩ = 0 :=
          (mul_eq_zero hcb0).resolve_left (powZHalf_ne_zero htau k)
        intro ⟨v, hv⟩ hvne
        dsimp only at hvne
        have hv2 : v < 2 * 2 ^ k := by rw [Nat.pow_succ] at hv; omega
        by_cases hp : v % 2 = 0
        · have hqne : v / 2 ≠ 0 := by omega
          have heq := (hsupp01 ⟨v / 2, by omega⟩ hqne).1
          unfold evenHalf at heq
          have hfin : (⟨2 * (v / 2), by rw [Nat.pow_succ]; omega⟩ : Fin (2 ^ (k + 1))) = ⟨v, hv⟩ :=
            Fin.ext (show 2 * (v / 2) = v by omega)
          rw [hfin] at heq; exact heq
        · by_cases hq0 : v / 2 = 0
          · unfold oddHalf at hx1_0
            have hfin : (⟨2 * 0 + 1, by rw [Nat.pow_succ]; omega⟩ : Fin (2 ^ (k + 1))) = ⟨v, hv⟩ :=
              Fin.ext (show 2 * 0 + 1 = v by omega)
            rw [hfin] at hx1_0; exact hx1_0
          · have heq := (hsupp01 ⟨v / 2, by omega⟩ hq0).2
            unfold oddHalf at heq
            have hfin : (⟨2 * (v / 2) + 1, by rw [Nat.pow_succ]; omega⟩ : Fin (2 ^ (k + 1))) = ⟨v, hv⟩ :=
              Fin.ext (show 2 * (v / 2) + 1 = v by omega)
            rw [hfin] at heq; exact heq
  intro k x hx
  have hFge : 0 ≤ sys.F cert.W k x := (hF_ind k).1 x
  have hSurplusGe : 0 ≤ quadForm (fun i j => Wtarget i j - cert.W i j) (sys.L k x) := by
    have heq : quadForm (fun i j => Wtarget i j - cert.W i j) (sys.L k x) =
               sosEval cert.surplusTerms (sys.L k x) := by
      rw [← quadForm_sosMatrix cert.surplusTerms]
      unfold quadForm quadBilin
      apply sumFin_congr; intro i
      apply sumFin_congr; intro j
      dsimp only
      rw [hSm i j]
    rw [heq]
    exact sosEval_nonneg hSpos _
  have hDecomp : sys.Q k x + quadForm Wtarget (sys.L k x) =
      sys.F cert.W k x + quadForm (fun i j => Wtarget i j - cert.W i j) (sys.L k x) := by
    unfold BQS.F BQS.BF BQS.Q quadForm
    rw [quadBilin_mat_sub, add_assoc, sub_eq_add_neg]
    calc sys.B k x x + quadBilin Wtarget (sys.L k x) (sys.L k x)
        = sys.B k x x + (quadBilin Wtarget (sys.L k x) (sys.L k x) + 0) := by rw [add_zero]
      _ = sys.B k x x + (quadBilin Wtarget (sys.L k x) (sys.L k x) +
            (quadBilin cert.W (sys.L k x) (sys.L k x) + -(quadBilin cert.W (sys.L k x) (sys.L k x)))) := by
            rw [add_neg_cancel]
      _ = sys.B k x x + (quadBilin cert.W (sys.L k x) (sys.L k x) +
            (quadBilin Wtarget (sys.L k x) (sys.L k x) + -(quadBilin cert.W (sys.L k x) (sys.L k x)))) := by
            congr 1
            rw [← add_assoc, add_comm (quadBilin Wtarget _ _) (quadBilin cert.W _ _), add_assoc]
  rw [hDecomp]
  by_cases hF0 : sys.F cert.W k x = 0
  · have hsupp := (hF_ind k).2 x hF0
    have hx0ne : x ⟨0, Nat.two_pow_pos k⟩ ≠ 0 := by
      rcases hx with ⟨i, hi⟩
      by_cases hi0 : i.val = 0
      · have heq : i = ⟨0, Nat.two_pow_pos k⟩ := Fin.ext hi0
        rw [← heq]; exact hi
      · exfalso; exact hi (hsupp i hi0)
    have hLx := sys.L_of_support_zero heig k x hsupp
    let sc := powZHalf tau k * x ⟨0, Nat.two_pow_pos k⟩
    have hscne : sc ≠ 0 := fun h => by
      rcases mul_eq_zero h with h1 | h2
      · exact powZHalf_ne_zero htau k h1
      · exact hx0ne h2
    have hSurpStrict : 0 < quadForm (fun i j => Wtarget i j - cert.W i j) (sys.L k x) := by
      rw [hLx]
      unfold quadForm
      rw [quadBilin_smul_left, quadBilin_smul_right, ← mul_assoc]
      exact mul_pos (sq_pos_of_ne_zero hscne) hSurpPos
    exact add_pos_of_nonneg_of_pos hFge hSurpStrict
  · have hFpos : 0 < sys.F cert.W k x := by
      refine Quotient.inductionOn (sys.F cert.W k x) (fun a ha hne => ?_) hFge hF0
      rw [nonneg_mk_iff] at ha
      rw [pos_mk_iff]
      have hm : a.mant ≠ 0 := by
        intro hm0; apply hne; apply Quotient.sound; show a.mant * 1 = 0 * _; simp [hm0]
      omega
    exact add_pos_of_pos_of_nonneg hFpos hSurplusGe


/-! ## Section 4: Pure-Silicon Bitwise Operators (2-Adic Valuation, Monna Map) & Exact Double-Sum Bridges -/

theorem sumFin_fin2 (f : Fin 2 → ZHalf) :
    sumFin f = f ⟨0, by decide⟩ + f ⟨1, by decide⟩ := by
  unfold sumFin
  simp only [sumFinAux, zero_add]
  rfl

theorem ofNat_pow2 (k : Nat) : Int.ofNat (2 ^ k) = Dyadic.pow2Int k := by
  induction k with
  | zero => rfl
  | succ m ih =>
    show Int.ofNat (2 ^ m * 2) = Dyadic.pow2Int m * 2
    rw [Int.ofNat_eq_natCast, Int.natCast_mul, ← Int.ofNat_eq_natCast, ih]
    rfl

theorem ofNat_add_int (a b : Nat) : Int.ofNat (a + b) = Int.ofNat a + Int.ofNat b := by
  simp only [Int.ofNat_eq_natCast, Int.natCast_add]

theorem neg_pos_iff {x : ZHalf} : 0 < -x ↔ x < 0 := by
  have h : 0 - x = -x := by rw [sub_eq_add_neg, zero_add]
  rw [← h, sub_pos_iff]

/-- Structurally recursive exact 2-adic valuation (trailing zero count `ctz`) — reduces inside kernel `decide`! -/
def v2NatAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n =>
    if n = 0 then 0
    else if n % 2 = 0 then 1 + v2NatAux fuel (n / 2)
    else 0

def v2Nat (n : Nat) : Nat := v2NatAux n n

theorem v2NatAux_ge : ∀ (fuel1 fuel2 n : Nat), n ≤ fuel1 → n ≤ fuel2 →
    v2NatAux fuel1 n = v2NatAux fuel2 n := by
  intro fuel1
  induction fuel1 with
  | zero =>
    intro fuel2 n h1 _
    have hn0 : n = 0 := by omega
    subst hn0
    cases fuel2 <;> simp [v2NatAux]
  | succ f1 ih =>
    intro fuel2 n h1 h2
    cases fuel2 with
    | zero =>
      have hn0 : n = 0 := by omega
      subst hn0; simp [v2NatAux]
    | succ f2 =>
      unfold v2NatAux
      by_cases hn0 : n = 0
      · simp [hn0]
      · by_cases hp : n % 2 = 0
        · simp only [hn0, hp, ↓reduceIte]
          congr 1
          exact ih f2 (n / 2) (by omega) (by omega)
        · simp [hn0, hp]

theorem v2Nat_zero : v2Nat 0 = 0 := rfl

theorem v2Nat_odd (n : Nat) (h : n % 2 = 1) : v2Nat n = 0 := by
  unfold v2Nat
  cases n with
  | zero => omega
  | succ m =>
    unfold v2NatAux
    have hmod : ¬ ((m + 1) % 2 = 0) := by omega
    simp [hmod]

theorem v2Nat_two_mul {n : Nat} (hn : n ≠ 0) : v2Nat (2 * n) = 1 + v2Nat n := by
  unfold v2Nat
  have hge : 1 ≤ 2 * n := by omega
  obtain ⟨f, hf⟩ : ∃ f, 2 * n = f + 1 := ⟨2 * n - 1, by omega⟩
  rw [hf]
  conv => lhs; unfold v2NatAux
  have hne : f + 1 ≠ 0 := by omega
  have hmod : (f + 1) % 2 = 0 := by omega
  have hdiv : (f + 1) / 2 = n := by omega
  simp only [hne, hmod, hdiv, ↓reduceIte]
  congr 1
  exact v2NatAux_ge f n n (by omega) (Nat.le_refl n)

/-- Exact absolute difference of natural numbers. -/
def absDiff (a b : Nat) : Nat := if a ≤ b then b - a else a - b

theorem absDiff_comm (a b : Nat) : absDiff a b = absDiff b a := by
  unfold absDiff; split <;> split <;> omega

theorem absDiff_self (a : Nat) : absDiff a a = 0 := by
  unfold absDiff; simp

theorem absDiff_two_mul (a b : Nat) : absDiff (2 * a) (2 * b) = 2 * absDiff a b := by
  unfold absDiff; split <;> split <;> omega

theorem absDiff_two_mul_add_one (a b : Nat) : absDiff (2 * a + 1) (2 * b + 1) = 2 * absDiff a b := by
  unfold absDiff; split <;> split <;> omega

theorem absDiff_even_odd_mod2 (a b : Nat) : absDiff (2 * a) (2 * b + 1) % 2 = 1 := by
  unfold absDiff; split <;> omega

theorem absDiff_odd_even_mod2 (a b : Nat) : absDiff (2 * a + 1) (2 * b) % 2 = 1 := by
  unfold absDiff; split <;> omega

/-- Exact `k`-bit reversal (pure-silicon 2-adic Monna map numerator). -/
def bitrev : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, i => (i % 2) * (2 ^ k) + bitrev k (i / 2)

theorem bitrev_lt (k i : Nat) : bitrev k i < 2 ^ k := by
  induction k generalizing i with
  | zero => simp [bitrev]
  | succ k ih =>
    change (i % 2) * (2 ^ k) + bitrev k (i / 2) < 2 ^ (k + 1)
    have h := ih (i / 2)
    have hmod : i % 2 = 0 ∨ i % 2 = 1 := by omega
    rw [Nat.pow_succ]
    rcases hmod with h0 | h1
    · rw [h0]; omega
    · rw [h1]; omega

theorem bitrev_two_mul (k i : Nat) : bitrev (k + 1) (2 * i) = bitrev k i := by
  change (2 * i % 2) * (2 ^ k) + bitrev k (2 * i / 2) = bitrev k i
  have h1 : 2 * i % 2 = 0 := by omega
  have h2 : 2 * i / 2 = i := by omega
  rw [h1, h2]; simp

theorem bitrev_two_mul_add_one (k i : Nat) : bitrev (k + 1) (2 * i + 1) = 2 ^ k + bitrev k i := by
  change ((2 * i + 1) % 2) * (2 ^ k) + bitrev k ((2 * i + 1) / 2) = 2 ^ k + bitrev k i
  have h1 : (2 * i + 1) % 2 = 1 := by omega
  have h2 : (2 * i + 1) / 2 = i := by omega
  rw [h1, h2]; simp

/-- Exact dyadic Monna coordinate `ρ_k(i) = bitrev k i / 2^k ∈ Z[1/2]`. -/
def monnaCoord (k i : Nat) : ZHalf := dyad (Int.ofNat (bitrev k i)) k

theorem monnaCoord_two_mul (k i : Nat) :
    monnaCoord (k + 1) (2 * i) = dyad 1 1 * monnaCoord k i := by
  unfold monnaCoord
  rw [bitrev_two_mul]
  apply Quotient.sound
  show Int.ofNat (bitrev k i) * Dyadic.pow2Int (1 + k) =
       (1 * Int.ofNat (bitrev k i)) * Dyadic.pow2Int (k + 1)
  rw [Int.one_mul, Nat.add_comm 1 k]

theorem monnaCoord_two_mul_add_one (k i : Nat) :
    monnaCoord (k + 1) (2 * i + 1) = dyad 1 1 + dyad 1 1 * monnaCoord k i := by
  unfold monnaCoord
  rw [bitrev_two_mul_add_one]
  change Quotient.mk Dyadic.instSetoid ⟨Int.ofNat (2 ^ k + bitrev k i), k + 1⟩ =
         Quotient.mk Dyadic.instSetoid ⟨1, 1⟩ +
         Quotient.mk Dyadic.instSetoid ⟨1 * Int.ofNat (bitrev k i), 1 + k⟩
  rw [ZHalf.mk_add_eq]
  apply Quotient.sound
  show Int.ofNat (2 ^ k + bitrev k i) * Dyadic.pow2Int (1 + (1 + k)) =
       (1 * Dyadic.pow2Int (1 + k) + 1 * Int.ofNat (bitrev k i) * Dyadic.pow2Int 1) * Dyadic.pow2Int (k + 1)
  rw [ofNat_add_int, ofNat_pow2, Int.one_mul, Int.one_mul]
  have h2 : Dyadic.pow2Int 1 = 2 := rfl
  have h1k : Dyadic.pow2Int (1 + k) = 2 * Dyadic.pow2Int k := by rw [Dyadic.pow2Int_add, h2]
  have hk1 : Dyadic.pow2Int (k + 1) = 2 * Dyadic.pow2Int k := by rw [Nat.add_comm, h1k]
  have h11k : Dyadic.pow2Int (1 + (1 + k)) = 2 * (2 * Dyadic.pow2Int k) := by rw [Dyadic.pow2Int_add, h2, h1k]
  rw [h11k, h1k, hk1, h2, Int.add_mul, Int.add_mul]
  congr 1
  · calc Dyadic.pow2Int k * (2 * (2 * Dyadic.pow2Int k))
        = (Dyadic.pow2Int k * 2) * (2 * Dyadic.pow2Int k) := (Int.mul_assoc _ _ _).symm
      _ = (2 * Dyadic.pow2Int k) * (2 * Dyadic.pow2Int k) := by rw [Int.mul_comm (Dyadic.pow2Int k) 2]
  · calc Int.ofNat (bitrev k i) * (2 * (2 * Dyadic.pow2Int k))
        = (Int.ofNat (bitrev k i) * 2) * (2 * Dyadic.pow2Int k) := (Int.mul_assoc _ _ _).symm

/-- Explicit normalized mean functional `μ_k(x) = 2^{-k} ∑_i x_i`. -/
def muForm (k : Nat) (x : Fin (2 ^ k) → ZHalf) : ZHalf :=
  pow2Neg k * sumFin x

/-- Explicit normalized Monna-moment functional `ν_k(x) = 2^{-k} ∑_i ρ_k(i) x_i`. -/
def nuForm (k : Nat) (x : Fin (2 ^ k) → ZHalf) : ZHalf :=
  pow2Neg k * sumFin (fun i => monnaCoord k i.val * x i)

theorem muForm_zero (x : Fin (2 ^ 0) → ZHalf) : muForm 0 x = x ⟨0, by decide⟩ := by
  unfold muForm
  have h1 : pow2Neg 0 = 1 := rfl
  rw [h1, one_mul, sumFin_fin1]

theorem nuForm_zero (x : Fin (2 ^ 0) → ZHalf) : nuForm 0 x = 0 := by
  unfold nuForm monnaCoord
  rw [sumFin_fin1]
  have h0 : dyad (Int.ofNat (bitrev 0 0)) 0 = 0 := by decide
  rw [h0, zero_mul, mul_zero]

theorem muForm_succ (k : Nat) (x : Fin (2 ^ (k + 1)) → ZHalf) :
    muForm (k + 1) x = dyad 1 1 * muForm k (evenHalf x) + dyad 1 1 * muForm k (oddHalf x) := by
  unfold muForm
  rw [sumFin_pow2_succ, show pow2Neg (k + 1) = dyad 1 1 * pow2Neg k from by
    rw [show k + 1 = 1 + k from Nat.add_comm k 1]; exact pow2Neg_add 1 k]
  rw [mul_add, mul_assoc, mul_assoc]
  rfl

theorem nuForm_succ (k : Nat) (x : Fin (2 ^ (k + 1)) → ZHalf) :
    nuForm (k + 1) x =
      dyad 1 2 * nuForm k (evenHalf x) +
      dyad 1 2 * muForm k (oddHalf x) +
      dyad 1 2 * nuForm k (oddHalf x) := by
  unfold nuForm muForm
  rw [sumFin_pow2_succ]
  have hE : sumFin (fun i : Fin (2 ^ k) => monnaCoord (k + 1) (2 * i.val) * evenHalf x i) =
            dyad 1 1 * sumFin (fun i : Fin (2 ^ k) => monnaCoord k i.val * evenHalf x i) := by
    rw [← sumFin_mul_left]
    apply sumFin_congr; intro i
    rw [monnaCoord_two_mul, mul_assoc]
  have hO : sumFin (fun i : Fin (2 ^ k) => monnaCoord (k + 1) (2 * i.val + 1) * oddHalf x i) =
            dyad 1 1 * sumFin (oddHalf x) +
            dyad 1 1 * sumFin (fun i : Fin (2 ^ k) => monnaCoord k i.val * oddHalf x i) := by
    rw [← sumFin_mul_left, ← sumFin_mul_left, ← sumFin_add]
    apply sumFin_congr; intro i
    rw [monnaCoord_two_mul_add_one, add_mul, mul_assoc]
  change pow2Neg (k + 1) * (sumFin (fun i : Fin (2 ^ k) => monnaCoord (k + 1) (2 * i.val) * evenHalf x i) +
                            sumFin (fun i : Fin (2 ^ k) => monnaCoord (k + 1) (2 * i.val + 1) * oddHalf x i)) = _
  rw [hE, hO]
  have hp : pow2Neg (k + 1) = dyad 1 1 * pow2Neg k := by
    rw [show k + 1 = 1 + k from Nat.add_comm k 1]; exact pow2Neg_add 1 k
  have hq : dyad 1 1 * dyad 1 1 = dyad 1 2 := by decide
  rw [hp, mul_add, mul_add, ← add_assoc]
  have rearr : ∀ a : ZHalf, (dyad 1 1 * pow2Neg k) * (dyad 1 1 * a) = dyad 1 2 * (pow2Neg k * a) := fun a => by
    calc (dyad 1 1 * pow2Neg k) * (dyad 1 1 * a)
        = (dyad 1 1 * (pow2Neg k * dyad 1 1)) * a := by simp [mul_assoc]
      _ = (dyad 1 1 * (dyad 1 1 * pow2Neg k)) * a := by rw [mul_comm (pow2Neg k) (dyad 1 1)]
      _ = (dyad 1 1 * dyad 1 1) * (pow2Neg k * a) := by simp [mul_assoc]
      _ = dyad 1 2 * (pow2Neg k * a) := by rw [hq]
  rw [rearr, rearr, rearr]

/-- Explicit double-sum 2-adic Riesz form:
    `R_k^{(s)}(x) = 2^{-2k} ∑_{i ≠ j} 2^{-s * v_2(i ⊕ j)} x_i x_j`. -/
def riesz2AdicKernel (s i j : Nat) : ZHalf :=
  if i = j then 0 else pow2Neg (s * v2Nat (i ^^^ j))

def riesz2AdicForm (s k : Nat) (x : Fin (2 ^ k) → ZHalf) : ZHalf :=
  pow2Neg (2 * k) * sumFin (fun i => sumFin (fun j => riesz2AdicKernel s i.val j.val * x i * x j))

theorem riesz2AdicForm_zero (s : Nat) (x : Fin (2 ^ 0) → ZHalf) :
    riesz2AdicForm s 0 x = 0 := by
  unfold riesz2AdicForm riesz2AdicKernel
  rw [sumFin_fin1, sumFin_fin1]
  simp [zero_mul, mul_zero]

/-- Explicit double-sum Archimedean Monna distance form:
    `A_k(x) = 2^{-2k} ∑_{i, j} |ρ_k(i) - ρ_k(j)| x_i x_j`. -/
def monnaArchKernel (k i j : Nat) : ZHalf :=
  dyad (Int.ofNat (absDiff (bitrev k i) (bitrev k j))) k

def monnaArchForm (k : Nat) (x : Fin (2 ^ k) → ZHalf) : ZHalf :=
  pow2Neg (2 * k) * sumFin (fun i => sumFin (fun j => monnaArchKernel k i.val j.val * x i * x j))

theorem monnaArchForm_zero (x : Fin (2 ^ 0) → ZHalf) : monnaArchForm 0 x = 0 := by
  unfold monnaArchForm monnaArchKernel
  rw [sumFin_fin1, sumFin_fin1]
  have h0 : dyad (Int.ofNat (absDiff (bitrev 0 0) (bitrev 0 0))) 0 = 0 := by decide
  rw [h0, zero_mul, zero_mul, mul_zero]

theorem monnaArchKernel_even_odd (k a b : Nat) :
    monnaArchKernel (k + 1) (2 * a) (2 * b + 1) =
    dyad 1 1 + dyad 1 1 * monnaCoord k b - dyad 1 1 * monnaCoord k a := by
  unfold monnaArchKernel monnaCoord
  rw [bitrev_two_mul, bitrev_two_mul_add_one]
  have hlt : bitrev k a < 2 ^ k := bitrev_lt k a
  have hle : bitrev k a ≤ 2 ^ k + bitrev k b := by omega
  have hdiff : absDiff (bitrev k a) (2 ^ k + bitrev k b) = 2 ^ k + bitrev k b - bitrev k a := by
    unfold absDiff; simp [hle]
  rw [hdiff]
  have h1 : dyad (Int.ofNat (2 ^ k + bitrev k b - bitrev k a)) (k + 1) +
            dyad 1 1 * dyad (Int.ofNat (bitrev k a)) k =
            dyad 1 1 + dyad 1 1 * dyad (Int.ofNat (bitrev k b)) k := by
    have hadd_nat : (2 ^ k + bitrev k b - bitrev k a) + bitrev k a = 2 ^ k + bitrev k b := by omega
    have hL : dyad (Int.ofNat (2 ^ k + bitrev k b - bitrev k a)) (k + 1) +
              dyad 1 1 * dyad (Int.ofNat (bitrev k a)) k =
              dyad (Int.ofNat (2 ^ k + bitrev k b)) (k + 1) := by
      change Quotient.mk Dyadic.instSetoid ⟨Int.ofNat (2 ^ k + bitrev k b - bitrev k a), k + 1⟩ +
             Quotient.mk Dyadic.instSetoid ⟨1 * Int.ofNat (bitrev k a), 1 + k⟩ = _
      rw [ZHalf.mk_add_eq]
      apply Quotient.sound
      show (Int.ofNat (2 ^ k + bitrev k b - bitrev k a) * Dyadic.pow2Int (1 + k) +
            1 * Int.ofNat (bitrev k a) * Dyadic.pow2Int (k + 1)) * Dyadic.pow2Int (k + 1) =
           Int.ofNat (2 ^ k + bitrev k b) * Dyadic.pow2Int ((k + 1) + (1 + k))
      rw [Int.one_mul, Nat.add_comm 1 k, ← Int.add_mul, ← ofNat_add_int, hadd_nat,
          Int.mul_assoc, ← Dyadic.pow2Int_add]
    rw [hL]
    have hR := monnaCoord_two_mul_add_one k b
    unfold monnaCoord at hR
    rw [bitrev_two_mul_add_one] at hR
    exact hR
  have hsub : ∀ x y z : ZHalf, x + y = z → x = z - y := fun x y z h => by
    calc x = x + 0 := (add_zero x).symm
      _ = x + (y + (-y)) := by rw [add_neg_cancel]
      _ = (x + y) + (-y) := (add_assoc x y (-y)).symm
      _ = z - y := by rw [h]; rfl
  exact hsub _ _ _ h1

theorem monnaArchForm_succ (k : Nat) (x : Fin (2 ^ (k + 1)) → ZHalf) :
    monnaArchForm (k + 1) x =
      dyad 1 3 * monnaArchForm k (evenHalf x) +
      dyad 1 3 * monnaArchForm k (oddHalf x) +
      dyad 1 2 * muForm k (evenHalf x) * muForm k (oddHalf x) +
      dyad 1 2 * muForm k (evenHalf x) * nuForm k (oddHalf x) -
      dyad 1 2 * nuForm k (evenHalf x) * muForm k (oddHalf x) := by
  unfold monnaArchForm
  rw [sumFin_pow2_succ]
  have hinner : ∀ (f : Fin (2 ^ (k + 1)) → ZHalf),
      sumFin f = sumFin (fun j : Fin (2 ^ k) => f ⟨2 * j.val, by have := j.isLt; rw [Nat.pow_succ]; omega⟩) +
                 sumFin (fun j : Fin (2 ^ k) => f ⟨2 * j.val + 1, by have := j.isLt; rw [Nat.pow_succ]; omega⟩) :=
    fun f => sumFin_pow2_succ f
  rw [sumFin_congr (fun i => hinner _), sumFin_congr (fun i => hinner _), sumFin_add, sumFin_add]
  have hEE : ∀ a b : Nat, monnaArchKernel (k + 1) (2 * a) (2 * b) = dyad 1 1 * monnaArchKernel k a b := fun a b => by
    unfold monnaArchKernel
    rw [bitrev_two_mul, bitrev_two_mul]
    apply Quotient.sound
    show Int.ofNat (absDiff (bitrev k a) (bitrev k b)) * Dyadic.pow2Int (1 + k) =
         (1 * Int.ofNat (absDiff (bitrev k a) (bitrev k b))) * Dyadic.pow2Int (k + 1)
    rw [Int.one_mul, Nat.add_comm 1 k]
  have hOO : ∀ a b : Nat, monnaArchKernel (k + 1) (2 * a + 1) (2 * b + 1) = dyad 1 1 * monnaArchKernel k a b := fun a b => by
    unfold monnaArchKernel
    rw [bitrev_two_mul_add_one, bitrev_two_mul_add_one]
    have hd : absDiff (2 ^ k + bitrev k a) (2 ^ k + bitrev k b) = absDiff (bitrev k a) (bitrev k b) := by
      unfold absDiff; split <;> split <;> omega
    rw [hd]
    apply Quotient.sound
    show Int.ofNat (absDiff (bitrev k a) (bitrev k b)) * Dyadic.pow2Int (1 + k) =
         (1 * Int.ofNat (absDiff (bitrev k a) (bitrev k b))) * Dyadic.pow2Int (k + 1)
    rw [Int.one_mul, Nat.add_comm 1 k]
  have hOE : ∀ a b : Nat, monnaArchKernel (k + 1) (2 * a + 1) (2 * b) =
                          monnaArchKernel (k + 1) (2 * b) (2 * a + 1) := fun a b => by
    unfold monnaArchKernel; rw [absDiff_comm]
  have sEE : sumFin (fun i : Fin (2 ^ k) => sumFin (fun j : Fin (2 ^ k) =>
               monnaArchKernel (k + 1) (2 * i.val) (2 * j.val) * evenHalf x i * evenHalf x j)) =
             dyad 1 1 * sumFin (fun i : Fin (2 ^ k) => sumFin (fun j : Fin (2 ^ k) =>
               monnaArchKernel k i.val j.val * evenHalf x i * evenHalf x j)) := by
    rw [← sumFin_mul_left]; apply sumFin_congr; intro i
    rw [← sumFin_mul_left]; apply sumFin_congr; intro j
    rw [hEE i.val j.val, mul_assoc (dyad 1 1), mul_assoc (dyad 1 1)]
  have sOO : sumFin (fun i : Fin (2 ^ k) => sumFin (fun j : Fin (2 ^ k) =>
               monnaArchKernel (k + 1) (2 * i.val + 1) (2 * j.val + 1) * oddHalf x i * oddHalf x j)) =
             dyad 1 1 * sumFin (fun i : Fin (2 ^ k) => sumFin (fun j : Fin (2 ^ k) =>
               monnaArchKernel k i.val j.val * oddHalf x i * oddHalf x j)) := by
    rw [← sumFin_mul_left]; apply sumFin_congr; intro i
    rw [← sumFin_mul_left]; apply sumFin_congr; intro j
    rw [hOO i.val j.val, mul_assoc (dyad 1 1), mul_assoc (dyad 1 1)]
  let S0 := sumFin (evenHalf x)
  let S1 := sumFin (oddHalf x)
  let T0 := sumFin (fun i : Fin (2 ^ k) => monnaCoord k i.val * evenHalf x i)
  let T1 := sumFin (fun i : Fin (2 ^ k) => monnaCoord k i.val * oddHalf x i)
  have sEO : sumFin (fun i : Fin (2 ^ k) => sumFin (fun j : Fin (2 ^ k) =>
               monnaArchKernel (k + 1) (2 * i.val) (2 * j.val + 1) * evenHalf x i * oddHalf x j)) =
             dyad 1 1 * (S0 * S1 + S0 * T1 - T0 * S1) := by
    have hterm : ∀ i j : Fin (2 ^ k),
        monnaArchKernel (k + 1) (2 * i.val) (2 * j.val + 1) * evenHalf x i * oddHalf x j =
        dyad 1 1 * (evenHalf x i * oddHalf x j + evenHalf x i * (monnaCoord k j.val * oddHalf x j) -
                    (monnaCoord k i.val * evenHalf x i) * oddHalf x j) := fun i j => by
      rw [monnaArchKernel_even_odd]
      simp only [sub_mul, add_mul, mul_sub, mul_add]
      congr 1
      · congr 1
        · exact mul_assoc _ _ _
        · calc dyad 1 1 * monnaCoord k j.val * evenHalf x i * oddHalf x j
              = dyad 1 1 * (monnaCoord k j.val * evenHalf x i * oddHalf x j) := by simp [mul_assoc]
            _ = dyad 1 1 * (evenHalf x i * monnaCoord k j.val * oddHalf x j) := by rw [mul_comm (monnaCoord k j.val)]
            _ = dyad 1 1 * (evenHalf x i * (monnaCoord k j.val * oddHalf x j)) := by rw [mul_assoc (evenHalf x i)]
      · simp [mul_assoc]
    rw [sumFin_congr (fun i => sumFin_congr (fun j => hterm i j))]
    rw [sumFin_congr (fun i => sumFin_mul_left (dyad 1 1) _), sumFin_mul_left]
    congr 1
    rw [sumFin_congr (fun i => sumFin_sub _ _), sumFin_sub,
        sumFin_congr (fun i => sumFin_add _ _), sumFin_add]
    congr 1
    · congr 1
      · rw [sumFin_congr (fun i => sumFin_mul_left (evenHalf x i) _), sumFin_mul_right]
      · rw [sumFin_congr (fun i => sumFin_mul_left (evenHalf x i) _), sumFin_mul_right]
    · rw [sumFin_congr (fun i => sumFin_mul_left (monnaCoord k i.val * evenHalf x i) _), sumFin_mul_right]
  have sOE : sumFin (fun i : Fin (2 ^ k) => sumFin (fun j : Fin (2 ^ k) =>
               monnaArchKernel (k + 1) (2 * i.val + 1) (2 * j.val) * oddHalf x i * evenHalf x j)) =
             dyad 1 1 * (S0 * S1 + S0 * T1 - T0 * S1) := by
    rw [sumFin_swap]
    have hsw : ∀ i j : Fin (2 ^ k),
        monnaArchKernel (k + 1) (2 * j.val + 1) (2 * i.val) * oddHalf x j * evenHalf x i =
        monnaArchKernel (k + 1) (2 * i.val) (2 * j.val + 1) * evenHalf x i * oddHalf x j := fun i j => by
      rw [hOE j.val i.val, mul_assoc, mul_comm (oddHalf x j) (evenHalf x i), ← mul_assoc]
    rw [sumFin_congr (fun i => sumFin_congr (fun j => hsw i j))]
    exact sEO
  change pow2Neg (2 * (k + 1)) *
    ((sumFin (fun i : Fin (2 ^ k) => sumFin (fun j : Fin (2 ^ k) =>
        monnaArchKernel (k + 1) (2 * i.val) (2 * j.val) * evenHalf x i * evenHalf x j)) +
      sumFin (fun i : Fin (2 ^ k) => sumFin (fun j : Fin (2 ^ k) =>
        monnaArchKernel (k + 1) (2 * i.val) (2 * j.val + 1) * evenHalf x i * oddHalf x j))) +
     (sumFin (fun i : Fin (2 ^ k) => sumFin (fun j : Fin (2 ^ k) =>
        monnaArchKernel (k + 1) (2 * i.val + 1) (2 * j.val) * oddHalf x i * evenHalf x j)) +
      sumFin (fun i : Fin (2 ^ k) => sumFin (fun j : Fin (2 ^ k) =>
        monnaArchKernel (k + 1) (2 * i.val + 1) (2 * j.val + 1) * oddHalf x i * oddHalf x j)))) = _
  rw [sEE, sOO, sEO, sOE]
  have hrearr : ∀ a b c : ZHalf, (a + c) + (c + b) = (a + b) + (c + c) := fun a b c => by
    rw [add_comm c b]; exact add_four_swap a c b c
  rw [hrearr]
  have hp2 : pow2Neg (2 * (k + 1)) = dyad 1 2 * pow2Neg (2 * k) := by
    rw [show 2 * (k + 1) = 2 + 2 * k by omega]; exact pow2Neg_add 2 (2 * k)
  have h13 : dyad 1 2 * dyad 1 1 = dyad 1 3 := by decide
  have h11 : dyad 1 1 + dyad 1 1 = 1 := by decide
  have hpk : pow2Neg (2 * k) = pow2Neg k * pow2Neg k := by
    rw [show 2 * k = k + k by omega]; exact pow2Neg_add k k
  unfold muForm nuForm
  rw [hp2, mul_add, mul_add]
  have hsc : ∀ A : ZHalf, (dyad 1 2 * pow2Neg (2 * k)) * (dyad 1 1 * A) =
             dyad 1 3 * (pow2Neg (2 * k) * A) := fun A => by
    calc (dyad 1 2 * pow2Neg (2 * k)) * (dyad 1 1 * A)
        = (dyad 1 2 * (pow2Neg (2 * k) * dyad 1 1)) * A := by simp [mul_assoc]
      _ = (dyad 1 2 * (dyad 1 1 * pow2Neg (2 * k))) * A := by rw [mul_comm (pow2Neg (2 * k))]
      _ = (dyad 1 2 * dyad 1 1) * (pow2Neg (2 * k) * A) := by simp [mul_assoc]
      _ = dyad 1 3 * (pow2Neg (2 * k) * A) := by rw [h13]
  have hcr : ∀ A B : ZHalf, (dyad 1 2 * pow2Neg (2 * k)) * (A * B) =
             dyad 1 2 * (pow2Neg k * A) * (pow2Neg k * B) := fun A B => by
    rw [hpk]
    calc (dyad 1 2 * (pow2Neg k * pow2Neg k)) * (A * B)
        = dyad 1 2 * (pow2Neg k * (pow2Neg k * A) * B) := by simp [mul_assoc]
      _ = dyad 1 2 * (pow2Neg k * (A * pow2Neg k) * B) := by rw [mul_comm (pow2Neg k) A]
      _ = dyad 1 2 * (pow2Neg k * A) * (pow2Neg k * B) := by simp [mul_assoc]
  rw [hsc, hsc]
  have hdbl : dyad 1 1 * (S0 * S1 + S0 * T1 - T0 * S1) + dyad 1 1 * (S0 * S1 + S0 * T1 - T0 * S1) =
              S0 * S1 + S0 * T1 - T0 * S1 := by
    rw [← add_mul, h11, one_mul]
  rw [hdbl, mul_sub, mul_add, hcr S0 S1, hcr S0 T1, hcr T0 S1]
  rw [sub_eq_add_neg, sub_eq_add_neg, ← add_assoc, ← add_assoc]

/-! ## Section 5: Four Concrete Infinite Theorems + Infinite Sharpness + Structural Witnesses -/

def vec1 (a : ZHalf) : Fin 1 → ZHalf := fun _ => a
def vec2 (a b : ZHalf) : Fin 2 → ZHalf := fun i => if i.val = 0 then a else b
def vec4 (a b c d : ZHalf) : Fin 4 → ZHalf := fun i =>
  match i.val with
  | 0 => a | 1 => b | 2 => c | _ => d

def mat1 (a : ZHalf) : Fin 1 → Fin 1 → ZHalf := fun _ _ => a
def mat2 (a b c d : ZHalf) : Fin 2 → Fin 2 → ZHalf := fun i j =>
  match i.val, j.val with
  | 0, 0 => a | 0, 1 => b
  | 1, 0 => c | _, _ => d

def mat4 (r0 r1 r2 r3 : Fin 4 → ZHalf) : Fin 4 → Fin 4 → ZHalf := fun i =>
  match i.val with
  | 0 => r0 | 1 => r1 | 2 => r2 | _ => r3

theorem quadForm_fin2 (M : Fin 2 → Fin 2 → ZHalf) (v : Fin 2 → ZHalf) :
    quadForm M v =
      (M ⟨0, by decide⟩ ⟨0, by decide⟩ * v ⟨0, by decide⟩ * v ⟨0, by decide⟩ +
       M ⟨0, by decide⟩ ⟨1, by decide⟩ * v ⟨0, by decide⟩ * v ⟨1, by decide⟩) +
      (M ⟨1, by decide⟩ ⟨0, by decide⟩ * v ⟨1, by decide⟩ * v ⟨0, by decide⟩ +
       M ⟨1, by decide⟩ ⟨1, by decide⟩ * v ⟨1, by decide⟩ * v ⟨1, by decide⟩) := by
  unfold quadForm quadBilin
  rw [sumFin_fin2]
  rw [sumFin_fin2, sumFin_fin2]

theorem quadForm_fin4 (M : Fin 4 → Fin 4 → ZHalf) (v : Fin 4 → ZHalf) :
    quadForm M v =
      (M ⟨0, by decide⟩ ⟨0, by decide⟩ * v ⟨0, by decide⟩ * v ⟨0, by decide⟩ +
       M ⟨0, by decide⟩ ⟨1, by decide⟩ * v ⟨0, by decide⟩ * v ⟨1, by decide⟩ +
       M ⟨0, by decide⟩ ⟨2, by decide⟩ * v ⟨0, by decide⟩ * v ⟨2, by decide⟩ +
       M ⟨0, by decide⟩ ⟨3, by decide⟩ * v ⟨0, by decide⟩ * v ⟨3, by decide⟩) +
      (M ⟨1, by decide⟩ ⟨0, by decide⟩ * v ⟨1, by decide⟩ * v ⟨0, by decide⟩ +
       M ⟨1, by decide⟩ ⟨1, by decide⟩ * v ⟨1, by decide⟩ * v ⟨1, by decide⟩ +
       M ⟨1, by decide⟩ ⟨2, by decide⟩ * v ⟨1, by decide⟩ * v ⟨2, by decide⟩ +
       M ⟨1, by decide⟩ ⟨3, by decide⟩ * v ⟨1, by decide⟩ * v ⟨3, by decide⟩) +
      (M ⟨2, by decide⟩ ⟨0, by decide⟩ * v ⟨2, by decide⟩ * v ⟨0, by decide⟩ +
       M ⟨2, by decide⟩ ⟨1, by decide⟩ * v ⟨2, by decide⟩ * v ⟨1, by decide⟩ +
       M ⟨2, by decide⟩ ⟨2, by decide⟩ * v ⟨2, by decide⟩ * v ⟨2, by decide⟩ +
       M ⟨2, by decide⟩ ⟨3, by decide⟩ * v ⟨2, by decide⟩ * v ⟨3, by decide⟩) +
      (M ⟨3, by decide⟩ ⟨0, by decide⟩ * v ⟨3, by decide⟩ * v ⟨0, by decide⟩ +
       M ⟨3, by decide⟩ ⟨1, by decide⟩ * v ⟨3, by decide⟩ * v ⟨1, by decide⟩ +
       M ⟨3, by decide⟩ ⟨2, by decide⟩ * v ⟨3, by decide⟩ * v ⟨2, by decide⟩ +
       M ⟨3, by decide⟩ ⟨3, by decide⟩ * v ⟨3, by decide⟩ * v ⟨3, by decide⟩) := by
  unfold quadForm quadBilin sumFin
  simp only [sumFinAux, zero_add]
  rfl

/-! ### THEOREM 1: Infinite 2-Parameter Sharp 2-Adic Riesz Positivity Family (∀ s ≥ 1, ∀ k ≥ 0, ∀ x ≠ 0) -/

def sysRiesz (s : Nat) : BQS 1 where
  q0  := 0
  l0  := vec1 1
  h00 := pow2Neg (s + 2)
  h01 := 0
  h11 := pow2Neg (s + 2)
  U0  := mat1 (dyad 1 1)
  U1  := mat1 (dyad 1 1)
  C   := mat2 0 (dyad (-(Dyadic.pow2Int (s + 1) - 1)) 2)
              (dyad (-(Dyadic.pow2Int (s + 1) - 1)) 2) 0

def WRiesz (s : Nat) : Fin 1 → Fin 1 → ZHalf := mat1 (pow2Nat s)

def certRiesz (s : Nat) : PDCert 1 where
  W            := WRiesz s
  h1           := (pow2Neg (s + 2), 1, 0)
  h2           := (pow2Neg (s + 2), 0, 1)
  hExtra       := []
  deltaTerms   := [(dyad (Dyadic.pow2Int s - 1) 2, vec2 1 (-1))]
  surplusTerms := []

theorem sysRiesz_L_eq (s k : Nat) (x : Fin (2 ^ k) → ZHalf) :
    (sysRiesz s).L k x ⟨0, by decide⟩ = muForm k x := by
  induction k with
  | zero =>
    unfold BQS.L sysRiesz vec1
    rw [muForm_zero, one_mul]
  | succ k ih =>
    unfold BQS.L
    rw [sumFin_fin1, sumFin_fin1, ih (evenHalf x), ih (oddHalf x), muForm_succ]
    rfl

/-- Parametric certificate validity for ALL `s ≥ 1`! -/
theorem checkStrictPD_riesz_all (s : Nat) (hs : 1 ≤ s) :
    checkStrictPD (sysRiesz s) (WRiesz s) (certRiesz s) = true := by
  unfold checkStrictPD checkCoreCert
  have h1 : isSymmMat (sysRiesz s).C = true := by
    unfold isSymmMat; simp only [List.all_eq_true, decide_eq_true_eq]
    intro i _ j _
    match i, j with
    | ⟨0, _⟩, ⟨0, _⟩ => rfl
    | ⟨0, _⟩, ⟨1, _⟩ => rfl
    | ⟨1, _⟩, ⟨0, _⟩ => rfl
    | ⟨1, _⟩, ⟨1, _⟩ => rfl
  have h2 : isSymmMat (certRiesz s).W = true := by
    unfold isSymmMat; simp only [List.all_eq_true, decide_eq_true_eq]
    intro i _ j _; rfl
  have h2t : isSymmMat (WRiesz s) = true := h2
  have h3 : allPosWeights ((certRiesz s).h1 :: (certRiesz s).h2 :: (certRiesz s).hExtra) = true := by
    unfold allPosWeights certRiesz
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨pow2Neg_pos (s + 2), pow2Neg_pos (s + 2)⟩
  have hdet : decide ((certRiesz s).h1.2.1 * (certRiesz s).h2.2.2 - (certRiesz s).h1.2.2 * (certRiesz s).h2.2.1 ≠ 0) = true := by
    rw [decide_eq_true_eq]
    show (1 : ZHalf) * 1 - 0 * 0 ≠ 0
    decide
  have hh00 : decide ((hTermsSum ((certRiesz s).h1 :: (certRiesz s).h2 :: (certRiesz s).hExtra)).1 = (sysRiesz s).h00) = true := by
    rw [decide_eq_true_eq]
    unfold hTermsSum certRiesz sysRiesz
    simp only [List.foldr, mul_one, mul_zero, add_zero]
  have hh01 : decide ((hTermsSum ((certRiesz s).h1 :: (certRiesz s).h2 :: (certRiesz s).hExtra)).2.1 = (sysRiesz s).h01) = true := by
    rw [decide_eq_true_eq]
    unfold hTermsSum certRiesz sysRiesz
    simp only [List.foldr, mul_one, mul_zero, add_zero]
  have hh11 : decide ((hTermsSum ((certRiesz s).h1 :: (certRiesz s).h2 :: (certRiesz s).hExtra)).2.2 = (sysRiesz s).h11) = true := by
    rw [decide_eq_true_eq]
    unfold hTermsSum certRiesz sysRiesz
    simp only [List.foldr, mul_one, mul_zero, add_zero, zero_add]
  have hDpos : allPosWeights (certRiesz s).deltaTerms = true := by
    unfold allPosWeights certRiesz
    simp only [List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq]
    rw [dyad, pos_mk_iff]
    have hp : 2 ≤ Dyadic.pow2Int s := by
      cases s with
      | zero => omega
      | succ t =>
        have hpos := Dyadic.pow2Int_pos t
        rw [Dyadic.pow2Int_succ]
        omega
    show (0 : Int) < Dyadic.pow2Int s - 1
    omega
  have hDeq : matEq (deltaMat (sysRiesz s) (certRiesz s).W) (sosMatrix (certRiesz s).deltaTerms) = true := by
    unfold matEq
    simp only [List.all_eq_true, decide_eq_true_eq]
    intro i _ j _
    unfold deltaMat UtWU kronHW sosMatrix certRiesz sysRiesz WRiesz
    simp only [List.foldr, add_zero]
    rw [sumFin_fin1, sumFin_fin1]
    have hdiag : (0 : ZHalf) + dyad 1 1 * pow2Nat s * dyad 1 1 - pow2Neg (s + 2) * pow2Nat s =
                 dyad (Dyadic.pow2Int s - 1) 2 := by
      rw [zero_add]
      have hterm1 : dyad 1 1 * pow2Nat s * dyad 1 1 = dyad (Dyadic.pow2Int s) 2 := by
        apply Quotient.sound
        show (1 * Dyadic.pow2Int s * 1) * Dyadic.pow2Int 2 = Dyadic.pow2Int s * Dyadic.pow2Int (1 + 0 + 1)
        simp
      have hterm2 : pow2Neg (s + 2) * pow2Nat s = dyad 1 2 := by
        apply Quotient.sound
        show (1 * Dyadic.pow2Int s) * Dyadic.pow2Int 2 = 1 * Dyadic.pow2Int (s + 2 + 0)
        rw [Int.one_mul, Int.one_mul, Nat.add_zero, Dyadic.pow2Int_add]
      rw [hterm1, hterm2]
      change Quotient.mk Dyadic.instSetoid ⟨Dyadic.pow2Int s, 2⟩ +
             Quotient.mk Dyadic.instSetoid ⟨-1, 2⟩ = _
      rw [ZHalf.mk_add_eq]
      apply Quotient.sound
      show (Dyadic.pow2Int s * Dyadic.pow2Int 2 + (-1) * Dyadic.pow2Int 2) * Dyadic.pow2Int 2 =
           (Dyadic.pow2Int s - 1) * Dyadic.pow2Int (2 + 2)
      have h2 : Dyadic.pow2Int 2 = 4 := rfl
      have h4 : Dyadic.pow2Int (2 + 2) = 16 := rfl
      rw [h2, h4]; omega
    have hoff : dyad (-(Dyadic.pow2Int (s + 1) - 1)) 2 + dyad 1 1 * pow2Nat s * dyad 1 1 - 0 * pow2Nat s =
                -(dyad (Dyadic.pow2Int s - 1) 2) := by
      rw [zero_mul, sub_eq_add_neg, neg_zero, add_zero]
      have hterm1 : dyad 1 1 * pow2Nat s * dyad 1 1 = dyad (Dyadic.pow2Int s) 2 := by
        apply Quotient.sound
        show (1 * Dyadic.pow2Int s * 1) * Dyadic.pow2Int 2 = Dyadic.pow2Int s * Dyadic.pow2Int (1 + 0 + 1)
        simp
      rw [hterm1]
      change Quotient.mk Dyadic.instSetoid ⟨-(Dyadic.pow2Int (s + 1) - 1), 2⟩ +
             Quotient.mk Dyadic.instSetoid ⟨Dyadic.pow2Int s, 2⟩ =
             Quotient.mk Dyadic.instSetoid ⟨-(Dyadic.pow2Int s - 1), 2⟩
      rw [ZHalf.mk_add_eq]
      apply Quotient.sound
      show ((-(Dyadic.pow2Int (s + 1) - 1)) * Dyadic.pow2Int 2 +
            Dyadic.pow2Int s * Dyadic.pow2Int 2) * Dyadic.pow2Int 2 =
           (-(Dyadic.pow2Int s - 1)) * Dyadic.pow2Int (2 + 2)
      rw [Dyadic.pow2Int_succ]
      have h2 : Dyadic.pow2Int 2 = 4 := rfl
      have h4 : Dyadic.pow2Int (2 + 2) = 16 := rfl
      rw [h2, h4]; omega
    match i, j with
    | ⟨0, _⟩, ⟨0, _⟩ =>
      change (0 : ZHalf) + dyad 1 1 * pow2Nat s * dyad 1 1 - pow2Neg (s + 2) * pow2Nat s =
             dyad (Dyadic.pow2Int s - 1) 2 * 1 * 1
      rw [mul_one, mul_one]; exact hdiag
    | ⟨0, _⟩, ⟨1, _⟩ =>
      change dyad (-(Dyadic.pow2Int (s + 1) - 1)) 2 + dyad 1 1 * pow2Nat s * dyad 1 1 - 0 * pow2Nat s =
             dyad (Dyadic.pow2Int s - 1) 2 * 1 * (-1)
      rw [mul_one, mul_neg, mul_one]; exact hoff
    | ⟨1, _⟩, ⟨0, _⟩ =>
      change dyad (-(Dyadic.pow2Int (s + 1) - 1)) 2 + dyad 1 1 * pow2Nat s * dyad 1 1 - 0 * pow2Nat s =
             dyad (Dyadic.pow2Int s - 1) 2 * (-1) * 1
      rw [mul_one, mul_neg, mul_one]; exact hoff
    | ⟨1, _⟩, ⟨1, _⟩ =>
      change (0 : ZHalf) + dyad 1 1 * pow2Nat s * dyad 1 1 - pow2Neg (s + 2) * pow2Nat s =
             dyad (Dyadic.pow2Int s - 1) 2 * (-1) * (-1)
      rw [mul_neg, mul_one, mul_neg, mul_one, neg_neg]; exact hdiag
  have hSpos : allPosWeights (certRiesz s).surplusTerms = true := rfl
  have hSeq : matEq (fun i j => WRiesz s i j - (certRiesz s).W i j) (sosMatrix (certRiesz s).surplusTerms) = true := by
    unfold matEq; simp only [List.all_eq_true, decide_eq_true_eq]
    intro i _ j _; exact sub_self _
  have hf0 : decide (0 < baseScalar (sysRiesz s) (certRiesz s).W) = true := by
    rw [decide_eq_true_eq]
    unfold baseScalar sysRiesz certRiesz WRiesz quadForm quadBilin vec1 mat1
    rw [sumFin_fin1, sumFin_fin1, zero_add, mul_one, mul_one]
    exact pow2Nat_pos s
  simp [h1, h2, h2t, h3, hdet, hh00, hh01, hh11, hDpos, hDeq, hSpos, hSeq, hf0]

def vecOnes (n : Nat) : Fin n → ZHalf := fun _ => 1

theorem muForm_ones (k : Nat) : muForm k (vecOnes (2 ^ k)) = 1 := by
  induction k with
  | zero => exact muForm_zero (vecOnes 1)
  | succ k ih =>
    rw [muForm_succ]
    have h1 : evenHalf (vecOnes (2 ^ (k + 1))) = vecOnes (2 ^ k) := rfl
    have h2 : oddHalf (vecOnes (2 ^ (k + 1))) = vecOnes (2 ^ k) := rfl
    rw [h1, h2, ih, mul_one]
    decide

def sysArch : BQS 2 where
  q0  := 0
  l0  := vec2 1 0
  h00 := dyad 1 3
  h01 := 0
  h11 := dyad 1 3
  U0  := mat2 (dyad 1 1) 0 0 (dyad 1 2)
  U1  := mat2 (dyad 1 1) 0 (dyad 1 2) (dyad 1 2)
  C   := mat4
    (vec4 0 0 (dyad (-1) 3) (dyad (-1) 3))
    (vec4 0 0 (dyad 1 3)    0)
    (vec4 (dyad (-1) 3) (dyad 1 3) 0 0)
    (vec4 (dyad (-1) 3) 0 0 0)

def WArchTarget : Fin 2 → Fin 2 → ZHalf := mat2 (dyad 1 1) 0 0 0

/-- Exact Brownian-bridge strengthening `W_BB = [[0, 1], [1, -2]]`, giving exact 1-term rank-1
    `Δ_BB = 1/8 * (0, 1, 1, -1)^2` and exact 1-term surplus `1/2 * (1, -2)^2`! -/
def certArch : PDCert 2 where
  W            := mat2 0 1 1 (-2)
  h1           := (dyad 1 3, 1, 0)
  h2           := (dyad 1 3, 0, 1)
  hExtra       := []
  deltaTerms   := [(dyad 1 3, vec4 0 1 1 (-1))]
  surplusTerms := [(dyad 1 1, vec2 1 (-2))]

theorem checkBoundaryStrictPD_arch :
    checkBoundaryStrictPD sysArch WArchTarget certArch (dyad 1 1) = true := by decide

theorem monna_L_eq (sys : BQS 2)
    (hl0 : sys.l0 = vec2 1 0)
    (hU0 : sys.U0 = mat2 (dyad 1 1) 0 0 (dyad 1 2))
    (hU1 : sys.U1 = mat2 (dyad 1 1) 0 (dyad 1 2) (dyad 1 2))
    (k : Nat) (x : Fin (2 ^ k) → ZHalf) :
    sys.L k x ⟨0, by decide⟩ = muForm k x ∧ sys.L k x ⟨1, by decide⟩ = nuForm k x := by
  induction k with
  | zero =>
    unfold BQS.L
    rw [hl0, muForm_zero, nuForm_zero]
    constructor
    · change (1 : ZHalf) * x ⟨0, by decide⟩ = x ⟨0, by decide⟩; exact one_mul _
    · change (0 : ZHalf) * x ⟨0, by decide⟩ = 0; exact zero_mul _
  | succ k ih =>
    rcases ih (evenHalf x) with ⟨ih0e, ih1e⟩
    rcases ih (oddHalf x) with ⟨ih0o, ih1o⟩
    constructor
    · unfold BQS.L
      rw [sumFin_fin2, sumFin_fin2, hU0, hU1, ih0e, ih1e, ih0o, ih1o, muForm_succ]
      change (dyad 1 1 * muForm k (evenHalf x) + 0 * nuForm k (evenHalf x)) +
             (dyad 1 1 * muForm k (oddHalf x) + 0 * nuForm k (oddHalf x)) = _
      simp [zero_mul, add_zero]
    · unfold BQS.L
      rw [sumFin_fin2, sumFin_fin2, hU0, hU1, ih0e, ih1e, ih0o, ih1o, nuForm_succ]
      change (0 * muForm k (evenHalf x) + dyad 1 2 * nuForm k (evenHalf x)) +
             (dyad 1 2 * muForm k (oddHalf x) + dyad 1 2 * nuForm k (oddHalf x)) = _
      rw [zero_mul, zero_add, ← add_assoc]

theorem sysArch_Q_eq (k : Nat) (x : Fin (2 ^ k) → ZHalf) :
    sysArch.Q k x = -monnaArchForm k x := by
  induction k with
  | zero =>
    unfold BQS.Q BQS.B sysArch
    rw [monnaArchForm_zero, zero_mul, zero_mul, neg_zero]
  | succ k ih =>
    unfold BQS.Q BQS.B
    change dyad 1 3 * sysArch.Q k (evenHalf x) +
           0 * (sysArch.B k (evenHalf x) (oddHalf x) + sysArch.B k (oddHalf x) (evenHalf x)) +
           dyad 1 3 * sysArch.Q k (oddHalf x) +
           quadForm sysArch.C (pairVec (sysArch.L k (evenHalf x)) (sysArch.L k (oddHalf x))) = _
    rw [ih (evenHalf x), ih (oddHalf x), zero_mul, add_zero, monnaArchForm_succ]
    have hLe := monna_L_eq sysArch rfl rfl rfl k (evenHalf x)
    have hLo := monna_L_eq sysArch rfl rfl rfl k (oddHalf x)
    rw [quadForm_fin4]
    have pv0 : pairVec (sysArch.L k (evenHalf x)) (sysArch.L k (oddHalf x)) ⟨0, by decide⟩ = muForm k (evenHalf x) := by
      unfold pairVec; simp; exact hLe.1
    have pv1 : pairVec (sysArch.L k (evenHalf x)) (sysArch.L k (oddHalf x)) ⟨1, by decide⟩ = nuForm k (evenHalf x) := by
      unfold pairVec; simp; exact hLe.2
    have pv2 : pairVec (sysArch.L k (evenHalf x)) (sysArch.L k (oddHalf x)) ⟨2, by decide⟩ = muForm k (oddHalf x) := by
      unfold pairVec; simp; exact hLo.1
    have pv3 : pairVec (sysArch.L k (evenHalf x)) (sysArch.L k (oddHalf x)) ⟨3, by decide⟩ = nuForm k (oddHalf x) := by
      unfold pairVec; simp; exact hLo.2
    rw [pv0, pv1, pv2, pv3]
    change dyad 1 3 * (-monnaArchForm k (evenHalf x)) + dyad 1 3 * (-monnaArchForm k (oddHalf x)) +
      ((0 * muForm k (evenHalf x) * muForm k (evenHalf x) + 0 * muForm k (evenHalf x) * nuForm k (evenHalf x) +
        dyad (-1) 3 * muForm k (evenHalf x) * muForm k (oddHalf x) + dyad (-1) 3 * muForm k (evenHalf x) * nuForm k (oddHalf x)) +
       (0 * nuForm k (evenHalf x) * muForm k (evenHalf x) + 0 * nuForm k (evenHalf x) * nuForm k (evenHalf x) +
        dyad 1 3 * nuForm k (evenHalf x) * muForm k (oddHalf x) + 0 * nuForm k (evenHalf x) * nuForm k (oddHalf x)) +
       (dyad (-1) 3 * muForm k (oddHalf x) * muForm k (evenHalf x) + dyad 1 3 * muForm k (oddHalf x) * nuForm k (evenHalf x) +
        0 * muForm k (oddHalf x) * muForm k (oddHalf x) + 0 * muForm k (oddHalf x) * nuForm k (oddHalf x)) +
       (dyad (-1) 3 * nuForm k (oddHalf x) * muForm k (evenHalf x) + 0 * nuForm k (oddHalf x) * nuForm k (evenHalf x) +
        0 * nuForm k (oddHalf x) * muForm k (oddHalf x) + 0 * nuForm k (oddHalf x) * nuForm k (oddHalf x))) = _
    simp only [zero_mul, zero_add, add_zero, mul_neg]
    have h1 : dyad (-1) 3 + dyad (-1) 3 = -(dyad 1 2) := by decide
    have h2 : dyad 1 3 + dyad 1 3 = dyad 1 2 := by decide
    generalize muForm k (evenHalf x) = m0
    generalize nuForm k (evenHalf x) = n0
    generalize muForm k (oddHalf x) = m1
    generalize nuForm k (oddHalf x) = n1
    have hc1 : dyad (-1) 3 * m1 * m0 = dyad (-1) 3 * m0 * m1 := by rw [mul_assoc, mul_comm m1 m0, ← mul_assoc]
    have hc2 : dyad 1 3 * m1 * n0 = dyad 1 3 * n0 * m1 := by rw [mul_assoc, mul_comm m1 n0, ← mul_assoc]
    have hc3 : dyad (-1) 3 * n1 * m0 = dyad (-1) 3 * m0 * n1 := by rw [mul_assoc, mul_comm n1 m0, ← mul_assoc]
    rw [hc1, hc2, hc3]
    have ha : dyad (-1) 3 * m0 * m1 + dyad (-1) 3 * m0 * m1 = -(dyad 1 2 * m0 * m1) := by
      rw [← add_mul, ← add_mul, h1, neg_mul, neg_mul]
    have hb : dyad (-1) 3 * m0 * n1 + dyad (-1) 3 * m0 * n1 = -(dyad 1 2 * m0 * n1) := by
      rw [← add_mul, ← add_mul, h1, neg_mul, neg_mul]
    have hc : dyad 1 3 * n0 * m1 + dyad 1 3 * n0 * m1 = dyad 1 2 * n0 * m1 := by
      rw [← add_mul, ← add_mul, h2]
    have hq : ((dyad (-1) 3 * m0 * m1 + dyad (-1) 3 * m0 * n1) + dyad 1 3 * n0 * m1 +
               (dyad (-1) 3 * m0 * m1 + dyad 1 3 * n0 * m1) + dyad (-1) 3 * m0 * n1) =
              -(dyad 1 2 * m0 * m1) + -(dyad 1 2 * m0 * n1) + dyad 1 2 * n0 * m1 := by
      rw [← ha, ← hb, ← hc]
      generalize dyad (-1) 3 * m0 * m1 = X
      generalize dyad (-1) 3 * m0 * n1 = Y
      generalize dyad 1 3 * n0 * m1 = Z
      calc (X + Y) + Z + (X + Z) + Y
          = ((X + Y) + (X + Z)) + (Z + Y) := by
              rw [add_assoc (X + Y) Z (X + Z), add_comm Z (X + Z), ← add_assoc (X + Y), add_assoc]
        _ = ((X + X) + (Y + Z)) + (Z + Y) := by rw [add_four_swap X Y X Z]
        _ = (X + X) + ((Y + Z) + (Y + Z)) := by rw [add_assoc, add_comm Z Y]
        _ = (X + X) + ((Y + Y) + (Z + Z)) := by rw [add_four_swap Y Z Y Z]
        _ = (X + X) + (Y + Y) + (Z + Z) := (add_assoc _ _ _).symm
    rw [hq, sub_eq_add_neg, neg_add, neg_add, neg_add, neg_add, neg_neg, ← add_assoc, ← add_assoc]

def vecEndpoints (k : Nat) : Fin (2 ^ k) → ZHalf :=
  fun i => if i.val = 0 ∨ i.val = 2 ^ k - 1 then 1 else 0

theorem bitrev_zero (k : Nat) : bitrev k 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => unfold bitrev; simp [ih]

theorem bitrev_max (k : Nat) : bitrev k (2 ^ k - 1) = 2 ^ k - 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hp := Nat.two_pow_pos k
    have hodd : 2 ^ (k + 1) - 1 = 2 * (2 ^ k - 1) + 1 := by rw [Nat.pow_succ]; omega
    rw [hodd, bitrev_two_mul_add_one, ih]
    omega

/-- INFINITE SHARPNESS THEOREM FOR THEOREM 2:
    For EVERY dyadic reduction `c = 1/2 - 2^{-r} < 1/2`, the two-point boundary witness
    `x^{(k)} = e_0 + e_{2^k - 1}` (at `k = r + 2`) makes the form STRICTLY NEGATIVE! -/
theorem thm_monnaArch_sharp (r : Nat) :
    ∃ (k : Nat) (x : Fin (2 ^ k) → ZHalf), (∃ i, x i ≠ 0) ∧
      (dyad 1 1 - pow2Neg r) * (muForm k x * muForm k x) - monnaArchForm k x < 0 := by
  let k := r + 2
  have hkpos : 1 ≤ k := by omega
  have hne01 : (0 : Nat) ≠ 2 ^ k - 1 := by
    have : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hkpos
    omega
  refine ⟨k, vecEndpoints k, ⟨⟨0, Nat.two_pow_pos k⟩, by unfold vecEndpoints; simp; decide⟩, ?_⟩
  let i0 : Fin (2 ^ k) := ⟨0, Nat.two_pow_pos k⟩
  let i1 : Fin (2 ^ k) := ⟨2 ^ k - 1, by have := Nat.two_pow_pos k; omega⟩
  have hsplit_vec : ∀ (f : Fin (2 ^ k) → ZHalf),
      (∀ i : Fin (2 ^ k), i ≠ i0 → i ≠ i1 → f i = 0) →
      sumFin f = f i0 + f i1 := fun f hf => by
    let f0 : Fin (2 ^ k) → ZHalf := fun i => if i = i0 then f i0 else 0
    let f1 : Fin (2 ^ k) → ZHalf := fun i => if i = i1 then f i1 else 0
    have hfeq : ∀ i : Fin (2 ^ k), f i = f0 i + f1 i := fun i => by
      by_cases h0 : i = i0
      · subst h0
        have hneq : i0 ≠ i1 := fun h => hne01 (congrArg Fin.val h)
        simp [f0, f1, hneq, add_zero]
      · by_cases h1 : i = i1
        · subst h1; simp [f0, f1, h0, zero_add]
        · simp [f0, f1, h0, h1, add_zero, hf i h0 h1]
    rw [sumFin_congr hfeq, sumFin_add]
    have s0 : sumFin f0 = f i0 := by
      rw [sumFin_single i0 f0 (fun i hi => by simp [f0, hi])]; simp [f0]
    have s1 : sumFin f1 = f i1 := by
      rw [sumFin_single i1 f1 (fun i hi => by simp [f1, hi])]; simp [f1]
    rw [s0, s1]
  have hmu : muForm k (vecEndpoints k) = pow2Neg k * 2 := by
    unfold muForm
    rw [hsplit_vec (vecEndpoints k) (fun i h0 h1 => by
      unfold vecEndpoints
      have hv0 : i.val ≠ 0 := fun h => h0 (Fin.ext h)
      have hv1 : i.val ≠ 2 ^ k - 1 := fun h => h1 (Fin.ext h)
      simp [hv0, hv1])]
    have e0 : vecEndpoints k i0 = 1 := by unfold vecEndpoints; simp [i0]
    have e1 : vecEndpoints k i1 = 1 := by unfold vecEndpoints; simp [i1]
    rw [e0, e1]; congr 1
  have hA : monnaArchForm k (vecEndpoints k) =
            pow2Neg (2 * k) * (2 * dyad (Int.ofNat (2 ^ k - 1)) k) := by
    unfold monnaArchForm
    congr 1
    rw [hsplit_vec _ (fun i h0 h1 => by
      have hv0 : i.val ≠ 0 := fun h => h0 (Fin.ext h)
      have hv1 : i.val ≠ 2 ^ k - 1 := fun h => h1 (Fin.ext h)
      have hxi : vecEndpoints k i = 0 := by unfold vecEndpoints; simp [hv0, hv1]
      rw [sumFin_congr (fun j => by rw [hxi, mul_zero, zero_mul])]; exact sumFin_zero)]
    have innerSplit : ∀ a : Fin (2 ^ k),
        sumFin (fun j : Fin (2 ^ k) => monnaArchKernel k a.val j.val * vecEndpoints k a * vecEndpoints k j) =
        monnaArchKernel k a.val i0.val * vecEndpoints k a * 1 +
        monnaArchKernel k a.val i1.val * vecEndpoints k a * 1 := fun a => by
      rw [hsplit_vec _ (fun j h0 h1 => by
        have hv0 : j.val ≠ 0 := fun h => h0 (Fin.ext h)
        have hv1 : j.val ≠ 2 ^ k - 1 := fun h => h1 (Fin.ext h)
        have hxj : vecEndpoints k j = 0 := by unfold vecEndpoints; simp [hv0, hv1]
        rw [hxj, mul_zero])]
      have e0 : vecEndpoints k i0 = 1 := by unfold vecEndpoints; simp [i0]
      have e1 : vecEndpoints k i1 = 1 := by unfold vecEndpoints; simp [i1]
      rw [e0, e1]
    rw [innerSplit i0, innerSplit i1]
    have e0 : vecEndpoints k i0 = 1 := by unfold vecEndpoints; simp [i0]
    have e1 : vecEndpoints k i1 = 1 := by unfold vecEndpoints; simp [i1]
    rw [e0, e1]
    simp only [mul_one]
    have k00 : monnaArchKernel k i0.val i0.val = 0 := by
      unfold monnaArchKernel; rw [absDiff_self]; apply Quotient.sound; show (0 : Int) * _ = 0 * _; simp
    have k11 : monnaArchKernel k i1.val i1.val = 0 := by
      unfold monnaArchKernel; rw [absDiff_self]; apply Quotient.sound; show (0 : Int) * _ = 0 * _; simp
    have k01 : monnaArchKernel k i0.val i1.val = dyad (Int.ofNat (2 ^ k - 1)) k := by
      unfold monnaArchKernel i0 i1; dsimp only
      rw [bitrev_zero, bitrev_max]; unfold absDiff; simp
    have k10 : monnaArchKernel k i1.val i0.val = dyad (Int.ofNat (2 ^ k - 1)) k := by
      unfold monnaArchKernel; rw [absDiff_comm]; exact k01
    rw [k00, k11, k01, k10, zero_add, add_zero]
    have h2 : (1 : ZHalf) + 1 = 2 := by decide
    calc dyad (Int.ofNat (2 ^ k - 1)) k + dyad (Int.ofNat (2 ^ k - 1)) k
        = (1 + 1) * dyad (Int.ofNat (2 ^ k - 1)) k := by rw [add_mul, one_mul]
      _ = 2 * dyad (Int.ofNat (2 ^ k - 1)) k := by rw [h2]
  rw [hmu, hA]
  have hsq : (pow2Neg k * 2) * (pow2Neg k * 2) = pow2Neg (2 * k) * 4 := by
    have hpk : pow2Neg (2 * k) = pow2Neg k * pow2Neg k := by
      rw [show 2 * k = k + k by omega]; exact pow2Neg_add k k
    rw [hpk]
    have h4 : (2 : ZHalf) * 2 = 4 := by decide
    calc (pow2Neg k * 2) * (pow2Neg k * 2)
        = (pow2Neg k * (2 * pow2Neg k)) * 2 := by simp [mul_assoc]
      _ = (pow2Neg k * (pow2Neg k * 2)) * 2 := by rw [mul_comm (2 : ZHalf) (pow2Neg k)]
      _ = (pow2Neg k * pow2Neg k) * (2 * 2) := by simp [mul_assoc]
      _ = (pow2Neg k * pow2Neg k) * 4 := by rw [h4]
  rw [hsq]
  have hfact : (dyad 1 1 - pow2Neg r) * (pow2Neg (2 * k) * 4) -
               pow2Neg (2 * k) * (2 * dyad (Int.ofNat (2 ^ k - 1)) k) =
               -(pow2Neg (2 * k) * (2 * dyad (Int.ofNat (2 ^ k - 1)) k - (dyad 1 1 - pow2Neg r) * 4)) := by
    rw [← mul_assoc (dyad 1 1 - pow2Neg r), mul_comm (dyad 1 1 - pow2Neg r) (pow2Neg (2 * k)),
        mul_assoc (pow2Neg (2 * k)), ← mul_sub, ← mul_neg]
    congr 1
    have hns : ∀ a b : ZHalf, a - b = -(b - a) := fun a b => by
      rw [sub_eq_add_neg, sub_eq_add_neg, neg_add, neg_neg, add_comm]
    exact hns _ _
  rw [hfact, ← neg_pos_iff, neg_neg]
  refine mul_pos (pow2Neg_pos (2 * k)) ?_
  have hrew : 2 * dyad (Int.ofNat (2 ^ k - 1)) k = 2 - dyad 2 k := by
    have h1 : 1 ≤ 2 ^ k := Nat.two_pow_pos k
    have hsubInt : Int.ofNat (2 ^ k - 1) = Dyadic.pow2Int k - 1 := by
      have hadd : (2 ^ k - 1) + 1 = 2 ^ k := by omega
      have h2 := congrArg Int.ofNat hadd
      have h1int : Int.ofNat 1 = 1 := rfl
      rw [ofNat_add_int, ofNat_pow2, h1int] at h2
      omega
    rw [hsubInt]
    change Quotient.mk Dyadic.instSetoid ⟨2 * (Dyadic.pow2Int k - 1), 0 + k⟩ =
           Quotient.mk Dyadic.instSetoid ⟨2, 0⟩ + Quotient.mk Dyadic.instSetoid ⟨-2, k⟩
    rw [ZHalf.mk_add_eq]
    apply Quotient.sound
    show (2 * (Dyadic.pow2Int k - 1)) * Dyadic.pow2Int (0 + k) =
         (2 * Dyadic.pow2Int k + (-2) * Dyadic.pow2Int 0) * Dyadic.pow2Int (0 + k)
    congr 1
    have h0 : Dyadic.pow2Int 0 = 1 := rfl
    rw [h0]; omega
  have h4h : (dyad 1 1 - pow2Neg r) * 4 = 2 - dyad 4 r := by
    rw [sub_mul]
    have h1 : dyad 1 1 * 4 = 2 := by decide
    have h2 : pow2Neg r * 4 = dyad 4 r := by
      apply Quotient.sound
      show (1 * 4) * Dyadic.pow2Int r = 4 * Dyadic.pow2Int (r + 0); simp
    rw [h1, h2]
  rw [hrew, h4h]
  have hsimp : (2 - dyad 2 k) - (2 - dyad 4 r) = dyad 4 r - dyad 2 k := by
    rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, neg_add, neg_neg,
        add_four_swap 2 (-dyad 2 k) (-2) (dyad 4 r), add_neg_cancel, zero_add, add_comm]
  rw [hsimp, sub_pos_iff]
  change Dyadic.lt ⟨2, r + 2⟩ ⟨4, r⟩
  unfold Dyadic.lt
  show (2 : Int) * Dyadic.pow2Int r < 4 * Dyadic.pow2Int (r + 2)
  rw [Dyadic.pow2Int_add]
  have h2 : Dyadic.pow2Int 2 = 4 := rfl
  have hp := Dyadic.pow2Int_pos r
  rw [h2]; omega

/-! ### THEOREM 3: Sharp Coupled Non-Commuting Adelic-Monna-Dipole Form (∀ k ≥ 0, ∀ x ≠ 0) -/

def sysAdelic : BQS 2 where
  q0  := 0
  l0  := vec2 1 0
  h00 := dyad 1 3
  h01 := 0
  h11 := dyad 1 3
  U0  := mat2 (dyad 1 1) 0 0 (dyad 1 2)
  U1  := mat2 (dyad 1 1) 0 (dyad 1 2) (dyad 1 2)
  C   := mat4
    (vec4 0 0 (dyad (-1) 0) (dyad (-1) 2))
    (vec4 0 0 (dyad 1 2)    0)
    (vec4 (dyad (-1) 0) (dyad 1 2) 0 0)
    (vec4 (dyad (-1) 2) 0 0 0)

/-- Boundary matrix `W_adelic = [[2, 2], [2, -4]]`, i.e., `3*μ^2 - (μ - 2*ν)^2`. -/
def WAdelic : Fin 2 → Fin 2 → ZHalf := mat2 2 2 2 (-4)

/-- Exact 2-term pure Z[1/2] SOS certificate for the coupled non-commuting adelic form! -/
def certAdelic : PDCert 2 where
  W            := WAdelic
  h1           := (dyad 1 3, 1, 0)
  h2           := (dyad 1 3, 0, 1)
  hExtra       := []
  deltaTerms   := [
    (dyad 1 1, vec4 (dyad (-1) 1) (dyad 1 1) 1 (dyad (-1) 1)),
    (dyad 1 3, vec4 1 1 0 (-1))
  ]
  surplusTerms := []

theorem checkStrictPD_adelic :
    checkStrictPD sysAdelic WAdelic certAdelic = true := by decide

/-- Asymmetric, non-diagonal bilinear transfer `H = [[1/8, 1/16], [1/16, 3/16]]`
    coupled with indefinite full adelic interface `C = C_2adic + C_arch`. -/
def sysAsym : BQS 2 where
  q0  := 0
  l0  := vec2 1 0
  h00 := dyad 1 3
  h01 := dyad 1 4
  h11 := dyad 3 4
  U0  := mat2 (dyad 1 1) 0 0 (dyad 1 2)
  U1  := mat2 (dyad 1 1) 0 (dyad 1 2) (dyad 1 2)
  C   := mat4
    (vec4 0 0 (dyad (-3) 3) (dyad (-1) 3))
    (vec4 0 0 (dyad 1 3)    0)
    (vec4 (dyad (-3) 3) (dyad 1 3) 0 0)
    (vec4 (dyad (-1) 3) 0 0 0)

/-- Indefinite boundary potential `W_asym = [[1, 2], [2, -2]]` (det = -6 < 0!). -/
def WAsymIndef : Fin 2 → Fin 2 → ZHalf := mat2 1 2 2 (-2)

/-- Pure-mean target `W_mean = [[3, 0], [0, 0]]`, with exact 1-term surplus `2 * (μ - ν)^2`. -/
def WAsymMean : Fin 2 → Fin 2 → ZHalf := mat2 3 0 0 0

/-- Pure Z[1/2] spanning SOS of `H` (2 terms, det = 1) + 4-term pure Z[1/2] SOS of `Δ`! -/
def certAsymIndef : PDCert 2 where
  W            := WAsymIndef
  h1           := (dyad 1 3, 1, dyad 1 1)
  h2           := (dyad 5 5, 0, 1)
  hExtra       := []
  deltaTerms   := [
    (dyad 1 3, vec4 1 0 (dyad 1 1) 0),
    (dyad 1 3, vec4 0 1 1 0),
    (dyad 1 5, vec4 0 0 1 0),
    (dyad 1 2, vec4 0 0 1 (-1))
  ]
  surplusTerms := []

def certAsymMean : PDCert 2 where
  W            := WAsymIndef
  h1           := (dyad 1 3, 1, dyad 1 1)
  h2           := (dyad 5 5, 0, 1)
  hExtra       := []
  deltaTerms   := certAsymIndef.deltaTerms
  surplusTerms := [(2, vec2 1 (-1))]

theorem checkStrictPD_asym_indef :
    checkStrictPD sysAsym WAsymIndef certAsymIndef = true := by decide

theorem checkStrictPD_asym_mean :
    checkStrictPD sysAsym WAsymMean certAsymMean = true := by decide

def basisFin4 (idx : Fin 4) : Fin 4 → ZHalf := fun i => if i = idx then 1 else 0

end DyadicPDEngine
