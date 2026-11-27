/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions (`coupled-s4-tfunction-orbits`)

Coupled 2-Variable Reversible T-Function Orbit-Lifting Engine: definitions and sorry-free helper lemmas (pure Lean 4 `Init`, zero Mathlib).
-/

namespace CoupledS4TFunction


-- ============================================================================
-- PART 1: GENERAL S4-MONODROMY ORBIT-LIFTING ENGINE
-- ============================================================================

abbrev State (w : Nat) := BitVec w × BitVec w

abbrev Fiber := Bool × Bool

def truncState {w : Nat} (s : State (w + 1)) : State w :=
  (s.1.setWidth w, s.2.setWidth w)

def msbPair {w : Nat} (s : State (w + 1)) : Fiber :=
  (s.1.getLsbD w, s.2.getLsbD w)

def liftState {w : Nat} (p : Fiber) (s : State w) : State (w + 1) :=
  (BitVec.cons p.1 s.1, BitVec.cons p.2 s.2)

@[simp] theorem getLsbD_cons_self {w : Nat} (b : Bool) (x : BitVec w) :
    (BitVec.cons b x).getLsbD w = b := by
  rw [BitVec.getLsbD_cons]
  simp

@[simp] theorem getElem_cons_self {w : Nat} (b : Bool) (x : BitVec w) :
    (BitVec.cons b x)[w] = b := by
  rw [← BitVec.getLsbD_eq_getElem]
  exact getLsbD_cons_self b x

@[simp] theorem getElem_cons_lt {w : Nat} (b : Bool) (x : BitVec w) {i : Nat} (hi : i < w) :
    (BitVec.cons b x)[i]'(Nat.lt_succ_of_lt hi) = x[i] := by
  rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_cons]
  simp [Nat.ne_of_lt hi]

@[simp] theorem setWidth_cons {w : Nat} (b : Bool) (x : BitVec w) :
    (BitVec.cons b x).setWidth w = x := by
  ext i hi
  simp

theorem cons_eta {w : Nat} (x : BitVec (w + 1)) :
    BitVec.cons (x.getLsbD w) (x.setWidth w) = x := by
  ext i hi
  by_cases h : i = w
  · subst h
    simp [BitVec.getLsbD_eq_getElem]
  · have hlt : i < w := by omega
    simp [hlt]
    exact BitVec.getLsbD_eq_getElem hi

def iter {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => f (iter f n x)

def IsExactPeriod {α : Type} (f : α → α) (x : α) (L : Nat) : Prop :=
  0 < L ∧ iter f L x = x ∧ ∀ k, 0 < k → k < L → iter f k x ≠ x

structure TFunc2 where
  eval : ∀ w, State w → State w
  compat : ∀ w (s : State (w + 1)), truncState (eval (w + 1) s) = eval w (truncState s)

def fiber (T : TFunc2) (w : Nat) (s : State w) (p : Fiber) : Fiber :=
  msbPair (T.eval (w + 1) (liftState p s))

def monodromy (T : TFunc2) (w : Nat) (s : State w) : Nat → Fiber → Fiber
  | 0, p => p
  | n + 1, p => fiber T w (iter (T.eval w) n s) (monodromy T w s n p)

def IsPureTranslation (f : Fiber → Fiber) : Prop :=
  ∃ a b : Bool, ∀ p : Fiber, f p = (xor p.1 a, xor p.2 b)

/-- Upper-triangular affine element of D4 ⊂ AGL(2, F2) = S4:
    (a, b) ↦ (a ⊕ (lam && b) ⊕ alpha, b ⊕ beta). -/
structure D4Elem where
  lam : Bool
  alpha : Bool
  beta : Bool
  deriving DecidableEq

def D4Elem.id : D4Elem := ⟨false, false, false⟩

def D4Elem.apply (e : D4Elem) (p : Fiber) : Fiber :=
  (xor (xor p.1 (e.lam && p.2)) e.alpha, xor p.2 e.beta)

def D4Elem.comp (e₂ e₁ : D4Elem) : D4Elem :=
  ⟨xor e₁.lam e₂.lam, xor (xor e₁.alpha e₂.alpha) (e₂.lam && e₁.beta), xor e₁.beta e₂.beta⟩

def allBitVecs : (w : Nat) → List (BitVec w)
  | 0 => [0#0]
  | w + 1 =>
    (allBitVecs w).map (BitVec.cons false) ++ (allBitVecs w).map (BitVec.cons true)

def allStates (w : Nat) : List (State w) :=
  (allBitVecs w).flatMap (fun x => (allBitVecs w).map (fun y => (x, y)))

def xorList {α : Type} (f : α → Bool) : List α → Bool
  | [] => false
  | a :: t => xor (f a) (xorList f t)

def orbitList {α : Type} (f : α → α) (s0 : α) : Nat → List α
  | 0 => []
  | n + 1 => orbitList f s0 n ++ [iter f n s0]

/-- Monodromy of a D4-fibered T-function accumulated in D4Elem. -/
def d4Monodromy (T : TFunc2) (w : Nat)
    (lam alpha beta : State w → Bool) (s : State w) : Nat → D4Elem
  | 0 => D4Elem.id
  | n + 1 =>
    let sn := iter (T.eval w) n s
    D4Elem.comp ⟨lam sn, alpha sn, beta sn⟩ (d4Monodromy T w lam alpha beta s n)

def halfStates (w : Nat) : List (BitVec w × BitVec (w + 1)) :=
  (allBitVecs w).flatMap (fun x => (allBitVecs (w + 1)).map (fun y => (x, y)))

structure TFunc1 where
  eval : ∀ w, BitVec w → BitVec w
  compat : ∀ w (x : BitVec (w + 1)), (eval (w + 1) x).setWidth w = eval w (x.setWidth w)

structure TScalar2 where
  eval : ∀ w, BitVec w → BitVec w → BitVec w
  compat : ∀ w (x y : BitVec (w + 1)),
    (eval (w + 1) x y).setWidth w = eval w (x.setWidth w) (y.setWidth w)

/-- Pure-silicon carry-propagation mask m(x, y) = ((x &&& y) + 1) ^^^ (x &&& y). -/
def andCarryMask {w : Nat} (x y : BitVec w) : BitVec w :=
  let z := x &&& y
  (z + 1#w) ^^^ z

theorem setWidth_add {w : Nat} (a b : BitVec (w + 1)) :
    (a + b).setWidth w = a.setWidth w + b.setWidth w := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
  have hdvd : 2 ^ w ∣ 2 ^ (w + 1) := ⟨2, by rw [Nat.pow_succ]⟩
  rw [Nat.mod_mod_of_dvd _ hdvd, Nat.add_mod]

theorem setWidth_mul {w : Nat} (a b : BitVec (w + 1)) :
    (a * b).setWidth w = a.setWidth w * b.setWidth w := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_mul]
  have hdvd : 2 ^ w ∣ 2 ^ (w + 1) := ⟨2, by rw [Nat.pow_succ]⟩
  rw [Nat.mod_mod_of_dvd _ hdvd, Nat.mul_mod]

theorem setWidth_and {w : Nat} (a b : BitVec (w + 1)) :
    (a &&& b).setWidth w = a.setWidth w &&& b.setWidth w := by
  ext i hi; simp

theorem setWidth_xor {w : Nat} (a b : BitVec (w + 1)) :
    (a ^^^ b).setWidth w = a.setWidth w ^^^ b.setWidth w := by
  ext i hi; simp

theorem setWidth_ofNat {w : Nat} (n : Nat) :
    (BitVec.ofNat (w + 1) n).setWidth w = BitVec.ofNat w n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have hdvd : 2 ^ w ∣ 2 ^ (w + 1) := ⟨2, by rw [Nat.pow_succ]⟩
  exact Nat.mod_mod_of_dvd n hdvd

theorem setWidth_andCarryMask {w : Nat} (x y : BitVec (w + 1)) :
    (andCarryMask x y).setWidth w = andCarryMask (x.setWidth w) (y.setWidth w) := by
  simp only [andCarryMask, setWidth_xor, setWidth_add, setWidth_and, setWidth_ofNat]

/-- Universal Nonlinear Full-Period 2^(2w) Family:
    T_{P,Q,R}(x, y) = (x + (y & m) + 2*P(x, y),  y + m + 2*Q(y) + 4*R(x, y))
    where m = ((x & y) + 1) ^ (x & y). -/
def family1 (P : TScalar2) (Q : TFunc1) (R : TScalar2) : TFunc2 where
  eval w s :=
    let x := s.1
    let y := s.2
    let m := andCarryMask x y
    (x + (y &&& m) + 2#w * P.eval w x y,
     y + m + 2#w * Q.eval w y + 4#w * R.eval w x y)
  compat w s := by
    rcases s with ⟨x, y⟩
    simp only [truncState]
    apply Prod.ext
    · simp only [setWidth_add, setWidth_and, setWidth_mul, setWidth_ofNat,
        setWidth_andCarryMask, P.compat]
    · simp only [setWidth_add, setWidth_mul, setWidth_ofNat,
        setWidth_andCarryMask, Q.compat, R.compat]

def fam1Lam (w : Nat) (s : State w) : Bool :=
  decide (s.1 = BitVec.allOnes w ∧ s.2 = BitVec.allOnes w)

def fam1Alpha (P : TScalar2) (w : Nat) (s : State w) : Bool :=
  let x1 := BitVec.cons false s.1
  let y1 := BitVec.cons false s.2
  let m1 := andCarryMask x1 y1
  (x1 + (y1 &&& m1) + 2#(w + 1) * P.eval (w + 1) x1 y1).getLsbD w

def fam1Beta (Q : TFunc1) (R : TScalar2) (w : Nat) (s : State w) : Bool :=
  let x1 := BitVec.cons false s.1
  let y1 := BitVec.cons false s.2
  let m1 := andCarryMask x1 y1
  (y1 + m1 + 2#(w + 1) * Q.eval (w + 1) y1 + 4#(w + 1) * R.eval (w + 1) x1 y1).getLsbD w

/-- Constructive genuinely nonlinear arithmetic-bitwise witness:
    P(x, y) = x*y + (x &&& y), Q(y) = y*y, R(x, y) = x*y + (x ^^^ y). -/
def witnessP : TScalar2 where
  eval _ x y := x * y + (x &&& y)
  compat _ x y := by simp [setWidth_add, setWidth_mul]

def witnessQ : TFunc1 where
  eval _ y := y * y
  compat _ y := by simp [setWidth_mul]

def witnessR : TScalar2 where
  eval _ x y := x * y + (x ^^^ y)
  compat _ x y := by simp [setWidth_add, setWidth_mul]

/-- Sharpness Counterexample 1A: weakening 4*R to 2*R with R(x,y) = x &&& y
    collapses period at w = 2 from 16 to 4! -/
def fam1Sharp2And (w : Nat) (s : State w) : State w :=
  let m := andCarryMask s.1 s.2
  (s.1 + (s.2 &&& m), s.2 + m + 2#w * (s.1 &&& s.2))

/-- Sharpness Counterexample 1B: weakening 4*R to 2*R with R(x,y) = x * y
    collapses period at w = 2 from 16 to 8! -/
def fam1Sharp2Mul (w : Nat) (s : State w) : State w :=
  let m := andCarryMask s.1 s.2
  (s.1 + (s.2 &&& m) + 2#w * (s.1 * s.2), s.2 + m + 2#w * (s.1 * s.2))

/-- Sharpness Counterexample 1C (Infinite Obstruction): removing the cross-bit
    shear (y &&& m) collapses EVERY orbit to period <= 2^w for ALL w >= 1! -/
def fam1NoShear (P : TScalar2) (Q : TFunc1) (R : TScalar2) : TFunc2 where
  eval w s :=
    let m := andCarryMask s.1 s.2
    (s.1 + 1#w + 2#w * P.eval w s.1 s.2,
     s.2 + m + 2#w * Q.eval w s.2 + 4#w * R.eval w s.1 s.2)
  compat w s := by
    rcases s with ⟨x, y⟩
    simp only [truncState]
    apply Prod.ext
    · simp only [setWidth_add, setWidth_mul, setWidth_ofNat, P.compat]
    · simp only [setWidth_add, setWidth_mul, setWidth_ofNat, setWidth_andCarryMask, Q.compat, R.compat]

/-- Pure-silicon trailing-zero mask: m(y) = y ^^^ (y - 1).
    Bit k of zeroMask y is true iff y mod 2^k = 0! -/
def zeroMask {w : Nat} (y : BitVec w) : BitVec w :=
  y ^^^ (y - 1#w)

theorem setWidth_sub {w : Nat} (a b : BitVec (w + 1)) :
    (a - b).setWidth w = a.setWidth w - b.setWidth w := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub]
  have hp : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
  have hdvd : 2 ^ w ∣ 2 ^ (w + 1) := ⟨2, by rw [Nat.pow_succ]⟩
  rw [Nat.mod_mod_of_dvd _ hdvd]
  have hb : b.toNat < 2 ^ (w + 1) := b.isLt
  by_cases hblt : b.toNat < 2 ^ w
  · rw [Nat.mod_eq_of_lt hblt]
    have hsplit : 2 ^ (w + 1) - b.toNat + a.toNat = 2 ^ w + (2 ^ w - b.toNat + a.toNat) := by omega
    rw [hsplit, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod,
        Nat.add_mod (2 ^ w - b.toNat), Nat.add_mod (2 ^ w - b.toNat) (a.toNat % 2 ^ w), Nat.mod_mod]
  · have hbmod : b.toNat % 2 ^ w = b.toNat - 2 ^ w := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hbmod]
    have hsplit : 2 ^ (w + 1) - b.toNat + a.toNat = 2 ^ w - (b.toNat - 2 ^ w) + a.toNat := by omega
    rw [hsplit, Nat.add_mod (2 ^ w - (b.toNat - 2 ^ w)),
        Nat.add_mod (2 ^ w - (b.toNat - 2 ^ w)) (a.toNat % 2 ^ w), Nat.mod_mod]

theorem setWidth_zeroMask {w : Nat} (y : BitVec (w + 1)) :
    (zeroMask y).setWidth w = zeroMask (y.setWidth w) := by
  simp only [zeroMask, setWidth_xor, setWidth_sub, setWidth_ofNat]

/-- Shift-XOR polynomial of y: ⨁_{d ∈ shifts} (y <<< d). -/
def shiftXorY {w : Nat} : List Nat → BitVec w → BitVec w
  | [], _ => 0#w
  | d :: ds, y => (y <<< d) ^^^ shiftXorY ds y

theorem setWidth_shiftLeft {w : Nat} (y : BitVec (w + 1)) (d : Nat) :
    (y <<< d).setWidth w = (y.setWidth w) <<< d := by
  ext i hi
  simp only [BitVec.getElem_setWidth, BitVec.getElem_shiftLeft]
  by_cases h : i < d
  · simp [h]
  · simp [h, show i < w + 1 by omega]
    exact (BitVec.getLsbD_eq_getElem (by omega)).symm

theorem setWidth_shiftXorY {w : Nat} (shifts : List Nat) (y : BitVec (w + 1)) :
    (shiftXorY shifts y).setWidth w = shiftXorY shifts (y.setWidth w) := by
  induction shifts with
  | nil => simp [shiftXorY]
  | cons d ds ih =>
    simp only [shiftXorY, setWidth_xor, setWidth_shiftLeft, ih]

/-- Twisted Silicon Ternary Odometer parametric in any strictly-positive shift list:
    m = y ^^^ (y - 1)
    T_shifts(x, y) = (x ^^^ ((x ^^^ y) &&& m) ^^^ ⨁_{d ∈ shifts} (y <<< d),  y ^^^ (x &&& m)). -/
def ternPoly (shifts : List Nat) : TFunc2 where
  eval w s :=
    let x := s.1
    let y := s.2
    let m := zeroMask y
    (x ^^^ ((x ^^^ y) &&& m) ^^^ shiftXorY shifts y,
     y ^^^ (x &&& m))
  compat w s := by
    rcases s with ⟨x, y⟩
    simp only [truncState]
    apply Prod.ext
    · simp only [setWidth_xor, setWidth_and, setWidth_zeroMask, setWidth_shiftXorY]
    · simp only [setWidth_xor, setWidth_and, setWidth_zeroMask]

/-- Order-3 element of S4 \ D4: R(a, b) = (b, a ⊕ b). -/
def rot3 (p : Fiber) : Fiber := (p.2, xor p.1 p.2)

def shiftBit (shifts : List Nat) (w : Nat) (y0 : BitVec w) : Bool :=
  xorList (fun d => if d ≤ w then y0.getLsbD (w - d) else false) shifts

/-- Exact Hamming weight (popcount) of a BitVec w. -/
def popcount : {w : Nat} → BitVec w → Nat
  | 0, _ => 0
  | w + 1, x => (if x.getLsbD w then 1 else 0) + popcount (x.setWidth w)

/-- Binomial coefficient (standard Pascal recursion). -/
def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

/-- Sharpness Decoy Counterexample for Family II:
    Replacing (y <<< 1) by (x <<< 1) agrees with C(w,k) * 3^k for ALL w = 1, 2, 3, 4,
    yet BREAKS at w = 5: state (0#5, 9#5) has EXACT period 18 (not a power of 3)! -/
def ternSharpX (w : Nat) (s : State w) : State w :=
  let m := zeroMask s.2
  (s.1 ^^^ ((s.1 ^^^ s.2) &&& m) ^^^ (s.1 <<< 1),
   s.2 ^^^ (s.1 &&& m))

/-- Hybrid S4 map combining order-3 (3,1) at bit 0 with D4 4-cycle quadrupling
    at all higher bits w >= 1:
    Exact cycle spectrum for EVERY w >= 1 is {4^(w-1), 3 * 4^(w-1)}! -/
def hybridZ {w : Nat} (x y : BitVec w) : BitVec w :=
  ((x &&& y) &&& ~~~(1#w)) ||| ((y ^^^ 1#w) &&& 1#w)

def hybridMaskHi {w : Nat} (x y : BitVec w) : BitVec w :=
  let z := hybridZ x y
  ((z + 1#w) ^^^ z) &&& ~~~(1#w)

def hybridTwoCycle : TFunc2 where
  eval w s :=
    let x := s.1
    let y := s.2
    let m := hybridMaskHi x y
    (((x ^^^ (y &&& m)) &&& ~~~(1#w)) ||| (y &&& 1#w),
     ((y ^^^ m) &&& ~~~(1#w)) ||| ((x ^^^ y) &&& 1#w))
  compat w s := by
    rcases s with ⟨x, y⟩
    have hnot1 : (~~~(1#(w + 1))).setWidth w = ~~~(1#w) := by
      ext i hi; simp
    have hor : ∀ a b : BitVec (w + 1), (a ||| b).setWidth w = a.setWidth w ||| b.setWidth w := by
      intro a b; ext i hi; simp
    have hz : (hybridZ x y).setWidth w = hybridZ (x.setWidth w) (y.setWidth w) := by
      simp only [hybridZ, hor, setWidth_and, setWidth_xor, hnot1, setWidth_ofNat]
    have hm : (hybridMaskHi x y).setWidth w = hybridMaskHi (x.setWidth w) (y.setWidth w) := by
      simp only [hybridMaskHi, setWidth_and, setWidth_xor, setWidth_add, setWidth_ofNat, hnot1, hz]
    simp only [truncState]
    apply Prod.ext <;> simp only [hor, setWidth_and, setWidth_xor, hnot1, setWidth_ofNat, hm]

/-- Trigger state for the two cycles at width w + 1:
    bit 0 is (c, 0), and all bits 1..w are (1, 1)! -/
def hybridTrig (c : Bool) : (w : Nat) → State (w + 1)
  | 0 => (BitVec.cons c 0#0, 0#1)
  | w + 1 => liftState (true, true) (hybridTrig c w)

end CoupledS4TFunction
