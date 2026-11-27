/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions (`MortonCarryMonodromyRenorm`)

All definitions and helper lemmas needed to state the headline theorems.
-/

namespace Dynsil4.CMR

/-! ## Section 0: Self-Contained Iteration & Exact Period Primitives -/

/-- `iter f k x` is the `k`-fold iterate `f^k(x)`. -/
def iter {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | k + 1, x => f (iter f k x)

/-- `HasExactPeriod f x P` means `P` is the exact minimal positive period of `x` under `f`. -/
def HasExactPeriod {α : Type} (f : α → α) (x : α) (P : Nat) : Prop :=
  0 < P ∧ iter f P x = x ∧ ∀ t, 0 < t → t < P → iter f t x ≠ x

/-! ## Section 1: Radix-B Digit Permutations & Carry-Coupled Word Lift -/

/-- A bijection on radix-`B` digits `{0, ..., B - 1}` (represented on `Nat` with explicit bounds). -/
structure DigitPerm (B : Nat) where
  toFun : Nat → Nat
  invFun : Nat → Nat
  h_lt : ∀ a, a < B → toFun a < B
  h_inv_lt : ∀ a, a < B → invFun a < B
  h_left : ∀ a, a < B → invFun (toFun a) = a
  h_right : ∀ a, a < B → toFun (invFun a) = a

namespace DigitPerm

def id (B : Nat) : DigitPerm B where
  toFun := fun a => a
  invFun := fun a => a
  h_lt := fun _ h => h
  h_inv_lt := fun _ h => h
  h_left := fun _ _ => rfl
  h_right := fun _ _ => rfl

def comp {B : Nat} (f g : DigitPerm B) : DigitPerm B where
  toFun := fun a => f.toFun (g.toFun a)
  invFun := fun a => g.invFun (f.invFun a)
  h_lt := fun a ha => f.h_lt _ (g.h_lt a ha)
  h_inv_lt := fun a ha => g.h_inv_lt _ (f.h_inv_lt a ha)
  h_left := fun a ha => by rw [f.h_left _ (g.h_lt a ha), g.h_left a ha]
  h_right := fun a ha => by rw [g.h_right _ (f.h_inv_lt a ha), f.h_right a ha]

def pow {B : Nat} (π : DigitPerm B) : Nat → DigitPerm B
  | 0 => DigitPerm.id B
  | k + 1 => DigitPerm.comp π (pow π k)

end DigitPerm

/-- Low-digit step `τ_π(a) = (π(a) + 1) mod B`. -/
def tau (B : Nat) (π : DigitPerm B) (a : Nat) : Nat :=
  (π.toFun a + 1) % B

/-- Digit-wise lift of `π : DigitPerm B` to `n` radix-`B` digits (`z < B^n`). -/
def wordPerm (B : Nat) (π : DigitPerm B) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, z => π.toFun (z % B) + B * wordPerm B π n (z / B)

/-- The carry-coupled radix-`B` dynamical step: `F_{π, n}(z) = (Π_n(z) + 1) mod B^n`. -/
def step (B : Nat) (π : DigitPerm B) (n z : Nat) : Nat :=
  (wordPerm B π n z + 1) % (B ^ n)

/-! ## Section 2: Core Reusable Mechanism — Carry-Monodromy Renormalization (CMR) Engine -/

/--
Finite Carry-Cycle Certificate for `π : DigitPerm B`:
Certifies that starting from the post-carry basepoint `0`, `tau B π` takes `L - 1` carry-free
steps (`π(τ^r(0)) < B - 1`) and emits its unique carry (`π(τ^{L-1}(0)) = B - 1`) at step `L - 1`.
-/
structure CarryCycleCert (B : Nat) (π : DigitPerm B) (L : Nat) : Prop where
  hL : 0 < L
  h_no_carry : ∀ r, r < L - 1 → π.toFun (iter (tau B π) r 0) < B - 1
  h_carry : π.toFun (iter (tau B π) (L - 1) 0) = B - 1

/--
**Finite Renormalization Automaton (`RenormAutomaton B S`):**
A finite-state certificate of `S` digit bijections closed under Carry-Monodromy Renormalization
`π_s ↦ π_s^{L_s} = π_{next s}`.
-/
structure RenormAutomaton (B S : Nat) where
  perm : Fin S → DigitPerm B
  len : Fin S → Nat
  next : Fin S → Fin S
  cert : ∀ s, CarryCycleCert B (perm s) (len s)
  closure : ∀ s a, a < B → ((perm s).pow (len s)).toFun a = (perm (next s)).toFun a

/-- Exact predicted period product from a finite `RenormAutomaton` at width `n`. -/
def RenormAutomaton.orbitProd {B S : Nat} (A : RenormAutomaton B S) : Fin S → Nat → Nat
  | _, 0 => 1
  | s, n + 1 => A.len s * A.orbitProd (A.next s) n

/-! ## Section 3: d-Dimensional Morton Cyclic Coordinate Rotation & Native `BitVec (d * n)` Bridge -/

theorem nat_div_eq_one {a b : Nat} (h1 : b ≤ a) (h2 : a < 2 * b) : a / b = 1 := by
  have hb : 0 < b := by omega
  have hsub : a - b < b := by omega
  have hrew : a = (a - b) + b * 1 := by omega
  calc a / b = ((a - b) + b * 1) / b := by rw [← hrew]
    _ = (a - b) / b + 1 := Nat.add_mul_div_left (a - b) 1 hb
    _ = 0 + 1 := by rw [Nat.div_eq_of_lt hsub]
    _ = 1 := rfl

theorem nat_mod_eq_sub {a b : Nat} (h1 : b ≤ a) (h2 : a < 2 * b) : a % b = a - b := by
  have hdiv := nat_div_eq_one h1 h2
  have hdm := Nat.div_add_mod a b
  rw [hdiv, Nat.mul_one] at hdm
  omega

theorem two_pow_eq_two_mul_pred (d : Nat) (hd : 1 ≤ d) :
    2 ^ d = 2 * 2 ^ (d - 1) := by
  have hd_eq : d = (d - 1) + 1 := by omega
  calc 2 ^ d = 2 ^ ((d - 1) + 1) := by rw [← hd_eq]
    _ = 2 ^ (d - 1) * 2 := Nat.pow_succ 2 (d - 1)
    _ = 2 * 2 ^ (d - 1) := Nat.mul_comm _ _

/-- `rotDigit d a` cyclically rotates a `d`-bit Morton digit left by 1 bit:
    bit `i` moves to bit `(i + 1) mod d`. -/
def rotDigit (d a : Nat) : Nat :=
  (2 * a) % (2 ^ d) + (2 * a) / (2 ^ d)

/-- Inverse of `rotDigit d`: cyclic right rotation of a `d`-bit digit by 1 bit. -/
def rotDigitInv (d a : Nat) : Nat :=
  a / 2 + (a % 2) * (2 ^ (d - 1))

theorem rotDigit_eq_branch (d : Nat) (hd : 1 ≤ d) (a : Nat) (ha : a < 2 ^ d) :
    rotDigit d a = if a < 2 ^ (d - 1) then 2 * a else 2 * a - 2 ^ d + 1 := by
  simp only [rotDigit]
  have hpow := two_pow_eq_two_mul_pred d hd
  split
  · rename_i hhi
    have h1 : 2 * a < 2 ^ d := by omega
    rw [Nat.mod_eq_of_lt h1, Nat.div_eq_of_lt h1, Nat.add_zero]
  · rename_i hhi
    have hge : 2 ^ d ≤ 2 * a := by omega
    have hlt2 : 2 * a < 2 * (2 ^ d) := by omega
    rw [nat_mod_eq_sub hge hlt2, nat_div_eq_one hge hlt2]

theorem rotDigit_lt (d : Nat) (hd : 1 ≤ d) (a : Nat) (ha : a < 2 ^ d) :
    rotDigit d a < 2 ^ d := by
  rw [rotDigit_eq_branch d hd a ha]
  have hpow := two_pow_eq_two_mul_pred d hd
  split <;> omega

theorem rotDigitInv_lt (d : Nat) (hd : 1 ≤ d) (a : Nat) (ha : a < 2 ^ d) :
    rotDigitInv d a < 2 ^ d := by
  simp only [rotDigitInv]
  have hpow := two_pow_eq_two_mul_pred d hd
  have hmod : a % 2 < 2 := Nat.mod_lt a (by omega)
  by_cases h0 : a % 2 = 0
  · rw [h0, Nat.zero_mul, Nat.add_zero]; omega
  · have h1 : a % 2 = 1 := by omega
    rw [h1, Nat.one_mul]; omega

theorem rotDigit_left_inv (d : Nat) (hd : 1 ≤ d) (a : Nat) (ha : a < 2 ^ d) :
    rotDigitInv d (rotDigit d a) = a := by
  rw [rotDigit_eq_branch d hd a ha]
  simp only [rotDigitInv]
  have hpow := two_pow_eq_two_mul_pred d hd
  split
  · have hm : (2 * a) % 2 = 0 := by omega
    have hd2 : (2 * a) / 2 = a := by omega
    rw [hm, hd2, Nat.zero_mul, Nat.add_zero]
  · rename_i hhi
    have hge : 2 ^ (d - 1) ≤ a := by omega
    have hrew : 2 * a - 2 ^ d + 1 = 2 * (a - 2 ^ (d - 1)) + 1 := by omega
    rw [hrew]
    have hm : (2 * (a - 2 ^ (d - 1)) + 1) % 2 = 1 := by omega
    have hd2 : (2 * (a - 2 ^ (d - 1)) + 1) / 2 = a - 2 ^ (d - 1) := by omega
    rw [hm, hd2, Nat.one_mul]; omega

theorem rotDigit_right_inv (d : Nat) (hd : 1 ≤ d) (a : Nat) (ha : a < 2 ^ d) :
    rotDigit d (rotDigitInv d a) = a := by
  have hlt := rotDigitInv_lt d hd a ha
  rw [rotDigit_eq_branch d hd _ hlt]
  have hpow := two_pow_eq_two_mul_pred d hd
  have hhalf : a / 2 < 2 ^ (d - 1) := by omega
  by_cases h0 : a % 2 = 0
  · have hinv : rotDigitInv d a = a / 2 := by
      simp only [rotDigitInv, h0, Nat.zero_mul, Nat.add_zero]
    simp only [hinv, hhalf, ↓reduceIte]; omega
  · have h1 : a % 2 = 1 := by omega
    have hinv : rotDigitInv d a = a / 2 + 2 ^ (d - 1) := by
      simp only [rotDigitInv, h1, Nat.one_mul]
    have hnot : ¬ (a / 2 + 2 ^ (d - 1) < 2 ^ (d - 1)) := by omega
    simp only [hinv, hnot, ↓reduceIte]; omega

/-- `rotDigitPerm d hd` is the `d`-dimensional Morton cyclic coordinate rotation on `Fin (2^d)`. -/
def rotDigitPerm (d : Nat) (hd : 1 ≤ d) : DigitPerm (2 ^ d) where
  toFun := rotDigit d
  invFun := rotDigitInv d
  h_lt := rotDigit_lt d hd
  h_inv_lt := rotDigitInv_lt d hd
  h_left := rotDigit_left_inv d hd
  h_right := rotDigit_right_inv d hd

/-- Phase-tracking predicate characterizing the Flag-Helix set (`(d+1)^n` elements inside `Fin (2^(dn))`). -/
def isFlagHelixPhase (d : Nat) (hd : 1 ≤ d) (phi : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, z =>
    let dig := z % (2 ^ d)
    let unrot := iter (rotDigitInv d) phi dig
    if ((unrot + 1) &&& unrot) == 0 then
      let r := Nat.log2 (unrot + 1)
      isFlagHelixPhase d hd (phi + r) n (z / (2 ^ d))
    else
      false

def isFlagHelix (d : Nat) (hd : 1 ≤ d) (n z : Nat) : Bool :=
  isFlagHelixPhase d hd 0 n z

/-- 2D Morton coordinate swap `S_2 : DigitPerm 4` (`0 ↔ 0, 1 ↔ 2, 3 ↔ 3`). -/
abbrev swap2D : DigitPerm 4 := rotDigitPerm 2 (by omega)

/-- Predicate: all `n` base-4 digits of `h` are diagonal (`0` or `3`, i.e., `x = y`). -/
def allDiag2D : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, h => (h % 4 == 0 || h % 4 == 3) && allDiag2D n (h / 4)

/-- Fiber-shift map for 2D Morton swap: maps a state on `a ∈ {0, 1, 3}` forward to `{0} × Fin (4^n)`. -/
def shiftToFiber2D (n a h : Nat) : Nat :=
  if a == 0 then h
  else if a == 3 then step 4 swap2D n h
  else (h + 1) % (4 ^ n)

/-- Exact recursive closed-form period of ANY `z < 4^n` under 2D Morton swap `+ 1`. -/
def period2D : Nat → Nat → Nat
  | 0, _ => 1
  | n + 1, z =>
    if z % 4 == 2 then
      if allDiag2D n (z / 4) then 1 else 2
    else
      3 * period2D n (shiftToFiber2D n (z % 4) (z / 4))

/-- D3: **Delayed-Fracture Trap (`B = 8`, `π_delay = (0, 1, 2, 4, 5, 6, 7, 3)`):**
    Has order `5` and a 3-state renormalization cycle `π^1 → π^3 → π^4 → π^1` with lengths `(8, 8, 4)`.
    Stays FULL-PERIOD at `n = 1` (`8`) and `n = 2` (`64`), then FRACTURES at `n = 3` (`256 < 512`)! -/
def piDelayFun : Nat → Nat
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 5 | 5 => 6 | 6 => 7 | 7 => 3 | x => x

def piDelayInv : Nat → Nat
  | 0 => 0 | 1 => 1 | 2 => 2 | 4 => 3 | 5 => 4 | 6 => 5 | 7 => 6 | 3 => 7 | x => x

def piDelay : DigitPerm 8 where
  toFun := piDelayFun
  invFun := piDelayInv
  h_lt := by intro a ha; revert a; decide
  h_inv_lt := by intro a ha; revert a; decide
  h_left := by intro a ha; revert a; decide
  h_right := by intro a ha; revert a; decide

theorem piDelay_cert0 : CarryCycleCert 8 piDelay 8 where
  hL := by omega
  h_no_carry := by intro r hr; revert r; decide
  h_carry := by decide

theorem piDelay_cert1 : CarryCycleCert 8 (piDelay.pow 3) 8 where
  hL := by omega
  h_no_carry := by intro r hr; revert r; decide
  h_carry := by decide

theorem piDelay_cert2 : CarryCycleCert 8 (piDelay.pow 4) 4 where
  hL := by omega
  h_no_carry := by intro r hr; revert r; decide
  h_carry := by decide

def piDelayAutomaton : RenormAutomaton 8 3 where
  perm := fun s =>
    if s.val == 0 then piDelay
    else if s.val == 1 then piDelay.pow 3
    else piDelay.pow 4
  len := fun s => if s.val == 2 then 4 else 8
  next := fun s => ⟨(s.val + 1) % 3, Nat.mod_lt _ (by omega)⟩
  cert := fun s => by
    cases s with | mk v hv =>
    have : v = 0 ∨ v = 1 ∨ v = 2 := by omega
    rcases this with rfl | rfl | rfl
    · exact piDelay_cert0
    · exact piDelay_cert1
    · exact piDelay_cert2
  closure := fun s a ha => by
    cases s with | mk v hv =>
    have : v = 0 ∨ v = 1 ∨ v = 2 := by omega
    rcases this with rfl | rfl | rfl
    · have h : ∀ x, x < 8 → (piDelay.pow 8).toFun x = (piDelay.pow 3).toFun x := by decide
      exact h a ha
    · have h : ∀ x, x < 8 → ((piDelay.pow 3).pow 8).toFun x = (piDelay.pow 4).toFun x := by decide
      exact h a ha
    · have h : ∀ x, x < 8 → ((piDelay.pow 4).pow 4).toFun x = piDelay.toFun x := by decide
      simpa using h a ha

end Dynsil4.CMR
