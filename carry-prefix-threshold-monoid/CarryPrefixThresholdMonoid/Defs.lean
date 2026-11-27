/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions (`carry-prefix-threshold-monoid`)

Carry-lookahead prefix monoid with the threshold-step semigroup: definitions and sorry-free helper lemmas (pure Lean 4 `Init`, zero Mathlib).
-/

namespace SiliconCarryMonoid


-- ============================================================================
-- 0. Exact Euclidean Floor-Division Primitives (Pure Core Lean 4)
-- ============================================================================

theorem natCast_mul_int (a b : Nat) : ((a * b : Nat) : Int) = (a : Int) * (b : Int) := rfl

class PrefixSemigroup (M : Type u) where
  mul : M → M → M
  mul_assoc : ∀ a b c : M, mul (mul a b) c = mul a (mul b c)

class PrefixMonoid (M : Type u) extends PrefixSemigroup M where
  one : M
  one_mul : ∀ a : M, mul one a = a
  mul_one : ∀ a : M, mul a one = a

/-- Arbitrary non-empty binary parallel-prefix tree (ripple, Sklansky, Kogge-Stone, etc.). -/
inductive PrefixTree (α : Type u) where
  | leaf (a : α) : PrefixTree α
  | node (lo hi : PrefixTree α) : PrefixTree α
  deriving Repr, DecidableEq

namespace PrefixTree


def fringe : PrefixTree α → List α
  | .leaf a => [a]
  | .node lo hi => lo.fringe ++ hi.fringe

def width : PrefixTree α → Nat
  | .leaf _ => 1
  | .node lo hi => lo.width + hi.width

/-- Parallel-prefix evaluation: upper block composed after lower block (`hi ∘ lo`). -/
def eval [PrefixSemigroup M] (enc : α → M) : PrefixTree α → M
  | .leaf a => enc a
  | .node lo hi => PrefixSemigroup.mul (hi.eval enc) (lo.eval enc)

/-- Sequential ripple-carry evaluation of a non-empty list in any semigroup. -/
def rippleNonempty [PrefixSemigroup M] : M → List M → M
  | x, [] => x
  | x, y :: ys => PrefixSemigroup.mul (rippleNonempty y ys) x

/-- Sequential ripple-carry evaluation of any list in a monoid. -/
def rippleMonoid [PrefixMonoid M] : List M → M
  | [] => PrefixMonoid.one
  | x :: xs => PrefixSemigroup.mul (rippleMonoid xs) x

end PrefixTree


-- ============================================================================
-- 2. Exact Affine-Floor Monoid M_div (Mixed-Radix / Multi-Input / Signed-Borrow)
-- ============================================================================

/-- Exact block carry-transfer operator `c ↦ ⌊(c + sum) / mod⌋` with `mod > 0`. -/
structure DivElem where
  mod : Nat
  mod_pos : 0 < mod
  sum : Int
  deriving DecidableEq

namespace DivElem


def act (d : DivElem) (c : Int) : Int :=
  (c + d.sum) / (d.mod : Int)

def one : DivElem := ⟨1, Nat.one_pos, 0⟩

def comp (hi lo : DivElem) : DivElem :=
  ⟨lo.mod * hi.mod, Nat.mul_pos lo.mod_pos hi.mod_pos, lo.sum + (lo.mod : Int) * hi.sum⟩

theorem comp_assoc (a b c : DivElem) : (a.comp b).comp c = a.comp (b.comp c) := by
  cases a; cases b; cases c
  simp only [comp, DivElem.mk.injEq]
  constructor
  · exact (Nat.mul_assoc _ _ _).symm
  · rw [natCast_mul_int, Int.mul_add, Int.mul_assoc]
    omega

theorem one_comp (a : DivElem) : one.comp a = a := by
  cases a
  simp [one, comp]

theorem comp_one (a : DivElem) : a.comp one = a := by
  cases a
  simp [one, comp]

instance : PrefixMonoid DivElem where
  mul := comp
  mul_assoc := comp_assoc
  one := one
  one_mul := one_comp
  mul_one := comp_one

/-- Carry-interval invariance predicate for a block `d` on `[L, U]`. -/
def Preserves (L U : Int) (d : DivElem) : Prop :=
  ∀ c : Int, L ≤ c → c ≤ U → L ≤ d.act c ∧ d.act c ≤ U

end DivElem


-- ============================================================================
-- 3. Canonical Threshold-Step Semigroup T (Generalized (G, P) Monoid)
-- ============================================================================

/-- Elements of the Threshold-Step Semigroup `T`:
- `const q`: carry-absorbing (`c ↦ q`, generalizing Kill `const 0` and Generate `const 1`)
- `step q t`: 1-step threshold propagator (`c ↦ q + [c ≥ t]`, generalizing Propagate `step 0 1`) -/
inductive ThreshElem where
  | const (q : Int) : ThreshElem
  | step (q t : Int) : ThreshElem
  deriving DecidableEq, Repr

namespace ThreshElem


def eval : ThreshElem → Int → Int
  | .const q, _ => q
  | .step q t, c => if c ≥ t then q + 1 else q

def isConst : ThreshElem → Bool
  | .const _ => true
  | .step _ _ => false

/-- Exact silicon composition law `(hi ∘ lo)(c) = hi(lo(c))`. -/
def comp (hi lo : ThreshElem) : ThreshElem :=
  match hi, lo with
  | .const q₂, _ => .const q₂
  | .step q₂ t₂, .const q₁ => .const (if q₁ ≥ t₂ then q₂ + 1 else q₂)
  | .step q₂ t₂, .step q₁ t₁ =>
    if q₁ ≥ t₂ then .const (q₂ + 1)
    else if q₁ + 1 < t₂ then .const q₂
    else .step q₂ t₁

/-- **Theorem 3a (Exact Composition Soundness on all of `ℤ`).** -/
theorem comp_eval (hi lo : ThreshElem) (c : Int) :
    (hi.comp lo).eval c = hi.eval (lo.eval c) := by
  cases hi with
  | const q₂ => rfl
  | step q₂ t₂ =>
    cases lo with
    | const q₁ => simp [comp, eval]
    | step q₁ t₁ =>
      simp only [comp]
      by_cases h1 : q₁ ≥ t₂
      · simp only [h1, ↓reduceIte, eval]
        by_cases hc : c ≥ t₁
        · have : q₁ + 1 ≥ t₂ := by omega
          simp [hc, this]
        · simp [hc, h1]
      · by_cases h2 : q₁ + 1 < t₂
        · simp only [h1, h2, ↓reduceIte, eval]
          by_cases hc : c ≥ t₁
          · have : ¬ (q₁ + 1 ≥ t₂) := by omega
            simp [hc, this]
          · simp [hc, h1]
        · simp only [h1, h2, ↓reduceIte, eval]
          by_cases hc : c ≥ t₁
          · have : q₁ + 1 ≥ t₂ := by omega
            simp [hc, this]
          · simp [hc, h1]

/-- **Theorem 3b (Canonical Injectivity on `ℤ`).** -/
theorem eval_injective {e₁ e₂ : ThreshElem} (h : ∀ c : Int, e₁.eval c = e₂.eval c) :
    e₁ = e₂ := by
  cases e₁ with
  | const q₁ =>
    cases e₂ with
    | const q₂ =>
      have h0 := h 0
      simp [eval] at h0
      rw [h0]
    | step q₂ t₂ =>
      have hlo := h (t₂ - 1)
      have hhi := h t₂
      simp [eval] at hlo hhi
      omega
  | step q₁ t₁ =>
    cases e₂ with
    | const q₂ =>
      have hlo := h (t₁ - 1)
      have hhi := h t₁
      simp [eval] at hlo hhi
      omega
    | step q₂ t₂ =>
      have hmin := h (min t₁ t₂ - 1)
      simp only [eval] at hmin
      have h1 : ¬ (min t₁ t₂ - 1 ≥ t₁) := by omega
      have h2 : ¬ (min t₁ t₂ - 1 ≥ t₂) := by omega
      simp only [h1, h2, ↓reduceIte] at hmin
      have ht₁ := h t₁
      have ht₂ := h t₂
      simp only [eval] at ht₁ ht₂
      have hge1 : t₁ ≥ t₁ := by omega
      have hge2 : t₂ ≥ t₂ := by omega
      simp only [hge1, hge2, ↓reduceIte] at ht₁ ht₂
      have ht : t₁ = t₂ := by
        by_cases hlt : t₁ < t₂
        · have : ¬ (t₁ ≥ t₂) := by omega
          simp only [this, ↓reduceIte] at ht₁
          omega
        · by_cases hgt : t₂ < t₁
          · have : ¬ (t₂ ≥ t₁) := by omega
            simp only [this, ↓reduceIte] at ht₂
            omega
          · omega
      rw [hmin, ht]

/-- **Theorem 3c (Strict Syntactic Associativity).** -/
theorem comp_assoc (a b c : ThreshElem) : (a.comp b).comp c = a.comp (b.comp c) := by
  apply eval_injective
  intro x
  rw [comp_eval, comp_eval, comp_eval, comp_eval]

instance : PrefixSemigroup ThreshElem where
  mul := comp
  mul_assoc := comp_assoc

/-- Canonical bounded sub-semigroup `T_[L, U]` for carry interval `[L, U]`. -/
def inBounds (L U : Int) : ThreshElem → Prop
  | .const q => L ≤ q ∧ q ≤ U
  | .step q t => L ≤ q ∧ q < U ∧ L < t ∧ t ≤ U

/-- Explicit enumeration of `T_[L, U]` for `N = U - L + 1` carry states. -/
def enumBounded (L : Int) (N : Nat) : List ThreshElem :=
  let consts := (List.range N).map (fun i : Nat => ThreshElem.const (L + (i : Int)))
  let steps := (List.range (N - 1)).flatMap (fun i : Nat =>
    (List.range (N - 1)).map (fun j : Nat => ThreshElem.step (L + (i : Int)) (L + 1 + (j : Int))))
  consts ++ steps

/-- Faithful embedding of classical 2-input `(G, P)` into `T_[0, 1]`. -/
def embedClassicalGP (g p : Bool) : ThreshElem :=
  if g then .const 1 else if p then .step 0 1 else .const 0

/-- Faithful embedding of signed-borrow `(B, P)` on `{-1, 0}` into `T_[-1, 0]`. -/
def embedSignedBorrow (b p : Bool) : ThreshElem :=
  if b then .const (-1) else if p then .step (-1) 0 else .const 0

end ThreshElem


-- ============================================================================
-- 4. Super-Critical Collapse Homomorphism & Exact Sharpness Obstruction
-- ============================================================================

/-- Domain-collapse compiler from infinite `DivElem` to bounded `ThreshElem`. -/
def collapse (L U : Int) (d : DivElem) : ThreshElem :=
  let m : Int := (d.mod : Int)
  let q : Int := (L + d.sum) / m
  let r : Int := (L + d.sum) % m
  if r + (U - L) < m then .const q else .step q (L + m - r)

/-- Adjacent resonance-lock predicate for a chain of threshold elements. -/
def ResonantChain : List ThreshElem → Prop
  | [] => False
  | [.const _] => False
  | [.step _ _] => True
  | .const _ :: _ :: _ => False
  | .step _ _ :: .const _ :: _ => False
  | .step q₁ _ :: .step q₂ t₂ :: rest => q₁ + 1 = t₂ ∧ ResonantChain (.step q₂ t₂ :: rest)

/-- Single-bit threshold encoding for 3-input binary addition (`s ∈ {0, 1, 2, 3}`, `c ∈ {0, 1, 2}`). -/
def enc3Bit (s : Nat) : ThreshElem :=
  collapse 0 2 ⟨2, by omega, (s : Int)⟩

/-- Single-bit threshold encoding for signed 3-input `x + y - z` (`s ∈ {0,1,2,3}` shifted by -1, `c ∈ {-1,0,1}`). -/
def encSigned3Bit (s : Nat) : ThreshElem :=
  collapse (-1) 1 ⟨2, by omega, (s : Int) - 1⟩

/-- Local 1-bit parity-resonance predicate for 3-input digit strings `s_i ∈ {0,1,2,3}`. -/
def BitResonant3 : List Nat → Bool
  | [] => false
  | [_] => true
  | s₁ :: s₂ :: rest => (s₁ / 2 + s₂ % 2 == 1) && BitResonant3 (s₂ :: rest)

/-- Full space of all `4^w` 3-input digit strings of width `w`. -/
def allDigits3 : Nat → List (List Nat)
  | 0 => [[]]
  | w + 1 =>
    ((allDigits3 w).map (fun ds => 0 :: ds)) ++
    ((allDigits3 w).map (fun ds => 1 :: ds)) ++
    ((allDigits3 w).map (fun ds => 2 :: ds)) ++
    ((allDigits3 w).map (fun ds => 3 :: ds))

/-- Number of binary triples `(x_i, y_i, z_i) ∈ {0,1}^3` producing column sum `s_i`. -/
def digitWeight3 : Nat → Nat
  | 0 => 1
  | 1 => 3
  | 2 => 3
  | _ => 1

def stringWeight3 : List Nat → Nat
  | [] => 1
  | s :: ds => digitWeight3 s * stringWeight3 ds

def sumWeights3 : List (List Nat) → Nat
  | [] => 0
  | ds :: rest => stringWeight3 ds + sumWeights3 rest

/-- Closed-form canonical fixed point for Crandall / Mersenne feedback `G_δ(c) = ⌊(δc + S)/M⌋`. -/
def crandallFixedPoint (δ : Int) : ThreshElem → Int
  | .const q => q
  | .step q t => if δ * (q + 1) ≥ t then q + 1 else q

/-- Crandall / Mersenne dual-fixed-point band test. -/
def isCrandallDual (δ : Int) : ThreshElem → Prop
  | .const _ => False
  | .step q t => δ * q < t ∧ t ≤ δ * (q + 1)

/-- Closed-form fixed point for Fermat negative feedback `H(c) = ⌊(-c + S) / M⌋`. -/
def fermatFixedPoint : ThreshElem → Int
  | .const q => q
  | .step q t => if q + t > 0 then q else q + 1

/-- General modulo-`m` affine prefix monoid `c ↦ (a * c + r) % m`. -/
structure AffMod (m : Nat) (hm : 0 < m) where
  a : Nat
  r : Nat
  ha : a < m
  hr : r < m

namespace AffMod


def act {m : Nat} {hm : 0 < m} (x : AffMod m hm) (c : Nat) : Nat :=
  (x.a * c + x.r) % m

def one (m : Nat) (hm : 0 < m) : AffMod m hm :=
  ⟨1 % m, 0, Nat.mod_lt 1 hm, hm⟩

def comp {m : Nat} {hm : 0 < m} (hi lo : AffMod m hm) : AffMod m hm :=
  ⟨(hi.a * lo.a) % m, (hi.a * lo.r + hi.r) % m, Nat.mod_lt _ hm, Nat.mod_lt _ hm⟩

theorem comp_assoc {m : Nat} {hm : 0 < m} (x y z : AffMod m hm) :
    (x.comp y).comp z = x.comp (y.comp z) := by
  rcases x with ⟨ax, rx, hax, hrx⟩
  rcases y with ⟨ay, ry, hay, hry⟩
  rcases z with ⟨az, rz, haz, hrz⟩
  simp only [comp, AffMod.mk.injEq]
  constructor
  · rw [Nat.mul_mod (ax * ay % m) az, Nat.mod_mod, ← Nat.mul_mod,
        Nat.mul_mod ax (ay * az % m), Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]
  · rw [Nat.add_mod, Nat.mul_mod (ax * ay % m) rz, Nat.mod_mod, ← Nat.mul_mod,
        Nat.mod_mod, ← Nat.add_mod]
    rw [Nat.add_mod (ax * ((ay * rz + ry) % m)) rx,
        Nat.mul_mod ax ((ay * rz + ry) % m), Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
    congr 1
    rw [Nat.mul_add, Nat.mul_assoc]
    omega

theorem one_comp {m : Nat} {hm : 0 < m} (x : AffMod m hm) : (one m hm).comp x = x := by
  rcases x with ⟨ax, rx, hax, hrx⟩
  simp only [one, comp, AffMod.mk.injEq]
  constructor
  · rw [Nat.mul_mod (1 % m) ax, Nat.mod_mod, ← Nat.mul_mod, Nat.one_mul, Nat.mod_eq_of_lt hax]
  · rw [Nat.add_zero, Nat.mul_mod (1 % m) rx, Nat.mod_mod, ← Nat.mul_mod, Nat.one_mul,
        Nat.mod_eq_of_lt hrx]

theorem comp_one {m : Nat} {hm : 0 < m} (x : AffMod m hm) : x.comp (one m hm) = x := by
  rcases x with ⟨ax, rx, hax, hrx⟩
  simp only [one, comp, AffMod.mk.injEq]
  constructor
  · rw [Nat.mul_mod ax (1 % m), Nat.mod_mod, ← Nat.mul_mod, Nat.mul_one, Nat.mod_eq_of_lt hax]
  · rw [Nat.mul_zero, Nat.zero_add, Nat.mod_eq_of_lt hrx]

instance (m : Nat) (hm : 0 < m) : PrefixMonoid (AffMod m hm) where
  mul := comp
  mul_assoc := comp_assoc
  one := one m hm
  one_mul := one_comp
  mul_one := comp_one

/-- Single base-`b` digit slice lifted into `AffMod m hm`. -/
def baseSlice (m : Nat) (hm : 0 < m) (b d : Nat) : AffMod m hm :=
  ⟨b % m, d % m, Nat.mod_lt _ hm, Nat.mod_lt _ hm⟩

/-- Width-`w` base-`b` modulo-`m` affine element `(b^w % m, r)`. -/
def baseBlock (m : Nat) (hm : 0 < m) (b w r : Nat) (hr : r < m) : AffMod m hm :=
  ⟨b ^ w % m, r, Nat.mod_lt _ hm, hr⟩

end AffMod

end SiliconCarryMonoid
