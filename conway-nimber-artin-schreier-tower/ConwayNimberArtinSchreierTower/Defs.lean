/-
  Pure-Silicon Conway Nimber Fermat-Tower Engine &
  Universal Artin-Schreier Contraction / Block-Periodicity Mechanism
  ===================================================================
  Standalone Lean 4.36.0 (fully self-contained, zero external dependencies).
-/

namespace ConwaySilicon

/-! ## Section 1: Pure-Silicon Fermat-Tower Bit-Tree Engine (`Nim k`) -/

/-- A level-`k` Conway nimber represented as a perfect binary tree of depth `k`
    (equivalently, a `2^k`-bit word representing an element of `F_{2^(2^k)} = [0, 2^(2^k))`). -/
inductive Nim : Nat → Type where
  | bit  : Bool → Nim 0
  | pair : Nim k → Nim k → Nim (k + 1)
  deriving DecidableEq, Repr

namespace Nim

/-- Additive identity `0` in `Nim k`. -/
def zero : {k : Nat} → Nim k
  | 0     => .bit false
  | _ + 1 => .pair zero zero

/-- Multiplicative identity `1` in `Nim k`. -/
def one : {k : Nat} → Nim k
  | 0     => .bit true
  | _ + 1 => .pair zero one

/-- Half-Fermat element `H_k = 2^(2^k - 1)` in `Nim k` (leftmost/topmost 1-bit). -/
def halfFermat : {k : Nat} → Nim k
  | 0     => .bit true
  | _ + 1 => .pair halfFermat zero

/-- Fermat generator `F_k = 2^(2^k)` living in `Nim (k + 1)`. -/
def fermatGen (k : Nat) : Nim (k + 1) := .pair one zero

/-- Canonical embedding `Nim k ↪ Nim (k + 1)` into the low half. -/
def embed (x : Nim k) : Nim (k + 1) := .pair zero x

/-- Canonical upward embedding across arbitrary levels `k ≤ n`. -/
def embedLe : {k n : Nat} → k ≤ n → Nim k → Nim n
  | k, n, h, x =>
    if hEq : k = n then
      hEq ▸ x
    else
      match n, h, hEq with
      | 0, h, hEq => absurd (Nat.eq_zero_of_le_zero h) hEq
      | _ + 1, h, hEq =>
        .pair zero (embedLe (Nat.le_of_lt_succ (Nat.lt_of_le_of_ne h hEq)) x)

/-- High and low `2^k`-bit halves of a `Nim (k + 1)`. -/
def hi : Nim (k + 1) → Nim k
  | .pair a _ => a

def lo : Nim (k + 1) → Nim k
  | .pair _ b => b

/-- Basis element `2^i` inside `Nim k` (returns `zero` if `i ≥ 2^k`). -/
def pow2 : (k : Nat) → Nat → Nim k
  | 0, i     => if i = 0 then .bit true else .bit false
  | k + 1, i =>
    if i < 2 ^ k then
      .pair zero (pow2 k i)
    else
      .pair (pow2 k (i - 2 ^ k)) zero

/-- Canonical integer value `toNat : Nim k → [0, 2^(2^k))`. -/
def toNat : {k : Nat} → Nim k → Nat
  | 0, .bit b       => if b then 1 else 0
  | k + 1, .pair a b => a.toNat * 2 ^ (2 ^ k) + b.toNat

/-- Canonical inverse `ofNat k n : Nim k` reading the low `2^k` bits of `n`. -/
def ofNat : (k : Nat) → Nat → Nim k
  | 0, n     => .bit (n % 2 == 1)
  | k + 1, n => .pair (ofNat k (n / 2 ^ (2 ^ k))) (ofNat k (n % 2 ^ (2 ^ k)))

/-- Nim-addition `⊕` (bitwise XOR on bit-trees). -/
def xor : {k : Nat} → Nim k → Nim k → Nim k
  | 0, .bit a, .bit b           => .bit (Bool.xor a b)
  | _ + 1, .pair a1 a0, .pair b1 b0 => .pair (xor a1 b1) (xor a0 b0)

/-- Pure-silicon half-Fermat scaling `S_k(x) = x ⊗ H_k`:
    `S_0(x) = x`, `S_{k+1}(a, b) = (S_k(a ⊕ b), S_k(S_k(a)))`. -/
def scaleH : {k : Nat} → Nim k → Nim k
  | 0, x           => x
  | _ + 1, .pair a b => .pair (scaleH (xor a b)) (scaleH (scaleH a))

/-- Pure-silicon Conway nim-multiplication `⊗` via Fermat-block Karatsuba split:
    `(a1 F_k ⊕ a0) ⊗ (b1 F_k ⊕ b0) = ((a1⊕a0)(b1⊕b0) ⊕ a0 b0) F_k ⊕ (a0 b0 ⊕ S_k(a1 b1))`. -/
def mul : {k : Nat} → Nim k → Nim k → Nim k
  | 0, .bit a, .bit b => .bit (a && b)
  | _ + 1, .pair a1 a0, .pair b1 b0 =>
    let p0 := mul a0 b0
    let p1 := mul a1 b1
    let pm := mul (xor a0 a1) (xor b0 b1)
    .pair (xor pm p0) (xor p0 (scaleH p1))

/-- Frobenius squaring `Φ_k(x) = x ⊗ x` as a pure linear bit-tree operator. -/
def sq : {k : Nat} → Nim k → Nim k
  | 0, x           => x
  | _ + 1, .pair a b =>
    let sa := sq a
    .pair sa (xor (sq b) (scaleH sa))

/-- Iterated Frobenius `Φ_k^t(x) = x^(2^t)`. -/
def sqIter : Nat → Nim k → Nim k
  | 0, x     => x
  | t + 1, x => sq (sqIter t x)

/-- Artin-Schreier operator `℘_k(x) = x^2 ⊕ x`. -/
def wp (x : Nim k) : Nim k := xor (sq x) x

/-- Iterated Artin-Schreier operator `℘_k^m(x)`. -/
def wpIter : Nat → Nim k → Nim k
  | 0, x     => x
  | m + 1, x => wp (wpIter m x)

/-- Nimber exponentiation `x^e`. -/
def pow (x : Nim k) : Nat → Nim k
  | 0     => one
  | e + 1 => mul x (pow x e)

/-- Absolute trace `Tr_k(x) = bit_{2^k - 1}(x)` (O(k) left-spine walk). -/
def trace : {k : Nat} → Nim k → Bool
  | 0, .bit b     => b
  | _ + 1, .pair a _ => trace a

/-- Relative norm `N_{k+1} : Nim (k + 1) → Nim k`, `N(a, b) = S_k(a^2) ⊕ a b ⊕ b^2`. -/
def norm : Nim (k + 1) → Nim k
  | .pair a b => xor (xor (scaleH (sq a)) (mul a b)) (sq b)

/-- Pure-silicon norm-descent multiplicative inverse `inv x` (with `inv 0 = 0`). -/
def inv : {k : Nat} → Nim k → Nim k
  | 0, x => x
  | _ + 1, .pair a b =>
    let d := inv (norm (.pair a b))
    .pair (mul a d) (mul (xor a b) d)

/-- Bit-length of a nimber, defined structurally on `Nim k`. -/
def bitLen : {k : Nat} → Nim k → Nat
  | 0, .bit false     => 0
  | 0, .bit true      => 1
  | k + 1, .pair a b  =>
    if a = zero then bitLen b else 2 ^ k + bitLen a

/-! ### Basic `xor` vector-space laws -/

theorem xor_comm : ∀ {k : Nat} (x y : Nim k), xor x y = xor y x
  | 0, .bit a, .bit b => by cases a <;> cases b <;> rfl
  | _ + 1, .pair a1 a0, .pair b1 b0 => by
    simp [xor, xor_comm a1 b1, xor_comm a0 b0]

theorem xor_assoc : ∀ {k : Nat} (x y z : Nim k), xor (xor x y) z = xor x (xor y z)
  | 0, .bit a, .bit b, .bit c => by cases a <;> cases b <;> cases c <;> rfl
  | _ + 1, .pair a1 a0, .pair b1 b0, .pair c1 c0 => by
    simp [xor, xor_assoc a1 b1 c1, xor_assoc a0 b0 c0]

theorem xor_self : ∀ {k : Nat} (x : Nim k), xor x x = zero
  | 0, .bit a => by cases a <;> rfl
  | _ + 1, .pair a1 a0 => by simp [xor, zero, xor_self a1, xor_self a0]

theorem xor_zero : ∀ {k : Nat} (x : Nim k), xor x zero = x
  | 0, .bit a => by cases a <;> rfl
  | _ + 1, .pair a1 a0 => by simp [xor, zero, xor_zero a1, xor_zero a0]

theorem zero_xor : ∀ {k : Nat} (x : Nim k), xor zero x = x
  | 0, .bit a => by cases a <;> rfl
  | _ + 1, .pair a1 a0 => by simp [xor, zero, zero_xor a1, zero_xor a0]

instance {k : Nat} : Std.Associative (xor (k := k)) := ⟨xor_assoc⟩
instance {k : Nat} : Std.Commutative (xor (k := k)) := ⟨xor_comm⟩

theorem xor_eq_zero_iff {k : Nat} {x y : Nim k} : xor x y = zero ↔ x = y := by
  constructor
  · intro h
    calc x = xor x zero := (xor_zero x).symm
      _ = xor x (xor x y) := by rw [h]
      _ = y := by rw [← xor_assoc, xor_self, zero_xor]
  · intro h; subst h; exact xor_self x

theorem xor_left_comm {k : Nat} (x y z : Nim k) : xor x (xor y z) = xor y (xor x z) := by
  rw [← xor_assoc, xor_comm x y, xor_assoc]

theorem xor_right_comm {k : Nat} (x y z : Nim k) : xor (xor x y) z = xor (xor x z) y := by
  rw [xor_assoc, xor_comm y z, ← xor_assoc]

theorem xor_cancel_left {k : Nat} (x y : Nim k) : xor x (xor x y) = y := by
  rw [← xor_assoc, xor_self, zero_xor]

theorem xor_cancel_right {k : Nat} (x y : Nim k) : xor (xor x y) y = x := by
  rw [xor_assoc, xor_self, xor_zero]

/-! ### `scaleH` linearity -/

theorem scaleH_zero : ∀ {k : Nat}, scaleH (zero : Nim k) = zero
  | 0 => rfl
  | _ + 1 => by simp [scaleH, zero, xor_zero, scaleH_zero]

theorem scaleH_xor : ∀ {k : Nat} (x y : Nim k), scaleH (xor x y) = xor (scaleH x) (scaleH y)
  | 0, _, _ => rfl
  | _ + 1, .pair a1 a0, .pair b1 b0 => by
    simp only [xor, scaleH]
    congr 1
    · rw [← scaleH_xor]; congr 1; ac_rfl
    · rw [scaleH_xor, scaleH_xor]

/-! ### Section 2: Complete Ring & Field Laws of `Nim k` (for all `k : Nat`) -/

structure RingLaws (k : Nat) : Prop where
  mul_comm    : ∀ x y : Nim k, mul x y = mul y x
  mul_assoc   : ∀ x y z : Nim k, mul (mul x y) z = mul x (mul y z)
  mul_xor_l   : ∀ x y z : Nim k, mul (xor x y) z = xor (mul x z) (mul y z)
  mul_zero    : ∀ x : Nim k, mul x zero = zero
  mul_one     : ∀ x : Nim k, mul x one = x
  scaleH_eq   : ∀ x : Nim k, scaleH x = mul x halfFermat

theorem ringLaws_zero : RingLaws 0 where
  mul_comm := fun (.bit a) (.bit b) => by cases a <;> cases b <;> rfl
  mul_assoc := fun (.bit a) (.bit b) (.bit c) => by cases a <;> cases b <;> cases c <;> rfl
  mul_xor_l := fun (.bit a) (.bit b) (.bit c) => by cases a <;> cases b <;> cases c <;> rfl
  mul_zero := fun (.bit a) => by cases a <;> rfl
  mul_one := fun (.bit a) => by cases a <;> rfl
  scaleH_eq := fun (.bit a) => by cases a <;> rfl

/-- Helper to expand `mul (pair a1 a0) (pair b1 b0)` into canonical non-Karatsuba form
    given `RingLaws k`. -/
theorem mul_pair_expand {k : Nat} (L : RingLaws k) (a1 a0 b1 b0 : Nim k) :
    mul (.pair a1 a0) (.pair b1 b0) =
      .pair (xor (xor (mul a1 b1) (mul a1 b0)) (mul a0 b1))
            (xor (mul a0 b0) (scaleH (mul a1 b1))) := by
  have mul_xor_r : ∀ u v w : Nim k, mul u (xor v w) = xor (mul u v) (mul u w) := fun u v w => by
    rw [L.mul_comm, L.mul_xor_l, L.mul_comm v u, L.mul_comm w u]
  simp only [mul]
  congr 1
  rw [L.mul_xor_l, mul_xor_r, mul_xor_r]
  have hcancel :
      xor (xor (xor (mul a0 b0) (mul a0 b1)) (xor (mul a1 b0) (mul a1 b1))) (mul a0 b0) =
      xor (xor (mul a0 b0) (mul a0 b0)) (xor (mul a0 b1) (xor (mul a1 b0) (mul a1 b1))) := by ac_rfl
  rw [hcancel, xor_self, zero_xor]
  ac_rfl

theorem ringLaws_step {k : Nat} (L : RingLaws k) : RingLaws (k + 1) := by
  have mul_xor_r : ∀ u v w : Nim k, mul u (xor v w) = xor (mul u v) (mul u w) := fun u v w => by
    rw [L.mul_comm, L.mul_xor_l, L.mul_comm v u, L.mul_comm w u]
  have mul_scaleH_l : ∀ u v : Nim k, mul (scaleH u) v = scaleH (mul u v) := fun u v => by
    rw [L.scaleH_eq, L.scaleH_eq, L.mul_assoc, L.mul_comm halfFermat v, ← L.mul_assoc]
  have mul_scaleH_r : ∀ u v : Nim k, mul u (scaleH v) = scaleH (mul u v) := fun u v => by
    rw [L.scaleH_eq, L.scaleH_eq, ← L.mul_assoc]
  refine ⟨?comm, ?assoc, ?dist, ?mzero, ?mone, ?sh⟩
  · intro (.pair a1 a0) (.pair b1 b0)
    rw [mul_pair_expand L, mul_pair_expand L]
    congr 1
    · rw [L.mul_comm a1 b1, L.mul_comm a1 b0, L.mul_comm a0 b1]; ac_rfl
    · rw [L.mul_comm a0 b0, L.mul_comm a1 b1]
  · intro (.pair a1 a0) (.pair b1 b0) (.pair c1 c0)
    rw [mul_pair_expand L, mul_pair_expand L, mul_pair_expand L, mul_pair_expand L]
    congr 1
    · simp only [L.mul_xor_l, mul_xor_r, L.mul_assoc, mul_scaleH_l, mul_scaleH_r]
      ac_rfl
    · simp only [L.mul_xor_l, mul_xor_r, L.mul_assoc, scaleH_xor, mul_scaleH_l, mul_scaleH_r]
      ac_rfl
  · intro (.pair a1 a0) (.pair b1 b0) (.pair c1 c0)
    simp only [xor]
    rw [mul_pair_expand L, mul_pair_expand L, mul_pair_expand L]
    simp only [xor, L.mul_xor_l, scaleH_xor]
    congr 1 <;> ac_rfl
  · intro (.pair a1 a0)
    rw [zero, mul_pair_expand L]
    simp [L.mul_zero, xor_zero, scaleH_zero]
  · intro (.pair a1 a0)
    rw [one, mul_pair_expand L]
    simp [L.mul_zero, L.mul_one, zero_xor, xor_zero, scaleH_zero]
  · intro (.pair a1 a0)
    rw [halfFermat, mul_pair_expand L]
    simp [L.mul_zero, xor_zero, zero_xor, scaleH, L.scaleH_eq, L.mul_xor_l]

theorem ringLaws : ∀ k : Nat, RingLaws k
  | 0     => ringLaws_zero
  | k + 1 => ringLaws_step (ringLaws k)

theorem mul_comm {k : Nat} (x y : Nim k) : mul x y = mul y x := (ringLaws k).mul_comm x y
theorem mul_assoc {k : Nat} (x y z : Nim k) : mul (mul x y) z = mul x (mul y z) := (ringLaws k).mul_assoc x y z
theorem mul_xor_l {k : Nat} (x y z : Nim k) : mul (xor x y) z = xor (mul x z) (mul y z) := (ringLaws k).mul_xor_l x y z
theorem mul_xor_r {k : Nat} (x y z : Nim k) : mul x (xor y z) = xor (mul x y) (mul x z) := by
  rw [mul_comm, mul_xor_l, mul_comm y x, mul_comm z x]
theorem mul_zero {k : Nat} (x : Nim k) : mul x zero = zero := (ringLaws k).mul_zero x
theorem zero_mul {k : Nat} (x : Nim k) : mul zero x = zero := by rw [mul_comm, mul_zero]
theorem mul_one {k : Nat} (x : Nim k) : mul x one = x := (ringLaws k).mul_one x
theorem one_mul {k : Nat} (x : Nim k) : mul one x = x := by rw [mul_comm, mul_one]
theorem scaleH_eq {k : Nat} (x : Nim k) : scaleH x = mul x halfFermat := (ringLaws k).scaleH_eq x

instance {k : Nat} : Std.Associative (mul (k := k)) := ⟨mul_assoc⟩
instance {k : Nat} : Std.Commutative (mul (k := k)) := ⟨mul_comm⟩

theorem mul_pair {k : Nat} (a1 a0 b1 b0 : Nim k) :
    mul (.pair a1 a0) (.pair b1 b0) =
      .pair (xor (xor (mul a1 b1) (mul a1 b0)) (mul a0 b1))
            (xor (mul a0 b0) (scaleH (mul a1 b1))) :=
  mul_pair_expand (ringLaws k) a1 a0 b1 b0

theorem one_ne_zero : ∀ {k : Nat}, (one : Nim k) ≠ zero
  | 0, h     => by cases h
  | k + 1, h => one_ne_zero (k := k) (congrArg lo h)

/-! ### Frobenius squaring & absolute trace laws -/

theorem sq_eq_mul_self : ∀ {k : Nat} (x : Nim k), sq x = mul x x
  | 0, .bit a => by cases a <;> rfl
  | _ + 1, .pair a b => by
    rw [sq, mul_pair, sq_eq_mul_self a, sq_eq_mul_self b]
    congr 1
    rw [mul_comm a b, xor_assoc, xor_self, xor_zero]

theorem sq_zero {k : Nat} : sq (zero : Nim k) = zero := by
  rw [sq_eq_mul_self, mul_zero]

theorem sq_one {k : Nat} : sq (one : Nim k) = one := by
  rw [sq_eq_mul_self, mul_one]

/-! ### Embedding homomorphism & Fermat generator laws -/

theorem embed_zero {k : Nat} : embed (zero : Nim k) = zero := rfl
theorem embed_one {k : Nat} : embed (one : Nim k) = one := rfl
theorem embed_xor {k : Nat} (x y : Nim k) : embed (xor x y) = xor (embed x) (embed y) := by
  simp [embed, xor, xor_zero]
theorem embed_mul {k : Nat} (x y : Nim k) : embed (mul x y) = mul (embed x) (embed y) := by
  simp [embed, mul_pair, zero_mul, mul_zero, xor_zero, scaleH_zero]
theorem embed_sq {k : Nat} (x : Nim k) : embed (sq x) = sq (embed x) := by
  simp [embed, sq, sq_zero, scaleH_zero, xor_zero]
theorem embed_wp {k : Nat} (x : Nim k) : embed (wp x) = wp (embed x) := by
  simp [wp, embed_xor, embed_sq]
theorem embed_inj {k : Nat} {x y : Nim k} (h : embed x = embed y) : x = y := by
  injection h

theorem pair_decomp {k : Nat} (a b : Nim k) :
    Nim.pair a b = xor (mul (fermatGen k) (embed a)) (embed b) := by
  simp [fermatGen, embed, mul_pair, one_mul, mul_zero, zero_mul, xor_zero, zero_xor, scaleH_zero, xor]

theorem mul_fermatGen_embed {k : Nat} (a : Nim k) :
    mul (fermatGen k) (embed a) = .pair a zero := by
  simp [fermatGen, embed, mul_pair, one_mul, mul_zero, zero_mul, xor_zero, zero_xor, scaleH_zero]

theorem sq_fermatGen {k : Nat} :
    sq (fermatGen k) = xor (fermatGen k) (embed halfFermat) := by
  simp [fermatGen, sq, sq_one, sq_zero, scaleH_eq, one_mul, zero_xor, embed, xor, xor_zero]

theorem wp_fermatGen {k : Nat} :
    wp (fermatGen k) = embed (halfFermat (k := k)) := by
  rw [wp, sq_fermatGen, xor_comm, xor_cancel_left]

theorem sq_xor {k : Nat} (x y : Nim k) : sq (xor x y) = xor (sq x) (sq y) := by
  rw [sq_eq_mul_self, sq_eq_mul_self, sq_eq_mul_self, mul_xor_l, mul_xor_r, mul_xor_r]
  have h : xor (xor (mul x x) (mul x y)) (xor (mul y x) (mul y y)) =
           xor (xor (mul x y) (mul x y)) (xor (mul x x) (mul y y)) := by
    rw [mul_comm y x]; ac_rfl
  rw [h, xor_self, zero_xor]

theorem sq_mul {k : Nat} (x y : Nim k) : sq (mul x y) = mul (sq x) (sq y) := by
  rw [sq_eq_mul_self, sq_eq_mul_self, sq_eq_mul_self]; ac_rfl

theorem wp_zero {k : Nat} : wp (zero : Nim k) = zero := by
  simp [wp, sq_zero, xor_zero]

theorem wp_one {k : Nat} : wp (one : Nim k) = zero := by
  simp [wp, sq_one, xor_self]

theorem wp_xor {k : Nat} (x y : Nim k) : wp (xor x y) = xor (wp x) (wp y) := by
  simp only [wp, sq_xor]; ac_rfl

theorem wpIter_zero_x {k : Nat} (m : Nat) : wpIter m (zero : Nim k) = zero := by
  induction m with
  | zero => rfl
  | succ m ih => simp [wpIter, ih, wp_zero]

theorem wpIter_xor {k : Nat} (m : Nat) (x y : Nim k) :
    wpIter m (xor x y) = xor (wpIter m x) (wpIter m y) := by
  induction m with
  | zero => rfl
  | succ m ih => simp [wpIter, ih, wp_xor]

theorem wpIter_add {k : Nat} (m n : Nat) (x : Nim k) :
    wpIter (m + n) x = wpIter m (wpIter n x) := by
  induction m with
  | zero => simp [wpIter]
  | succ m ih => rw [Nat.succ_add, wpIter, wpIter, ih]

theorem wpIter_comm {k : Nat} (m n : Nat) (x : Nim k) :
    wpIter m (wpIter n x) = wpIter n (wpIter m x) := by
  rw [← wpIter_add, Nat.add_comm, wpIter_add]

theorem embed_wpIter {k : Nat} (m : Nat) (x : Nim k) :
    embed (wpIter m x) = wpIter m (embed x) := by
  induction m with
  | zero => rfl
  | succ m ih => simp [wpIter, ih, embed_wp]

theorem sqIter_zero {k : Nat} (t : Nat) : sqIter t (zero : Nim k) = zero := by
  induction t with
  | zero => rfl
  | succ t ih => simp [sqIter, ih, sq_zero]

theorem sqIter_one {k : Nat} (t : Nat) : sqIter t (one : Nim k) = one := by
  induction t with
  | zero => rfl
  | succ t ih => simp [sqIter, ih, sq_one]

theorem sqIter_xor {k : Nat} (t : Nat) (x y : Nim k) :
    sqIter t (xor x y) = xor (sqIter t x) (sqIter t y) := by
  induction t with
  | zero => rfl
  | succ t ih => simp [sqIter, ih, sq_xor]

theorem sqIter_mul {k : Nat} (t : Nat) (x y : Nim k) :
    sqIter t (mul x y) = mul (sqIter t x) (sqIter t y) := by
  induction t with
  | zero => rfl
  | succ t ih => simp [sqIter, ih, sq_mul]

theorem sqIter_add {k : Nat} (a b : Nat) (x : Nim k) :
    sqIter (a + b) x = sqIter a (sqIter b x) := by
  induction a with
  | zero => simp [sqIter]
  | succ a ih => rw [Nat.succ_add, sqIter, sqIter, ih]

theorem embed_sqIter {k : Nat} (t : Nat) (x : Nim k) :
    embed (sqIter t x) = sqIter t (embed x) := by
  induction t with
  | zero => rfl
  | succ t ih => simp [sqIter, ih, embed_sq]

theorem hi_sq {k : Nat} (x : Nim (k + 1)) : hi (sq x) = sq (hi x) := by
  cases x; rfl

theorem hi_sqIter {k : Nat} (t : Nat) (x : Nim (k + 1)) :
    hi (sqIter t x) = sqIter t (hi x) := by
  induction t with
  | zero => rfl
  | succ t ih => simp [sqIter, hi_sq, ih]

theorem hi_xor {k : Nat} (x y : Nim (k + 1)) : hi (xor x y) = xor (hi x) (hi y) := by
  cases x; cases y; rfl

theorem hi_wp {k : Nat} (x : Nim (k + 1)) : hi (wp x) = wp (hi x) := by
  simp [wp, hi_xor, hi_sq]

theorem hi_wpIter {k : Nat} (m : Nat) (x : Nim (k + 1)) :
    hi (wpIter m x) = wpIter m (hi x) := by
  induction m with
  | zero => rfl
  | succ m ih => simp [wpIter, hi_wp, ih]

theorem trace_zero : ∀ {k : Nat}, trace (zero : Nim k) = false
  | 0 => rfl
  | k + 1 => trace_zero (k := k)

theorem trace_halfFermat : ∀ {k : Nat}, trace (halfFermat : Nim k) = true
  | 0 => rfl
  | k + 1 => trace_halfFermat (k := k)

theorem trace_xor : ∀ {k : Nat} (x y : Nim k), trace (xor x y) = Bool.xor (trace x) (trace y)
  | 0, .bit _, .bit _ => rfl
  | _ + 1, .pair a _, .pair b _ => trace_xor a b

theorem trace_sq : ∀ {k : Nat} (x : Nim k), trace (sq x) = trace x
  | 0, .bit _ => rfl
  | _ + 1, .pair a _ => trace_sq a

theorem trace_wp {k : Nat} (x : Nim k) : trace (wp x) = false := by
  rw [wp, trace_xor, trace_sq]; cases trace x <;> rfl

/-! ### Multiplicative Inverse & Field Axioms (via Artin-Schreier irreducibility) -/

theorem mul_norm_conj {k : Nat} (a b : Nim k) :
    mul (.pair a b) (.pair a (xor a b)) = embed (norm (.pair a b)) := by
  rw [mul_pair, norm, embed]
  congr 1
  · rw [mul_xor_r, mul_comm b a]; have h : xor (xor (mul a a) (xor (mul a a) (mul a b))) (mul a b) =
      xor (xor (mul a a) (mul a a)) (xor (mul a b) (mul a b)) := by ac_rfl
    rw [h, xor_self, xor_self, xor_zero]
  · rw [mul_xor_r, sq_eq_mul_self a, sq_eq_mul_self b, mul_comm b a]; ac_rfl

theorem inv_zero : ∀ {k : Nat}, inv (zero : Nim k) = zero
  | 0 => rfl
  | _ + 1 => by simp [inv, zero, xor_zero, zero_mul]

/-- Sum of Frobenius iterates `∑_{j < t} x^(2^j)`. -/
def frobSum {k : Nat} : Nat → Nim k → Nim k
  | 0, _     => zero
  | t + 1, x => xor (frobSum t x) (sqIter t x)

theorem frobSum_xor {k : Nat} (t : Nat) (x y : Nim k) :
    frobSum t (xor x y) = xor (frobSum t x) (frobSum t y) := by
  induction t with
  | zero => simp [frobSum, xor_zero]
  | succ t ih => simp only [frobSum, ih, sqIter_xor]; ac_rfl

theorem frobSum_add {k : Nat} (a b : Nat) (x : Nim k) :
    frobSum (a + b) x = xor (frobSum a x) (frobSum b (sqIter a x)) := by
  induction b with
  | zero => simp [frobSum, xor_zero]
  | succ b ih =>
    rw [← Nat.add_assoc, frobSum, frobSum, ih, ← sqIter_add, Nat.add_comm b a, xor_assoc]

theorem embed_frobSum {k : Nat} (t : Nat) (x : Nim k) :
    embed (frobSum t x) = frobSum t (embed x) := by
  induction t with
  | zero => rfl
  | succ t ih => simp [frobSum, ih, embed_xor, embed_sqIter]

theorem hi_frobSum {k : Nat} (t : Nat) (x : Nim (k + 1)) :
    hi (frobSum t x) = frobSum t (hi x) := by
  induction t with
  | zero => rfl
  | succ t ih => simp [frobSum, ih, hi_xor, hi_sqIter]

theorem sq_frobSum {k : Nat} (t : Nat) (x : Nim k) :
    sq (frobSum t x) = xor (frobSum (t + 1) x) x := by
  induction t with
  | zero => simp [frobSum, sq_zero, sqIter, xor_self, zero_xor]
  | succ s ihs =>
    rw [frobSum, sq_xor, ihs, frobSum]
    change xor (xor (frobSum (s + 1) x) x) (sqIter (s + 1) x) =
           xor (xor (frobSum (s + 1) x) (sqIter (s + 1) x)) x
    ac_rfl

theorem sqIter_fermatGen {k : Nat} (t : Nat) :
    sqIter t (fermatGen k) = xor (fermatGen k) (embed (frobSum t halfFermat)) := by
  induction t with
  | zero => simp [sqIter, frobSum, embed_zero, xor_zero]
  | succ t ih =>
    rw [sqIter, ih, sq_xor, sq_fermatGen, ← embed_sq, sq_frobSum, embed_xor]
    have : xor (xor (fermatGen k) (embed (halfFermat (k := k))))
               (xor (embed (frobSum (t + 1) halfFermat)) (embed halfFermat)) =
           xor (fermatGen k)
               (xor (embed (frobSum (t + 1) halfFermat))
                    (xor (embed halfFermat) (embed halfFermat))) := by ac_rfl
    rw [this, xor_self, xor_zero]

/-- Simultaneous induction proving both `x^(2^(2^k)) = x` and
    `Tr_k(x) = ∑_{j < 2^k} x^(2^j)` across all Fermat blocks `k`. -/
theorem frob_and_trace :
    ∀ k : Nat,
      (∀ x : Nim k, sqIter (2 ^ k) x = x) ∧
      (∀ x : Nim k, frobSum (2 ^ k) x = if trace x then one else zero)
  | 0 => by
    constructor
    · intro (.bit b); cases b <;> rfl
    · intro (.bit b); cases b <;> rfl
  | k + 1 => by
    obtain ⟨hFrob, hTr⟩ := frob_and_trace k
    have hF_step : sqIter (2 ^ k) (fermatGen k) = xor (fermatGen k) one := by
      rw [sqIter_fermatGen, hTr halfFermat, trace_halfFermat]; rfl
    have hPair_half : ∀ a b : Nim k, sqIter (2 ^ k) (.pair a b) = .pair a (xor b a) := by
      intro a b
      rw [pair_decomp a b, sqIter_xor, sqIter_mul, hF_step, ← embed_sqIter, ← embed_sqIter,
          hFrob a, hFrob b, mul_xor_l, one_mul, xor_right_comm, ← pair_decomp a b]
      simp [embed, xor, xor_zero, xor_comm]
    constructor
    · intro (.pair a b)
      have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ, Nat.mul_two]
      rw [h2, sqIter_add, hPair_half, hPair_half, xor_assoc, xor_self, xor_zero]
    · intro (.pair a b)
      have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ, Nat.mul_two]
      rw [h2, frobSum_add, hPair_half, ← frobSum_xor]
      have hdiff : xor (.pair a b) (.pair a (xor b a)) = embed a := by
        simp [xor, embed, xor_self, xor_cancel_left]
      rw [hdiff, ← embed_frobSum, hTr a, trace]
      cases trace a <;> rfl

theorem sqIter_pow2_eq_self {k : Nat} (x : Nim k) : sqIter (2 ^ k) x = x :=
  (frob_and_trace k).1 x

theorem frobSum_pow2_eq_trace {k : Nat} (x : Nim k) :
    frobSum (2 ^ k) x = if trace x then one else zero :=
  (frob_and_trace k).2 x

theorem sqIter_fermatGen_pow2 {k : Nat} :
    sqIter (2 ^ k) (fermatGen k) = xor (fermatGen k) one := by
  rw [sqIter_fermatGen, frobSum_pow2_eq_trace, trace_halfFermat]; rfl

theorem sqIter_pow2_pair {k : Nat} (a b : Nim k) :
    sqIter (2 ^ k) (.pair a b) = .pair a (xor b a) := by
  rw [pair_decomp a b, sqIter_xor, sqIter_mul, sqIter_fermatGen_pow2,
      ← embed_sqIter, ← embed_sqIter, sqIter_pow2_eq_self a, sqIter_pow2_eq_self b,
      mul_xor_l, one_mul, xor_right_comm, ← pair_decomp a b]
  simp [embed, xor, xor_zero, xor_comm]

/-! ## Section 3: `toNat`/`bitLen` Bridge, Bitwise-OR MSB Law, Trace-Gram Law & Contraction -/

theorem toNat_zero : ∀ {k : Nat}, toNat (zero : Nim k) = 0
  | 0     => rfl
  | k + 1 => by simp [zero, toNat, toNat_zero (k := k)]

theorem toNat_one : ∀ {k : Nat}, toNat (one : Nim k) = 1
  | 0     => rfl
  | k + 1 => by simp [one, toNat, toNat_zero (k := k), toNat_one (k := k)]

theorem toNat_embed {k : Nat} (x : Nim k) : (embed x).toNat = x.toNat := by
  simp [embed, toNat, toNat_zero]

theorem toNat_lt : ∀ {k : Nat} (x : Nim k), x.toNat < 2 ^ (2 ^ k)
  | 0, .bit false => by decide
  | 0, .bit true  => by decide
  | k + 1, .pair a b => by
    have ha := toNat_lt a
    have hb := toNat_lt b
    have hpow : 2 ^ (2 ^ (k + 1)) = 2 ^ (2 ^ k) * 2 ^ (2 ^ k) := by
      rw [Nat.pow_succ, Nat.mul_two, Nat.pow_add]
    rw [toNat, hpow]
    have h1 : a.toNat + 1 ≤ 2 ^ (2 ^ k) := ha
    have h2 : a.toNat * 2 ^ (2 ^ k) + b.toNat < (a.toNat + 1) * 2 ^ (2 ^ k) := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    exact Nat.lt_of_lt_of_le h2 (Nat.mul_le_mul_right _ h1)

theorem toNat_eq_zero_iff : ∀ {k : Nat} {x : Nim k}, x.toNat = 0 ↔ x = zero
  | 0, .bit false => by simp [toNat, zero]
  | 0, .bit true  => by simp [toNat, zero]
  | k + 1, .pair a b => by
    have hpos : 0 < 2 ^ (2 ^ k) := Nat.pow_pos (by decide)
    simp only [toNat, zero]
    constructor
    · intro h
      have ha0 : a.toNat = 0 := by
        by_cases ha : a.toNat = 0
        · exact ha
        · have : 1 * 2 ^ (2 ^ k) ≤ a.toNat * 2 ^ (2 ^ k) :=
            Nat.mul_le_mul_right _ (Nat.pos_of_ne_zero ha)
          omega
      have hb0 : b.toNat = 0 := by rw [ha0, Nat.zero_mul, Nat.zero_add] at h; exact h
      rw [(toNat_eq_zero_iff (k := k)).mp ha0, (toNat_eq_zero_iff (k := k)).mp hb0]
    · intro h
      have ha : a = zero := congrArg hi h
      have hb : b = zero := congrArg lo h
      rw [ha, hb, toNat_zero, Nat.zero_mul]

theorem toNat_ofNat : ∀ (k n : Nat), n < 2 ^ (2 ^ k) → (ofNat k n).toNat = n
  | 0, 0, _ => rfl
  | 0, 1, _ => rfl
  | 0, _ + 2, h => by omega
  | k + 1, n, h => by
    have hpow : 2 ^ (2 ^ (k + 1)) = 2 ^ (2 ^ k) * 2 ^ (2 ^ k) := by
      rw [Nat.pow_succ, Nat.mul_two, Nat.pow_add]
    have hpos : 0 < 2 ^ (2 ^ k) := Nat.pow_pos (by decide)
    have hq : n / 2 ^ (2 ^ k) < 2 ^ (2 ^ k) := by
      rw [Nat.div_lt_iff_lt_mul hpos]; rw [hpow] at h; exact h
    have hr : n % 2 ^ (2 ^ k) < 2 ^ (2 ^ k) := Nat.mod_lt n hpos
    simp only [ofNat, toNat, toNat_ofNat k _ hq, toNat_ofNat k _ hr]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod n (2 ^ (2 ^ k))

theorem ofNat_toNat : ∀ {k : Nat} (x : Nim k), ofNat k x.toNat = x
  | 0, .bit false => rfl
  | 0, .bit true  => rfl
  | k + 1, .pair a b => by
    have hb := toNat_lt b
    have hpos : 0 < 2 ^ (2 ^ k) := Nat.pow_pos (by decide)
    have hdiv : (a.toNat * 2 ^ (2 ^ k) + b.toNat) / 2 ^ (2 ^ k) = a.toNat := by
      rw [Nat.mul_comm a.toNat, Nat.mul_add_div hpos, Nat.div_eq_of_lt hb, Nat.add_zero]
    have hmod : (a.toNat * 2 ^ (2 ^ k) + b.toNat) % 2 ^ (2 ^ k) = b.toNat := by
      rw [Nat.mul_comm a.toNat, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
    simp only [toNat, ofNat, hdiv, hmod, ofNat_toNat a, ofNat_toNat b]

theorem toNat_inj {k : Nat} {x y : Nim k} (h : x.toNat = y.toNat) : x = y := by
  have := congrArg (ofNat k) h
  rwa [ofNat_toNat, ofNat_toNat] at this

theorem toNat_pow2 : ∀ (k i : Nat), i < 2 ^ k → (pow2 k i).toNat = 2 ^ i
  | 0, 0, _ => rfl
  | 0, _ + 1, h => by omega
  | k + 1, i, h => by
    have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ, Nat.mul_two]
    simp only [pow2]
    split
    · rename_i hlt
      simp only [toNat, toNat_zero, Nat.zero_mul, Nat.zero_add]
      exact toNat_pow2 k i hlt
    · rename_i hge
      have hlt' : i - 2 ^ k < 2 ^ k := by omega
      simp only [toNat, toNat_zero, Nat.add_zero, toNat_pow2 k (i - 2 ^ k) hlt']
      rw [← Nat.pow_add]
      congr 1; omega

theorem toNat_halfFermat : ∀ (k : Nat), (halfFermat (k := k)).toNat = 2 ^ (2 ^ k - 1)
  | 0 => rfl
  | k + 1 => by
    have hpos : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
    simp only [halfFermat, toNat, toNat_zero, Nat.add_zero, toNat_halfFermat k]
    rw [← Nat.pow_add]
    congr 1
    rw [Nat.pow_succ, Nat.mul_two]; omega

theorem toNat_fermatGen (k : Nat) : (fermatGen k).toNat = 2 ^ (2 ^ k) := by
  simp [fermatGen, toNat, toNat_one, toNat_zero]

theorem pow2_zero : ∀ (k : Nat), pow2 k 0 = one
  | 0 => rfl
  | k + 1 => by
    have hpos : 0 < 2 ^ k := Nat.pow_pos (by decide)
    simp [pow2, hpos, pow2_zero k, one]

theorem pow2_halfFermat : ∀ (k : Nat), pow2 k (2 ^ k - 1) = halfFermat
  | 0 => rfl
  | k + 1 => by
    have hpos : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
    have hnot : ¬ (2 ^ (k + 1) - 1 < 2 ^ k) := by rw [Nat.pow_succ, Nat.mul_two]; omega
    have hsub : 2 ^ (k + 1) - 1 - 2 ^ k = 2 ^ k - 1 := by rw [Nat.pow_succ, Nat.mul_two]; omega
    simp [pow2, hnot, hsub, pow2_halfFermat k, halfFermat]

theorem pow2_fermatGen (k : Nat) : pow2 (k + 1) (2 ^ k) = fermatGen k := by
  have hnot : ¬ (2 ^ k < 2 ^ k) := Nat.lt_irrefl _
  simp [pow2, hnot, Nat.sub_self, pow2_zero, fermatGen]

/-- Fundamental bit-splitting lemma for `u * 2^w + v` with `v < 2^w`. -/
theorem testBit_mul_two_pow_add (w u v j : Nat) (hv : v < 2 ^ w) :
    (u * 2 ^ w + v).testBit j = if j < w then v.testBit j else u.testBit (j - w) := by
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
  split
  · rename_i hlt
    have hw : 2 ^ w = 2 ^ j * 2 ^ (w - j) := by rw [← Nat.pow_add]; congr 1; omega
    have hpos : 0 < 2 ^ j := Nat.pow_pos (by decide)
    have hdiv' : (u * 2 ^ w + v) / 2 ^ j = u * 2 ^ (w - j) + v / 2 ^ j := by
      have hre : u * 2 ^ w = 2 ^ j * (u * 2 ^ (w - j)) := by
        rw [hw, ← Nat.mul_assoc, Nat.mul_comm u (2 ^ j), Nat.mul_assoc]
      rw [hre, Nat.mul_add_div hpos]
    rw [hdiv']
    obtain ⟨d, hd⟩ : ∃ d, w - j = d + 1 := ⟨w - j - 1, by omega⟩
    rw [hd, Nat.pow_succ, Nat.mul_comm (2 ^ d) 2, ← Nat.mul_assoc, Nat.mul_comm u 2, Nat.mul_assoc]
    have hmod : (2 * (u * 2 ^ d) + v / 2 ^ j) % 2 = (v / 2 ^ j) % 2 := by
      rw [Nat.mul_add_mod]
    simp [hmod]
  · rename_i hge
    have hj : 2 ^ j = 2 ^ w * 2 ^ (j - w) := by rw [← Nat.pow_add]; congr 1; omega
    have hpos : 0 < 2 ^ w := Nat.pow_pos (by decide)
    rw [hj, ← Nat.div_div_eq_div_mul, Nat.mul_comm u (2 ^ w),
        Nat.mul_add_div hpos, Nat.div_eq_of_lt hv, Nat.add_zero]

/-- Exact match between bit-tree `xor` and `Nat.xor` (`^^^`). -/
theorem toNat_xor : ∀ {k : Nat} (x y : Nim k), (xor x y).toNat = x.toNat ^^^ y.toNat
  | 0, .bit false, .bit false => rfl
  | 0, .bit false, .bit true  => rfl
  | 0, .bit true, .bit false  => rfl
  | 0, .bit true, .bit true   => rfl
  | k + 1, .pair a1 a0, .pair b1 b0 => by
    have ha0 := toNat_lt a0
    have hb0 := toNat_lt b0
    have hab0 : (a0.toNat ^^^ b0.toNat) < 2 ^ (2 ^ k) := Nat.xor_lt_two_pow ha0 hb0
    simp only [xor, toNat, toNat_xor a1 b1, toNat_xor a0 b0]
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_xor,
        testBit_mul_two_pow_add (2 ^ k) _ _ j hab0,
        testBit_mul_two_pow_add (2 ^ k) _ _ j ha0,
        testBit_mul_two_pow_add (2 ^ k) _ _ j hb0]
    split
    · rw [Nat.testBit_xor]
    · rw [Nat.testBit_xor]

theorem ofNat_xor (k a b : Nat) (ha : a < 2 ^ (2 ^ k)) (hb : b < 2 ^ (2 ^ k)) :
    xor (ofNat k a) (ofNat k b) = ofNat k (a ^^^ b) := by
  apply toNat_inj
  have hab : a ^^^ b < 2 ^ (2 ^ k) := Nat.xor_lt_two_pow ha hb
  rw [toNat_xor, toNat_ofNat k a ha, toNat_ofNat k b hb, toNat_ofNat k (a ^^^ b) hab]

/-! ### `bitLen` structural properties -/

theorem bitLen_zero : ∀ {k : Nat}, bitLen (zero : Nim k) = 0
  | 0     => rfl
  | k + 1 => by simp [zero, bitLen, bitLen_zero (k := k)]

theorem bitLen_eq_zero_iff : ∀ {k : Nat} {x : Nim k}, bitLen x = 0 ↔ x = zero
  | 0, .bit false => by simp [bitLen, zero]
  | 0, .bit true  => by simp [bitLen, zero]
  | k + 1, .pair a b => by
    have hpos : 0 < 2 ^ k := Nat.pow_pos (by decide)
    simp only [bitLen, zero]
    split
    · rename_i ha
      subst ha
      constructor
      · intro hb; rw [(bitLen_eq_zero_iff (k := k)).mp hb]
      · intro h; have hb : b = zero := congrArg lo h; rw [hb, bitLen_zero]
    · rename_i ha
      constructor
      · intro h; omega
      · intro h; exact absurd (congrArg hi h) ha

theorem bitLen_one : ∀ {k : Nat}, bitLen (one : Nim k) = 1
  | 0     => rfl
  | k + 1 => by simp [one, bitLen, bitLen_one (k := k)]

theorem bitLen_eq_one_iff : ∀ {k : Nat} {x : Nim k}, bitLen x = 1 ↔ x = one
  | 0, .bit false => by simp [bitLen, one]
  | 0, .bit true  => by simp [bitLen, one]
  | k + 1, .pair a b => by
    have hpos : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
    simp only [bitLen, one]
    split
    · rename_i ha
      subst ha
      constructor
      · intro hb; rw [(bitLen_eq_one_iff (k := k)).mp hb]
      · intro h; have hb : b = one := congrArg lo h; rw [hb, bitLen_one]
    · rename_i ha
      have hba : 1 ≤ bitLen a := Nat.pos_of_ne_zero (fun h => ha (bitLen_eq_zero_iff.mp h))
      constructor
      · intro h; omega
      · intro h; exact absurd (congrArg hi h) ha

theorem bitLen_le : ∀ {k : Nat} (x : Nim k), bitLen x ≤ 2 ^ k
  | 0, .bit false => by decide
  | 0, .bit true  => by decide
  | k + 1, .pair a b => by
    have ha := bitLen_le a
    have hb := bitLen_le b
    have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ, Nat.mul_two]
    simp only [bitLen]
    split <;> omega

theorem bitLen_trace_true : ∀ {k : Nat} {x : Nim k}, trace x = true → bitLen x = 2 ^ k
  | 0, .bit false, h => by cases h
  | 0, .bit true, _  => rfl
  | k + 1, .pair a b, h => by
    have ha_bl : bitLen a = 2 ^ k := bitLen_trace_true (k := k) h
    have ha_ne : a ≠ zero := by
      intro h0; rw [h0, bitLen_zero] at ha_bl
      have : 0 < 2 ^ k := Nat.pow_pos (by decide)
      omega
    simp only [bitLen, ha_ne, ↓reduceIte, ha_bl]
    rw [Nat.pow_succ, Nat.mul_two]

theorem bitLen_embed {k : Nat} (x : Nim k) : bitLen (embed x) = bitLen x := by
  simp [embed, bitLen]

theorem bitLen_pow2 : ∀ (k i : Nat), i < 2 ^ k → bitLen (pow2 k i) = i + 1
  | 0, 0, _ => rfl
  | 0, _ + 1, h => by omega
  | k + 1, i, h => by
    have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ, Nat.mul_two]
    simp only [pow2]
    split
    · rename_i hlt
      simp only [bitLen, ↓reduceIte]
      exact bitLen_pow2 k i hlt
    · rename_i hge
      have hlt' : i - 2 ^ k < 2 ^ k := by omega
      have hne : pow2 k (i - 2 ^ k) ≠ zero := by
        intro h0
        have := bitLen_pow2 k (i - 2 ^ k) hlt'
        rw [h0, bitLen_zero] at this
        omega
      simp only [bitLen, hne, ↓reduceIte, bitLen_pow2 k (i - 2 ^ k) hlt']
      omega

theorem bitLen_xor_le : ∀ {k : Nat} (x y : Nim k), bitLen (xor x y) ≤ max (bitLen x) (bitLen y)
  | 0, .bit a, .bit b => by cases a <;> cases b <;> decide
  | k + 1, .pair a1 a0, .pair b1 b0 => by
    have ih1 := bitLen_xor_le a1 b1
    have ih0 := bitLen_xor_le a0 b0
    have hle0 := bitLen_le a0
    have hle1 := bitLen_le b0
    by_cases ha : a1 = zero <;> by_cases hb : b1 = zero
    · subst ha; subst hb
      simp [xor, xor_zero, bitLen, ih0]
    · subst ha
      simp only [xor, zero_xor, bitLen, ↓reduceIte, hb]
      omega
    · subst hb
      simp only [xor, xor_zero, bitLen, ↓reduceIte, ha]
      omega
    · simp only [xor, bitLen, ha, hb, ↓reduceIte]
      split
      · have : bitLen (xor a0 b0) ≤ 2 ^ k := bitLen_le _
        omega
      · omega

theorem toNat_lt_two_pow_bitLen : ∀ {k : Nat} (x : Nim k), x.toNat < 2 ^ (bitLen x)
  | 0, .bit false => by decide
  | 0, .bit true  => by decide
  | k + 1, .pair a b => by
    simp only [toNat, bitLen]
    split
    · rename_i ha; subst ha
      simp only [toNat_zero, Nat.zero_mul, Nat.zero_add]
      exact toNat_lt_two_pow_bitLen b
    · rename_i ha
      have ha_lt := toNat_lt_two_pow_bitLen a
      have hb_lt := toNat_lt b
      rw [Nat.pow_add]
      have h1 : a.toNat * 2 ^ (2 ^ k) + b.toNat < (a.toNat + 1) * 2 ^ (2 ^ k) := by
        rw [Nat.add_mul, Nat.one_mul]; omega
      have h2 : (a.toNat + 1) * 2 ^ (2 ^ k) ≤ 2 ^ bitLen a * 2 ^ (2 ^ k) :=
        Nat.mul_le_mul_right _ ha_lt
      rw [Nat.mul_comm (2 ^ (2 ^ k))]
      exact Nat.lt_of_lt_of_le h1 h2

theorem two_pow_bitLen_sub_one_le : ∀ {k : Nat} {x : Nim k}, x ≠ zero → 2 ^ (bitLen x - 1) ≤ x.toNat
  | 0, .bit false, h => absurd rfl h
  | 0, .bit true, _  => by decide
  | k + 1, .pair a b, h => by
    simp only [toNat, bitLen]
    split
    · rename_i ha; subst ha
      have hb : b ≠ zero := fun hb0 => h (by rw [hb0]; rfl)
      simp only [toNat_zero, Nat.zero_mul, Nat.zero_add]
      exact two_pow_bitLen_sub_one_le hb
    · rename_i ha
      have ha_le := two_pow_bitLen_sub_one_le ha
      have ha_bl : 1 ≤ bitLen a := Nat.pos_of_ne_zero (fun h0 => ha (bitLen_eq_zero_iff.mp h0))
      have hsub : 2 ^ k + bitLen a - 1 = (bitLen a - 1) + 2 ^ k := by
        rw [Nat.add_sub_assoc ha_bl, Nat.add_comm]
      rw [hsub, Nat.pow_add]
      have h1 : 2 ^ (bitLen a - 1) * 2 ^ (2 ^ k) ≤ a.toNat * 2 ^ (2 ^ k) :=
        Nat.mul_le_mul_right _ ha_le
      exact Nat.le_trans h1 (Nat.le_add_right _ _)

theorem bitLen_le_iff {k : Nat} (x : Nim k) (m : Nat) : bitLen x ≤ m ↔ x.toNat < 2 ^ m := by
  constructor
  · intro h
    exact Nat.lt_of_lt_of_le (toNat_lt_two_pow_bitLen x) (Nat.pow_le_pow_right (by decide) h)
  · intro h
    by_cases hx : x = zero
    · rw [hx, bitLen_zero]; exact Nat.zero_le m
    · have hle := two_pow_bitLen_sub_one_le hx
      have hlt : 2 ^ (bitLen x - 1) < 2 ^ m := Nat.lt_of_le_of_lt hle h
      have h1 : bitLen x - 1 < m := (Nat.pow_lt_pow_iff_right (a := 2) (by decide)).mp hlt
      omega

/-! ### Theorem A: Bitwise-OR MSB Law & Trace-Gram Kronecker Law -/

theorem or_high_bit (k a b : Nat) (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    ((2 ^ k + a) ||| b) = 2 ^ k + (a ||| b) := by
  have hab : a ||| b < 2 ^ k := Nat.or_lt_two_pow ha hb
  apply Nat.eq_of_testBit_eq; intro t
  rw [Nat.testBit_or,
      ← Nat.one_mul (2 ^ k),
      testBit_mul_two_pow_add k 1 a t ha,
      testBit_mul_two_pow_add k 1 (a ||| b) t hab]
  split
  · rw [Nat.testBit_or]
  · rename_i hge
    have hb0 : b.testBit t = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (Nat.not_lt.mp hge)))
    simp [hb0]

theorem or_both_high (k a b : Nat) (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    ((2 ^ k + a) ||| (2 ^ k + b)) = 2 ^ k + (a ||| b) := by
  have hab : a ||| b < 2 ^ k := Nat.or_lt_two_pow ha hb
  apply Nat.eq_of_testBit_eq; intro t
  rw [Nat.testBit_or,
      ← Nat.one_mul (2 ^ k),
      testBit_mul_two_pow_add k 1 a t ha,
      testBit_mul_two_pow_add k 1 b t hb,
      testBit_mul_two_pow_add k 1 (a ||| b) t hab]
  split
  · rw [Nat.testBit_or]
  · simp

/-- **Theorem A1 (Bitwise-OR MSB Law):** For all `k` and all `i, j < 2^k`,
    the nim-product `2^i ⊗ 2^j` has exact bit-length `(i ||| j) + 1`. -/
theorem bitLen_mul_pow2 : ∀ (k i j : Nat), i < 2 ^ k → j < 2 ^ k →
    bitLen (mul (pow2 k i) (pow2 k j)) = (i ||| j) + 1
  | 0, 0, 0, _, _ => rfl
  | 0, _ + 1, _, hi, _ => by omega
  | 0, _, _ + 1, _, hj => by omega
  | k + 1, i, j, hi, hj => by
    have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ, Nat.mul_two]
    simp only [pow2]
    split <;> split
    · rename_i hi' hj'
      rw [mul_pair]
      simp only [zero_mul, mul_zero, xor_zero, scaleH_zero, bitLen, ↓reduceIte]
      exact bitLen_mul_pow2 k i j hi' hj'
    · rename_i hi' hj'
      have hj2 : j - 2 ^ k < 2 ^ k := by omega
      rw [mul_pair]
      simp only [zero_mul, mul_zero, xor_zero, zero_xor, scaleH_zero, bitLen]
      have hih := bitLen_mul_pow2 k i (j - 2 ^ k) hi' hj2
      have hne : mul (pow2 k i) (pow2 k (j - 2 ^ k)) ≠ zero := by
        intro h0; rw [h0, bitLen_zero] at hih; omega
      simp only [hne, ↓reduceIte, hih]
      have hor : (i ||| j) = 2 ^ k + (i ||| (j - 2 ^ k)) := by
        have h := or_high_bit k (j - 2 ^ k) i hj2 hi'
        rw [show 2 ^ k + (j - 2 ^ k) = j by omega, Nat.or_comm] at h
        rw [Nat.or_comm (j - 2 ^ k) i] at h
        exact h
      omega
    · rename_i hi' hj'
      have hi2 : i - 2 ^ k < 2 ^ k := by omega
      rw [mul_pair]
      simp only [zero_mul, mul_zero, xor_zero, zero_xor, scaleH_zero, bitLen]
      have hih := bitLen_mul_pow2 k (i - 2 ^ k) j hi2 hj'
      have hne : mul (pow2 k (i - 2 ^ k)) (pow2 k j) ≠ zero := by
        intro h0; rw [h0, bitLen_zero] at hih; omega
      simp only [hne, ↓reduceIte, hih]
      have hor : (i ||| j) = 2 ^ k + ((i - 2 ^ k) ||| j) := by
        have h := or_high_bit k (i - 2 ^ k) j hi2 hj'
        rwa [show 2 ^ k + (i - 2 ^ k) = i by omega] at h
      omega
    · rename_i hi' hj'
      have hi2 : i - 2 ^ k < 2 ^ k := by omega
      have hj2 : j - 2 ^ k < 2 ^ k := by omega
      rw [mul_pair]
      simp only [zero_mul, mul_zero, xor_zero, zero_xor, bitLen]
      have hih := bitLen_mul_pow2 k (i - 2 ^ k) (j - 2 ^ k) hi2 hj2
      have hne : mul (pow2 k (i - 2 ^ k)) (pow2 k (j - 2 ^ k)) ≠ zero := by
        intro h0; rw [h0, bitLen_zero] at hih; omega
      simp only [hne, ↓reduceIte, hih]
      have hor : (i ||| j) = 2 ^ k + ((i - 2 ^ k) ||| (j - 2 ^ k)) := by
        have h := or_both_high k (i - 2 ^ k) (j - 2 ^ k) hi2 hj2
        rwa [show 2 ^ k + (i - 2 ^ k) = i by omega, show 2 ^ k + (j - 2 ^ k) = j by omega] at h
      omega

/-- **Theorem A2 (Trace-Gram Kronecker Law):** For all `k` and all `i, j < 2^k`,
    the absolute trace Gram matrix `(G_k)_{i,j} = Tr_k(2^i ⊗ 2^j)` equals
    `[(i ||| j) = 2^k - 1]` (i.e., the k-fold Kronecker power `[[0,1],[1,1]]^{⊗k}`). -/
theorem trace_gram_kronecker : ∀ (k i j : Nat), i < 2 ^ k → j < 2 ^ k →
    trace (mul (pow2 k i) (pow2 k j)) = decide ((i ||| j) = 2 ^ k - 1)
  | 0, 0, 0, _, _ => rfl
  | 0, _ + 1, _, hi, _ => by omega
  | 0, _, _ + 1, _, hj => by omega
  | k + 1, i, j, hi, hj => by
    have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ, Nat.mul_two]
    have hpos : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
    simp only [pow2]
    split <;> split
    · rename_i hi' hj'
      rw [mul_pair]
      simp only [zero_mul, mul_zero, xor_zero, scaleH_zero, trace, trace_zero]
      have hor : (i ||| j) < 2 ^ k := Nat.or_lt_two_pow hi' hj'
      have hne : ¬ ((i ||| j) = 2 ^ (k + 1) - 1) := by omega
      simp [hne]
    · rename_i hi' hj'
      have hj2 : j - 2 ^ k < 2 ^ k := by omega
      rw [mul_pair]
      simp only [zero_mul, mul_zero, xor_zero, zero_xor, scaleH_zero, trace]
      rw [trace_gram_kronecker k i (j - 2 ^ k) hi' hj2]
      have hor : (i ||| j) = 2 ^ k + (i ||| (j - 2 ^ k)) := by
        have h := or_high_bit k (j - 2 ^ k) i hj2 hi'
        rw [show 2 ^ k + (j - 2 ^ k) = j by omega, Nat.or_comm] at h
        rw [Nat.or_comm (j - 2 ^ k) i] at h
        exact h
      rw [hor]; exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩
    · rename_i hi' hj'
      have hi2 : i - 2 ^ k < 2 ^ k := by omega
      rw [mul_pair]
      simp only [zero_mul, mul_zero, xor_zero, zero_xor, scaleH_zero, trace]
      rw [trace_gram_kronecker k (i - 2 ^ k) j hi2 hj']
      have hor : (i ||| j) = 2 ^ k + ((i - 2 ^ k) ||| j) := by
        have h := or_high_bit k (i - 2 ^ k) j hi2 hj'
        rwa [show 2 ^ k + (i - 2 ^ k) = i by omega] at h
      rw [hor]; exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩
    · rename_i hi' hj'
      have hi2 : i - 2 ^ k < 2 ^ k := by omega
      have hj2 : j - 2 ^ k < 2 ^ k := by omega
      rw [mul_pair]
      simp only [zero_mul, mul_zero, xor_zero, zero_xor, trace]
      rw [trace_gram_kronecker k (i - 2 ^ k) (j - 2 ^ k) hi2 hj2]
      have hor : (i ||| j) = 2 ^ k + ((i - 2 ^ k) ||| (j - 2 ^ k)) := by
        have h := or_both_high k (i - 2 ^ k) (j - 2 ^ k) hi2 hj2
        rwa [show 2 ^ k + (i - 2 ^ k) = i by omega, show 2 ^ k + (j - 2 ^ k) = j by omega] at h
      rw [hor]; exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩

/-- Finite XOR-sum `⨁_{i < n} f(i)` inside `Nim k`. -/
def xorSumRange {k : Nat} : Nat → (Nat → Nim k) → Nim k
  | 0, _     => zero
  | n + 1, f => xor (xorSumRange n f) (f n)

/-- Finite nim-product `⨂_{i < n} f(i)` inside `Nim k`. -/
def prodRange {k : Nat} : Nat → (Nat → Nim k) → Nim k
  | 0, _     => one
  | n + 1, f => mul (prodRange n f) (f n)

theorem xorSumRange_congr {k : Nat} (n : Nat) {f g : Nat → Nim k} (h : ∀ i < n, f i = g i) :
    xorSumRange n f = xorSumRange n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [xorSumRange, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

theorem xorSumRange_zero {k : Nat} (n : Nat) : xorSumRange n (fun _ => (zero : Nim k)) = zero := by
  induction n with
  | zero => rfl
  | succ n ih => simp [xorSumRange, ih, xor_zero]

theorem xorSumRange_xor {k : Nat} (n : Nat) (f g : Nat → Nim k) :
    xorSumRange n (fun i => xor (f i) (g i)) = xor (xorSumRange n f) (xorSumRange n g) := by
  induction n with
  | zero => simp [xorSumRange, xor_zero]
  | succ n ih => simp only [xorSumRange, ih]; ac_rfl

theorem xorSumRange_add {k : Nat} (a b : Nat) (f : Nat → Nim k) :
    xorSumRange (a + b) f = xor (xorSumRange a f) (xorSumRange b (fun i => f (a + i))) := by
  induction b with
  | zero => simp [xorSumRange, xor_zero]
  | succ b ih => rw [← Nat.add_assoc, xorSumRange, xorSumRange, ih, xor_assoc]

theorem xorSumRange_mul_left {k : Nat} (n : Nat) (c : Nim k) (f : Nat → Nim k) :
    mul c (xorSumRange n f) = xorSumRange n (fun i => mul c (f i)) := by
  induction n with
  | zero => simp [xorSumRange, mul_zero]
  | succ n ih => simp [xorSumRange, mul_xor_r, ih]

theorem xorSumRange_mul_right {k : Nat} (n : Nat) (f : Nat → Nim k) (c : Nim k) :
    mul (xorSumRange n f) c = xorSumRange n (fun i => mul (f i) c) := by
  rw [mul_comm, xorSumRange_mul_left]
  exact xorSumRange_congr n (fun i _ => mul_comm c (f i))

theorem xorSumRange_swap {k : Nat} (m n : Nat) (f : Nat → Nat → Nim k) :
    xorSumRange m (fun i => xorSumRange n (fun j => f i j)) =
    xorSumRange n (fun j => xorSumRange m (fun i => f i j)) := by
  induction m with
  | zero => simp [xorSumRange, xorSumRange_zero]
  | succ m ih => simp only [xorSumRange, ih, xorSumRange_xor]

theorem xorSumRange_wp {k : Nat} (n : Nat) (f : Nat → Nim k) :
    wp (xorSumRange n f) = xorSumRange n (fun i => wp (f i)) := by
  induction n with
  | zero => simp [xorSumRange, wp_zero]
  | succ n ih => simp [xorSumRange, wp_xor, ih]

theorem xorSumRange_sq {k : Nat} (n : Nat) (f : Nat → Nim k) :
    sq (xorSumRange n f) = xorSumRange n (fun i => sq (f i)) := by
  induction n with
  | zero => simp [xorSumRange, sq_zero]
  | succ n ih => simp [xorSumRange, sq_xor, ih]

theorem xorSumRange_single {k : Nat} (n idx : Nat) (hidx : idx < n) (f : Nat → Nim k)
    (hother : ∀ i < n, i ≠ idx → f i = zero) :
    xorSumRange n f = f idx := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [xorSumRange]
    by_cases heq : n = idx
    · subst heq
      have h0 : xorSumRange n f = zero := by
        rw [xorSumRange_congr n (fun i hi => hother i (Nat.lt_succ_of_lt hi) (by omega))]
        exact xorSumRange_zero n
      rw [h0, zero_xor]
    · have hlt : idx < n := by omega
      rw [ih hlt (fun i hi hne => hother i (Nat.lt_succ_of_lt hi) hne),
          hother n (Nat.lt_succ_self n) heq, xor_zero]

theorem prodRange_congr {k : Nat} (n : Nat) {f g : Nat → Nim k} (h : ∀ i < n, f i = g i) :
    prodRange n f = prodRange n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [prodRange, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

theorem prodRange_add {k : Nat} (a b : Nat) (f : Nat → Nim k) :
    prodRange (a + b) f = mul (prodRange a f) (prodRange b (fun i => f (a + i))) := by
  induction b with
  | zero => simp [prodRange, mul_one]
  | succ b ih => rw [← Nat.add_assoc, prodRange, prodRange, ih, mul_assoc]

/-! ### Dyadic Subspace Polynomial & Dyadic-Shell Wilson / Nim-Harmonic Theorems -/

/-- Dyadic subspace product `Π_m(X) = ⨂_{a < 2^m} (X ⊕ a)`. -/
def dyadicProd (k m : Nat) (X : Nim k) : Nim k :=
  prodRange (2 ^ m) (fun a => xor X (ofNat k a))

/-- Dyadic coset nim-harmonic sum `⨁_{a < 2^m} (X ⊕ a)^{-1}`. -/
def cosetHarmonic (k m : Nat) (X : Nim k) : Nim k :=
  xorSumRange (2 ^ m) (fun a => inv (xor X (ofNat k a)))

theorem ofNat_pow2_add (k m a : Nat) (hm : m < 2 ^ k) (ha : a < 2 ^ m) :
    ofNat k (2 ^ m + a) = xor (pow2 k m) (ofNat k a) := by
  have hpow_le : 2 ^ (m + 1) ≤ 2 ^ (2 ^ k) := Nat.pow_le_pow_right (by decide) hm
  have h2m_lt : 2 ^ m < 2 ^ (2 ^ k) :=
    Nat.lt_of_lt_of_le (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self m)) hpow_le
  have ha_lt : a < 2 ^ (2 ^ k) := Nat.lt_trans ha h2m_lt
  have hsum_lt : 2 ^ m + a < 2 ^ (2 ^ k) := by
    have : 2 ^ m + a < 2 ^ (m + 1) := by rw [Nat.pow_succ, Nat.mul_two]; omega
    exact Nat.lt_of_lt_of_le this hpow_le
  apply toNat_inj
  rw [toNat_ofNat k (2 ^ m + a) hsum_lt, toNat_xor, toNat_pow2 k m hm, toNat_ofNat k a ha_lt]
  apply Nat.eq_of_testBit_eq; intro t
  rw [Nat.testBit_xor, ← Nat.one_mul (2 ^ m), testBit_mul_two_pow_add m 1 a t ha, Nat.one_mul]
  split
  · rename_i hlt
    rw [Nat.testBit_two_pow]
    have hne : m ≠ t := by omega
    simp [hne]
  · rename_i hge
    have ha0 : a.testBit t = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (Nat.not_lt.mp hge)))
    rw [ha0, Bool.xor_false, Nat.testBit_two_pow]
    by_cases hmt : m = t
    · subst hmt; simp
    · have hgt : t - m ≠ 0 := by omega
      have h1 : (1 : Nat).testBit (t - m) = false := by
        cases htm : t - m with
        | zero => exact absurd htm hgt
        | succ d =>
          have : 1 < 2 ^ (d + 1) := by
            have := Nat.one_le_pow d 2 (by decide)
            rw [Nat.pow_succ]; omega
          exact Nat.testBit_lt_two_pow this
      simp [hmt, h1]

/-- Bitwise submask predicate `j ⊆ m` (equivalent to `C(m, j) ≡ 1 (mod 2)` by Lucas' theorem). -/
def submask (j m : Nat) : Bool := (j &&& m) == j

theorem submask_zero_left (m : Nat) : submask 0 m = true := by
  simp [submask]

theorem submask_self (m : Nat) : submask m m = true := by
  simp [submask, Nat.and_self]

theorem submask_le {j m : Nat} (h : submask j m = true) : j ≤ m := by
  simp only [submask, beq_iff_eq] at h
  rw [← h]
  exact Nat.and_le_right

theorem submask_div2 (j m : Nat) :
    submask j m = (submask (j / 2) (m / 2) && (!(j % 2 == 1) || (m % 2 == 1))) := by
  simp only [submask]
  have hiff : (j &&& m = j) ↔ ((j / 2 &&& m / 2 = j / 2) ∧ (j % 2 = 1 → m % 2 = 1)) := by
    constructor
    · intro h
      constructor
      · apply Nat.eq_of_testBit_eq; intro t
        have ht := congrArg (fun x => x.testBit (t + 1)) h
        rw [Nat.testBit_and] at ht
        simpa [Nat.testBit_div_two] using ht
      · intro hj1
        have h0 := congrArg (fun x => x.testBit 0) h
        rw [Nat.testBit_and] at h0
        simp only [Nat.testBit_zero] at h0
        rw [hj1] at h0
        simp at h0
        exact h0
    · rintro ⟨hd, hm⟩
      apply Nat.eq_of_testBit_eq; intro t
      cases t with
      | zero =>
        rw [Nat.testBit_and]
        simp only [Nat.testBit_zero]
        by_cases hj : j % 2 = 1
        · simp [hj, hm hj]
        · have : j % 2 = 0 := by omega
          simp [this]
      | succ t =>
        rw [Nat.testBit_and]
        have ht := congrArg (fun x => x.testBit t) hd
        rw [Nat.testBit_and] at ht
        simpa [Nat.testBit_div_two] using ht
  cases hL : ((j &&& m) == j) <;> cases hR : ((j / 2 &&& m / 2 == j / 2) && (!(j % 2 == 1) || (m % 2 == 1)))
  · rfl
  · exfalso
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, beq_eq_false_iff_ne] at hR hL
    have : j &&& m = j := hiff.mpr ⟨hR.1, fun hj => hR.2.resolve_left (fun hne => hne hj)⟩
    exact hL this
  · exfalso
    simp only [beq_iff_eq] at hL
    obtain ⟨hd, hmod⟩ := hiff.mp hL
    simp only [Bool.and_eq_false_iff, Bool.or_eq_false_iff, Bool.not_eq_false', beq_eq_false_iff_ne, beq_iff_eq] at hR
    rcases hR with hne | ⟨hj, hm⟩
    · exact hne hd
    · exact hm (hmod hj)
  · rfl

/-- Pure-silicon Pascal-Lucas identity mod 2:
    `submask j (m + 1) = xor (submask j m) (if j = 0 then false else submask (j - 1) m)`. -/
theorem submask_succ : ∀ (m j : Nat),
    submask j (m + 1) = Bool.xor (submask j m) (if j = 0 then false else submask (j - 1) m) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro j
    by_cases hj0 : j = 0
    · subst hj0; simp [submask_zero_left]
    · by_cases hm : m % 2 = 0
      · -- m = 2a, m + 1 = 2a + 1
        have hdiv : (m + 1) / 2 = m / 2 := by omega
        have hmod : (m + 1) % 2 = 1 := by omega
        rw [submask_div2 j (m + 1), hdiv, hmod]
        rw [submask_div2 j m, hm]
        rw [submask_div2 (j - 1) m, hm]
        by_cases hj : j % 2 = 0
        · have hj1 : (j - 1) % 2 = 1 := by omega
          simp [hj0, hj, hj1]
        · have hj1 : j % 2 = 1 := by omega
          have hj1' : (j - 1) % 2 = 0 := by omega
          have hjdiv : (j - 1) / 2 = j / 2 := by omega
          simp [hj0, hj1, hj1', hjdiv]
      · -- m = 2a + 1, m + 1 = 2(a + 1)
        have hm1 : m % 2 = 1 := by omega
        have hdiv : (m + 1) / 2 = m / 2 + 1 := by omega
        have hmod : (m + 1) % 2 = 0 := by omega
        have hlt : m / 2 < m := by omega
        rw [submask_div2 j (m + 1), hdiv, hmod]
        rw [submask_div2 j m, hm1]
        rw [submask_div2 (j - 1) m, hm1]
        by_cases hj : j % 2 = 0
        · have hjdiv_ne : j / 2 ≠ 0 := by omega
          have hj1div : (j - 1) / 2 = j / 2 - 1 := by omega
          simp only [hj0, ↓reduceIte, hj, hj1div]
          have hbool : (!(0 == 1) || (0 == 1)) = true := rfl
          have hbool2 : (!(0 == 1) || (1 == 1)) = true := rfl
          have hbool3 : (!((j - 1) % 2 == 1) || (1 == 1)) = true := by cases ((j - 1) % 2 == 1) <;> rfl
          rw [hbool, hbool2, hbool3, Bool.and_true, Bool.and_true, Bool.and_true]
          have := ih (m / 2) hlt (j / 2)
          simp only [hjdiv_ne, ↓reduceIte] at this
          exact this
        · have hj1 : j % 2 = 1 := by omega
          have hj1div : (j - 1) / 2 = j / 2 := by omega
          simp [hj0, hj1, hj1div]

/-- **Theorem C2 (Sierpiński Frobenius Expansion):**
    For ALL `k`, ALL `m : Nat`, and ALL `x ∈ Nim k`:
    `℘^m(x) = ⨁_{j ≤ m, j ⊆ m} x^(2^j)`. -/
theorem wpIter_eq_sierpinski {k : Nat} (m : Nat) (x : Nim k) :
    wpIter m x = xorSumRange (m + 1) (fun j => if submask j m then sqIter j x else zero) := by
  induction m with
  | zero => simp [wpIter, xorSumRange, submask_zero_left, sqIter, zero_xor]
  | succ m ih =>
    rw [wpIter, ih, wp, xorSumRange_sq]
    have hshift :
        xorSumRange (m + 1) (fun j => sq (if submask j m then sqIter j x else zero)) =
        xorSumRange (m + 2) (fun j => if j = 0 then zero else if submask (j - 1) m then sqIter j x else zero) := by
      have hbody : ∀ n : Nat,
          xorSumRange n (fun j => sq (if submask j m then sqIter j x else zero)) =
          xorSumRange (n + 1) (fun j => if j = 0 then zero else if submask (j - 1) m then sqIter j x else zero) := by
        intro n
        induction n with
        | zero => simp [xorSumRange, zero_xor]
        | succ n ihn =>
          simp only [xorSumRange, ihn]
          congr 1
          cases hsub : submask n m <;> simp [hsub, sq_zero, sqIter]
      exact hbody (m + 1)
    have hpad :
        xorSumRange (m + 1) (fun j => if submask j m then sqIter j x else zero) =
        xorSumRange (m + 2) (fun j => if submask j m then sqIter j x else zero) := by
      have hgt : submask (m + 1) m = false := by
        cases h : submask (m + 1) m
        · rfl
        · have := submask_le h; omega
      simp [xorSumRange, hgt, xor_zero]
    rw [hshift, hpad, ← xorSumRange_xor]
    apply xorSumRange_congr
    intro j _
    rw [submask_succ m j]
    by_cases hj0 : j = 0
    · subst hj0; simp [submask_zero_left, zero_xor]
    · simp only [hj0, ↓reduceIte]
      cases submask j m <;> cases submask (j - 1) m <;> simp [xor_zero, zero_xor, xor_self]

/-- Corollary: `℘^(2^r)(x) = x^(2^(2^r)) ⊕ x` (Frobenius-shift formula for every power of 2). -/
theorem wpIter_pow2_eq_sqIter_xor {k : Nat} (r : Nat) (x : Nim k) :
    wpIter (2 ^ r) x = xor (sqIter (2 ^ r) x) x := by
  rw [wpIter_eq_sierpinski]
  have hsplit : 2 ^ r + 1 = 1 + 2 ^ r := by omega
  have hmid : ∀ j, 0 < j → j < 2 ^ r → submask j (2 ^ r) = false := by
    intro j hj0 hjlt
    cases h : submask j (2 ^ r)
    · rfl
    · exfalso
      simp only [submask, beq_iff_eq] at h
      have hand : j &&& 2 ^ r = 0 := by
        apply Nat.eq_of_testBit_eq; intro t
        rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
        by_cases hrt : r = t
        · subst hrt; simp [Nat.testBit_lt_two_pow hjlt]
        · simp [hrt]
      rw [hand] at h
      omega
  simp only [xorSumRange, submask_self, ↓reduceIte]
  have hleft : xorSumRange (2 ^ r) (fun j => if submask j (2 ^ r) then sqIter j x else zero) = x := by
    have hpos : 0 < 2 ^ r := Nat.pow_pos (by decide)
    rw [xorSumRange_single (2 ^ r) 0 hpos _ (fun j hj hne => by
      have := hmid j (Nat.pos_of_ne_zero hne) hj
      simp [this])]
    simp [submask_zero_left, sqIter]
  rw [hleft, xor_comm]

/-! ### Powers, Lucas-Binomial Theorem, Popcount & Binary Power-Sum Collapse -/

theorem pow_add {k : Nat} (x : Nim k) (a b : Nat) : pow x (a + b) = mul (pow x a) (pow x b) := by
  induction a with
  | zero => simp [pow, one_mul]
  | succ a ih => rw [Nat.succ_add, pow, pow, ih, mul_assoc]

theorem pow_mul_two {k : Nat} (x : Nim k) (e : Nat) : pow x (e + e) = sq (pow x e) := by
  rw [pow_add, sq_eq_mul_self]

theorem sqIter_eq_pow {k : Nat} (j : Nat) (x : Nim k) : sqIter j x = pow x (2 ^ j) := by
  induction j with
  | zero => simp [sqIter, pow, mul_one]
  | succ j ih => rw [sqIter, ih, Nat.pow_succ, Nat.mul_two, pow_mul_two]

theorem pow_zero_val {k : Nat} (x : Nim k) : pow x 0 = one := rfl

theorem pow_xor_lucas {k : Nat} (d : Nat) (x y : Nim k) :
    pow (xor x y) d = xorSumRange (d + 1) (fun r => if submask r d then mul (pow x r) (pow y (d - r)) else zero) := by
  induction d with
  | zero => simp [pow, xorSumRange, submask_zero_left, zero_xor, mul_one]
  | succ d ih =>
    rw [pow, ih, mul_xor_l, xorSumRange_mul_left, xorSumRange_mul_left]
    have hx_part :
        xorSumRange (d + 1) (fun r => mul x (if submask r d then mul (pow x r) (pow y (d - r)) else zero)) =
        xorSumRange (d + 2) (fun r => if r = 0 then zero else if submask (r - 1) d then mul (pow x r) (pow y (d + 1 - r)) else zero) := by
      have hgen : ∀ n, n ≤ d + 1 →
          xorSumRange n (fun r => mul x (if submask r d then mul (pow x r) (pow y (d - r)) else zero)) =
          xorSumRange (n + 1) (fun r => if r = 0 then zero else if submask (r - 1) d then mul (pow x r) (pow y (d + 1 - r)) else zero) := by
        intro n hn
        induction n with
        | zero => simp [xorSumRange, zero_xor]
        | succ n ihn =>
          simp only [xorSumRange, ihn (Nat.le_of_lt hn)]
          congr 1
          cases hsub : submask n d <;> simp [hsub, mul_zero, pow, mul_assoc]
      exact hgen (d + 1) (Nat.le_refl _)
    have hy_part :
        xorSumRange (d + 1) (fun r => mul y (if submask r d then mul (pow x r) (pow y (d - r)) else zero)) =
        xorSumRange (d + 2) (fun r => if submask r d then mul (pow x r) (pow y (d + 1 - r)) else zero) := by
      have hgt : submask (d + 1) d = false := by
        cases h : submask (d + 1) d
        · rfl
        · have := submask_le h; omega
      conv => rhs; rw [xorSumRange]; simp [hgt, xor_zero]
      apply xorSumRange_congr
      intro r hr
      cases hsub : submask r d
      · simp [mul_zero]
      · simp only [↓reduceIte]
        have hrle : r ≤ d := submask_le hsub
        have hsub_eq : d + 1 - r = (d - r) + 1 := by omega
        rw [hsub_eq, pow]; ac_rfl
    rw [hx_part, hy_part, ← xorSumRange_xor]
    apply xorSumRange_congr
    intro r _
    rw [submask_succ d r]
    by_cases hr0 : r = 0
    · subst hr0; simp [submask_zero_left, zero_xor]
    · simp only [hr0, ↓reduceIte]
      cases submask r d <;> cases submask (r - 1) d <;> simp [xor_zero, zero_xor, xor_self]

/-- Dyadic prefix power sum `S(m, d) = ⨁_{x < 2^m} x^d`. -/
def powerSum (k m d : Nat) : Nim k :=
  xorSumRange (2 ^ m) (fun a => pow (ofNat k a) d)

/-- Binary Hamming weight (`popcount`). -/
def popcount (n : Nat) : Nat :=
  if h : n = 0 then 0 else n % 2 + popcount (n / 2)
termination_by n

theorem popcount_zero : popcount 0 = 0 := by unfold popcount; simp

theorem popcount_eq (n : Nat) (hn : n ≠ 0) : popcount n = n % 2 + popcount (n / 2) := by
  conv => lhs; unfold popcount
  simp [hn]

theorem popcount_le_of_submask : ∀ (d r : Nat), submask r d = true → popcount r ≤ popcount d := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro r hr
    by_cases hd0 : d = 0
    · subst hd0
      have hr0 : r = 0 := Nat.eq_zero_of_le_zero (submask_le hr)
      subst hr0; exact Nat.le_refl _
    · by_cases hr0 : r = 0
      · subst hr0; rw [popcount_zero]; exact Nat.zero_le _
      · rw [popcount_eq r hr0, popcount_eq d hd0]
        rw [submask_div2] at hr
        simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, beq_eq_false_iff_ne] at hr
        have hlt : d / 2 < d := by omega
        have hih := ih (d / 2) hlt (r / 2) hr.1
        have hmod : r % 2 ≤ d % 2 := by
          rcases hr.2 with hne | hd1 <;> omega
        omega

theorem popcount_lt_of_submask_lt : ∀ (d r : Nat), r < d → submask r d = true → popcount r < popcount d := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro r hlt hr
    have hd0 : d ≠ 0 := by omega
    by_cases hr0 : r = 0
    · subst hr0
      rw [popcount_zero]
      have hpos : 0 < popcount d := by
        by_cases hmod : d % 2 = 1
        · rw [popcount_eq d hd0, hmod]; omega
        · rw [popcount_eq d hd0]
          have hd2 : d / 2 ≠ 0 := by omega
          have hsub : submask 0 (d / 2) = true := submask_zero_left _
          have := ih (d / 2) (by omega) 0 (by omega) hsub
          rw [popcount_zero] at this; omega
      exact hpos
    · rw [popcount_eq r hr0, popcount_eq d hd0]
      rw [submask_div2] at hr
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, beq_eq_false_iff_ne] at hr
      have hdiv_le : r / 2 ≤ d / 2 := Nat.div_le_div_right (Nat.le_of_lt hlt)
      by_cases hdiv_eq : r / 2 = d / 2
      · have hmod_lt : r % 2 < d % 2 := by omega
        rw [hdiv_eq]; omega
      · have hdiv_lt : r / 2 < d / 2 := by omega
        have hih := ih (d / 2) (by omega) (r / 2) hdiv_lt hr.1
        have hmod : r % 2 ≤ d % 2 := by
          rcases hr.2 with hne | hd1 <;> omega
        omega

theorem popcount_two_pow_sub_one : ∀ m : Nat, popcount (2 ^ m - 1) = m
  | 0 => by simp [popcount_zero]
  | m + 1 => by
    have hne : 2 ^ (m + 1) - 1 ≠ 0 := by
      have := Nat.one_le_pow m 2 (by decide)
      rw [Nat.pow_succ]; omega
    rw [popcount_eq _ hne]
    have hmod : (2 ^ (m + 1) - 1) % 2 = 1 := by
      have := Nat.one_le_pow m 2 (by decide)
      rw [Nat.pow_succ]; omega
    have hdiv : (2 ^ (m + 1) - 1) / 2 = 2 ^ m - 1 := by
      have := Nat.one_le_pow m 2 (by decide)
      rw [Nat.pow_succ]; omega
    rw [hmod, hdiv, popcount_two_pow_sub_one m]; omega

theorem popcount_lt_of_lt_two_pow_sub_one : ∀ (m d : Nat), d < 2 ^ m - 1 → popcount d < m := by
  intro m
  induction m with
  | zero => intro d hd; omega
  | succ m ih =>
    intro d hd
    by_cases hd0 : d = 0
    · subst hd0; rw [popcount_zero]; omega
    · rw [popcount_eq d hd0]
      have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
      by_cases hmod : d % 2 = 0
      · have hdiv_le : d / 2 ≤ 2 ^ m - 1 := by omega
        by_cases heq : d / 2 = 2 ^ m - 1
        · rw [hmod, heq, popcount_two_pow_sub_one]; omega
        · have := ih (d / 2) (by omega); omega
      · have hdiv_lt : d / 2 < 2 ^ m - 1 := by omega
        have := ih (d / 2) hdiv_lt; omega

/-- Step formula for prefix power sums:
    `S(m + 1, d) = ⨁_{r < d, r ⊆ d} (2^m)^(d - r) ⊗ S(m, r)`. -/
theorem powerSum_succ (k m d : Nat) (hm : m < 2 ^ k) :
    powerSum k (m + 1) d =
      xorSumRange d (fun r => if submask r d then mul (pow (pow2 k m) (d - r)) (powerSum k m r) else zero) := by
  unfold powerSum
  have h2 : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [Nat.pow_succ, Nat.mul_two]
  rw [h2, xorSumRange_add, ← xorSumRange_xor]
  have hterm : ∀ a < 2 ^ m,
      xor (pow (ofNat k a) d) (pow (ofNat k (2 ^ m + a)) d) =
      xorSumRange d (fun r => if submask r d then mul (pow (pow2 k m) (d - r)) (pow (ofNat k a) r) else zero) := by
    intro a ha
    rw [ofNat_pow2_add k m a hm ha, xor_comm (pow2 k m), pow_xor_lucas d (ofNat k a) (pow2 k m)]
    simp only [xorSumRange, submask_self, ↓reduceIte, Nat.sub_self, pow_zero_val, mul_one]
    have hcancel : xor (pow (ofNat k a) d)
        (xor (xorSumRange d (fun r => if submask r d then mul (pow (ofNat k a) r) (pow (pow2 k m) (d - r)) else zero))
             (pow (ofNat k a) d)) =
        xorSumRange d (fun r => if submask r d then mul (pow (ofNat k a) r) (pow (pow2 k m) (d - r)) else zero) := by
      have : xor (pow (ofNat k a) d)
          (xor (xorSumRange d (fun r => if submask r d then mul (pow (ofNat k a) r) (pow (pow2 k m) (d - r)) else zero))
               (pow (ofNat k a) d)) =
          xor (xor (pow (ofNat k a) d) (pow (ofNat k a) d))
              (xorSumRange d (fun r => if submask r d then mul (pow (ofNat k a) r) (pow (pow2 k m) (d - r)) else zero)) := by ac_rfl
      rw [this, xor_self, zero_xor]
    rw [hcancel]
    apply xorSumRange_congr; intro r _
    cases submask r d
    · rfl
    · exact mul_comm _ _
  rw [xorSumRange_congr (2 ^ m) hterm, xorSumRange_swap]
  apply xorSumRange_congr; intro r _
  cases submask r d
  · simp [xorSumRange_zero]
  · simp [← xorSumRange_mul_left]

/-- **Theorem E2 (Popcount Annihilation):**
    For ALL `k`, ALL `m ≤ 2^k`, and ALL `d` with `popcount d < m`, `S(m, d) = 0`. -/
theorem powerSum_popcount_vanish (k m : Nat) (hm : m ≤ 2 ^ k) :
    ∀ d : Nat, popcount d < m → powerSum k m d = zero := by
  induction m with
  | zero => intro d hd; omega
  | succ m ih =>
    intro d hd
    rw [powerSum_succ k m d hm]
    have h0 : ∀ r < d, (if submask r d then mul (pow (pow2 k m) (d - r)) (powerSum k m r) else zero) = zero := by
      intro r hr
      cases hsub : submask r d
      · rfl
      · simp only [↓reduceIte]
        have hpc : popcount r < m := by
          have := popcount_lt_of_submask_lt d r hr hsub; omega
        rw [ih (Nat.le_of_lt hm) r hpc, mul_zero]
    rw [xorSumRange_congr d h0, xorSumRange_zero]

/-- Helper: adding `2^t` to `(2^m - 1) - 2^j` (with `t ≠ j`, both `< m`) has `popcount < m`. -/
theorem popcount_missing_bit_add_lt (m j t : Nat) (hj : j < m) (ht : t < m) (hne : t ≠ j) :
    popcount (2 ^ m - 1 - 2 ^ j + 2 ^ t) < m := by
  have hlt1 : 2 ^ j < 2 ^ m := Nat.pow_lt_pow_right (by decide) hj
  have hlt2 : 2 ^ t < 2 ^ m := Nat.pow_lt_pow_right (by decide) ht
  by_cases htj : t < j
  · -- Carry from bit t stops at bit j: value < 2^m - 1!
    have hval : 2 ^ m - 1 - 2 ^ j + 2 ^ t < 2 ^ m - 1 := by
      have : 2 ^ t < 2 ^ j := Nat.pow_lt_pow_right (by decide) htj
      omega
    exact popcount_lt_of_lt_two_pow_sub_one m _ hval
  · -- t > j: carry overflows out of bit m. Write val = 2^m + (2^t - 1 - 2^j) < 2^m + (2^m - 1).
    -- Here 2^m - 1 - 2^j + 2^t = 2^m + (2^t - 2^j - 1): bits t..m-1 become 0, bit m becomes 1,
    -- and bits 0..t-1 stay (except bit j = 0). Proved directly.
    have hgt : j < t := by omega
    have hsum : 2 ^ m - 1 - 2 ^ j + 2 ^ t = 2 ^ m + (2 ^ t - 1 - 2 ^ j) := by
      have : 2 ^ j < 2 ^ t := Nat.pow_lt_pow_right (by decide) hgt
      omega
    rw [hsum]
    -- popcount(2^m + x) = 1 + popcount(x) for x < 2^m!
    have hadd_pc : ∀ (n x : Nat), x < 2 ^ n → popcount (2 ^ n + x) = 1 + popcount x := by
      intro n
      induction n with
      | zero =>
        intro x hx
        have hx0 : x = 0 := by omega
        subst hx0
        rw [Nat.pow_zero, Nat.add_zero, popcount_eq 1 (by decide), popcount_zero]
      | succ n ihn =>
        intro x hx
        have hpos : 0 < 2 ^ (n + 1) := Nat.pow_pos (by decide)
        rw [popcount_eq (2 ^ (n + 1) + x) (by omega)]
        have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
        have hmod : (2 ^ (n + 1) + x) % 2 = x % 2 := by rw [h2, Nat.mul_add_mod]
        have hdiv : (2 ^ (n + 1) + x) / 2 = 2 ^ n + x / 2 := by rw [h2, Nat.mul_add_div (by decide)]
        rw [hmod, hdiv, ihn (x / 2) (by omega)]
        by_cases hx0 : x = 0
        · subst hx0; simp [popcount_zero]
        · rw [popcount_eq x hx0]; omega
    have hx_lt : 2 ^ t - 1 - 2 ^ j < 2 ^ m :=
      Nat.lt_of_le_of_lt (Nat.le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)) hlt2
    rw [hadd_pc m _ hx_lt]
    have hx_lt_t : 2 ^ t - 1 - 2 ^ j < 2 ^ t - 1 := by
      have : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by decide)
      have : 2 ^ j < 2 ^ t := Nat.pow_lt_pow_right (by decide) hgt
      omega
    have hpc_x : popcount (2 ^ t - 1 - 2 ^ j) < t := popcount_lt_of_lt_two_pow_sub_one t _ hx_lt_t
    omega

theorem bitLen_xorSumRange_le {k : Nat} (n B : Nat) (f : Nat → Nim k)
    (h : ∀ i < n, bitLen (f i) ≤ B) :
    bitLen (xorSumRange n f) ≤ B := by
  induction n with
  | zero => simp [xorSumRange, bitLen_zero]
  | succ n ih =>
    simp only [xorSumRange]
    have h1 := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have h2 := h n (Nat.lt_succ_self n)
    have hle := bitLen_xor_le (xorSumRange n f) (f n)
    omega

/-- Bit-extraction of a basis XOR-sum. -/
theorem testBit_xorSumRange_pow2 (n m a t : Nat) (hm : m ≤ 2 ^ n) :
    (xorSumRange m (fun u => if a.testBit u then pow2 n u else zero)).toNat.testBit t =
      (decide (t < m) && a.testBit t) := by
  induction m with
  | zero => simp [xorSumRange, toNat_zero]
  | succ m ih =>
    simp only [xorSumRange, toNat_xor, Nat.testBit_xor, ih (Nat.le_of_lt hm)]
    by_cases htm : t = m
    · subst htm
      have hlt : ¬ (t < t) := Nat.lt_irrefl t
      have hlt1 : t < t + 1 := Nat.lt_succ_self t
      simp only [hlt, hlt1, decide_false, decide_true, Bool.false_and, Bool.false_xor, Bool.true_and]
      cases hbit : a.testBit t
      · simp [toNat_zero]
      · simp only [↓reduceIte]
        rw [toNat_pow2 n t hm, Nat.testBit_two_pow_self]
    · have hright0 : (if a.testBit m then pow2 n m else zero).toNat.testBit t = false := by
        cases a.testBit m
        · simp [toNat_zero]
        · simp only [↓reduceIte]
          rw [toNat_pow2 n m hm, Nat.testBit_two_pow]
          have hne : m ≠ t := fun h => htm h.symm
          simp [hne]
      rw [hright0, Bool.xor_false]
      have hiff : (t < m) ↔ (t < m + 1) := by omega
      simp [hiff]

/-- Basis decomposition of any `x : Nim n` up to `bitLen x` bits. -/
theorem eq_xorSumRange_pow2 {n : Nat} (x : Nim n) :
    x = xorSumRange (bitLen x) (fun u => if x.toNat.testBit u then pow2 n u else zero) := by
  apply toNat_inj
  apply Nat.eq_of_testBit_eq; intro t
  rw [testBit_xorSumRange_pow2 n (bitLen x) x.toNat t (bitLen_le x)]
  by_cases ht : t < bitLen x
  · simp [ht]
  · simp only [ht, decide_false, Bool.false_and]
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (toNat_lt_two_pow_bitLen x)
      (Nat.pow_le_pow_right (by decide) (Nat.not_lt.mp ht)))

/-- Bit-length bound for multiplying any `x : Nim n` by a basis element `2^v`. -/
theorem bitLen_mul_pow2_le {n : Nat} (x : Nim n) (v B : Nat) (hv : v < 2 ^ n)
    (hB : ∀ u < bitLen x, (u ||| v) < B) :
    bitLen (mul x (pow2 n v)) ≤ B := by
  conv => lhs; rw [eq_xorSumRange_pow2 x]
  rw [xorSumRange_mul_right]
  apply bitLen_xorSumRange_le (bitLen x) B
  intro u hu
  cases x.toNat.testBit u
  · simp [zero_mul, bitLen_zero]
  · simp only [↓reduceIte]
    have hu_lt : u < 2 ^ n := Nat.lt_of_lt_of_le hu (bitLen_le x)
    rw [bitLen_mul_pow2 n u v hu_lt hv]
    exact hB u hu

/-- Aligned bitwise-OR bound: for any multiple `a * 2^s` and any `b < 2^s`,
    every `u ≤ a * 2^s` satisfies `(u ||| b) ≤ a * 2^s + b`. -/
theorem or_le_of_aligned (a s b u : Nat) (hb : b < 2 ^ s) (hu : u ≤ a * 2 ^ s) :
    (u ||| b) ≤ a * 2 ^ s + b := by
  have hpos : 0 < 2 ^ s := Nat.pow_pos (by decide)
  have hdecomp : ∀ (q r : Nat), r < 2 ^ s → ((q * 2 ^ s + r) ||| b) = q * 2 ^ s + (r ||| b) := by
    intro q r hr
    have hrb : r ||| b < 2 ^ s := Nat.or_lt_two_pow hr hb
    apply Nat.eq_of_testBit_eq; intro t
    rw [Nat.testBit_or, testBit_mul_two_pow_add s q r t hr, testBit_mul_two_pow_add s q (r ||| b) t hrb]
    split
    · rw [Nat.testBit_or]
    · rename_i hge
      have hb0 : b.testBit t = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (Nat.not_lt.mp hge)))
      simp [hb0]
  by_cases heq : u = a * 2 ^ s
  · subst heq
    have := hdecomp a 0 hpos
    simpa using Nat.le_of_eq this
  · have hlt : u < a * 2 ^ s := by omega
    have hq_lt : u / 2 ^ s < a := by rw [Nat.div_lt_iff_lt_mul hpos]; exact hlt
    have hr_lt : u % 2 ^ s < 2 ^ s := Nat.mod_lt u hpos
    have hu_eq : u = (u / 2 ^ s) * 2 ^ s + u % 2 ^ s := by
      rw [Nat.mul_comm]; exact (Nat.div_add_mod u (2 ^ s)).symm
    have hrb_lt : (u % 2 ^ s) ||| b < 2 ^ s := Nat.or_lt_two_pow hr_lt hb
    rw [hu_eq, hdecomp (u / 2 ^ s) (u % 2 ^ s) hr_lt]
    have h1 : (u / 2 ^ s) * 2 ^ s + ((u % 2 ^ s) ||| b) < (u / 2 ^ s + 1) * 2 ^ s := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    have h2 : (u / 2 ^ s + 1) * 2 ^ s ≤ a * 2 ^ s := Nat.mul_le_mul_right _ hq_lt
    omega

theorem add_eq_or_of_and_zero : ∀ u v : Nat, (u &&& v) = 0 → u + v = (u ||| v) := by
  intro u
  induction u using Nat.strongRecOn with
  | ind u ih =>
    intro v h
    by_cases hu0 : u = 0
    · subst hu0; simp
    · have hdiv_and : (u / 2 &&& v / 2) = 0 := by
        apply Nat.eq_of_testBit_eq; intro t
        have ht := congrArg (fun x => x.testBit (t + 1)) h
        rw [Nat.testBit_and, Nat.zero_testBit] at ht
        simpa [Nat.testBit_and, Nat.testBit_div_two] using ht
      have hbit0 : ¬ (u % 2 = 1 ∧ v % 2 = 1) := by
        rintro ⟨hu1, hv1⟩
        have h0 := congrArg (fun x => x.testBit 0) h
        rw [Nat.testBit_and, Nat.testBit_zero, Nat.testBit_zero, Nat.zero_testBit, hu1, hv1] at h0
        cases h0
      have hih := ih (u / 2) (by omega) (v / 2) hdiv_and
      have hor_decomp : (u ||| v) = 2 * ((u / 2) ||| (v / 2)) + ((u % 2) ||| (v % 2)) := by
        apply Nat.eq_of_testBit_eq; intro t
        cases t with
        | zero =>
          have hlt2 : (u % 2 ||| v % 2) < 2 ^ 1 := Nat.or_lt_two_pow (n := 1) (by omega) (by omega)
          have h2eq : 2 * (u / 2 ||| v / 2) = (u / 2 ||| v / 2) * 2 ^ 1 := by rw [Nat.pow_one, Nat.mul_comm]
          rw [Nat.testBit_or, h2eq, testBit_mul_two_pow_add 1 _ _ 0 hlt2]
          simp only [Nat.zero_lt_one, ↓reduceIte, Nat.testBit_zero]
          have hm1 : (u % 2) % 2 = u % 2 := Nat.mod_mod _ _
          have hm2 : (v % 2) % 2 = v % 2 := Nat.mod_mod _ _
          simp [hm1, hm2]
        | succ t =>
          have hlt2 : (u % 2 ||| v % 2) < 2 ^ 1 := Nat.or_lt_two_pow (n := 1) (by omega) (by omega)
          have h2eq : 2 * (u / 2 ||| v / 2) = (u / 2 ||| v / 2) * 2 ^ 1 := by rw [Nat.pow_one, Nat.mul_comm]
          rw [Nat.testBit_or, h2eq, testBit_mul_two_pow_add 1 _ _ (t + 1) hlt2]
          simp only [Nat.not_lt.mpr (Nat.succ_le_succ (Nat.zero_le t)), ↓reduceIte,
                     Nat.add_sub_cancel, Nat.testBit_or, Nat.testBit_div_two]
      rw [hor_decomp, ← hih]
      have hmod_or : (u % 2 ||| v % 2) = u % 2 + v % 2 := by
        have hu_cases : u % 2 = 0 ∨ u % 2 = 1 := by omega
        have hv_cases : v % 2 = 0 ∨ v % 2 = 1 := by omega
        rcases hu_cases with hu1 | hu1 <;> rcases hv_cases with hv1 | hv1
        · rw [hu1, hv1]; rfl
        · rw [hu1, hv1]; rfl
        · rw [hu1, hv1]; rfl
        · exact absurd ⟨hu1, hv1⟩ hbit0
      rw [hmod_or]; omega

/-- Disjoint basis product: if `u < 2^n`, `v < 2^n`, and `u &&& v = 0`,
    then `pow2 n u ⊗ pow2 n v = pow2 n (u + v)`. -/
theorem mul_pow2_disjoint : ∀ (n u v : Nat), u < 2 ^ n → v < 2 ^ n → (u &&& v) = 0 →
    mul (pow2 n u) (pow2 n v) = pow2 n (u + v)
  | 0, 0, 0, _, _, _ => rfl
  | 0, _ + 1, _, hu, _, _ => by omega
  | 0, _, _ + 1, _, hv, _ => by omega
  | n + 1, u, v, hu, hv, hdisj => by
    have h2 : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Nat.pow_succ, Nat.mul_two]
    have hnot_both : ¬ (2 ^ n ≤ u ∧ 2 ^ n ≤ v) := by
      rintro ⟨hu1, hv1⟩
      have hbit := congrArg (fun x => x.testBit n) hdisj
      rw [Nat.testBit_and, Nat.zero_testBit] at hbit
      have htu : u.testBit n = true := by
        have : u = 1 * 2 ^ n + (u - 2 ^ n) := by omega
        rw [this, testBit_mul_two_pow_add n 1 (u - 2 ^ n) n (by omega)]
        simp
      have htv : v.testBit n = true := by
        have : v = 1 * 2 ^ n + (v - 2 ^ n) := by omega
        rw [this, testBit_mul_two_pow_add n 1 (v - 2 ^ n) n (by omega)]
        simp
      rw [htu, htv] at hbit; cases hbit
    have hdisj_sub : ∀ (a b : Nat), a < 2 ^ n → b < 2 ^ n → ((2 ^ n + a) &&& b) = 0 → (a &&& b) = 0 := by
      intro a b ha hb h
      apply Nat.eq_of_testBit_eq; intro t
      rw [Nat.testBit_and, Nat.zero_testBit]
      have ht := congrArg (fun x => x.testBit t) h
      rw [Nat.testBit_and, Nat.zero_testBit, ← Nat.one_mul (2 ^ n),
          testBit_mul_two_pow_add n 1 a t ha] at ht
      by_cases hlt : t < n
      · simpa [hlt] using ht
      · have hb0 : b.testBit t = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (Nat.not_lt.mp hlt)))
        simp [hb0]
    simp only [pow2]
    split <;> split
    · rename_i hu' hv'
      rw [mul_pair]
      simp only [zero_mul, mul_zero, xor_zero, scaleH_zero]
      have huv_lt : u + v < 2 ^ n := by
        rw [add_eq_or_of_and_zero u v hdisj]; exact Nat.or_lt_two_pow hu' hv'
      rw [mul_pow2_disjoint n u v hu' hv' hdisj]
      simp [huv_lt]
    · rename_i hu' hv'
      have hv2 : v - 2 ^ n < 2 ^ n := by omega
      have hsub : (u &&& (v - 2 ^ n)) = 0 := by
        rw [Nat.and_comm]
        apply hdisj_sub (v - 2 ^ n) u hv2 hu'
        rw [show 2 ^ n + (v - 2 ^ n) = v by omega, Nat.and_comm]
        exact hdisj
      rw [mul_pair]
      simp only [zero_mul, mul_zero, xor_zero, zero_xor, scaleH_zero]
      rw [mul_pow2_disjoint n u (v - 2 ^ n) hu' hv2 hsub]
      have hge : ¬ (u + v < 2 ^ n) := by omega
      have hsubeq : u + v - 2 ^ n = u + (v - 2 ^ n) := by omega
      simp [hge, hsubeq]
    · rename_i hu' hv'
      have hu2 : u - 2 ^ n < 2 ^ n := by omega
      have hsub : ((u - 2 ^ n) &&& v) = 0 := by
        apply hdisj_sub (u - 2 ^ n) v hu2 hv'
        rwa [show 2 ^ n + (u - 2 ^ n) = u by omega]
      rw [mul_pair]
      simp only [zero_mul, mul_zero, xor_zero, zero_xor, scaleH_zero]
      rw [mul_pow2_disjoint n (u - 2 ^ n) v hu2 hv' hsub]
      have hge : ¬ (u + v < 2 ^ n) := by omega
      have hsubeq : u + v - 2 ^ n = (u - 2 ^ n) + v := by omega
      simp [hge, hsubeq]
    · rename_i hu' hv'
      exact absurd ⟨Nat.not_lt.mp hu', Nat.not_lt.mp hv'⟩ hnot_both

/-- Leibniz rule for `℘^(2^k)`:
    `℘^(2^k)(A ⊗ B) = A ⊗ ℘^(2^k)(B) ⊕ ℘^(2^k)(A) ⊗ Φ^(2^k)(B)`. -/
theorem wpIter_pow2_mul {n : Nat} (k : Nat) (A B : Nim n) :
    wpIter (2 ^ k) (mul A B) =
      xor (mul A (wpIter (2 ^ k) B)) (mul (wpIter (2 ^ k) A) (sqIter (2 ^ k) B)) := by
  rw [wpIter_pow2_eq_sqIter_xor, wpIter_pow2_eq_sqIter_xor, wpIter_pow2_eq_sqIter_xor,
      sqIter_mul, mul_xor_r, mul_xor_l]
  have h : xor (xor (mul A (sqIter (2 ^ k) B)) (mul A B))
               (xor (mul (sqIter (2 ^ k) A) (sqIter (2 ^ k) B)) (mul A (sqIter (2 ^ k) B))) =
           xor (xor (mul A (sqIter (2 ^ k) B)) (mul A (sqIter (2 ^ k) B)))
               (xor (mul (sqIter (2 ^ k) A) (sqIter (2 ^ k) B)) (mul A B)) := by ac_rfl
  rw [h, xor_self, zero_xor]

/-- Exact right-shift law inside `Nim (k + 1)`: `℘^(2^k)(pair a b) = embed a`. -/
theorem wpIter_pow2_pair {k : Nat} (a b : Nim k) :
    wpIter (2 ^ k) (.pair a b) = embed a := by
  rw [wpIter_pow2_eq_sqIter_xor, sqIter_pow2_pair]
  simp only [xor, embed, xor_self]
  congr 1
  rw [xor_comm b a, xor_cancel_right]

/-- `℘^(2^k)(F_n) = embed (frobSum (2^k) H_n)`. -/
theorem wpIter_pow2_fermatGen (k n : Nat) :
    wpIter (2 ^ k) (fermatGen n) = embed (frobSum (2 ^ k) (halfFermat (k := n))) := by
  rw [wpIter_pow2_eq_sqIter_xor, sqIter_fermatGen, xor_comm (fermatGen n), xor_cancel_right]

/-- Helper: `sqIter (2^k)` fixes all elements `< 2^(2^k)` inside any higher block `Nim n`. -/
theorem sqIter_pow2_pow2_of_lt : ∀ (n k s : Nat), s < 2 ^ k → s < 2 ^ n →
    sqIter (2 ^ k) (pow2 n s) = pow2 n s := by
  intro n
  induction n with
  | zero =>
    intro k s hs hsn
    have hs0 : s = 0 := by omega
    subst hs0
    rw [pow2_zero]
    exact sqIter_one (2 ^ k)
  | succ n ih =>
    intro k s hs hsn
    by_cases hnk : n + 1 ≤ k
    · have hdvd : ∃ q, 2 ^ k = q * 2 ^ (n + 1) := by
        refine ⟨2 ^ (k - (n + 1)), ?_⟩
        rw [← Nat.pow_add]; congr 1; omega
      obtain ⟨q, hq⟩ := hdvd
      have hiter : ∀ r, sqIter (r * 2 ^ (n + 1)) (pow2 (n + 1) s) = pow2 (n + 1) s := by
        intro r
        induction r with
        | zero => simp [sqIter]
        | succ r ihr =>
          rw [Nat.succ_mul, Nat.add_comm (r * 2 ^ (n + 1)), sqIter_add, sqIter_pow2_eq_self, ihr]
      rw [hq]
      exact hiter q
    · have hkn : k ≤ n := by omega
      have hs_lt_n : s < 2 ^ n := Nat.lt_of_lt_of_le hs (Nat.pow_le_pow_right (by decide) hkn)
      simp only [pow2, hs_lt_n, ↓reduceIte]
      change sqIter (2 ^ k) (embed (pow2 n s)) = embed (pow2 n s)
      rw [← embed_sqIter, ih k s hs hs_lt_n]

/-- Helper: `sqIter (2^k)` on `pow2 n (2^k + s)` for `s < 2^k` gives `pow2 n (2^k + s) ⊕ pow2 n s`. -/
theorem sqIter_pow2_pow2_mid : ∀ (n k s : Nat), s < 2 ^ k → 2 ^ k + s < 2 ^ n →
    sqIter (2 ^ k) (pow2 n (2 ^ k + s)) = xor (pow2 n (2 ^ k + s)) (pow2 n s) := by
  intro n
  induction n with
  | zero => intro k s _ h; have := Nat.one_le_pow k 2 (by decide); omega
  | succ n ih =>
    intro k s hs hlt
    by_cases hnk : n = k
    · subst hnk
      have hnot : ¬ (2 ^ n + s < 2 ^ n) := by omega
      have hsub : 2 ^ n + s - 2 ^ n = s := by omega
      simp only [pow2, hnot, ↓reduceIte, hsub, hs]
      rw [sqIter_pow2_pair, zero_xor]
      simp [xor, xor_zero, zero_xor]
    · have hkn : k < n := by
        have hpos : 0 < 2 ^ n := Nat.pow_pos (by decide)
        by_cases hle : n < k
        · have : 2 ^ (n + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hle
          omega
        · omega
      have h2k_le : 2 ^ (k + 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hkn
      have hlt_n : 2 ^ k + s < 2 ^ n := by rw [Nat.pow_succ, Nat.mul_two] at h2k_le; omega
      have hs_n : s < 2 ^ n := by omega
      simp only [pow2, hlt_n, hs_n, ↓reduceIte]
      change sqIter (2 ^ k) (embed (pow2 n (2 ^ k + s))) = xor (embed (pow2 n (2 ^ k + s))) (embed (pow2 n s))
      rw [← embed_sqIter, ← embed_xor, ih k s hs hlt_n]

/-- Level-independence of `(wpIter m (pow2 n i)).toNat` across Fermat blocks. -/
theorem toNat_wpIter_pow2_level_indep (n1 n2 m i : Nat) (h1 : i < 2 ^ n1) (h2 : i < 2 ^ n2) :
    (wpIter m (pow2 n1 i)).toNat = (wpIter m (pow2 n2 i)).toNat := by
  -- Prove for n1 ≤ n2 by induction on n2 - n1, then use symmetry!
  have hstep : ∀ a b, a ≤ b → i < 2 ^ a → (wpIter m (pow2 a i)).toNat = (wpIter m (pow2 b i)).toNat := by
    intro a b hab
    induction hab with
    | refl => intro _; rfl
    | @step b' _ ih =>
      intro ha
      have hia : i < 2 ^ b' := Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by assumption))
      rw [ih ha]
      simp only [pow2, hia, ↓reduceIte]
      change (wpIter m (pow2 b' i)).toNat = (wpIter m (embed (pow2 b' i))).toNat
      rw [← embed_wpIter, toNat_embed]
  by_cases hle : n1 ≤ n2
  · exact hstep n1 n2 hle h1
  · exact (hstep n2 n1 (by omega) h2).symm

/-- Pure structural-recursive Conway ONAG `mex` nim-multiplication table on `[0, N) × [0, N)`. -/
def mexFromMask : Nat → Nat → Nat → Nat
  | 0, _, cur     => cur
  | f + 1, m, cur => if m.testBit cur then mexFromMask f m (cur + 1) else cur

def buildMexRowAux (prevRows : List (List Nat)) (fuel : Nat) (b : Nat) (curRow : List Nat) : List Nat :=
  match fuel with
  | 0 => curRow
  | f + 1 =>
    let mask := prevRows.foldl (fun acc rowA' =>
      let valA'b := rowA'.getD b 0
      (List.range b).foldl (fun acc2 b' =>
        let valAb' := curRow.getD b' 0
        let valA'b' := rowA'.getD b' 0
        acc2 ||| (1 <<< (valA'b ^^^ valAb' ^^^ valA'b'))
      ) acc
    ) 0
    let entry := mexFromMask 256 mask 0
    buildMexRowAux prevRows f (b + 1) (curRow ++ [entry])

def buildMexTableAux (n : Nat) : Nat → List (List Nat) → List (List Nat)
  | 0, rows     => rows
  | f + 1, rows => buildMexTableAux n f (rows ++ [buildMexRowAux rows n 0 []])

def buildMexTable (n : Nat) : List (List Nat) := buildMexTableAux n n []

end Nim
end ConwaySilicon

/-! ### Exhaustive Axiom Audit (`#print axioms`) on All Main Public Theorems -/
