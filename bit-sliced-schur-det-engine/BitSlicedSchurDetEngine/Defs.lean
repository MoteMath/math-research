/-!
# Recursive Bit-Sliced Schur-Complement Determinant Engine (Standalone Lean 4.36.0)

Zero Mathlib, zero external dependencies, zero `sorry`, zero custom axioms.

Architecture:
1. Self-contained commutative ring (`CRing`), integral domain (`IntDomain`), `Int`, and `ZMod`
   (including zero-divisor rings like `ZMod 6`).
2. Genuine classical Leibniz / Levi-Civita determinant `det : Mat R n -> R` over any `CRing R`,
   with complete zero-circularity proofs of:
   - `det_one`, `det_smul`, `det_mul`, `det_row_add`, `det_row_smul`, `det_col_add`,
     `det_col_smul`, `det_col_swap`, `det_congr_of_unit_row`, `det_blockUpper`, `det_blockLower`.
3. Reusable Division-Free Block-Schur Lifting Engine over ANY `CRing R`:
   - `det_block_schur_left_unimodular`
   - `det_block_schur_right_unimodular`
   - `det_block_schur_left_scaled`
   - `det_block_schur_right_scaled`
   - `det_block_scalar_top` & `det_block_schur_proportional` (constructive, works even when γ = 0
     or γ is a zero divisor!)
   - `det_bitSliced_schur_lift` & `det_bitSliced_schur_zero_iff` (finite -> infinite bit-sliced
     compiler lifting 1-step Schur renormalization to 2^k-mask closed forms & invertibility dichotomies).
4. Concrete Novel Infinite Theorem Families proved through the engine:
   - Family I: Non-Uniform Highest-Common-Bit (HCB) Weighted Kernel `H_k(f; γ, α, β, δ)`
   - Family II: Weighted Boolean-Poset Subset-Disjointness Hybrid Kernel `B_k(a, c; u, w, d)`
-/

namespace BitSlicedSchur

/-! ## Section 1: Commutative Rings, Integral Domains, and Finite Sums/Products -/

class CRing (R : Type u) where
  zero : R
  one : R
  add : R → R → R
  neg : R → R
  mul : R → R → R
  add_assoc : ∀ a b c : R, add (add a b) c = add a (add b c)
  zero_add : ∀ a : R, add zero a = a
  add_comm : ∀ a b : R, add a b = add b a
  add_left_neg : ∀ a : R, add (neg a) a = zero
  mul_assoc : ∀ a b c : R, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : R, mul one a = a
  mul_comm : ∀ a b : R, mul a b = mul b a
  left_distrib : ∀ a b c : R, mul a (add b c) = add (mul a b) (mul a c)

class IntDomain (R : Type u) extends CRing R where
  mul_eq_zero : ∀ a b : R, mul a b = zero → a = zero ∨ b = zero
  one_ne_zero : one ≠ zero

namespace CRing

variable {R : Type u} [CRing R]

def sub (a b : R) : R := add a (neg b)

def pow (a : R) : Nat → R
  | 0 => one
  | n + 1 => mul (pow a n) a

def ofNat : Nat → R
  | 0 => zero
  | n + 1 => add (ofNat n) one

def ofInt : Int → R
  | Int.ofNat n => ofNat n
  | Int.negSucc n => neg (ofNat (n + 1))

theorem add_zero (a : R) : add a zero = a := by
  rw [add_comm, zero_add]

theorem add_right_neg (a : R) : add a (neg a) = zero := by
  rw [add_comm, add_left_neg]

theorem mul_one (a : R) : mul a one = a := by
  rw [mul_comm, one_mul]

theorem right_distrib (a b c : R) : mul (add a b) c = add (mul a c) (mul b c) := by
  rw [mul_comm, left_distrib, mul_comm c a, mul_comm c b]

theorem add_left_cancel {a b c : R} (h : add a b = add a c) : b = c := by
  have h1 : add (neg a) (add a b) = add (neg a) (add a c) := congrArg (add (neg a)) h
  rw [← add_assoc, ← add_assoc, add_left_neg, zero_add, zero_add] at h1
  exact h1

theorem mul_zero (a : R) : mul a zero = zero := by
  apply add_left_cancel (a := mul a zero)
  rw [← left_distrib, add_zero, add_zero]

theorem zero_mul (a : R) : mul zero a = zero := by
  rw [mul_comm, mul_zero]

theorem neg_eq_of_add_eq_zero {a b : R} (h : add a b = zero) : neg a = b := by
  apply add_left_cancel (a := a)
  rw [add_right_neg, h]

theorem neg_zero : neg (zero : R) = zero :=
  neg_eq_of_add_eq_zero (zero_add zero)

theorem neg_neg (a : R) : neg (neg a) = a :=
  neg_eq_of_add_eq_zero (add_left_neg a)

theorem neg_add (a b : R) : neg (add a b) = add (neg a) (neg b) := by
  apply neg_eq_of_add_eq_zero
  rw [add_assoc, ← add_assoc b (neg a) (neg b), add_comm b (neg a), add_assoc (neg a) b (neg b),
      add_right_neg, add_zero, add_right_neg]

theorem mul_neg (a b : R) : mul a (neg b) = neg (mul a b) := by
  symm
  apply neg_eq_of_add_eq_zero
  rw [← left_distrib, add_right_neg, mul_zero]

theorem neg_mul (a b : R) : mul (neg a) b = neg (mul a b) := by
  rw [mul_comm, mul_neg, mul_comm]

theorem neg_mul_neg (a b : R) : mul (neg a) (neg b) = mul a b := by
  rw [neg_mul, mul_neg, neg_neg]

theorem neg_one_mul (a : R) : mul (neg one) a = neg a := by
  rw [neg_mul, one_mul]

theorem sub_self (a : R) : sub a a = zero := add_right_neg a

theorem sub_zero (a : R) : sub a zero = a := by
  unfold sub; rw [neg_zero, add_zero]

theorem zero_sub (a : R) : sub zero a = neg a := by
  unfold sub; rw [zero_add]

theorem add_sub_cancel (a b : R) : add (sub a b) b = a := by
  unfold sub; rw [add_assoc, add_left_neg, add_zero]

theorem sub_add_cancel (a b : R) : sub (add a b) b = a := by
  unfold sub; rw [add_assoc, add_right_neg, add_zero]

theorem sub_eq_zero_iff (a b : R) : sub a b = zero ↔ a = b := by
  constructor
  · intro h
    have h1 := congrArg (fun x => add x b) h
    simp only [add_sub_cancel, zero_add] at h1
    exact h1
  · intro h; subst h; exact sub_self a

theorem mul_sub (a b c : R) : mul a (sub b c) = sub (mul a b) (mul a c) := by
  unfold sub; rw [left_distrib, mul_neg]

theorem sub_mul (a b c : R) : mul (sub a b) c = sub (mul a c) (mul b c) := by
  unfold sub; rw [right_distrib, neg_mul]

theorem pow_zero (a : R) : pow a 0 = one := rfl
theorem pow_succ (a : R) (n : Nat) : pow a (n + 1) = mul (pow a n) a := rfl
theorem pow_one (a : R) : pow a 1 = a := one_mul a

theorem pow_add (a : R) (m n : Nat) : pow a (m + n) = mul (pow a m) (pow a n) := by
  induction n with
  | zero => rw [Nat.add_zero, pow_zero, mul_one]
  | succ n ih => rw [Nat.add_succ, pow_succ, pow_succ, ih, mul_assoc]

theorem mul_pow (a b : R) (n : Nat) : pow (mul a b) n = mul (pow a n) (pow b n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pow_zero, one_mul]
  | succ n ih =>
    rw [pow_succ, pow_succ, pow_succ, ih]
    rw [mul_assoc, ← mul_assoc (pow b n) a b, mul_comm (pow b n) a, mul_assoc a (pow b n) b,
        ← mul_assoc]

theorem one_pow (n : Nat) : pow (one : R) n = one := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ih, one_mul]

theorem ofNat_add (m n : Nat) : ofNat (R := R) (m + n) = add (ofNat m) (ofNat n) := by
  induction n with
  | zero =>
    change ofNat m = add (ofNat m) zero
    rw [add_zero]
  | succ n ih =>
    change add (ofNat (m + n)) one = add (ofNat m) (add (ofNat n) one)
    rw [ih, add_assoc]

theorem ofNat_mul (m n : Nat) : ofNat (R := R) (m * n) = mul (ofNat m) (ofNat n) := by
  induction n with
  | zero =>
    change zero = mul (ofNat m) zero
    rw [mul_zero]
  | succ n ih =>
    rw [Nat.mul_succ, ofNat_add, ih]
    change add (mul (ofNat m) (ofNat n)) (ofNat m) = mul (ofNat m) (add (ofNat n) one)
    rw [left_distrib, mul_one]

theorem ofInt_zero : ofInt (R := R) 0 = zero := rfl
theorem ofInt_one : ofInt (R := R) 1 = one := zero_add one
theorem ofInt_neg_one : ofInt (R := R) (-1) = neg one := by
  change neg (add zero one) = neg one
  rw [zero_add]

theorem ofInt_neg (z : Int) : ofInt (R := R) (-z) = neg (ofInt z) := by
  cases z with
  | ofNat n =>
    cases n with
    | zero => exact neg_zero.symm
    | succ n => rfl
  | negSucc n =>
    change ofNat (n + 1) = neg (neg (ofNat (n + 1)))
    rw [neg_neg]

theorem ofInt_mul (x y : Int) : ofInt (R := R) (x * y) = mul (ofInt x) (ofInt y) := by
  cases x with
  | ofNat m =>
    cases y with
    | ofNat n => exact ofNat_mul m n
    | negSucc n =>
      have h : Int.ofNat m * Int.negSucc n = -(Int.ofNat (m * (n + 1))) := by
        change (m : Int) * Int.negSucc n = -((m * (n + 1) : Nat) : Int)
        rw [Int.negSucc_eq, Int.mul_neg, Int.natCast_mul, Int.natCast_add, Int.natCast_one]
      rw [h, ofInt_neg]
      change neg (ofNat (m * (n + 1))) = mul (ofNat m) (neg (ofNat (n + 1)))
      rw [ofNat_mul, mul_neg]
  | negSucc m =>
    cases y with
    | ofNat n =>
      have h : Int.negSucc m * Int.ofNat n = -(Int.ofNat ((m + 1) * n)) := by
        change Int.negSucc m * (n : Int) = -(((m + 1) * n : Nat) : Int)
        rw [Int.negSucc_eq, Int.neg_mul, Int.natCast_mul, Int.natCast_add, Int.natCast_one]
      rw [h, ofInt_neg]
      change neg (ofNat ((m + 1) * n)) = mul (neg (ofNat (m + 1))) (ofNat n)
      rw [ofNat_mul, neg_mul]
    | negSucc n =>
      have h : Int.negSucc m * Int.negSucc n = Int.ofNat ((m + 1) * (n + 1)) := by
        change Int.negSucc m * Int.negSucc n = (((m + 1) * (n + 1) : Nat) : Int)
        rw [Int.negSucc_eq, Int.negSucc_eq, Int.neg_mul_neg, Int.natCast_mul,
            Int.natCast_add, Int.natCast_add, Int.natCast_one]
      rw [h]
      change ofNat ((m + 1) * (n + 1)) = mul (neg (ofNat (m + 1))) (neg (ofNat (n + 1)))
      rw [neg_mul_neg, ofNat_mul]

end CRing

instance : CRing Int where
  zero := 0
  one := 1
  add := Int.add
  neg := Int.neg
  mul := Int.mul
  add_assoc := Int.add_assoc
  zero_add := Int.zero_add
  add_comm := Int.add_comm
  add_left_neg := Int.add_left_neg
  mul_assoc := Int.mul_assoc
  one_mul := Int.one_mul
  mul_comm := Int.mul_comm
  left_distrib := Int.mul_add

instance : IntDomain Int where
  mul_eq_zero := fun a b h => Int.mul_eq_zero.mp h
  one_ne_zero := by decide

/-- Residue ring `Z / (m + 1) Z` for kernel-checked tests in zero-divisor rings (e.g., `ZMod 5` = Z/6Z). -/
abbrev ZMod (m : Nat) := Fin (m + 1)

instance (m : Nat) : CRing (ZMod m) where
  zero := ⟨0, Nat.zero_lt_succ m⟩
  one := ⟨1 % (m + 1), Nat.mod_lt _ (Nat.zero_lt_succ m)⟩
  add a b := ⟨(a.val + b.val) % (m + 1), Nat.mod_lt _ (Nat.zero_lt_succ m)⟩
  neg a := ⟨((m + 1) - a.val % (m + 1)) % (m + 1), Nat.mod_lt _ (Nat.zero_lt_succ m)⟩
  mul a b := ⟨(a.val * b.val) % (m + 1), Nat.mod_lt _ (Nat.zero_lt_succ m)⟩
  add_assoc a b c := by
    apply Fin.ext; simp only [Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]
  zero_add a := by
    apply Fin.ext; simp only [Nat.zero_add, Nat.mod_eq_of_lt a.isLt]
  add_comm a b := by
    apply Fin.ext; simp only [Nat.add_comm]
  add_left_neg a := by
    apply Fin.ext
    have hlt := a.isLt
    have hmod : a.val % (m + 1) = a.val := Nat.mod_eq_of_lt hlt
    rw [hmod]
    simp only [Nat.mod_add_mod]
    have hsub : m + 1 - a.val + a.val = m + 1 := Nat.sub_add_cancel (Nat.le_of_lt hlt)
    rw [hsub, Nat.mod_self]
  mul_assoc a b c := by
    apply Fin.ext
    simp only [Nat.mod_mul_mod, Nat.mul_mod_mod, Nat.mul_assoc]
  one_mul a := by
    apply Fin.ext
    simp only [Nat.mod_mul_mod, Nat.one_mul, Nat.mod_eq_of_lt a.isLt]
  mul_comm a b := by
    apply Fin.ext; simp only [Nat.mul_comm]
  left_distrib a b c := by
    apply Fin.ext
    simp only [Nat.mul_mod_mod, Nat.add_mod_mod, Nat.mod_add_mod, Nat.mul_add]

/-! ### Finite Sums and Products over `Fin n` -/

section FinOps
variable {R : Type u} [CRing R]

def sumFin : (n : Nat) → (Fin n → R) → R
  | 0, _ => CRing.zero
  | n + 1, f => CRing.add (sumFin n (fun i => f i.castSucc)) (f (Fin.last n))

def prodFin : (n : Nat) → (Fin n → R) → R
  | 0, _ => CRing.one
  | n + 1, f => CRing.mul (prodFin n (fun i => f i.castSucc)) (f (Fin.last n))

theorem sumFin_congr {n : Nat} {f g : Fin n → R} (h : ∀ i, f i = g i) :
    sumFin n f = sumFin n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumFin]
    rw [ih (fun i => h i.castSucc), h (Fin.last n)]

theorem prodFin_congr {n : Nat} {f g : Fin n → R} (h : ∀ i, f i = g i) :
    prodFin n f = prodFin n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [prodFin]
    rw [ih (fun i => h i.castSucc), h (Fin.last n)]

theorem sumFin_zero (n : Nat) : sumFin n (fun _ => (CRing.zero : R)) = CRing.zero := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumFin]; rw [ih, CRing.add_zero]

theorem prodFin_one (n : Nat) : prodFin n (fun _ => (CRing.one : R)) = CRing.one := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [prodFin]; rw [ih, CRing.mul_one]

theorem sumFin_add {n : Nat} (f g : Fin n → R) :
    sumFin n (fun i => CRing.add (f i) (g i)) = CRing.add (sumFin n f) (sumFin n g) := by
  induction n with
  | zero => exact (CRing.zero_add CRing.zero).symm
  | succ n ih =>
    simp only [sumFin]
    rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc)]
    rw [CRing.add_assoc, ← CRing.add_assoc (sumFin n (fun i => g i.castSucc)),
        CRing.add_comm (sumFin n (fun i => g i.castSucc)) (f (Fin.last n)),
        CRing.add_assoc, ← CRing.add_assoc]

theorem sumFin_neg {n : Nat} (f : Fin n → R) :
    sumFin n (fun i => CRing.neg (f i)) = CRing.neg (sumFin n f) := by
  induction n with
  | zero => exact CRing.neg_zero.symm
  | succ n ih =>
    simp only [sumFin]
    rw [ih (fun i => f i.castSucc), CRing.neg_add]

theorem sumFin_mul_left {n : Nat} (c : R) (f : Fin n → R) :
    CRing.mul c (sumFin n f) = sumFin n (fun i => CRing.mul c (f i)) := by
  induction n with
  | zero => exact CRing.mul_zero c
  | succ n ih =>
    simp only [sumFin]
    rw [CRing.left_distrib, ih]

theorem sumFin_mul_right {n : Nat} (f : Fin n → R) (c : R) :
    CRing.mul (sumFin n f) c = sumFin n (fun i => CRing.mul (f i) c) := by
  rw [CRing.mul_comm, sumFin_mul_left]
  exact sumFin_congr (fun i => CRing.mul_comm c (f i))

theorem sumFin_comm {m n : Nat} (f : Fin m → Fin n → R) :
    sumFin m (fun i => sumFin n (fun j => f i j)) =
    sumFin n (fun j => sumFin m (fun i => f i j)) := by
  induction m with
  | zero => exact (sumFin_zero n).symm
  | succ m ih =>
    change CRing.add (sumFin m (fun i => sumFin n (fun j => f i.castSucc j)))
                     (sumFin n (fun j => f (Fin.last m) j)) =
           sumFin n (fun j => CRing.add (sumFin m (fun i => f i.castSucc j)) (f (Fin.last m) j))
    rw [ih (fun i j => f i.castSucc j), ← sumFin_add]

theorem sumFin_single {n : Nat} (a : Fin n) (f : Fin n → R)
    (h : ∀ i, i ≠ a → f i = CRing.zero) : sumFin n f = f a := by
  induction n with
  | zero => exact Fin.elim0 a
  | succ n ih =>
    simp only [sumFin]
    by_cases ha : a.val < n
    · have hlast : Fin.last n ≠ a := by
        intro heq; have := congrArg Fin.val heq; simp only [Fin.val_last] at this; omega
      rw [h (Fin.last n) hlast, CRing.add_zero]
      have hsub := ih ⟨a.val, ha⟩ (fun i => f i.castSucc) (by
        intro i hi
        apply h i.castSucc
        intro heq
        apply hi
        apply Fin.ext
        have hv : i.castSucc.val = a.val := congrArg Fin.val heq
        exact hv)
      rw [hsub]
      have hcast : (⟨a.val, ha⟩ : Fin n).castSucc = a := Fin.ext rfl
      rw [hcast]
    · have haeq : a = Fin.last n := by apply Fin.ext; simp only [Fin.val_last]; omega
      subst haeq
      have hzero : sumFin n (fun i => f i.castSucc) = CRing.zero := by
        rw [sumFin_congr (fun i => h i.castSucc (by
          intro heq; have := congrArg Fin.val heq; simp only [Fin.val_castSucc, Fin.val_last] at this; omega))]
        exact sumFin_zero n
      rw [hzero, CRing.zero_add]

theorem sumFin_split {m n : Nat} (f : Fin (m + n) → R) :
    sumFin (m + n) f =
      CRing.add (sumFin m (fun i => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right m n)⟩))
                (sumFin n (fun j => f ⟨m + j.val, Nat.add_lt_add_left j.isLt m⟩)) := by
  induction n with
  | zero =>
    change sumFin m f = CRing.add (sumFin m (fun i => f ⟨i.val, _⟩)) CRing.zero
    rw [CRing.add_zero]
    exact sumFin_congr (fun i => by congr 1)
  | succ n ih =>
    change CRing.add (sumFin (m + n) (fun i => f i.castSucc)) (f (Fin.last (m + n))) =
      CRing.add (sumFin m (fun i => f ⟨i.val, _⟩))
        (CRing.add (sumFin n (fun j => f ⟨m + j.val, _⟩)) (f ⟨m + n, _⟩))
    rw [ih (fun i => f i.castSucc), CRing.add_assoc]
    rfl

theorem prodFin_mul {n : Nat} (f g : Fin n → R) :
    prodFin n (fun i => CRing.mul (f i) (g i)) = CRing.mul (prodFin n f) (prodFin n g) := by
  induction n with
  | zero => exact (CRing.one_mul CRing.one).symm
  | succ n ih =>
    simp only [prodFin]
    rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc)]
    rw [CRing.mul_assoc, ← CRing.mul_assoc (prodFin n (fun i => g i.castSucc)),
        CRing.mul_comm (prodFin n (fun i => g i.castSucc)) (f (Fin.last n)),
        CRing.mul_assoc, ← CRing.mul_assoc]

theorem prodFin_const {n : Nat} (c : R) : prodFin n (fun _ => c) = CRing.pow c n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [prodFin]; rw [ih]; rfl

theorem prodFin_eq_zero_of_exists {n : Nat} (f : Fin n → R) (a : Fin n) (ha : f a = CRing.zero) :
    prodFin n f = CRing.zero := by
  induction n with
  | zero => exact Fin.elim0 a
  | succ n ih =>
    simp only [prodFin]
    by_cases hlt : a.val < n
    · have h0 := ih (fun i => f i.castSucc) ⟨a.val, hlt⟩ (by
        have : (⟨a.val, hlt⟩ : Fin n).castSucc = a := Fin.ext rfl
        rw [this, ha])
      rw [h0, CRing.zero_mul]
    · have : a = Fin.last n := by apply Fin.ext; simp only [Fin.val_last]; omega
      rw [← this, ha, CRing.mul_zero]

theorem prodFin_split {m n : Nat} (f : Fin (m + n) → R) :
    prodFin (m + n) f =
      CRing.mul (prodFin m (fun i => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right m n)⟩))
                (prodFin n (fun j => f ⟨m + j.val, Nat.add_lt_add_left j.isLt m⟩)) := by
  induction n with
  | zero =>
    change prodFin m f = CRing.mul (prodFin m (fun i => f ⟨i.val, _⟩)) CRing.one
    rw [CRing.mul_one]
    exact prodFin_congr (fun i => by congr 1)
  | succ n ih =>
    change CRing.mul (prodFin (m + n) (fun i => f i.castSucc)) (f (Fin.last (m + n))) =
      CRing.mul (prodFin m (fun i => f ⟨i.val, _⟩))
        (CRing.mul (prodFin n (fun j => f ⟨m + j.val, _⟩)) (f ⟨m + n, _⟩))
    rw [ih (fun i => f i.castSucc), CRing.mul_assoc]
    rfl

/-- Skew-symmetric double sum vanishes over EVERY commutative ring (even characteristic 2!). -/
theorem sumFin_skew_zero {n : Nat} (G : Fin n → Fin n → R)
    (hdiag : ∀ i, G i i = CRing.zero)
    (hskew : ∀ i j, G j i = CRing.neg (G i j)) :
    sumFin n (fun i => sumFin n (fun j => G i j)) = CRing.zero := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change CRing.add
      (sumFin n (fun i => CRing.add (sumFin n (fun j => G i.castSucc j.castSucc))
                                    (G i.castSucc (Fin.last n))))
      (CRing.add (sumFin n (fun j => G (Fin.last n) j.castSucc))
                 (G (Fin.last n) (Fin.last n))) = CRing.zero
    rw [sumFin_add]
    have hih := ih (fun i j => G i.castSucc j.castSucc)
      (fun i => hdiag i.castSucc) (fun i j => hskew i.castSucc j.castSucc)
    rw [hih, CRing.zero_add, hdiag (Fin.last n), CRing.add_zero]
    have hneg : sumFin n (fun j => G (Fin.last n) j.castSucc) =
                CRing.neg (sumFin n (fun i => G i.castSucc (Fin.last n))) := by
      rw [← sumFin_neg]
      exact sumFin_congr (fun i => hskew i.castSucc (Fin.last n))
    rw [hneg, CRing.add_right_neg]

end FinOps

theorem prodFin_eq_zero_iff {R : Type u} [IntDomain R] {n : Nat} (f : Fin n → R) :
    prodFin n f = CRing.zero ↔ ∃ i : Fin n, f i = CRing.zero := by
  induction n with
  | zero =>
    constructor
    · intro h; exact absurd h IntDomain.one_ne_zero
    · rintro ⟨i, _⟩; exact Fin.elim0 i
  | succ n ih =>
    simp only [prodFin]
    constructor
    · intro h
      rcases IntDomain.mul_eq_zero _ _ h with h1 | h2
      · rcases (ih (fun i => f i.castSucc)).mp h1 with ⟨i, hi⟩
        exact ⟨i.castSucc, hi⟩
      · exact ⟨Fin.last n, h2⟩
    · rintro ⟨i, hi⟩
      exact prodFin_eq_zero_of_exists f i hi

/-! ## Section 2: Transpositions, `sumVec`, Levi-Civita `eps`, and Classical `det` -/

def swapFin {n : Nat} (p q : Fin n) (i : Fin n) : Fin n :=
  if i = p then q else if i = q then p else i

theorem swapFin_invol {n : Nat} (p q i : Fin n) : swapFin p q (swapFin p q i) = i := by
  unfold swapFin
  by_cases h1 : i = p
  · subst h1
    by_cases h2 : q = i
    · subst h2; simp
    · simp [h2]
  · by_cases h2 : i = q
    · subst h2; simp [h1]
    · simp [h1, h2]

theorem swapFin_self {n : Nat} (p i : Fin n) : swapFin p p i = i := by
  unfold swapFin; split <;> simp_all

theorem swapFin_comm {n : Nat} (p q i : Fin n) : swapFin p q i = swapFin q p i := by
  unfold swapFin
  by_cases h1 : i = p <;> by_cases h2 : i = q <;> simp_all

theorem swapFin_left {n : Nat} (p q : Fin n) : swapFin p q p = q := by
  unfold swapFin; simp

theorem swapFin_right {n : Nat} (p q : Fin n) : swapFin p q q = p := by
  unfold swapFin; by_cases h : q = p <;> simp [h]

theorem swapFin_inj {n : Nat} (p q : Fin n) {x y : Fin n}
    (h : swapFin p q x = swapFin p q y) : x = y := by
  have := congrArg (swapFin p q) h
  rw [swapFin_invol, swapFin_invol] at this
  exact this

/-- Finite pigeonhole principle: every injective `Fin m -> Fin m` is surjective. -/
theorem fin_inj_surj : ∀ {m : Nat} (g : Fin m → Fin m),
    (∀ x y, g x = g y → x = y) → ∀ y : Fin m, ∃ x : Fin m, g x = y
  | 0, _, _, y => Fin.elim0 y
  | m + 1, g, hinj, y => by
    let a := g (Fin.last m)
    let g' : Fin (m + 1) → Fin (m + 1) := fun x => swapFin a (Fin.last m) (g x)
    have hg'_inj : ∀ x1 x2, g' x1 = g' x2 → x1 = x2 := fun x1 x2 h =>
      hinj x1 x2 (swapFin_inj a (Fin.last m) h)
    have hg'_last : g' (Fin.last m) = Fin.last m := swapFin_left a (Fin.last m)
    have hg'_lt : ∀ x : Fin m, (g' x.castSucc).val < m := by
      intro x
      have hne : g' x.castSucc ≠ Fin.last m := by
        intro heq
        have hx := hg'_inj x.castSucc (Fin.last m) (heq.trans hg'_last.symm)
        have hv := congrArg Fin.val hx
        simp only [Fin.val_castSucc, Fin.val_last] at hv
        omega
      have hv := (g' x.castSucc).isLt
      have hne' : (g' x.castSucc).val ≠ m := fun h => hne (Fin.ext h)
      omega
    let gSub : Fin m → Fin m := fun x => ⟨(g' x.castSucc).val, hg'_lt x⟩
    have hgSub_inj : ∀ x1 x2, gSub x1 = gSub x2 → x1 = x2 := by
      intro x1 x2 h
      have hv : (gSub x1).val = (gSub x2).val := congrArg Fin.val h
      have heq := hg'_inj x1.castSucc x2.castSucc (Fin.ext hv)
      have hv2 : x1.castSucc.val = x2.castSucc.val := congrArg Fin.val heq
      exact Fin.ext hv2
    let y' := swapFin a (Fin.last m) y
    by_cases hy : y'.val < m
    · rcases fin_inj_surj gSub hgSub_inj ⟨y'.val, hy⟩ with ⟨x, hx⟩
      refine ⟨x.castSucc, ?_⟩
      have hv : (gSub x).val = y'.val := congrArg Fin.val hx
      have h1 : g' x.castSucc = y' := Fin.ext hv
      have h2 := congrArg (swapFin a (Fin.last m)) h1
      dsimp only [g', y'] at h2
      rw [swapFin_invol, swapFin_invol] at h2
      exact h2
    · refine ⟨Fin.last m, ?_⟩
      have hy_eq : y' = Fin.last m := by apply Fin.ext; simp only [Fin.val_last]; omega
      have h2 := congrArg (swapFin a (Fin.last m)) hy_eq
      dsimp only [y'] at h2
      rw [swapFin_invol, swapFin_right] at h2
      exact h2.symm

def finSnoc {m : Nat} {α : Type u} (g : Fin m → α) (a : α) : Fin (m + 1) → α :=
  fun i => if h : i.val < m then g ⟨i.val, h⟩ else a

theorem finSnoc_castSucc {m : Nat} {α : Type u} (g : Fin m → α) (a : α) (i : Fin m) :
    finSnoc g a i.castSucc = g i := by
  unfold finSnoc; simp [i.isLt]

theorem finSnoc_last {m : Nat} {α : Type u} (g : Fin m → α) (a : α) :
    finSnoc g a (Fin.last m) = a := by
  unfold finSnoc; simp

def finAppend {m n : Nat} {α : Type u} (f1 : Fin m → α) (f2 : Fin n → α) : Fin (m + n) → α :=
  fun i => if h : i.val < m then f1 ⟨i.val, h⟩ else f2 ⟨i.val - m, by omega⟩

/-- Exact sum over all functions `Fin m -> Fin k`, defined structurally without Mathlib. -/
def sumVec {R : Type u} [CRing R] : (m k : Nat) → ((Fin m → Fin k) → R) → R
  | 0, _, F => F Fin.elim0
  | m + 1, k, F =>
    sumFin k (fun a => sumVec m k (fun g => F (finSnoc g a)))

section SumVecProps
variable {R : Type u} [CRing R]

theorem sumVec_congr {m k : Nat} {F G : (Fin m → Fin k) → R} (h : ∀ f, F f = G f) :
    sumVec m k F = sumVec m k G := by
  induction m with
  | zero => exact h Fin.elim0
  | succ m ih =>
    simp only [sumVec]
    exact sumFin_congr (fun a => ih (fun g => h (finSnoc g a)))

theorem sumVec_zero {m k : Nat} : sumVec m k (fun _ => (CRing.zero : R)) = CRing.zero := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [sumVec]; rw [sumFin_congr (fun _ => ih), sumFin_zero]

theorem sumVec_add {m k : Nat} (F G : (Fin m → Fin k) → R) :
    sumVec m k (fun f => CRing.add (F f) (G f)) = CRing.add (sumVec m k F) (sumVec m k G) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [sumVec]
    rw [sumFin_congr (fun a => ih (fun g => F (finSnoc g a)) (fun g => G (finSnoc g a))),
        sumFin_add]

theorem sumVec_neg {m k : Nat} (F : (Fin m → Fin k) → R) :
    sumVec m k (fun f => CRing.neg (F f)) = CRing.neg (sumVec m k F) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [sumVec]
    rw [sumFin_congr (fun a => ih (fun g => F (finSnoc g a))), sumFin_neg]

theorem sumVec_mul_left {m k : Nat} (c : R) (F : (Fin m → Fin k) → R) :
    CRing.mul c (sumVec m k F) = sumVec m k (fun f => CRing.mul c (F f)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [sumVec]
    rw [sumFin_mul_left]
    exact sumFin_congr (fun a => ih (fun g => F (finSnoc g a)))

theorem sumVec_mul_right {m k : Nat} (F : (Fin m → Fin k) → R) (c : R) :
    CRing.mul (sumVec m k F) c = sumVec m k (fun f => CRing.mul (F f) c) := by
  rw [CRing.mul_comm, sumVec_mul_left]
  exact sumVec_congr (fun f => CRing.mul_comm c (F f))

theorem prodFin_sumFin {m k : Nat} (T : Fin m → Fin k → R) :
    prodFin m (fun i => sumFin k (fun a => T i a)) =
    sumVec m k (fun f => prodFin m (fun i => T i (f i))) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [prodFin, sumVec]
    rw [ih (fun i => T i.castSucc)]
    rw [sumFin_mul_left]
    apply sumFin_congr; intro a
    rw [sumVec_mul_right]
    apply sumVec_congr; intro g
    congr 1
    · exact prodFin_congr (fun i => by rw [finSnoc_castSucc])
    · rw [finSnoc_last]

theorem sumVec_swap_last2 {m k : Nat} (F : (Fin (m + 2) → Fin k) → R) :
    sumVec (m + 2) k (fun f => F (fun i => f (swapFin ⟨m, by omega⟩ (Fin.last (m + 1)) i))) =
    sumVec (m + 2) k F := by
  simp only [sumVec]
  rw [sumFin_comm]
  apply sumFin_congr; intro a
  apply sumFin_congr; intro b
  apply sumVec_congr; intro g
  congr 1; funext i
  let s1 : Fin (m + 2) := ⟨m, by omega⟩
  let s2 : Fin (m + 2) := Fin.last (m + 1)
  change finSnoc (finSnoc g a) b (swapFin s1 s2 i) = finSnoc (finSnoc g b) a i
  by_cases h1 : i.val < m
  · have hne1 : i ≠ s1 := by intro h; have := congrArg Fin.val h; simp [s1] at this; omega
    have hne2 : i ≠ s2 := by intro h; have := congrArg Fin.val h; simp [s2] at this; omega
    have hsw : swapFin s1 s2 i = i := by unfold swapFin; simp [hne1, hne2]
    rw [hsw]; unfold finSnoc; simp [h1, Nat.lt_trans h1 (Nat.lt_succ_self m)]
  · by_cases h2 : i.val = m
    · have heq1 : i = s1 := Fin.ext h2
      rw [heq1, swapFin_left]; unfold finSnoc; simp [s1, s2]
    · have heq2 : i = s2 := by apply Fin.ext; simp [s2]; omega
      rw [heq2, swapFin_right]; unfold finSnoc; simp [s1, s2]

theorem sumVec_swap_adj {m k : Nat} (j : Nat) (hj : j + 1 < m) (F : (Fin m → Fin k) → R) :
    sumVec m k (fun f => F (fun i => f (swapFin ⟨j, by omega⟩ ⟨j + 1, hj⟩ i))) =
    sumVec m k F := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases htop : j + 1 = m
    · cases m with
      | zero => omega
      | succ m' =>
        have hjm : j = m' := by omega
        subst hjm
        exact sumVec_swap_last2 F
    · have hj' : j + 1 < m := by omega
      simp only [sumVec]
      apply sumFin_congr; intro a
      have hrec := ih hj' (fun g => F (finSnoc g a))
      rw [← hrec]
      apply sumVec_congr; intro g
      congr 1; funext i
      by_cases hi : i.val < m
      · have hcast1 : (⟨i.val, hi⟩ : Fin m) = ⟨j, by omega⟩ ↔ i = ⟨j, by omega⟩ := by
          constructor
          · intro h; apply Fin.ext; have hv := congrArg Fin.val h; exact hv
          · intro h; apply Fin.ext; have hv := congrArg Fin.val h; exact hv
        have hcast2 : (⟨i.val, hi⟩ : Fin m) = ⟨j + 1, hj'⟩ ↔ i = ⟨j + 1, hj⟩ := by
          constructor
          · intro h; apply Fin.ext; have hv := congrArg Fin.val h; exact hv
          · intro h; apply Fin.ext; have hv := congrArg Fin.val h; exact hv
        unfold finSnoc swapFin
        by_cases h1 : i = ⟨j, by omega⟩
        · have hltj : j < m := by omega
          simp [h1, hj', hltj]
        · by_cases h2 : i = ⟨j + 1, hj⟩
          · have hltj : j < m := by omega
            simp [h2, hltj, hj']
          · have h1' : (⟨i.val, hi⟩ : Fin m) ≠ ⟨j, by omega⟩ := fun h => h1 (hcast1.mp h)
            have h2' : (⟨i.val, hi⟩ : Fin m) ≠ ⟨j + 1, hj'⟩ := fun h => h2 (hcast2.mp h)
            simp [h1, h2, h1', h2', hi]
      · unfold finSnoc swapFin
        have hne1 : i ≠ ⟨j, by omega⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
        have hne2 : i ≠ ⟨j + 1, hj⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
        simp [hi, hne1, hne2]

theorem sumVec_swap {m k : Nat} (p q : Fin m) (F : (Fin m → Fin k) → R) :
    sumVec m k (fun f => F (fun i => f (swapFin p q i))) = sumVec m k F := by
  suffices h : ∀ (d : Nat) (p q : Fin m), p.val + d = q.val →
      ∀ F : (Fin m → Fin k) → R,
      sumVec m k (fun f => F (fun i => f (swapFin p q i))) = sumVec m k F by
    by_cases hpq : p.val ≤ q.val
    · exact h (q.val - p.val) p q (by omega) F
    · rw [show (fun (f : Fin m → Fin k) => F (fun i => f (swapFin p q i))) =
               (fun (f : Fin m → Fin k) => F (fun i => f (swapFin q p i))) from
            funext (fun f => by congr 1; funext i; rw [swapFin_comm])]
      exact h (p.val - q.val) q p (by omega) F
  intro d
  induction d with
  | zero =>
    intro p q hpq F
    have : p = q := Fin.ext (by omega)
    subst this
    exact sumVec_congr (fun f => by congr 1; funext i; rw [swapFin_self])
  | succ d ih =>
    intro p q hpq F
    cases d with
    | zero =>
      have hj : p.val + 1 < m := by omega
      have hq : q = ⟨p.val + 1, hj⟩ := Fin.ext (by simp; omega)
      subst hq
      exact sumVec_swap_adj p.val hj F
    | succ d' =>
      have hr_lt : p.val + d' + 1 < m := by omega
      let r : Fin m := ⟨p.val + d' + 1, hr_lt⟩
      have hpr : p.val + (d' + 1) = r.val := by simp [r]; omega
      have hq_eq : q = ⟨r.val + 1, by simp [r]; omega⟩ := Fin.ext (by simp [r]; omega)
      have hr_eq : (⟨r.val, by omega⟩ : Fin m) = r := Fin.ext rfl
      have hdecomp : ∀ i : Fin m,
          swapFin p q i = swapFin r q (swapFin p r (swapFin r q i)) := by
        intro i
        have hne_pr : p ≠ r := by intro h; have := congrArg Fin.val h; simp [r] at this; omega
        have hne_pq : p ≠ q := by intro h; have := congrArg Fin.val h; omega
        have hne_rq : r ≠ q := by intro h; have := congrArg Fin.val h; simp [r] at this; omega
        by_cases h1 : i = p
        · subst h1
          have : swapFin r q i = i := by unfold swapFin; simp [hne_pr, hne_pq]
          rw [swapFin_left, this, swapFin_left, swapFin_left]
        · by_cases h2 : i = q
          · subst h2
            rw [swapFin_right, swapFin_right, swapFin_right]
            unfold swapFin; simp [hne_pr, hne_pq]
          · by_cases h3 : i = r
            · subst h3
              rw [swapFin_left]
              have : swapFin p r q = q := by unfold swapFin; simp [Ne.symm hne_pq, Ne.symm hne_rq]
              rw [this, swapFin_right]
              unfold swapFin; simp [h1, h2]
            · have s1 : swapFin r q i = i := by unfold swapFin; simp [h3, h2]
              have s2 : swapFin p r i = i := by unfold swapFin; simp [h1, h3]
              have s3 : swapFin p q i = i := by unfold swapFin; simp [h1, h2]
              rw [s1, s2, s1, s3]
      have hstep1 : sumVec m k (fun f => F (fun i => f (swapFin r q (swapFin p r (swapFin r q i))))) =
                    sumVec m k (fun f => F (fun i => f (swapFin p r (swapFin r q i)))) := by
        have hadj := sumVec_swap_adj r.val (by simp [r]; omega)
          (fun f => F (fun i => f (swapFin p r (swapFin r q i))))
        rw [hr_eq, ← hq_eq] at hadj
        exact hadj
      have hstep2 : sumVec m k (fun f => F (fun i => f (swapFin p r (swapFin r q i)))) =
                    sumVec m k (fun f => F (fun i => f (swapFin r q i))) :=
        ih p r hpr (fun f => F (fun i => f (swapFin r q i)))
      have hstep3 : sumVec m k (fun f => F (fun i => f (swapFin r q i))) = sumVec m k F := by
        have hadj := sumVec_swap_adj r.val (by simp [r]; omega) F
        rw [hr_eq, ← hq_eq] at hadj
        exact hadj
      calc sumVec m k (fun f => F (fun i => f (swapFin p q i)))
          = sumVec m k (fun f => F (fun i => f (swapFin r q (swapFin p r (swapFin r q i))))) :=
              sumVec_congr (fun f => by congr 1; funext i; rw [hdecomp])
        _ = sumVec m k (fun f => F (fun i => f (swapFin p r (swapFin r q i)))) := hstep1
        _ = sumVec m k (fun f => F (fun i => f (swapFin r q i))) := hstep2
        _ = sumVec m k F := hstep3

theorem sumVec_skew_zero {m k : Nat} (p q : Fin m) (hpq : p ≠ q)
    (F : (Fin m → Fin k) → R)
    (hdiag : ∀ f, f p = f q → F f = CRing.zero)
    (hskew : ∀ f, F (fun i => f (swapFin p q i)) = CRing.neg (F f)) :
    sumVec m k F = CRing.zero := by
  cases m with
  | zero => exact Fin.elim0 p
  | succ m1 =>
    cases m1 with
    | zero => exfalso; apply hpq; apply Fin.ext; omega
    | succ m' =>
      let s1 : Fin (m' + 2) := ⟨m', by omega⟩
      let s2 : Fin (m' + 2) := Fin.last (m' + 1)
      let q1 := swapFin p s1 q
      have hq1_ne : q1 ≠ s1 := by
        intro h
        have h' := congrArg (swapFin p s1) h
        rw [swapFin_invol, swapFin_right] at h'
        exact hpq h'.symm
      let π : Fin (m' + 2) → Fin (m' + 2) := fun i => swapFin q1 s2 (swapFin p s1 i)
      have hπ_p : π p = s1 := by
        dsimp only [π]
        rw [swapFin_left]
        have hs12 : s1 ≠ s2 := by intro h; have := congrArg Fin.val h; simp [s1, s2] at this
        unfold swapFin; simp [Ne.symm hq1_ne, hs12]
      have hπ_q : π q = s2 := by
        dsimp only [π]
        exact swapFin_left q1 s2
      have hπ_inj : ∀ x y, π x = π y → x = y := fun x y h =>
        swapFin_inj p s1 (swapFin_inj q1 s2 h)
      have hπ_swap : ∀ i, π (swapFin p q i) = swapFin s1 s2 (π i) := by
        intro i
        by_cases h1 : i = p
        · subst h1; rw [swapFin_left, hπ_q, hπ_p, swapFin_left]
        · by_cases h2 : i = q
          · subst h2; rw [swapFin_right, hπ_p, hπ_q, swapFin_right]
          · have hs : swapFin p q i = i := by unfold swapFin; simp [h1, h2]
            rw [hs]
            have hne1 : π i ≠ s1 := fun h => h1 (hπ_inj i p (h.trans hπ_p.symm))
            have hne2 : π i ≠ s2 := fun h => h2 (hπ_inj i q (h.trans hπ_q.symm))
            unfold swapFin; simp [hne1, hne2]
      have hreidx : sumVec (m' + 2) k F = sumVec (m' + 2) k (fun f => F (fun i => f (π i))) := by
        calc sumVec (m' + 2) k F
            = sumVec (m' + 2) k (fun f => F (fun i => f (swapFin p s1 i))) :=
                (sumVec_swap p s1 F).symm
          _ = sumVec (m' + 2) k (fun f => F (fun i => f (swapFin q1 s2 (swapFin p s1 i)))) :=
                (sumVec_swap q1 s2 (fun f => F (fun i => f (swapFin p s1 i)))).symm
      rw [hreidx]
      simp only [sumVec]
      apply sumFin_skew_zero (G := fun a b => sumVec m' k (fun g => F (fun i => finSnoc (finSnoc g b) a (π i))))
      · intro a
        rw [← sumVec_zero (m := m') (k := k)]
        apply sumVec_congr; intro g
        apply hdiag
        rw [hπ_p, hπ_q]
        simp [s1, s2, finSnoc]
      · intro a b
        rw [← sumVec_neg]
        apply sumVec_congr; intro g
        rw [← hskew]
        congr 1; funext i
        rw [hπ_swap]
        generalize π i = j
        by_cases hj1 : j.val < m'
        · have hne1 : j ≠ s1 := by intro h; have := congrArg Fin.val h; simp [s1] at this; omega
          have hne2 : j ≠ s2 := by intro h; have := congrArg Fin.val h; simp [s2] at this; omega
          have hsw : swapFin s1 s2 j = j := by unfold swapFin; simp [hne1, hne2]
          rw [hsw]; unfold finSnoc; simp [hj1, Nat.lt_trans hj1 (Nat.lt_succ_self m')]
        · by_cases hj2 : j.val = m'
          · have heq : j = s1 := Fin.ext hj2
            rw [heq, swapFin_left]; unfold finSnoc; simp [s1, s2]
          · have heq : j = s2 := by apply Fin.ext; simp [s2]; omega
            rw [heq, swapFin_right]; unfold finSnoc; simp [s1, s2]

theorem sumVec_split {m n k : Nat} (F : (Fin (m + n) → Fin k) → R) :
    sumVec (m + n) k F =
    sumVec m k (fun f1 => sumVec n k (fun f2 => F (finAppend f1 f2))) := by
  have hcomm : ∀ (r : Nat) (G : Fin k → (Fin r → Fin k) → R),
      sumFin k (fun a => sumVec r k (fun f1 => G a f1)) =
      sumVec r k (fun f1 => sumFin k (fun a => G a f1)) := by
    intro r
    induction r with
    | zero => intro _; rfl
    | succ r' ihr =>
      intro G
      simp only [sumVec]
      rw [sumFin_comm]
      apply sumFin_congr; intro b
      exact ihr (fun a g => G a (finSnoc g b))
  induction n with
  | zero =>
    apply sumVec_congr; intro f1
    congr 1; funext i
    unfold finAppend; simp
  | succ n ih =>
    change sumFin k (fun a => sumVec (m + n) k (fun g => F (finSnoc g a))) =
      sumVec m k (fun f1 => sumFin k (fun a => sumVec n k (fun g2 => F (finAppend f1 (finSnoc g2 a)))))
    rw [← hcomm m]
    apply sumFin_congr; intro a
    rw [ih (fun g => F (finSnoc g a))]
    apply sumVec_congr; intro f1
    apply sumVec_congr; intro g2
    congr 1; funext i
    unfold finSnoc finAppend
    by_cases h1 : i.val < m + n
    · by_cases h2 : i.val < m
      · simp [h1, h2]
      · have h3 : i.val - m < n := by omega
        simp [h1, h2, h3]
    · have h2 : ¬ i.val < m := by omega
      have h3 : ¬ (i.val - m < n) := by omega
      simp [h1, h2, h3]

/-- Reindexing the codomain of `sumVec` by `swapFin c1 c2` preserves `sumVec`. -/
theorem sumFin_swap_codomain {k : Nat} (c1 c2 : Fin k) (f : Fin k → R) :
    sumFin k (fun a => f (swapFin c1 c2 a)) = sumFin k f := by
  by_cases h : c1 = c2
  · subst h; exact sumFin_congr (fun a => by rw [swapFin_self])
  · have hdiff : sumFin k (fun a => CRing.sub (f (swapFin c1 c2 a)) (f a)) = CRing.zero := by
      have hsplit : sumFin k (fun a => CRing.sub (f (swapFin c1 c2 a)) (f a)) =
          CRing.add (sumFin k (fun a => if a = c1 then CRing.sub (f c2) (f c1) else CRing.zero))
                    (sumFin k (fun a => if a = c2 then CRing.sub (f c1) (f c2) else CRing.zero)) := by
        rw [← sumFin_add]
        apply sumFin_congr; intro a
        by_cases h1 : a = c1
        · subst h1; simp [swapFin_left, h, CRing.add_zero]
        · by_cases h2 : a = c2
          · subst h2; simp [swapFin_right, Ne.symm h, CRing.zero_add]
          · have hsw : swapFin c1 c2 a = a := by unfold swapFin; simp [h1, h2]
            simp [h1, h2, hsw, CRing.sub_self, CRing.zero_add]
      rw [hsplit]
      rw [sumFin_single c1 _ (fun a ha => by simp [ha])]
      rw [sumFin_single c2 _ (fun a ha => by simp [ha])]
      simp only [ite_true]
      unfold CRing.sub
      rw [CRing.add_assoc, ← CRing.add_assoc (CRing.neg (f c1)), CRing.add_left_neg,
          CRing.zero_add, CRing.add_right_neg]
    have hsub : sumFin k (fun a => CRing.sub (f (swapFin c1 c2 a)) (f a)) =
        CRing.sub (sumFin k (fun a => f (swapFin c1 c2 a))) (sumFin k f) := by
      unfold CRing.sub; rw [sumFin_add, sumFin_neg]
    rw [hsub] at hdiff
    exact (CRing.sub_eq_zero_iff _ _).mp hdiff

theorem sumVec_swap_codomain {m k : Nat} (c1 c2 : Fin k) (F : (Fin m → Fin k) → R) :
    sumVec m k (fun f => F (fun i => swapFin c1 c2 (f i))) = sumVec m k F := by
  induction m with
  | zero =>
    change F (fun i => swapFin c1 c2 (Fin.elim0 i)) = F Fin.elim0
    congr 1; funext i; exact Fin.elim0 i
  | succ m ih =>
    simp only [sumVec]
    rw [← sumFin_swap_codomain c1 c2 (fun a => sumVec m k (fun g => F (finSnoc g a)))]
    apply sumFin_congr; intro a
    rw [← ih (fun g => F (finSnoc g (swapFin c1 c2 a)))]
    apply sumVec_congr; intro g
    congr 1; funext i; unfold finSnoc
    by_cases hi : i.val < m <;> simp [hi]

/-- Restrict `sumVec` from codomain `m + n` to `m` when terms vanish outside `< m`. -/
theorem sumVec_restrict_lo {r m n : Nat} (F : (Fin r → Fin (m + n)) → R)
    (hvanish : ∀ f, (∃ i : Fin r, ¬ (f i).val < m) → F f = CRing.zero) :
    sumVec r (m + n) F =
    sumVec r m (fun g => F (fun i => ⟨(g i).val, Nat.lt_of_lt_of_le (g i).isLt (Nat.le_add_right m n)⟩)) := by
  induction r with
  | zero =>
    change F Fin.elim0 = F (fun i => ⟨(Fin.elim0 (α := Fin m) i).val, _⟩)
    congr 1; funext i; exact Fin.elim0 i
  | succ r ih =>
    simp only [sumVec]
    rw [sumFin_split (m := m) (n := n)]
    have hhi : sumFin n (fun b => sumVec r (m + n) (fun g => F (finSnoc g ⟨m + b.val, Nat.add_lt_add_left b.isLt m⟩))) = CRing.zero := by
      have hz : ∀ b : Fin n, sumVec r (m + n) (fun g => F (finSnoc g ⟨m + b.val, Nat.add_lt_add_left b.isLt m⟩)) = CRing.zero := by
        intro b
        rw [← sumVec_zero (m := r) (k := m + n)]
        apply sumVec_congr; intro g
        apply hvanish
        refine ⟨Fin.last r, ?_⟩
        rw [finSnoc_last]; simp
      rw [sumFin_congr hz, sumFin_zero]
    rw [hhi, CRing.add_zero]
    apply sumFin_congr; intro a
    rw [ih (fun g => F (finSnoc g ⟨a.val, Nat.lt_of_lt_of_le a.isLt (Nat.le_add_right m n)⟩))]
    · apply sumVec_congr; intro g
      congr 1; funext i; unfold finSnoc
      by_cases hi : i.val < r <;> simp [hi]
    · rintro g ⟨i, hi⟩
      apply hvanish
      refine ⟨i.castSucc, ?_⟩
      rw [finSnoc_castSucc]; exact hi

/-- Restrict `sumVec` from codomain `m + n` to `>= m` when terms vanish on `< m`. -/
theorem sumVec_restrict_hi {r m n : Nat} (F : (Fin r → Fin (m + n)) → R)
    (hvanish : ∀ f, (∃ i : Fin r, (f i).val < m) → F f = CRing.zero) :
    sumVec r (m + n) F =
    sumVec r n (fun g => F (fun i => ⟨m + (g i).val, Nat.add_lt_add_left (g i).isLt m⟩)) := by
  induction r with
  | zero =>
    change F Fin.elim0 = F (fun i => ⟨m + (Fin.elim0 (α := Fin n) i).val, _⟩)
    congr 1; funext i; exact Fin.elim0 i
  | succ r ih =>
    simp only [sumVec]
    rw [sumFin_split (m := m) (n := n)]
    have hlo : sumFin m (fun a => sumVec r (m + n) (fun g => F (finSnoc g ⟨a.val, Nat.lt_of_lt_of_le a.isLt (Nat.le_add_right m n)⟩))) = CRing.zero := by
      have hz : ∀ a : Fin m, sumVec r (m + n) (fun g => F (finSnoc g ⟨a.val, Nat.lt_of_lt_of_le a.isLt (Nat.le_add_right m n)⟩)) = CRing.zero := by
        intro a
        rw [← sumVec_zero (m := r) (k := m + n)]
        apply sumVec_congr; intro g
        apply hvanish
        refine ⟨Fin.last r, ?_⟩
        rw [finSnoc_last]; exact a.isLt
      rw [sumFin_congr hz, sumFin_zero]
    rw [hlo, CRing.zero_add]
    apply sumFin_congr; intro b
    rw [ih (fun g => F (finSnoc g ⟨m + b.val, Nat.add_lt_add_left b.isLt m⟩))]
    · apply sumVec_congr; intro g
      congr 1; funext i; unfold finSnoc
      by_cases hi : i.val < r <;> simp [hi]
    · rintro g ⟨i, hi⟩
      apply hvanish
      refine ⟨i.castSucc, ?_⟩
      rw [finSnoc_castSucc]; exact hi

end SumVecProps

/-! ### Levi-Civita Symbol `eps` via Pairwise Sign Product -/

def pairSign (a b : Nat) : Int :=
  if a < b then 1 else if a = b then 0 else -1

theorem pairSign_self (a : Nat) : pairSign a a = 0 := by
  unfold pairSign; simp

theorem pairSign_swap (a b : Nat) : pairSign b a = -(pairSign a b) := by
  unfold pairSign
  by_cases h1 : a < b
  · have h2 : ¬ b < a := by omega
    have h3 : b ≠ a := by omega
    simp [h1, h2, h3]
  · by_cases h2 : a = b
    · subst h2; simp
    · have h3 : b < a := by omega
      simp [h1, h2, h3]

theorem pairSign_lt {a b : Nat} (h : a < b) : pairSign a b = 1 := by
  unfold pairSign; simp [h]

theorem pairSign_gt {a b : Nat} (h : b < a) : pairSign a b = -1 := by
  unfold pairSign
  have h1 : ¬ a < b := by omega
  have h2 : a ≠ b := by omega
  simp [h1, h2]

def epsNat : (n : Nat) → (Fin n → Nat) → Int
  | 0, _ => 1
  | n + 1, f =>
    epsNat n (fun i => f i.castSucc) *
    prodFin (R := Int) n (fun i => pairSign (f i.castSucc) (f (Fin.last n)))

def eps {n : Nat} (f : Fin n → Fin n) : Int :=
  epsNat n (fun i => (f i).val)

theorem prodFin_swap_adj {R : Type u} [CRing R] {n : Nat} (j : Nat) (hj : j + 1 < n) (f : Fin n → R) :
    prodFin n (fun i => f (swapFin ⟨j, by omega⟩ ⟨j + 1, hj⟩ i)) = prodFin n f := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases htop : j + 1 = n
    · cases n with
      | zero => omega
      | succ n' =>
        have hjm : n' = j := by omega
        subst n'
        change CRing.mul
          (CRing.mul (prodFin j (fun i => f (swapFin ⟨j, by omega⟩ (Fin.last (j + 1)) i.castSucc.castSucc)))
                     (f (swapFin ⟨j, by omega⟩ (Fin.last (j + 1)) (Fin.last j).castSucc)))
          (f (swapFin ⟨j, by omega⟩ (Fin.last (j + 1)) (Fin.last (j + 1)))) =
          CRing.mul (CRing.mul (prodFin j (fun i => f i.castSucc.castSucc))
                               (f (Fin.last j).castSucc))
                    (f (Fin.last (j + 1)))
        have h1 : swapFin ⟨j, by omega⟩ (Fin.last (j + 1)) (Fin.last (j + 1)) = (Fin.last j).castSucc := by
          rw [swapFin_right]; exact Fin.ext rfl
        have h2 : swapFin ⟨j, by omega⟩ (Fin.last (j + 1)) (Fin.last j).castSucc = Fin.last (j + 1) := by
          have : (Fin.last j).castSucc = (⟨j, by omega⟩ : Fin (j + 2)) := Fin.ext rfl
          rw [this]; exact swapFin_left _ _
        have hlo : prodFin j (fun i => f (swapFin ⟨j, by omega⟩ (Fin.last (j + 1)) i.castSucc.castSucc)) =
                   prodFin j (fun i => f i.castSucc.castSucc) := by
          apply prodFin_congr; intro i
          have hsw : swapFin ⟨j, by omega⟩ (Fin.last (j + 1)) i.castSucc.castSucc = i.castSucc.castSucc := by
            unfold swapFin
            have hne1 : i.castSucc.castSucc ≠ (⟨j, by omega⟩ : Fin (j + 2)) := by
              intro h; have := congrArg Fin.val h; simp at this; omega
            have hne2 : i.castSucc.castSucc ≠ Fin.last (j + 1) := by
              intro h; have := congrArg Fin.val h; simp at this; omega
            simp [hne1, hne2]
          rw [hsw]
        rw [h1, h2, hlo, CRing.mul_assoc, CRing.mul_comm (f (Fin.last (j + 1))), ← CRing.mul_assoc]
    · have hj' : j + 1 < n := by omega
      simp only [prodFin]
      have hlast : swapFin ⟨j, by omega⟩ ⟨j + 1, hj⟩ (Fin.last n) = Fin.last n := by
        unfold swapFin
        have h1 : Fin.last n ≠ ⟨j, by omega⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
        have h2 : Fin.last n ≠ ⟨j + 1, hj⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
        simp [h1, h2]
      rw [hlast]
      congr 1
      rw [← ih hj' (fun i => f i.castSucc)]
      apply prodFin_congr; intro i
      congr 1
      unfold swapFin
      have hcast1 : i = ⟨j, by omega⟩ ↔ i.castSucc = ⟨j, by omega⟩ := by
        constructor
        · intro h; apply Fin.ext; have hv := congrArg Fin.val h; exact hv
        · intro h; apply Fin.ext; have hv := congrArg Fin.val h; exact hv
      have hcast2 : i = ⟨j + 1, hj'⟩ ↔ i.castSucc = ⟨j + 1, hj⟩ := by
        constructor
        · intro h; apply Fin.ext; have hv := congrArg Fin.val h; exact hv
        · intro h; apply Fin.ext; have hv := congrArg Fin.val h; exact hv
      by_cases h1 : i = ⟨j, by omega⟩
      · simp [h1]
      · have hn1 : i.castSucc ≠ ⟨j, by omega⟩ := fun h => h1 (hcast1.mpr h)
        by_cases h2 : i = ⟨j + 1, hj'⟩
        · simp [h2]
        · have hn2 : i.castSucc ≠ ⟨j + 1, hj⟩ := fun h => h2 (hcast2.mpr h)
          simp [h1, h2, hn1, hn2]

theorem epsNat_id (n : Nat) : epsNat n (fun i => i.val) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [epsNat, Fin.val_castSucc]
    rw [ih, Int.one_mul]
    rw [prodFin_congr (fun i => pairSign_lt (by simp [i.isLt]))]
    exact prodFin_one (R := Int) n

theorem epsNat_eq_zero_of_lt {n : Nat} (f : Fin n → Nat) (p q : Fin n) (hlt : p.val < q.val)
    (heq : f p = f q) : epsNat n f = 0 := by
  induction n with
  | zero => exact Fin.elim0 p
  | succ n ih =>
    simp only [epsNat]
    by_cases hq : q.val < n
    · have hp : p.val < n := Nat.lt_trans hlt hq
      have hfp : f (⟨p.val, hp⟩ : Fin n).castSucc = f p := congrArg f (Fin.ext rfl)
      have hfq : f (⟨q.val, hq⟩ : Fin n).castSucc = f q := congrArg f (Fin.ext rfl)
      have h0 := ih (fun i => f i.castSucc) ⟨p.val, hp⟩ ⟨q.val, hq⟩ hlt (by rw [hfp, hfq, heq])
      rw [h0, Int.zero_mul]
    · have hqeq : q = Fin.last n := by apply Fin.ext; simp; omega
      subst hqeq
      have hp : p.val < n := by simp at hlt; exact hlt
      have h0 : prodFin (R := Int) n (fun i => pairSign (f i.castSucc) (f (Fin.last n))) = 0 := by
        apply prodFin_eq_zero_of_exists (R := Int) _ ⟨p.val, hp⟩
        have : (⟨p.val, hp⟩ : Fin n).castSucc = p := Fin.ext rfl
        rw [this, heq, pairSign_self]; rfl
      rw [h0, Int.mul_zero]

theorem epsNat_eq_zero_of_eq {n : Nat} (f : Fin n → Nat) (p q : Fin n) (hne : p ≠ q)
    (heq : f p = f q) : epsNat n f = 0 := by
  by_cases hlt : p.val < q.val
  · exact epsNat_eq_zero_of_lt f p q hlt heq
  · have hgt : q.val < p.val := by
      have : p.val ≠ q.val := fun h => hne (Fin.ext h)
      omega
    exact epsNat_eq_zero_of_lt f q p hgt heq.symm

theorem epsNat_swap_adj {n : Nat} (j : Nat) (hj : j + 1 < n) (f : Fin n → Nat) :
    epsNat n (fun i => f (swapFin ⟨j, by omega⟩ ⟨j + 1, hj⟩ i)) = -(epsNat n f) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases htop : j + 1 = n
    · cases n with
      | zero => omega
      | succ n' =>
        have hjm : n' = j := by omega
        subst n'
        let s1 : Fin (j + 2) := ⟨j, by omega⟩
        let s2 : Fin (j + 2) := Fin.last (j + 1)
        have hs1_eq : s1 = (Fin.last j).castSucc := Fin.ext rfl
        have hsw_s2 : swapFin s1 s2 s2 = (Fin.last j).castSucc := by
          rw [swapFin_right]; exact hs1_eq
        have hsw_s1 : swapFin s1 s2 (Fin.last j).castSucc = s2 := by
          rw [← hs1_eq]; exact swapFin_left s1 s2
        have hsw_lo : ∀ i : Fin j, swapFin s1 s2 i.castSucc.castSucc = i.castSucc.castSucc := by
          intro i; unfold swapFin
          have h1 : i.castSucc.castSucc ≠ s1 := by intro h; have := congrArg Fin.val h; simp [s1] at this; omega
          have h2 : i.castSucc.castSucc ≠ s2 := by intro h; have := congrArg Fin.val h; simp [s2] at this; omega
          simp [h1, h2]
        change (epsNat j (fun i => f (swapFin s1 s2 i.castSucc.castSucc)) *
                prodFin (R := Int) j (fun i => pairSign (f (swapFin s1 s2 i.castSucc.castSucc))
                                                        (f (swapFin s1 s2 (Fin.last j).castSucc)))) *
               (prodFin (R := Int) j (fun i => pairSign (f (swapFin s1 s2 i.castSucc.castSucc))
                                                        (f (swapFin s1 s2 s2))) *
                pairSign (f (swapFin s1 s2 (Fin.last j).castSucc)) (f (swapFin s1 s2 s2))) =
               -((epsNat j (fun i => f i.castSucc.castSucc) *
                  prodFin (R := Int) j (fun i => pairSign (f i.castSucc.castSucc) (f (Fin.last j).castSucc))) *
                 (prodFin (R := Int) j (fun i => pairSign (f i.castSucc.castSucc) (f s2)) *
                  pairSign (f (Fin.last j).castSucc) (f s2)))
        simp only [hsw_lo, hsw_s1, hsw_s2]
        rw [pairSign_swap (f (Fin.last j).castSucc) (f s2)]
        rw [Int.mul_neg, Int.mul_neg]
        congr 1
        let A := epsNat j (fun i => f i.castSucc.castSucc)
        let B := prodFin (R := Int) j (fun i => pairSign (f i.castSucc.castSucc) (f (Fin.last j).castSucc))
        let C := prodFin (R := Int) j (fun i => pairSign (f i.castSucc.castSucc) (f s2))
        let D := pairSign (f (Fin.last j).castSucc) (f s2)
        change (A * C) * (B * D) = (A * B) * (C * D)
        rw [Int.mul_assoc, Int.mul_assoc, ← Int.mul_assoc C B D, Int.mul_comm C B, Int.mul_assoc]
    · have hj' : j + 1 < n := by omega
      change epsNat n (fun i => f (swapFin ⟨j, by omega⟩ ⟨j + 1, hj⟩ i.castSucc)) *
             prodFin (R := Int) n (fun i => pairSign (f (swapFin ⟨j, by omega⟩ ⟨j + 1, hj⟩ i.castSucc))
                                                     (f (swapFin ⟨j, by omega⟩ ⟨j + 1, hj⟩ (Fin.last n)))) =
             -(epsNat n (fun i => f i.castSucc) *
               prodFin (R := Int) n (fun i => pairSign (f i.castSucc) (f (Fin.last n))))
      have hlast : swapFin ⟨j, by omega⟩ ⟨j + 1, hj⟩ (Fin.last n) = Fin.last n := by
        unfold swapFin
        have h1 : Fin.last n ≠ ⟨j, by omega⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
        have h2 : Fin.last n ≠ ⟨j + 1, hj⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
        simp [h1, h2]
      rw [hlast]
      have hcast_sw : ∀ i : Fin n,
          swapFin ⟨j, by omega⟩ ⟨j + 1, hj⟩ i.castSucc = (swapFin ⟨j, by omega⟩ ⟨j + 1, hj'⟩ i).castSucc := by
        intro i; unfold swapFin
        have h1 : i.castSucc = ⟨j, by omega⟩ ↔ i = ⟨j, by omega⟩ := by
          constructor
          · intro h; apply Fin.ext; have hv := congrArg Fin.val h; exact hv
          · intro h; apply Fin.ext; have hv := congrArg Fin.val h; exact hv
        have h2 : i.castSucc = ⟨j + 1, hj⟩ ↔ i = ⟨j + 1, hj'⟩ := by
          constructor
          · intro h; apply Fin.ext; have hv := congrArg Fin.val h; exact hv
          · intro h; apply Fin.ext; have hv := congrArg Fin.val h; exact hv
        by_cases c1 : i = ⟨j, by omega⟩
        · simp [c1]
        · have cn1 : i.castSucc ≠ ⟨j, by omega⟩ := fun h => c1 (h1.mp h)
          by_cases c2 : i = ⟨j + 1, hj'⟩
          · simp [c2]
          · have cn2 : i.castSucc ≠ ⟨j + 1, hj⟩ := fun h => c2 (h2.mp h)
            simp [c1, c2, cn1, cn2]
      have heps : epsNat n (fun i => f (swapFin ⟨j, by omega⟩ ⟨j + 1, hj⟩ i.castSucc)) =
                  -(epsNat n (fun i => f i.castSucc)) := by
        rw [show (fun i : Fin n => f (swapFin ⟨j, by omega⟩ ⟨j + 1, hj⟩ i.castSucc)) =
                 (fun i : Fin n => f (swapFin ⟨j, by omega⟩ ⟨j + 1, hj'⟩ i).castSucc) from
              funext (fun i => by rw [hcast_sw])]
        exact ih hj' (fun i => f i.castSucc)
      have hprod : prodFin (R := Int) n (fun i => pairSign (f (swapFin ⟨j, by omega⟩ ⟨j + 1, hj⟩ i.castSucc)) (f (Fin.last n))) =
                   prodFin (R := Int) n (fun i => pairSign (f i.castSucc) (f (Fin.last n))) := by
        rw [show (fun i : Fin n => pairSign (f (swapFin ⟨j, by omega⟩ ⟨j + 1, hj⟩ i.castSucc)) (f (Fin.last n))) =
                 (fun i : Fin n => pairSign (f (swapFin ⟨j, by omega⟩ ⟨j + 1, hj'⟩ i).castSucc) (f (Fin.last n))) from
              funext (fun i => by rw [hcast_sw])]
        exact prodFin_swap_adj (R := Int) j hj' (fun i => pairSign (f i.castSucc) (f (Fin.last n)))
      rw [heps, hprod, Int.neg_mul]

/-- General transposition flips `epsNat` whenever `p ≠ q`. -/
theorem epsNat_swap {n : Nat} (p q : Fin n) (hpq : p ≠ q) (f : Fin n → Nat) :
    epsNat n (fun i => f (swapFin p q i)) = -(epsNat n f) := by
  suffices h : ∀ (d : Nat) (p q : Fin n), p.val + (d + 1) = q.val →
      ∀ f : Fin n → Nat, epsNat n (fun i => f (swapFin p q i)) = -(epsNat n f) by
    by_cases hlt : p.val < q.val
    · exact h (q.val - p.val - 1) p q (by omega) f
    · have hgt : q.val < p.val := by
        have : p.val ≠ q.val := fun heq => hpq (Fin.ext heq)
        omega
      rw [show (fun i => f (swapFin p q i)) = (fun i => f (swapFin q p i)) from
            funext (fun i => by rw [swapFin_comm])]
      exact h (p.val - q.val - 1) q p (by omega) f
  intro d
  induction d with
  | zero =>
    intro p q hpq f
    have hj : p.val + 1 < n := by omega
    have hq : q = ⟨p.val + 1, hj⟩ := Fin.ext (by simp; omega)
    subst hq
    exact epsNat_swap_adj p.val hj f
  | succ d ih =>
    intro p q hpq f
    have hr_lt : p.val + d + 1 < n := by omega
    let r : Fin n := ⟨p.val + d + 1, hr_lt⟩
    have hpr : p.val + (d + 1) = r.val := by simp [r]; omega
    have hq_eq : q = ⟨r.val + 1, by simp [r]; omega⟩ := Fin.ext (by simp [r]; omega)
    have hr_eq : (⟨r.val, by omega⟩ : Fin n) = r := Fin.ext rfl
    have hdecomp : ∀ i : Fin n,
        swapFin p q i = swapFin r q (swapFin p r (swapFin r q i)) := by
      intro i
      have hne_pr : p ≠ r := by intro h; have := congrArg Fin.val h; simp [r] at this; omega
      have hne_pq : p ≠ q := by intro h; have := congrArg Fin.val h; omega
      have hne_rq : r ≠ q := by intro h; have := congrArg Fin.val h; simp [r] at this; omega
      by_cases h1 : i = p
      · subst h1
        have : swapFin r q i = i := by unfold swapFin; simp [hne_pr, hne_pq]
        rw [swapFin_left, this, swapFin_left, swapFin_left]
      · by_cases h2 : i = q
        · subst h2
          rw [swapFin_right, swapFin_right, swapFin_right]
          unfold swapFin; simp [hne_pr, hne_pq]
        · by_cases h3 : i = r
          · subst h3
            rw [swapFin_left]
            have : swapFin p r q = q := by unfold swapFin; simp [Ne.symm hne_pq, Ne.symm hne_rq]
            rw [this, swapFin_right]
            unfold swapFin; simp [h1, h2]
          · have s1 : swapFin r q i = i := by unfold swapFin; simp [h3, h2]
            have s2 : swapFin p r i = i := by unfold swapFin; simp [h1, h3]
            have s3 : swapFin p q i = i := by unfold swapFin; simp [h1, h2]
            rw [s1, s2, s1, s3]
    have hstep1 : epsNat n (fun i => f (swapFin r q (swapFin p r (swapFin r q i)))) =
                  -(epsNat n (fun i => f (swapFin r q (swapFin p r i)))) := by
      have hadj := epsNat_swap_adj r.val (by simp [r]; omega)
        (fun i => f (swapFin r q (swapFin p r i)))
      rw [hr_eq, ← hq_eq] at hadj
      exact hadj
    have hstep2 : epsNat n (fun i => f (swapFin r q (swapFin p r i))) =
                  -(epsNat n (fun i => f (swapFin r q i))) :=
      ih p r hpr (fun i => f (swapFin r q i))
    have hstep3 : epsNat n (fun i => f (swapFin r q i)) = -(epsNat n f) := by
      have hadj := epsNat_swap_adj r.val (by simp [r]; omega) f
      rw [hr_eq, ← hq_eq] at hadj
      exact hadj
    rw [show (fun i => f (swapFin p q i)) = (fun i => f (swapFin r q (swapFin p r (swapFin r q i)))) from
          funext (fun i => by rw [hdecomp])]
    rw [hstep1, hstep2, hstep3]; omega

theorem epsNat_split {m n : Nat} (f1 : Fin m → Nat) (f2 : Fin n → Nat) :
    epsNat (m + n) (finAppend f1 f2) =
    epsNat m f1 * epsNat n f2 *
    prodFin (R := Int) n (fun j => prodFin (R := Int) m (fun i => pairSign (f1 i) (f2 j))) := by
  induction n with
  | zero =>
    change epsNat m (finAppend f1 f2) = epsNat m f1 * 1 * 1
    rw [Int.mul_one, Int.mul_one]
    congr 1; funext i; unfold finAppend; simp
  | succ n ih =>
    change epsNat (m + n) (fun i => finAppend f1 f2 i.castSucc) *
           prodFin (R := Int) (m + n) (fun i => pairSign (finAppend f1 f2 i.castSucc) (finAppend f1 f2 (Fin.last (m + n)))) =
           epsNat m f1 * (epsNat n (fun j => f2 j.castSucc) *
                          prodFin (R := Int) n (fun j => pairSign (f2 j.castSucc) (f2 (Fin.last n)))) *
           (prodFin (R := Int) n (fun j => prodFin (R := Int) m (fun i => pairSign (f1 i) (f2 j.castSucc))) *
            prodFin (R := Int) m (fun i => pairSign (f1 i) (f2 (Fin.last n))))
    have hcast : (fun i : Fin (m + n) => finAppend f1 f2 i.castSucc) =
                 finAppend f1 (fun j : Fin n => f2 j.castSucc) := by
      funext i; unfold finAppend
      by_cases h : i.val < m <;> simp [h]
    have hlast : finAppend f1 f2 (Fin.last (m + n)) = f2 (Fin.last n) := by
      unfold finAppend
      have h : ¬ (m + n < m) := by omega
      simp only [Fin.val_last, h, dite_false]
      congr 1; apply Fin.ext; simp
    rw [hcast, hlast, ih (fun j => f2 j.castSucc)]
    have hprod_cast : prodFin (R := Int) (m + n) (fun i => pairSign (finAppend f1 f2 i.castSucc) (f2 (Fin.last n))) =
                      prodFin (R := Int) (m + n) (fun i => pairSign (finAppend f1 (fun j => f2 j.castSucc) i) (f2 (Fin.last n))) :=
      prodFin_congr (fun i => by rw [congrFun hcast i])
    rw [hprod_cast, prodFin_split (R := Int) (m := m) (n := n)]
    have hlo : prodFin (R := Int) m (fun i => pairSign (finAppend f1 (fun j => f2 j.castSucc) ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right m n)⟩) (f2 (Fin.last n))) =
               prodFin (R := Int) m (fun i => pairSign (f1 i) (f2 (Fin.last n))) := by
      apply prodFin_congr; intro i; unfold finAppend; simp [i.isLt]
    have hhi : prodFin (R := Int) n (fun j => pairSign (finAppend f1 (fun j => f2 j.castSucc) ⟨m + j.val, Nat.add_lt_add_left j.isLt m⟩) (f2 (Fin.last n))) =
               prodFin (R := Int) n (fun j => pairSign (f2 j.castSucc) (f2 (Fin.last n))) := by
      apply prodFin_congr; intro j; unfold finAppend
      have h : ¬ (m + j.val < m) := by omega
      simp [h]
    rw [hlo, hhi]
    change (epsNat m f1 * epsNat n (fun j => f2 j.castSucc) *
            prodFin (R := Int) n (fun j => prodFin (R := Int) m (fun i => pairSign (f1 i) (f2 j.castSucc)))) *
           (prodFin (R := Int) m (fun i => pairSign (f1 i) (f2 (Fin.last n))) *
            prodFin (R := Int) n (fun j => pairSign (f2 j.castSucc) (f2 (Fin.last n)))) = _
    let A := epsNat m f1
    let B := epsNat n (fun j => f2 j.castSucc)
    let C := prodFin (R := Int) n (fun j => prodFin (R := Int) m (fun i => pairSign (f1 i) (f2 j.castSucc)))
    let D := prodFin (R := Int) m (fun i => pairSign (f1 i) (f2 (Fin.last n)))
    let E := prodFin (R := Int) n (fun j => pairSign (f2 j.castSucc) (f2 (Fin.last n)))
    change A * B * C * (D * E) = A * (B * E) * (C * D)
    calc A * B * C * (D * E)
        = A * (B * C * (E * D)) := by rw [Int.mul_comm D E, Int.mul_assoc A B C, Int.mul_assoc A (B * C)]
      _ = A * (B * (E * (C * D))) := by
            congr 1
            rw [Int.mul_assoc B C (E * D), ← Int.mul_assoc C E D, Int.mul_comm C E, Int.mul_assoc E C D]
      _ = A * (B * E) * (C * D) := by rw [← Int.mul_assoc B E (C * D), ← Int.mul_assoc A (B * E)]

def sumFinNat : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => sumFinNat n (fun i => f i.castSucc) + f (Fin.last n)

theorem sumFinNat_congr {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i = g i) :
    sumFinNat n f = sumFinNat n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumFinNat]; rw [ih (fun i => h i.castSucc), h (Fin.last n)]

theorem sumFinNat_eq_zero_iff {n : Nat} (f : Fin n → Nat) :
    sumFinNat n f = 0 ↔ ∀ i : Fin n, f i = 0 := by
  induction n with
  | zero => exact ⟨fun _ i => Fin.elim0 i, fun _ => rfl⟩
  | succ n ih =>
    simp only [sumFinNat]
    constructor
    · intro h i
      have h1 : sumFinNat n (fun k => f k.castSucc) = 0 := by omega
      have h2 : f (Fin.last n) = 0 := by omega
      by_cases hi : i.val < n
      · have : i = (⟨i.val, hi⟩ : Fin n).castSucc := Fin.ext rfl
        rw [this]; exact (ih _).mp h1 ⟨i.val, hi⟩
      · have : i = Fin.last n := by apply Fin.ext; simp; omega
        rw [this]; exact h2
    · intro h
      have h1 := (ih (fun k => f k.castSucc)).mpr (fun k => h k.castSucc)
      rw [h1, h (Fin.last n)]

theorem sumFinNat_swap_adj {n : Nat} (j : Nat) (hj : j + 1 < n) (f : Fin n → Nat) :
    sumFinNat n (fun i => f (swapFin ⟨j, by omega⟩ ⟨j + 1, hj⟩ i)) = sumFinNat n f := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases htop : j + 1 = n
    · cases n with
      | zero => omega
      | succ n' =>
        have hjm : n' = j := by omega
        subst n'
        change sumFinNat j (fun i => f (swapFin ⟨j, by omega⟩ (Fin.last (j + 1)) i.castSucc.castSucc)) +
               f (swapFin ⟨j, by omega⟩ (Fin.last (j + 1)) (Fin.last j).castSucc) +
               f (swapFin ⟨j, by omega⟩ (Fin.last (j + 1)) (Fin.last (j + 1))) =
               sumFinNat j (fun i => f i.castSucc.castSucc) + f (Fin.last j).castSucc + f (Fin.last (j + 1))
        have h1 : swapFin ⟨j, by omega⟩ (Fin.last (j + 1)) (Fin.last (j + 1)) = (Fin.last j).castSucc := by
          rw [swapFin_right]; exact Fin.ext rfl
        have h2 : swapFin ⟨j, by omega⟩ (Fin.last (j + 1)) (Fin.last j).castSucc = Fin.last (j + 1) := by
          have : (Fin.last j).castSucc = (⟨j, by omega⟩ : Fin (j + 2)) := Fin.ext rfl
          rw [this]; exact swapFin_left _ _
        have hlo : sumFinNat j (fun i => f (swapFin ⟨j, by omega⟩ (Fin.last (j + 1)) i.castSucc.castSucc)) =
                   sumFinNat j (fun i => f i.castSucc.castSucc) := by
          apply sumFinNat_congr; intro i
          have hsw : swapFin ⟨j, by omega⟩ (Fin.last (j + 1)) i.castSucc.castSucc = i.castSucc.castSucc := by
            unfold swapFin
            have hne1 : i.castSucc.castSucc ≠ (⟨j, by omega⟩ : Fin (j + 2)) := by
              intro h; have := congrArg Fin.val h; simp at this; omega
            have hne2 : i.castSucc.castSucc ≠ Fin.last (j + 1) := by
              intro h; have := congrArg Fin.val h; simp at this; omega
            simp [hne1, hne2]
          rw [hsw]
        rw [h1, h2, hlo]; omega
    · have hj' : j + 1 < n := by omega
      simp only [sumFinNat]
      have hlast : swapFin ⟨j, by omega⟩ ⟨j + 1, hj⟩ (Fin.last n) = Fin.last n := by
        unfold swapFin
        have h1 : Fin.last n ≠ ⟨j, by omega⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
        have h2 : Fin.last n ≠ ⟨j + 1, hj⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
        simp [h1, h2]
      rw [hlast]
      congr 1
      rw [← ih hj' (fun i => f i.castSucc)]
      apply sumFinNat_congr; intro i; congr 1
      unfold swapFin
      have hcast1 : i = ⟨j, by omega⟩ ↔ i.castSucc = ⟨j, by omega⟩ := by
        constructor
        · intro h; apply Fin.ext; have hv := congrArg Fin.val h; exact hv
        · intro h; apply Fin.ext; have hv := congrArg Fin.val h; exact hv
      have hcast2 : i = ⟨j + 1, hj'⟩ ↔ i.castSucc = ⟨j + 1, hj⟩ := by
        constructor
        · intro h; apply Fin.ext; have hv := congrArg Fin.val h; exact hv
        · intro h; apply Fin.ext; have hv := congrArg Fin.val h; exact hv
      by_cases h1 : i = ⟨j, by omega⟩
      · simp [h1]
      · have hn1 : i.castSucc ≠ ⟨j, by omega⟩ := fun h => h1 (hcast1.mpr h)
        by_cases h2 : i = ⟨j + 1, hj'⟩
        · simp [h2]
        · have hn2 : i.castSucc ≠ ⟨j + 1, hj⟩ := fun h => h2 (hcast2.mpr h)
          simp [h1, h2, hn1, hn2]

def invCount : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, h =>
    invCount n (fun i => h i.castSucc) +
    sumFinNat n (fun i => if h (Fin.last n) < h i.castSucc then 1 else 0)

theorem invCount_zero_of_mono {n : Nat} (h : Fin n → Nat)
    (hmono : ∀ j : Nat, (hj : j + 1 < n) → h ⟨j, by omega⟩ ≤ h ⟨j + 1, hj⟩) :
    invCount n h = 0 := by
  have hle : ∀ i j : Fin n, i.val ≤ j.val → h i ≤ h j := by
    suffices ∀ d (i j : Fin n), i.val + d = j.val → h i ≤ h j by
      intro i j hij; exact this (j.val - i.val) i j (by omega)
    intro d
    induction d with
    | zero => intro i j hij; have : i = j := Fin.ext (by omega); rw [this]; exact Nat.le_refl _
    | succ d ih =>
      intro i j hij
      have hlt : i.val + d < n := by omega
      have hstep := hmono (i.val + d) (by omega)
      have hj : (⟨i.val + d + 1, by omega⟩ : Fin n) = j := Fin.ext (by dsimp only; omega)
      rw [hj] at hstep
      exact Nat.le_trans (ih i ⟨i.val + d, hlt⟩ rfl) hstep
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [invCount]
    have h1 := ih (fun i => h i.castSucc)
      (fun j hj => hmono j (Nat.lt_succ_of_lt hj))
      (fun i j hij => hle i.castSucc j.castSucc hij)
    have h2 : sumFinNat n (fun i => if h (Fin.last n) < h i.castSucc then 1 else 0) = 0 := by
      rw [sumFinNat_eq_zero_iff]
      intro i
      have := hle i.castSucc (Fin.last n) (by simp only [Fin.val_castSucc, Fin.val_last]; exact Nat.le_of_lt i.isLt)
      have hnot : ¬ h (Fin.last n) < h i.castSucc := by omega
      simp [hnot]
    rw [h1, h2]

theorem invCount_swap_adj_dec {n : Nat} (j : Nat) (hj : j + 1 < n) (h : Fin n → Nat)
    (hinv : h ⟨j + 1, hj⟩ < h ⟨j, by omega⟩) :
    invCount n (fun i => h (swapFin ⟨j, by omega⟩ ⟨j + 1, hj⟩ i)) + 1 = invCount n h := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases htop : j + 1 = n
    · cases n with
      | zero => omega
      | succ n' =>
        have hjm : n' = j := by omega
        subst n'
        let s1 : Fin (j + 2) := ⟨j, by omega⟩
        let s2 : Fin (j + 2) := Fin.last (j + 1)
        have hs1_eq : s1 = (Fin.last j).castSucc := Fin.ext rfl
        have hsw_s2 : swapFin s1 s2 s2 = (Fin.last j).castSucc := by
          rw [swapFin_right]; exact hs1_eq
        have hsw_s1 : swapFin s1 s2 (Fin.last j).castSucc = s2 := by
          rw [← hs1_eq]; exact swapFin_left s1 s2
        have hsw_lo : ∀ i : Fin j, swapFin s1 s2 i.castSucc.castSucc = i.castSucc.castSucc := by
          intro i; unfold swapFin
          have h1 : i.castSucc.castSucc ≠ s1 := by intro h; have := congrArg Fin.val h; simp [s1] at this; omega
          have h2 : i.castSucc.castSucc ≠ s2 := by intro h; have := congrArg Fin.val h; simp [s2] at this; omega
          simp [h1, h2]
        change (invCount j (fun i => h (swapFin s1 s2 i.castSucc.castSucc)) +
                sumFinNat j (fun i => if h (swapFin s1 s2 (Fin.last j).castSucc) < h (swapFin s1 s2 i.castSucc.castSucc) then 1 else 0)) +
               (sumFinNat j (fun i => if h (swapFin s1 s2 s2) < h (swapFin s1 s2 i.castSucc.castSucc) then 1 else 0) +
                (if h (swapFin s1 s2 s2) < h (swapFin s1 s2 (Fin.last j).castSucc) then 1 else 0)) + 1 =
               (invCount j (fun i => h i.castSucc.castSucc) +
                sumFinNat j (fun i => if h (Fin.last j).castSucc < h i.castSucc.castSucc then 1 else 0)) +
               (sumFinNat j (fun i => if h s2 < h i.castSucc.castSucc then 1 else 0) +
                (if h s2 < h (Fin.last j).castSucc then 1 else 0))
        simp only [hsw_lo, hsw_s1, hsw_s2]
        have hlt1 : h s2 < h (Fin.last j).castSucc := hinv
        have hnot : ¬ h (Fin.last j).castSucc < h s2 := by omega
        simp only [hlt1, hnot, ite_true, ite_false]
        omega
    · have hj' : j + 1 < n := by omega
      change invCount n (fun i => h (swapFin ⟨j, by omega⟩ ⟨j + 1, hj⟩ i.castSucc)) +
             sumFinNat n (fun i => if h (swapFin ⟨j, by omega⟩ ⟨j + 1, hj⟩ (Fin.last n)) <
                                      h (swapFin ⟨j, by omega⟩ ⟨j + 1, hj⟩ i.castSucc) then 1 else 0) + 1 =
             invCount n (fun i => h i.castSucc) +
             sumFinNat n (fun i => if h (Fin.last n) < h i.castSucc then 1 else 0)
      have hlast : swapFin ⟨j, by omega⟩ ⟨j + 1, hj⟩ (Fin.last n) = Fin.last n := by
        unfold swapFin
        have h1 : Fin.last n ≠ ⟨j, by omega⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
        have h2 : Fin.last n ≠ ⟨j + 1, hj⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
        simp [h1, h2]
      rw [hlast]
      have hcast_sw : ∀ i : Fin n,
          swapFin ⟨j, by omega⟩ ⟨j + 1, hj⟩ i.castSucc = (swapFin ⟨j, by omega⟩ ⟨j + 1, hj'⟩ i).castSucc := by
        intro i; unfold swapFin
        have h1 : i.castSucc = ⟨j, by omega⟩ ↔ i = ⟨j, by omega⟩ := by
          constructor
          · intro h; apply Fin.ext; have hv := congrArg Fin.val h; exact hv
          · intro h; apply Fin.ext; have hv := congrArg Fin.val h; exact hv
        have h2 : i.castSucc = ⟨j + 1, hj⟩ ↔ i = ⟨j + 1, hj'⟩ := by
          constructor
          · intro h; apply Fin.ext; have hv := congrArg Fin.val h; exact hv
          · intro h; apply Fin.ext; have hv := congrArg Fin.val h; exact hv
        by_cases c1 : i = ⟨j, by omega⟩
        · simp [c1]
        · have cn1 : i.castSucc ≠ ⟨j, by omega⟩ := fun h => c1 (h1.mp h)
          by_cases c2 : i = ⟨j + 1, hj'⟩
          · simp [c2]
          · have cn2 : i.castSucc ≠ ⟨j + 1, hj⟩ := fun h => c2 (h2.mp h)
            simp [c1, c2, cn1, cn2]
      have hrec : invCount n (fun i => h (swapFin ⟨j, by omega⟩ ⟨j + 1, hj⟩ i.castSucc)) + 1 =
                  invCount n (fun i => h i.castSucc) := by
        rw [show (fun i : Fin n => h (swapFin ⟨j, by omega⟩ ⟨j + 1, hj⟩ i.castSucc)) =
                 (fun i : Fin n => h (swapFin ⟨j, by omega⟩ ⟨j + 1, hj'⟩ i).castSucc) from
              funext (fun i => by rw [hcast_sw])]
        exact ih hj' (fun i => h i.castSucc) hinv
      have hsum : sumFinNat n (fun i => if h (Fin.last n) < h (swapFin ⟨j, by omega⟩ ⟨j + 1, hj⟩ i.castSucc) then 1 else 0) =
                  sumFinNat n (fun i => if h (Fin.last n) < h i.castSucc then 1 else 0) := by
        rw [show (fun i : Fin n => if h (Fin.last n) < h (swapFin ⟨j, by omega⟩ ⟨j + 1, hj⟩ i.castSucc) then 1 else 0) =
                 (fun i : Fin n => if h (Fin.last n) < h (swapFin ⟨j, by omega⟩ ⟨j + 1, hj'⟩ i).castSucc then 1 else 0) from
              funext (fun i => by rw [hcast_sw])]
        exact sumFinNat_swap_adj j hj' (fun i => if h (Fin.last n) < h i.castSucc then 1 else 0)
      rw [hsum]; omega

/-- Constructive search for an adjacent inversion when `invCount > 0`. -/
theorem exists_adj_inv_of_invCount_pos {n : Nat} (h : Fin n → Nat) (hpos : 0 < invCount n h) :
    ∃ j : Nat, ∃ hj : j + 1 < n, h ⟨j + 1, hj⟩ < h ⟨j, by omega⟩ := by
  suffices ∀ (k : Nat) (hk : k ≤ n),
      (∀ j : Nat, (hj : j + 1 < k) → h ⟨j, by omega⟩ ≤ h ⟨j + 1, by omega⟩) ∨
      (∃ j : Nat, ∃ hj : j + 1 < k, h ⟨j + 1, by omega⟩ < h ⟨j, by omega⟩) by
    rcases this n (Nat.le_refl n) with hmono | ⟨j, hj, hlt⟩
    · exfalso
      have := invCount_zero_of_mono h hmono
      omega
    · exact ⟨j, hj, hlt⟩
  intro k
  induction k with
  | zero => intro _; left; intro j hj; omega
  | succ k ih =>
    intro hk
    rcases ih (Nat.le_of_lt hk) with hmono | ⟨j, hj, hlt⟩
    · cases k with
      | zero => left; intro j hj; omega
      | succ k' =>
        by_cases hcmp : h ⟨k', by omega⟩ ≤ h ⟨k' + 1, by omega⟩
        · left
          intro j hj
          by_cases hlast : j = k'
          · subst hlast; exact hcmp
          · exact hmono j (by omega)
        · right
          exact ⟨k', by omega, by omega⟩
    · right
      exact ⟨j, Nat.lt_succ_of_lt hj, hlt⟩

/-! ### Matrices, Block Matrices, and Genuine Leibniz Determinant -/

abbrev Mat (R : Type u) (n : Nat) := Fin n → Fin n → R

section MatDefs
variable {R : Type u} [CRing R]

def matZero (n : Nat) : Mat R n := fun _ _ => CRing.zero

def matOne (n : Nat) : Mat R n := fun i j => if i = j then CRing.one else CRing.zero

def matAdd {n : Nat} (A B : Mat R n) : Mat R n := fun i j => CRing.add (A i j) (B i j)

def matNeg {n : Nat} (A : Mat R n) : Mat R n := fun i j => CRing.neg (A i j)

def matSub {n : Nat} (A B : Mat R n) : Mat R n := fun i j => CRing.sub (A i j) (B i j)

def matSmul {n : Nat} (c : R) (A : Mat R n) : Mat R n := fun i j => CRing.mul c (A i j)

def matMul {n : Nat} (A B : Mat R n) : Mat R n :=
  fun i j => sumFin n (fun k => CRing.mul (A i k) (B k j))

def blockMat {m n : Nat}
    (A : Fin m → Fin m → R) (B : Fin m → Fin n → R)
    (C : Fin n → Fin m → R) (D : Fin n → Fin n → R) : Mat R (m + n) :=
  fun i j =>
    if hi : i.val < m then
      if hj : j.val < m then A ⟨i.val, hi⟩ ⟨j.val, hj⟩
      else B ⟨i.val, hi⟩ ⟨j.val - m, by omega⟩
    else
      if hj : j.val < m then C ⟨i.val - m, by omega⟩ ⟨j.val, hj⟩
      else D ⟨i.val - m, by omega⟩ ⟨j.val - m, by omega⟩

/-- Genuine classical Leibniz determinant via Levi-Civita sum over `Fin n -> Fin n`. -/
def det {n : Nat} (M : Mat R n) : R :=
  sumVec n n (fun f => CRing.mul (CRing.ofInt (eps f)) (prodFin n (fun i => M i (f i))))

theorem matMul_one_left {n : Nat} (A : Mat R n) : matMul (matOne n) A = A := by
  funext i j; unfold matMul matOne
  rw [sumFin_single i]
  · simp [CRing.one_mul]
  · intro k hk; simp [Ne.symm hk, CRing.zero_mul]

theorem matMul_one_right {n : Nat} (A : Mat R n) : matMul A (matOne n) = A := by
  funext i j; unfold matMul matOne
  rw [sumFin_single j]
  · simp [CRing.mul_one]
  · intro k hk; simp [hk, CRing.mul_zero]

theorem matMul_zero_left {n : Nat} (A : Mat R n) : matMul (matZero n) A = matZero n := by
  funext i j; unfold matMul matZero
  rw [sumFin_congr (fun _ => CRing.zero_mul _), sumFin_zero]

theorem matMul_zero_right {n : Nat} (A : Mat R n) : matMul A (matZero n) = matZero n := by
  funext i j; unfold matMul matZero
  rw [sumFin_congr (fun _ => CRing.mul_zero _), sumFin_zero]

theorem matMul_smul_left {n : Nat} (c : R) (A B : Mat R n) :
    matMul (matSmul c A) B = matSmul c (matMul A B) := by
  funext i j; unfold matMul matSmul
  rw [sumFin_mul_left]
  exact sumFin_congr (fun k => CRing.mul_assoc c (A i k) (B k j))

theorem matMul_smul_right {n : Nat} (c : R) (A B : Mat R n) :
    matMul A (matSmul c B) = matSmul c (matMul A B) := by
  funext i j; unfold matMul matSmul
  rw [sumFin_mul_left]
  exact sumFin_congr (fun k => by rw [CRing.mul_comm (A i k), CRing.mul_assoc, CRing.mul_comm (B k j)])

theorem matMul_neg_left {n : Nat} (A B : Mat R n) :
    matMul (matNeg A) B = matNeg (matMul A B) := by
  funext i j; unfold matMul matNeg
  rw [← sumFin_neg]
  exact sumFin_congr (fun k => CRing.neg_mul (A i k) (B k j))

theorem matMul_neg_right {n : Nat} (A B : Mat R n) :
    matMul A (matNeg B) = matNeg (matMul A B) := by
  funext i j; unfold matMul matNeg
  rw [← sumFin_neg]
  exact sumFin_congr (fun k => CRing.mul_neg (A i k) (B k j))

theorem matAdd_zero_left {n : Nat} (A : Mat R n) : matAdd (matZero n) A = A := by
  funext i j; exact CRing.zero_add (A i j)

theorem matAdd_zero_right {n : Nat} (A : Mat R n) : matAdd A (matZero n) = A := by
  funext i j; exact CRing.add_zero (A i j)

theorem blockMat_mul {n : Nat} (A1 B1 C1 D1 A2 B2 C2 D2 : Mat R n) :
    matMul (blockMat A1 B1 C1 D1) (blockMat A2 B2 C2 D2) =
    blockMat (matAdd (matMul A1 A2) (matMul B1 C2))
             (matAdd (matMul A1 B2) (matMul B1 D2))
             (matAdd (matMul C1 A2) (matMul D1 C2))
             (matAdd (matMul C1 B2) (matMul D1 D2)) := by
  funext i j
  unfold matMul blockMat matAdd
  rw [sumFin_split (m := n) (n := n)]
  by_cases hi : i.val < n <;> by_cases hj : j.val < n
  · simp only [hi, hj, dite_true]
    congr 1
    · apply sumFin_congr; intro k; simp [k.isLt]
    · apply sumFin_congr; intro k
      have hk : ¬ (n + k.val < n) := by omega
      simp [hk]
  · simp only [hi, hj, dite_true, dite_false]
    congr 1
    · apply sumFin_congr; intro k; simp [k.isLt]
    · apply sumFin_congr; intro k
      have hk : ¬ (n + k.val < n) := by omega
      simp [hk]
  · simp only [hi, hj, dite_true, dite_false]
    congr 1
    · apply sumFin_congr; intro k; simp [k.isLt]
    · apply sumFin_congr; intro k
      have hk : ¬ (n + k.val < n) := by omega
      simp [hk]
  · simp only [hi, hj, dite_false]
    congr 1
    · apply sumFin_congr; intro k; simp [k.isLt]
    · apply sumFin_congr; intro k
      have hk : ¬ (n + k.val < n) := by omega
      simp [hk]

/-! ### Core Determinant Theorems (Zero-Circularity Proofs from Leibniz Definition) -/

theorem det_one (n : Nat) : det (matOne (R := R) n) = CRing.one := by
  unfold det
  suffices h : ∀ (m : Nat) (hm : m ≤ n) (G : (Fin m → Fin n) → R),
      (∀ f, (∃ i : Fin m, (f i).val ≠ i.val) → G f = CRing.zero) →
      sumVec m n G = G (fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩) by
    rw [h n (Nat.le_refl n)]
    · have heps : eps (fun i : Fin n => (⟨i.val, i.isLt⟩ : Fin n)) = 1 := epsNat_id n
      rw [heps, CRing.ofInt_one, CRing.one_mul]
      have hones : prodFin n (fun i => matOne (R := R) n i ⟨i.val, i.isLt⟩) =
                   prodFin n (fun _ => (CRing.one : R)) := by
        apply prodFin_congr; intro i; unfold matOne; simp
      rw [hones, prodFin_one]
    · rintro f ⟨i, hi⟩
      have h0 : prodFin n (fun r => matOne (R := R) n r (f r)) = CRing.zero := by
        apply prodFin_eq_zero_of_exists _ i
        unfold matOne
        have : i ≠ f i := fun h => hi (congrArg Fin.val h).symm
        simp [this]
      rw [h0, CRing.mul_zero]
  intro m hm
  induction m with
  | zero =>
    intro G _
    change G Fin.elim0 = G (fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩)
    congr 1; funext i; exact Fin.elim0 i
  | succ m ih =>
    intro G hG
    simp only [sumVec]
    rw [sumFin_single ⟨m, hm⟩]
    · rw [ih (Nat.le_of_lt hm) (fun g => G (finSnoc g ⟨m, hm⟩))]
      · congr 1; funext i; unfold finSnoc
        by_cases hi : i.val < m
        · simp [hi]
        · simp only [hi, dite_false]
          apply Fin.ext; simp; omega
      · rintro g ⟨i, hi⟩
        apply hG
        refine ⟨i.castSucc, ?_⟩
        rw [finSnoc_castSucc]; exact hi
    · intro a ha
      rw [← sumVec_zero (m := m) (k := n)]
      apply sumVec_congr; intro g
      apply hG
      refine ⟨Fin.last m, ?_⟩
      rw [finSnoc_last]
      intro heq; apply ha; exact Fin.ext heq

theorem det_smul {n : Nat} (c : R) (M : Mat R n) :
    det (matSmul c M) = CRing.mul (CRing.pow c n) (det M) := by
  unfold det matSmul
  rw [sumVec_mul_left]
  apply sumVec_congr; intro f
  rw [prodFin_mul, prodFin_const]
  rw [← CRing.mul_assoc, CRing.mul_comm (CRing.ofInt (eps f)) (CRing.pow c n), CRing.mul_assoc]

theorem det_row_add {n : Nat} (r : Fin n) (M M1 M2 : Mat R n)
    (hother : ∀ i j, i ≠ r → M i j = M1 i j ∧ M i j = M2 i j)
    (hrow : ∀ j, M r j = CRing.add (M1 r j) (M2 r j)) :
    det M = CRing.add (det M1) (det M2) := by
  unfold det
  rw [← sumVec_add]
  apply sumVec_congr; intro f
  rw [← CRing.left_distrib]
  congr 1
  -- Prove product splits at single index r
  suffices hp : ∀ (m : Nat) (P P1 P2 : Fin m → R) (idx : Fin m),
      (∀ i, i ≠ idx → P i = P1 i ∧ P i = P2 i) →
      P idx = CRing.add (P1 idx) (P2 idx) →
      prodFin m P = CRing.add (prodFin m P1) (prodFin m P2) by
    exact hp n (fun i => M i (f i)) (fun i => M1 i (f i)) (fun i => M2 i (f i)) r
      (fun i hi => hother i (f i) hi) (hrow (f r))
  intro m
  induction m with
  | zero => intro _ _ _ idx; exact Fin.elim0 idx
  | succ m ih =>
    intro P P1 P2 idx ho hidx
    simp only [prodFin]
    by_cases hlt : idx.val < m
    · have hne : Fin.last m ≠ idx := by intro h; have := congrArg Fin.val h; simp at this; omega
      have ⟨hL1, hL2⟩ := ho (Fin.last m) hne
      have hrec := ih (fun i => P i.castSucc) (fun i => P1 i.castSucc) (fun i => P2 i.castSucc)
        ⟨idx.val, hlt⟩
        (fun i hi => ho i.castSucc (fun heq => hi (Fin.ext (by have hv := congrArg Fin.val heq; exact hv))))
        (by have : (⟨idx.val, hlt⟩ : Fin m).castSucc = idx := Fin.ext rfl; rw [this]; exact hidx)
      rw [hrec, CRing.right_distrib]
      rw [hL1]; congr 1; rw [← hL1, hL2]
    · have heq : idx = Fin.last m := by apply Fin.ext; simp; omega
      subst heq
      have h1 : prodFin m (fun i => P i.castSucc) = prodFin m (fun i => P1 i.castSucc) :=
        prodFin_congr (fun i => (ho i.castSucc (by intro h; have := congrArg Fin.val h; simp at this; omega)).1)
      have h2 : prodFin m (fun i => P i.castSucc) = prodFin m (fun i => P2 i.castSucc) :=
        prodFin_congr (fun i => (ho i.castSucc (by intro h; have := congrArg Fin.val h; simp at this; omega)).2)
      rw [hidx, CRing.left_distrib, ← h1, ← h2]

theorem det_row_smul {n : Nat} (r : Fin n) (c : R) (M M1 : Mat R n)
    (hother : ∀ i j, i ≠ r → M i j = M1 i j)
    (hrow : ∀ j, M r j = CRing.mul c (M1 r j)) :
    det M = CRing.mul c (det M1) := by
  unfold det
  rw [sumVec_mul_left]
  apply sumVec_congr; intro f
  rw [← CRing.mul_assoc, CRing.mul_comm c (CRing.ofInt (eps f)), CRing.mul_assoc]
  congr 1
  suffices hp : ∀ (m : Nat) (P P1 : Fin m → R) (idx : Fin m),
      (∀ i, i ≠ idx → P i = P1 i) → P idx = CRing.mul c (P1 idx) →
      prodFin m P = CRing.mul c (prodFin m P1) by
    exact hp n (fun i => M i (f i)) (fun i => M1 i (f i)) r
      (fun i hi => hother i (f i) hi) (hrow (f r))
  intro m
  induction m with
  | zero => intro _ _ idx; exact Fin.elim0 idx
  | succ m ih =>
    intro P P1 idx ho hidx
    simp only [prodFin]
    by_cases hlt : idx.val < m
    · have hne : Fin.last m ≠ idx := by intro h; have := congrArg Fin.val h; simp at this; omega
      have hrec := ih (fun i => P i.castSucc) (fun i => P1 i.castSucc) ⟨idx.val, hlt⟩
        (fun i hi => ho i.castSucc (fun heq => hi (Fin.ext (by have hv := congrArg Fin.val heq; exact hv))))
        (by have : (⟨idx.val, hlt⟩ : Fin m).castSucc = idx := Fin.ext rfl; rw [this]; exact hidx)
      rw [hrec, ho (Fin.last m) hne, CRing.mul_assoc]
    · have heq : idx = Fin.last m := by apply Fin.ext; simp; omega
      subst heq
      have h1 : prodFin m (fun i => P i.castSucc) = prodFin m (fun i => P1 i.castSucc) :=
        prodFin_congr (fun i => ho i.castSucc (by intro h; have := congrArg Fin.val h; simp at this; omega))
      rw [h1, hidx, ← CRing.mul_assoc, CRing.mul_comm (prodFin m (fun i => P1 i.castSucc)) c, CRing.mul_assoc]

theorem det_col_add {n : Nat} (col : Fin n) (M M1 M2 : Mat R n)
    (hother : ∀ i j, j ≠ col → M i j = M1 i j ∧ M i j = M2 i j)
    (hcol : ∀ i, M i col = CRing.add (M1 i col) (M2 i col)) :
    det M = CRing.add (det M1) (det M2) := by
  unfold det
  rw [← sumVec_add]
  apply sumVec_congr; intro f
  by_cases hinj : ∀ x y : Fin n, f x = f y → x = y
  · rcases fin_inj_surj f hinj col with ⟨r, hr⟩
    rw [← CRing.left_distrib]; congr 1
    suffices hp : ∀ (m : Nat) (P P1 P2 : Fin m → R) (idx : Fin m),
        (∀ i, i ≠ idx → P i = P1 i ∧ P i = P2 i) →
        P idx = CRing.add (P1 idx) (P2 idx) →
        prodFin m P = CRing.add (prodFin m P1) (prodFin m P2) by
      exact hp n (fun i => M i (f i)) (fun i => M1 i (f i)) (fun i => M2 i (f i)) r
        (fun i hi => hother i (f i) (fun heq => hi (hinj i r (heq.trans hr.symm))))
        (by rw [hr]; exact hcol r)
    intro m
    induction m with
    | zero => intro _ _ _ idx; exact Fin.elim0 idx
    | succ m ih =>
      intro P P1 P2 idx ho hidx
      simp only [prodFin]
      by_cases hlt : idx.val < m
      · have hne : Fin.last m ≠ idx := by intro h; have := congrArg Fin.val h; simp at this; omega
        have ⟨hL1, hL2⟩ := ho (Fin.last m) hne
        have hrec := ih (fun i => P i.castSucc) (fun i => P1 i.castSucc) (fun i => P2 i.castSucc)
          ⟨idx.val, hlt⟩
          (fun i hi => ho i.castSucc (fun heq => hi (Fin.ext (by have hv := congrArg Fin.val heq; exact hv))))
          (by have : (⟨idx.val, hlt⟩ : Fin m).castSucc = idx := Fin.ext rfl; rw [this]; exact hidx)
        rw [hrec, CRing.right_distrib, hL1]; congr 1; rw [← hL1, hL2]
      · have heq : idx = Fin.last m := by apply Fin.ext; simp; omega
        subst heq
        have h1 : prodFin m (fun i => P i.castSucc) = prodFin m (fun i => P1 i.castSucc) :=
          prodFin_congr (fun i => (ho i.castSucc (by intro h; have := congrArg Fin.val h; simp at this; omega)).1)
        have h2 : prodFin m (fun i => P i.castSucc) = prodFin m (fun i => P2 i.castSucc) :=
          prodFin_congr (fun i => (ho i.castSucc (by intro h; have := congrArg Fin.val h; simp at this; omega)).2)
        rw [hidx, CRing.left_distrib, ← h1, ← h2]
  · -- Non-injective f => eps f = 0, both sides are 0!
    have h0 : eps f = 0 := by
      have h1 : ∀ (m : Nat) (Q : Fin m → Bool), (¬ ∀ i, Q i = true) → ∃ i, Q i = false := by
        intro m
        induction m with
        | zero => intro Q hnot; exfalso; apply hnot; intro i; exact Fin.elim0 i
        | succ m ih =>
          intro Q hnot
          cases hlast : Q (Fin.last m)
          · exact ⟨Fin.last m, hlast⟩
          · rcases ih (fun i => Q i.castSucc) (by
              intro hall; apply hnot; intro i
              by_cases hi : i.val < m
              · have : i = (⟨i.val, hi⟩ : Fin m).castSucc := Fin.ext rfl
                rw [this]; exact hall ⟨i.val, hi⟩
              · have : i = Fin.last m := by apply Fin.ext; simp; omega
                rw [this]; exact hlast) with ⟨i, hi⟩
            exact ⟨i.castSucc, hi⟩
      rcases h1 n (fun x => decide (∀ y : Fin n, f x = f y → x = y)) (by
        intro hall; apply hinj; intro x y hxy
        have := hall x; simp only [decide_eq_true_eq] at this; exact this y hxy) with ⟨x, hx⟩
      simp only [decide_eq_false_iff_not] at hx
      rcases h1 n (fun y => decide (f x = f y → x = y)) (by
        intro hall; apply hx; intro y hy
        have := hall y; simp only [decide_eq_true_eq] at this; exact this hy) with ⟨y, hy⟩
      simp only [decide_eq_false_iff_not] at hy
      by_cases hxy : f x = f y
      · exact epsNat_eq_zero_of_eq (fun i => (f i).val) x y (fun h => hy (fun _ => h)) (congrArg Fin.val hxy)
      · exfalso; exact hy (fun h => absurd h hxy)
    rw [h0, CRing.ofInt_zero, CRing.zero_mul, CRing.zero_mul, CRing.zero_mul, CRing.add_zero]

theorem det_col_smul {n : Nat} (col : Fin n) (c : R) (M M1 : Mat R n)
    (hother : ∀ i j, j ≠ col → M i j = M1 i j)
    (hcol : ∀ i, M i col = CRing.mul c (M1 i col)) :
    det M = CRing.mul c (det M1) := by
  unfold det
  rw [sumVec_mul_left]
  apply sumVec_congr; intro f
  by_cases hinj : ∀ x y : Fin n, f x = f y → x = y
  · rcases fin_inj_surj f hinj col with ⟨r, hr⟩
    rw [← CRing.mul_assoc, CRing.mul_comm c (CRing.ofInt (eps f)), CRing.mul_assoc]
    congr 1
    suffices hp : ∀ (m : Nat) (P P1 : Fin m → R) (idx : Fin m),
        (∀ i, i ≠ idx → P i = P1 i) → P idx = CRing.mul c (P1 idx) →
        prodFin m P = CRing.mul c (prodFin m P1) by
      exact hp n (fun i => M i (f i)) (fun i => M1 i (f i)) r
        (fun i hi => hother i (f i) (fun heq => hi (hinj i r (heq.trans hr.symm))))
        (by rw [hr]; exact hcol r)
    intro m
    induction m with
    | zero => intro _ _ idx; exact Fin.elim0 idx
    | succ m ih =>
      intro P P1 idx ho hidx
      simp only [prodFin]
      by_cases hlt : idx.val < m
      · have hne : Fin.last m ≠ idx := by intro h; have := congrArg Fin.val h; simp at this; omega
        have hrec := ih (fun i => P i.castSucc) (fun i => P1 i.castSucc) ⟨idx.val, hlt⟩
          (fun i hi => ho i.castSucc (fun heq => hi (Fin.ext (by have hv := congrArg Fin.val heq; exact hv))))
          (by have : (⟨idx.val, hlt⟩ : Fin m).castSucc = idx := Fin.ext rfl; rw [this]; exact hidx)
        rw [hrec, ho (Fin.last m) hne, CRing.mul_assoc]
      · have heq : idx = Fin.last m := by apply Fin.ext; simp; omega
        subst heq
        have h1 : prodFin m (fun i => P i.castSucc) = prodFin m (fun i => P1 i.castSucc) :=
          prodFin_congr (fun i => ho i.castSucc (by intro h; have := congrArg Fin.val h; simp at this; omega))
        rw [h1, hidx, ← CRing.mul_assoc, CRing.mul_comm (prodFin m (fun i => P1 i.castSucc)) c, CRing.mul_assoc]
  · have h0 : eps f = 0 := by
      have h1 : ∀ (m : Nat) (Q : Fin m → Bool), (¬ ∀ i, Q i = true) → ∃ i, Q i = false := by
        intro m
        induction m with
        | zero => intro Q hnot; exfalso; apply hnot; intro i; exact Fin.elim0 i
        | succ m ih =>
          intro Q hnot
          cases hlast : Q (Fin.last m)
          · exact ⟨Fin.last m, hlast⟩
          · rcases ih (fun i => Q i.castSucc) (by
              intro hall; apply hnot; intro i
              by_cases hi : i.val < m
              · have : i = (⟨i.val, hi⟩ : Fin m).castSucc := Fin.ext rfl
                rw [this]; exact hall ⟨i.val, hi⟩
              · have : i = Fin.last m := by apply Fin.ext; simp; omega
                rw [this]; exact hlast) with ⟨i, hi⟩
            exact ⟨i.castSucc, hi⟩
      rcases h1 n (fun x => decide (∀ y : Fin n, f x = f y → x = y)) (by
        intro hall; apply hinj; intro x y hxy
        have := hall x; simp only [decide_eq_true_eq] at this; exact this y hxy) with ⟨x, hx⟩
      simp only [decide_eq_false_iff_not] at hx
      rcases h1 n (fun y => decide (f x = f y → x = y)) (by
        intro hall; apply hx; intro y hy
        have := hall y; simp only [decide_eq_true_eq] at this; exact this hy) with ⟨y, hy⟩
      simp only [decide_eq_false_iff_not] at hy
      by_cases hxy : f x = f y
      · exact epsNat_eq_zero_of_eq (fun i => (f i).val) x y (fun h => hy (fun _ => h)) (congrArg Fin.val hxy)
      · exfalso; exact hy (fun h => absurd h hxy)
    rw [h0, CRing.ofInt_zero, CRing.zero_mul, CRing.zero_mul, CRing.mul_zero]

/-- If row `r` is the unit vector `e_r^T` in both `M1` and `M2`, and `M1, M2` agree outside
    column `r`, then `det M1 = det M2` (entries in column `r` off the diagonal never contribute!). -/
theorem det_congr_of_unit_row {n : Nat} (r : Fin n) (M1 M2 : Mat R n)
    (hrow1 : ∀ j, M1 r j = if j = r then CRing.one else CRing.zero)
    (hrow2 : ∀ j, M2 r j = if j = r then CRing.one else CRing.zero)
    (hother : ∀ i j, j ≠ r → M1 i j = M2 i j) :
    det M1 = det M2 := by
  unfold det
  apply sumVec_congr; intro f
  by_cases hfr : f r = r
  · by_cases heps : eps f = 0
    · rw [heps, CRing.ofInt_zero, CRing.zero_mul, CRing.zero_mul]
    · congr 1
      apply prodFin_congr; intro i
      by_cases hir : i = r
      · subst hir; rw [hrow1, hrow2]
      · have hne : f i ≠ r := by
          intro hfi
          apply heps
          exact epsNat_eq_zero_of_eq (fun k => (f k).val) i r hir (by rw [hfi, hfr])
        exact hother i (f i) hne
  · have h1 : prodFin n (fun i => M1 i (f i)) = CRing.zero :=
      prodFin_eq_zero_of_exists _ r (by rw [hrow1]; simp [hfr])
    have h2 : prodFin n (fun i => M2 i (f i)) = CRing.zero :=
      prodFin_eq_zero_of_exists _ r (by rw [hrow2]; simp [hfr])
    rw [h1, h2, CRing.mul_zero]

/-- Block upper-triangular determinant theorem over ANY commutative ring `R`. -/
theorem det_blockUpper {m n : Nat}
    (A : Mat R m) (B : Fin m → Fin n → R) (D : Mat R n) :
    det (blockMat A B (fun _ _ => CRing.zero) D) = CRing.mul (det A) (det D) := by
  unfold det
  rw [sumVec_split (m := m) (n := n)]
  -- For any f1, f2: if any j has f2 j < m, the bottom-left block gives 0!
  -- And if all j have f2 j >= m AND eps (finAppend f1 f2) ≠ 0, then by pigeonhole all i have f1 i < m!
  have hstep1 : sumVec m (m + n) (fun f1 => sumVec n (m + n) (fun f2 =>
      CRing.mul (CRing.ofInt (eps (finAppend f1 f2)))
        (prodFin (m + n) (fun k => blockMat A B (fun _ _ => CRing.zero) D k (finAppend f1 f2 k))))) =
      sumVec m (m + n) (fun f1 => sumVec n n (fun g2 =>
        CRing.mul (CRing.ofInt (eps (finAppend f1 (fun j => ⟨m + (g2 j).val, Nat.add_lt_add_left (g2 j).isLt m⟩))))
          (prodFin (m + n) (fun k => blockMat A B (fun _ _ => CRing.zero) D k
            (finAppend f1 (fun j => ⟨m + (g2 j).val, Nat.add_lt_add_left (g2 j).isLt m⟩) k))))) := by
    apply sumVec_congr; intro f1
    apply sumVec_restrict_hi
    rintro f2 ⟨j, hj⟩
    have h0 : prodFin (m + n) (fun k => blockMat A B (fun _ _ => CRing.zero) D k (finAppend f1 f2 k)) = CRing.zero := by
      apply prodFin_eq_zero_of_exists _ ⟨m + j.val, Nat.add_lt_add_left j.isLt m⟩
      unfold blockMat finAppend
      have h1 : ¬ (m + j.val < m) := by omega
      simp only [h1, dite_false]
      have hsub : (⟨m + j.val - m, by omega⟩ : Fin n) = j := Fin.ext (by simp)
      have hval : (f2 ⟨m + j.val - m, by omega⟩).val < m := by rw [hsub]; exact hj
      simp only [hval, dite_true]
    rw [h0, CRing.mul_zero]
  rw [hstep1]
  have hsf : ∀ (r1 k1 k2 : Nat) (G : Fin k1 → (Fin r1 → Fin k2) → R),
      sumFin k1 (fun a => sumVec r1 k2 (fun h => G a h)) =
      sumVec r1 k2 (fun h => sumFin k1 (fun a => G a h)) := by
    intro r1 k1 k2
    induction r1 with
    | zero => intro _; rfl
    | succ r1 ihr =>
      intro G
      simp only [sumVec]
      rw [sumFin_comm]
      exact sumFin_congr (fun b => ihr (fun a u => G a (finSnoc u b)))
  have hcomm : ∀ (m1 m2 k1 k2 : Nat) (F : (Fin m1 → Fin k1) → (Fin m2 → Fin k2) → R),
      sumVec m1 k1 (fun f1 => sumVec m2 k2 (fun g2 => F f1 g2)) =
      sumVec m2 k2 (fun g2 => sumVec m1 k1 (fun f1 => F f1 g2)) := by
    intro m1 m2 k1 k2
    induction m1 with
    | zero => intro _; rfl
    | succ m1 ihm =>
      intro F
      simp only [sumVec]
      rw [sumFin_congr (fun a => ihm (fun f1 g2 => F (finSnoc f1 a) g2)), hsf]
  rw [hcomm]
  have hstep2 : ∀ g2 : Fin n → Fin n,
      sumVec m (m + n) (fun f1 =>
        CRing.mul (CRing.ofInt (eps (finAppend f1 (fun j => ⟨m + (g2 j).val, Nat.add_lt_add_left (g2 j).isLt m⟩))))
          (prodFin (m + n) (fun k => blockMat A B (fun _ _ => CRing.zero) D k
            (finAppend f1 (fun j => ⟨m + (g2 j).val, Nat.add_lt_add_left (g2 j).isLt m⟩) k)))) =
      sumVec m m (fun g1 =>
        CRing.mul (CRing.ofInt (eps (finAppend (fun i => ⟨(g1 i).val, Nat.lt_of_lt_of_le (g1 i).isLt (Nat.le_add_right m n)⟩)
                                               (fun j => ⟨m + (g2 j).val, Nat.add_lt_add_left (g2 j).isLt m⟩))))
          (prodFin (m + n) (fun k => blockMat A B (fun _ _ => CRing.zero) D k
            (finAppend (fun i => ⟨(g1 i).val, Nat.lt_of_lt_of_le (g1 i).isLt (Nat.le_add_right m n)⟩)
                       (fun j => ⟨m + (g2 j).val, Nat.add_lt_add_left (g2 j).isLt m⟩) k)))) := by
    intro g2
    apply sumVec_restrict_lo
    rintro f1 ⟨i, hi⟩
    by_cases h2inj : ∀ j1 j2 : Fin n, g2 j1 = g2 j2 → j1 = j2
    · let y : Fin n := ⟨(f1 i).val - m, by omega⟩
      rcases fin_inj_surj g2 h2inj y with ⟨j, hj⟩
      have h0 : eps (finAppend f1 (fun r => ⟨m + (g2 r).val, Nat.add_lt_add_left (g2 r).isLt m⟩)) = 0 := by
        apply epsNat_eq_zero_of_eq _ ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right m n)⟩
                                     ⟨m + j.val, Nat.add_lt_add_left j.isLt m⟩
        · intro heq; have hv := congrArg Fin.val heq; simp at hv; omega
        · unfold finAppend
          have h1 : ¬ (m + j.val < m) := by omega
          simp only [i.isLt, h1, dite_true, dite_false]
          have hsub : (⟨m + j.val - m, by omega⟩ : Fin n) = j := Fin.ext (by simp)
          rw [hsub, hj]; simp [y]; omega
      rw [h0, CRing.ofInt_zero, CRing.zero_mul]
    · have hfind : ∀ (r : Nat) (Q : Fin r → Bool), (¬ ∀ a, Q a = true) → ∃ a, Q a = false := by
        intro r
        induction r with
        | zero => intro Q hnot; exfalso; apply hnot; intro a; exact Fin.elim0 a
        | succ r ihr =>
          intro Q hnot
          cases hlast : Q (Fin.last r)
          · exact ⟨Fin.last r, hlast⟩
          · rcases ihr (fun a => Q a.castSucc) (by
              intro hall; apply hnot; intro a
              by_cases ha : a.val < r
              · have : a = (⟨a.val, ha⟩ : Fin r).castSucc := Fin.ext rfl
                rw [this]; exact hall ⟨a.val, ha⟩
              · have : a = Fin.last r := by apply Fin.ext; simp; omega
                rw [this]; exact hlast) with ⟨a, ha⟩
            exact ⟨a.castSucc, ha⟩
      rcases hfind n (fun j1 => decide (∀ j2 : Fin n, g2 j1 = g2 j2 → j1 = j2)) (by
        intro hall; apply h2inj; intro j1 j2 h12
        have := hall j1; simp only [decide_eq_true_eq] at this; exact this j2 h12) with ⟨j1, hj1⟩
      simp only [decide_eq_false_iff_not] at hj1
      rcases hfind n (fun j2 => decide (g2 j1 = g2 j2 → j1 = j2)) (by
        intro hall; apply hj1; intro j2 h12
        have := hall j2; simp only [decide_eq_true_eq] at this; exact this h12) with ⟨j2, hj2⟩
      simp only [decide_eq_false_iff_not] at hj2
      by_cases h12 : g2 j1 = g2 j2
      · have hne : j1 ≠ j2 := fun h => hj2 (fun _ => h)
        have h0 : eps (finAppend f1 (fun r => ⟨m + (g2 r).val, Nat.add_lt_add_left (g2 r).isLt m⟩)) = 0 := by
          apply epsNat_eq_zero_of_eq _ ⟨m + j1.val, Nat.add_lt_add_left j1.isLt m⟩
                                       ⟨m + j2.val, Nat.add_lt_add_left j2.isLt m⟩
          · intro heq; apply hne; apply Fin.ext; have hv := congrArg Fin.val heq; simp at hv; omega
          · unfold finAppend
            have ha1 : ¬ (m + j1.val < m) := by omega
            have ha2 : ¬ (m + j2.val < m) := by omega
            simp only [ha1, ha2, dite_false]
            have hs1 : (⟨m + j1.val - m, by omega⟩ : Fin n) = j1 := Fin.ext (by simp)
            have hs2 : (⟨m + j2.val - m, by omega⟩ : Fin n) = j2 := Fin.ext (by simp)
            rw [hs1, hs2, h12]
        rw [h0, CRing.ofInt_zero, CRing.zero_mul]
      · exfalso; exact hj2 (fun h => absurd h h12)
  rw [sumVec_congr hstep2]
  rw [CRing.mul_comm (sumVec m m _), sumVec_mul_right]
  apply sumVec_congr; intro g2
  rw [CRing.mul_comm, sumVec_mul_right]
  apply sumVec_congr; intro g1
  have heps_sp : eps (finAppend (fun i : Fin m => (⟨(g1 i).val, Nat.lt_of_lt_of_le (g1 i).isLt (Nat.le_add_right m n)⟩ : Fin (m + n)))
                                (fun j : Fin n => (⟨m + (g2 j).val, Nat.add_lt_add_left (g2 j).isLt m⟩ : Fin (m + n)))) =
                 eps g1 * eps g2 := by
    unfold eps
    have hfn : (fun k : Fin (m + n) => (finAppend (fun i : Fin m => (⟨(g1 i).val, Nat.lt_of_lt_of_le (g1 i).isLt (Nat.le_add_right m n)⟩ : Fin (m + n)))
                                                  (fun j : Fin n => (⟨m + (g2 j).val, Nat.add_lt_add_left (g2 j).isLt m⟩ : Fin (m + n))) k).val) =
               finAppend (fun i : Fin m => (g1 i).val) (fun j : Fin n => m + (g2 j).val) := by
      funext k; unfold finAppend; by_cases hk : k.val < m <;> simp [hk]
    rw [hfn, epsNat_split]
    have hshift : ∀ (r : Nat) (v : Fin r → Nat), epsNat r (fun j => m + v j) = epsNat r v := by
      intro r
      induction r with
      | zero => intro _; rfl
      | succ r ihr =>
        intro v; simp only [epsNat]; rw [ihr (fun j => v j.castSucc)]
        congr 1; apply prodFin_congr; intro j; unfold pairSign
        have h1 : m + v j.castSucc < m + v (Fin.last r) ↔ v j.castSucc < v (Fin.last r) := by omega
        simp [h1]
    rw [hshift n (fun j => (g2 j).val)]
    have hcross : prodFin (R := Int) n (fun j => prodFin (R := Int) m (fun i => pairSign (g1 i).val (m + (g2 j).val))) = 1 := by
      have h1 : prodFin (R := Int) n (fun j => prodFin (R := Int) m (fun i => pairSign (g1 i).val (m + (g2 j).val))) =
                prodFin (R := Int) n (fun _ => CRing.one) := by
        apply prodFin_congr; intro j
        have h2 : prodFin (R := Int) m (fun i => pairSign (g1 i).val (m + (g2 j).val)) =
                  prodFin (R := Int) m (fun _ => CRing.one) :=
          prodFin_congr (fun i => pairSign_lt (by have := (g1 i).isLt; omega))
        rw [h2]; exact prodFin_one (R := Int) m
      rw [h1]; exact prodFin_one (R := Int) n
    rw [hcross, Int.mul_one]
  rw [heps_sp, CRing.ofInt_mul, prodFin_split (m := m) (n := n)]
  have hlo : prodFin m (fun i => blockMat A B (fun _ _ => CRing.zero) D ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right m n)⟩
      (finAppend (fun r : Fin m => (⟨(g1 r).val, Nat.lt_of_lt_of_le (g1 r).isLt (Nat.le_add_right m n)⟩ : Fin (m + n)))
                 (fun r : Fin n => (⟨m + (g2 r).val, Nat.add_lt_add_left (g2 r).isLt m⟩ : Fin (m + n)))
                 ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right m n)⟩)) =
      prodFin m (fun i => A i (g1 i)) := by
    apply prodFin_congr; intro i; unfold blockMat finAppend; simp [i.isLt, (g1 i).isLt]
  have hhi : prodFin n (fun j => blockMat A B (fun _ _ => CRing.zero) D ⟨m + j.val, Nat.add_lt_add_left j.isLt m⟩
      (finAppend (fun r : Fin m => (⟨(g1 r).val, Nat.lt_of_lt_of_le (g1 r).isLt (Nat.le_add_right m n)⟩ : Fin (m + n)))
                 (fun r : Fin n => (⟨m + (g2 r).val, Nat.add_lt_add_left (g2 r).isLt m⟩ : Fin (m + n)))
                 ⟨m + j.val, Nat.add_lt_add_left j.isLt m⟩)) =
      prodFin n (fun j => D j (g2 j)) := by
    apply prodFin_congr; intro j; unfold blockMat finAppend
    have h1 : ¬ (m + j.val < m) := by omega
    simp only [h1, dite_false]
    have hsub : (⟨m + j.val - m, by omega⟩ : Fin n) = j := Fin.ext (by simp)
    have h2' : ¬ (m + (g2 ⟨m + j.val - m, by omega⟩).val < m) := by omega
    simp only [h2', dite_false]
    have harg : (⟨m + (g2 ⟨m + j.val - m, by omega⟩).val - m, by omega⟩ : Fin n) = g2 j := by
      apply Fin.ext; simp
    rw [harg, hsub]
  rw [hlo, hhi]
  rw [CRing.mul_assoc, ← CRing.mul_assoc (CRing.ofInt (eps g2)),
      CRing.mul_comm (CRing.ofInt (eps g2)) (prodFin m (fun i => A i (g1 i))),
      CRing.mul_assoc, ← CRing.mul_assoc, CRing.mul_assoc]

/-- Block lower-triangular determinant theorem over ANY commutative ring `R`. -/
theorem det_blockLower {m n : Nat}
    (A : Mat R m) (C : Fin n → Fin m → R) (D : Mat R n) :
    det (blockMat A (fun _ _ => CRing.zero) C D) = CRing.mul (det A) (det D) := by
  unfold det
  rw [sumVec_split (m := m) (n := n)]
  -- If any i < m has f1 i >= m, top-right block is 0!
  have hstep1 : sumVec m (m + n) (fun f1 => sumVec n (m + n) (fun f2 =>
      CRing.mul (CRing.ofInt (eps (finAppend f1 f2)))
        (prodFin (m + n) (fun k => blockMat A (fun _ _ => CRing.zero) C D k (finAppend f1 f2 k))))) =
      sumVec m m (fun g1 => sumVec n (m + n) (fun f2 =>
        CRing.mul (CRing.ofInt (eps (finAppend (fun i => ⟨(g1 i).val, Nat.lt_of_lt_of_le (g1 i).isLt (Nat.le_add_right m n)⟩) f2)))
          (prodFin (m + n) (fun k => blockMat A (fun _ _ => CRing.zero) C D k
            (finAppend (fun i => ⟨(g1 i).val, Nat.lt_of_lt_of_le (g1 i).isLt (Nat.le_add_right m n)⟩) f2 k))))) := by
    apply sumVec_restrict_lo
    rintro f1 ⟨i, hi⟩
    refine Eq.trans (b := sumVec n (m + n) (fun _ => (CRing.zero : R))) ?_ sumVec_zero
    apply sumVec_congr; intro f2
    have h0 : prodFin (m + n) (fun k => blockMat A (fun _ _ => CRing.zero) C D k (finAppend f1 f2 k)) = CRing.zero := by
      apply prodFin_eq_zero_of_exists _ ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right m n)⟩
      unfold blockMat finAppend
      simp only [i.isLt, dite_true]
      have hnot : ¬ (f1 i).val < m := hi
      simp only [hnot, dite_false]
    rw [h0, CRing.mul_zero]
  rw [hstep1]
  have hstep2 : ∀ g1 : Fin m → Fin m,
      sumVec n (m + n) (fun f2 =>
        CRing.mul (CRing.ofInt (eps (finAppend (fun i => ⟨(g1 i).val, Nat.lt_of_lt_of_le (g1 i).isLt (Nat.le_add_right m n)⟩) f2)))
          (prodFin (m + n) (fun k => blockMat A (fun _ _ => CRing.zero) C D k
            (finAppend (fun i => ⟨(g1 i).val, Nat.lt_of_lt_of_le (g1 i).isLt (Nat.le_add_right m n)⟩) f2 k)))) =
      sumVec n n (fun g2 =>
        CRing.mul (CRing.ofInt (eps (finAppend (fun i => ⟨(g1 i).val, Nat.lt_of_lt_of_le (g1 i).isLt (Nat.le_add_right m n)⟩)
                                               (fun j => ⟨m + (g2 j).val, Nat.add_lt_add_left (g2 j).isLt m⟩))))
          (prodFin (m + n) (fun k => blockMat A (fun _ _ => CRing.zero) C D k
            (finAppend (fun i => ⟨(g1 i).val, Nat.lt_of_lt_of_le (g1 i).isLt (Nat.le_add_right m n)⟩)
                       (fun j => ⟨m + (g2 j).val, Nat.add_lt_add_left (g2 j).isLt m⟩) k)))) := by
    intro g1
    apply sumVec_restrict_hi
    rintro f2 ⟨j, hj⟩
    by_cases h1inj : ∀ i1 i2 : Fin m, g1 i1 = g1 i2 → i1 = i2
    · rcases fin_inj_surj g1 h1inj ⟨(f2 j).val, hj⟩ with ⟨i, hi⟩
      have h0 : eps (finAppend (fun r => ⟨(g1 r).val, Nat.lt_of_lt_of_le (g1 r).isLt (Nat.le_add_right m n)⟩) f2) = 0 := by
        apply epsNat_eq_zero_of_eq _ ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right m n)⟩
                                     ⟨m + j.val, Nat.add_lt_add_left j.isLt m⟩
        · intro heq; have hv := congrArg Fin.val heq; simp at hv; omega
        · unfold finAppend
          have h1 : ¬ (m + j.val < m) := by omega
          simp only [i.isLt, h1, dite_true, dite_false]
          have hsub : (⟨m + j.val - m, by omega⟩ : Fin n) = j := Fin.ext (by simp)
          rw [hsub]; have hv := congrArg Fin.val hi; exact hv
      rw [h0, CRing.ofInt_zero, CRing.zero_mul]
    · have hfind : ∀ (r : Nat) (Q : Fin r → Bool), (¬ ∀ a, Q a = true) → ∃ a, Q a = false := by
        intro r
        induction r with
        | zero => intro Q hnot; exfalso; apply hnot; intro a; exact Fin.elim0 a
        | succ r ihr =>
          intro Q hnot
          cases hlast : Q (Fin.last r)
          · exact ⟨Fin.last r, hlast⟩
          · rcases ihr (fun a => Q a.castSucc) (by
              intro hall; apply hnot; intro a
              by_cases ha : a.val < r
              · have : a = (⟨a.val, ha⟩ : Fin r).castSucc := Fin.ext rfl
                rw [this]; exact hall ⟨a.val, ha⟩
              · have : a = Fin.last r := by apply Fin.ext; simp; omega
                rw [this]; exact hlast) with ⟨a, ha⟩
            exact ⟨a.castSucc, ha⟩
      rcases hfind m (fun i1 => decide (∀ i2 : Fin m, g1 i1 = g1 i2 → i1 = i2)) (by
        intro hall; apply h1inj; intro i1 i2 h12
        have := hall i1; simp only [decide_eq_true_eq] at this; exact this i2 h12) with ⟨i1, hi1⟩
      simp only [decide_eq_false_iff_not] at hi1
      rcases hfind m (fun i2 => decide (g1 i1 = g1 i2 → i1 = i2)) (by
        intro hall; apply hi1; intro i2 h12
        have := hall i2; simp only [decide_eq_true_eq] at this; exact this h12) with ⟨i2, hi2⟩
      simp only [decide_eq_false_iff_not] at hi2
      by_cases h12 : g1 i1 = g1 i2
      · have hne : i1 ≠ i2 := fun h => hi2 (fun _ => h)
        have h0 : eps (finAppend (fun r => ⟨(g1 r).val, Nat.lt_of_lt_of_le (g1 r).isLt (Nat.le_add_right m n)⟩) f2) = 0 := by
          apply epsNat_eq_zero_of_eq _ ⟨i1.val, Nat.lt_of_lt_of_le i1.isLt (Nat.le_add_right m n)⟩
                                       ⟨i2.val, Nat.lt_of_lt_of_le i2.isLt (Nat.le_add_right m n)⟩
          · intro heq; apply hne; apply Fin.ext; have hv := congrArg Fin.val heq; exact hv
          · unfold finAppend; simp [i1.isLt, i2.isLt, h12]
        rw [h0, CRing.ofInt_zero, CRing.zero_mul]
      · exfalso; exact hi2 (fun h => absurd h h12)
  rw [sumVec_congr hstep2]
  rw [sumVec_mul_right]
  apply sumVec_congr; intro g1
  rw [sumVec_mul_left]
  apply sumVec_congr; intro g2
  have heps_sp : eps (finAppend (fun i : Fin m => (⟨(g1 i).val, Nat.lt_of_lt_of_le (g1 i).isLt (Nat.le_add_right m n)⟩ : Fin (m + n)))
                                (fun j : Fin n => (⟨m + (g2 j).val, Nat.add_lt_add_left (g2 j).isLt m⟩ : Fin (m + n)))) =
                 eps g1 * eps g2 := by
    unfold eps
    have hfn : (fun k : Fin (m + n) => (finAppend (fun i : Fin m => (⟨(g1 i).val, Nat.lt_of_lt_of_le (g1 i).isLt (Nat.le_add_right m n)⟩ : Fin (m + n)))
                                                  (fun j : Fin n => (⟨m + (g2 j).val, Nat.add_lt_add_left (g2 j).isLt m⟩ : Fin (m + n))) k).val) =
               finAppend (fun i : Fin m => (g1 i).val) (fun j : Fin n => m + (g2 j).val) := by
      funext k; unfold finAppend; by_cases hk : k.val < m <;> simp [hk]
    rw [hfn, epsNat_split]
    have hshift : ∀ (r : Nat) (v : Fin r → Nat), epsNat r (fun j => m + v j) = epsNat r v := by
      intro r
      induction r with
      | zero => intro _; rfl
      | succ r ihr =>
        intro v; simp only [epsNat]; rw [ihr (fun j => v j.castSucc)]
        congr 1; apply prodFin_congr; intro j; unfold pairSign
        have h1 : m + v j.castSucc < m + v (Fin.last r) ↔ v j.castSucc < v (Fin.last r) := by omega
        simp [h1]
    rw [hshift n (fun j => (g2 j).val)]
    have hcross : prodFin (R := Int) n (fun j => prodFin (R := Int) m (fun i => pairSign (g1 i).val (m + (g2 j).val))) = 1 := by
      have h1 : prodFin (R := Int) n (fun j => prodFin (R := Int) m (fun i => pairSign (g1 i).val (m + (g2 j).val))) =
                prodFin (R := Int) n (fun _ => CRing.one) := by
        apply prodFin_congr; intro j
        have h2 : prodFin (R := Int) m (fun i => pairSign (g1 i).val (m + (g2 j).val)) =
                  prodFin (R := Int) m (fun _ => CRing.one) :=
          prodFin_congr (fun i => pairSign_lt (by have := (g1 i).isLt; omega))
        rw [h2]; exact prodFin_one (R := Int) m
      rw [h1]; exact prodFin_one (R := Int) n
    rw [hcross, Int.mul_one]
  rw [heps_sp, CRing.ofInt_mul, prodFin_split (m := m) (n := n)]
  have hlo : prodFin m (fun i => blockMat A (fun _ _ => CRing.zero) C D ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right m n)⟩
      (finAppend (fun r : Fin m => (⟨(g1 r).val, Nat.lt_of_lt_of_le (g1 r).isLt (Nat.le_add_right m n)⟩ : Fin (m + n)))
                 (fun r : Fin n => (⟨m + (g2 r).val, Nat.add_lt_add_left (g2 r).isLt m⟩ : Fin (m + n)))
                 ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right m n)⟩)) =
      prodFin m (fun i => A i (g1 i)) := by
    apply prodFin_congr; intro i; unfold blockMat finAppend; simp [i.isLt, (g1 i).isLt]
  have hhi : prodFin n (fun j => blockMat A (fun _ _ => CRing.zero) C D ⟨m + j.val, Nat.add_lt_add_left j.isLt m⟩
      (finAppend (fun r : Fin m => (⟨(g1 r).val, Nat.lt_of_lt_of_le (g1 r).isLt (Nat.le_add_right m n)⟩ : Fin (m + n)))
                 (fun r : Fin n => (⟨m + (g2 r).val, Nat.add_lt_add_left (g2 r).isLt m⟩ : Fin (m + n)))
                 ⟨m + j.val, Nat.add_lt_add_left j.isLt m⟩)) =
      prodFin n (fun j => D j (g2 j)) := by
    apply prodFin_congr; intro j; unfold blockMat finAppend
    have h1 : ¬ (m + j.val < m) := by omega
    simp only [h1, dite_false]
    have hsub : (⟨m + j.val - m, by omega⟩ : Fin n) = j := Fin.ext (by simp)
    have h2' : ¬ (m + (g2 ⟨m + j.val - m, by omega⟩).val < m) := by omega
    simp only [h2', dite_false]
    have harg : (⟨m + (g2 ⟨m + j.val - m, by omega⟩).val - m, by omega⟩ : Fin n) = g2 j := by
      apply Fin.ext; simp
    rw [harg, hsub]
  rw [hlo, hhi]
  rw [CRing.mul_assoc, ← CRing.mul_assoc (CRing.ofInt (eps g2)),
      CRing.mul_comm (CRing.ofInt (eps g2)) (prodFin m (fun i => A i (g1 i))),
      CRing.mul_assoc, ← CRing.mul_assoc, CRing.mul_assoc]

theorem det_blockUpper_zero {n : Nat} (A B D : Mat R n) :
    det (blockMat A B (matZero n) D) = CRing.mul (det A) (det D) :=
  det_blockUpper A B D

theorem det_blockLower_zero {n : Nat} (A C D : Mat R n) :
    det (blockMat A (matZero n) C D) = CRing.mul (det A) (det D) :=
  det_blockLower A C D

/-! ## Section 3: Reusable Division-Free Block-Schur Lifting Engine -/

end MatDefs

/-! ### Reusable Bit-Sliced Schur Lifting Meta-Engine (`pow2` + Finite → Infinite Compiler) -/

/-- Bit-split friendly powers of 2: `pow2 (k + 1)` is definitionally `pow2 k + pow2 k`! -/
def pow2 : Nat → Nat
  | 0 => 1
  | k + 1 => pow2 k + pow2 k

theorem pow2_pos (k : Nat) : 0 < pow2 k := by
  induction k with
  | zero => exact Nat.zero_lt_one
  | succ k ih => unfold pow2; omega

theorem pow2_eq (k : Nat) : pow2 k = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold pow2; rw [ih, Nat.pow_succ]; omega

/-- Generic bitmask-tree leaf evaluator driven by a 1-step renormalization rule `step`. -/
def evalBitTree {P : Nat → Type u} {R : Type v}
    (base : P 0 → R)
    (step : ∀ k, P (k + 1) → P k × P k) :
    ∀ k, P k → Fin (pow2 k) → R
  | 0, p, _ => base p
  | k + 1, p, s =>
    if h : s.val < pow2 k then
      evalBitTree base step k (step k p).1 ⟨s.val, h⟩
    else
      evalBitTree base step k (step k p).2 ⟨s.val - pow2 k, by have hlt := s.isLt; unfold pow2 at hlt; omega⟩

/-- **REUSABLE INFINITE PROOF MECHANISM (`det_bitSliced_schur_lift`)**:
    Given ANY parameterized family of `2^k × 2^k` matrices `M k p` over any `CRing R`,
    together with a finite 1-step renormalization rule `step k p = (p0, p1)` certified by a
    block-Schur reduction `det (M (k+1) p) = det (M k p0) * det (M k p1)`, lifts the finite
    step law automatically to an exact `2^k`-factor bitmask product formula for ALL `k : Nat`! -/
theorem det_bitSliced_schur_lift {R : Type u} [CRing R]
    {P : Nat → Type v}
    (M : ∀ k, P k → Mat R (pow2 k))
    (base : P 0 → R)
    (step : ∀ k, P (k + 1) → P k × P k)
    (hbase : ∀ p : P 0, det (M 0 p) = base p)
    (hstep : ∀ k (p : P (k + 1)),
      det (M (k + 1) p) = CRing.mul (det (M k (step k p).1)) (det (M k (step k p).2))) :
    ∀ k (p : P k), det (M k p) = prodFin (pow2 k) (evalBitTree base step k p) := by
  intro k
  induction k with
  | zero =>
    intro p
    rw [hbase p]
    change base p = CRing.mul CRing.one (base p)
    rw [CRing.one_mul]
  | succ k ih =>
    intro p
    rw [hstep k p, ih (step k p).1, ih (step k p).2]
    have hsp := prodFin_split (R := R) (m := pow2 k) (n := pow2 k)
      (fun s : Fin (pow2 k + pow2 k) => evalBitTree base step (k + 1) p s)
    change CRing.mul (prodFin (pow2 k) (evalBitTree base step k (step k p).1))
                     (prodFin (pow2 k) (evalBitTree base step k (step k p).2)) =
           prodFin (pow2 k + pow2 k) (fun s : Fin (pow2 k + pow2 k) => evalBitTree base step (k + 1) p s)
    rw [hsp]
    congr 1
    · apply prodFin_congr; intro i
      have h1 : evalBitTree base step (k + 1) p ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right _ _)⟩ =
                evalBitTree base step k (step k p).1 i := by
        simp only [evalBitTree, i.isLt, dite_true]
      exact h1.symm
    · apply prodFin_congr; intro j
      have h : ¬ (pow2 k + j.val < pow2 k) := by omega
      have h2 : evalBitTree base step (k + 1) p ⟨pow2 k + j.val, Nat.add_lt_add_left j.isLt (pow2 k)⟩ =
                evalBitTree base step k (step k p).2 j := by
        simp only [evalBitTree, h, dite_false]
        congr 1; apply Fin.ext; simp
      exact h2.symm

theorem testBit_lt_pow2 (k x m : Nat) (hx : x < pow2 k) (hm : k ≤ m) :
    x.testBit m = false := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h1 : pow2 k = 2 ^ k := pow2_eq k
  have h2 : 2 ^ k ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm
  have hlt : x < 2 ^ m := by omega
  rw [Nat.div_eq_of_lt hlt]
  decide

theorem testBit_add_pow2_eq (k x : Nat) (hx : x < pow2 k) :
    (pow2 k + x).testBit k = true := by
  rw [Nat.testBit_eq_decide_div_mod_eq, pow2_eq]
  have hlt : x < 2 ^ k := by rw [← pow2_eq]; exact hx
  have hpos : 0 < 2 ^ k := Nat.pow_pos (by omega)
  have hdiv : (2 ^ k + x) / 2 ^ k = 1 := by
    rw [Nat.add_div_left x hpos, Nat.div_eq_of_lt hlt]
  rw [hdiv]
  decide

theorem testBit_add_pow2_lt (k x m : Nat) (hm : m < k) :
    (pow2 k + x).testBit m = x.testBit m := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, pow2_eq]
  have hpos : 0 < 2 ^ m := Nat.pow_pos (by omega)
  have hexp : 2 ^ k = 2 ^ m * (2 * 2 ^ (k - m - 1)) := by
    have hk : k = m + (1 + (k - m - 1)) := by omega
    calc 2 ^ k = 2 ^ (m + (1 + (k - m - 1))) := congrArg (2 ^ ·) hk
      _ = 2 ^ m * (2 * 2 ^ (k - m - 1)) := by rw [Nat.pow_add, Nat.pow_add, Nat.pow_one]
  rw [hexp, Nat.mul_add_div hpos]
  have hmod : (2 * 2 ^ (k - m - 1) + x / 2 ^ m) % 2 = (x / 2 ^ m) % 2 := by omega
  rw [hmod]

theorem testBit_add_pow2_gt (k x m : Nat) (hx : x < pow2 k) (hm : k < m) :
    (pow2 k + x).testBit m = false := by
  apply testBit_lt_pow2 (k + 1) (pow2 k + x) m
  · change pow2 k + x < pow2 k + pow2 k; omega
  · omega

theorem and_lt_pow2 (k x y : Nat) (hx : x < pow2 k) (_hy : y < pow2 k) :
    (x &&& y) < pow2 k := by
  have hle : (x &&& y) ≤ x := Nat.and_le_left
  omega

theorem and_add_pow2_right (k x y : Nat) (hx : x < pow2 k) (_hy : y < pow2 k) :
    (x &&& (pow2 k + y)) = (x &&& y) := by
  apply Nat.eq_of_testBit_eq; intro m
  rw [Nat.testBit_and, Nat.testBit_and]
  by_cases hm : m < k
  · rw [testBit_add_pow2_lt k y m hm]
  · rw [testBit_lt_pow2 k x m hx (by omega)]; simp

theorem and_add_pow2_left (k x y : Nat) (hx : x < pow2 k) (hy : y < pow2 k) :
    ((pow2 k + x) &&& y) = (x &&& y) := by
  rw [Nat.and_comm, and_add_pow2_right k y x hy hx, Nat.and_comm]

theorem and_add_pow2_both (k x y : Nat) (hx : x < pow2 k) (hy : y < pow2 k) :
    ((pow2 k + x) &&& (pow2 k + y)) = pow2 k + (x &&& y) := by
  apply Nat.eq_of_testBit_eq; intro m
  rw [Nat.testBit_and]
  have hxy : (x &&& y) < pow2 k := and_lt_pow2 k x y hx hy
  by_cases hm1 : m < k
  · rw [testBit_add_pow2_lt k x m hm1, testBit_add_pow2_lt k y m hm1,
        testBit_add_pow2_lt k (x &&& y) m hm1, Nat.testBit_and]
  · by_cases hm2 : m = k
    · subst m
      rw [testBit_add_pow2_eq k x hx, testBit_add_pow2_eq k y hy, testBit_add_pow2_eq k (x &&& y) hxy]
      rfl
    · have hm3 : k < m := by omega
      rw [testBit_add_pow2_gt k x m hx hm3, testBit_add_pow2_gt k y m hy hm3,
          testBit_add_pow2_gt k (x &&& y) m hxy hm3]
      rfl

/-- Structurally recursive 1-indexed highest set bit of `z` (`0` if `z = 0`), fully kernel-reducible! -/
def msbPosAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, z => if z = 0 then 0 else msbPosAux fuel (z / 2) + 1

def msbPos (z : Nat) : Nat := msbPosAux z z

theorem msbPosAux_eq_of_le (fuel1 fuel2 z : Nat) (h1 : z ≤ fuel1) (h2 : z ≤ fuel2) :
    msbPosAux fuel1 z = msbPosAux fuel2 z := by
  induction fuel1 generalizing fuel2 z with
  | zero =>
    have hz : z = 0 := by omega
    subst hz; cases fuel2 <;> simp [msbPosAux]
  | succ f1 ih =>
    cases fuel2 with
    | zero =>
      have hz : z = 0 := by omega
      subst hz; simp [msbPosAux]
    | succ f2 =>
      unfold msbPosAux
      by_cases hz : z = 0
      · simp [hz]
      · simp only [hz, ite_false]
        rw [ih f2 (z / 2) (by omega) (by omega)]

theorem msbPos_zero : msbPos 0 = 0 := rfl

theorem msbPos_pos_eq (z : Nat) (hz : z ≠ 0) : msbPos z = msbPos (z / 2) + 1 := by
  cases z with
  | zero => exact absurd rfl hz
  | succ z' =>
    change (if z' + 1 = 0 then 0 else msbPosAux z' ((z' + 1) / 2) + 1) =
           msbPosAux ((z' + 1) / 2) ((z' + 1) / 2) + 1
    simp only [Nat.succ_ne_zero, ite_false]
    rw [msbPosAux_eq_of_le z' ((z' + 1) / 2) ((z' + 1) / 2) (by omega) (Nat.le_refl _)]

theorem msbPos_lt_pow2 (k z : Nat) (hz : z < pow2 k) : msbPos z ≤ k := by
  induction k generalizing z with
  | zero =>
    have h0 : z = 0 := by unfold pow2 at hz; omega
    subst h0; rw [msbPos_zero]; exact Nat.le_refl 0
  | succ k ih =>
    by_cases h0 : z = 0
    · subst h0; rw [msbPos_zero]; exact Nat.zero_le _
    · rw [msbPos_pos_eq z h0]
      have hdiv : z / 2 < pow2 k := by unfold pow2 at hz; omega
      have hle := ih (z / 2) hdiv
      omega

theorem msbPos_add_pow2 (k z : Nat) (hz : z < pow2 k) : msbPos (pow2 k + z) = k + 1 := by
  induction k generalizing z with
  | zero =>
    have h0 : z = 0 := by unfold pow2 at hz; omega
    subst h0; decide
  | succ k ih =>
    have hne : pow2 (k + 1) + z ≠ 0 := by have := pow2_pos (k + 1); omega
    rw [msbPos_pos_eq _ hne]
    have hdiv : (pow2 (k + 1) + z) / 2 = pow2 k + z / 2 := by
      change (pow2 k + pow2 k + z) / 2 = pow2 k + z / 2; omega
    rw [hdiv, ih (z / 2) (by unfold pow2 at hz; omega)]

theorem testBit_msbPos_pred (z : Nat) (hz : z ≠ 0) : z.testBit (msbPos z - 1) = true := by
  induction z using Nat.strongRecOn with
  | ind z ih =>
    by_cases h1 : z / 2 = 0
    · have hz1 : z = 1 := by omega
      subst hz1; decide
    · rw [msbPos_pos_eq z hz]
      have hsub : msbPos (z / 2) + 1 - 1 = msbPos (z / 2) := by omega
      rw [hsub]
      have hpos : 0 < msbPos (z / 2) := by rw [msbPos_pos_eq (z / 2) h1]; omega
      have hrec := ih (z / 2) (by omega) h1
      have htb : z.testBit (msbPos (z / 2)) = (z / 2).testBit (msbPos (z / 2) - 1) := by
        rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
        have hk : msbPos (z / 2) = (msbPos (z / 2) - 1) + 1 := by omega
        have hpow : 2 ^ msbPos (z / 2) = 2 * 2 ^ (msbPos (z / 2) - 1) := by
          calc 2 ^ msbPos (z / 2) = 2 ^ ((msbPos (z / 2) - 1) + 1) := congrArg (2 ^ ·) hk
            _ = 2 * 2 ^ (msbPos (z / 2) - 1) := by rw [Nat.pow_succ, Nat.mul_comm]
        rw [hpow, ← Nat.div_div_eq_div_mul]
      rw [htb, hrec]

/-- Structurally recursive bitwise popcount (Hamming weight) on `Nat`, fully kernel-reducible! -/
def popcountAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, z => if z = 0 then 0 else (z % 2) + popcountAux fuel (z / 2)

def popcount (z : Nat) : Nat := popcountAux z z

theorem popcountAux_eq_of_le (fuel1 fuel2 z : Nat) (h1 : z ≤ fuel1) (h2 : z ≤ fuel2) :
    popcountAux fuel1 z = popcountAux fuel2 z := by
  induction fuel1 generalizing fuel2 z with
  | zero =>
    have hz : z = 0 := by omega
    subst hz; cases fuel2 <;> simp [popcountAux]
  | succ f1 ih =>
    cases fuel2 with
    | zero =>
      have hz : z = 0 := by omega
      subst hz; simp [popcountAux]
    | succ f2 =>
      unfold popcountAux
      by_cases hz : z = 0
      · simp [hz]
      · simp only [hz, ite_false]
        rw [ih f2 (z / 2) (by omega) (by omega)]

theorem popcount_zero : popcount 0 = 0 := rfl

theorem popcount_pos_eq (z : Nat) (hz : z ≠ 0) : popcount z = (z % 2) + popcount (z / 2) := by
  cases z with
  | zero => exact absurd rfl hz
  | succ z' =>
    change (if z' + 1 = 0 then 0 else (z' + 1) % 2 + popcountAux z' ((z' + 1) / 2)) =
           (z' + 1) % 2 + popcountAux ((z' + 1) / 2) ((z' + 1) / 2)
    simp only [Nat.succ_ne_zero, ite_false]
    rw [popcountAux_eq_of_le z' ((z' + 1) / 2) ((z' + 1) / 2) (by omega) (Nat.le_refl _)]

theorem popcount_add_pow2 (k z : Nat) (hz : z < pow2 k) :
    popcount (pow2 k + z) = 1 + popcount z := by
  induction k generalizing z with
  | zero =>
    have h0 : z = 0 := by unfold pow2 at hz; omega
    subst h0; decide
  | succ k ih =>
    have hne : pow2 (k + 1) + z ≠ 0 := by have := pow2_pos (k + 1); omega
    rw [popcount_pos_eq _ hne]
    have hmod : (pow2 (k + 1) + z) % 2 = z % 2 := by
      change (pow2 k + pow2 k + z) % 2 = z % 2; omega
    have hdiv : (pow2 (k + 1) + z) / 2 = pow2 k + z / 2 := by
      change (pow2 k + pow2 k + z) / 2 = pow2 k + z / 2; omega
    rw [hmod, hdiv, ih (z / 2) (by unfold pow2 at hz; omega)]
    by_cases hz0 : z = 0
    · subst hz0; simp [popcount_zero]
    · rw [popcount_pos_eq z hz0]; omega

/-! ### Family I: Non-Uniform Highest-Common-Bit (HCB) Weighted Kernel -/

section FamilyI
variable {R : Type u} [CRing R]

/-- Single bit-slice weight at 0-indexed bit `b` (1-indexed `b + 1`). -/
def bitWeight (γ α β δ : Nat → R) (b x y : Nat) : R :=
  match x.testBit b, y.testBit b with
  | false, false => γ (b + 1)
  | false, true  => α (b + 1)
  | true,  false => β (b + 1)
  | true,  true  => δ (b + 1)

/-- Background non-uniform Kronecker bit-weight matrix `G_k`. -/
def kronBitMat (γ α β δ : Nat → R) (k : Nat) : Mat R (pow2 k) :=
  fun x y => prodFin k (fun b => bitWeight γ α β δ b.val x.val y.val)

/-- **Family I: Non-Uniform Highest-Common-Bit (HCB) Weighted Kernel Matrix `H_k(f; γ, α, β, δ)`**.
    At entry `(x, y)`, `j = msbPos(x &&& y)` selects the profile value `f j`, while every
    other bit `b ≠ j - 1` contributes its bit-pair weight `bitWeight γ α β δ b x y`. -/
def hcbMat (γ α β δ : Nat → R) (k : Nat) (f : Nat → R) : Mat R (pow2 k) :=
  fun x y =>
    let j := msbPos (x.val &&& y.val)
    CRing.mul (f j)
      (prodFin k (fun b => if b.val + 1 = j then CRing.one else bitWeight γ α β δ b.val x.val y.val))

/-- Exact 1-step Schur-complement profile renormalization operator `T_m`. -/
def hcbRenorm (γ α β δ : Nat → R) (m : Nat) (f : Nat → R) : Nat → R :=
  fun j =>
    if j = 0 then
      CRing.sub (CRing.mul (γ m) (f m)) (CRing.mul (CRing.mul (α m) (β m)) (f 0))
    else
      CRing.sub (CRing.mul (CRing.mul (γ m) (δ j)) (f m))
                (CRing.mul (CRing.mul (α m) (β m)) (f j))

theorem det_hcbMat_zero (γ α β δ : Nat → R) (f : Nat → R) :
    det (hcbMat γ α β δ 0 f) = f 0 := by
  unfold det hcbMat
  change CRing.add CRing.zero
    (CRing.mul (CRing.ofInt (eps (finSnoc Fin.elim0 ⟨0, Nat.zero_lt_one⟩)))
      (CRing.mul CRing.one (CRing.mul (f (msbPos (0 &&& 0))) CRing.one))) = f 0
  have heps : eps (finSnoc Fin.elim0 (⟨0, Nat.zero_lt_one⟩ : Fin 1)) = 1 := rfl
  have hand : msbPos (0 &&& 0) = 0 := by decide
  rw [heps, hand, CRing.ofInt_one, CRing.zero_add, CRing.one_mul, CRing.one_mul, CRing.mul_one]

/-- Exact MSB bit-splitting identity for `hcbMat` at size `2^(k+1) × 2^(k+1)`. -/
theorem hcbMat_succ_eq_block (γ α β δ : Nat → R) (k : Nat) (f : Nat → R) :
    hcbMat γ α β δ (k + 1) f =
    blockMat (matSmul (γ (k + 1)) (hcbMat γ α β δ k f))
             (matSmul (α (k + 1)) (hcbMat γ α β δ k f))
             (matSmul (β (k + 1)) (hcbMat γ α β δ k f))
             (matSmul (f (k + 1)) (kronBitMat γ α β δ k)) := by
  funext x y
  unfold hcbMat blockMat matSmul kronBitMat
  simp only [prodFin, Fin.val_castSucc, Fin.val_last]
  by_cases hx : x.val < pow2 k <;> by_cases hy : y.val < pow2 k
  · -- (0, 0) block
    simp only [hx, hy, dite_true]
    have hjle : msbPos (x.val &&& y.val) ≤ k :=
      msbPos_lt_pow2 k _ (and_lt_pow2 k x.val y.val hx hy)
    have hne : k + 1 ≠ msbPos (x.val &&& y.val) := by omega
    have hbw : bitWeight γ α β δ k x.val y.val = γ (k + 1) := by
      unfold bitWeight
      rw [testBit_lt_pow2 k x.val k hx (Nat.le_refl k),
          testBit_lt_pow2 k y.val k hy (Nat.le_refl k)]
    simp only [hne, ite_false, hbw]
    rw [← CRing.mul_assoc, CRing.mul_comm (CRing.mul (f _) (prodFin k _)) (γ (k + 1))]
  · -- (0, 1) block
    simp only [hx, hy, dite_true, dite_false]
    have hy' : y.val - pow2 k < pow2 k := by have hlt := y.isLt; unfold pow2 at hlt; omega
    have hy_eq : y.val = pow2 k + (y.val - pow2 k) := by omega
    have hand : (x.val &&& y.val) = (x.val &&& (y.val - pow2 k)) := by
      have h := and_add_pow2_right k x.val (y.val - pow2 k) hx hy'
      rwa [← hy_eq] at h
    have hjle : msbPos (x.val &&& (y.val - pow2 k)) ≤ k :=
      msbPos_lt_pow2 k _ (and_lt_pow2 k x.val (y.val - pow2 k) hx hy')
    have hne : k + 1 ≠ msbPos (x.val &&& (y.val - pow2 k)) := by omega
    have hbw : bitWeight γ α β δ k x.val y.val = α (k + 1) := by
      unfold bitWeight
      rw [testBit_lt_pow2 k x.val k hx (Nat.le_refl k), hy_eq, testBit_add_pow2_eq k _ hy']
    have hprod : prodFin k (fun b => if b.val + 1 = msbPos (x.val &&& (y.val - pow2 k)) then CRing.one
                                     else bitWeight γ α β δ b.val x.val y.val) =
                 prodFin k (fun b => if b.val + 1 = msbPos (x.val &&& (y.val - pow2 k)) then CRing.one
                                     else bitWeight γ α β δ b.val x.val (y.val - pow2 k)) := by
      apply prodFin_congr; intro b
      by_cases hc : b.val + 1 = msbPos (x.val &&& (y.val - pow2 k))
      · simp [hc]
      · simp only [hc, ite_false]; unfold bitWeight
        have htby := testBit_add_pow2_lt k (y.val - pow2 k) b.val b.isLt
        rw [← hy_eq] at htby; rw [htby]
    rw [hand, hbw, hprod]; simp only [hne, ite_false]
    rw [← CRing.mul_assoc, CRing.mul_comm (CRing.mul (f _) (prodFin k _)) (α (k + 1))]
  · -- (1, 0) block
    simp only [hx, hy, dite_true, dite_false]
    have hx' : x.val - pow2 k < pow2 k := by have hlt := x.isLt; unfold pow2 at hlt; omega
    have hx_eq : x.val = pow2 k + (x.val - pow2 k) := by omega
    have hand : (x.val &&& y.val) = ((x.val - pow2 k) &&& y.val) := by
      have h := and_add_pow2_left k (x.val - pow2 k) y.val hx' hy
      rwa [← hx_eq] at h
    have hjle : msbPos ((x.val - pow2 k) &&& y.val) ≤ k :=
      msbPos_lt_pow2 k _ (and_lt_pow2 k (x.val - pow2 k) y.val hx' hy)
    have hne : k + 1 ≠ msbPos ((x.val - pow2 k) &&& y.val) := by omega
    have hbw : bitWeight γ α β δ k x.val y.val = β (k + 1) := by
      unfold bitWeight
      rw [hx_eq, testBit_add_pow2_eq k _ hx', testBit_lt_pow2 k y.val k hy (Nat.le_refl k)]
    have hprod : prodFin k (fun b => if b.val + 1 = msbPos ((x.val - pow2 k) &&& y.val) then CRing.one
                                     else bitWeight γ α β δ b.val x.val y.val) =
                 prodFin k (fun b => if b.val + 1 = msbPos ((x.val - pow2 k) &&& y.val) then CRing.one
                                     else bitWeight γ α β δ b.val (x.val - pow2 k) y.val) := by
      apply prodFin_congr; intro b
      by_cases hc : b.val + 1 = msbPos ((x.val - pow2 k) &&& y.val)
      · simp [hc]
      · simp only [hc, ite_false]; unfold bitWeight
        have htbx := testBit_add_pow2_lt k (x.val - pow2 k) b.val b.isLt
        rw [← hx_eq] at htbx; rw [htbx]
    rw [hand, hbw, hprod]; simp only [hne, ite_false]
    rw [← CRing.mul_assoc, CRing.mul_comm (CRing.mul (f _) (prodFin k _)) (β (k + 1))]
  · -- (1, 1) block
    simp only [hx, hy, dite_false]
    have hx' : x.val - pow2 k < pow2 k := by have hlt := x.isLt; unfold pow2 at hlt; omega
    have hy' : y.val - pow2 k < pow2 k := by have hlt := y.isLt; unfold pow2 at hlt; omega
    have hx_eq : x.val = pow2 k + (x.val - pow2 k) := by omega
    have hy_eq : y.val = pow2 k + (y.val - pow2 k) := by omega
    have hand : (x.val &&& y.val) = pow2 k + ((x.val - pow2 k) &&& (y.val - pow2 k)) := by
      have h := and_add_pow2_both k (x.val - pow2 k) (y.val - pow2 k) hx' hy'
      rwa [← hx_eq, ← hy_eq] at h
    have hmsb : msbPos (x.val &&& y.val) = k + 1 := by
      rw [hand]
      exact msbPos_add_pow2 k _ (and_lt_pow2 k _ _ hx' hy')
    rw [hmsb]; simp only [ite_true, CRing.mul_one]
    congr 1
    apply prodFin_congr; intro b
    have hne : b.val + 1 ≠ k + 1 := by omega
    simp only [hne, ite_false]
    unfold bitWeight
    have htbx := testBit_add_pow2_lt k (x.val - pow2 k) b.val b.isLt
    have htby := testBit_add_pow2_lt k (y.val - pow2 k) b.val b.isLt
    rw [← hx_eq] at htbx; rw [← hy_eq] at htby
    rw [htbx, htby]

/-- Exact Schur-complement closure identity for Family I! -/
theorem hcbMat_schur_closure (γ α β δ : Nat → R) (k : Nat) (f : Nat → R) :
    matSub (matSmul (γ (k + 1)) (matSmul (f (k + 1)) (kronBitMat γ α β δ k)))
           (matSmul (CRing.mul (α (k + 1)) (β (k + 1))) (hcbMat γ α β δ k f)) =
    hcbMat γ α β δ k (hcbRenorm γ α β δ (k + 1) f) := by
  funext x y
  unfold matSub matSmul kronBitMat hcbMat hcbRenorm
  let j := msbPos (x.val &&& y.val)
  change CRing.sub (CRing.mul (γ (k + 1)) (CRing.mul (f (k + 1)) (prodFin k (fun b => bitWeight γ α β δ b.val x.val y.val))))
                   (CRing.mul (CRing.mul (α (k + 1)) (β (k + 1)))
                     (CRing.mul (f j) (prodFin k (fun b => if b.val + 1 = j then CRing.one else bitWeight γ α β δ b.val x.val y.val)))) =
         CRing.mul (if j = 0 then CRing.sub (CRing.mul (γ (k + 1)) (f (k + 1))) (CRing.mul (CRing.mul (α (k + 1)) (β (k + 1))) (f 0))
                    else CRing.sub (CRing.mul (CRing.mul (γ (k + 1)) (δ j)) (f (k + 1))) (CRing.mul (CRing.mul (α (k + 1)) (β (k + 1))) (f j)))
                   (prodFin k (fun b => if b.val + 1 = j then CRing.one else bitWeight γ α β δ b.val x.val y.val))
  by_cases hj0 : j = 0
  · simp only [hj0, ite_true]
    have hprod : prodFin k (fun b => if b.val + 1 = 0 then CRing.one else bitWeight γ α β δ b.val x.val y.val) =
                 prodFin k (fun b => bitWeight γ α β δ b.val x.val y.val) :=
      prodFin_congr (fun b => by simp)
    rw [hprod, ← CRing.mul_assoc, ← CRing.mul_assoc, ← CRing.sub_mul]
  · simp only [hj0, ite_false]
    have hjle : j ≤ k := msbPos_lt_pow2 k _ (and_lt_pow2 k x.val y.val x.isLt y.isLt)
    have hne_and : (x.val &&& y.val) ≠ 0 := by
      intro h0; apply hj0; dsimp only [j]; rw [h0, msbPos_zero]
    have htb_and : (x.val &&& y.val).testBit (j - 1) = true := testBit_msbPos_pred _ hne_and
    rw [Nat.testBit_and, Bool.and_eq_true] at htb_and
    have hbw_j : bitWeight γ α β δ (j - 1) x.val y.val = δ j := by
      unfold bitWeight
      rw [htb_and.1, htb_and.2]
      have : j - 1 + 1 = j := by omega
      rw [this]
    have hfactor : prodFin k (fun b => bitWeight γ α β δ b.val x.val y.val) =
                   CRing.mul (δ j)
                     (prodFin k (fun b => if b.val + 1 = j then CRing.one else bitWeight γ α β δ b.val x.val y.val)) := by
      suffices hp : ∀ (m : Nat) (P : Fin m → R) (idx : Fin m),
          prodFin m P = CRing.mul (P idx) (prodFin m (fun b => if b = idx then CRing.one else P b)) by
        have h := hp k (fun b => bitWeight γ α β δ b.val x.val y.val) ⟨j - 1, by omega⟩
        rw [h, hbw_j]
        congr 1; apply prodFin_congr; intro b
        have hiff : b = ⟨j - 1, by omega⟩ ↔ b.val + 1 = j := by
          constructor
          · intro heq; have hv := congrArg Fin.val heq; simp at hv; omega
          · intro hv; apply Fin.ext; simp; omega
        by_cases hc : b.val + 1 = j
        · have hc' : b = ⟨j - 1, by omega⟩ := hiff.mpr hc
          simp only [hc, ite_true]
          simp only [hc', ite_true]
        · have hc' : b ≠ ⟨j - 1, by omega⟩ := fun h => hc (hiff.mp h)
          simp only [hc, ite_false]
          simp only [hc', ite_false]
      intro m
      induction m with
      | zero => intro _ idx; exact Fin.elim0 idx
      | succ m ih =>
        intro P idx
        simp only [prodFin]
        by_cases hlt : idx.val < m
        · have hne : Fin.last m ≠ idx := by intro h; have := congrArg Fin.val h; simp at this; omega
          simp only [hne, ite_false]
          have hrec := ih (fun b => P b.castSucc) ⟨idx.val, hlt⟩
          have hcast : (⟨idx.val, hlt⟩ : Fin m).castSucc = idx := Fin.ext rfl
          rw [hrec, hcast, CRing.mul_assoc]
          congr 1; congr 1
          apply prodFin_congr; intro b
          have hiff : b = ⟨idx.val, hlt⟩ ↔ b.castSucc = idx := by
            constructor
            · intro h; apply Fin.ext; have hv := congrArg Fin.val h; exact hv
            · intro h; apply Fin.ext; have hv := congrArg Fin.val h; exact hv
          by_cases hc : b = ⟨idx.val, hlt⟩
          · simp [hc]
          · have hc' : b.castSucc ≠ idx := fun h => hc (hiff.mpr h)
            simp [hc, hc']
        · have heq : idx = Fin.last m := by apply Fin.ext; simp; omega
          subst heq
          simp only [ite_true, CRing.mul_one]
          have hlo : prodFin m (fun b => if b.castSucc = Fin.last m then CRing.one else P b.castSucc) =
                     prodFin m (fun b => P b.castSucc) :=
            prodFin_congr (fun b => by
              have : b.castSucc ≠ Fin.last m := by intro h; have := congrArg Fin.val h; simp at this; omega
              simp [this])
          rw [hlo, CRing.mul_comm]
    rw [hfactor]
    rw [← CRing.mul_assoc (f (k + 1)), ← CRing.mul_assoc (γ (k + 1)),
        CRing.mul_comm (f (k + 1)) (δ j), ← CRing.mul_assoc (γ (k + 1)),
        ← CRing.mul_assoc (CRing.mul (α (k + 1)) (β (k + 1))), ← CRing.sub_mul]

/-- Product of `-(α (b+1) * β (b+1))` over set bits of `s` in `[lo, lo + len)`. -/
def negPProd (α β : Nat → R) (s : Nat) : Nat → Nat → R
  | _, 0 => CRing.one
  | lo, len + 1 =>
    CRing.mul (negPProd α β s lo len)
      (if s.testBit (lo + len) then CRing.neg (CRing.mul (α (lo + len + 1)) (β (lo + len + 1))) else CRing.one)

/-- Product of `Δ_{b+1} = γ_{b+1}*δ_{b+1} - α_{b+1}*β_{b+1}` over set bits of `s` in `[0, len)`. -/
def deltaProd (γ α β δ : Nat → R) (s : Nat) : Nat → R
  | 0 => CRing.one
  | len + 1 =>
    CRing.mul (deltaProd γ α β δ s len)
      (if s.testBit len then CRing.sub (CRing.mul (γ (len + 1)) (δ (len + 1)))
                                       (CRing.mul (α (len + 1)) (β (len + 1)))
       else CRing.one)

/-- **Explicit Non-Recursive Closed-Form Bitmask Factor `L_s(f)`** for Family I:
    `L_s(f) = (∏_{u ∈ s} (-p_u)) * f(0) + ∑_{t ∈ s} (∏_{u ∈ s, u < t} Δ_u) * γ_t * (∏_{u ∈ s, u > t} (-p_u)) * f(t)`. -/
def hcbMaskFactor (γ α β δ : Nat → R) (k : Nat) (f : Nat → R) (s : Nat) : R :=
  CRing.add
    (CRing.mul (negPProd α β s 0 k) (f 0))
    (sumFin k (fun b =>
      if s.testBit b.val then
        CRing.mul
          (CRing.mul (CRing.mul (deltaProd γ α β δ s b.val) (γ (b.val + 1)))
                     (negPProd α β s (b.val + 1) (k - (b.val + 1))))
          (f (b.val + 1))
      else CRing.zero))

/-- Key telescoping identity:
    `negPProd(0, k) + ∑_{b < k, s_b = 1} deltaProd(b) * (γ_{b+1} * δ_{b+1}) * negPProd(b+1, k-(b+1)) = deltaProd(k)`. -/
theorem hcb_telescoping (γ α β δ : Nat → R) (s k : Nat) :
    CRing.add (negPProd α β s 0 k)
      (sumFin k (fun b =>
        if s.testBit b.val then
          CRing.mul (CRing.mul (deltaProd γ α β δ s b.val) (CRing.mul (γ (b.val + 1)) (δ (b.val + 1))))
                    (negPProd α β s (b.val + 1) (k - (b.val + 1)))
        else CRing.zero)) =
    deltaProd γ α β δ s k := by
  induction k with
  | zero =>
    change CRing.add CRing.one CRing.zero = CRing.one
    exact CRing.add_zero CRing.one
  | succ k ih =>
    -- Split off the last bit k!
    have hneg_split : ∀ (lo len : Nat),
        negPProd α β s lo (len + 1) =
        CRing.mul (negPProd α β s lo len)
          (if s.testBit (lo + len) then CRing.neg (CRing.mul (α (lo + len + 1)) (β (lo + len + 1))) else CRing.one) :=
      fun _ _ => rfl
    let wK := if s.testBit k then CRing.neg (CRing.mul (α (k + 1)) (β (k + 1))) else CRing.one
    have hnp0 : negPProd α β s 0 (k + 1) = CRing.mul (negPProd α β s 0 k) wK := by
      simp only [negPProd, Nat.zero_add, wK]
    have hsum_step :
        sumFin (k + 1) (fun b =>
          if s.testBit b.val then
            CRing.mul (CRing.mul (deltaProd γ α β δ s b.val) (CRing.mul (γ (b.val + 1)) (δ (b.val + 1))))
                      (negPProd α β s (b.val + 1) (k + 1 - (b.val + 1)))
          else CRing.zero) =
        CRing.add
          (CRing.mul
            (sumFin k (fun b =>
              if s.testBit b.val then
                CRing.mul (CRing.mul (deltaProd γ α β δ s b.val) (CRing.mul (γ (b.val + 1)) (δ (b.val + 1))))
                          (negPProd α β s (b.val + 1) (k - (b.val + 1)))
              else CRing.zero))
            wK)
          (if s.testBit k then CRing.mul (deltaProd γ α β δ s k) (CRing.mul (γ (k + 1)) (δ (k + 1))) else CRing.zero) := by
      simp only [sumFin, Fin.val_castSucc, Fin.val_last]
      congr 1
      · rw [sumFin_mul_right]
        apply sumFin_congr; intro b
        cases htb : s.testBit b.val with
        | false =>
          simp only [Bool.false_eq_true, ite_false, CRing.zero_mul]
        | true =>
          simp only [ite_true]
          have hsub : k + 1 - (b.val + 1) = (k - (b.val + 1)) + 1 := by omega
          have hadd : b.val + 1 + (k - (b.val + 1)) = k := by omega
          rw [hsub, hneg_split, hadd, ← CRing.mul_assoc]
      · cases htb : s.testBit k with
        | false =>
          simp only [Bool.false_eq_true, ite_false]
        | true =>
          simp only [ite_true, Nat.sub_self, negPProd, CRing.mul_one]
    rw [hnp0, hsum_step, ← CRing.add_assoc, ← CRing.right_distrib, ih]
    simp only [deltaProd]
    cases htb : s.testBit k with
    | false =>
      dsimp only [wK]
      simp only [htb, Bool.false_eq_true, ite_false, CRing.add_zero]
    | true =>
      dsimp only [wK]
      simp only [htb, ite_true]
      rw [CRing.mul_sub, CRing.mul_neg]
      unfold CRing.sub
      rw [CRing.add_comm]

/-- Invariance of `negPProd`, `deltaProd`, and `hcbMaskFactor` under adding `pow2 k` above bit `k`. -/
theorem negPProd_add_pow2 (α β : Nat → R) (k s lo len : Nat) (hle : lo + len ≤ k) :
    negPProd α β (pow2 k + s) lo len = negPProd α β s lo len := by
  induction len with
  | zero => rfl
  | succ len ih =>
    simp only [negPProd]
    rw [ih (by omega), testBit_add_pow2_lt k s (lo + len) (by omega)]

theorem deltaProd_add_pow2 (γ α β δ : Nat → R) (k s len : Nat) (hle : len ≤ k) :
    deltaProd γ α β δ (pow2 k + s) len = deltaProd γ α β δ s len := by
  induction len with
  | zero => rfl
  | succ len ih =>
    simp only [deltaProd]
    rw [ih (by omega), testBit_add_pow2_lt k s len (by omega)]

/-- Renormalization step on `hcbMaskFactor`: `L_s(T_{k+1} f) = L_{s + 2^k}(f)` for `s < 2^k`! -/
theorem hcbMaskFactor_renorm (γ α β δ : Nat → R) (k : Nat) (f : Nat → R) (s : Nat) (hs : s < pow2 k) :
    hcbMaskFactor γ α β δ k (hcbRenorm γ α β δ (k + 1) f) s =
    hcbMaskFactor γ α β δ (k + 1) f (pow2 k + s) := by
  unfold hcbMaskFactor hcbRenorm
  simp only [ite_true, show ∀ b : Fin k, b.val + 1 ≠ 0 from fun _ => Nat.succ_ne_zero _, ite_false]
  -- Expand LHS into f(k+1) part and f(0..k) part!
  let pK := CRing.mul (α (k + 1)) (β (k + 1))
  let gK := γ (k + 1)
  let fK := f (k + 1)
  -- Rewrite LHS term 0:
  have ht0 : CRing.mul (negPProd α β s 0 k) (CRing.sub (CRing.mul gK fK) (CRing.mul pK (f 0))) =
             CRing.add (CRing.mul (CRing.mul (negPProd α β s 0 k) gK) fK)
                       (CRing.mul (CRing.mul (negPProd α β s 0 k) (CRing.neg pK)) (f 0)) := by
    rw [CRing.mul_sub]
    unfold CRing.sub
    rw [← CRing.mul_assoc, ← CRing.mul_assoc, CRing.mul_neg, CRing.neg_mul]
  -- Rewrite LHS sum over b < k:
  have hsum_split :
      sumFin k (fun b =>
        if s.testBit b.val then
          CRing.mul
            (CRing.mul (CRing.mul (deltaProd γ α β δ s b.val) (γ (b.val + 1)))
                       (negPProd α β s (b.val + 1) (k - (b.val + 1))))
            (CRing.sub (CRing.mul (CRing.mul gK (δ (b.val + 1))) fK) (CRing.mul pK (f (b.val + 1))))
        else CRing.zero) =
      CRing.add
        (CRing.mul
          (CRing.mul
            (sumFin k (fun b =>
              if s.testBit b.val then
                CRing.mul (CRing.mul (deltaProd γ α β δ s b.val) (CRing.mul (γ (b.val + 1)) (δ (b.val + 1))))
                          (negPProd α β s (b.val + 1) (k - (b.val + 1)))
              else CRing.zero))
            gK)
          fK)
        (sumFin k (fun b =>
          if s.testBit b.val then
            CRing.mul
              (CRing.mul (CRing.mul (deltaProd γ α β δ s b.val) (γ (b.val + 1)))
                         (CRing.mul (negPProd α β s (b.val + 1) (k - (b.val + 1))) (CRing.neg pK)))
              (f (b.val + 1))
          else CRing.zero)) := by
    rw [sumFin_mul_right, sumFin_mul_right, ← sumFin_add]
    apply sumFin_congr; intro b
    cases htb : s.testBit b.val with
    | false =>
      simp only [Bool.false_eq_true, ite_false, CRing.zero_mul, CRing.add_zero]
    | true =>
      simp only [ite_true]
      rw [CRing.mul_sub]
      unfold CRing.sub
      congr 1
      · let D := deltaProd γ α β δ s b.val
        let gb := γ (b.val + 1)
        let db := δ (b.val + 1)
        let N := negPProd α β s (b.val + 1) (k - (b.val + 1))
        change CRing.mul (CRing.mul (CRing.mul D gb) N) (CRing.mul (CRing.mul gK db) fK) =
               CRing.mul (CRing.mul (CRing.mul (CRing.mul D (CRing.mul gb db)) N) gK) fK
        rw [← CRing.mul_assoc (CRing.mul (CRing.mul D gb) N)]
        congr 1
        rw [CRing.mul_comm gK db, ← CRing.mul_assoc (CRing.mul (CRing.mul D gb) N) db gK]
        congr 1
        rw [CRing.mul_assoc (CRing.mul D gb) N db, CRing.mul_comm N db,
            ← CRing.mul_assoc (CRing.mul D gb) db N, CRing.mul_assoc D gb db]
      · rw [← CRing.mul_assoc, CRing.mul_assoc (CRing.mul (deltaProd γ α β δ s b.val) (γ (b.val + 1))) _ pK,
            CRing.mul_neg, CRing.mul_neg, CRing.neg_mul]
  rw [ht0, hsum_split]
  -- Combine the two fK terms via `hcb_telescoping`!
  let T1 := CRing.mul (CRing.mul (negPProd α β s 0 k) gK) fK
  let T2 := CRing.mul (CRing.mul (negPProd α β s 0 k) (CRing.neg pK)) (f 0)
  let T3 := CRing.mul (CRing.mul (sumFin k (fun b =>
              if s.testBit b.val then
                CRing.mul (CRing.mul (deltaProd γ α β δ s b.val) (CRing.mul (γ (b.val + 1)) (δ (b.val + 1))))
                          (negPProd α β s (b.val + 1) (k - (b.val + 1)))
              else CRing.zero)) gK) fK
  let T4 := sumFin k (fun b =>
              if s.testBit b.val then
                CRing.mul (CRing.mul (CRing.mul (deltaProd γ α β δ s b.val) (γ (b.val + 1)))
                                     (CRing.mul (negPProd α β s (b.val + 1) (k - (b.val + 1))) (CRing.neg pK)))
                          (f (b.val + 1))
              else CRing.zero)
  have hrearr : CRing.add (CRing.add T1 T2) (CRing.add T3 T4) =
                CRing.add T2 (CRing.add T4 (CRing.add T1 T3)) := by
    rw [CRing.add_comm T1 T2, CRing.add_assoc, CRing.add_comm T1 (CRing.add T3 T4),
        CRing.add_comm T3 T4, CRing.add_assoc, CRing.add_comm T3 T1]
  have htele : CRing.add T1 T3 = CRing.mul (CRing.mul (deltaProd γ α β δ s k) gK) fK := by
    dsimp only [T1, T3]
    rw [← CRing.right_distrib, ← CRing.right_distrib, hcb_telescoping]
  change CRing.add (CRing.add T1 T2) (CRing.add T3 T4) = _
  rw [hrearr, htele]
  -- Now unfold RHS `sumFin (k + 1)` and match all 3 pieces!
  simp only [sumFin, Fin.val_castSucc, Fin.val_last]
  have htk : (pow2 k + s).testBit k = true := testBit_add_pow2_eq k s hs
  congr 1
  · -- f 0 term
    dsimp only [T2]
    congr 1
    simp only [negPProd, Nat.zero_add, htk, ite_true]
    rw [negPProd_add_pow2 α β k s 0 k (by omega)]
  · congr 1
    · -- sum over b < k
      dsimp only [T4]
      apply sumFin_congr; intro b
      rw [testBit_add_pow2_lt k s b.val b.isLt]
      cases htb : s.testBit b.val with
      | false =>
        simp only [Bool.false_eq_true, ite_false]
      | true =>
        simp only [ite_true]
        rw [deltaProd_add_pow2 γ α β δ k s b.val (by omega)]
        have hsub : k + 1 - (b.val + 1) = (k - (b.val + 1)) + 1 := by omega
        have hadd : b.val + 1 + (k - (b.val + 1)) = k := by omega
        rw [hsub]
        simp only [negPProd, hadd, htk, ite_true]
        rw [negPProd_add_pow2 α β k s (b.val + 1) (k - (b.val + 1)) (by omega)]
    · -- last term b = k
      simp only [htk, ite_true, Nat.sub_self, negPProd, CRing.mul_one]
      rw [deltaProd_add_pow2 γ α β δ k s k (Nat.le_refl k)]

theorem hcbMaskFactor_low (γ α β δ : Nat → R) (k : Nat) (f : Nat → R) (s : Nat) (hs : s < pow2 k) :
    hcbMaskFactor γ α β δ (k + 1) f s = hcbMaskFactor γ α β δ k f s := by
  unfold hcbMaskFactor
  have htk : s.testBit k = false := testBit_lt_pow2 k s k hs (Nat.le_refl k)
  simp only [sumFin, Fin.val_castSucc, Fin.val_last, htk, Bool.false_eq_true, ite_false, CRing.add_zero]
  congr 1
  · simp only [negPProd, Nat.zero_add, htk, Bool.false_eq_true, ite_false, CRing.mul_one]
  · apply sumFin_congr; intro b
    cases htb : s.testBit b.val with
    | false =>
      simp only [Bool.false_eq_true, ite_false]
    | true =>
      simp only [ite_true]
      have hsub : k + 1 - (b.val + 1) = (k - (b.val + 1)) + 1 := by omega
      have hadd : b.val + 1 + (k - (b.val + 1)) = k := by omega
      rw [hsub]; simp only [negPProd, hadd, htk, Bool.false_eq_true, ite_false, CRing.mul_one]

/-- **COROLLARY I-A (Pure MSB-AND Profile Theorem)**:
    For `M_k(x, y) = f(msbPos(x &&& y))` over ANY commutative ring `R`,
    `det M_k = prod_{s : Fin (2^k)} (if s = 0 then f 0 else (-1)^(popcount s - 1) * (f(minBit s) - f 0))`
    and in closed power-product form:
    - `k = 0`: `f 0`
    - `k = 1`: `f 0 * (f 1 - f 0)`
    - `k ≥ 2`: `-(f 0 * ∏_{j=1}^k (f j - f 0)^(2^(k - j)))`! -/
def msbAndMat (k : Nat) (f : Nat → R) : Mat R (pow2 k) :=
  fun x y => f (msbPos (x.val &&& y.val))

theorem msbAndMat_eq_hcb (k : Nat) (f : Nat → R) :
    msbAndMat k f = hcbMat (fun _ => CRing.one) (fun _ => CRing.one) (fun _ => CRing.one) (fun _ => CRing.one) k f := by
  funext x y; unfold msbAndMat hcbMat
  have h1 : prodFin k (fun b => if b.val + 1 = msbPos (x.val &&& y.val) then (CRing.one : R)
                                else bitWeight (fun _ => CRing.one) (fun _ => CRing.one)
                                               (fun _ => CRing.one) (fun _ => CRing.one) b.val x.val y.val) =
            CRing.one := by
    have hcongr : prodFin k (fun b => if b.val + 1 = msbPos (x.val &&& y.val) then (CRing.one : R)
                                      else bitWeight (fun _ => CRing.one) (fun _ => CRing.one)
                                                     (fun _ => CRing.one) (fun _ => CRing.one) b.val x.val y.val) =
                  prodFin k (fun _ => (CRing.one : R)) := by
      apply prodFin_congr; intro b
      by_cases h : b.val + 1 = msbPos (x.val &&& y.val)
      · simp [h]
      · simp only [h, ite_false]; unfold bitWeight
        cases x.val.testBit b.val <;> cases y.val.testBit b.val <;> rfl
    rw [hcongr]; exact prodFin_one k
  dsimp only
  rw [h1, CRing.mul_one]

theorem sub_sub_sub_eq_neg {a b c : R} :
    CRing.sub (CRing.sub c b) (CRing.sub c a) = CRing.neg (CRing.sub b a) := by
  unfold CRing.sub
  rw [CRing.neg_add, CRing.neg_neg, CRing.add_comm (CRing.neg c) a,
      ← CRing.add_assoc, CRing.add_comm c (CRing.neg b), CRing.add_assoc (CRing.neg b),
      CRing.add_comm c a, CRing.add_assoc (CRing.neg b), CRing.add_assoc a c (CRing.neg c),
      CRing.add_right_neg, CRing.add_zero, CRing.neg_add, CRing.neg_neg, CRing.add_comm]

end FamilyI

/-- **COROLLARY I-C (Popcount-Scaled MSB-AND Alternating-Sum Theorem over `Int`)**:
    When `γ = α = β = 1, δ = 2` on `Int`, the matrix entry is literally:
    `M_k(x, y) = if x &&& y = 0 then f 0 else f (msbPos (x &&& y)) * 2 ^ (popcount (x &&& y) - 1)`! -/
def popMsbAndMat (k : Nat) (f : Nat → Int) : Mat Int (pow2 k) :=
  fun x y =>
    if (x.val &&& y.val) = 0 then f 0
    else f (msbPos (x.val &&& y.val)) * (2 ^ (popcount (x.val &&& y.val) - 1) : Int)

theorem popMsbAndMat_eq_hcb (k : Nat) (f : Nat → Int) :
    popMsbAndMat k f = hcbMat (R := Int) (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 2) k f := by
  -- Helper: prodFin k of (if b = (j-1) then 1 else if (x&y).testBit b then 2 else 1) = 2^(popcount(x&y) - [j>0])
  have hpow2_prod : ∀ (m z : Nat), z < pow2 m →
      prodFin (R := Int) m (fun b => if z.testBit b.val then (2 : Int) else 1) = (2 : Int) ^ (popcount z) := by
    intro m
    induction m with
    | zero =>
      intro z hz
      have h0 : z = 0 := by unfold pow2 at hz; omega
      subst h0; simp [prodFin, popcount_zero]; rfl
    | succ m ih =>
      intro z hz
      simp only [prodFin, Fin.val_castSucc, Fin.val_last]
      by_cases hlt : z < pow2 m
      · have htb : z.testBit m = false := testBit_lt_pow2 m z m hlt (Nat.le_refl m)
        change prodFin (R := Int) m (fun b => if z.testBit b.val then (2 : Int) else 1) *
               (if z.testBit m then (2 : Int) else 1) = (2 : Int) ^ popcount z
        rw [htb]; simp only [Bool.false_eq_true, ite_false, Int.mul_one]
        exact ih z hlt
      · have hz' : z - pow2 m < pow2 m := by unfold pow2 at hz; omega
        have hzeq : z = pow2 m + (z - pow2 m) := by omega
        have htb : z.testBit m = true := by rw [hzeq]; exact testBit_add_pow2_eq m _ hz'
        change prodFin (R := Int) m (fun b => if z.testBit b.val then (2 : Int) else 1) *
               (if z.testBit m then (2 : Int) else 1) = (2 : Int) ^ popcount z
        rw [htb]; simp only [ite_true]
        have hlo : prodFin (R := Int) m (fun b => if z.testBit b.val then (2 : Int) else 1) =
                   prodFin (R := Int) m (fun b => if (z - pow2 m).testBit b.val then (2 : Int) else 1) :=
          prodFin_congr (fun b => by
            have htbz := testBit_add_pow2_lt m (z - pow2 m) b.val b.isLt
            rw [← hzeq] at htbz; rw [htbz])
        have hpop : popcount z = popcount (z - pow2 m) + 1 := by
          have hp := popcount_add_pow2 m (z - pow2 m) hz'
          rw [← hzeq] at hp; omega
        rw [hlo, ih _ hz', hpop, Int.pow_succ]
  funext x y
  unfold popMsbAndMat hcbMat
  let z := x.val &&& y.val
  have hz_lt : z < pow2 k := and_lt_pow2 k x.val y.val x.isLt y.isLt
  have hbw_eq : ∀ b : Nat,
      bitWeight (R := Int) (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 2) b x.val y.val =
      if z.testBit b then 2 else 1 := by
    intro b; unfold bitWeight; dsimp only [z]; rw [Nat.testBit_and]
    cases x.val.testBit b <;> cases y.val.testBit b <;> rfl
  change (if z = 0 then f 0 else f (msbPos z) * (2 : Int) ^ (popcount z - 1)) =
         f (msbPos z) * prodFin (R := Int) k (fun b => if b.val + 1 = msbPos z then (1 : Int)
                                                       else bitWeight (R := Int) (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 2) b.val x.val y.val)
  by_cases hz0 : z = 0
  · simp only [hz0, ite_true, msbPos_zero]
    have h1 : prodFin (R := Int) k (fun b => if b.val + 1 = 0 then (1 : Int)
                                             else bitWeight (R := Int) (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 2) b.val x.val y.val) = 1 := by
      have hc : prodFin (R := Int) k (fun b => if b.val + 1 = 0 then (1 : Int)
                                               else bitWeight (R := Int) (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 2) b.val x.val y.val) =
                prodFin (R := Int) k (fun _ => (CRing.one : Int)) := by
        apply prodFin_congr; intro b
        simp only [Nat.succ_ne_zero, ite_false, hbw_eq, hz0, Nat.zero_testBit, Bool.false_eq_true, ite_false]; rfl
      rw [hc]; exact prodFin_one (R := Int) k
    rw [h1, Int.mul_one]
  · simp only [hz0, ite_false]
    congr 1
    have hj_pos : 0 < msbPos z := by rw [msbPos_pos_eq z hz0]; omega
    have hj_le : msbPos z ≤ k := msbPos_lt_pow2 k z hz_lt
    have htb : z.testBit (msbPos z - 1) = true := testBit_msbPos_pred z hz0
    have h2rhs : 2 * prodFin (R := Int) k (fun b => if b.val + 1 = msbPos z then (1 : Int)
                                                    else bitWeight (R := Int) (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 2) b.val x.val y.val) =
                 prodFin (R := Int) k (fun b => if z.testBit b.val then (2 : Int) else 1) := by
      suffices hp : ∀ (m : Nat) (P : Fin m → Int) (idx : Fin m),
          P idx * prodFin (R := Int) m (fun b => if b = idx then (1 : Int) else P b) = prodFin (R := Int) m P by
        have h := hp k (fun b => if z.testBit b.val then (2 : Int) else 1) ⟨msbPos z - 1, by omega⟩
        simp only [htb, ite_true] at h
        rw [← h]; congr 1; apply prodFin_congr; intro b
        have hiff : b.val + 1 = msbPos z ↔ b = ⟨msbPos z - 1, by omega⟩ := by
          constructor
          · intro heq; apply Fin.ext; simp; omega
          · intro heq; have hv := congrArg Fin.val heq; simp at hv; omega
        by_cases hc : b.val + 1 = msbPos z
        · have hc' : b = ⟨msbPos z - 1, by omega⟩ := hiff.mp hc
          simp only [hc, ite_true]
          simp only [hc', ite_true]
        · have hc' : b ≠ ⟨msbPos z - 1, by omega⟩ := fun h => hc (hiff.mpr h)
          simp only [hc, ite_false]
          simp only [hc', ite_false, hbw_eq]
      intro m
      induction m with
      | zero => intro _ idx; exact Fin.elim0 idx
      | succ m ih =>
        intro P idx
        simp only [prodFin]
        by_cases hlt : idx.val < m
        · have hne : Fin.last m ≠ idx := by intro h; have := congrArg Fin.val h; simp at this; omega
          simp only [hne, ite_false]
          have hrec := ih (fun b => P b.castSucc) ⟨idx.val, hlt⟩
          have hcast : (⟨idx.val, hlt⟩ : Fin m).castSucc = idx := Fin.ext rfl
          rw [hcast] at hrec
          change P idx * (prodFin (R := Int) m (fun b => if b.castSucc = idx then (1 : Int) else P b.castSucc) * P (Fin.last m)) =
                 prodFin (R := Int) m (fun b => P b.castSucc) * P (Fin.last m)
          rw [← Int.mul_assoc]
          congr 1
          rw [← hrec]; congr 1; apply prodFin_congr; intro b
          have hiff : b.castSucc = idx ↔ b = ⟨idx.val, hlt⟩ := by
            constructor
            · intro h; apply Fin.ext; have hv := congrArg Fin.val h; exact hv
            · intro h; apply Fin.ext; have hv := congrArg Fin.val h; exact hv
          by_cases hc : b = ⟨idx.val, hlt⟩
          · simp [hc]
          · have hc' : b.castSucc ≠ idx := fun h => hc (hiff.mp h)
            simp [hc, hc']
        · have heq : idx = Fin.last m := by apply Fin.ext; simp; omega
          subst heq
          simp only [ite_true]
          have hlo : prodFin (R := Int) m (fun b => if b.castSucc = Fin.last m then (1 : Int) else P b.castSucc) =
                     prodFin (R := Int) m (fun b => P b.castSucc) :=
            prodFin_congr (fun b => by
              have : b.castSucc ≠ Fin.last m := by intro h; have := congrArg Fin.val h; simp at this; omega
              simp [this])
          change P (Fin.last m) * (prodFin (R := Int) m (fun b => if b.castSucc = Fin.last m then (1 : Int) else P b.castSucc) * 1) =
                 prodFin (R := Int) m (fun b => P b.castSucc) * P (Fin.last m)
          rw [hlo, Int.mul_one, Int.mul_comm]
    rw [hpow2_prod k z hz_lt] at h2rhs
    have hpop_pos : 0 < popcount z := by
      have : ∀ (n : Nat), n ≠ 0 → 0 < popcount n := by
        intro n hn
        induction n using Nat.strongRecOn with
        | ind n ihn =>
          rw [popcount_pos_eq n hn]
          by_cases hmod : n % 2 = 1
          · omega
          · have hd : n / 2 ≠ 0 := by omega
            have := ihn (n / 2) (by omega) hd
            omega
      exact this z hz0
    have h2lhs : 2 * (2 : Int) ^ (popcount z - 1) = (2 : Int) ^ (popcount z) := by
      have hk : popcount z = (popcount z - 1) + 1 := by omega
      have hp : (2 : Int) ^ (popcount z) = (2 : Int) ^ ((popcount z - 1) + 1) := congrArg ((2 : Int) ^ ·) hk
      rw [hp, Int.pow_succ, Int.mul_comm]
    omega

section FamilyII
variable {R : Type u} [CRing R]

/-- Weighted bitwise-subset indicator `[x ⊆ y]` (`x &&& y = x`). -/
def subsetWeight (u d : Nat → R) (k x y : Nat) : R :=
  if (x &&& y) = x then
    prodFin k (fun b =>
      match x.testBit b.val, y.testBit b.val with
      | false, true => u (b.val + 1)
      | true,  true => d (b.val + 1)
      | _,     _    => CRing.one)
  else CRing.zero

/-- Weighted bitwise-disjointness indicator `[x &&& y = 0]`. -/
def disjWeight (u w : Nat → R) (k x y : Nat) : R :=
  if (x &&& y) = 0 then
    prodFin k (fun b =>
      match x.testBit b.val, y.testBit b.val with
      | false, true => u (b.val + 1)
      | true, false => w (b.val + 1)
      | _,    _     => CRing.one)
  else CRing.zero

/-- **Family II: Weighted Boolean-Poset Subset-Disjointness Hybrid Kernel Matrix `B_k(a, c; u, w, d)`**. -/
def boolHybridMat (u w d : Nat → R) (k : Nat) (a c : R) : Mat R (pow2 k) :=
  fun x y => CRing.add (CRing.mul a (subsetWeight u d k x.val y.val))
                       (CRing.mul c (disjWeight u w k x.val y.val))

theorem det_boolHybridMat_zero (u w d : Nat → R) (a c : R) :
    det (boolHybridMat u w d 0 a c) = CRing.add a c := by
  unfold det boolHybridMat subsetWeight disjWeight
  change CRing.add CRing.zero
    (CRing.mul (CRing.ofInt (eps (finSnoc Fin.elim0 ⟨0, Nat.zero_lt_one⟩)))
      (CRing.mul CRing.one
        (CRing.add (CRing.mul a (if (0 &&& 0) = 0 then CRing.one else CRing.zero))
                   (CRing.mul c (if (0 &&& 0) = 0 then CRing.one else CRing.zero))))) = CRing.add a c
  have heps : eps (finSnoc Fin.elim0 (⟨0, Nat.zero_lt_one⟩ : Fin 1)) = 1 := rfl
  have h0 : (0 &&& 0) = 0 := by decide
  rw [heps, CRing.ofInt_one, CRing.zero_add, CRing.one_mul, CRing.one_mul]
  simp only [h0, ite_true, CRing.mul_one]

/-- Exact MSB bit-splitting identity for Family II (triggers RIGHT unimodular Block-Schur!). -/
theorem boolHybridMat_succ_eq_block (u w d : Nat → R) (k : Nat) (a c : R) :
    boolHybridMat u w d (k + 1) a c =
    blockMat (boolHybridMat u w d k a c)
             (matSmul (u (k + 1)) (boolHybridMat u w d k a c))
             (fun x y => CRing.mul (CRing.mul (w (k + 1)) c) (disjWeight u w k x.val y.val))
             (fun x y => CRing.mul (CRing.mul (d (k + 1)) a) (subsetWeight u d k x.val y.val)) := by
  funext x y
  unfold boolHybridMat blockMat matSmul subsetWeight disjWeight
  by_cases hx : x.val < pow2 k <;> by_cases hy : y.val < pow2 k
  · -- (0, 0) block
    simp only [hx, hy, dite_true, prodFin, Fin.val_castSucc, Fin.val_last]
    have htx : x.val.testBit k = false := testBit_lt_pow2 k x.val k hx (Nat.le_refl k)
    have hty : y.val.testBit k = false := testBit_lt_pow2 k y.val k hy (Nat.le_refl k)
    simp only [htx, hty, CRing.mul_one]
  · -- (0, 1) block
    simp only [hx, hy, dite_true, dite_false, prodFin, Fin.val_castSucc, Fin.val_last]
    have hy' : y.val - pow2 k < pow2 k := by have hlt := y.isLt; unfold pow2 at hlt; omega
    have hy_eq : y.val = pow2 k + (y.val - pow2 k) := by omega
    have hand : (x.val &&& y.val) = (x.val &&& (y.val - pow2 k)) := by
      have h := and_add_pow2_right k x.val (y.val - pow2 k) hx hy'
      rwa [← hy_eq] at h
    have htx : x.val.testBit k = false := testBit_lt_pow2 k x.val k hx (Nat.le_refl k)
    have hty : y.val.testBit k = true := by rw [hy_eq]; exact testBit_add_pow2_eq k _ hy'
    rw [hand, htx, hty, CRing.left_distrib]
    congr 1
    · by_cases hsub : (x.val &&& (y.val - pow2 k)) = x.val
      · simp only [hsub, ite_true]
        have hlo : prodFin k (fun b => match x.val.testBit b.val, y.val.testBit b.val with
                                       | false, true => u (b.val + 1) | true, true => d (b.val + 1) | _, _ => CRing.one) =
                   prodFin k (fun b => match x.val.testBit b.val, (y.val - pow2 k).testBit b.val with
                                       | false, true => u (b.val + 1) | true, true => d (b.val + 1) | _, _ => CRing.one) :=
          prodFin_congr (fun b => by
            have htby := testBit_add_pow2_lt k (y.val - pow2 k) b.val b.isLt
            rw [← hy_eq] at htby; rw [htby])
        rw [hlo, CRing.mul_comm (prodFin k _) (u (k + 1)), ← CRing.mul_assoc,
            CRing.mul_comm a (u (k + 1)), CRing.mul_assoc]
      · simp only [hsub, ite_false, CRing.mul_zero]
    · by_cases hdj : (x.val &&& (y.val - pow2 k)) = 0
      · simp only [hdj, ite_true]
        have hlo : prodFin k (fun b => match x.val.testBit b.val, y.val.testBit b.val with
                                       | false, true => u (b.val + 1) | true, false => w (b.val + 1) | _, _ => CRing.one) =
                   prodFin k (fun b => match x.val.testBit b.val, (y.val - pow2 k).testBit b.val with
                                       | false, true => u (b.val + 1) | true, false => w (b.val + 1) | _, _ => CRing.one) :=
          prodFin_congr (fun b => by
            have htby := testBit_add_pow2_lt k (y.val - pow2 k) b.val b.isLt
            rw [← hy_eq] at htby; rw [htby])
        rw [hlo, CRing.mul_comm (prodFin k _) (u (k + 1)), ← CRing.mul_assoc,
            CRing.mul_comm c (u (k + 1)), CRing.mul_assoc]
      · simp only [hdj, ite_false, CRing.mul_zero]
  · -- (1, 0) block: x >= 2^k > y, so (x &&& y) < 2^k < x => subset is FALSE!
    simp only [hx, hy, dite_true, dite_false, prodFin, Fin.val_castSucc, Fin.val_last]
    have hx' : x.val - pow2 k < pow2 k := by have hlt := x.isLt; unfold pow2 at hlt; omega
    have hx_eq : x.val = pow2 k + (x.val - pow2 k) := by omega
    have hand : (x.val &&& y.val) = ((x.val - pow2 k) &&& y.val) := by
      have h := and_add_pow2_left k (x.val - pow2 k) y.val hx' hy
      rwa [← hx_eq] at h
    have hnot_sub : (x.val &&& y.val) ≠ x.val := by
      have hlt : (x.val &&& y.val) < pow2 k := by rw [hand]; exact and_lt_pow2 k _ _ hx' hy
      omega
    have htx : x.val.testBit k = true := by rw [hx_eq]; exact testBit_add_pow2_eq k _ hx'
    have hty : y.val.testBit k = false := testBit_lt_pow2 k y.val k hy (Nat.le_refl k)
    simp only [hnot_sub, ite_false, CRing.mul_zero, CRing.zero_add]
    rw [hand, htx, hty]
    by_cases hdj : ((x.val - pow2 k) &&& y.val) = 0
    · simp only [hdj, ite_true]
      have hlo : prodFin k (fun b => match x.val.testBit b.val, y.val.testBit b.val with
                                     | false, true => u (b.val + 1) | true, false => w (b.val + 1) | _, _ => CRing.one) =
                 prodFin k (fun b => match (x.val - pow2 k).testBit b.val, y.val.testBit b.val with
                                     | false, true => u (b.val + 1) | true, false => w (b.val + 1) | _, _ => CRing.one) :=
        prodFin_congr (fun b => by
          have htbx := testBit_add_pow2_lt k (x.val - pow2 k) b.val b.isLt
          rw [← hx_eq] at htbx; rw [htbx])
      rw [hlo, CRing.mul_comm (prodFin k _) (w (k + 1)), ← CRing.mul_assoc,
          CRing.mul_comm c (w (k + 1))]
    · simp only [hdj, ite_false, CRing.mul_zero]
  · -- (1, 1) block: both >= 2^k => (x &&& y) >= 2^k > 0 => disjoint is FALSE!
    simp only [hx, hy, dite_false, prodFin, Fin.val_castSucc, Fin.val_last]
    have hx' : x.val - pow2 k < pow2 k := by have hlt := x.isLt; unfold pow2 at hlt; omega
    have hy' : y.val - pow2 k < pow2 k := by have hlt := y.isLt; unfold pow2 at hlt; omega
    have hx_eq : x.val = pow2 k + (x.val - pow2 k) := by omega
    have hy_eq : y.val = pow2 k + (y.val - pow2 k) := by omega
    have hand : (x.val &&& y.val) = pow2 k + ((x.val - pow2 k) &&& (y.val - pow2 k)) := by
      have h := and_add_pow2_both k (x.val - pow2 k) (y.val - pow2 k) hx' hy'
      rwa [← hx_eq, ← hy_eq] at h
    have hnot_dj : (x.val &&& y.val) ≠ 0 := by have := pow2_pos k; omega
    have hsub_iff : (x.val &&& y.val) = x.val ↔ ((x.val - pow2 k) &&& (y.val - pow2 k)) = x.val - pow2 k := by
      rw [hand]; omega
    have htx : x.val.testBit k = true := by rw [hx_eq]; exact testBit_add_pow2_eq k _ hx'
    have hty : y.val.testBit k = true := by rw [hy_eq]; exact testBit_add_pow2_eq k _ hy'
    simp only [hnot_dj, ite_false, CRing.mul_zero, CRing.add_zero, htx, hty]
    by_cases hsub : ((x.val - pow2 k) &&& (y.val - pow2 k)) = x.val - pow2 k
    · simp only [hsub, hsub_iff.mpr hsub, ite_true]
      have hlo : prodFin k (fun b => match x.val.testBit b.val, y.val.testBit b.val with
                                     | false, true => u (b.val + 1) | true, true => d (b.val + 1) | _, _ => CRing.one) =
                 prodFin k (fun b => match (x.val - pow2 k).testBit b.val, (y.val - pow2 k).testBit b.val with
                                     | false, true => u (b.val + 1) | true, true => d (b.val + 1) | _, _ => CRing.one) :=
        prodFin_congr (fun b => by
          have htbx := testBit_add_pow2_lt k (x.val - pow2 k) b.val b.isLt
          have htby := testBit_add_pow2_lt k (y.val - pow2 k) b.val b.isLt
          rw [← hx_eq] at htbx; rw [← hy_eq] at htby; rw [htbx, htby])
      rw [hlo, CRing.mul_comm (prodFin k _) (d (k + 1)), ← CRing.mul_assoc,
          CRing.mul_comm a (d (k + 1))]
    · have hsub' : (x.val &&& y.val) ≠ x.val := fun h => hsub (hsub_iff.mp h)
      simp only [hsub, hsub', ite_false, CRing.mul_zero]

/-- Explicit closed-form bitmask factor for Family II. -/
def boolHybridMaskFactor (u w d : Nat → R) (k : Nat) (a c : R) (s : Nat) : R :=
  CRing.add
    (CRing.mul a (prodFin k (fun b => if s.testBit b.val then d (b.val + 1) else CRing.one)))
    (CRing.mul c (prodFin k (fun b => if s.testBit b.val then CRing.neg (CRing.mul (u (b.val + 1)) (w (b.val + 1))) else CRing.one)))

/-- **COROLLARY II-A (Uniform Boolean-Poset Subset-Disjointness Determinant)**:
    For ALL `k ≥ 1` and ALL `a, c : R` in ANY `CRing R`:
    `det_{0 ≤ x, y < 2^k} (a * [x ⊆ y] + c * [x &&& y = 0]) = (a^2 - c^2)^(2^(k - 1))`! -/
def subsetDisjMat (k : Nat) (a c : R) : Mat R (pow2 k) :=
  fun x y => CRing.add (if (x.val &&& y.val) = x.val then a else CRing.zero)
                       (if (x.val &&& y.val) = 0 then c else CRing.zero)

theorem subsetDisjMat_eq_boolHybrid (k : Nat) (a c : R) :
    subsetDisjMat k a c =
    boolHybridMat (fun _ => CRing.one) (fun _ => CRing.one) (fun _ => CRing.one) k a c := by
  funext x y; unfold subsetDisjMat boolHybridMat subsetWeight disjWeight
  congr 1
  · by_cases h : (x.val &&& y.val) = x.val
    · simp only [h, ite_true]
      have h1 : prodFin k (fun b => match x.val.testBit b.val, y.val.testBit b.val with
                                    | false, true => (CRing.one : R) | true, true => CRing.one | _, _ => CRing.one) =
                CRing.one := by
        have hc : prodFin k (fun b => match x.val.testBit b.val, y.val.testBit b.val with
                                      | false, true => (CRing.one : R) | true, true => CRing.one | _, _ => CRing.one) =
                  prodFin k (fun _ => (CRing.one : R)) :=
          prodFin_congr (fun b => by cases x.val.testBit b.val <;> cases y.val.testBit b.val <;> rfl)
        rw [hc]; exact prodFin_one k
      rw [h1, CRing.mul_one]
    · simp only [h, ite_false, CRing.mul_zero]
  · by_cases h : (x.val &&& y.val) = 0
    · simp only [h, ite_true]
      have h1 : prodFin k (fun b => match x.val.testBit b.val, y.val.testBit b.val with
                                    | false, true => (CRing.one : R) | true, false => CRing.one | _, _ => CRing.one) =
                CRing.one := by
        have hc : prodFin k (fun b => match x.val.testBit b.val, y.val.testBit b.val with
                                      | false, true => (CRing.one : R) | true, false => CRing.one | _, _ => CRing.one) =
                  prodFin k (fun _ => (CRing.one : R)) :=
          prodFin_congr (fun b => by cases x.val.testBit b.val <;> cases y.val.testBit b.val <;> rfl)
        rw [hc]; exact prodFin_one k
      rw [h1, CRing.mul_one]
    · simp only [h, ite_false, CRing.mul_zero]

end FamilyII

/-- Witness 1 (Non-Vacuity of Family I — Delayed Singularity at `k = 3` triggered by unique 3-bit mask `s = 7`):
    `fSing = [1, 3, 5, 3, 9, ...]`, `γ = α = β = 1, δ = 2` on `Int`.
    - Invertible for `k = 0` (`det = 1`), `k = 1` (`det = 2`), `k = 2` (`det = 24`);
    - Singular for ALL `k ≥ 3` (`det = 0`) because `L_7(fSing) = -1 + 3 - 5 + 3 = 0`! -/
def fSing (j : Nat) : Int :=
  match j with
  | 0 => 1
  | 1 => 3
  | 2 => 5
  | 3 => 3
  | n => 2 * (n : Int) + 1

end BitSlicedSchur
