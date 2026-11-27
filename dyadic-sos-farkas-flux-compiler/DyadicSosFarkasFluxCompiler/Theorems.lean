/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DyadicSosFarkasFluxCompiler.Defs

/-!
# Exact Z[1/2] Dyadic Sum-of-Squares, Schmüdgen-Farkas Positivstellensatz,
# and Telescoping-Flux Infinite-Dimensional Proof Compiler (Task 5 / certcomp-5)

Standalone Lean 4.34.1 — zero Mathlib, zero Lake, zero `sorry`, zero `native_decide`,
zero custom axioms. Every certificate is pure data checked inside the kernel by `decide`.

## Architecture
1. Exact dyadic rationals `Dyadic` = Z[1/2] (`mant / 2^exp`) with congruence `Equiv` and order `Nonneg`.
2. Dimension-polymorphic canonical sparse multivariate polynomials `DyadicPoly` over Z[1/2].
3. Pure-data `DyadicGram` + `checkGramPSD` verifying exact binary LDL^T factorizations
   `2^scale * G = L^T * diag(d) * L` (`d_k ≥ 0`, `G` symmetric), lifted by `gram_psd_sound`.
4. Pure-data `FarkasSOSCert` + `checkFarkasSOS` / `checkFarkasRefutation` implementing the full
   exact dyadic Schmüdgen-Farkas Positivstellensatz (`farkas_sos_sound`, `farkas_refutation_sound`).
5. Infinite-dimensional lifters `CyclicFluxCert` (`cyclic_flux_sound`, `cyclic_flux_sound_int`,
   `binary_cyclic_sound`) and `OpenFluxCert` (`open_flux_sound`) lifting finite local certificates
   to `∀ n ≥ 1` and universal global parameters `∀ t ∈ Z[1/2]`.
6. Six flagship theorems (two non-convex infinite-dimensional quartic cyclic inequalities,
   two sharp continuous-hypercube [0,1]^n 3-pattern density theorems, a sharp Boolean {0,1}^n
   frustrated-triangle theorem with proved continuous-vs-binary integrality gap, doubly-infinite
   parametric + open-boundary discrete biharmonic-Sobolev theorems, and a nonlinear Positivstellensatz
   refutation), plus non-vacuity witnesses, sharpness counterexamples, and 10 adversarial mutation tests.
-/


-- ============================================================================
-- Section 1: Exact Dyadic Rationals Z[1/2]
-- ============================================================================

namespace DyadicSOS

namespace Dyadic

def pow2Neg (k : Nat) : Dyadic := ⟨1, k⟩

instance : Zero Dyadic := ⟨zero⟩

instance : One Dyadic := ⟨one⟩

instance : Add Dyadic := ⟨add⟩

instance : Neg Dyadic := ⟨neg⟩

instance : Sub Dyadic := ⟨sub⟩

instance : Mul Dyadic := ⟨mul⟩

instance : HPow Dyadic Nat Dyadic := ⟨pow⟩

/-- Exact mathematical equality in `Z[1/2]`. -/
def Equiv (a b : Dyadic) : Prop :=
  a.mant * ((2 : Int) ^ b.exp) = b.mant * ((2 : Int) ^ a.exp)

infix:50 " ≈ " => Equiv

theorem pow2_pos (n : Nat) : (0 : Int) < (2 : Int) ^ n := by
  induction n with
  | zero => decide
  | succ k ih =>
    rw [Int.pow_succ]
    omega

theorem pow2Int_eq (k : Nat) : pow2Int k = (2 : Int) ^ k := by
  unfold pow2Int
  induction k with
  | zero => rfl
  | succ j ih =>
    rw [Nat.pow_succ, Int.ofNat_eq_natCast, Int.natCast_mul, ← Int.ofNat_eq_natCast, ih, Int.pow_succ]
    rfl

theorem pow2_ne_zero (n : Nat) : ((2 : Int) ^ n) ≠ 0 := by
  have h := pow2_pos n
  omega

theorem int_mul_cancel_right {a b c : Int} (hc : c ≠ 0) (h : a * c = b * c) : a = b :=
  Int.eq_of_mul_eq_mul_right hc h

theorem nonneg_of_mul_pos {a c : Int} (hc : 0 < c) (h : 0 ≤ a * c) : 0 ≤ a := by
  by_cases ha : 0 ≤ a
  · exact ha
  · have hlt : a < 0 := by omega
    have hneg : a * c < 0 := Int.mul_neg_of_neg_of_pos hlt hc
    omega

-- Equivalence relation

theorem equiv_refl (a : Dyadic) : a ≈ a := rfl

theorem equiv_symm {a b : Dyadic} (h : a ≈ b) : b ≈ a := h.symm

theorem equiv_trans {a b c : Dyadic} (hab : a ≈ b) (hbc : b ≈ c) : a ≈ c := by
  unfold Equiv at *
  have h1 : a.mant * (2 : Int) ^ c.exp * (2 : Int) ^ b.exp =
            c.mant * (2 : Int) ^ a.exp * (2 : Int) ^ b.exp := by
    calc a.mant * (2 : Int) ^ c.exp * (2 : Int) ^ b.exp
        = (a.mant * (2 : Int) ^ b.exp) * (2 : Int) ^ c.exp := by
            rw [Int.mul_assoc, Int.mul_comm ((2 : Int) ^ c.exp), ← Int.mul_assoc]
      _ = (b.mant * (2 : Int) ^ a.exp) * (2 : Int) ^ c.exp := by rw [hab]
      _ = (b.mant * (2 : Int) ^ c.exp) * (2 : Int) ^ a.exp := by
            rw [Int.mul_assoc, Int.mul_comm ((2 : Int) ^ a.exp), ← Int.mul_assoc]
      _ = (c.mant * (2 : Int) ^ b.exp) * (2 : Int) ^ a.exp := by rw [hbc]
      _ = c.mant * (2 : Int) ^ a.exp * (2 : Int) ^ b.exp := by
            rw [Int.mul_assoc, Int.mul_comm ((2 : Int) ^ b.exp), ← Int.mul_assoc]
  exact int_mul_cancel_right (pow2_ne_zero b.exp) h1

-- Congruences

theorem equiv_add {a1 a2 b1 b2 : Dyadic} (ha : a1 ≈ a2) (hb : b1 ≈ b2) :
    add a1 b1 ≈ add a2 b2 := by
  unfold Equiv add at *
  simp only [Int.pow_add]
  calc (a1.mant * (2 : Int) ^ b1.exp + b1.mant * (2 : Int) ^ a1.exp) *
        ((2 : Int) ^ a2.exp * (2 : Int) ^ b2.exp)
      = (a1.mant * (2 : Int) ^ a2.exp) * ((2 : Int) ^ b1.exp * (2 : Int) ^ b2.exp) +
        (b1.mant * (2 : Int) ^ b2.exp) * ((2 : Int) ^ a1.exp * (2 : Int) ^ a2.exp) := by
          rw [Int.add_mul]
          congr 1
          · simp only [Int.mul_assoc, Int.mul_left_comm]
          · simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    _ = (a2.mant * (2 : Int) ^ a1.exp) * ((2 : Int) ^ b1.exp * (2 : Int) ^ b2.exp) +
        (b2.mant * (2 : Int) ^ b1.exp) * ((2 : Int) ^ a1.exp * (2 : Int) ^ a2.exp) := by
          rw [ha, hb]
    _ = (a2.mant * (2 : Int) ^ b2.exp + b2.mant * (2 : Int) ^ a2.exp) *
        ((2 : Int) ^ a1.exp * (2 : Int) ^ b1.exp) := by
          rw [Int.add_mul]
          congr 1
          · simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
          · simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]

theorem equiv_neg {a b : Dyadic} (h : a ≈ b) : neg a ≈ neg b := by
  unfold Equiv neg at *
  simp only [Int.neg_mul, h]

theorem equiv_sub {a1 a2 b1 b2 : Dyadic} (ha : a1 ≈ a2) (hb : b1 ≈ b2) :
    sub a1 b1 ≈ sub a2 b2 :=
  equiv_add ha (equiv_neg hb)

theorem equiv_mul {a1 a2 b1 b2 : Dyadic} (ha : a1 ≈ a2) (hb : b1 ≈ b2) :
    mul a1 b1 ≈ mul a2 b2 := by
  unfold Equiv mul at *
  simp only [Int.pow_add]
  calc (a1.mant * b1.mant) * ((2 : Int) ^ a2.exp * (2 : Int) ^ b2.exp)
      = (a1.mant * (2 : Int) ^ a2.exp) * (b1.mant * (2 : Int) ^ b2.exp) := by
          simp only [Int.mul_assoc, Int.mul_left_comm]
    _ = (a2.mant * (2 : Int) ^ a1.exp) * (b2.mant * (2 : Int) ^ b1.exp) := by rw [ha, hb]
    _ = (a2.mant * b2.mant) * ((2 : Int) ^ a1.exp * (2 : Int) ^ b1.exp) := by
          simp only [Int.mul_assoc, Int.mul_left_comm]

theorem equiv_divPow2 {a b : Dyadic} (k : Nat) (h : a ≈ b) : divPow2 a k ≈ divPow2 b k := by
  unfold Equiv divPow2 at *
  simp only [Int.pow_add]
  calc a.mant * ((2 : Int) ^ b.exp * (2 : Int) ^ k)
      = (a.mant * (2 : Int) ^ b.exp) * (2 : Int) ^ k := by rw [Int.mul_assoc]
    _ = (b.mant * (2 : Int) ^ a.exp) * (2 : Int) ^ k := by rw [h]
    _ = b.mant * ((2 : Int) ^ a.exp * (2 : Int) ^ k) := by rw [Int.mul_assoc]

theorem equiv_pow {a b : Dyadic} (n : Nat) (h : a ≈ b) : pow a n ≈ pow b n := by
  induction n with
  | zero => exact equiv_refl one
  | succ k ih => exact equiv_mul h ih

-- Ring laws up to Equiv

theorem add_comm (a b : Dyadic) : add a b ≈ add b a := by
  unfold Equiv add
  simp only [Nat.add_comm a.exp b.exp, Int.add_comm]

theorem add_assoc (a b c : Dyadic) : add (add a b) c ≈ add a (add b c) := by
  unfold Equiv add
  simp only [Int.pow_add, Nat.add_assoc]
  have hL : (a.mant * (2 : Int) ^ b.exp + b.mant * (2 : Int) ^ a.exp) * (2 : Int) ^ c.exp +
            c.mant * ((2 : Int) ^ a.exp * (2 : Int) ^ b.exp) =
            a.mant * ((2 : Int) ^ b.exp * (2 : Int) ^ c.exp) +
            (b.mant * (2 : Int) ^ c.exp + c.mant * (2 : Int) ^ b.exp) * (2 : Int) ^ a.exp := by
    rw [Int.add_mul, Int.add_mul, Int.add_assoc]
    congr 1
    · rw [Int.mul_assoc]
    · congr 1
      · simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
      · simp only [Int.mul_left_comm, Int.mul_comm]
  rw [hL]

theorem add_zero (a : Dyadic) : add a zero ≈ a := by
  unfold Equiv add zero
  simp

theorem zero_add (a : Dyadic) : add zero a ≈ a := by
  unfold Equiv add zero
  simp

theorem add_neg_self (a : Dyadic) : add a (neg a) ≈ zero := by
  unfold Equiv add neg zero
  simp only [Int.pow_zero, Int.mul_one, Int.zero_mul, Int.neg_mul]
  omega

theorem mul_comm (a b : Dyadic) : mul a b ≈ mul b a := by
  unfold Equiv mul
  simp only [Nat.add_comm a.exp b.exp, Int.mul_comm a.mant b.mant]

theorem mul_assoc (a b c : Dyadic) : mul (mul a b) c ≈ mul a (mul b c) := by
  unfold Equiv mul
  simp only [Nat.add_assoc, Int.mul_assoc]

theorem mul_one (a : Dyadic) : mul a one ≈ a := by
  unfold Equiv mul one
  simp

theorem one_mul (a : Dyadic) : mul one a ≈ a := by
  unfold Equiv mul one
  simp

theorem mul_zero (a : Dyadic) : mul a zero ≈ zero := by
  unfold Equiv mul zero
  simp

theorem zero_mul (a : Dyadic) : mul zero a ≈ zero := by
  unfold Equiv mul zero
  simp

theorem left_distrib (a b c : Dyadic) : mul a (add b c) ≈ add (mul a b) (mul a c) := by
  unfold Equiv mul add
  simp only [Int.pow_add]
  calc a.mant * (b.mant * (2 : Int) ^ c.exp + c.mant * (2 : Int) ^ b.exp) *
        ((2 : Int) ^ a.exp * (2 : Int) ^ b.exp * ((2 : Int) ^ a.exp * (2 : Int) ^ c.exp))
      = (a.mant * b.mant * ((2 : Int) ^ a.exp * (2 : Int) ^ c.exp) +
         a.mant * c.mant * ((2 : Int) ^ a.exp * (2 : Int) ^ b.exp)) *
        ((2 : Int) ^ a.exp * ((2 : Int) ^ b.exp * (2 : Int) ^ c.exp)) := by
          rw [Int.mul_add, Int.add_mul, Int.add_mul]
          congr 1
          · simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
          · simp only [Int.mul_assoc, Int.mul_left_comm]

theorem right_distrib (a b c : Dyadic) : mul (add a b) c ≈ add (mul a c) (mul b c) :=
  equiv_trans (mul_comm (add a b) c)
    (equiv_trans (left_distrib c a b) (equiv_add (mul_comm c a) (mul_comm c b)))

theorem neg_mul (a b : Dyadic) : mul (neg a) b ≈ neg (mul a b) := by
  unfold Equiv mul neg
  simp [Int.neg_mul]

theorem mul_neg (a b : Dyadic) : mul a (neg b) ≈ neg (mul a b) := by
  unfold Equiv mul neg
  simp [Int.mul_neg]

theorem pow_add (a : Dyadic) (m n : Nat) : pow a (m + n) ≈ mul (pow a m) (pow a n) := by
  induction m with
  | zero =>
    simp only [Nat.zero_add, pow]
    exact equiv_symm (one_mul (pow a n))
  | succ k ih =>
    rw [Nat.succ_add]
    simp only [pow]
    exact equiv_trans (equiv_mul (equiv_refl a) ih) (equiv_symm (mul_assoc a (pow a k) (pow a n)))

theorem ofInt_add (x y : Int) : ofInt (x + y) ≈ add (ofInt x) (ofInt y) := by
  unfold Equiv ofInt add
  simp

theorem ofInt_mul (x y : Int) : ofInt (x * y) ≈ mul (ofInt x) (ofInt y) := by
  unfold Equiv ofInt mul
  simp

theorem ofInt_neg (x : Int) : ofInt (-x) ≈ neg (ofInt x) := by
  unfold Equiv ofInt neg
  simp

theorem ofInt_zero : ofInt 0 = zero := rfl

theorem ofInt_one : ofInt 1 = one := rfl

theorem divPow2_zero (a : Dyadic) : divPow2 a 0 ≈ a := by
  unfold Equiv divPow2
  simp

theorem divPow2_add (a b : Dyadic) (k : Nat) :
    divPow2 (add a b) k ≈ add (divPow2 a k) (divPow2 b k) := by
  unfold Equiv divPow2 add
  simp only [Int.pow_add]
  rw [Int.add_mul, Int.add_mul]
  congr 1
  · simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  · simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]

theorem divPow2_mul (a b : Dyadic) (k1 k2 : Nat) :
    divPow2 (mul a b) (k1 + k2) ≈ mul (divPow2 a k1) (divPow2 b k2) := by
  unfold Equiv divPow2 mul
  simp only [Int.pow_add]
  simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]

theorem divPow2_neg (a : Dyadic) (k : Nat) : divPow2 (neg a) k = neg (divPow2 a k) := rfl

theorem divPow2_scale_cancel (a : Dyadic) (k : Nat) :
    divPow2 (mul (ofInt ((2 : Int) ^ k)) a) k ≈ a := by
  unfold Equiv divPow2 mul ofInt
  simp only [Int.pow_add, Nat.zero_add]
  simp only [Int.mul_assoc, Int.mul_comm]

theorem divPow2_shift_up (a : Dyadic) (k m : Nat) (hkm : k ≤ m) :
    divPow2 (mul (ofInt ((2 : Int) ^ (m - k))) a) m ≈ divPow2 a k := by
  unfold Equiv divPow2 mul ofInt
  have hsum : (m - k) + k = m := Nat.sub_add_cancel hkm
  simp only [Nat.zero_add, Int.pow_add]
  calc (2 : Int) ^ (m - k) * a.mant * ((2 : Int) ^ a.exp * (2 : Int) ^ k)
      = a.mant * ((2 : Int) ^ a.exp * ((2 : Int) ^ (m - k) * (2 : Int) ^ k)) := by
          simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    _ = a.mant * ((2 : Int) ^ a.exp * (2 : Int) ^ m) := by
          rw [← Int.pow_add, hsum]

-- Nonnegativity and zero lemmas

theorem nonneg_of_equiv {a b : Dyadic} (hab : a ≈ b) (ha : Nonneg a) : Nonneg b := by
  unfold Equiv Nonneg at *
  have h1 : 0 ≤ a.mant * (2 : Int) ^ b.exp := Int.mul_nonneg ha (Int.le_of_lt (pow2_pos b.exp))
  rw [hab] at h1
  exact nonneg_of_mul_pos (pow2_pos a.exp) h1

theorem isZero_of_equiv {a b : Dyadic} (hab : a ≈ b) (ha : IsZero a) : IsZero b := by
  unfold Equiv IsZero at *
  rw [ha, Int.zero_mul] at hab
  have h0 : b.mant * (2 : Int) ^ a.exp = 0 * (2 : Int) ^ a.exp := by
    rw [Int.zero_mul]
    exact hab.symm
  exact int_mul_cancel_right (pow2_ne_zero a.exp) h0

theorem equiv_zero_of_isZero {a : Dyadic} (ha : IsZero a) : a ≈ zero := by
  unfold Equiv IsZero zero at *
  simp [ha]

theorem nonneg_zero : Nonneg zero := by unfold Nonneg zero; dsimp only; omega

theorem nonneg_ofInt {z : Int} (hz : 0 ≤ z) : Nonneg (ofInt z) := hz

theorem nonneg_add {a b : Dyadic} (ha : Nonneg a) (hb : Nonneg b) : Nonneg (add a b) := by
  unfold Nonneg add at *
  dsimp only
  have h1 : 0 ≤ a.mant * (2 : Int) ^ b.exp := Int.mul_nonneg ha (Int.le_of_lt (pow2_pos b.exp))
  have h2 : 0 ≤ b.mant * (2 : Int) ^ a.exp := Int.mul_nonneg hb (Int.le_of_lt (pow2_pos a.exp))
  omega

theorem nonneg_mul {a b : Dyadic} (ha : Nonneg a) (hb : Nonneg b) : Nonneg (mul a b) :=
  Int.mul_nonneg ha hb

theorem nonneg_sq (a : Dyadic) : Nonneg (mul a a) := by
  unfold Nonneg mul
  dsimp only
  by_cases h : 0 ≤ a.mant
  · exact Int.mul_nonneg h h
  · have hneg : 0 ≤ -a.mant := by omega
    have hmul : 0 ≤ (-a.mant) * (-a.mant) := Int.mul_nonneg hneg hneg
    rw [Int.neg_mul_neg] at hmul
    exact hmul

theorem nonneg_divPow2 {a : Dyadic} (k : Nat) (ha : Nonneg a) : Nonneg (divPow2 a k) := ha

theorem nonneg_of_divPow2 {a : Dyadic} (k : Nat) (ha : Nonneg (divPow2 a k)) : Nonneg a := ha

theorem nonneg_of_scale_pow2 {a : Dyadic} (k : Nat) (h : Nonneg (mul (ofInt ((2 : Int) ^ k)) a)) :
    Nonneg a := by
  unfold Nonneg mul ofInt at *
  have hpos : (0 : Int) < (2 : Int) ^ k := pow2_pos k
  rw [Int.mul_comm] at h
  exact nonneg_of_mul_pos hpos h

theorem nonneg_sub_iff_le (a b : Dyadic) : Nonneg (sub b a) ↔ Le a b := by
  unfold Nonneg sub add neg Le
  simp only [Int.neg_mul]
  omega

theorem le_refl (a : Dyadic) : Le a a := Int.le_refl _

theorem le_of_nonneg_sub {a b : Dyadic} (h : Nonneg (sub b a)) : Le a b :=
  (nonneg_sub_iff_le a b).mp h

theorem nonneg_sub_of_le {a b : Dyadic} (h : Le a b) : Nonneg (sub b a) :=
  (nonneg_sub_iff_le a b).mpr h

theorem not_nonneg_neg_const {m : Int} {e : Nat} (hm : m < 0) : ¬ Nonneg ⟨m, e⟩ := by
  unfold Nonneg
  dsimp only
  omega

theorem add_sub_cancel (a b : Dyadic) : add (sub a b) b ≈ a := by
  unfold sub
  exact equiv_trans (add_assoc a (neg b) b)
    (equiv_trans (equiv_add (equiv_refl a) (equiv_trans (add_comm (neg b) b) (add_neg_self b)))
      (add_zero a))

theorem sub_add_cancel (a b : Dyadic) : sub (add a b) b ≈ a := by
  unfold sub
  exact equiv_trans (add_assoc a b (neg b))
    (equiv_trans (equiv_add (equiv_refl a) (add_neg_self b)) (add_zero a))

theorem add_sub_swap (a b c : Dyadic) : add a (sub b c) ≈ sub (add a b) c := by
  unfold sub
  exact equiv_symm (add_assoc a b (neg c))


-- ============================================================================
-- Section 2: Dimension-Polymorphic Sparse Multivariate Polynomials over Z[1/2]
-- ============================================================================

end Dyadic

namespace Mono

theorem cmp_eq_iff : ∀ m1 m2 : Mono, cmp m1 m2 = .eq → m1 = m2
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [cmp] at h
  | _ :: _, [], h => by simp [cmp] at h
  | (v1, e1) :: t1, (v2, e2) :: t2, h => by
    unfold cmp at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · have hvEq : v1 = v2 := by omega
            have heEq : e1 = e2 := by omega
            have htEq : t1 = t2 := cmp_eq_iff t1 t2 h
            rw [hvEq, heEq, htEq]

theorem eval_ofInt (m : Mono) (env : Nat → Int) :
    eval m (fun i => Dyadic.ofInt (env i)) = Dyadic.ofInt (evalInt m env) := by
  induction m with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨v, e⟩
    simp only [eval, evalInt, ih]
    have hpow : ∀ k : Nat, Dyadic.pow (Dyadic.ofInt (env v)) k = Dyadic.ofInt ((env v) ^ k) := by
      intro k
      induction k with
      | zero => rw [Int.pow_zero]; rfl
      | succ j ihj =>
        simp only [Dyadic.pow]
        rw [ihj]
        simp only [Dyadic.mul, Dyadic.ofInt, Int.pow_succ, Int.mul_comm, Nat.add_zero]
    rw [hpow e]
    rfl

theorem eval_insertFactor (v e : Nat) (m : Mono) (env : Nat → Dyadic) :
    eval (insertFactor v e m) env ≈ Dyadic.mul (Dyadic.pow (env v) e) (eval m env) := by
  induction m with
  | nil =>
    simp only [insertFactor, eval]
    exact Dyadic.equiv_refl _
  | cons hd tl ih =>
    rcases hd with ⟨v', e'⟩
    unfold insertFactor
    by_cases hlt : v < v'
    · simp only [hlt, ↓reduceIte, eval]
      exact Dyadic.equiv_refl _
    · simp only [hlt, ↓reduceIte]
      by_cases hgt : v' < v
      · simp only [hgt, ↓reduceIte, eval]
        refine Dyadic.equiv_trans (Dyadic.equiv_mul (Dyadic.equiv_refl _) ih) ?_
        refine Dyadic.equiv_trans (Dyadic.equiv_symm (Dyadic.mul_assoc _ _ _)) ?_
        refine Dyadic.equiv_trans (Dyadic.equiv_mul (Dyadic.mul_comm _ _) (Dyadic.equiv_refl _)) ?_
        exact Dyadic.mul_assoc _ _ _
      · have hv : v = v' := by omega
        simp only [hgt, ↓reduceIte, eval]
        subst hv
        exact Dyadic.equiv_trans (Dyadic.equiv_mul (Dyadic.pow_add (env v) e e') (Dyadic.equiv_refl _))
          (Dyadic.mul_assoc _ _ _)

theorem eval_mul (m1 m2 : Mono) (env : Nat → Dyadic) :
    eval (mul m1 m2) env ≈ Dyadic.mul (eval m1 env) (eval m2 env) := by
  induction m1 with
  | nil =>
    simp only [mul, eval]
    exact Dyadic.equiv_symm (Dyadic.one_mul (eval m2 env))
  | cons hd tl ih =>
    rcases hd with ⟨v, e⟩
    simp only [mul, eval]
    exact Dyadic.equiv_trans (eval_insertFactor v e (mul tl m2) env)
      (Dyadic.equiv_trans (Dyadic.equiv_mul (Dyadic.equiv_refl _) ih)
        (Dyadic.equiv_symm (Dyadic.mul_assoc _ _ _)))

theorem eval_shiftFrom (k delta : Nat) (m : Mono) (env : Nat → Dyadic) :
    eval (shiftFrom k delta m) env =
    eval m (fun v => env (if v < k then v else v + delta)) := by
  induction m with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨v, e⟩
    unfold shiftFrom at ih ⊢
    simp only [List.map_cons, eval]
    rw [ih]

end Mono

namespace Poly

theorem eval_ofInt (p : Poly) (env : Nat → Int) :
    eval p (fun i => Dyadic.ofInt (env i)) = Dyadic.ofInt (evalInt p env) := by
  induction p with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨m, c⟩
    simp only [eval, evalInt, ih, Mono.eval_ofInt]
    simp [Dyadic.add, Dyadic.mul, Dyadic.ofInt]

theorem eval_insert (m : Mono) (c : Int) (p : Poly) (env : Nat → Dyadic) :
    eval (insert m c p) env ≈ Dyadic.add (Dyadic.mul (Dyadic.ofInt c) (Mono.eval m env)) (eval p env) := by
  induction p with
  | nil =>
    unfold insert
    by_cases hc : c == 0
    · have hc0 : c = 0 := by simpa using hc
      subst hc0
      simp only [beq_self_eq_true, ↓reduceIte, eval, Dyadic.ofInt_zero]
      exact Dyadic.equiv_symm (Dyadic.equiv_trans (Dyadic.add_zero _) (Dyadic.zero_mul _))
    · simp only [hc, eval]
      exact Dyadic.equiv_refl _
  | cons hd tl ih =>
    rcases hd with ⟨m', c'⟩
    unfold insert
    by_cases hc : c == 0
    · have hc0 : c = 0 := by simpa using hc
      subst hc0
      simp only [beq_self_eq_true, ↓reduceIte, Dyadic.ofInt_zero]
      exact Dyadic.equiv_symm
        (Dyadic.equiv_trans (Dyadic.equiv_add (Dyadic.zero_mul _) (Dyadic.equiv_refl _))
          (Dyadic.zero_add _))
    · simp only [hc]
      cases hcmp : Mono.cmp m m' with
      | lt =>
        simp only [eval]
        exact Dyadic.equiv_refl _
      | eq =>
        have hm : m = m' := Mono.cmp_eq_iff m m' hcmp
        subst hm
        dsimp only
        have hcomb : Dyadic.add (Dyadic.mul (Dyadic.ofInt (c + c')) (Mono.eval m env)) (eval tl env) ≈
            Dyadic.add (Dyadic.mul (Dyadic.ofInt c) (Mono.eval m env))
              (Dyadic.add (Dyadic.mul (Dyadic.ofInt c') (Mono.eval m env)) (eval tl env)) := by
          refine Dyadic.equiv_trans
            (Dyadic.equiv_add
              (Dyadic.equiv_trans (Dyadic.equiv_mul (Dyadic.ofInt_add c c') (Dyadic.equiv_refl _))
                (Dyadic.right_distrib _ _ _))
              (Dyadic.equiv_refl _)) ?_
          exact Dyadic.add_assoc _ _ _
        by_cases hs : (c + c' == 0)
        · have hs0 : c + c' = 0 := by simpa using hs
          simp only [hs, ↓reduceIte, eval]
          refine Dyadic.equiv_trans ?_ hcomb
          rw [hs0]
          simp only [Dyadic.ofInt_zero]
          exact Dyadic.equiv_symm
            (Dyadic.equiv_trans (Dyadic.equiv_add (Dyadic.zero_mul _) (Dyadic.equiv_refl _))
              (Dyadic.zero_add _))
        · simp only [hs, eval]
          exact hcomb
      | gt =>
        simp only [eval]
        refine Dyadic.equiv_trans (Dyadic.equiv_add (Dyadic.equiv_refl _) ih) ?_
        refine Dyadic.equiv_trans (Dyadic.equiv_symm (Dyadic.add_assoc _ _ _)) ?_
        refine Dyadic.equiv_trans (Dyadic.equiv_add (Dyadic.add_comm _ _) (Dyadic.equiv_refl _)) ?_
        exact Dyadic.add_assoc _ _ _

theorem eval_normGo (p acc : Poly) (env : Nat → Dyadic) :
    eval (normGo p acc) env ≈ Dyadic.add (eval p env) (eval acc env) := by
  induction p generalizing acc with
  | nil =>
    simp only [normGo, eval]
    exact Dyadic.equiv_symm (Dyadic.zero_add _)
  | cons hd tl ih =>
    rcases hd with ⟨m, c⟩
    simp only [normGo, eval]
    refine Dyadic.equiv_trans (ih (insert m c acc)) ?_
    refine Dyadic.equiv_trans (Dyadic.equiv_add (Dyadic.equiv_refl _) (eval_insert m c acc env)) ?_
    refine Dyadic.equiv_trans (Dyadic.equiv_symm (Dyadic.add_assoc _ _ _)) ?_
    exact Dyadic.equiv_add (Dyadic.add_comm _ _) (Dyadic.equiv_refl _)

theorem eval_norm (p : Poly) (env : Nat → Dyadic) :
    eval (norm p) env ≈ eval p env := by
  unfold norm
  exact Dyadic.equiv_trans (eval_normGo p [] env) (Dyadic.add_zero _)

theorem eval_scale (k : Int) (p : Poly) (env : Nat → Dyadic) :
    eval (scale k p) env ≈ Dyadic.mul (Dyadic.ofInt k) (eval p env) := by
  unfold scale
  by_cases hk : k == 0
  · have hk0 : k = 0 := by simpa using hk
    subst hk0
    simp only [beq_self_eq_true, ↓reduceIte, eval, Dyadic.ofInt_zero]
    exact Dyadic.equiv_symm (Dyadic.zero_mul _)
  · simp only [hk]
    induction p with
    | nil =>
      simp only [List.map_nil, eval]
      exact Dyadic.equiv_symm (Dyadic.mul_zero _)
    | cons hd tl ih =>
      rcases hd with ⟨m, c⟩
      simp only [List.map_cons, eval]
      refine Dyadic.equiv_trans
        (Dyadic.equiv_add
          (Dyadic.equiv_trans (Dyadic.equiv_mul (Dyadic.ofInt_mul k c) (Dyadic.equiv_refl _))
            (Dyadic.mul_assoc _ _ _))
          ih) ?_
      exact Dyadic.equiv_symm (Dyadic.left_distrib _ _ _)

theorem eval_neg (p : Poly) (env : Nat → Dyadic) :
    eval (neg p) env ≈ Dyadic.neg (eval p env) := by
  induction p with
  | nil =>
    simp only [neg, List.map_nil, eval]
    exact Dyadic.equiv_refl _
  | cons hd tl ih =>
    rcases hd with ⟨m, c⟩
    simp only [neg, List.map_cons, eval]
    refine Dyadic.equiv_trans
      (Dyadic.equiv_add
        (Dyadic.equiv_trans (Dyadic.equiv_mul (Dyadic.ofInt_neg c) (Dyadic.equiv_refl _))
          (Dyadic.neg_mul _ _))
        ih) ?_
    unfold Dyadic.Equiv Dyadic.add Dyadic.neg
    simp only [Int.neg_mul, Int.neg_add]

theorem append_eval (p q : Poly) (env : Nat → Dyadic) :
    eval (p ++ q) env ≈ Dyadic.add (eval p env) (eval q env) := by
  induction p with
  | nil =>
    simp only [List.nil_append, eval]
    exact Dyadic.equiv_symm (Dyadic.zero_add _)
  | cons hd tl ih =>
    rcases hd with ⟨m, c⟩
    simp only [List.cons_append, eval]
    exact Dyadic.equiv_trans (Dyadic.equiv_add (Dyadic.equiv_refl _) ih)
      (Dyadic.equiv_symm (Dyadic.add_assoc _ _ _))

theorem eval_add (p q : Poly) (env : Nat → Dyadic) :
    eval (add p q) env ≈ Dyadic.add (eval p env) (eval q env) :=
  Dyadic.equiv_trans (eval_norm (p ++ q) env) (append_eval p q env)

theorem eval_mulTerm (m1 : Mono) (c1 : Int) (q : Poly) (env : Nat → Dyadic) :
    eval (mulTerm m1 c1 q) env ≈
    Dyadic.mul (Dyadic.mul (Dyadic.ofInt c1) (Mono.eval m1 env)) (eval q env) := by
  induction q with
  | nil =>
    simp only [mulTerm, List.map_nil, eval]
    exact Dyadic.equiv_symm (Dyadic.mul_zero _)
  | cons hd tl ih =>
    rcases hd with ⟨m2, c2⟩
    simp only [mulTerm, List.map_cons, eval]
    have hterm :
        Dyadic.mul (Dyadic.ofInt (c1 * c2)) (Mono.eval (Mono.mul m1 m2) env) ≈
        Dyadic.mul (Dyadic.mul (Dyadic.ofInt c1) (Mono.eval m1 env))
                   (Dyadic.mul (Dyadic.ofInt c2) (Mono.eval m2 env)) := by
      refine Dyadic.equiv_trans (Dyadic.equiv_mul (Dyadic.ofInt_mul c1 c2) (Mono.eval_mul m1 m2 env)) ?_
      refine Dyadic.equiv_trans (Dyadic.mul_assoc _ _ _) ?_
      refine Dyadic.equiv_trans (Dyadic.equiv_mul (Dyadic.equiv_refl _)
        (Dyadic.equiv_trans (Dyadic.equiv_symm (Dyadic.mul_assoc _ _ _))
          (Dyadic.equiv_trans (Dyadic.equiv_mul (Dyadic.mul_comm _ _) (Dyadic.equiv_refl _))
            (Dyadic.mul_assoc _ _ _)))) ?_
      exact Dyadic.equiv_symm (Dyadic.mul_assoc _ _ _)
    exact Dyadic.equiv_trans (Dyadic.equiv_add hterm ih) (Dyadic.equiv_symm (Dyadic.left_distrib _ _ _))

theorem eval_mulRaw (p q : Poly) (env : Nat → Dyadic) :
    eval (mulRaw p q) env ≈ Dyadic.mul (eval p env) (eval q env) := by
  induction p with
  | nil =>
    simp only [mulRaw, eval]
    exact Dyadic.equiv_symm (Dyadic.zero_mul _)
  | cons hd tl ih =>
    rcases hd with ⟨m1, c1⟩
    simp only [mulRaw, eval]
    refine Dyadic.equiv_trans (append_eval _ _ env) ?_
    refine Dyadic.equiv_trans (Dyadic.equiv_add (eval_mulTerm m1 c1 q env) ih) ?_
    exact Dyadic.equiv_symm (Dyadic.right_distrib _ _ _)

theorem eval_mul (p q : Poly) (env : Nat → Dyadic) :
    eval (mul p q) env ≈ Dyadic.mul (eval p env) (eval q env) :=
  Dyadic.equiv_trans (eval_norm _ env) (eval_mulRaw p q env)

theorem eval_shiftFrom (k delta : Nat) (p : Poly) (env : Nat → Dyadic) :
    eval (shiftFrom k delta p) env ≈
    eval p (fun v => env (if v < k then v else v + delta)) := by
  unfold shiftFrom
  refine Dyadic.equiv_trans (eval_norm _ env) ?_
  induction p with
  | nil => exact Dyadic.equiv_refl _
  | cons hd tl ih =>
    rcases hd with ⟨m, c⟩
    simp only [List.map_cons, eval, Mono.eval_shiftFrom]
    exact Dyadic.equiv_add (Dyadic.equiv_refl _) ih

end Poly

namespace DyadicPoly

def const (mant : Int) (shift : Nat := 0) : DyadicPoly :=
  ⟨shift, if mant == 0 then [] else [([], mant)]⟩

def var (v : Nat) : DyadicPoly := ⟨0, [([(v, 1)], 1)]⟩

theorem eval_ofInt (p : DyadicPoly) (env : Nat → Int) :
    eval p (fun i => Dyadic.ofInt (env i)) = ⟨Poly.evalInt p.poly env, p.shift⟩ := by
  unfold eval
  rw [Poly.eval_ofInt]
  simp [Dyadic.divPow2, Dyadic.ofInt]

theorem natMax_le_left (a b : Nat) : a ≤ natMax a b := by
  unfold natMax; split <;> omega

theorem natMax_le_right (a b : Nat) : b ≤ natMax a b := by
  unfold natMax; split <;> omega

theorem monoEq_eq_iff : ∀ m1 m2 : Mono, monoEq m1 m2 = true → m1 = m2
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | (v1, e1) :: t1, (v2, e2) :: t2, h => by
    simp only [monoEq, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨hv, he⟩, ht⟩
    rw [hv, he, monoEq_eq_iff t1 t2 ht]

theorem polyEq_eq_iff : ∀ p q : Poly, polyEq p q = true → p = q
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | (m1, c1) :: t1, (m2, c2) :: t2, h => by
    simp only [polyEq, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨hm, hc⟩, ht⟩
    rw [monoEq_eq_iff m1 m2 hm, hc, polyEq_eq_iff t1 t2 ht]

theorem eval_add (a b : DyadicPoly) (env : Nat → Dyadic) :
    eval (add a b) env ≈ Dyadic.add (eval a env) (eval b env) := by
  unfold eval add
  dsimp only
  let m := natMax a.shift b.shift
  have hma : a.shift ≤ m := natMax_le_left a.shift b.shift
  have hmb : b.shift ≤ m := natMax_le_right a.shift b.shift
  refine Dyadic.equiv_trans (Dyadic.equiv_divPow2 m (Poly.eval_add _ _ env)) ?_
  refine Dyadic.equiv_trans (Dyadic.divPow2_add _ _ m) ?_
  refine Dyadic.equiv_add ?_ ?_
  · rw [Dyadic.pow2Int_eq]
    exact Dyadic.equiv_trans (Dyadic.equiv_divPow2 m (Poly.eval_scale _ _ env))
      (Dyadic.divPow2_shift_up _ a.shift m hma)
  · rw [Dyadic.pow2Int_eq]
    exact Dyadic.equiv_trans (Dyadic.equiv_divPow2 m (Poly.eval_scale _ _ env))
      (Dyadic.divPow2_shift_up _ b.shift m hmb)

theorem eval_neg (a : DyadicPoly) (env : Nat → Dyadic) :
    eval (neg a) env ≈ Dyadic.neg (eval a env) := by
  unfold eval neg
  dsimp only
  rw [← Dyadic.divPow2_neg]
  exact Dyadic.equiv_divPow2 a.shift (Poly.eval_neg a.poly env)

theorem eval_sub (a b : DyadicPoly) (env : Nat → Dyadic) :
    eval (sub a b) env ≈ Dyadic.sub (eval a env) (eval b env) := by
  unfold sub Dyadic.sub
  exact Dyadic.equiv_trans (eval_add a (neg b) env)
    (Dyadic.equiv_add (Dyadic.equiv_refl _) (eval_neg b env))

theorem eval_mul (a b : DyadicPoly) (env : Nat → Dyadic) :
    eval (mul a b) env ≈ Dyadic.mul (eval a env) (eval b env) := by
  unfold eval mul
  dsimp only
  exact Dyadic.equiv_trans (Dyadic.equiv_divPow2 (a.shift + b.shift) (Poly.eval_mul a.poly b.poly env))
    (Dyadic.divPow2_mul _ _ a.shift b.shift)

theorem eval_shiftFrom (k delta : Nat) (a : DyadicPoly) (env : Nat → Dyadic) :
    eval (shiftFrom k delta a) env ≈
    eval a (fun v => env (if v < k then v else v + delta)) := by
  unfold eval shiftFrom
  dsimp only
  exact Dyadic.equiv_divPow2 a.shift (Poly.eval_shiftFrom k delta a.poly env)

theorem eval_one (env : Nat → Dyadic) : eval one env ≈ Dyadic.one := by
  unfold eval one Poly.eval Mono.eval
  exact Dyadic.equiv_trans (Dyadic.divPow2_zero _)
    (Dyadic.equiv_trans (Dyadic.add_zero _) (Dyadic.one_mul _))

theorem eval_const (m : Int) (s : Nat) (env : Nat → Dyadic) :
    eval (const m s) env ≈ ⟨m, s⟩ := by
  unfold eval const
  by_cases hm : m == 0
  · have hm0 : m = 0 := by simpa using hm
    subst hm0
    simp [Poly.eval, Dyadic.divPow2, Dyadic.zero, Dyadic.Equiv]
  · simp only [hm, Bool.false_eq_true, ↓reduceIte, Poly.eval, Mono.eval]
    unfold Dyadic.Equiv Dyadic.divPow2 Dyadic.add Dyadic.mul Dyadic.ofInt Dyadic.one Dyadic.zero
    simp

theorem eq_sound {a b : DyadicPoly} (h : eq a b = true) (env : Nat → Dyadic) :
    eval a env ≈ eval b env := by
  unfold eq at h
  have hpeq : Poly.norm (Poly.scale (Dyadic.pow2Int b.shift) a.poly) =
              Poly.norm (Poly.scale (Dyadic.pow2Int a.shift) b.poly) :=
    polyEq_eq_iff _ _ h
  rw [Dyadic.pow2Int_eq, Dyadic.pow2Int_eq] at hpeq
  have hev : Poly.eval (Poly.scale ((2 : Int) ^ b.shift) a.poly) env ≈
             Poly.eval (Poly.scale ((2 : Int) ^ a.shift) b.poly) env := by
    refine Dyadic.equiv_trans (Dyadic.equiv_symm (Poly.eval_norm _ env)) ?_
    rw [hpeq]
    exact Poly.eval_norm _ env
  have h1 : Dyadic.mul (Dyadic.ofInt ((2 : Int) ^ b.shift)) (Poly.eval a.poly env) ≈
            Dyadic.mul (Dyadic.ofInt ((2 : Int) ^ a.shift)) (Poly.eval b.poly env) := by
    exact Dyadic.equiv_trans (Dyadic.equiv_symm (Poly.eval_scale _ _ env))
      (Dyadic.equiv_trans hev (Poly.eval_scale _ _ env))
  have h2 : Dyadic.divPow2 (Dyadic.mul (Dyadic.ofInt ((2 : Int) ^ b.shift)) (Poly.eval a.poly env))
              (a.shift + b.shift) ≈
            Dyadic.divPow2 (Dyadic.mul (Dyadic.ofInt ((2 : Int) ^ a.shift)) (Poly.eval b.poly env))
              (a.shift + b.shift) := Dyadic.equiv_divPow2 (a.shift + b.shift) h1
  have hL : Dyadic.divPow2 (Dyadic.mul (Dyadic.ofInt ((2 : Int) ^ b.shift)) (Poly.eval a.poly env))
              (a.shift + b.shift) ≈ eval a env := by
    have h0 := Dyadic.divPow2_shift_up (Poly.eval a.poly env) a.shift (a.shift + b.shift) (Nat.le_add_right _ _)
    rw [Nat.add_sub_cancel_left] at h0
    exact h0
  have hR : Dyadic.divPow2 (Dyadic.mul (Dyadic.ofInt ((2 : Int) ^ a.shift)) (Poly.eval b.poly env))
              (a.shift + b.shift) ≈ eval b env := by
    have h0 := Dyadic.divPow2_shift_up (Poly.eval b.poly env) b.shift (a.shift + b.shift) (Nat.le_add_left _ _)
    rw [Nat.add_sub_cancel] at h0
    exact h0
  exact Dyadic.equiv_trans (Dyadic.equiv_symm hL) (Dyadic.equiv_trans h2 hR)


-- ============================================================================
-- Section 3: Exact Dyadic Gram Matrix & Binary LDL^T PSD Compiler
-- ============================================================================

end DyadicPoly

namespace Gram

def dotDyadic : List Int → List Dyadic → Dyadic
  | c :: cs, u :: us => Dyadic.add (Dyadic.mul (Dyadic.ofInt c) u) (dotDyadic cs us)
  | _, _ => Dyadic.zero

def quadForm : List (List Int) → List Dyadic → List Dyadic → Dyadic
  | row :: rows, u :: us, full =>
      Dyadic.add (Dyadic.mul u (dotDyadic row full)) (quadForm rows us full)
  | _, _, _ => Dyadic.zero

theorem dotDyadic_zeroRow (r : Nat) (u : List Dyadic) :
    dotDyadic (zeroRow r) u ≈ Dyadic.zero := by
  induction r generalizing u with
  | zero => exact Dyadic.equiv_refl _
  | succ k ih =>
    cases u with
    | nil => exact Dyadic.equiv_refl _
    | cons x xs =>
      simp only [zeroRow, List.replicate_succ, dotDyadic, Dyadic.ofInt_zero]
      exact Dyadic.equiv_trans (Dyadic.equiv_add (Dyadic.zero_mul x) (ih xs)) (Dyadic.add_zero _)

theorem quadForm_zeroMat (m r : Nat) (us full : List Dyadic) :
    quadForm (List.replicate m (zeroRow r)) us full ≈ Dyadic.zero := by
  induction m generalizing us with
  | zero => exact Dyadic.equiv_refl _
  | succ k ih =>
    cases us with
    | nil => exact Dyadic.equiv_refl _
    | cons u rest =>
      simp only [List.replicate_succ, quadForm]
      exact Dyadic.equiv_trans
        (Dyadic.equiv_add
          (Dyadic.equiv_trans (Dyadic.equiv_mul (Dyadic.equiv_refl u) (dotDyadic_zeroRow r full))
            (Dyadic.mul_zero u))
          (ih rest))
        (Dyadic.add_zero _)

theorem dotDyadic_addScaledRow (k : Int) (a b : List Int) (u : List Dyadic)
    (hlen : a.length = b.length) :
    dotDyadic (addScaledRow k a b) u ≈
    Dyadic.add (dotDyadic a u) (Dyadic.mul (Dyadic.ofInt k) (dotDyadic b u)) := by
  induction a generalizing b u with
  | nil =>
    cases b with
    | nil =>
      simp only [addScaledRow, dotDyadic]
      exact Dyadic.equiv_symm (Dyadic.equiv_trans (Dyadic.zero_add _) (Dyadic.mul_zero _))
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases b with
    | nil => simp at hlen
    | cons y ys =>
      have hlen' : xs.length = ys.length := by simpa using hlen
      cases u with
      | nil =>
        simp only [addScaledRow, dotDyadic]
        exact Dyadic.equiv_symm (Dyadic.equiv_trans (Dyadic.zero_add _) (Dyadic.mul_zero _))
      | cons v vs =>
        simp only [addScaledRow, dotDyadic]
        have hhd : Dyadic.mul (Dyadic.ofInt (x + k * y)) v ≈
            Dyadic.add (Dyadic.mul (Dyadic.ofInt x) v)
                       (Dyadic.mul (Dyadic.ofInt k) (Dyadic.mul (Dyadic.ofInt y) v)) := by
          refine Dyadic.equiv_trans (Dyadic.equiv_mul (Dyadic.ofInt_add x (k * y)) (Dyadic.equiv_refl v)) ?_
          refine Dyadic.equiv_trans (Dyadic.right_distrib _ _ v) ?_
          refine Dyadic.equiv_add (Dyadic.equiv_refl _) ?_
          exact Dyadic.equiv_trans (Dyadic.equiv_mul (Dyadic.ofInt_mul k y) (Dyadic.equiv_refl v))
            (Dyadic.mul_assoc _ _ _)
        refine Dyadic.equiv_trans (Dyadic.equiv_add hhd (ih ys vs hlen')) ?_
        -- (a1 + b1) + (a2 + k*b2) ≈ (a1 + a2) + k*(b1' + b2)
        have rearr : ∀ p1 q1 p2 q2 : Dyadic,
            Dyadic.add (Dyadic.add p1 q1) (Dyadic.add p2 q2) ≈
            Dyadic.add (Dyadic.add p1 p2) (Dyadic.add q1 q2) := by
          intro p1 q1 p2 q2
          refine Dyadic.equiv_trans (Dyadic.add_assoc p1 q1 (Dyadic.add p2 q2)) ?_
          refine Dyadic.equiv_trans (Dyadic.equiv_add (Dyadic.equiv_refl p1)
            (Dyadic.equiv_trans (Dyadic.equiv_symm (Dyadic.add_assoc q1 p2 q2))
              (Dyadic.equiv_trans (Dyadic.equiv_add (Dyadic.add_comm q1 p2) (Dyadic.equiv_refl q2))
                (Dyadic.add_assoc p2 q1 q2)))) ?_
          exact Dyadic.equiv_symm (Dyadic.add_assoc p1 p2 (Dyadic.add q1 q2))
        exact Dyadic.equiv_trans (rearr _ _ _ _)
          (Dyadic.equiv_add (Dyadic.equiv_refl _) (Dyadic.equiv_symm (Dyadic.left_distrib _ _ _)))

theorem quadForm_addOuterProd (d : Int) (row : List Int)
    (acc : List (List Int)) (cs : List Int) (us full : List Dyadic)
    (hacc : acc.length = cs.length)
    (hrows : ∀ ar ∈ acc, ar.length = row.length) :
    quadForm (addOuterProd d row acc cs) us full ≈
    Dyadic.add (quadForm acc us full)
      (Dyadic.mul (Dyadic.ofInt d) (Dyadic.mul (dotDyadic cs us) (dotDyadic row full))) := by
  induction acc generalizing cs us with
  | nil =>
    cases cs with
    | nil =>
      simp only [addOuterProd, quadForm, dotDyadic]
      exact Dyadic.equiv_symm
        (Dyadic.equiv_trans (Dyadic.zero_add _)
          (Dyadic.equiv_trans (Dyadic.equiv_mul (Dyadic.equiv_refl _) (Dyadic.zero_mul _))
            (Dyadic.mul_zero _)))
    | cons _ _ => simp at hacc
  | cons ar ars ih =>
    cases cs with
    | nil => simp at hacc
    | cons c cs' =>
      have hacc' : ars.length = cs'.length := by simpa using hacc
      have har : ar.length = row.length := hrows ar (List.Mem.head _)
      have hars : ∀ x ∈ ars, x.length = row.length := fun x hx => hrows x (List.Mem.tail _ hx)
      cases us with
      | nil =>
        simp only [addOuterProd, quadForm, dotDyadic]
        exact Dyadic.equiv_symm
          (Dyadic.equiv_trans (Dyadic.zero_add _)
            (Dyadic.equiv_trans (Dyadic.equiv_mul (Dyadic.equiv_refl _) (Dyadic.zero_mul _))
              (Dyadic.mul_zero _)))
      | cons u us' =>
        simp only [addOuterProd, quadForm, dotDyadic]
        have hhd : Dyadic.mul u (dotDyadic (addScaledRow (d * c) ar row) full) ≈
            Dyadic.add (Dyadic.mul u (dotDyadic ar full))
              (Dyadic.mul (Dyadic.ofInt d)
                (Dyadic.mul (Dyadic.mul (Dyadic.ofInt c) u) (dotDyadic row full))) := by
          refine Dyadic.equiv_trans
            (Dyadic.equiv_mul (Dyadic.equiv_refl u) (dotDyadic_addScaledRow (d * c) ar row full har)) ?_
          refine Dyadic.equiv_trans (Dyadic.left_distrib u _ _) ?_
          refine Dyadic.equiv_add (Dyadic.equiv_refl _) ?_
          -- u * ((d * c) * s) ≈ d * ((c * u) * s)
          refine Dyadic.equiv_trans
            (Dyadic.equiv_mul (Dyadic.equiv_refl u)
              (Dyadic.equiv_mul (Dyadic.ofInt_mul d c) (Dyadic.equiv_refl _))) ?_
          refine Dyadic.equiv_trans (Dyadic.equiv_symm (Dyadic.mul_assoc u _ _)) ?_
          refine Dyadic.equiv_trans (Dyadic.equiv_mul (Dyadic.mul_comm u _) (Dyadic.equiv_refl _)) ?_
          refine Dyadic.equiv_trans (Dyadic.equiv_mul (Dyadic.mul_assoc _ _ u) (Dyadic.equiv_refl _)) ?_
          exact Dyadic.mul_assoc _ _ _
        refine Dyadic.equiv_trans (Dyadic.equiv_add hhd (ih cs' us' hacc' hars)) ?_
        have rearr : ∀ p1 q1 p2 q2 : Dyadic,
            Dyadic.add (Dyadic.add p1 q1) (Dyadic.add p2 q2) ≈
            Dyadic.add (Dyadic.add p1 p2) (Dyadic.add q1 q2) := by
          intro p1 q1 p2 q2
          refine Dyadic.equiv_trans (Dyadic.add_assoc p1 q1 (Dyadic.add p2 q2)) ?_
          refine Dyadic.equiv_trans (Dyadic.equiv_add (Dyadic.equiv_refl p1)
            (Dyadic.equiv_trans (Dyadic.equiv_symm (Dyadic.add_assoc q1 p2 q2))
              (Dyadic.equiv_trans (Dyadic.equiv_add (Dyadic.add_comm q1 p2) (Dyadic.equiv_refl q2))
                (Dyadic.add_assoc p2 q1 q2)))) ?_
          exact Dyadic.equiv_symm (Dyadic.add_assoc p1 p2 (Dyadic.add q1 q2))
        refine Dyadic.equiv_trans (rearr _ _ _ _) ?_
        refine Dyadic.equiv_add (Dyadic.equiv_refl _) ?_
        refine Dyadic.equiv_trans (Dyadic.equiv_symm (Dyadic.left_distrib _ _ _)) ?_
        exact Dyadic.equiv_mul (Dyadic.equiv_refl _) (Dyadic.equiv_symm (Dyadic.right_distrib _ _ _))

theorem addScaledRow_length (k : Int) (a b : List Int) (h : a.length = b.length) :
    (addScaledRow k a b).length = a.length := by
  induction a generalizing b with
  | nil => cases b <;> simp [addScaledRow] at h ⊢
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys =>
      simp only [addScaledRow, List.length_cons]
      exact congrArg Nat.succ (ih ys (by simpa using h))

theorem addOuterProd_shape (d : Int) (row : List Int) (acc : List (List Int)) (cs : List Int)
    (r : Nat) (hrow : row.length = r) (hacc : acc.length = cs.length)
    (hrows : ∀ ar ∈ acc, ar.length = r) :
    (addOuterProd d row acc cs).length = cs.length ∧
    ∀ ar ∈ addOuterProd d row acc cs, ar.length = r := by
  induction acc generalizing cs with
  | nil =>
    cases cs with
    | nil => simp [addOuterProd]
    | cons _ _ => simp at hacc
  | cons ar ars ih =>
    cases cs with
    | nil => simp at hacc
    | cons c cs' =>
      have hacc' : ars.length = cs'.length := by simpa using hacc
      have har : ar.length = r := hrows ar (List.Mem.head _)
      have hars : ∀ x ∈ ars, x.length = r := fun x hx => hrows x (List.Mem.tail _ hx)
      rcases ih cs' hacc' hars with ⟨hlen, hmem⟩
      constructor
      · simp [addOuterProd, hlen]
      · intro x hx
        simp only [addOuterProd, List.mem_cons] at hx
        rcases hx with rfl | hx'
        · rw [addScaledRow_length (d * c) ar row (by rw [har, hrow]), har]
        · exact hmem x hx'

theorem reconFromFactors_shape (r : Nat) (ds : List Int) (L : List (List Int))
    (hlen : ds.length = L.length) (hL : ∀ row ∈ L, row.length = r) :
    (reconFromFactors r ds L).length = r ∧
    ∀ ar ∈ reconFromFactors r ds L, ar.length = r := by
  induction ds generalizing L with
  | nil =>
    simp only [reconFromFactors, zeroMat, List.length_replicate]
    refine ⟨trivial, ?_⟩
    intro ar har
    have hEq := List.eq_of_mem_replicate har
    subst hEq
    simp [zeroRow]
  | cons d ds' ih =>
    cases L with
    | nil => simp at hlen
    | cons row rows =>
      have hlen' : ds'.length = rows.length := by simpa using hlen
      have hrow : row.length = r := hL row (List.Mem.head _)
      have hrows : ∀ x ∈ rows, x.length = r := fun x hx => hL x (List.Mem.tail _ hx)
      rcases ih rows hlen' hrows with ⟨haccLen, haccRows⟩
      simp only [reconFromFactors]
      have hshape := addOuterProd_shape d row (reconFromFactors r ds' rows) row r hrow
        (by rw [haccLen, hrow]) haccRows
      rw [hrow] at hshape
      exact hshape

theorem reconFromFactors_nonneg (r : Nat) (ds : List Int) (L : List (List Int)) (u : List Dyadic)
    (hlen : ds.length = L.length)
    (hL : ∀ row ∈ L, row.length = r)
    (hd : ∀ d ∈ ds, 0 ≤ d) :
    Dyadic.Nonneg (quadForm (reconFromFactors r ds L) u u) := by
  induction ds generalizing L with
  | nil =>
    simp only [reconFromFactors, zeroMat]
    exact Dyadic.nonneg_of_equiv (Dyadic.equiv_symm (quadForm_zeroMat r r u u)) Dyadic.nonneg_zero
  | cons d ds' ih =>
    cases L with
    | nil => simp at hlen
    | cons row rows =>
      have hlen' : ds'.length = rows.length := by simpa using hlen
      have hrow : row.length = r := hL row (List.Mem.head _)
      have hrows : ∀ x ∈ rows, x.length = r := fun x hx => hL x (List.Mem.tail _ hx)
      have hd0 : 0 ≤ d := hd d (List.Mem.head _)
      have hds' : ∀ x ∈ ds', 0 ≤ x := fun x hx => hd x (List.Mem.tail _ hx)
      have hprev := ih rows hlen' hrows hds'
      rcases reconFromFactors_shape r ds' rows hlen' hrows with ⟨haccLen, haccRows⟩
      have hstep := quadForm_addOuterProd d row (reconFromFactors r ds' rows) row u u
        (by rw [haccLen, hrow]) (fun ar har => by rw [haccRows ar har, hrow])
      have hterm : Dyadic.Nonneg (Dyadic.mul (Dyadic.ofInt d)
          (Dyadic.mul (dotDyadic row u) (dotDyadic row u))) :=
        Dyadic.nonneg_mul (Dyadic.nonneg_ofInt hd0) (Dyadic.nonneg_sq _)
      have hsum : Dyadic.Nonneg (Dyadic.add (quadForm (reconFromFactors r ds' rows) u u)
          (Dyadic.mul (Dyadic.ofInt d) (Dyadic.mul (dotDyadic row u) (dotDyadic row u)))) :=
        Dyadic.nonneg_add hprev hterm
      exact Dyadic.nonneg_of_equiv (Dyadic.equiv_symm hstep) hsum

theorem dotDyadic_scale (k : Int) (row : List Int) (u : List Dyadic) :
    dotDyadic (row.map (fun x => k * x)) u ≈ Dyadic.mul (Dyadic.ofInt k) (dotDyadic row u) := by
  induction row generalizing u with
  | nil =>
    simp only [List.map_nil, dotDyadic]
    exact Dyadic.equiv_symm (Dyadic.mul_zero _)
  | cons x xs ih =>
    cases u with
    | nil =>
      simp only [List.map_cons, dotDyadic]
      exact Dyadic.equiv_symm (Dyadic.mul_zero _)
    | cons v vs =>
      simp only [List.map_cons, dotDyadic]
      refine Dyadic.equiv_trans
        (Dyadic.equiv_add
          (Dyadic.equiv_trans (Dyadic.equiv_mul (Dyadic.ofInt_mul k x) (Dyadic.equiv_refl v))
            (Dyadic.mul_assoc _ _ _))
          (ih vs)) ?_
      exact Dyadic.equiv_symm (Dyadic.left_distrib _ _ _)

theorem quadForm_scaleMat (k : Int) (M : List (List Int)) (us full : List Dyadic) :
    quadForm (scaleMat k M) us full ≈ Dyadic.mul (Dyadic.ofInt k) (quadForm M us full) := by
  induction M generalizing us with
  | nil =>
    simp only [scaleMat, List.map_nil, quadForm]
    exact Dyadic.equiv_symm (Dyadic.mul_zero _)
  | cons row rows ih =>
    cases us with
    | nil =>
      simp only [scaleMat, List.map_cons, quadForm]
      exact Dyadic.equiv_symm (Dyadic.mul_zero _)
    | cons u us' =>
      simp only [scaleMat, List.map_cons, quadForm]
      have hhd : Dyadic.mul u (dotDyadic (row.map (fun x => k * x)) full) ≈
          Dyadic.mul (Dyadic.ofInt k) (Dyadic.mul u (dotDyadic row full)) := by
        refine Dyadic.equiv_trans (Dyadic.equiv_mul (Dyadic.equiv_refl u) (dotDyadic_scale k row full)) ?_
        refine Dyadic.equiv_trans (Dyadic.equiv_symm (Dyadic.mul_assoc u _ _)) ?_
        refine Dyadic.equiv_trans (Dyadic.equiv_mul (Dyadic.mul_comm u _) (Dyadic.equiv_refl _)) ?_
        exact Dyadic.mul_assoc _ _ _
      exact Dyadic.equiv_trans (Dyadic.equiv_add hhd (ih us')) (Dyadic.equiv_symm (Dyadic.left_distrib _ _ _))

-- Exact expansion of a DyadicGram into a DyadicPoly

theorem eval_rowPoly (row : List Int) (basis : List Mono) (env : Nat → Dyadic) :
    Poly.eval (rowPoly row basis) env = dotDyadic row (basis.map (Mono.eval · env)) := by
  induction row generalizing basis with
  | nil => rfl
  | cons c cs ih =>
    cases basis with
    | nil => rfl
    | cons m ms =>
      simp only [rowPoly, Poly.eval, List.map_cons, dotDyadic, ih]

theorem eval_mulMonoPoly (m : Mono) (p : Poly) (env : Nat → Dyadic) :
    Poly.eval (mulMonoPoly m p) env ≈ Dyadic.mul (Mono.eval m env) (Poly.eval p env) := by
  induction p with
  | nil =>
    simp only [mulMonoPoly, List.map_nil, Poly.eval]
    exact Dyadic.equiv_symm (Dyadic.mul_zero _)
  | cons hd tl ih =>
    rcases hd with ⟨m', c⟩
    simp only [mulMonoPoly, List.map_cons, Poly.eval]
    have hhd : Dyadic.mul (Dyadic.ofInt c) (Mono.eval (Mono.mul m m') env) ≈
        Dyadic.mul (Mono.eval m env) (Dyadic.mul (Dyadic.ofInt c) (Mono.eval m' env)) := by
      refine Dyadic.equiv_trans (Dyadic.equiv_mul (Dyadic.equiv_refl _) (Mono.eval_mul m m' env)) ?_
      refine Dyadic.equiv_trans (Dyadic.equiv_symm (Dyadic.mul_assoc _ _ _)) ?_
      refine Dyadic.equiv_trans (Dyadic.equiv_mul (Dyadic.mul_comm _ _) (Dyadic.equiv_refl _)) ?_
      exact Dyadic.mul_assoc _ _ _
    exact Dyadic.equiv_trans (Dyadic.equiv_add hhd ih) (Dyadic.equiv_symm (Dyadic.left_distrib _ _ _))

theorem eval_gramPolyRaw (G : List (List Int)) (bs fullBasis : List Mono) (env : Nat → Dyadic) :
    Poly.eval (gramPolyRaw G bs fullBasis) env ≈
    quadForm G (bs.map (Mono.eval · env)) (fullBasis.map (Mono.eval · env)) := by
  induction G generalizing bs with
  | nil => exact Dyadic.equiv_refl _
  | cons row rows ih =>
    cases bs with
    | nil => exact Dyadic.equiv_refl _
    | cons m ms =>
      simp only [gramPolyRaw, List.map_cons, quadForm]
      refine Dyadic.equiv_trans (Poly.append_eval _ _ env) ?_
      refine Dyadic.equiv_add ?_ (ih ms)
      refine Dyadic.equiv_trans (eval_mulMonoPoly m (rowPoly row fullBasis) env) ?_
      rw [eval_rowPoly]
      exact Dyadic.equiv_refl _

/-- **Meta-Theorem 1 (Gram PSD Soundness):**
Any pure-data `DyadicGram` passing `checkPSD` evaluates to a nonnegative dyadic value
on EVERY assignment `env : Nat → Dyadic`. -/
theorem psd_sound (g : DyadicGram) (hchk : checkPSD g = true) (env : Nat → Dyadic) :
    Dyadic.Nonneg (DyadicPoly.eval (toDyadicPoly g) env) := by
  unfold checkPSD at hchk
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hlenDL⟩, hLrows⟩, hdiag⟩, hrecon⟩
  rw [Dyadic.pow2Int_eq] at hrecon
  let u := g.basis.map (Mono.eval · env)
  have hnnRecon : Dyadic.Nonneg (quadForm (reconFromFactors g.basis.length g.diag g.L) u u) :=
    reconFromFactors_nonneg g.basis.length g.diag g.L u hlenDL hLrows hdiag
  rw [← hrecon] at hnnRecon
  have hsc : Dyadic.Nonneg (Dyadic.mul (Dyadic.ofInt ((2 : Int) ^ g.scale)) (quadForm g.G u u)) :=
    Dyadic.nonneg_of_equiv (quadForm_scaleMat _ g.G u u) hnnRecon
  have hqf : Dyadic.Nonneg (quadForm g.G u u) := Dyadic.nonneg_of_scale_pow2 g.scale hsc
  have hraw : Dyadic.Nonneg (Poly.eval (gramPolyRaw g.G g.basis g.basis) env) :=
    Dyadic.nonneg_of_equiv (Dyadic.equiv_symm (eval_gramPolyRaw g.G g.basis g.basis env)) hqf
  have hnorm : Dyadic.Nonneg (Poly.eval (Poly.norm (gramPolyRaw g.G g.basis g.basis)) env) :=
    Dyadic.nonneg_of_equiv (Dyadic.equiv_symm (Poly.eval_norm _ env)) hraw
  exact Dyadic.nonneg_divPow2 g.shift hnorm


-- ============================================================================
-- Section 4: Exact Dyadic Schmüdgen-Farkas Positivstellensatz Compiler
-- ============================================================================

end Gram

namespace FarkasSOS

def checkRefutation (negMant : Int) (negShift : Nat)
    (ineqs eqs : List DyadicPoly) (cert : FarkasSOSCert) : Bool :=
  decide (negMant < 0) && check (DyadicPoly.const negMant negShift) ineqs eqs cert

theorem prodIneqs_nonneg (ineqs : List DyadicPoly) (idxs : List Nat) (p : DyadicPoly)
    (env : Nat → Dyadic)
    (hineq : ∀ g ∈ ineqs, Dyadic.Nonneg (DyadicPoly.eval g env))
    (hprod : prodIneqs ineqs idxs = some p) :
    Dyadic.Nonneg (DyadicPoly.eval p env) := by
  induction idxs generalizing p with
  | nil =>
    simp only [prodIneqs, Option.some.injEq] at hprod
    subst hprod
    exact Dyadic.nonneg_of_equiv (Dyadic.equiv_symm (DyadicPoly.eval_one env))
      (Dyadic.nonneg_ofInt (by omega))
  | cons idx rest ih =>
    simp only [prodIneqs] at hprod
    cases hget : ineqs[idx]? with
    | none => simp [hget] at hprod
    | some g =>
      cases hrest : prodIneqs ineqs rest with
      | none => simp [hget, hrest] at hprod
      | some q =>
        simp only [hget, hrest, Option.some.injEq] at hprod
        subst hprod
        have hgMem : g ∈ ineqs := List.mem_of_getElem? hget
        have hgNN : Dyadic.Nonneg (DyadicPoly.eval g env) := hineq g hgMem
        have hqNN : Dyadic.Nonneg (DyadicPoly.eval q env) := ih q hrest
        exact Dyadic.nonneg_of_equiv (Dyadic.equiv_symm (DyadicPoly.eval_mul g q env))
          (Dyadic.nonneg_mul hgNN hqNN)

theorem sumIneqProds_nonneg (ineqs : List DyadicPoly) (prods : List (List Nat × DyadicGram))
    (s : DyadicPoly) (env : Nat → Dyadic)
    (hineq : ∀ g ∈ ineqs, Dyadic.Nonneg (DyadicPoly.eval g env))
    (hsum : sumIneqProds ineqs prods = some s) :
    Dyadic.Nonneg (DyadicPoly.eval s env) := by
  induction prods generalizing s with
  | nil =>
    simp only [sumIneqProds, Option.some.injEq] at hsum
    subst hsum
    exact Dyadic.nonneg_zero
  | cons hd tl ih =>
    rcases hd with ⟨idxs, gr⟩
    simp only [sumIneqProds] at hsum
    cases hpsd : Gram.checkPSD gr with
    | false => simp [hpsd] at hsum
    | true =>
      simp only [hpsd, ↓reduceIte] at hsum
      cases hp : prodIneqs ineqs idxs with
      | none => simp [hp] at hsum
      | some p =>
        cases hacc : sumIneqProds ineqs tl with
        | none => simp [hp, hacc] at hsum
        | some acc =>
          simp only [hp, hacc, Option.some.injEq] at hsum
          subst hsum
          have hgrNN := Gram.psd_sound gr hpsd env
          have hpNN := prodIneqs_nonneg ineqs idxs p env hineq hp
          have haccNN := ih acc hacc
          have hmulNN := Dyadic.nonneg_of_equiv (Dyadic.equiv_symm (DyadicPoly.eval_mul _ _ env))
            (Dyadic.nonneg_mul hgrNN hpNN)
          exact Dyadic.nonneg_of_equiv (Dyadic.equiv_symm (DyadicPoly.eval_add _ _ env))
            (Dyadic.nonneg_add hmulNN haccNN)

theorem sumEqCofacts_zero (qs hs : List DyadicPoly) (s : DyadicPoly) (env : Nat → Dyadic)
    (heq : ∀ h ∈ hs, Dyadic.IsZero (DyadicPoly.eval h env))
    (hsum : sumEqCofacts qs hs = some s) :
    Dyadic.IsZero (DyadicPoly.eval s env) := by
  induction qs generalizing hs s with
  | nil =>
    cases hs with
    | nil =>
      simp only [sumEqCofacts, Option.some.injEq] at hsum
      subst hsum
      rfl
    | cons _ _ => simp [sumEqCofacts] at hsum
  | cons q qs' ih =>
    cases hs with
    | nil => simp [sumEqCofacts] at hsum
    | cons h hs' =>
      simp only [sumEqCofacts] at hsum
      cases hacc : sumEqCofacts qs' hs' with
      | none => simp [hacc] at hsum
      | some acc =>
        simp only [hacc, Option.some.injEq] at hsum
        subst hsum
        have hh0 : Dyadic.IsZero (DyadicPoly.eval h env) := heq h (List.Mem.head _)
        have hacc0 : Dyadic.IsZero (DyadicPoly.eval acc env) :=
          ih hs' acc (fun x hx => heq x (List.Mem.tail _ hx)) hacc
        have hmul0 : Dyadic.IsZero (DyadicPoly.eval (DyadicPoly.mul q h) env) := by
          have hev := DyadicPoly.eval_mul q h env
          have hz : Dyadic.IsZero (Dyadic.mul (DyadicPoly.eval q env) (DyadicPoly.eval h env)) := by
            unfold Dyadic.IsZero Dyadic.mul at *
            simp [hh0]
          exact Dyadic.isZero_of_equiv (Dyadic.equiv_symm hev) hz
        have hadd0 : Dyadic.IsZero (Dyadic.add (DyadicPoly.eval (DyadicPoly.mul q h) env)
            (DyadicPoly.eval acc env)) := by
          unfold Dyadic.IsZero Dyadic.add at *
          simp [hmul0, hacc0]
        exact Dyadic.isZero_of_equiv (Dyadic.equiv_symm (DyadicPoly.eval_add _ _ env)) hadd0

/-- **Meta-Theorem 2 (Exact Dyadic Schmüdgen-Farkas Positivstellensatz Soundness):**
A finite certificate passing `FarkasSOS.check` lifts to a universally quantified inequality
over ALL `env : Nat → Dyadic`. -/
theorem sound (target : DyadicPoly) (ineqs eqs : List DyadicPoly) (cert : FarkasSOSCert)
    (hchk : check target ineqs eqs cert = true)
    (env : Nat → Dyadic)
    (hineq : ∀ g ∈ ineqs, Dyadic.Nonneg (DyadicPoly.eval g env))
    (heq : ∀ h ∈ eqs, Dyadic.IsZero (DyadicPoly.eval h env)) :
    Dyadic.Nonneg (DyadicPoly.eval target env) := by
  unfold check at hchk
  cases hpsd : Gram.checkPSD cert.mainGram with
  | false => simp [hpsd] at hchk
  | true =>
    simp only [hpsd, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hchk
    cases hsi : sumIneqProds ineqs cert.ineqProds with
    | none => simp [hsi] at hchk
    | some sIneq =>
      cases hse : sumEqCofacts cert.eqCofacts eqs with
      | none => simp [hsi, hse] at hchk
      | some sEq =>
        simp only [hsi, hse] at hchk
        have hMainNN := Gram.psd_sound cert.mainGram hpsd env
        have hIneqNN := sumIneqProds_nonneg ineqs cert.ineqProds sIneq env hineq hsi
        have hEqZero := sumEqCofacts_zero cert.eqCofacts eqs sEq env heq hse
        have hEqNN : Dyadic.Nonneg (DyadicPoly.eval sEq env) := by
          unfold Dyadic.Nonneg Dyadic.IsZero at *
          omega
        have hAdd1NN := Dyadic.nonneg_of_equiv (Dyadic.equiv_symm (DyadicPoly.eval_add sIneq sEq env))
          (Dyadic.nonneg_add hIneqNN hEqNN)
        have hRhsNN := Dyadic.nonneg_of_equiv
          (Dyadic.equiv_symm (DyadicPoly.eval_add (Gram.toDyadicPoly cert.mainGram) _ env))
          (Dyadic.nonneg_add hMainNN hAdd1NN)
        exact Dyadic.nonneg_of_equiv (Dyadic.equiv_symm (DyadicPoly.eq_sound hchk env)) hRhsNN

/-- **Meta-Theorem 2b (Integer Specialization):** Universal inequality over `env : Nat → Int`. -/
theorem sound_int (target : DyadicPoly) (ineqs eqs : List DyadicPoly) (cert : FarkasSOSCert)
    (hchk : check target ineqs eqs cert = true)
    (env : Nat → Int)
    (hineq : ∀ g ∈ ineqs, 0 ≤ Poly.evalInt g.poly env)
    (heq : ∀ h ∈ eqs, Poly.evalInt h.poly env = 0) :
    0 ≤ Poly.evalInt target.poly env := by
  have h := sound target ineqs eqs cert hchk (fun i => Dyadic.ofInt (env i))
    (fun g hg => by rw [DyadicPoly.eval_ofInt]; exact hineq g hg)
    (fun h hh => by rw [DyadicPoly.eval_ofInt]; exact heq h hh)
  rw [DyadicPoly.eval_ofInt] at h
  exact h

/-- **Meta-Theorem 2c (Exact Dyadic Positivstellensatz / Farkas Refutation Soundness):**
Certifying a strictly negative constant proves the constraint system is universally infeasible. -/
theorem refutation_sound (negMant : Int) (negShift : Nat)
    (ineqs eqs : List DyadicPoly) (cert : FarkasSOSCert)
    (hchk : checkRefutation negMant negShift ineqs eqs cert = true)
    (env : Nat → Dyadic) :
    ¬ ((∀ g ∈ ineqs, Dyadic.Nonneg (DyadicPoly.eval g env)) ∧
       (∀ h ∈ eqs, Dyadic.IsZero (DyadicPoly.eval h env))) := by
  unfold checkRefutation at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
  rcases hchk with ⟨hneg, hsos⟩
  rintro ⟨hineq, heq⟩
  have hnn := sound (DyadicPoly.const negMant negShift) ineqs eqs cert hsos env hineq heq
  have hconst := Dyadic.nonneg_of_equiv (DyadicPoly.eval_const negMant negShift env) hnn
  exact Dyadic.not_nonneg_neg_const hneg hconst


-- ============================================================================
-- Section 5: Infinite-Dimensional Lifting Engines (Finite Cert -> ∀ n ≥ 1)
-- ============================================================================

end FarkasSOS

/-- Open-chain window embedding: variables `< paramCount` are global parameters,
and variables `paramCount + j` read `x (i + j)`. -/
def openWin (paramCount : Nat) (params x : Nat → Dyadic) (i : Nat) : Nat → Dyadic :=
  fun v => if v < paramCount then params v else x (i + (v - paramCount))

theorem sumDyadic_ofInt (f : Nat → Int) (m : Nat) :
    sumDyadic (fun i => Dyadic.ofInt (f i)) m = Dyadic.ofInt (sumInt f m) := by
  induction m with
  | zero => rfl
  | succ k ih =>
    simp only [sumDyadic, sumInt]
    rw [ih]
    simp only [Dyadic.add, Dyadic.ofInt, Int.pow_zero, Int.mul_one, Nat.add_zero]

theorem sumDyadic_divPow2 (f : Nat → Int) (s m : Nat) :
    sumDyadic (fun i => ⟨f i, s⟩) m ≈ ⟨sumInt f m, s⟩ := by
  induction m with
  | zero => simp [sumDyadic, sumInt, Dyadic.zero, Dyadic.Equiv]
  | succ k ih =>
    simp only [sumDyadic, sumInt]
    have hadd : Dyadic.add ⟨sumInt f k, s⟩ ⟨f k, s⟩ ≈ ⟨sumInt f k + f k, s⟩ := by
      unfold Dyadic.Equiv Dyadic.add
      simp only [Int.pow_add]
      rw [Int.add_mul, Int.add_mul]
      congr 1
      · simp only [Int.mul_assoc]
      · simp only [Int.mul_assoc]
    exact Dyadic.equiv_trans (Dyadic.equiv_add ih (Dyadic.equiv_refl _)) hadd

theorem sumDyadic_congr {f g : Nat → Dyadic} (m : Nat) (h : ∀ i, i < m → f i ≈ g i) :
    sumDyadic f m ≈ sumDyadic g m := by
  induction m with
  | zero => exact Dyadic.equiv_refl _
  | succ k ih =>
    simp only [sumDyadic]
    exact Dyadic.equiv_add (ih (fun i hi => h i (Nat.lt_succ_of_lt hi))) (h k (Nat.lt_succ_self k))

theorem sumDyadic_add (f g : Nat → Dyadic) (m : Nat) :
    sumDyadic (fun i => Dyadic.add (f i) (g i)) m ≈
    Dyadic.add (sumDyadic f m) (sumDyadic g m) := by
  induction m with
  | zero =>
    simp only [sumDyadic]
    exact Dyadic.equiv_symm (Dyadic.add_zero _)
  | succ k ih =>
    simp only [sumDyadic]
    refine Dyadic.equiv_trans (Dyadic.equiv_add ih (Dyadic.equiv_refl _)) ?_
    -- (A + B) + (a + b) ≈ (A + a) + (B + b)
    have rearr : ∀ A B a b : Dyadic,
        Dyadic.add (Dyadic.add A B) (Dyadic.add a b) ≈
        Dyadic.add (Dyadic.add A a) (Dyadic.add B b) := by
      intro A B a b
      refine Dyadic.equiv_trans (Dyadic.add_assoc A B (Dyadic.add a b)) ?_
      refine Dyadic.equiv_trans (Dyadic.equiv_add (Dyadic.equiv_refl A)
        (Dyadic.equiv_trans (Dyadic.equiv_symm (Dyadic.add_assoc B a b))
          (Dyadic.equiv_trans (Dyadic.equiv_add (Dyadic.add_comm B a) (Dyadic.equiv_refl b))
            (Dyadic.add_assoc a B b)))) ?_
      exact Dyadic.equiv_symm (Dyadic.add_assoc A a (Dyadic.add B b))
    exact rearr _ _ _ _

theorem sumDyadic_nonneg {f : Nat → Dyadic} (m : Nat) (h : ∀ i, i < m → Dyadic.Nonneg (f i)) :
    Dyadic.Nonneg (sumDyadic f m) := by
  induction m with
  | zero => exact Dyadic.nonneg_zero
  | succ k ih =>
    simp only [sumDyadic]
    exact Dyadic.nonneg_add (ih (fun i hi => h i (Nat.lt_succ_of_lt hi))) (h k (Nat.lt_succ_self k))

theorem sumDyadic_telescope (F : Nat → Dyadic) (m : Nat) :
    sumDyadic (fun i => Dyadic.sub (F i) (F (i + 1))) m ≈ Dyadic.sub (F 0) (F m) := by
  induction m with
  | zero =>
    simp only [sumDyadic, Dyadic.sub]
    exact Dyadic.equiv_symm (Dyadic.add_neg_self (F 0))
  | succ k ih =>
    simp only [sumDyadic]
    refine Dyadic.equiv_trans (Dyadic.equiv_add ih (Dyadic.equiv_refl _)) ?_
    unfold Dyadic.sub
    -- (F 0 + -F k) + (F k + -F (k+1)) ≈ F 0 + -F (k+1)
    refine Dyadic.equiv_trans (Dyadic.add_assoc (F 0) (Dyadic.neg (F k)) _) ?_
    refine Dyadic.equiv_add (Dyadic.equiv_refl (F 0)) ?_
    refine Dyadic.equiv_trans (Dyadic.equiv_symm (Dyadic.add_assoc (Dyadic.neg (F k)) (F k) _)) ?_
    refine Dyadic.equiv_trans
      (Dyadic.equiv_add (Dyadic.equiv_trans (Dyadic.add_comm _ _) (Dyadic.add_neg_self (F k)))
        (Dyadic.equiv_refl _)) ?_
    exact Dyadic.zero_add _

theorem cyclicWin_shift (paramCount n : Nat) (params x : Nat → Dyadic) (i v : Nat) :
    cyclicWin paramCount n params x i (if v < paramCount then v else v + 1) =
    cyclicWin paramCount n params x (i + 1) v := by
  unfold cyclicWin
  by_cases hv : v < paramCount
  · simp [hv]
  · have hv1 : ¬ (v + 1 < paramCount) := by omega
    have hsub : v + 1 - paramCount = (v - paramCount) + 1 := by omega
    have hadd : i + ((v - paramCount) + 1) = (i + 1) + (v - paramCount) := by omega
    simp [hv, hv1, hsub, hadd]

theorem cyclicWin_mod (paramCount n : Nat) (params x : Nat → Dyadic) (i : Nat) :
    cyclicWin paramCount n params x (i % n) = cyclicWin paramCount n params x i := by
  funext v
  unfold cyclicWin
  by_cases hv : v < paramCount
  · simp [hv]
  · simp only [hv, ↓reduceIte]
    have hmod : (i % n + (v - paramCount)) % n = (i + (v - paramCount)) % n := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    rw [hmod]

theorem openWin_shift (paramCount : Nat) (params x : Nat → Dyadic) (i v : Nat) :
    openWin paramCount params x i (if v < paramCount then v else v + 1) =
    openWin paramCount params x (i + 1) v := by
  unfold openWin
  by_cases hv : v < paramCount
  · simp [hv]
  · have hv1 : ¬ (v + 1 < paramCount) := by omega
    have hsub : v + 1 - paramCount = (v - paramCount) + 1 := by omega
    have hadd : i + ((v - paramCount) + 1) = (i + 1) + (v - paramCount) := by omega
    simp [hv, hv1, hsub, hadd]

/-- **Meta-Theorem 3A (Cyclic Infinite-Dimensional Telescoping Flux Soundness):**
A SINGLE finite `CyclicFluxCert` checked by `decide` proves nonnegativity of the cyclic
stencil sum for EVERY dimension `n ≥ 1`, EVERY global parameter assignment `params`,
and EVERY vector `x : Nat → Dyadic` satisfying the local constraints. -/
theorem cyclic_flux_sound (paramCount : Nat) (stencil : DyadicPoly)
    (localIneqs localEqs : List DyadicPoly) (cert : CyclicFluxCert)
    (hchk : checkCyclicFlux paramCount stencil localIneqs localEqs cert = true)
    (n : Nat) (hn : 1 ≤ n) (params x : Nat → Dyadic)
    (hineq : ∀ i, i < n → ∀ g ∈ localIneqs,
      Dyadic.Nonneg (DyadicPoly.eval g (cyclicWin paramCount n params x i)))
    (heq : ∀ i, i < n → ∀ h ∈ localEqs,
      Dyadic.IsZero (DyadicPoly.eval h (cyclicWin paramCount n params x i))) :
    Dyadic.Nonneg (sumDyadic (fun i => DyadicPoly.eval stencil (cyclicWin paramCount n params x i)) n) := by
  let shifted := DyadicPoly.sub (DyadicPoly.add stencil cert.flux)
                   (DyadicPoly.shiftFrom paramCount 1 cert.flux)
  let P : Nat → Dyadic := fun i => DyadicPoly.eval stencil (cyclicWin paramCount n params x i)
  let F : Nat → Dyadic := fun i => DyadicPoly.eval cert.flux (cyclicWin paramCount n params x i)
  -- Step 1: Every shifted site i < n is nonnegative by Meta-Theorem 2
  have hsite : ∀ i, i < n → Dyadic.Nonneg (Dyadic.add (P i) (Dyadic.sub (F i) (F (i + 1)))) := by
    intro i hi
    have hnn := FarkasSOS.sound shifted localIneqs localEqs cert.sosCert hchk
      (cyclicWin paramCount n params x i) (hineq i hi) (heq i hi)
    have hsh : DyadicPoly.eval (DyadicPoly.shiftFrom paramCount 1 cert.flux)
        (cyclicWin paramCount n params x i) ≈ F (i + 1) := by
      refine Dyadic.equiv_trans (DyadicPoly.eval_shiftFrom paramCount 1 cert.flux _) ?_
      have hfn : (fun v => cyclicWin paramCount n params x i (if v < paramCount then v else v + 1)) =
                 cyclicWin paramCount n params x (i + 1) := by
        funext v; exact cyclicWin_shift paramCount n params x i v
      rw [hfn]
      exact Dyadic.equiv_refl _
    have hev : DyadicPoly.eval shifted (cyclicWin paramCount n params x i) ≈
        Dyadic.add (P i) (Dyadic.sub (F i) (F (i + 1))) := by
      refine Dyadic.equiv_trans (DyadicPoly.eval_sub _ _ _) ?_
      refine Dyadic.equiv_trans (Dyadic.equiv_sub (DyadicPoly.eval_add _ _ _) hsh) ?_
      exact Dyadic.equiv_symm (Dyadic.add_sub_swap (P i) (F i) (F (i + 1)))
    exact Dyadic.nonneg_of_equiv hev hnn
  -- Step 2: Sum over i = 0..n-1 is nonnegative
  have hsumNN : Dyadic.Nonneg (sumDyadic (fun i => Dyadic.add (P i) (Dyadic.sub (F i) (F (i + 1)))) n) :=
    sumDyadic_nonneg n hsite
  -- Step 3: Cyclic telescoping: F n = F 0 since n % n = 0
  have hFn : F n = F 0 := by
    show DyadicPoly.eval cert.flux (cyclicWin paramCount n params x n) =
         DyadicPoly.eval cert.flux (cyclicWin paramCount n params x 0)
    rw [← cyclicWin_mod paramCount n params x n, Nat.mod_self]
  have htel : sumDyadic (fun i => Dyadic.sub (F i) (F (i + 1))) n ≈ Dyadic.zero := by
    refine Dyadic.equiv_trans (sumDyadic_telescope F n) ?_
    rw [hFn]
    exact Dyadic.add_neg_self (F 0)
  have hsplit : sumDyadic (fun i => Dyadic.add (P i) (Dyadic.sub (F i) (F (i + 1)))) n ≈
      sumDyadic P n := by
    refine Dyadic.equiv_trans (sumDyadic_add P (fun i => Dyadic.sub (F i) (F (i + 1))) n) ?_
    exact Dyadic.equiv_trans (Dyadic.equiv_add (Dyadic.equiv_refl _) htel) (Dyadic.add_zero _)
  have _ := hn
  exact Dyadic.nonneg_of_equiv hsplit hsumNN

/-- **Meta-Theorem 3B (Integer Cyclic Specialization):**
Direct universally quantified `Int` sum theorem for ALL `n ≥ 1`, `params`, `x : Nat → Int`. -/
theorem cyclic_flux_sound_int (paramCount : Nat) (stencil : DyadicPoly)
    (localIneqs localEqs : List DyadicPoly) (cert : CyclicFluxCert)
    (hchk : checkCyclicFlux paramCount stencil localIneqs localEqs cert = true)
    (n : Nat) (hn : 1 ≤ n) (params x : Nat → Int)
    (hineq : ∀ i, i < n → ∀ g ∈ localIneqs,
      0 ≤ Poly.evalInt g.poly (fun v => if v < paramCount then params v else x ((i + (v - paramCount)) % n)))
    (heq : ∀ i, i < n → ∀ h ∈ localEqs,
      Poly.evalInt h.poly (fun v => if v < paramCount then params v else x ((i + (v - paramCount)) % n)) = 0) :
    0 ≤ sumInt (fun i => Poly.evalInt stencil.poly
      (fun v => if v < paramCount then params v else x ((i + (v - paramCount)) % n))) n := by
  have hwin : ∀ i, cyclicWin paramCount n (fun v => Dyadic.ofInt (params v))
      (fun v => Dyadic.ofInt (x v)) i =
      fun v => Dyadic.ofInt (if v < paramCount then params v else x ((i + (v - paramCount)) % n)) := by
    intro i; funext v; unfold cyclicWin; split <;> rfl
  have hnn := cyclic_flux_sound paramCount stencil localIneqs localEqs cert hchk n hn
    (fun v => Dyadic.ofInt (params v)) (fun v => Dyadic.ofInt (x v))
    (fun i hi g hg => by rw [hwin i, DyadicPoly.eval_ofInt]; exact hineq i hi g hg)
    (fun i hi h hh => by rw [hwin i, DyadicPoly.eval_ofInt]; exact heq i hi h hh)
  have heqSum : sumDyadic (fun i => DyadicPoly.eval stencil
      (cyclicWin paramCount n (fun v => Dyadic.ofInt (params v)) (fun v => Dyadic.ofInt (x v)) i)) n ≈
      ⟨sumInt (fun i => Poly.evalInt stencil.poly
        (fun v => if v < paramCount then params v else x ((i + (v - paramCount)) % n))) n, stencil.shift⟩ := by
    have hcongr := sumDyadic_congr (f := fun i => DyadicPoly.eval stencil
        (cyclicWin paramCount n (fun v => Dyadic.ofInt (params v)) (fun v => Dyadic.ofInt (x v)) i))
      (g := fun i => ⟨Poly.evalInt stencil.poly
        (fun v => if v < paramCount then params v else x ((i + (v - paramCount)) % n)), stencil.shift⟩)
      n (fun i _ => by rw [hwin i, DyadicPoly.eval_ofInt]; exact Dyadic.equiv_refl _)
    exact Dyadic.equiv_trans hcongr (sumDyadic_divPow2 _ stencil.shift n)
  exact Dyadic.nonneg_of_equiv heqSum hnn

/-- Pure-data infinite-dimensional open-chain telescoping flux certificate. -/
structure OpenFluxCert where
  flux      : DyadicPoly
  bulkCert  : FarkasSOSCert
  leftCert  : FarkasSOSCert
  rightCert : FarkasSOSCert
deriving DecidableEq, Repr

def checkOpenFlux (paramCount : Nat) (stencil bLeft bRight : DyadicPoly)
    (localIneqs localEqs : List DyadicPoly) (cert : OpenFluxCert) : Bool :=
  let shifted := DyadicPoly.sub (DyadicPoly.add stencil cert.flux)
                  (DyadicPoly.shiftFrom paramCount 1 cert.flux)
  FarkasSOS.check shifted localIneqs localEqs cert.bulkCert &&
  FarkasSOS.check (DyadicPoly.sub bLeft cert.flux) localIneqs localEqs cert.leftCert &&
  FarkasSOS.check (DyadicPoly.add bRight cert.flux) localIneqs localEqs cert.rightCert

/-- **Meta-Theorem 3C (Open-Boundary Infinite-Dimensional Telescoping Flux Soundness):**
A SINGLE finite `OpenFluxCert` proves nonnegativity of
`bLeft(0) + ∑_{i=0}^{n-1} stencil(i) + bRight(n)` for EVERY `n ≥ 1` and `x : Nat → Dyadic`. -/
theorem open_flux_sound (paramCount : Nat) (stencil bLeft bRight : DyadicPoly)
    (localIneqs localEqs : List DyadicPoly) (cert : OpenFluxCert)
    (hchk : checkOpenFlux paramCount stencil bLeft bRight localIneqs localEqs cert = true)
    (n : Nat) (params x : Nat → Dyadic)
    (hineq : ∀ i, i ≤ n → ∀ g ∈ localIneqs,
      Dyadic.Nonneg (DyadicPoly.eval g (openWin paramCount params x i)))
    (heq : ∀ i, i ≤ n → ∀ h ∈ localEqs,
      Dyadic.IsZero (DyadicPoly.eval h (openWin paramCount params x i))) :
    Dyadic.Nonneg (Dyadic.add (DyadicPoly.eval bLeft (openWin paramCount params x 0))
      (Dyadic.add (sumDyadic (fun i => DyadicPoly.eval stencil (openWin paramCount params x i)) n)
                  (DyadicPoly.eval bRight (openWin paramCount params x n)))) := by
  unfold checkOpenFlux at hchk
  simp only [Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨hbulk, hleft⟩, hright⟩
  let P : Nat → Dyadic := fun i => DyadicPoly.eval stencil (openWin paramCount params x i)
  let F : Nat → Dyadic := fun i => DyadicPoly.eval cert.flux (openWin paramCount params x i)
  let BL : Dyadic := DyadicPoly.eval bLeft (openWin paramCount params x 0)
  let BR : Dyadic := DyadicPoly.eval bRight (openWin paramCount params x n)
  -- Left boundary: BL - F 0 ≥ 0
  have hL : Dyadic.Nonneg (Dyadic.sub BL (F 0)) := by
    have hnn := FarkasSOS.sound _ localIneqs localEqs cert.leftCert hleft
      (openWin paramCount params x 0) (hineq 0 (Nat.zero_le n)) (heq 0 (Nat.zero_le n))
    exact Dyadic.nonneg_of_equiv (DyadicPoly.eval_sub bLeft cert.flux _) hnn
  -- Right boundary: BR + F n ≥ 0
  have hR : Dyadic.Nonneg (Dyadic.add BR (F n)) := by
    have hnn := FarkasSOS.sound _ localIneqs localEqs cert.rightCert hright
      (openWin paramCount params x n) (hineq n (Nat.le_refl n)) (heq n (Nat.le_refl n))
    exact Dyadic.nonneg_of_equiv (DyadicPoly.eval_add bRight cert.flux _) hnn
  -- Bulk sites: P i + (F i - F (i+1)) ≥ 0
  have hsite : ∀ i, i < n → Dyadic.Nonneg (Dyadic.add (P i) (Dyadic.sub (F i) (F (i + 1)))) := by
    intro i hi
    have hnn := FarkasSOS.sound _ localIneqs localEqs cert.bulkCert hbulk
      (openWin paramCount params x i) (hineq i (Nat.le_of_lt hi)) (heq i (Nat.le_of_lt hi))
    have hsh : DyadicPoly.eval (DyadicPoly.shiftFrom paramCount 1 cert.flux)
        (openWin paramCount params x i) ≈ F (i + 1) := by
      refine Dyadic.equiv_trans (DyadicPoly.eval_shiftFrom paramCount 1 cert.flux _) ?_
      have hfn : (fun v => openWin paramCount params x i (if v < paramCount then v else v + 1)) =
                 openWin paramCount params x (i + 1) := by
        funext v; exact openWin_shift paramCount params x i v
      rw [hfn]
      exact Dyadic.equiv_refl _
    have hev : DyadicPoly.eval (DyadicPoly.sub (DyadicPoly.add stencil cert.flux)
        (DyadicPoly.shiftFrom paramCount 1 cert.flux)) (openWin paramCount params x i) ≈
        Dyadic.add (P i) (Dyadic.sub (F i) (F (i + 1))) := by
      refine Dyadic.equiv_trans (DyadicPoly.eval_sub _ _ _) ?_
      refine Dyadic.equiv_trans (Dyadic.equiv_sub (DyadicPoly.eval_add _ _ _) hsh) ?_
      exact Dyadic.equiv_symm (Dyadic.add_sub_swap (P i) (F i) (F (i + 1)))
    exact Dyadic.nonneg_of_equiv hev hnn
  -- Total sum: (BL - F 0) + (∑ P + (F 0 - F n)) + (BR + F n) ≈ BL + (∑ P + BR)
  have htotNN : Dyadic.Nonneg
      (Dyadic.add (Dyadic.sub BL (F 0))
        (Dyadic.add (sumDyadic (fun i => Dyadic.add (P i) (Dyadic.sub (F i) (F (i + 1)))) n)
                    (Dyadic.add BR (F n)))) :=
    Dyadic.nonneg_add hL (Dyadic.nonneg_add (sumDyadic_nonneg n hsite) hR)
  have hbulkEq : sumDyadic (fun i => Dyadic.add (P i) (Dyadic.sub (F i) (F (i + 1)))) n ≈
      Dyadic.add (sumDyadic P n) (Dyadic.sub (F 0) (F n)) :=
    Dyadic.equiv_trans (sumDyadic_add P _ n)
      (Dyadic.equiv_add (Dyadic.equiv_refl _) (sumDyadic_telescope F n))
  -- Exact telescoping cancellation of F 0 and F n
  have hcancel :
      Dyadic.add (Dyadic.sub BL (F 0))
        (Dyadic.add (Dyadic.add (sumDyadic P n) (Dyadic.sub (F 0) (F n)))
                    (Dyadic.add BR (F n))) ≈
      Dyadic.add BL (Dyadic.add (sumDyadic P n) BR) := by
    -- Simplify inner: ((S + (F0 - Fn)) + (BR + Fn)) ≈ (S + BR) + F0
    have hinner : Dyadic.add (Dyadic.add (sumDyadic P n) (Dyadic.sub (F 0) (F n)))
                             (Dyadic.add BR (F n)) ≈
                  Dyadic.add (F 0) (Dyadic.add (sumDyadic P n) BR) := by
      -- ((S + (F0 - Fn)) + (BR + Fn)) ≈ (S + BR) + ((F0 - Fn) + Fn) ≈ (S + BR) + F0 ≈ F0 + (S + BR)
      have rearr : ∀ A B C D : Dyadic,
          Dyadic.add (Dyadic.add A B) (Dyadic.add C D) ≈
          Dyadic.add (Dyadic.add A C) (Dyadic.add B D) := by
        intro A B C D
        refine Dyadic.equiv_trans (Dyadic.add_assoc A B (Dyadic.add C D)) ?_
        refine Dyadic.equiv_trans (Dyadic.equiv_add (Dyadic.equiv_refl A)
          (Dyadic.equiv_trans (Dyadic.equiv_symm (Dyadic.add_assoc B C D))
            (Dyadic.equiv_trans (Dyadic.equiv_add (Dyadic.add_comm B C) (Dyadic.equiv_refl D))
              (Dyadic.add_assoc C B D)))) ?_
        exact Dyadic.equiv_symm (Dyadic.add_assoc A C (Dyadic.add B D))
      refine Dyadic.equiv_trans (rearr _ _ _ _) ?_
      refine Dyadic.equiv_trans (Dyadic.equiv_add (Dyadic.equiv_refl _) (Dyadic.add_sub_cancel (F 0) (F n))) ?_
      exact Dyadic.add_comm _ _
    refine Dyadic.equiv_trans (Dyadic.equiv_add (Dyadic.equiv_refl _) hinner) ?_
    refine Dyadic.equiv_trans (Dyadic.equiv_symm (Dyadic.add_assoc (Dyadic.sub BL (F 0)) (F 0) _)) ?_
    exact Dyadic.equiv_add (Dyadic.add_sub_cancel BL (F 0)) (Dyadic.equiv_refl _)
  have hfull : Dyadic.add (Dyadic.sub BL (F 0))
      (Dyadic.add (sumDyadic (fun i => Dyadic.add (P i) (Dyadic.sub (F i) (F (i + 1)))) n)
                  (Dyadic.add BR (F n))) ≈
      Dyadic.add BL (Dyadic.add (sumDyadic P n) BR) :=
    Dyadic.equiv_trans
      (Dyadic.equiv_add (Dyadic.equiv_refl _) (Dyadic.equiv_add hbulkEq (Dyadic.equiv_refl _)))
      hcancel
  exact Dyadic.nonneg_of_equiv hfull htotNN

-- ============================================================================
-- Section 6: Six Flagship Infinite & Nonlinear Theorems Discharged via `decide`
-- ============================================================================

-- Helper constructors for readable Gram certificates

def constGram (mant : Int) (shift : Nat := 0) : DyadicGram :=
  { basis := [[]], shift := shift, G := [[mant]], scale := 0, diag := [mant], L := [[1]] }

def rank1Gram (basis : List Mono) (coeffs : List Int) (weight : Int := 1) (shift : Nat := 0) : DyadicGram :=
  { basis := basis
    shift := shift
    G := coeffs.map (fun ci => coeffs.map (fun cj => weight * ci * cj))
    scale := 0
    diag := [weight]
    L := [coeffs] }

-- ----------------------------------------------------------------------------
-- THEOREM 1: Infinite-Dimensional Asymmetric-Skew Quartic Cyclic Inequality
--   ∀ n ≥ 1, ∀ x : Fin n → Z[1/2] (and Z^n),
--   ∑_{i ∈ Z/nZ} ( 8 x_i^4 + 8 x_i^2 x_{i+1}^2 - 13 x_i^3 x_{i+1} + 13 x_i x_{i+1}^2 x_{i+2} ) ≥ 0
--   (i.e. c = 13/8 = 1.625, within 0.032 of irrational optimum 4√2 - 4 ≈ 1.656854;
--    local stencil is indefinite at (1,1,-1) -> -5/4 < 0; ANY 1-var flux fails;
--    27/16 is falsified at n=4, x = [-3, -2, 3, 2]!)
-- ----------------------------------------------------------------------------

def thm1_stencil : DyadicPoly :=
  { shift := 3
    poly := [([(0, 1), (1, 2), (2, 1)], (13)),
             ([(0, 2), (1, 2)], (8)),
             ([(0, 3), (1, 1)], (-13)),
             ([(0, 4)], (8))] }

def thm1_flux : DyadicPoly :=
  { shift := 6
    poly := [([(0, 1), (1, 3)], (-48)),
             ([(0, 2), (1, 2)], (-60)),
             ([(0, 3), (1, 1)], (101)),
             ([(0, 4)], (-49)),
             ([(1, 4)], (-15))] }

def thm1_gram : DyadicGram :=
  { basis := [[(0, 2)], [(0, 1), (1, 1)], [(1, 2)], [(1, 1), (2, 1)], [(2, 2)], [(0, 1), (2, 1)]]
    shift := 7
    G := [[(30), (-3), (-22), (16), (-8), (0)],
          [(-3), (52), (-48), (88), (30), (-16)],
          [(-22), (-48), (68), (-101), (-24), (16)],
          [(16), (88), (-101), (168), (48), (-30)],
          [(-8), (30), (-24), (48), (30), (0)],
          [(0), (-16), (16), (-30), (0), (16)]]
    scale := 14
    diag := [(1), (1), (1), (1), (1), (1),
             (152), (52), (344), (172), (2), (348), (30), (56), (590), (221), (94), (47), (74), (58),
             (800), (80), (292), (244), (708), (823)]
    L := [[(700), (-70), (-515), (374), (-187), (0)],
          [(0), (920), (-894), (1596), (520), (-285)],
          [(0), (0), (220), (-158), (-111), (33)],
          [(0), (0), (0), (197), (45), (-160)],
          [(0), (0), (0), (0), (413), (385)],
          [(0), (0), (0), (0), (0), (70)],
          [(1), (-1), (0), (0), (0), (0)],
          [(1), (0), (1), (0), (0), (0)],
          [(1), (0), (0), (1), (0), (0)],
          [(1), (0), (0), (0), (-1), (0)],
          [(0), (1), (-1), (0), (0), (0)],
          [(0), (1), (0), (-1), (0), (0)],
          [(0), (1), (0), (0), (1), (0)],
          [(0), (1), (0), (0), (0), (1)],
          [(0), (0), (1), (-1), (0), (0)],
          [(0), (0), (1), (0), (-1), (0)],
          [(0), (0), (1), (0), (0), (1)],
          [(0), (0), (0), (1), (1), (0)],
          [(0), (0), (0), (1), (0), (1)],
          [(0), (0), (0), (0), (1), (1)],
          [(1), (0), (0), (0), (0), (0)],
          [(0), (1), (0), (0), (0), (0)],
          [(0), (0), (1), (0), (0), (0)],
          [(0), (0), (0), (1), (0), (0)],
          [(0), (0), (0), (0), (1), (0)],
          [(0), (0), (0), (0), (0), (1)]] }

def thm1_cert : CyclicFluxCert :=
  { flux := thm1_flux, sosCert := { mainGram := thm1_gram, ineqProds := [], eqCofacts := [] } }

theorem thm1_cert_valid : checkCyclicFlux 0 thm1_stencil [] [] thm1_cert = true := by decide

theorem thm1_asym_skew_quartic_cyclic_dyadic (n : Nat) (hn : 1 ≤ n) (x : Nat → Dyadic) :
    Dyadic.Nonneg (sumDyadic (fun i => DyadicPoly.eval thm1_stencil (cyclicWin 0 n x x i)) n) :=
  cyclic_flux_sound 0 thm1_stencil [] [] thm1_cert thm1_cert_valid n hn x x
    (fun _ _ _ hg => nomatch hg) (fun _ _ _ hh => nomatch hh)

theorem thm1_asym_skew_quartic_cyclic_int (n : Nat) (hn : 1 ≤ n) (x : Nat → Int) :
    0 ≤ sumInt (asymSkewTerm x n) n := by
  have h := cyclic_flux_sound_int 0 thm1_stencil [] [] thm1_cert thm1_cert_valid n hn x x
    (fun _ _ _ hg => nomatch hg) (fun _ _ _ hh => nomatch hh)
  have hterm : ∀ i, Poly.evalInt thm1_stencil.poly
      (fun v => if v < 0 then x v else x ((i + (v - 0)) % n)) = asymSkewTerm x n i := by
    intro i
    simp only [thm1_stencil, Poly.evalInt, Mono.evalInt, asymSkewTerm, Nat.not_lt_zero, ↓reduceIte,
               Nat.sub_zero, Nat.add_zero, Int.mul_one, Int.pow_one, Int.add_zero]
    have hmul : ∀ u v w : Int,
        13 * (u * (v ^ 2 * w)) + (8 * (u ^ 2 * v ^ 2) + (-13 * (u ^ 3 * v) + 8 * u ^ 4)) =
        8 * u ^ 4 + 8 * u ^ 2 * v ^ 2 - 13 * u ^ 3 * v + 13 * u * v ^ 2 * w := by
      intro u v w
      simp only [Int.neg_mul, Int.mul_assoc]
      omega
    exact hmul (x (i % n)) (x ((i + 1) % n)) (x ((i + 2) % n))
  have hsum : ∀ m, sumInt (fun i => Poly.evalInt thm1_stencil.poly
      (fun v => if v < 0 then x v else x ((i + (v - 0)) % n))) m = sumInt (asymSkewTerm x n) m := by
    intro m; induction m with
    | zero => rfl
    | succ k ih => simp only [sumInt]; rw [ih, hterm k]
  rw [hsum n] at h
  exact h

-- ----------------------------------------------------------------------------
-- THEOREM 2: Second Independent Infinite-Dimensional Quartic Cyclic Inequality
--   ∀ n ≥ 1, ∀ x : Fin n → Z[1/2] (and Z^n),
--   ∑_{i ∈ Z/nZ} ( 4 x_i^4 + 4 x_i^2 x_{i+1}^2 - 7 x_i^3 x_{i+1}
--                  - 7 x_i x_{i+1}^2 x_{i+2} + 7 x_i^2 x_{i+1} x_{i+2} ) ≥ 0
--   (c = 7/4 = 1.75; falsified at c = 15/8 = 1.875 by n=8 integer cycle!)
-- ----------------------------------------------------------------------------

def thm2_stencil : DyadicPoly :=
  { shift := 2
    poly := [([(0, 1), (1, 2), (2, 1)], (-7)),
             ([(0, 2), (1, 1), (2, 1)], (7)),
             ([(0, 2), (1, 2)], (4)),
             ([(0, 3), (1, 1)], (-7)),
             ([(0, 4)], (4))] }

def thm2_flux : DyadicPoly :=
  { shift := 6
    poly := [([(0, 1), (1, 3)], (29)),
             ([(0, 2), (1, 2)], (-78)),
             ([(0, 3), (1, 1)], (53)),
             ([(0, 4)], (-30)),
             ([(1, 4)], (-5))] }

def thm2_gram : DyadicGram :=
  { basis := [[(0, 2)], [(0, 1), (1, 1)], [(1, 2)], [(1, 1), (2, 1)], [(2, 2)], [(0, 1), (2, 1)]]
    shift := 7
    G := [[(68), (-59), (-48), (88), (-22), (0)],
          [(-59), (68), (29), (-88), (20), (24)],
          [(-48), (29), (50), (-53), (15), (-24)],
          [(88), (-88), (-53), (126), (-29), (-20)],
          [(-22), (20), (15), (-29), (10), (0)],
          [(0), (24), (-24), (-20), (0), (44)]]
    scale := 12
    diag := [(1), (1), (1), (1), (1), (1),
             (229), (37), (20), (5), (154), (128), (64), (116), (472), (8), (36), (220), (187), (222),
             (508), (75), (651), (483), (587), (697)]
    L := [[(527), (-459), (-373), (684), (-171), (0)],
          [(0), (259), (-203), (-180), (13), (380)],
          [(0), (0), (152), (13), (2), (-139)],
          [(0), (0), (0), (119), (6), (-100)],
          [(0), (0), (0), (0), (102), (-42)],
          [(0), (0), (0), (0), (0), (59)],
          [(1), (1), (0), (0), (0), (0)],
          [(1), (0), (-1), (0), (0), (0)],
          [(1), (0), (0), (-1), (0), (0)],
          [(1), (0), (0), (0), (1), (0)],
          [(0), (1), (1), (0), (0), (0)],
          [(0), (1), (0), (1), (0), (0)],
          [(0), (1), (0), (0), (1), (0)],
          [(0), (1), (0), (0), (0), (-1)],
          [(0), (0), (1), (-1), (0), (0)],
          [(0), (0), (1), (0), (-1), (0)],
          [(0), (0), (1), (0), (0), (-1)],
          [(0), (0), (0), (1), (-1), (0)],
          [(0), (0), (0), (1), (0), (1)],
          [(0), (0), (0), (0), (1), (1)],
          [(1), (0), (0), (0), (0), (0)],
          [(0), (1), (0), (0), (0), (0)],
          [(0), (0), (1), (0), (0), (0)],
          [(0), (0), (0), (1), (0), (0)],
          [(0), (0), (0), (0), (1), (0)],
          [(0), (0), (0), (0), (0), (1)]] }

def thm2_cert : CyclicFluxCert :=
  { flux := thm2_flux, sosCert := { mainGram := thm2_gram, ineqProds := [], eqCofacts := [] } }

theorem thm2_cert_valid : checkCyclicFlux 0 thm2_stencil [] [] thm2_cert = true := by decide

def mixedQuarticTerm (x : Nat → Int) (n i : Nat) : Int :=
  let a := x (i % n)
  let b := x ((i + 1) % n)
  let c := x ((i + 2) % n)
  4 * a ^ 4 + 4 * a ^ 2 * b ^ 2 - 7 * a ^ 3 * b - 7 * a * b ^ 2 * c + 7 * a ^ 2 * b * c

theorem thm2_mixed_quartic_cyclic_int (n : Nat) (hn : 1 ≤ n) (x : Nat → Int) :
    0 ≤ sumInt (mixedQuarticTerm x n) n := by
  have h := cyclic_flux_sound_int 0 thm2_stencil [] [] thm2_cert thm2_cert_valid n hn x x
    (fun _ _ _ hg => nomatch hg) (fun _ _ _ hh => nomatch hh)
  have hterm : ∀ i, Poly.evalInt thm2_stencil.poly
      (fun v => if v < 0 then x v else x ((i + (v - 0)) % n)) = mixedQuarticTerm x n i := by
    intro i
    simp only [thm2_stencil, Poly.evalInt, Mono.evalInt, mixedQuarticTerm, Nat.not_lt_zero, ↓reduceIte,
               Nat.sub_zero, Nat.add_zero, Int.mul_one, Int.pow_one, Int.add_zero]
    have hmul : ∀ u v w : Int,
        -7 * (u * (v ^ 2 * w)) + (7 * (u ^ 2 * (v * w)) + (4 * (u ^ 2 * v ^ 2) +
          (-7 * (u ^ 3 * v) + 4 * u ^ 4))) =
        4 * u ^ 4 + 4 * u ^ 2 * v ^ 2 - 7 * u ^ 3 * v - 7 * u * v ^ 2 * w + 7 * u ^ 2 * v * w := by
      intro u v w
      simp only [Int.neg_mul, Int.mul_assoc]
      omega
    exact hmul (x (i % n)) (x ((i + 1) % n)) (x ((i + 2) % n))
  have hsum : ∀ m, sumInt (fun i => Poly.evalInt thm2_stencil.poly
      (fun v => if v < 0 then x v else x ((i + (v - 0)) % n))) m = sumInt (mixedQuarticTerm x n) m := by
    intro m; induction m with
    | zero => rfl
    | succ k ih => simp only [sumInt]; rw [ih, hterm k]
  rw [hsum n] at h
  exact h

-- ----------------------------------------------------------------------------
-- THEOREM 3A & 3B: Infinite-Dimensional Continuous Dyadic Hypercube [0,1]^n
--   3-Pattern Density Theorems (EXACTLY SHARP, using SOS + Schmüdgen-Farkas + Flux!)
-- ----------------------------------------------------------------------------

/-- Local hypercube constraints on a 3-point window `(x_0, x_1, x_2) ∈ [0,1]^3`. -/
def cubeIneqs3 : List DyadicPoly :=
  [ DyadicPoly.var 0,                                  -- 0: x0 ≥ 0
    { shift := 0, poly := [([], 1), ([(0, 1)], -1)] }, -- 1: 1 - x0 ≥ 0
    DyadicPoly.var 1,                                  -- 2: x1 ≥ 0
    { shift := 0, poly := [([], 1), ([(1, 1)], -1)] }, -- 3: 1 - x1 ≥ 0
    DyadicPoly.var 2,                                  -- 4: x2 ≥ 0
    { shift := 0, poly := [([], 1), ([(2, 1)], -1)] }  -- 5: 1 - x2 ≥ 0
  ]

theorem eval_cubeIneqs3 (n : Nat) (x : Nat → Dyadic)
    (h01 : ∀ k, Dyadic.Nonneg (x k) ∧ Dyadic.Le (x k) Dyadic.one)
    (i : Nat) :
    ∀ g ∈ cubeIneqs3, Dyadic.Nonneg (DyadicPoly.eval g (cyclicWin 0 n x x i)) := by
  have evalVar : ∀ j : Nat, DyadicPoly.eval (DyadicPoly.var j) (cyclicWin 0 n x x i) ≈
      x ((i + j) % n) := by
    intro j
    unfold DyadicPoly.eval DyadicPoly.var Poly.eval Mono.eval cyclicWin
    simp only [Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero, Dyadic.pow]
    refine Dyadic.equiv_trans (Dyadic.divPow2_zero _) ?_
    refine Dyadic.equiv_trans (Dyadic.add_zero _) ?_
    refine Dyadic.equiv_trans (Dyadic.one_mul _) ?_
    exact Dyadic.equiv_trans (Dyadic.mul_one _) (Dyadic.mul_one _)
  have evalOneMinus : ∀ j : Nat,
      DyadicPoly.eval { shift := 0, poly := [([], 1), ([(j, 1)], -1)] } (cyclicWin 0 n x x i) ≈
      Dyadic.sub Dyadic.one (x ((i + j) % n)) := by
    intro j
    unfold DyadicPoly.eval Poly.eval Mono.eval cyclicWin
    simp only [Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
    refine Dyadic.equiv_trans (Dyadic.divPow2_zero _) ?_
    refine Dyadic.equiv_add (Dyadic.one_mul _) ?_
    refine Dyadic.equiv_trans (Dyadic.add_zero _) ?_
    have hmon : Dyadic.mul (Dyadic.mul (x ((i + j) % n)) Dyadic.one) Dyadic.one ≈ x ((i + j) % n) :=
      Dyadic.equiv_trans (Dyadic.mul_one _) (Dyadic.mul_one _)
    refine Dyadic.equiv_trans (Dyadic.equiv_mul (Dyadic.ofInt_neg 1) hmon) ?_
    exact Dyadic.equiv_trans (Dyadic.neg_mul _ _) (Dyadic.equiv_neg (Dyadic.one_mul _))
  intro g hg
  simp only [cubeIneqs3, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Dyadic.nonneg_of_equiv (Dyadic.equiv_symm (evalVar 0)) (h01 ((i + 0) % n)).1
  · exact Dyadic.nonneg_of_equiv (Dyadic.equiv_symm (evalOneMinus 0))
      (Dyadic.nonneg_sub_of_le (h01 ((i + 0) % n)).2)
  · exact Dyadic.nonneg_of_equiv (Dyadic.equiv_symm (evalVar 1)) (h01 ((i + 1) % n)).1
  · exact Dyadic.nonneg_of_equiv (Dyadic.equiv_symm (evalOneMinus 1))
      (Dyadic.nonneg_sub_of_le (h01 ((i + 1) % n)).2)
  · exact Dyadic.nonneg_of_equiv (Dyadic.equiv_symm (evalVar 2)) (h01 ((i + 2) % n)).1
  · exact Dyadic.nonneg_of_equiv (Dyadic.equiv_symm (evalOneMinus 2))
      (Dyadic.nonneg_sub_of_le (h01 ((i + 2) % n)).2)

-- Theorem 3A: (1-a)(1-b) + a*b + a*(1-b)*c + (1-a)*b*(1-c) - 1/2 = (1 - 2a + 2ab + 2ac - 2bc)/2

def thm3a_stencil : DyadicPoly :=
  { shift := 1, poly := [([], 1), ([(0, 1)], -2), ([(0, 1), (1, 1)], 2),
                         ([(0, 1), (2, 1)], 2), ([(1, 1), (2, 1)], -2)] }

def thm3a_flux : DyadicPoly :=
  { shift := 1, poly := [([(0, 1)], 1), ([(1, 1)], 1), ([(0, 1), (1, 1)], -2)] }

def thm3a_cert : CyclicFluxCert :=
  { flux := thm3a_flux
    sosCert := {
      mainGram := rank1Gram [[], [(0, 1)], [(2, 1)]] [1, -1, -1] 1 1
      ineqProds := [([0, 1], constGram 1 1), ([4, 5], constGram 1 1)]
      eqCofacts := []
    } }

theorem thm3a_cert_valid : checkCyclicFlux 0 thm3a_stencil cubeIneqs3 [] thm3a_cert = true := by decide

/-- **Theorem 3A (Sharp Continuous Hypercube [0,1]^n Symmetric 3-Pattern Density):**
For ALL `n ≥ 1` and ALL `x ∈ ([0,1] ∩ Z[1/2])^n`, the cyclic sum of `00 + 11 + 101 + 010`
multilinear pattern indicators is `≥ n / 2` (attained with equality on period-4 `0011...`). -/
theorem thm3a_hypercube_sym_3pattern (n : Nat) (hn : 1 ≤ n) (x : Nat → Dyadic)
    (h01 : ∀ k, Dyadic.Nonneg (x k) ∧ Dyadic.Le (x k) Dyadic.one) :
    Dyadic.Nonneg (sumDyadic (fun i => DyadicPoly.eval thm3a_stencil (cyclicWin 0 n x x i)) n) :=
  cyclic_flux_sound 0 thm3a_stencil cubeIneqs3 [] thm3a_cert thm3a_cert_valid n hn x x
    (fun i _ => eval_cubeIneqs3 n x h01 i) (fun _ _ _ hh => nomatch hh)

-- Theorem 3B (Genuinely Cubic!): 3(1-a)(1-b) + 3ab + 2a(1-b)c - 1 = 2 - 3a - 3b + 6ab + 2ac - 2abc

def thm3b_flux : DyadicPoly :=
  { shift := 0, poly := [([(0, 1)], 1), ([(1, 1)], 2), ([(0, 1), (1, 1)], -2)] }

def thm3b_cert : CyclicFluxCert :=
  { flux := thm3b_flux
    sosCert := {
      mainGram := constGram 0 0
      ineqProds := [([1, 3, 5], constGram 2 0), ([0, 2], constGram 2 0)]
      eqCofacts := []
    } }

theorem thm3b_cert_valid : checkCyclicFlux 0 thm3b_stencil cubeIneqs3 [] thm3b_cert = true := by decide

/-- **Theorem 3B (Sharp Genuinely-Cubic Hypercube [0,1]^n Asymmetric 3-Pattern Density):**
For ALL `n ≥ 1` and ALL `x ∈ ([0,1] ∩ Z[1/2])^n`,
`∑_{i ∈ Z/nZ} (3(1-x_i)(1-x_{i+1}) + 3 x_i x_{i+1} + 2 x_i(1-x_{i+1})x_{i+2} - 1) ≥ 0`.
Simultaneously sharp on period-2 (`01...`) and period-3 (`001...`, `110...`). -/
theorem thm3b_hypercube_asym_3pattern (n : Nat) (hn : 1 ≤ n) (x : Nat → Dyadic)
    (h01 : ∀ k, Dyadic.Nonneg (x k) ∧ Dyadic.Le (x k) Dyadic.one) :
    Dyadic.Nonneg (sumDyadic (fun i => DyadicPoly.eval thm3b_stencil (cyclicWin 0 n x x i)) n) :=
  cyclic_flux_sound 0 thm3b_stencil cubeIneqs3 [] thm3b_cert thm3b_cert_valid n hn x x
    (fun i _ => eval_cubeIneqs3 n x h01 i) (fun _ _ _ hh => nomatch hh)

-- ----------------------------------------------------------------------------
-- THEOREM 4: Boolean {0,1}^n Frustrated Triangle & Continuous-vs-Binary Gap
--   ∀ n ≥ 1, ∀ b : Nat → Bool,
--   2 * ∑_{i ∈ Z/nZ} ( (b_i + b_{i+1} - 1)^2 + (b_i + b_{i+2} - 1)^2 ) ≥ n
--   (EXACTLY SHARP on {0,1}^n at `0011`; FALSIFIED on [0,1]^n at x_i = 1/2!)
-- ----------------------------------------------------------------------------

def boolEqs3 : List DyadicPoly :=
  [ { shift := 0, poly := [([(0, 2)], 1), ([(0, 1)], -1)] },
    { shift := 0, poly := [([(1, 2)], 1), ([(1, 1)], -1)] },
    { shift := 0, poly := [([(2, 2)], 1), ([(2, 1)], -1)] } ]

def thm4_stencil : DyadicPoly :=
  { shift := 1
    poly := [([], 3), ([(0, 1)], -8), ([(1, 1)], -4), ([(2, 1)], -4),
             ([(0, 2)], 4), ([(1, 2)], 2), ([(2, 2)], 2),
             ([(0, 1), (1, 1)], 4), ([(0, 1), (2, 1)], 4)] }

def thm4_cert : CyclicFluxCert :=
  { flux := thm3a_flux
    sosCert := {
      mainGram := rank1Gram [[], [(0, 1)], [(2, 1)]] [1, -1, -1] 1 1
      ineqProds := [([0, 1], constGram 1 1), ([4, 5], constGram 1 1),
                    ([1, 3, 5], constGram 1 0), ([0, 2, 4], constGram 1 0)]
      eqCofacts := [DyadicPoly.const 2 0, DyadicPoly.const 1 0, DyadicPoly.const 1 0]
    } }

theorem thm4_cert_valid : checkCyclicFlux 0 thm4_stencil cubeIneqs3 boolEqs3 thm4_cert = true := by decide

/-- **Theorem 4 (Sharp Boolean {0,1}^n Frustrated Triangle Inequality):**
Uses all 4 compiler layers: dyadic SOS Gram + Schmüdgen-Farkas hypercube products +
Boolean ideal cofactors `(x_i^2 - x_i)` + dyadic telescoping flux. -/
theorem thm4_boolean_frustrated_triangle (n : Nat) (hn : 1 ≤ n) (b : Nat → Bool) :
    0 ≤ sumInt (frustratedTriTerm b n) n := by
  let x : Nat → Int := fun k => boolToInt (b k)
  have hx01 : ∀ k, 0 ≤ x k ∧ x k ≤ 1 ∧ x k * x k = x k := by
    intro k; dsimp only [x, boolToInt]; cases b k <;> decide
  have h := cyclic_flux_sound_int 0 thm4_stencil cubeIneqs3 boolEqs3 thm4_cert thm4_cert_valid
    n hn x x
    (by
      intro i _ g hg
      simp only [cubeIneqs3, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [DyadicPoly.var, Poly.evalInt, Mono.evalInt, Nat.not_lt_zero, ↓reduceIte,
                   Nat.sub_zero, Nat.add_zero, Int.mul_one, Int.one_mul, Int.pow_one, Int.add_zero]
      · exact (hx01 (i % n)).1
      · have := (hx01 (i % n)).2.1; omega
      · exact (hx01 ((i + 1) % n)).1
      · have := (hx01 ((i + 1) % n)).2.1; omega
      · exact (hx01 ((i + 2) % n)).1
      · have := (hx01 ((i + 2) % n)).2.1; omega)
    (by
      intro i _ eqp heq
      simp only [boolEqs3, List.mem_cons, List.not_mem_nil, or_false] at heq
      rcases heq with rfl | rfl | rfl <;>
        simp only [Poly.evalInt, Mono.evalInt, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero,
                   Nat.add_zero, Int.mul_one, Int.one_mul, Int.pow_one, Int.add_zero]
      · have hsq := (hx01 (i % n)).2.2
        have hp2 : x (i % n) ^ 2 = x (i % n) * x (i % n) := by rw [Int.pow_succ, Int.pow_one]
        omega
      · have hsq := (hx01 ((i + 1) % n)).2.2
        have hp2 : x ((i + 1) % n) ^ 2 = x ((i + 1) % n) * x ((i + 1) % n) := by
          rw [Int.pow_succ, Int.pow_one]
        omega
      · have hsq := (hx01 ((i + 2) % n)).2.2
        have hp2 : x ((i + 2) % n) ^ 2 = x ((i + 2) % n) * x ((i + 2) % n) := by
          rw [Int.pow_succ, Int.pow_one]
        omega)
  have hterm : ∀ i, Poly.evalInt thm4_stencil.poly
      (fun v => if v < 0 then x v else x ((i + (v - 0)) % n)) = frustratedTriTerm b n i := by
    intro i
    simp only [thm4_stencil, Poly.evalInt, Mono.evalInt, frustratedTriTerm, x, Nat.not_lt_zero,
               ↓reduceIte, Nat.sub_zero, Nat.add_zero, Int.mul_one, Int.pow_one, Int.add_zero]
    have halg : ∀ u v w : Int,
        3 + (-8 * u + (-4 * v + (-4 * w + (4 * u ^ 2 + (2 * v ^ 2 + (2 * w ^ 2 +
          (4 * (u * v) + 4 * (u * w)))))))) =
        2 * ((u + v - 1) ^ 2 + (u + w - 1) ^ 2) - 1 := by
      intro u v w
      have h1 : (u + v - 1) ^ 2 = u ^ 2 + v ^ 2 + 1 + 2 * (u * v) - 2 * u - 2 * v := by
        rw [Int.pow_succ, Int.pow_one, Int.pow_succ, Int.pow_one, Int.pow_succ, Int.pow_one]
        simp only [Int.sub_eq_add_neg, Int.mul_add, Int.add_mul, Int.neg_mul, Int.mul_neg,
                   Int.mul_one, Int.one_mul]
        have hvu : v * u = u * v := Int.mul_comm v u
        omega
      have h2 : (u + w - 1) ^ 2 = u ^ 2 + w ^ 2 + 1 + 2 * (u * w) - 2 * u - 2 * w := by
        rw [Int.pow_succ, Int.pow_one, Int.pow_succ, Int.pow_one, Int.pow_succ, Int.pow_one]
        simp only [Int.sub_eq_add_neg, Int.mul_add, Int.add_mul, Int.neg_mul, Int.mul_neg,
                   Int.mul_one, Int.one_mul]
        have hwu : w * u = u * w := Int.mul_comm w u
        omega
      rw [h1, h2]
      omega
    exact halg (boolToInt (b (i % n))) (boolToInt (b ((i + 1) % n))) (boolToInt (b ((i + 2) % n)))
  have hsum : ∀ m, sumInt (fun i => Poly.evalInt thm4_stencil.poly
      (fun v => if v < 0 then x v else x ((i + (v - 0)) % n))) m = sumInt (frustratedTriTerm b n) m := by
    intro m; induction m with
    | zero => rfl
    | succ k ih => simp only [sumInt]; rw [ih, hterm k]
  rw [hsum n] at h
  exact h

-- ----------------------------------------------------------------------------
-- THEOREM 5A & 5B: Doubly-Infinite Parametric Cyclic & Open-Boundary
--   Discrete Biharmonic-Sobolev Inequalities (`paramCount = 1` & `OpenFluxCert`)
-- ----------------------------------------------------------------------------

-- Theorem 5A: var 0 = t (global parameter), vars 1,2,3 = (a, b, c) = (x_i, x_{i+1}, x_{i+2})
--   (c - 2b + a)^2 - 2t(b - a)^2 + t^2 a^2
--   = a^2 + 4b^2 + c^2 - 4ab + 2ac - 4bc - 2t a^2 + 4t ab - 2t b^2 + t^2 a^2

def thm5a_stencil : DyadicPoly :=
  { shift := 0
    poly := [([(1, 2)], 1), ([(2, 2)], 4), ([(3, 2)], 1),
             ([(1, 1), (2, 1)], -4), ([(1, 1), (3, 1)], 2), ([(2, 1), (3, 1)], -4),
             ([(0, 1), (1, 2)], -2), ([(0, 1), (1, 1), (2, 1)], 4), ([(0, 1), (2, 2)], -2),
             ([(0, 2), (1, 2)], 1)] }

-- flux(t; a, b) = 2t a^2 - 2t ab - t^2 a^2

def thm5a_flux : DyadicPoly :=
  { shift := 0
    poly := [([(0, 1), (1, 2)], 2), ([(0, 1), (1, 1), (2, 1)], -2), ([(0, 2), (1, 2)], -1)] }

def thm5a_cert : CyclicFluxCert :=
  { flux := thm5a_flux
    sosCert := {
      mainGram := rank1Gram [[(1, 1)], [(2, 1)], [(3, 1)], [(0, 1), (2, 1)]] [1, -2, 1, 1] 1 0
      ineqProds := []
      eqCofacts := []
    } }

theorem thm5a_cert_valid : checkCyclicFlux 1 thm5a_stencil [] [] thm5a_cert = true := by decide

/-- **Theorem 5A (Doubly-Infinite Parametric Discrete Biharmonic-Sobolev Theorem):**
Discharged in ONE finite certificate for ALL `n ≥ 1`, ALL `t ∈ Z`, and ALL `x : Nat → Z`. -/
theorem thm5a_parametric_biharmonic_cyclic_int (n : Nat) (hn : 1 ≤ n) (t : Int) (x : Nat → Int) :
    0 ≤ sumInt (biharmonicParamTerm t x n) n := by
  have h := cyclic_flux_sound_int 1 thm5a_stencil [] [] thm5a_cert thm5a_cert_valid
    n hn (fun _ => t) x (fun _ _ _ hg => nomatch hg) (fun _ _ _ hh => nomatch hh)
  have hterm : ∀ i, Poly.evalInt thm5a_stencil.poly
      (fun v => if v < 1 then t else x ((i + (v - 1)) % n)) = biharmonicParamTerm t x n i := by
    intro i
    simp only [thm5a_stencil, Poly.evalInt, Mono.evalInt, biharmonicParamTerm,
               Nat.zero_lt_one, Nat.lt_irrefl, ↓reduceIte,
               Int.mul_one, Int.one_mul, Int.pow_one, Int.add_zero]
    have h1lt : ¬ (2 < 1) := by omega
    have h2lt : ¬ (3 < 1) := by omega
    simp only [h1lt, h2lt, ↓reduceIte]
    have halg : ∀ tt a b c : Int,
        a ^ 2 + (4 * b ^ 2 + (c ^ 2 + (-4 * (a * b) + (2 * (a * c) + (-4 * (b * c) +
          (-2 * (tt * a ^ 2) + (4 * (tt * (a * b)) + (-2 * (tt * b ^ 2) + tt ^ 2 * a ^ 2)))))))) =
        (c - 2 * b + a) ^ 2 - 2 * tt * (b - a) ^ 2 + tt ^ 2 * a ^ 2 := by
      intro tt a b c
      have hs1 : (c - 2 * b + a) ^ 2 = c ^ 2 + 4 * b ^ 2 + a ^ 2 - 4 * (b * c) + 2 * (a * c) - 4 * (a * b) := by
        rw [Int.pow_succ, Int.pow_one, Int.pow_succ, Int.pow_one, Int.pow_succ, Int.pow_one,
            Int.pow_succ, Int.pow_one]
        simp only [Int.sub_eq_add_neg, Int.mul_add, Int.add_mul, Int.neg_mul, Int.mul_neg,
                   Int.mul_assoc]
        have hba : b * a = a * b := Int.mul_comm b a
        have hca : c * a = a * c := Int.mul_comm c a
        have hcb : c * b = b * c := Int.mul_comm c b
        have hc2b : c * (2 * b) = 2 * (b * c) := by rw [Int.mul_left_comm, Int.mul_comm c b]
        have hb2b : b * (2 * b) = 2 * (b * b) := by rw [Int.mul_left_comm]
        have ha2b : a * (2 * b) = 2 * (a * b) := by rw [Int.mul_left_comm]
        omega
      have hs2 : (b - a) ^ 2 = b ^ 2 - 2 * (a * b) + a ^ 2 := by
        rw [Int.pow_succ, Int.pow_one, Int.pow_succ, Int.pow_one, Int.pow_succ, Int.pow_one]
        simp only [Int.sub_eq_add_neg, Int.mul_add, Int.add_mul, Int.neg_mul, Int.mul_neg]
        have hba : b * a = a * b := Int.mul_comm b a
        omega
      rw [hs1, hs2]
      have hmul : 2 * tt * (b ^ 2 - 2 * (a * b) + a ^ 2) =
          2 * (tt * b ^ 2) - 4 * (tt * (a * b)) + 2 * (tt * a ^ 2) := by
        simp only [Int.sub_eq_add_neg, Int.mul_add, Int.mul_neg, Int.mul_assoc]
        have h2 : tt * (2 * (a * b)) = 2 * (tt * (a * b)) := by rw [Int.mul_left_comm]
        omega
      rw [hmul]
      omega
    exact halg t (x (i % n)) (x ((i + 1) % n)) (x ((i + 2) % n))
  have hsum : ∀ m, sumInt (fun i => Poly.evalInt thm5a_stencil.poly
      (fun v => if v < 1 then t else x ((i + (v - 1)) % n))) m =
      sumInt (biharmonicParamTerm t x n) m := by
    intro m; induction m with
    | zero => rfl
    | succ k ih => simp only [sumInt]; rw [ih, hterm k]
  rw [hsum n] at h
  exact h

-- Theorem 5B: Open-Boundary Discrete Biharmonic Stabilization (`OpenFluxCert`, t = 2, SHARP!)
--   2(x_0^2 + x_1^2) + ∑_{i=0}^{n-1} ((Δ^2 x_i)^2 - 4(Δ x_i)^2 + 4 x_i^2) + 2(x_n^2 + x_{n+1}^2) ≥ 0

def thm5b_stencil : DyadicPoly :=
  { shift := 0
    poly := [([(0, 2)], 1), ([(1, 2)], 0), ([(2, 2)], 1),
             ([(0, 1), (1, 1)], 4), ([(0, 1), (2, 1)], 2), ([(1, 1), (2, 1)], -4)] }

def thm5b_bBound : DyadicPoly :=
  { shift := 0, poly := [([(0, 2)], 2), ([(1, 2)], 2)] }

def thm5b_flux : DyadicPoly :=
  { shift := 0, poly := [([(0, 1), (1, 1)], -4)] }

def thm5b_cert : OpenFluxCert :=
  { flux := thm5b_flux
    bulkCert  := { mainGram := rank1Gram [[(0, 1)], [(2, 1)]] [1, 1] 1 0, ineqProds := [], eqCofacts := [] }
    leftCert  := { mainGram := rank1Gram [[(0, 1)], [(1, 1)]] [1, 1] 2 0, ineqProds := [], eqCofacts := [] }
    rightCert := { mainGram := rank1Gram [[(0, 1)], [(1, 1)]] [1, -1] 2 0, ineqProds := [], eqCofacts := [] } }

theorem thm5b_cert_valid :
    checkOpenFlux 0 thm5b_stencil thm5b_bBound thm5b_bBound [] [] thm5b_cert = true := by decide

/-- **Theorem 5B (Sharp Open-Boundary Discrete Biharmonic Stabilization):**
For ALL `n : Nat` and ALL `x : Nat → Int`,
`2(x_0^2 + x_1^2) + ∑_{i=0}^{n-1} ((Δ^2 x_i)^2 - 4(Δ x_i)^2 + 4 x_i^2) + 2(x_n^2 + x_{n+1}^2) ≥ 0`.
Exact equality `= 0` holds for infinitely many `n ≡ 1 (mod 4)` on the period-4 wave `(1,-1,-1,1,...)`! -/
theorem thm5b_open_biharmonic_stabilized_int (n : Nat) (x : Nat → Int) :
    0 ≤ 2 * (x 0 ^ 2 + x 1 ^ 2) + sumInt (openBiharmonicTerm x) n + 2 * (x n ^ 2 + x (n + 1) ^ 2) := by
  have hnn := open_flux_sound 0 thm5b_stencil thm5b_bBound thm5b_bBound [] [] thm5b_cert
    thm5b_cert_valid n (fun v => Dyadic.ofInt (x v)) (fun v => Dyadic.ofInt (x v))
    (fun _ _ _ hg => nomatch hg) (fun _ _ _ hh => nomatch hh)
  have hwin : ∀ i, openWin 0 (fun v => Dyadic.ofInt (x v)) (fun v => Dyadic.ofInt (x v)) i =
      fun v => Dyadic.ofInt (x (i + v)) := by
    intro i; funext v; unfold openWin; simp
  have hterm : ∀ i, Poly.evalInt thm5b_stencil.poly (fun v => x (i + v)) = openBiharmonicTerm x i := by
    intro i
    simp only [thm5b_stencil, Poly.evalInt, Mono.evalInt, openBiharmonicTerm,
               Nat.add_zero, Int.mul_one, Int.one_mul, Int.zero_mul, Int.pow_one, Int.add_zero, Int.zero_add]
    have halg : ∀ a b c : Int,
        a ^ 2 + (c ^ 2 + (4 * (a * b) + (2 * (a * c) + -4 * (b * c)))) =
        (c - 2 * b + a) ^ 2 - 4 * (b - a) ^ 2 + 4 * a ^ 2 := by
      intro a b c
      have hs1 : (c - 2 * b + a) ^ 2 = c ^ 2 + 4 * b ^ 2 + a ^ 2 - 4 * (b * c) + 2 * (a * c) - 4 * (a * b) := by
        rw [Int.pow_succ, Int.pow_one, Int.pow_succ, Int.pow_one, Int.pow_succ, Int.pow_one,
            Int.pow_succ, Int.pow_one]
        simp only [Int.sub_eq_add_neg, Int.mul_add, Int.add_mul, Int.neg_mul, Int.mul_neg,
                   Int.mul_assoc]
        have hba : b * a = a * b := Int.mul_comm b a
        have hca : c * a = a * c := Int.mul_comm c a
        have hcb : c * b = b * c := Int.mul_comm c b
        have hc2b : c * (2 * b) = 2 * (b * c) := by rw [Int.mul_left_comm, Int.mul_comm c b]
        have hb2b : b * (2 * b) = 2 * (b * b) := by rw [Int.mul_left_comm]
        have ha2b : a * (2 * b) = 2 * (a * b) := by rw [Int.mul_left_comm]
        omega
      have hs2 : (b - a) ^ 2 = b ^ 2 - 2 * (a * b) + a ^ 2 := by
        rw [Int.pow_succ, Int.pow_one, Int.pow_succ, Int.pow_one, Int.pow_succ, Int.pow_one]
        simp only [Int.sub_eq_add_neg, Int.mul_add, Int.add_mul, Int.neg_mul, Int.mul_neg]
        have hba : b * a = a * b := Int.mul_comm b a
        omega
      rw [hs1, hs2]
      omega
    exact halg (x i) (x (i + 1)) (x (i + 2))
  have hbEval : ∀ i, DyadicPoly.eval thm5b_bBound (openWin 0 (fun v => Dyadic.ofInt (x v))
      (fun v => Dyadic.ofInt (x v)) i) = Dyadic.ofInt (2 * (x i ^ 2 + x (i + 1) ^ 2)) := by
    intro i
    rw [hwin i, DyadicPoly.eval_ofInt]
    simp only [thm5b_bBound, Poly.evalInt, Mono.evalInt, Nat.add_zero, Int.mul_one, Int.add_zero,
               Dyadic.ofInt]
    congr 1; omega
  have hsumEq : sumDyadic (fun i => DyadicPoly.eval thm5b_stencil
      (openWin 0 (fun v => Dyadic.ofInt (x v)) (fun v => Dyadic.ofInt (x v)) i)) n =
      Dyadic.ofInt (sumInt (openBiharmonicTerm x) n) := by
    have hgo : ∀ m, sumDyadic (fun i => DyadicPoly.eval thm5b_stencil
        (openWin 0 (fun v => Dyadic.ofInt (x v)) (fun v => Dyadic.ofInt (x v)) i)) m =
        sumDyadic (fun i => Dyadic.ofInt (openBiharmonicTerm x i)) m := by
      intro m
      induction m with
      | zero => rfl
      | succ k ih =>
        simp only [sumDyadic]
        rw [ih, hwin k, DyadicPoly.eval_ofInt, hterm k]
        rfl
    rw [hgo n, sumDyadic_ofInt]
  rw [hbEval 0, hbEval n, hsumEq] at hnn
  unfold Dyadic.Nonneg Dyadic.add Dyadic.ofInt at hnn
  simp only [Int.pow_zero, Int.mul_one, Nat.zero_add] at hnn
  omega

-- ----------------------------------------------------------------------------
-- THEOREM 6: Fixed-Dimension Nonlinear Dyadic Positivstellensatz Refutation
--   Disk `1 - x^2 - y^2 ≥ 0` is disjoint from Half-Plane `x + y ≥ 23/16`
--   for ALL `x, y ∈ Z[1/2]`! (Perturbing `23/16` by `1/32` to `45/32` is FEASIBLE!)
-- ----------------------------------------------------------------------------

def thm6_gram : DyadicGram :=
  { basis := [[], [(0, 1)], [(1, 1)]]
    shift := 8
    G := [[529, -368, -368], [-368, 512, 0], [-368, 0, 512]]
    scale := 0
    diag := [1, 1]
    L := [[0, 16, -16], [-23, 16, 16]] }

def thm6_cert : FarkasSOSCert :=
  { mainGram := thm6_gram
    ineqProds := [([0], constGram 2 0), ([1], constGram 23 3)]
    eqCofacts := [] }

theorem thm6_cert_valid :
    FarkasSOS.checkRefutation (-17) 8 [thm6_g0, thm6_g1] [] thm6_cert = true := by decide

/-- **Theorem 6 (Nonlinear Dyadic Positivstellensatz Refutation):**
For ALL `x, y ∈ Z[1/2]`, the unit disk `x^2 + y^2 ≤ 1` and half-plane `x + y ≥ 23/16`
have empty intersection (certified via exact dyadic `-17/256` Positivstellensatz refutation). -/
theorem thm6_nonlinear_farkas_refutation (x y : Dyadic) :
    ¬ (Dyadic.Nonneg (DyadicPoly.eval thm6_g0 (fun i => if i = 0 then x else y)) ∧
       Dyadic.Nonneg (DyadicPoly.eval thm6_g1 (fun i => if i = 0 then x else y))) := by
  have href := FarkasSOS.refutation_sound (-17) 8 [thm6_g0, thm6_g1] [] thm6_cert thm6_cert_valid
    (fun i => if i = 0 then x else y)
  rintro ⟨h0, h1⟩
  apply href
  refine ⟨?_, fun _ hh => nomatch hh⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact h0
  · exact h1

-- ============================================================================
-- Section 7: Kernel-Checked Non-Vacuity, Sharpness, Integrality Gap &
--            10-Mutation Adversarial Rejection Suite
-- ============================================================================

-- 7.1 Non-vacuity witnesses (proving hypotheses are genuinely inhabited on non-trivial inputs)

/-- Non-vacuity for Theorem 3A/3B: the dyadic point `x_k = 1/2` satisfies `0 ≤ x_k ≤ 1`. -/
example : ∀ _k : Nat, Dyadic.Nonneg ⟨1, 1⟩ ∧ Dyadic.Le ⟨1, 1⟩ Dyadic.one := by
  intro _; exact ⟨by unfold Dyadic.Nonneg; dsimp only; omega, by unfold Dyadic.Le Dyadic.one; decide⟩

/-- Non-vacuity for Theorem 3A: period-4 binary word `0011` attains EXACT equality `0`. -/
def word0011 (k : Nat) : Dyadic :=
  if k % 4 < 2 then Dyadic.zero else Dyadic.one

theorem sharpness_3a_equality :
    (sumDyadic (fun i => DyadicPoly.eval thm3a_stencil (cyclicWin 0 4 word0011 word0011 i)) 4).mant = 0 := by
  decide

/-- Non-vacuity & exact sharpness for Theorem 4: `0011` attains exact equality `0` on `{0,1}^4`. -/
def bool0011 (k : Nat) : Bool := !(k % 4 < 2)

theorem sharpness_4_equality_bool : sumInt (frustratedTriTerm bool0011 4) 4 = 0 := by decide

/-- **Kernel-checked Continuous-vs-Binary Integrality Gap for Theorem 4:**
At `x_k = 1/2 ∈ [0,1] ∩ Z[1/2]`, the frustrated triangle stencil is STRICTLY NEGATIVE (`-1/2 < 0`),
proving the Boolean ideal `x_i^2 - x_i = 0` is strictly indispensable! -/
theorem gap_4_fails_on_hypercube :
    (DyadicPoly.eval thm4_stencil (fun _ => ⟨1, 1⟩)).mant < 0 := by decide

-- 7.2 Sharpness counterexamples (proving every bound breaks just outside its constant!)

/-- Sharpness of Theorem 1: at `c = 27/16` (just `1/16` tighter than `13/8`),
`x = [-3, -2, 3, 2]` gives `-25/4 < 0` (`16 * sum = -100 < 0`). -/
def ce1_vec (k : Nat) : Int :=
  match k % 4 with | 0 => -3 | 1 => -2 | 2 => 3 | _ => 2

def asymSkewTightTerm (x : Nat → Int) (n i : Nat) : Int :=
  let a := x (i % n); let b := x ((i + 1) % n); let c := x ((i + 2) % n)
  16 * a ^ 4 + 16 * a ^ 2 * b ^ 2 - 27 * a ^ 3 * b + 27 * a * b ^ 2 * c

theorem sharpness_1_counterexample_27_16 : sumInt (asymSkewTightTerm ce1_vec 4) 4 = -100 := by decide

/-- Local indefiniteness of Theorem 1 (and impossibility of ANY 1-variable flux `φ(a) - φ(b)`):
at `(1, 1, -1)` the local stencil is `-5/4 < 0` while `a = b = 1` kills every 1-variable flux! -/
theorem thm1_local_indefinite :
    (DyadicPoly.eval thm1_stencil (fun i => if i = 2 then Dyadic.ofInt (-1) else Dyadic.one)).mant < 0 := by
  decide

/-- Sharpness of Theorem 2: at `c = 15/8` (just `1/8` tighter than `7/4`),
`x = [0, -1, -2, -4, -4, -2, 1, -1]` gives `-25/8 < 0` (`8 * sum = -25 < 0`). -/
def ce2_vec (k : Nat) : Int :=
  match k % 8 with
  | 0 => 0 | 1 => -1 | 2 => -2 | 3 => -4 | 4 => -4 | 5 => -2 | 6 => 1 | _ => -1

def mixedTightTerm (x : Nat → Int) (n i : Nat) : Int :=
  let a := x (i % n); let b := x ((i + 1) % n); let c := x ((i + 2) % n)
  8 * a ^ 4 + 8 * a ^ 2 * b ^ 2 - 15 * a ^ 3 * b - 15 * a * b ^ 2 * c + 15 * a ^ 2 * b * c

theorem sharpness_2_counterexample_15_8 : sumInt (mixedTightTerm ce2_vec 8) 8 = -25 := by decide

/-- Sharpness of Theorem 5B: open period-4 wave `(1,-1,-1,1,1,-1,-1,...)` attains exact `0` at `n = 5`,
while dropping the boundary stabilization gives `-4 < 0` at `n = 1, x = (0, 1, 2)`. -/
def wave4 (k : Nat) : Int := match k % 4 with | 0 => 1 | 1 => -1 | 2 => -1 | _ => 1

theorem sharpness_5b_exact_zero_n5 :
    2 * (wave4 0 ^ 2 + wave4 1 ^ 2) + sumInt (openBiharmonicTerm wave4) 5 +
    2 * (wave4 5 ^ 2 + wave4 6 ^ 2) = 0 := by decide

def openCE (k : Nat) : Int := (k : Int)

theorem sharpness_5b_unstabilized_negative : sumInt (openBiharmonicTerm openCE) 1 = -4 := by decide

/-- Sharpness of Theorem 6: perturbing `23/16` by `1/32` to `45/32` becomes FEASIBLE at
the exact dyadic point `(45/64, 45/64)`! -/
def thm6_g1_relaxed : DyadicPoly := { shift := 5, poly := [([], -45), ([(0, 1)], 32), ([(1, 1)], 32)] }

theorem sharpness_6_feasible_at_45_32 :
    Dyadic.Nonneg (DyadicPoly.eval thm6_g0 (fun _ => ⟨45, 6⟩)) ∧
    Dyadic.Nonneg (DyadicPoly.eval thm6_g1_relaxed (fun _ => ⟨45, 6⟩)) := by
  exact ⟨by unfold Dyadic.Nonneg; decide, by unfold Dyadic.Nonneg; decide⟩

-- 7.3 Kernel-checked 10-Mutation Adversarial Rejection Suite (`check... bad = false := by decide`)

-- Mutation 1: Negative diagonal weight in LDL^T (`d_0 = -1`)

def bad_gram_neg_diag : DyadicGram :=
  { thm1_gram with diag := (-1) :: thm1_gram.diag.tail }

theorem reject_mut1_neg_diag : Gram.checkPSD bad_gram_neg_diag = false := by decide

-- Mutation 2: 1-bit flip in factor matrix L (`L[0][0] = 701` instead of `700`)

def bad_gram_ldlt_flip : DyadicGram :=
  { thm1_gram with L := ([701, -70, -515, 374, -187, 0] :: thm1_gram.L.tail) }

theorem reject_mut2_ldlt_flip : Gram.checkPSD bad_gram_ldlt_flip = false := by decide

-- Mutation 3: Asymmetric Gram matrix (`G[0][1] = -2` while `G[1][0] = -3`)

def bad_gram_asymmetric : DyadicGram :=
  { thm1_gram with G := ([30, -2, -22, 16, -8, 0] :: thm1_gram.G.tail) }

theorem reject_mut3_asymmetric : Gram.checkPSD bad_gram_asymmetric = false := by decide

-- Mutation 4: Wrong LDL^T binary scale exponent (`scale := 15` instead of `14`)

def bad_gram_wrong_scale : DyadicGram :=
  { thm1_gram with scale := 15 }

theorem reject_mut4_wrong_scale : Gram.checkPSD bad_gram_wrong_scale = false := by decide

-- Mutation 5: Valid PSD Gram (`shift := 8`) whose polynomial expansion fails to match stencil

def bad_gram_wrong_shift : DyadicGram :=
  { thm1_gram with shift := 8 }

theorem mut5_gram_still_psd : Gram.checkPSD bad_gram_wrong_shift = true := by decide

theorem reject_mut5_poly_mismatch :
    checkCyclicFlux 0 thm1_stencil [] []
      { thm1_cert with sosCert := { thm1_cert.sosCert with mainGram := bad_gram_wrong_shift } } = false := by
  decide

-- Mutation 6: Negative Farkas multiplier (`constGram (-1) 1`) on Theorem 3A

def bad_farkas_neg : CyclicFluxCert :=
  { thm3a_cert with sosCert := {
      thm3a_cert.sosCert with
      ineqProds := [([0, 1], constGram (-1) 1), ([4, 5], constGram 1 1)] } }

theorem reject_mut6_neg_farkas :
    checkCyclicFlux 0 thm3a_stencil cubeIneqs3 [] bad_farkas_neg = false := by decide

-- Mutation 7: Out-of-bounds constraint index in Schmüdgen product (`idx = 99`)

def bad_farkas_oob : CyclicFluxCert :=
  { thm3a_cert with sosCert := {
      thm3a_cert.sosCert with
      ineqProds := [([0, 99], constGram 1 1), ([4, 5], constGram 1 1)] } }

theorem reject_mut7_oob_index :
    checkCyclicFlux 0 thm3a_stencil cubeIneqs3 [] bad_farkas_oob = false := by decide

-- Mutation 8: Corrupted telescoping flux potential (`-48` instead of `-49` on `a^4`)

def bad_flux_thm1 : DyadicPoly :=
  { shift := 6
    poly := [([(0, 1), (1, 3)], (-48)), ([(0, 2), (1, 2)], (-60)),
             ([(0, 3), (1, 1)], (101)), ([(0, 4)], (-48)), ([(1, 4)], (-15))] }

theorem reject_mut8_corrupted_flux :
    checkCyclicFlux 0 thm1_stencil [] [] { thm1_cert with flux := bad_flux_thm1 } = false := by
  decide

-- Mutation 9: Over-tightened target constant (`c = 27/16` with the `13/8` cert)

def thm1_stencil_tight : DyadicPoly :=
  { shift := 4
    poly := [([(0, 1), (1, 2), (2, 1)], (27)), ([(0, 2), (1, 2)], (16)),
             ([(0, 3), (1, 1)], (-27)), ([(0, 4)], (16))] }

theorem reject_mut9_overtight_target :
    checkCyclicFlux 0 thm1_stencil_tight [] [] thm1_cert = false := by decide

-- Mutation 10: Weakened open boundary (`bLeft = a^2 + b^2` instead of `2a^2 + 2b^2`)
-- and positive refutation constant (`+17` instead of `-17`)

def thm5b_bWeak : DyadicPoly := { shift := 0, poly := [([(0, 2)], 1), ([(1, 2)], 1)] }

theorem reject_mut10a_weak_boundary :
    checkOpenFlux 0 thm5b_stencil thm5b_bWeak thm5b_bBound [] [] thm5b_cert = false := by decide

theorem reject_mut10b_positive_refutation :
    FarkasSOS.checkRefutation 17 8 [thm6_g0, thm6_g1] [] thm6_cert = false := by decide


-- ============================================================================
-- Section 8: Kernel Axiom Audit (every core & flagship theorem)
-- ============================================================================

end DyadicSOS
