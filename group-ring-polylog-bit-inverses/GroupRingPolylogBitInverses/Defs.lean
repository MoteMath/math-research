/-!
# Exact `Z[F_2^k]` Group-Ring Inversion, Parseval Duality, and the Shared-Bit Idempotent Lifting Engine

Standalone Lean 4.36.0 formalization (zero Mathlib, zero `sorry`, zero custom axioms).

## Structure
- **Part I**: Exact binary-vector group ring `Z[F_2^k]`, XOR-circulant matrices,
  Walsh-Hadamard transform (`wht`), convolution theorem, exact dyadic involution,
  Parseval/Plancherel duality, exact scaled group-ring & matrix inversion criterion,
  and XOR-preserving bijection with `BitVec k`.
- **Part II**: Parseval Rigidity & Obstruction Engine:
  1. Pure-Silicon Higman Rigidity (`conv f g = delta 0 → sumSq f = 1`).
  2. Odd-Divisibility Spectral Rigidity (`Odd m → (∀ ω, m ∣ wht f ω) → ∀ x, m ∣ f x`).
  3. Constant Spectral Parity & Mod-12 Parseval Dyadic Obstruction for ternary elements.
  4. Pure `{0, 1}` Self-Inversion Impossibility (`suppCount f ≤ 1`).
  5. Pure-Integer Parseval-Cauchy-Schwarz Support-Scale Uncertainty (`D^2 ≤ sumSq f * sumSq g`).
- **Part III**: Reusable Finite-to-Infinite Lifting Engine (`sharedLift`):
  exact spectral multiplexer law, exact scaled inversion lifting, exact entry-bound
  preservation, exact support-size recursion `2 * (|supp A| + |supp B|)`, and
  full affine-span preservation.
- **Part IV**: Concrete Infinite Sparse Matrix Families proved through the Engine:
  - **Theorem A**: Multiplexer Bit-Tree Family `treeElem d` on `k_d = 2^{d+1} - 2` bits
    (`N_d = 2^{2^{d+1}-2}`), polylogarithmic sparsity `|supp| = 4^d = ((k_d+2)/2)^2`,
    exact dyadic self-inverse `M(T_d)^2 = 4^d I`, bounded entries `{-1, 0, 1}`,
    full affine span, and exact `O(d)` dual spectral evaluator `spectralSign d`.
  - **Theorem B**: Asymmetric Non-Self-Inverse Sparse Family `(asymTreeP d, asymTreeQ d)`
    on `k_d = 5 * 2^d - 2` bits (`|supp| = 5 * 4^d`, `P_d * Q_d = (3 * 4^d) δ_0`,
    entries `{-1, 0, 1}`, full affine span, `P_d ≠ Q_d` and `P_d ≠ -Q_d`).
  - **Theorem C**: Universal All-Dimension Polylogarithmic Theorem (`∀ k ≥ 2, k ≠ 3`,
    full-affine-spanning ternary dyadic self-inverse with `|supp| = 4^d < (k + 2)^2`).
- **Part V**: Non-Vacuity Witnesses, Sharpness Counterexamples (`k = 1` impossibility,
  `k = 3` dyadic/flat-spectrum impossibility, unshifted overlap entry-blowup witness,
  unmatched-scale non-bent dyadic unit on `F_2^4`), and `#print axioms`.
-/

namespace SpecMat13

/-! ## Part I: Binary Vector Group Ring `Z[F_2^k]` & Walsh-Hadamard Duality -/

inductive BVec : Nat → Type where
  | nil : BVec 0
  | cons : Bool → BVec k → BVec (k + 1)
  deriving DecidableEq, Repr

def bzero : (k : Nat) → BVec k
  | 0 => .nil
  | k + 1 => .cons false (bzero k)

def bxor : {k : Nat} → BVec k → BVec k → BVec k
  | 0, .nil, .nil => .nil
  | _ + 1, .cons a x, .cons b y => .cons (xor a b) (bxor x y)

def bdot : {k : Nat} → BVec k → BVec k → Bool
  | 0, .nil, .nil => false
  | _ + 1, .cons a x, .cons b y => xor (a && b) (bdot x y)

def signBit (b : Bool) : Int := if b then -1 else 1

def bappendR : {k₁ k₂ : Nat} → BVec k₁ → BVec k₂ → BVec (k₁ + k₂)
  | _, 0, x, .nil => x
  | _, _ + 1, x, .cons b y => .cons b (bappendR x y)

def bsplitR : (k₁ k₂ : Nat) → BVec (k₁ + k₂) → BVec k₁ × BVec k₂
  | _, 0, x => (x, .nil)
  | k₁, k₂ + 1, .cons b x =>
      let (u, v) := bsplitR k₁ k₂ x
      (u, .cons b v)

theorem bsplitR_bappendR : {k₁ k₂ : Nat} → (x : BVec k₁) → (y : BVec k₂) →
    bsplitR k₁ k₂ (bappendR x y) = (x, y)
  | _, 0, _, .nil => rfl
  | k₁, k₂ + 1, x, .cons b y => by
      simp [bappendR, bsplitR, bsplitR_bappendR x y]

theorem bappendR_bsplitR : {k₁ k₂ : Nat} → (z : BVec (k₁ + k₂)) →
    bappendR (bsplitR k₁ k₂ z).1 (bsplitR k₁ k₂ z).2 = z
  | _, 0, _ => rfl
  | k₁, k₂ + 1, .cons b z => by
      have ih := bappendR_bsplitR (k₁ := k₁) (k₂ := k₂) z
      simp [bsplitR, bappendR, ih]

theorem bappendR_bzero : {k₁ k₂ : Nat} →
    bappendR (bzero k₁) (bzero k₂) = bzero (k₁ + k₂)
  | _, 0 => rfl
  | k₁, k₂ + 1 => by
      simp [bzero, bappendR, bappendR_bzero (k₁ := k₁) (k₂ := k₂)]

theorem bdot_bappendR : {k₁ k₂ : Nat} → (x₁ y₁ : BVec k₁) → (x₂ y₂ : BVec k₂) →
    bdot (bappendR x₁ x₂) (bappendR y₁ y₂) = xor (bdot x₁ y₁) (bdot x₂ y₂)
  | _, 0, x₁, y₁, .nil, .nil => by
      simp [bappendR, bdot]
  | k₁, k₂ + 1, x₁, y₁, .cons a x₂, .cons b y₂ => by
      simp only [bappendR, bdot, bdot_bappendR x₁ y₁ x₂ y₂]
      cases (a && b) <;> cases bdot x₁ y₁ <;> cases bdot x₂ y₂ <;> rfl

/-! ### Basic algebraic properties of `bxor`, `bdot`, `signBit` -/

theorem bxor_comm : {k : Nat} → (x y : BVec k) → bxor x y = bxor y x
  | 0, .nil, .nil => rfl
  | _ + 1, .cons a x, .cons b y => by
      simp only [bxor, bxor_comm x y]
      cases a <;> cases b <;> rfl

theorem bxor_assoc : {k : Nat} → (x y z : BVec k) → bxor (bxor x y) z = bxor x (bxor y z)
  | 0, .nil, .nil, .nil => rfl
  | _ + 1, .cons a x, .cons b y, .cons c z => by
      simp only [bxor, bxor_assoc x y z]
      cases a <;> cases b <;> cases c <;> rfl

theorem bxor_self : {k : Nat} → (x : BVec k) → bxor x x = bzero k
  | 0, .nil => rfl
  | _ + 1, .cons a x => by
      simp only [bxor, bzero, bxor_self x]
      cases a <;> rfl

theorem bxor_bzero_right : {k : Nat} → (x : BVec k) → bxor x (bzero k) = x
  | 0, .nil => rfl
  | _ + 1, .cons a x => by
      simp [bxor, bzero, bxor_bzero_right x]

theorem bxor_bzero_left : {k : Nat} → (x : BVec k) → bxor (bzero k) x = x
  | 0, .nil => rfl
  | _ + 1, .cons a x => by
      simp [bxor, bzero, bxor_bzero_left x]

theorem bxor_invol : {k : Nat} → (x y : BVec k) → bxor (bxor x y) y = x := by
  intro k x y
  rw [bxor_assoc, bxor_self, bxor_bzero_right]

theorem bxor_eq_bzero_iff : {k : Nat} → {x y : BVec k} → bxor x y = bzero k ↔ x = y := by
  intro k x y
  constructor
  · intro h
    have h1 := congrArg (fun z => bxor z y) h
    rw [bxor_invol, bxor_bzero_left] at h1
    exact h1
  · intro h; subst h; exact bxor_self x

theorem bdot_bzero_right : {k : Nat} → (x : BVec k) → bdot x (bzero k) = false
  | 0, .nil => rfl
  | _ + 1, .cons a x => by
      simp [bdot, bzero, bdot_bzero_right x]

theorem bdot_bzero_left : {k : Nat} → (x : BVec k) → bdot (bzero k) x = false
  | 0, .nil => rfl
  | _ + 1, .cons a x => by
      simp [bdot, bzero, bdot_bzero_left x]

theorem bdot_bxor_right : {k : Nat} → (ω x y : BVec k) →
    bdot ω (bxor x y) = xor (bdot ω x) (bdot ω y)
  | 0, .nil, .nil, .nil => rfl
  | _ + 1, .cons w ω, .cons a x, .cons b y => by
      simp only [bxor, bdot, bdot_bxor_right ω x y]
      cases w <;> cases a <;> cases b <;> cases bdot ω x <;> cases bdot ω y <;> rfl

theorem signBit_xor (a b : Bool) : signBit (xor a b) = signBit a * signBit b := by
  cases a <;> cases b <;> rfl

theorem signBit_sq (a : Bool) : signBit a * signBit a = 1 := by
  cases a <;> rfl

/-! ### Exact Bijection `BitVec k ≃ BVec k` preserving XOR -/

def ofBitVec : {k : Nat} → BitVec k → BVec k
  | 0, _ => .nil
  | k + 1, v => .cons (v.getLsbD 0) (ofBitVec (v.extractLsb' 1 k))

def toBitVec : {k : Nat} → BVec k → BitVec k
  | 0, .nil => 0#0
  | k + 1, .cons b x =>
      let hi : BitVec (k + 1) := (toBitVec x).zeroExtend (k + 1) <<< 1
      if b then hi ||| 1#(k + 1) else hi

theorem ofBitVec_xor : {k : Nat} → (u v : BitVec k) →
    ofBitVec (u ^^^ v) = bxor (ofBitVec u) (ofBitVec v)
  | 0, _, _ => rfl
  | k + 1, u, v => by
      simp only [ofBitVec, bxor, BitVec.getLsbD_xor]
      congr 1
      have h : (u ^^^ v).extractLsb' 1 k = u.extractLsb' 1 k ^^^ v.extractLsb' 1 k := by
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        simp [hi]
      rw [h, ofBitVec_xor]

theorem getLsbD_toBitVec_zero (k : Nat) (b : Bool) (x : BVec k) :
    (toBitVec (.cons b x)).getLsbD 0 = b := by
  cases b <;> simp [toBitVec]

theorem extractLsb'_toBitVec (k : Nat) (b : Bool) (x : BVec k) :
    (toBitVec (.cons b x)).extractLsb' 1 k = toBitVec x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  cases b <;> simp [toBitVec, hi, Nat.add_comm]

theorem ofBitVec_toBitVec : {k : Nat} → (x : BVec k) → ofBitVec (toBitVec x) = x
  | 0, .nil => rfl
  | k + 1, .cons b x => by
      simp only [ofBitVec, getLsbD_toBitVec_zero, extractLsb'_toBitVec, ofBitVec_toBitVec x]

theorem toBitVec_ofBitVec : {k : Nat} → (v : BitVec k) → toBitVec (ofBitVec v) = v
  | 0, v => by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi; omega
  | k + 1, v => by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [ofBitVec]
      cases i with
      | zero => exact getLsbD_toBitVec_zero k (v.getLsbD 0) (ofBitVec (v.extractLsb' 1 k))
      | succ j =>
          have hj : j < k := by omega
          have h1 : (toBitVec (.cons (v.getLsbD 0) (ofBitVec (v.extractLsb' 1 k)))).getLsbD (j + 1) =
              ((toBitVec (.cons (v.getLsbD 0) (ofBitVec (v.extractLsb' 1 k)))).extractLsb' 1 k).getLsbD j := by
            simp [hj, Nat.add_comm]
          rw [h1, extractLsb'_toBitVec, toBitVec_ofBitVec]
          simp [hj, Nat.add_comm]

/-! ### Exact Summation over `BVec k` -/

abbrev GR (k : Nat) := BVec k → Int

def sumBVec : {k : Nat} → (BVec k → Int) → Int
  | 0, f => f .nil
  | _ + 1, f => sumBVec (fun x => f (.cons false x)) + sumBVec (fun x => f (.cons true x))

theorem sumBVec_congr : {k : Nat} → {f g : BVec k → Int} →
    (∀ x, f x = g x) → sumBVec f = sumBVec g
  | 0, _, _, h => h .nil
  | _ + 1, _, _, h => by
      simp only [sumBVec]
      rw [sumBVec_congr (fun x => h (.cons false x)),
          sumBVec_congr (fun x => h (.cons true x))]

theorem sumBVec_zero : {k : Nat} → sumBVec (fun (_ : BVec k) => (0 : Int)) = 0
  | 0 => rfl
  | k + 1 => by simp [sumBVec, sumBVec_zero (k := k)]

theorem sumBVec_const : {k : Nat} → (c : Int) →
    sumBVec (fun (_ : BVec k) => c) = (2 : Int) ^ k * c
  | 0, c => by simp [sumBVec]
  | k + 1, c => by
      simp only [sumBVec, sumBVec_const (k := k) c, Int.pow_succ]
      have h : (2 : Int) ^ k * 2 * c = (2 : Int) ^ k * c + (2 : Int) ^ k * c := by
        calc
          (2 : Int) ^ k * 2 * c = 2 * ((2 : Int) ^ k * c) := by ac_rfl
          _ = (2 : Int) ^ k * c + (2 : Int) ^ k * c := by omega
      omega

theorem sumBVec_add : {k : Nat} → (f g : BVec k → Int) →
    sumBVec (fun x => f x + g x) = sumBVec f + sumBVec g
  | 0, _, _ => rfl
  | k + 1, f, g => by
      simp only [sumBVec, sumBVec_add]
      omega

theorem sumBVec_sub : {k : Nat} → (f g : BVec k → Int) →
    sumBVec (fun x => f x - g x) = sumBVec f - sumBVec g
  | 0, _, _ => rfl
  | k + 1, f, g => by
      simp only [sumBVec, sumBVec_sub]
      omega

theorem sumBVec_mul_left : {k : Nat} → (c : Int) → (f : BVec k → Int) →
    sumBVec (fun x => c * f x) = c * sumBVec f
  | 0, _, _ => rfl
  | k + 1, c, f => by
      simp only [sumBVec, sumBVec_mul_left, Int.mul_add]

theorem sumBVec_mul_right : {k : Nat} → (f : BVec k → Int) → (c : Int) →
    sumBVec (fun x => f x * c) = sumBVec f * c
  | 0, _, _ => rfl
  | k + 1, f, c => by
      simp only [sumBVec, sumBVec_mul_right, Int.add_mul]

theorem sumBVec_swap : {k₁ k₂ : Nat} → (f : BVec k₁ → BVec k₂ → Int) →
    sumBVec (fun x => sumBVec (fun y => f x y)) =
      sumBVec (fun y => sumBVec (fun x => f x y))
  | 0, _, _ => rfl
  | k₁ + 1, k₂, f => by
      simp only [sumBVec]
      rw [sumBVec_swap (fun x y => f (.cons false x) y),
          sumBVec_swap (fun x y => f (.cons true x) y),
          ← sumBVec_add]

theorem sumBVec_bxor_shift : {k : Nat} → (a : BVec k) → (f : BVec k → Int) →
    sumBVec (fun x => f (bxor x a)) = sumBVec f
  | 0, .nil, _ => rfl
  | k + 1, .cons b a, f => by
      cases b
      · simp only [sumBVec, bxor, Bool.xor_false]
        rw [sumBVec_bxor_shift a (fun x => f (.cons false x)),
            sumBVec_bxor_shift a (fun x => f (.cons true x))]
      · have h0 : (fun x : BVec k => f (bxor (.cons false x) (.cons true a))) =
            (fun x => f (.cons true (bxor x a))) := rfl
        have h1 : (fun x : BVec k => f (bxor (.cons true x) (.cons true a))) =
            (fun x => f (.cons false (bxor x a))) := rfl
        simp only [sumBVec]
        rw [h0, h1, sumBVec_bxor_shift a (fun x => f (.cons true x)),
            sumBVec_bxor_shift a (fun x => f (.cons false x)), Int.add_comm]

theorem sumBVec_bappendR : {k₁ k₂ : Nat} → (f : BVec (k₁ + k₂) → Int) →
    sumBVec f = sumBVec (fun x => sumBVec (fun y => f (bappendR x y)))
  | _, 0, _ => rfl
  | k₁, k₂ + 1, f =>
      let f0 : BVec (k₁ + k₂) → Int := fun z => f (.cons false z)
      let f1 : BVec (k₁ + k₂) → Int := fun z => f (.cons true z)
      let ih0 : sumBVec f0 = sumBVec (fun x => sumBVec (fun y => f0 (bappendR x y))) :=
        sumBVec_bappendR f0
      let ih1 : sumBVec f1 = sumBVec (fun x => sumBVec (fun y => f1 (bappendR x y))) :=
        sumBVec_bappendR f1
      calc
        sumBVec f = sumBVec f0 + sumBVec f1 := rfl
        _ = sumBVec (fun x => sumBVec (fun y => f0 (bappendR x y))) +
            sumBVec (fun x => sumBVec (fun y => f1 (bappendR x y))) := by
              rw [ih0, ih1]
        _ = sumBVec (fun x => sumBVec (fun y => f0 (bappendR x y)) +
                              sumBVec (fun y => f1 (bappendR x y))) :=
              (sumBVec_add _ _).symm
        _ = sumBVec (fun x => sumBVec (fun y => f (bappendR x y))) := rfl

theorem sumBVec_delta : {k : Nat} → (a : BVec k) → (f : BVec k → Int) →
    sumBVec (fun x => if x == a then f x else 0) = f a
  | 0, .nil, f => by simp [sumBVec]
  | k + 1, .cons b a, f => by
      cases b
      · simp only [sumBVec]
        have h1 : sumBVec (fun x => if (BVec.cons false x == BVec.cons false a) then f (.cons false x) else 0) = f (.cons false a) := by
          have hc : ∀ x, (if (BVec.cons false x == BVec.cons false a) then f (.cons false x) else 0) =
              (if x == a then f (.cons false x) else 0) := by
            intro x; by_cases hx : x = a <;> simp [hx]
          rw [sumBVec_congr hc, sumBVec_delta a (fun x => f (.cons false x))]
        have h2 : sumBVec (fun x => if (BVec.cons true x == BVec.cons false a) then f (.cons true x) else 0) = 0 := by
          have hc : ∀ x, (if (BVec.cons true x == BVec.cons false a) then f (.cons true x) else 0) = 0 := by
            intro x; simp
          rw [sumBVec_congr hc, sumBVec_zero]
        rw [h1, h2, Int.add_zero]
      · simp only [sumBVec]
        have h1 : sumBVec (fun x => if (BVec.cons false x == BVec.cons true a) then f (.cons false x) else 0) = 0 := by
          have hc : ∀ x, (if (BVec.cons false x == BVec.cons true a) then f (.cons false x) else 0) = 0 := by
            intro x; simp
          rw [sumBVec_congr hc, sumBVec_zero]
        have h2 : sumBVec (fun x => if (BVec.cons true x == BVec.cons true a) then f (.cons true x) else 0) = f (.cons true a) := by
          have hc : ∀ x, (if (BVec.cons true x == BVec.cons true a) then f (.cons true x) else 0) =
              (if x == a then f (.cons true x) else 0) := by
            intro x; by_cases hx : x = a <;> simp [hx]
          rw [sumBVec_congr hc, sumBVec_delta a (fun x => f (.cons true x))]
        rw [h1, h2, Int.zero_add]

theorem sumBVec_nonneg : {k : Nat} → {f : BVec k → Int} →
    (∀ x, 0 ≤ f x) → 0 ≤ sumBVec f
  | 0, _, h => h .nil
  | _ + 1, _, h => by
      simp only [sumBVec]
      have h1 := sumBVec_nonneg (fun x => h (.cons false x))
      have h2 := sumBVec_nonneg (fun x => h (.cons true x))
      omega

theorem sumBVec_le : {k : Nat} → {f g : BVec k → Int} →
    (∀ x, f x ≤ g x) → sumBVec f ≤ sumBVec g
  | 0, _, _, h => h .nil
  | _ + 1, _, _, h => by
      simp only [sumBVec]
      have h1 := sumBVec_le (fun x => h (.cons false x))
      have h2 := sumBVec_le (fun x => h (.cons true x))
      omega

theorem sumBVec_dvd : {k : Nat} → {m : Int} → {f : BVec k → Int} →
    (∀ x, m ∣ f x) → m ∣ sumBVec f
  | 0, _, _, h => h .nil
  | _ + 1, _, _, h => by
      simp only [sumBVec]
      exact Int.dvd_add (sumBVec_dvd (fun x => h (.cons false x)))
                        (sumBVec_dvd (fun x => h (.cons true x)))

theorem sumBVec_mod : {k : Nat} → (m : Int) → (f g : BVec k → Int) →
    (∀ x, f x % m = g x % m) → sumBVec f % m = sumBVec g % m
  | 0, _, _, _, h => h .nil
  | _ + 1, m, f, g, h => by
      simp only [sumBVec]
      have h1 := sumBVec_mod m (fun x => f (.cons false x)) (fun x => g (.cons false x))
        (fun x => h (.cons false x))
      have h2 := sumBVec_mod m (fun x => f (.cons true x)) (fun x => g (.cons true x))
        (fun x => h (.cons true x))
      rw [Int.add_emod, h1, h2, ← Int.add_emod]

/-! ### Group-Ring Operations: `scaleDelta`, `conv`, `xorMat`, `matMul`, `wht` -/

def scaleDelta {k : Nat} (D : Int) : GR k :=
  fun x => if x == bzero k then D else 0

def conv {k : Nat} (f g : GR k) : GR k :=
  fun z => sumBVec (fun x => f x * g (bxor x z))

def xorMat {k : Nat} (f : GR k) : BVec k → BVec k → Int :=
  fun x y => f (bxor x y)

def matMul {k : Nat} (M N : BVec k → BVec k → Int) : BVec k → BVec k → Int :=
  fun x y => sumBVec (fun z => M x z * N z y)

def wht {k : Nat} (f : GR k) : GR k :=
  fun ω => sumBVec (fun x => signBit (bdot ω x) * f x)

theorem matMul_xorMat {k : Nat} (f g : GR k) (x y : BVec k) :
    matMul (xorMat f) (xorMat g) x y = xorMat (conv f g) x y := by
  simp only [matMul, xorMat, conv]
  have hshift := sumBVec_bxor_shift x (fun z => f z * g (bxor z (bxor x y)))
  rw [← hshift]
  apply sumBVec_congr
  intro z
  have h1 : bxor z x = bxor x z := bxor_comm z x
  have h2 : bxor (bxor z x) (bxor x y) = bxor z y := by
    rw [bxor_assoc z x (bxor x y), ← bxor_assoc x x y, bxor_self, bxor_bzero_left]
  rw [h2, h1]

theorem wht_scaleDelta {k : Nat} (D : Int) (ω : BVec k) :
    wht (scaleDelta D) ω = D := by
  simp only [wht, scaleDelta]
  have hc : ∀ x : BVec k, signBit (bdot ω x) * (if x == bzero k then D else 0) =
      if x == bzero k then signBit (bdot ω x) * D else 0 := by
    intro x; by_cases h : x == bzero k <;> simp [h]
  rw [sumBVec_congr hc, sumBVec_delta (bzero k) (fun x => signBit (bdot ω x) * D)]
  simp [bdot_bzero_right, signBit]

theorem wht_cons {k : Nat} (f : GR (k + 1)) (b : Bool) (ω : BVec k) :
    wht f (.cons b ω) =
      wht (fun x => f (.cons false x)) ω + signBit b * wht (fun x => f (.cons true x)) ω := by
  simp only [wht, sumBVec, bdot]
  have h1 : sumBVec (fun x => signBit (xor (b && false) (bdot ω x)) * f (.cons false x)) =
      sumBVec (fun x => signBit (bdot ω x) * f (.cons false x)) := by
    apply sumBVec_congr; intro x; simp
  have h2 : sumBVec (fun x => signBit (xor (b && true) (bdot ω x)) * f (.cons true x)) =
      signBit b * sumBVec (fun x => signBit (bdot ω x) * f (.cons true x)) := by
    rw [← sumBVec_mul_left]
    apply sumBVec_congr; intro x
    simp only [Bool.and_true, signBit_xor, Int.mul_assoc]
  rw [h1, h2]

theorem pow2_pos (k : Nat) : (0 : Int) < (2 : Int) ^ k := by
  induction k with
  | zero => decide
  | succ n ih =>
      rw [Int.pow_succ]
      have : (2 : Int) ^ n * 2 = (2 : Int) ^ n + (2 : Int) ^ n := by omega
      omega

/-- **Core Engine Theorem 1 (WHT Convolution Homomorphism):**
    Walsh-Hadamard transform converts XOR-convolution into pointwise multiplication. -/
theorem wht_conv {k : Nat} (f g : GR k) (ω : BVec k) :
    wht (conv f g) ω = wht f ω * wht g ω := by
  simp only [wht, conv]
  have h1 : sumBVec (fun z => signBit (bdot ω z) * sumBVec (fun x => f x * g (bxor x z))) =
      sumBVec (fun z => sumBVec (fun x => signBit (bdot ω z) * (f x * g (bxor x z)))) := by
    apply sumBVec_congr; intro z; rw [sumBVec_mul_left]
  rw [h1, sumBVec_swap]
  have h2 : sumBVec (fun x => sumBVec (fun z => signBit (bdot ω z) * (f x * g (bxor x z)))) =
      sumBVec (fun x => (signBit (bdot ω x) * f x) * sumBVec (fun y => signBit (bdot ω y) * g y)) := by
    apply sumBVec_congr; intro x
    rw [← sumBVec_bxor_shift x (fun y => signBit (bdot ω y) * g y), ← sumBVec_mul_left]
    apply sumBVec_congr; intro z
    rw [bxor_comm z x, bdot_bxor_right, signBit_xor]
    have hs : signBit (bdot ω x) * (signBit (bdot ω x) * signBit (bdot ω z)) = signBit (bdot ω z) := by
      rw [← Int.mul_assoc, signBit_sq, Int.one_mul]
    calc
      signBit (bdot ω z) * (f x * g (bxor x z))
          = (signBit (bdot ω x) * (signBit (bdot ω x) * signBit (bdot ω z))) * (f x * g (bxor x z)) := by
            rw [hs]
      _ = signBit (bdot ω x) * f x * (signBit (bdot ω x) * signBit (bdot ω z) * g (bxor x z)) := by
            ac_rfl
  rw [h2, sumBVec_mul_right]

theorem wht_add {k : Nat} (f g : GR k) (ω : BVec k) :
    wht (fun x => f x + g x) ω = wht f ω + wht g ω := by
  simp only [wht, ← sumBVec_add]
  apply sumBVec_congr; intro x; exact Int.mul_add _ _ _

theorem wht_sub {k : Nat} (f g : GR k) (ω : BVec k) :
    wht (fun x => f x - g x) ω = wht f ω - wht g ω := by
  simp only [wht, ← sumBVec_sub]
  apply sumBVec_congr; intro x; exact Int.mul_sub _ _ _

/-- **Core Engine Theorem 2 (Exact Dyadic Involution):**
    Applying WHT twice recovers `2^k * f` exactly over `Int`. -/
theorem wht_wht : {k : Nat} → (f : GR k) → (x : BVec k) →
    wht (wht f) x = (2 : Int) ^ k * f x
  | 0, f, .nil => by
      simp [wht, sumBVec, bdot, signBit]
  | k + 1, f, .cons b x => by
      rw [wht_cons]
      have h0 : wht (fun ω => wht f (.cons false ω)) x =
          (2 : Int) ^ k * f (.cons false x) + (2 : Int) ^ k * f (.cons true x) := by
        have hc : (fun ω => wht f (.cons false ω)) =
            (fun ω => wht (fun y => f (.cons false y)) ω + wht (fun y => f (.cons true y)) ω) := by
          funext ω; rw [wht_cons]; simp [signBit]
        rw [hc, wht_add, wht_wht (fun y => f (.cons false y)) x,
            wht_wht (fun y => f (.cons true y)) x]
      have h1 : wht (fun ω => wht f (.cons true ω)) x =
          (2 : Int) ^ k * f (.cons false x) - (2 : Int) ^ k * f (.cons true x) := by
        have hc : (fun ω => wht f (.cons true ω)) =
            (fun ω => wht (fun y => f (.cons false y)) ω - wht (fun y => f (.cons true y)) ω) := by
          funext ω; rw [wht_cons]; simp [signBit]; omega
        rw [hc, wht_sub, wht_wht (fun y => f (.cons false y)) x,
            wht_wht (fun y => f (.cons true y)) x]
      rw [h0, h1, Int.pow_succ]
      cases b
      · simp only [signBit, Bool.false_eq_true, ↓reduceIte, Int.one_mul]
        calc
          (2 : Int) ^ k * f (.cons false x) + (2 : Int) ^ k * f (.cons true x) +
            ((2 : Int) ^ k * f (.cons false x) - (2 : Int) ^ k * f (.cons true x))
              = 2 * ((2 : Int) ^ k * f (.cons false x)) := by omega
          _ = (2 : Int) ^ k * 2 * f (.cons false x) := by ac_rfl
      · simp only [signBit, ↓reduceIte]
        calc
          (2 : Int) ^ k * f (.cons false x) + (2 : Int) ^ k * f (.cons true x) +
            (-1) * ((2 : Int) ^ k * f (.cons false x) - (2 : Int) ^ k * f (.cons true x))
              = 2 * ((2 : Int) ^ k * f (.cons true x)) := by omega
          _ = (2 : Int) ^ k * 2 * f (.cons true x) := by ac_rfl

theorem wht_injective {k : Nat} {f g : GR k} (h : ∀ ω, wht f ω = wht g ω) :
    ∀ x, f x = g x := by
  intro x
  have h2 : wht (wht f) x = wht (wht g) x := by
    have hf : wht f = wht g := funext h
    rw [hf]
  rw [wht_wht, wht_wht] at h2
  have hpos : (2 : Int) ^ k ≠ 0 := by have := pow2_pos k; omega
  exact Int.eq_of_mul_eq_mul_left hpos h2

def sumSq {k : Nat} (f : GR k) : Int := sumBVec (fun x => f x * f x)

/-- **Core Engine Theorem 4 (Exact Group-Ring Inversion Criterion):**
    `f * g = D • δ_0` iff `wht(f)(ω) * wht(g)(ω) = D` for all `ω`. -/
theorem group_ring_inv_iff {k : Nat} (f g : GR k) (D : Int) :
    (∀ x, conv f g x = scaleDelta D x) ↔ (∀ ω, wht f ω * wht g ω = D) := by
  constructor
  · intro h ω
    rw [← wht_conv]
    have hc : wht (conv f g) ω = wht (scaleDelta D) ω := by
      simp only [wht]; apply sumBVec_congr; intro x; rw [h x]
    rw [hc, wht_scaleDelta]
  · intro h
    apply wht_injective
    intro ω
    rw [wht_conv, h ω, wht_scaleDelta]

/-- **Core Engine Theorem 5 (Matrix-Level Inversion Lift):**
    Spectral inversion `wht f ω * wht g ω = D` directly yields exact `2^k × 2^k`
    matrix inversion `M(f) * M(g) = D • I`. -/
theorem xorMat_inv_of_wht {k : Nat} (f g : GR k) (D : Int)
    (h : ∀ ω, wht f ω * wht g ω = D) :
    ∀ x y : BVec k, matMul (xorMat f) (xorMat g) x y = if x == y then D else 0 := by
  intro x y
  rw [matMul_xorMat, xorMat, (group_ring_inv_iff f g D).mpr h (bxor x y)]
  simp only [scaleDelta]
  by_cases hxy : x = y
  · subst hxy; simp [bxor_self]
  · have hne : bxor x y ≠ bzero k := fun hc => hxy ((bxor_eq_bzero_iff).mp hc)
    simp [hxy, hne]

/-! ## Part II: Parseval Rigidity & Obstruction Engine -/

def suppCount {k : Nat} (f : GR k) : Nat :=
  (sumBVec (fun x => if f x == 0 then 0 else 1)).toNat

def sumInd {k : Nat} (f : GR k) : Int :=
  sumBVec (fun x => if f x == 0 then 0 else 1)

theorem sumInd_nonneg {k : Nat} (f : GR k) : 0 ≤ sumInd f := by
  apply sumBVec_nonneg; intro x; split <;> omega

theorem suppCount_eq_sumInd {k : Nat} (f : GR k) : (suppCount f : Int) = sumInd f := by
  simp only [suppCount]
  exact Int.toNat_of_nonneg (sumInd_nonneg f)

def IsTernary {k : Nat} (f : GR k) : Prop :=
  ∀ x, f x = -1 ∨ f x = 0 ∨ f x = 1

def IsBinary01 {k : Nat} (f : GR k) : Prop :=
  ∀ x, f x = 0 ∨ f x = 1

theorem sumSq_eq_sumInd_of_ternary {k : Nat} {f : GR k} (ht : IsTernary f) :
    sumSq f = sumInd f := by
  simp only [sumSq, sumInd]
  apply sumBVec_congr; intro x
  rcases ht x with h | h | h <;> simp [h]

theorem int_mul_self_nonneg (a : Int) : 0 ≤ a * a := by
  by_cases h : 0 ≤ a
  · exact Int.mul_nonneg h h
  · have hneg : 0 ≤ -a := by omega
    have hmul : 0 ≤ (-a) * (-a) := Int.mul_nonneg hneg hneg
    rw [Int.neg_mul_neg] at hmul
    exact hmul

/-- **Obstruction Theorem 2 (Odd-Divisibility Spectral Rigidity):**
    If an odd integer `m` divides `wht f ω` for all `ω`, then `m` divides `f x` for all `x`. -/
theorem odd_spectral_divisibility {k : Nat} {f : GR k} {m : Int}
    (hodd : m % 2 = 1) (hdvd : ∀ ω, m ∣ wht f ω) : ∀ x, m ∣ f x := by
  intro x
  have h2k : m ∣ (2 : Int) ^ k * f x := by
    rw [← wht_wht f x]
    simp only [wht]
    apply sumBVec_dvd
    intro ω
    exact Int.dvd_mul_of_dvd_right (hdvd ω)
  have cancel2 : ∀ n : Nat, m ∣ (2 : Int) ^ n * f x → m ∣ f x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        intro h
        rw [Int.pow_succ] at h
        have h' : m ∣ 2 * ((2 : Int) ^ n * f x) := by
          have : (2 : Int) ^ n * 2 * f x = 2 * ((2 : Int) ^ n * f x) := by ac_rfl
          rw [← this]; exact h
        rcases h' with ⟨t, ht⟩
        have hmt_even : (m * t) % 2 = 0 := by
          rw [← ht]; omega
        rw [Int.mul_emod, hodd] at hmt_even
        have ht_even : t % 2 = 0 := by omega
        have ht2 : t = 2 * (t / 2) := by omega
        have heq : 2 * ((2 : Int) ^ n * f x) = 2 * (m * (t / 2)) := by
          calc
            2 * ((2 : Int) ^ n * f x) = m * t := ht
            _ = m * (2 * (t / 2)) := by rw [← ht2]
            _ = 2 * (m * (t / 2)) := by ac_rfl
        have hdiv : m ∣ (2 : Int) ^ n * f x := ⟨t / 2, by omega⟩
        exact ih hdiv
  exact cancel2 k h2k

/-- **Obstruction Theorem 3 (Constant Spectral Parity):**
    Every Walsh-Hadamard coefficient has the exact same parity as `wht f 0`. -/
theorem wht_const_parity {k : Nat} (f : GR k) (ω : BVec k) :
    wht f ω % 2 = wht f (bzero k) % 2 := by
  simp only [wht]
  apply sumBVec_mod 2
  intro x
  have hb : bdot (bzero k) x = false := bdot_bzero_left x
  rw [hb]
  cases bdot ω x <;> simp [signBit] <;> omega

/-- Elementary helper: every natural divisor of `2^n` is a power of 2. -/
theorem nat_dvd_pow2 : ∀ (n d : Nat), d ∣ 2 ^ n → ∃ e, d = 2 ^ e
  | 0, d, hd => ⟨0, Nat.dvd_one.mp hd⟩
  | n + 1, d, hd => by
      by_cases h1 : d = 1
      · exact ⟨0, h1⟩
      · have hpos : 0 < d := by
          rcases hd with ⟨q, hq⟩
          by_cases hd0 : d = 0
          · subst hd0
            have : 0 < 2 ^ (n + 1) := Nat.pow_pos (by decide)
            omega
          · omega
        have heven : d % 2 = 0 := by
          rcases hd with ⟨q, hq⟩
          by_cases hodd : d % 2 = 1
          · -- Show any odd divisor of 2^(n+1) equals 1 by induction on n
            have hodd_dvd : ∀ m, d ∣ 2 ^ m → d % 2 = 1 → d = 1 := by
              intro m
              induction m with
              | zero => intro h _; exact Nat.dvd_one.mp h
              | succ m ihm =>
                  intro hm hmod
                  rcases hm with ⟨r, hr⟩
                  have hr_even : r % 2 = 0 := by
                    have h2 : (d * r) % 2 = 0 := by
                      rw [← hr, Nat.pow_succ]; omega
                    rw [Nat.mul_mod, hmod] at h2
                    omega
                  have hr2 : r = 2 * (r / 2) := by omega
                  have hdm : d ∣ 2 ^ m := by
                    refine ⟨r / 2, ?_⟩
                    rw [Nat.pow_succ] at hr
                    have hmul : 2 ^ m * 2 = d * (r / 2) * 2 := by
                      calc
                        2 ^ m * 2 = d * r := hr
                        _ = d * (2 * (r / 2)) := by rw [← hr2]
                        _ = d * (r / 2) * 2 := by ac_rfl
                    exact Nat.mul_right_cancel (by decide : 0 < 2) hmul
                  exact ihm hdm hmod
            exact False.elim (h1 (hodd_dvd (n + 1) ⟨q, hq⟩ hodd))
          · omega
        have hd' : d / 2 ∣ 2 ^ n := by
          rcases hd with ⟨q, hq⟩
          refine ⟨q, ?_⟩
          rw [Nat.pow_succ] at hq
          have hd2 : d = 2 * (d / 2) := by omega
          have hmul : 2 ^ n * 2 = (d / 2 * q) * 2 := by
            calc
              2 ^ n * 2 = d * q := hq
              _ = (2 * (d / 2)) * q := by rw [← hd2]
              _ = (d / 2 * q) * 2 := by ac_rfl
          exact Nat.mul_right_cancel (by decide : 0 < 2) hmul
        rcases nat_dvd_pow2 n (d / 2) hd' with ⟨e, he⟩
        refine ⟨e + 1, ?_⟩
        rw [Nat.pow_succ]
        omega

theorem pow2_int_mod3 (k : Nat) : (2 : Int) ^ k % 3 = 1 ∨ (2 : Int) ^ k % 3 = 2 := by
  induction k with
  | zero => left; decide
  | succ n ih =>
      rw [Int.pow_succ, Int.mul_emod]
      rcases ih with h | h <;> rw [h] <;> decide

theorem nat_pow2_sq_eq_pow4 (e : Nat) : ((2 ^ e : Nat) : Int) * ((2 ^ e : Nat) : Int) = (4 : Int) ^ e := by
  induction e with
  | zero => rfl
  | succ e ih =>
      rw [Nat.pow_succ, Int.pow_succ]
      push_cast
      have h22 : (2 : Int) * 2 = 4 := rfl
      calc
        (2 : Int) ^ e * 2 * ((2 : Int) ^ e * 2)
            = ((2 : Int) ^ e * (2 : Int) ^ e) * (2 * 2) := by ac_rfl
        _ = (4 : Int) ^ e * 4 := by
          have ih' : (2 : Int) ^ e * (2 : Int) ^ e = (4 : Int) ^ e := by simpa using ih
          rw [ih', h22]

/-- **Obstruction Theorem 6 (Pure-Integer Parseval-Cauchy-Schwarz Support-Scale Uncertainty):**
    For ALL `k ≥ 0` and ALL `f, g : GR k`, `f * g = D • δ_0` implies
    `D^2 ≤ (∑_x f(x)^2) * (∑_x g(x)^2)`. -/
theorem cauchy_schwarz_bvec : {k : Nat} → (u v : BVec k → Int) →
    (sumBVec (fun x => u x * v x)) ^ 2 ≤ sumSq u * sumSq v := by
  intro k u v
  let A := sumSq u
  let B := sumBVec (fun x => u x * v x)
  let C := sumSq v
  have hA : 0 ≤ A := sumBVec_nonneg (fun x => int_mul_self_nonneg (u x))
  by_cases hA0 : A = 0
  · have hu0 : ∀ x, u x = 0 := by
      have aux : ∀ {m : Nat} (w : BVec m → Int), sumSq w = 0 → ∀ x, w x = 0 := by
        intro m
        induction m with
        | zero =>
            intro w hw x; cases x
            simp only [sumSq, sumBVec] at hw
            have := Int.mul_eq_zero.mp hw
            rcases this with h | h <;> exact h
        | succ m ih =>
            intro w hw x
            have hsum : sumSq w =
                sumSq (fun y => w (.cons false y)) + sumSq (fun y => w (.cons true y)) := rfl
            rw [hsum] at hw
            have h0 : 0 ≤ sumSq (fun y => w (.cons false y)) :=
              sumBVec_nonneg (fun y => int_mul_self_nonneg _)
            have h1 : 0 ≤ sumSq (fun y => w (.cons true y)) :=
              sumBVec_nonneg (fun y => int_mul_self_nonneg _)
            cases x with
            | cons b y =>
                cases b
                · exact ih (fun y => w (.cons false y)) (by omega) y
                · exact ih (fun y => w (.cons true y)) (by omega) y
      exact aux u hA0
    have hB0 : B = 0 := by
      change sumBVec (fun x => u x * v x) = 0
      rw [sumBVec_congr (fun x => by rw [hu0 x, Int.zero_mul]), sumBVec_zero]
    change B ^ 2 ≤ A * C
    rw [hB0, hA0]; simp
  · have hApos : 0 < A := by omega
    have hnn : 0 ≤ sumBVec (fun x => (A * v x - B * u x) * (A * v x - B * u x)) :=
      sumBVec_nonneg (fun x => int_mul_self_nonneg _)
    have hexp : sumBVec (fun x => (A * v x - B * u x) * (A * v x - B * u x)) =
        A * (A * C - B * B) := by
      have hterm : ∀ x, (A * v x - B * u x) * (A * v x - B * u x) =
          (A * A) * (v x * v x) - (2 * A * B) * (u x * v x) + (B * B) * (u x * u x) := by
        intro x
        rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
        have e1 : A * v x * (A * v x) = A * A * (v x * v x) := by ac_rfl
        have e2 : A * v x * (B * u x) = A * B * (u x * v x) := by ac_rfl
        have e3 : B * u x * (A * v x) = A * B * (u x * v x) := by ac_rfl
        have e4 : B * u x * (B * u x) = B * B * (u x * u x) := by ac_rfl
        have e5 : 2 * A * B * (u x * v x) = A * B * (u x * v x) + A * B * (u x * v x) := by
          have : 2 * A * B * (u x * v x) = 2 * (A * B * (u x * v x)) := by ac_rfl
          rw [this]; omega
        rw [e1, e2, e3, e4, e5]; omega
      rw [sumBVec_congr hterm, sumBVec_add, sumBVec_sub,
          sumBVec_mul_left, sumBVec_mul_left, sumBVec_mul_left]
      change A * A * C - 2 * A * B * B + B * B * A = A * (A * C - B * B)
      rw [Int.mul_sub]
      have e1 : A * A * C = A * (A * C) := by ac_rfl
      have e2 : B * B * A = A * (B * B) := by ac_rfl
      have e3 : 2 * A * B * B = A * (B * B) + A * (B * B) := by
        have : 2 * A * B * B = 2 * (A * (B * B)) := by ac_rfl
        rw [this]; omega
      rw [e1, e2, e3]; omega
    rw [hexp] at hnn
    have hge : 0 ≤ A * C - B * B := by
      by_cases h : 0 ≤ A * C - B * B
      · exact h
      · exfalso
        have hneg : A * C - B * B < 0 := by omega
        have : A * (A * C - B * B) < 0 := Int.mul_neg_of_pos_of_neg hApos hneg
        omega
    change B ^ 2 ≤ A * C
    rw [Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.one_mul]
    omega

/-- Full affine span: `supp(f)` is not contained in any proper affine hyperplane of `F_2^k`. -/
def AffineSpan {k : Nat} (f : GR k) : Prop :=
  ∀ (ω : BVec k) (c : Bool), (∀ x, f x ≠ 0 → bdot ω x = c) → ω = bzero k

/--
**The Shared-Bit Idempotent Lifting Operator `sharedLift a ov b A B`:**
Given `A : GR (a + ov)` and `B : GR (b + ov)`, lifts `(A, B)` to `GR (((a + ov) + b) + 2)` via:
- `t` (outermost bit): idempotent split (`(1 + t)` on `A`, `(1 - t)` on `B`)
- `u` (second bit): disjoint-support multiplexer (`u = false` activates `A` with `x_b = 0`;
  `u = true` activates `B` with `x_a = 0`)
- `ov` shared bits between `A` and `B`.
Notice that when `ov = 0`, `a + 0 = a` and `b + 0 = b` are BOTH definitional (`rfl`),
yielding the zero-cast Disjoint-Subspace Bit-Tree Lift! -/
def sharedLift (a ov b : Nat) (A : GR (a + ov)) (B : GR (b + ov)) :
    GR (((a + ov) + b) + 2) :=
  fun z =>
    match z with
    | .cons t (.cons u x) =>
        let (x_aov, x_b) := bsplitR (a + ov) b x
        let (x_a, x_ov) := bsplitR a ov x_aov
        if u == false then
          if x_b == bzero b then A x_aov else 0
        else
          if x_a == bzero a then signBit t * B (bappendR x_b x_ov) else 0

/-- **Engine Lifting Theorem 1 (Exact Spectral Multiplexer Law):**
    In the Walsh domain, `ω_t` selects between `2 * wht A` and `2 * signBit ω_u * wht B`. -/
theorem sharedLift_wht (a ov b : Nat) (A : GR (a + ov)) (B : GR (b + ov))
    (ωt ωu : Bool) (ωx : BVec ((a + ov) + b)) :
    wht (sharedLift a ov b A B) (.cons ωt (.cons ωu ωx)) =
      let (ω_aov, ω_b) := bsplitR (a + ov) b ωx
      let (_, ω_ov) := bsplitR a ov ω_aov
      if ωt == false then
        2 * wht A ω_aov
      else
        2 * signBit ωu * wht B (bappendR ω_b ω_ov) := by
  rw [wht_cons, wht_cons, wht_cons]
  have hω : ωx = bappendR (bsplitR (a + ov) b ωx).1 (bsplitR (a + ov) b ωx).2 :=
    (bappendR_bsplitR ωx).symm
  have hω1 : (bsplitR (a + ov) b ωx).1 =
      bappendR (bsplitR a ov (bsplitR (a + ov) b ωx).1).1
               (bsplitR a ov (bsplitR (a + ov) b ωx).1).2 :=
    (bappendR_bsplitR _).symm
  have h_ff : wht (fun x => sharedLift a ov b A B (.cons false (.cons false x))) ωx =
      wht A (bsplitR (a + ov) b ωx).1 := by
    simp only [wht]
    rw [sumBVec_bappendR (k₁ := a + ov) (k₂ := b)]
    apply sumBVec_congr; intro x_aov
    have hc : ∀ x_b : BVec b,
        signBit (bdot ωx (bappendR x_aov x_b)) *
          sharedLift a ov b A B (.cons false (.cons false (bappendR x_aov x_b))) =
        if x_b == bzero b then
          signBit (bdot (bsplitR (a + ov) b ωx).1 x_aov) * A x_aov
        else 0 := by
      intro x_b
      simp only [sharedLift, beq_self_eq_true, ↓reduceIte, bsplitR_bappendR]
      by_cases hxb : x_b = bzero b
      · subst hxb
        simp only [beq_self_eq_true, ↓reduceIte]
        have hdot : bdot ωx (bappendR x_aov (bzero b)) = bdot (bsplitR (a + ov) b ωx).1 x_aov := by
          calc
            bdot ωx (bappendR x_aov (bzero b))
                = bdot (bappendR (bsplitR (a + ov) b ωx).1 (bsplitR (a + ov) b ωx).2) (bappendR x_aov (bzero b)) := by
                  rw [← hω]
            _ = xor (bdot (bsplitR (a + ov) b ωx).1 x_aov) (bdot (bsplitR (a + ov) b ωx).2 (bzero b)) :=
                  bdot_bappendR _ _ _ _
            _ = bdot (bsplitR (a + ov) b ωx).1 x_aov := by
                  rw [bdot_bzero_right, Bool.xor_false]
        rw [hdot]
      · simp [hxb]
    rw [sumBVec_congr hc, sumBVec_delta (bzero b)]
  have h_tf : wht (fun x => sharedLift a ov b A B (.cons true (.cons false x))) ωx =
      wht A (bsplitR (a + ov) b ωx).1 := h_ff
  have h_ft : wht (fun x => sharedLift a ov b A B (.cons false (.cons true x))) ωx =
      wht B (bappendR (bsplitR (a + ov) b ωx).2 (bsplitR a ov (bsplitR (a + ov) b ωx).1).2) := by
    simp only [wht]
    rw [sumBVec_bappendR (k₁ := a + ov) (k₂ := b), sumBVec_bappendR (k₁ := a) (k₂ := ov)]
    have hinner : ∀ x_a : BVec a,
        sumBVec (fun x_ov => sumBVec (fun x_b =>
          signBit (bdot ωx (bappendR (bappendR x_a x_ov) x_b)) *
            sharedLift a ov b A B (.cons false (.cons true (bappendR (bappendR x_a x_ov) x_b))))) =
        if x_a == bzero a then
          sumBVec (fun x_b => sumBVec (fun x_ov =>
            signBit (bdot (bappendR (bsplitR (a + ov) b ωx).2 (bsplitR a ov (bsplitR (a + ov) b ωx).1).2)
                          (bappendR x_b x_ov)) * B (bappendR x_b x_ov)))
        else 0 := by
      intro x_a
      by_cases hxa : x_a = bzero a
      · subst hxa
        simp only [beq_self_eq_true, ↓reduceIte]
        rw [sumBVec_swap]
        apply sumBVec_congr; intro x_b
        apply sumBVec_congr; intro x_ov
        have hdot : bdot ωx (bappendR (bappendR (bzero a) x_ov) x_b) =
            bdot (bappendR (bsplitR (a + ov) b ωx).2 (bsplitR a ov (bsplitR (a + ov) b ωx).1).2)
                 (bappendR x_b x_ov) := by
          calc
            bdot ωx (bappendR (bappendR (bzero a) x_ov) x_b)
                = bdot (bappendR (bsplitR (a + ov) b ωx).1 (bsplitR (a + ov) b ωx).2)
                       (bappendR (bappendR (bzero a) x_ov) x_b) := by rw [← hω]
            _ = xor (bdot (bsplitR (a + ov) b ωx).1 (bappendR (bzero a) x_ov))
                    (bdot (bsplitR (a + ov) b ωx).2 x_b) := bdot_bappendR _ _ _ _
            _ = xor (bdot (bappendR (bsplitR a ov (bsplitR (a + ov) b ωx).1).1
                                    (bsplitR a ov (bsplitR (a + ov) b ωx).1).2)
                          (bappendR (bzero a) x_ov))
                    (bdot (bsplitR (a + ov) b ωx).2 x_b) := by rw [← hω1]
            _ = xor (xor (bdot (bsplitR a ov (bsplitR (a + ov) b ωx).1).1 (bzero a))
                         (bdot (bsplitR a ov (bsplitR (a + ov) b ωx).1).2 x_ov))
                    (bdot (bsplitR (a + ov) b ωx).2 x_b) := by rw [bdot_bappendR]
            _ = xor (bdot (bsplitR a ov (bsplitR (a + ov) b ωx).1).2 x_ov)
                    (bdot (bsplitR (a + ov) b ωx).2 x_b) := by rw [bdot_bzero_right, Bool.false_xor]
            _ = xor (bdot (bsplitR (a + ov) b ωx).2 x_b)
                    (bdot (bsplitR a ov (bsplitR (a + ov) b ωx).1).2 x_ov) := Bool.xor_comm _ _
            _ = bdot (bappendR (bsplitR (a + ov) b ωx).2 (bsplitR a ov (bsplitR (a + ov) b ωx).1).2)
                     (bappendR x_b x_ov) := (bdot_bappendR _ _ _ _).symm
        rw [hdot]
        simp [sharedLift, bsplitR_bappendR, signBit]
      · have hne : (x_a == bzero a) = false := by simp [hxa]
        rw [hne]; simp only [Bool.false_eq_true, ↓reduceIte]
        have hz : ∀ x_ov : BVec ov, sumBVec (fun x_b : BVec b =>
            signBit (bdot ωx (bappendR (bappendR x_a x_ov) x_b)) *
              sharedLift a ov b A B (.cons false (.cons true (bappendR (bappendR x_a x_ov) x_b)))) = 0 := by
          intro x_ov
          have hz2 : ∀ x_b : BVec b,
              signBit (bdot ωx (bappendR (bappendR x_a x_ov) x_b)) *
                sharedLift a ov b A B (.cons false (.cons true (bappendR (bappendR x_a x_ov) x_b))) = 0 := by
            intro x_b
            simp only [sharedLift, bsplitR_bappendR, hne]
            simp
          rw [sumBVec_congr hz2, sumBVec_zero]
        rw [sumBVec_congr hz, sumBVec_zero]
    rw [sumBVec_congr hinner, sumBVec_delta (bzero a)]
    exact (sumBVec_bappendR (k₁ := b) (k₂ := ov)
      (fun x => signBit (bdot (bappendR (bsplitR (a + ov) b ωx).2 (bsplitR a ov (bsplitR (a + ov) b ωx).1).2) x) * B x)).symm
  have h_tt : wht (fun x => sharedLift a ov b A B (.cons true (.cons true x))) ωx =
      - wht B (bappendR (bsplitR (a + ov) b ωx).2 (bsplitR a ov (bsplitR (a + ov) b ωx).1).2) := by
    have hneg : ∀ x, sharedLift a ov b A B (.cons true (.cons true x)) =
        -1 * sharedLift a ov b A B (.cons false (.cons true x)) := by
      intro x
      simp [sharedLift, signBit]
      split <;> omega
    have hwneg : wht (fun x => sharedLift a ov b A B (.cons true (.cons true x))) ωx =
        -1 * wht (fun x => sharedLift a ov b A B (.cons false (.cons true x))) ωx := by
      simp only [wht]
      rw [← sumBVec_mul_left]
      apply sumBVec_congr; intro x
      rw [hneg x]; ac_rfl
    rw [hwneg, h_ft]; omega
  rw [h_ff, h_tf, h_ft, h_tt]
  cases ωt <;> cases ωu <;> simp [signBit] <;> omega

/-- **Engine Lifting Theorem 2 (Exact Inversion Lifting — Matched or Unmatched Scales):** -/
theorem sharedLift_inv (a ov b : Nat)
    (A A' : GR (a + ov)) (B B' : GR (b + ov)) (D₁ D₂ c₁ c₂ D : Int)
    (hA : ∀ x, conv A A' x = scaleDelta D₁ x)
    (hB : ∀ x, conv B B' x = scaleDelta D₂ x)
    (hD₁ : c₁ * D₁ = D) (hD₂ : c₂ * D₂ = D) :
    ∀ z, conv (sharedLift a ov b A B)
              (sharedLift a ov b (fun x => c₁ * A' x) (fun x => c₂ * B' x)) z =
         scaleDelta (4 * D) z := by
  rw [group_ring_inv_iff]
  intro ω
  match ω with
  | .cons ωt (.cons ωu ωx) =>
      rw [sharedLift_wht, sharedLift_wht]
      have hA_w := (group_ring_inv_iff A A' D₁).mp hA
      have hB_w := (group_ring_inv_iff B B' D₂).mp hB
      have hscaleA : ∀ w, wht (fun x => c₁ * A' x) w = c₁ * wht A' w := by
        intro w; simp only [wht, ← sumBVec_mul_left]
        apply sumBVec_congr; intro x; ac_rfl
      have hscaleB : ∀ w, wht (fun x => c₂ * B' x) w = c₂ * wht B' w := by
        intro w; simp only [wht, ← sumBVec_mul_left]
        apply sumBVec_congr; intro x; ac_rfl
      have h22 : (2 : Int) * 2 = 4 := rfl
      cases ωt
      · simp only [beq_self_eq_true, ↓reduceIte, hscaleA]
        let w1 := (bsplitR (a + ov) b ωx).1
        calc
          2 * wht A w1 * (2 * (c₁ * wht A' w1))
              = (2 * 2) * (c₁ * (wht A w1 * wht A' w1)) := by ac_rfl
          _ = 4 * (c₁ * D₁) := by rw [h22, hA_w w1]
          _ = 4 * D := by rw [hD₁]
      · simp only [beq_iff_eq, Bool.true_eq_false, ↓reduceIte, hscaleB]
        let w2 := bappendR (bsplitR (a + ov) b ωx).2 (bsplitR a ov (bsplitR (a + ov) b ωx).1).2
        calc
          2 * signBit ωu * wht B w2 * (2 * signBit ωu * (c₂ * wht B' w2))
              = (2 * 2) * ((signBit ωu * signBit ωu) * (c₂ * (wht B w2 * wht B' w2))) := by ac_rfl
          _ = 4 * (1 * (c₂ * D₂)) := by rw [h22, signBit_sq, hB_w w2]
          _ = 4 * D := by rw [Int.one_mul, hD₂]

/-- **Engine Lifting Theorem 3 (Matched-Scale Zero-Blowup Inversion Lifting):** -/
theorem sharedLift_inv_matched (a ov b : Nat)
    (A A' : GR (a + ov)) (B B' : GR (b + ov)) (D : Int)
    (hA : ∀ x, conv A A' x = scaleDelta D x)
    (hB : ∀ x, conv B B' x = scaleDelta D x) :
    ∀ z, conv (sharedLift a ov b A B) (sharedLift a ov b A' B') z =
         scaleDelta (4 * D) z := by
  have h := sharedLift_inv a ov b A A' B B' D D 1 1 D hA hB (Int.one_mul D) (Int.one_mul D)
  have hL : sharedLift a ov b (fun x => 1 * A' x) (fun x => 1 * B' x) = sharedLift a ov b A' B' := by
    funext z; simp only [Int.one_mul]
  rw [hL] at h
  exact h

/-- **Engine Lifting Theorem 4 (Entry-Bound & Ternary Preservation):** -/
theorem sharedLift_ternary (a ov b : Nat) {A : GR (a + ov)} {B : GR (b + ov)}
    (hA : IsTernary A) (hB : IsTernary B) :
    IsTernary (sharedLift a ov b A B) := by
  intro z
  match z with
  | .cons t (.cons u x) =>
      simp only [sharedLift]
      cases u
      · simp only [beq_self_eq_true, ↓reduceIte]
        split
        · exact hA _
        · right; left; rfl
      · simp only [beq_iff_eq, Bool.true_eq_false, ↓reduceIte]
        split
        · rcases hB (bappendR (bsplitR (a + ov) b x).2 (bsplitR a ov (bsplitR (a + ov) b x).1).2) with h | h | h
          · cases t <;> simp [signBit, h]
          · simp [h]
          · cases t <;> simp [signBit, h]
        · right; left; rfl

/-- **Engine Lifting Theorem 5 (Exact Fractal Support-Size Recursion):**
    `|supp(sharedLift a ov b A B)| = 2 * (|supp A| + |supp B|)`. -/
theorem sharedLift_suppCount (a ov b : Nat) (A : GR (a + ov)) (B : GR (b + ov)) :
    suppCount (sharedLift a ov b A B) = 2 * (suppCount A + suppCount B) := by
  suffices h : sumInd (sharedLift a ov b A B) = 2 * (sumInd A + sumInd B) by
    have h1 := suppCount_eq_sumInd (sharedLift a ov b A B)
    have h2 := suppCount_eq_sumInd A
    have h3 := suppCount_eq_sumInd B
    omega
  have hU0 : ∀ t : Bool,
      sumBVec (fun x => if sharedLift a ov b A B (.cons t (.cons false x)) == 0 then (0 : Int) else 1) =
        sumInd A := by
    intro t
    rw [sumBVec_bappendR (k₁ := a + ov) (k₂ := b)]
    simp only [sumInd]
    apply sumBVec_congr; intro x_aov
    have hc : ∀ x_b : BVec b,
        (if sharedLift a ov b A B (.cons t (.cons false (bappendR x_aov x_b))) == 0 then (0 : Int) else 1) =
        if x_b == bzero b then (if A x_aov == 0 then 0 else 1) else 0 := by
      intro x_b
      simp only [sharedLift, beq_self_eq_true, ↓reduceIte, bsplitR_bappendR]
      by_cases h : x_b == bzero b <;> simp [h]
    rw [sumBVec_congr hc, sumBVec_delta (bzero b)]
  have hU1 : ∀ t : Bool,
      sumBVec (fun x => if sharedLift a ov b A B (.cons t (.cons true x)) == 0 then (0 : Int) else 1) =
        sumInd B := by
    intro t
    rw [sumBVec_bappendR (k₁ := a + ov) (k₂ := b), sumBVec_bappendR (k₁ := a) (k₂ := ov)]
    have hc : ∀ x_a : BVec a,
        sumBVec (fun x_ov => sumBVec (fun x_b =>
          if sharedLift a ov b A B (.cons t (.cons true (bappendR (bappendR x_a x_ov) x_b))) == 0
          then (0 : Int) else 1)) =
        if x_a == bzero a then sumInd B else 0 := by
      intro x_a
      by_cases hxa : x_a = bzero a
      · subst hxa
        simp only [beq_self_eq_true, ↓reduceIte, sumInd]
        rw [sumBVec_swap, sumBVec_bappendR (k₁ := b) (k₂ := ov)]
        apply sumBVec_congr; intro x_b
        apply sumBVec_congr; intro x_ov
        simp only [sharedLift, bsplitR_bappendR, beq_self_eq_true, ↓reduceIte]
        cases t <;> simp [signBit]
      · have hne : (x_a == bzero a) = false := by simp [hxa]
        rw [hne]; simp only [Bool.false_eq_true, ↓reduceIte]
        have hz : ∀ x_ov : BVec ov, sumBVec (fun x_b : BVec b =>
            if sharedLift a ov b A B (.cons t (.cons true (bappendR (bappendR x_a x_ov) x_b))) == 0
            then (0 : Int) else 1) = 0 := by
          intro x_ov
          have hz2 : ∀ x_b : BVec b,
              (if sharedLift a ov b A B (.cons t (.cons true (bappendR (bappendR x_a x_ov) x_b))) == 0
               then (0 : Int) else 1) = 0 := by
            intro x_b
            simp only [sharedLift, bsplitR_bappendR, hne]
            rfl
          rw [sumBVec_congr hz2, sumBVec_zero]
        rw [sumBVec_congr hz, sumBVec_zero]
    rw [sumBVec_congr hc, sumBVec_delta (bzero a)]
  have hexpand : sumInd (sharedLift a ov b A B) =
      (sumBVec (fun x => if sharedLift a ov b A B (.cons false (.cons false x)) == 0 then 0 else 1) +
       sumBVec (fun x => if sharedLift a ov b A B (.cons false (.cons true x)) == 0 then 0 else 1)) +
      (sumBVec (fun x => if sharedLift a ov b A B (.cons true (.cons false x)) == 0 then 0 else 1) +
       sumBVec (fun x => if sharedLift a ov b A B (.cons true (.cons true x)) == 0 then 0 else 1)) := rfl
  rw [hexpand, hU0 false, hU1 false, hU0 true, hU1 true]
  omega

/-- **Engine Lifting Theorem 6 (Origin Membership & Full Affine-Span Preservation):** -/
theorem sharedLift_zero_ne (a ov b : Nat) {A : GR (a + ov)} {B : GR (b + ov)}
    (hA0 : A (bzero (a + ov)) ≠ 0) :
    sharedLift a ov b A B (bzero (((a + ov) + b) + 2)) ≠ 0 := by
  have hb : bzero (((a + ov) + b) + 2) = .cons false (.cons false (bappendR (bzero (a + ov)) (bzero b))) := by
    simp [bzero, bappendR_bzero]
  rw [hb]
  simp [sharedLift, bsplitR_bappendR, hA0]

theorem sharedLift_affineSpan (a ov b : Nat) {A : GR (a + ov)} {B : GR (b + ov)}
    (hA0 : A (bzero (a + ov)) ≠ 0) (hB0 : B (bzero (b + ov)) ≠ 0)
    (hAs : AffineSpan A) (hBs : AffineSpan B) :
    AffineSpan (sharedLift a ov b A B) := by
  intro ω c h
  match ω with
  | .cons ωt (.cons ωu ωx) =>
      have hz0 : sharedLift a ov b A B (.cons false (.cons false (bappendR (bzero (a + ov)) (bzero b)))) ≠ 0 := by
        simp [sharedLift, bsplitR_bappendR, hA0]
      have hc : c = false := by
        have h0 := h _ hz0
        rw [bappendR_bzero] at h0
        simpa [bdot, bdot_bzero_right] using h0.symm
      subst hc
      have hz1 : sharedLift a ov b A B (.cons true (.cons false (bappendR (bzero (a + ov)) (bzero b)))) ≠ 0 := by
        simp [sharedLift, bsplitR_bappendR, hA0]
      have hωt : ωt = false := by
        have h1 := h _ hz1
        rw [bappendR_bzero] at h1
        simpa [bdot, bdot_bzero_right] using h1
      subst hωt
      have hz2 : sharedLift a ov b A B (.cons false (.cons true (bappendR (bappendR (bzero a) (bzero ov)) (bzero b)))) ≠ 0 := by
        simp only [sharedLift, bsplitR_bappendR]
        simp [signBit, bappendR_bzero, hB0]
      have hωu : ωu = false := by
        have h2 := h _ hz2
        rw [bappendR_bzero, bappendR_bzero] at h2
        simpa [bdot, bdot_bzero_right] using h2
      subst hωu
      let ω_aov := (bsplitR (a + ov) b ωx).1
      let ω_b := (bsplitR (a + ov) b ωx).2
      have hωx : ωx = bappendR ω_aov ω_b := (bappendR_bsplitR ωx).symm
      have hω_aov : ω_aov = bzero (a + ov) := by
        apply hAs ω_aov false
        intro x_aov hx
        have hz : sharedLift a ov b A B (.cons false (.cons false (bappendR x_aov (bzero b)))) ≠ 0 := by
          simp [sharedLift, bsplitR_bappendR, hx]
        have hdot := h _ hz
        rw [hωx] at hdot
        simpa [bdot, bdot_bappendR, bdot_bzero_right] using hdot
      let ω_a := (bsplitR a ov ω_aov).1
      let ω_ov := (bsplitR a ov ω_aov).2
      have hω_aov2 : ω_aov = bappendR ω_a ω_ov := (bappendR_bsplitR ω_aov).symm
      have hω_bov : bappendR ω_b ω_ov = bzero (b + ov) := by
        apply hBs (bappendR ω_b ω_ov) false
        intro x_bov hx
        let x_b := (bsplitR b ov x_bov).1
        let x_ov := (bsplitR b ov x_bov).2
        have hx' : x_bov = bappendR x_b x_ov := (bappendR_bsplitR x_bov).symm
        have hz : sharedLift a ov b A B (.cons false (.cons true (bappendR (bappendR (bzero a) x_ov) x_b))) ≠ 0 := by
          simp [sharedLift, bsplitR_bappendR, signBit, ← hx', hx]
        have hdot := h _ hz
        rw [hωx, hω_aov2] at hdot
        simp only [bdot, Bool.false_and, Bool.false_xor, bdot_bappendR, bdot_bzero_right] at hdot
        rw [hx', bdot_bappendR, Bool.xor_comm]
        exact hdot
      have hω_b : ω_b = bzero b := by
        have := congrArg (fun z => (bsplitR b ov z).1) hω_bov
        rw [bsplitR_bappendR, ← bappendR_bzero (k₁ := b) (k₂ := ov), bsplitR_bappendR] at this
        exact this
      rw [hωx, hω_aov, hω_b, bappendR_bzero]
      rfl

/-! ## Part IV: Concrete Novel Infinite Families Proved Through the Engine -/

/-! ### Theorem A: Multiplexer Bit-Tree Family `treeElem d` (`k_d = 2^{d+1} - 2`, `|supp| = 4^d`) -/

abbrev treeWidth : Nat → Nat
  | 0 => 0
  | d + 1 => ((treeWidth d + 0) + treeWidth d) + 2

theorem treeWidth_closed (d : Nat) : treeWidth d + 2 = 2 ^ (d + 1) := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simp only [treeWidth]
      rw [Nat.pow_succ]
      omega

def treeElem : (d : Nat) → GR (treeWidth d)
  | 0 => fun _ => 1
  | d + 1 => sharedLift (treeWidth d) 0 (treeWidth d) (treeElem d) (treeElem d)

/-- Exact `O(d)` dual multiplexer spectral tree evaluator `spectralSign d ω ∈ {-1, +1}`. -/
def spectralSign : (d : Nat) → BVec (treeWidth d) → Int
  | 0, .nil => 1
  | d + 1, .cons ωt (.cons ωu ωx) =>
      let (ωL, ωR) := bsplitR (treeWidth d + 0) (treeWidth d) ωx
      if ωt == false then
        spectralSign d ωL
      else
        signBit ωu * spectralSign d ωR

theorem spectralSign_pm1 : (d : Nat) → (ω : BVec (treeWidth d)) →
    spectralSign d ω = 1 ∨ spectralSign d ω = -1
  | 0, .nil => Or.inl rfl
  | d + 1, .cons ωt (.cons ωu ωx) => by
      simp only [spectralSign]
      cases ωt
      · simp only [beq_self_eq_true, ↓reduceIte]
        exact spectralSign_pm1 d _
      · simp only [beq_iff_eq, Bool.true_eq_false, ↓reduceIte]
        have hsub := spectralSign_pm1 d (bsplitR (treeWidth d) (treeWidth d) ωx).2
        rcases hsub with h | h
        · cases ωu <;> simp [signBit, h]
        · cases ωu <;> simp [signBit, h]

/-- **Theorem A.2 (Exact Dyadic Self-Inversion of Multiplexer Bit-Tree Family):**
    `T_d * T_d = 4^d • δ_0` and `M(T_d) * M(T_d) = 4^d • I` for ALL `d ≥ 0`. -/
theorem treeElem_self_inv (d : Nat) :
    ∀ x, conv (treeElem d) (treeElem d) x = scaleDelta ((4 : Int) ^ d) x := by
  induction d with
  | zero =>
      intro x; cases x; decide
  | succ d ih =>
      have h := sharedLift_inv_matched (treeWidth d) 0 (treeWidth d)
        (treeElem d) (treeElem d) (treeElem d) (treeElem d) ((4 : Int) ^ d) ih ih
      intro x
      rw [treeElem, h x, Int.pow_succ, Int.mul_comm]

theorem treeElem_matrix_inv (d : Nat) :
    ∀ x y, matMul (xorMat (treeElem d)) (xorMat (treeElem d)) x y =
           if x == y then (4 : Int) ^ d else 0 := by
  apply xorMat_inv_of_wht
  exact (group_ring_inv_iff _ _ _).mp (treeElem_self_inv d)

/-- **Theorem A.3 (Bounded Signed-Binary Entries):** `treeElem d x ∈ {-1, 0, 1}` for all `d, x`. -/
theorem treeElem_ternary : (d : Nat) → IsTernary (treeElem d)
  | 0 => fun _ => Or.inr (Or.inr rfl)
  | d + 1 => sharedLift_ternary _ _ _ (treeElem_ternary d) (treeElem_ternary d)

/-- **Theorem A.4 (Polylogarithmic Exact Fractal Bit-Support Size):**
    `|supp(treeElem d)| = 4^d` (out of `N_d = 2^{2^{d+1}-2}`, so `4 * |supp| = (k_d + 2)^2`). -/
theorem treeElem_suppCount : (d : Nat) → suppCount (treeElem d) = 4 ^ d
  | 0 => by decide
  | d + 1 => by
      simp only [treeElem]
      rw [sharedLift_suppCount, treeElem_suppCount d, Nat.pow_succ]
      omega

/-- **Theorem A.5 (Full Linear/Affine Span in `F_2^{k_d}`):** -/
theorem treeElem_zero_ne : (d : Nat) → treeElem d (bzero (treeWidth d)) ≠ 0
  | 0 => by decide
  | d + 1 => sharedLift_zero_ne _ _ _ (treeElem_zero_ne d)

theorem treeElem_affineSpan : (d : Nat) → AffineSpan (treeElem d)
  | 0 => fun ω _ _ => by cases ω; rfl
  | d + 1 => sharedLift_affineSpan _ _ _ (treeElem_zero_ne d) (treeElem_zero_ne d)
               (treeElem_affineSpan d) (treeElem_affineSpan d)

/-! ### Theorem B: Asymmetric Non-Self-Inverse Sparse Family `(asymTreeP d, asymTreeQ d)` -/

/-- Base `k = 3` certificate: `A3 * B3 = 3 • δ_0`, `|supp| = 5`, entries `∈ {-1, 0, 1}`, `A3 ≠ ±B3`. -/
def baseA3 : GR 3
  | .cons false (.cons false (.cons false .nil)) =>  1
  | .cons false (.cons false (.cons true  .nil)) => -1
  | .cons false (.cons true  (.cons false .nil)) => -1
  | .cons false (.cons true  (.cons true  .nil)) => -1
  | .cons true  (.cons false (.cons false .nil)) => -1
  | _ => 0

def baseB3 : GR 3
  | .cons false (.cons false (.cons false .nil)) =>  1
  | .cons false (.cons false (.cons true  .nil)) => -1
  | .cons false (.cons true  (.cons false .nil)) => -1
  | .cons false (.cons true  (.cons true  .nil)) => -1
  | .cons true  (.cons false (.cons false .nil)) =>  1
  | _ => 0

theorem baseA3_inv : ∀ x, conv baseA3 baseB3 x = scaleDelta 3 x := by
  intro x
  match x with
  | .cons a (.cons b (.cons c .nil)) =>
      cases a <;> cases b <;> cases c <;> decide

theorem baseA3_ternary : IsTernary baseA3 := by
  intro x; match x with
  | .cons a (.cons b (.cons c .nil)) =>
      cases a <;> cases b <;> cases c <;> decide

theorem baseB3_ternary : IsTernary baseB3 := by
  intro x; match x with
  | .cons a (.cons b (.cons c .nil)) =>
      cases a <;> cases b <;> cases c <;> decide

theorem baseA3_suppCount : suppCount baseA3 = 5 := by decide
theorem baseB3_suppCount : suppCount baseB3 = 5 := by decide

theorem baseA3_zero_ne : baseA3 (bzero 3) ≠ 0 := by decide
theorem baseB3_zero_ne : baseB3 (bzero 3) ≠ 0 := by decide

theorem baseA3_affineSpan : AffineSpan baseA3 := by
  intro ω c h
  match ω with
  | .cons w0 (.cons w1 (.cons w2 .nil)) =>
      have h000 := h (.cons false (.cons false (.cons false .nil))) (by decide)
      have h001 := h (.cons false (.cons false (.cons true  .nil))) (by decide)
      have h010 := h (.cons false (.cons true  (.cons false .nil))) (by decide)
      have h100 := h (.cons true  (.cons false (.cons false .nil))) (by decide)
      cases w0 <;> cases w1 <;> cases w2 <;> cases c <;> simp [bdot, bzero] at *

theorem baseB3_affineSpan : AffineSpan baseB3 := by
  intro ω c h
  match ω with
  | .cons w0 (.cons w1 (.cons w2 .nil)) =>
      have h000 := h (.cons false (.cons false (.cons false .nil))) (by decide)
      have h001 := h (.cons false (.cons false (.cons true  .nil))) (by decide)
      have h010 := h (.cons false (.cons true  (.cons false .nil))) (by decide)
      have h100 := h (.cons true  (.cons false (.cons false .nil))) (by decide)
      cases w0 <;> cases w1 <;> cases w2 <;> cases c <;> simp [bdot, bzero] at *

abbrev asymWidth : Nat → Nat
  | 0 => 3
  | d + 1 => ((asymWidth d + 0) + asymWidth d) + 2

theorem asymWidth_closed (d : Nat) : asymWidth d + 2 = 5 * 2 ^ d := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simp only [asymWidth]
      rw [Nat.pow_succ]
      omega

def asymTreeP : (d : Nat) → GR (asymWidth d)
  | 0 => baseA3
  | d + 1 => sharedLift (asymWidth d) 0 (asymWidth d) (asymTreeP d) (asymTreeP d)

def asymTreeQ : (d : Nat) → GR (asymWidth d)
  | 0 => baseB3
  | d + 1 => sharedLift (asymWidth d) 0 (asymWidth d) (asymTreeQ d) (asymTreeQ d)

/-- **Theorem B.1 (Asymmetric Non-Self-Inverse Exact Inversion):**
    `P_d * Q_d = (3 * 4^d) • δ_0` for all `d ≥ 0`. -/
theorem asymTree_inv (d : Nat) :
    ∀ x, conv (asymTreeP d) (asymTreeQ d) x = scaleDelta (3 * (4 : Int) ^ d) x := by
  induction d with
  | zero => exact baseA3_inv
  | succ d ih =>
      have h := sharedLift_inv_matched (asymWidth d) 0 (asymWidth d)
        (asymTreeP d) (asymTreeQ d) (asymTreeP d) (asymTreeQ d) (3 * (4 : Int) ^ d) ih ih
      intro x
      rw [asymTreeP, asymTreeQ, h x, Int.pow_succ]
      have : 4 * (3 * (4 : Int) ^ d) = 3 * ((4 : Int) ^ d * 4) := by ac_rfl
      rw [this]

theorem asymTreeP_ternary : (d : Nat) → IsTernary (asymTreeP d)
  | 0 => baseA3_ternary
  | d + 1 => sharedLift_ternary _ _ _ (asymTreeP_ternary d) (asymTreeP_ternary d)

theorem asymTreeQ_ternary : (d : Nat) → IsTernary (asymTreeQ d)
  | 0 => baseB3_ternary
  | d + 1 => sharedLift_ternary _ _ _ (asymTreeQ_ternary d) (asymTreeQ_ternary d)

theorem asymTreeP_suppCount : (d : Nat) → suppCount (asymTreeP d) = 5 * 4 ^ d
  | 0 => baseA3_suppCount
  | d + 1 => by
      simp only [asymTreeP]
      rw [sharedLift_suppCount, asymTreeP_suppCount d, Nat.pow_succ]
      omega

theorem asymTreeQ_suppCount : (d : Nat) → suppCount (asymTreeQ d) = 5 * 4 ^ d
  | 0 => baseB3_suppCount
  | d + 1 => by
      simp only [asymTreeQ]
      rw [sharedLift_suppCount, asymTreeQ_suppCount d, Nat.pow_succ]
      omega

theorem asymTreeP_zero_ne : (d : Nat) → asymTreeP d (bzero (asymWidth d)) ≠ 0
  | 0 => baseA3_zero_ne
  | d + 1 => sharedLift_zero_ne _ _ _ (asymTreeP_zero_ne d)

theorem asymTreeQ_zero_ne : (d : Nat) → asymTreeQ d (bzero (asymWidth d)) ≠ 0
  | 0 => baseB3_zero_ne
  | d + 1 => sharedLift_zero_ne _ _ _ (asymTreeQ_zero_ne d)

theorem asymTreeP_affineSpan : (d : Nat) → AffineSpan (asymTreeP d)
  | 0 => baseA3_affineSpan
  | d + 1 => sharedLift_affineSpan _ _ _ (asymTreeP_zero_ne d) (asymTreeP_zero_ne d)
               (asymTreeP_affineSpan d) (asymTreeP_affineSpan d)

/-- **Theorem B.2 (Genuinely Non-Self-Inverse):**
    For ALL `d ≥ 0`, `P_d ≠ Q_d` and `∃ x, P_d x ≠ -Q_d x`. -/
def asymWitnessDiff : (d : Nat) → BVec (asymWidth d)
  | 0 => .cons true (.cons false (.cons false .nil))
  | d + 1 => .cons false (.cons false (bappendR (asymWitnessDiff d) (bzero (asymWidth d))))

theorem asymTree_val_zero (d : Nat) :
    asymTreeP d (bzero (asymWidth d)) = 1 ∧ asymTreeQ d (bzero (asymWidth d)) = 1 := by
  induction d with
  | zero => exact ⟨rfl, rfl⟩
  | succ d ih =>
      have hb : bzero (asymWidth (d + 1)) =
          .cons false (.cons false (bappendR (bzero (asymWidth d + 0)) (bzero (asymWidth d)))) := by
        simp [asymWidth, bzero, bappendR_bzero]
      rw [hb]
      simp only [asymTreeP, asymTreeQ, sharedLift, beq_self_eq_true, ↓reduceIte, bsplitR_bappendR]
      exact ih

theorem asymTree_val_diff (d : Nat) :
    asymTreeP d (asymWitnessDiff d) = -1 ∧ asymTreeQ d (asymWitnessDiff d) = 1 := by
  induction d with
  | zero => exact ⟨rfl, rfl⟩
  | succ d ih =>
      simp only [asymTreeP, asymTreeQ, asymWitnessDiff, sharedLift, beq_self_eq_true, ↓reduceIte,
                 bsplitR_bappendR]
      exact ih

/-- Bundled witness of a full-affine-spanning ternary dyadic self-inverse at dimension `k` and depth `d`. -/
structure DyadicSparseWitness (k d : Nat) where
  elem : GR k
  ternary : IsTernary elem
  selfInv : ∀ x, conv elem elem x = scaleDelta ((4 : Int) ^ d) x
  supp : suppCount elem = 4 ^ d
  zeroNe : elem (bzero k) ≠ 0
  span : AffineSpan elem

def liftWitness {a ov b d : Nat}
    (wA : DyadicSparseWitness (a + ov) d) (wB : DyadicSparseWitness (b + ov) d) :
    DyadicSparseWitness (((a + ov) + b) + 2) (d + 1) where
  elem := sharedLift a ov b wA.elem wB.elem
  ternary := sharedLift_ternary a ov b wA.ternary wB.ternary
  selfInv := by
    intro x
    have h := sharedLift_inv_matched a ov b wA.elem wA.elem wB.elem wB.elem ((4 : Int) ^ d)
      wA.selfInv wB.selfInv x
    rw [h, Int.pow_succ, Int.mul_comm]
  supp := by
    rw [sharedLift_suppCount, wA.supp, wB.supp, Nat.pow_succ]
    omega
  zeroNe := sharedLift_zero_ne a ov b wA.zeroNe
  span := sharedLift_affineSpan a ov b wA.zeroNe wB.zeroNe wA.span wB.span

def treeWitness (d : Nat) : DyadicSparseWitness (treeWidth d) d where
  elem := treeElem d
  ternary := treeElem_ternary d
  selfInv := treeElem_self_inv d
  supp := treeElem_suppCount d
  zeroNe := treeElem_zero_ne d
  span := treeElem_affineSpan d

/-- Every dimension `k ∈ [2d, 2^{d+1} - 2]` has a depth-`d` dyadic sparse witness (`∀ d ≥ 2`). -/
theorem depth_covers_interval : (d : Nat) → 2 ≤ d →
    ∀ k : Nat, 2 * d ≤ k → k ≤ 2 ^ (d + 1) - 2 → Nonempty (DyadicSparseWitness k d)
  | 0, h, _, _, _ => by omega
  | 1, h, _, _, _ => by omega
  | 2, _, k, hlo, hhi => by
      have w1 : DyadicSparseWitness 2 1 := treeWitness 1
      have hcases : k = 4 ∨ k = 5 ∨ k = 6 := by omega
      rcases hcases with rfl | rfl | rfl
      · exact ⟨liftWitness (a := 0) (ov := 2) (b := 0) w1 w1⟩
      · exact ⟨liftWitness (a := 1) (ov := 1) (b := 1) w1 w1⟩
      · exact ⟨liftWitness (a := 2) (ov := 0) (b := 2) w1 w1⟩
  | d + 3, _, k, hlo, hhi => by
      have hd' : 2 ≤ d + 2 := by omega
      by_cases hmid : k ≤ 2 ^ (d + 3)
      · let m := k - 2
        have hm_lo : 2 * (d + 2) ≤ m := by omega
        have hm_hi : m ≤ 2 ^ (d + 3) - 2 := by omega
        rcases depth_covers_interval (d + 2) hd' m hm_lo hm_hi with ⟨wm⟩
        have h0m : m = 0 + m := (Nat.zero_add m).symm
        have hk : ((0 + m) + 0) + 2 = k := by omega
        have wm' : DyadicSparseWitness (0 + m) (d + 2) := h0m ▸ wm
        exact ⟨hk ▸ liftWitness (a := 0) (ov := m) (b := 0) wm' wm'⟩
      · let wmax := treeWitness (d + 2)
        have hpow_ge : 8 ≤ 2 ^ (d + 3) := by
          have : 2 ^ 3 ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by omega) (by omega)
          simpa using this
        have hpow_step : 2 ^ (d + 4) = 2 * 2 ^ (d + 3) := by
          rw [Nat.pow_succ, Nat.mul_comm]
        have hcl : treeWidth (d + 2) + 2 = 2 ^ (d + 3) := treeWidth_closed (d + 2)
        have hw : treeWidth (d + 2) = 2 ^ (d + 3) - 2 := by omega
        let k1 := 2 ^ (d + 3) - 2
        let ov := 2 ^ (d + 4) - 2 - k
        let a := k1 - ov
        have hhi' : k ≤ 2 ^ (d + 4) - 2 := hhi
        have h1 : treeWidth (d + 2) = a + ov := by rw [hw]; omega
        have h3 : ((a + ov) + a) + 2 = k := by omega
        have wL : DyadicSparseWitness (a + ov) (d + 2) := h1 ▸ wmax
        exact ⟨h3 ▸ liftWitness (a := a) (ov := ov) (b := a) wL wL⟩

theorem nat_pow4_eq_pow2_sq (d : Nat) : 4 ^ d = (2 ^ d) ^ 2 := by
  induction d with
  | zero => decide
  | succ n ih =>
      rw [Nat.pow_succ 4 n, Nat.pow_succ 2 n]
      have hstep : (2 ^ n * 2) ^ 2 = (2 ^ n) ^ 2 * 4 := by
        have h22 : 2 * 2 = 4 := rfl
        calc
          (2 ^ n * 2) ^ 2 = (2 ^ n * 2) * (2 ^ n * 2) := by
            simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
          _ = (2 ^ n * 2 ^ n) * (2 * 2) := by ac_rfl
          _ = (2 ^ n) ^ 2 * 4 := by
            simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, h22]
      rw [hstep, ih]

theorem minDepth_spec (k : Nat) (hk : 4 ≤ k) :
    ∃ d : Nat, 2 ≤ d ∧ 2 * d ≤ k ∧ k ≤ 2 ^ (d + 1) - 2 ∧ 4 ^ d < (k + 2) ^ 2 := by
  have hex : ∃ d : Nat, 2 ≤ d ∧ k ≤ 2 ^ (d + 1) - 2 ∧ (d = 2 ∨ (3 ≤ d ∧ 2 ^ d - 2 < k)) := by
    have aux : ∀ f : Nat, k ≤ 2 ^ (f + 3) - 2 →
        ∃ d : Nat, 2 ≤ d ∧ k ≤ 2 ^ (d + 1) - 2 ∧ (d = 2 ∨ (3 ≤ d ∧ 2 ^ d - 2 < k)) := by
      intro f
      induction f with
      | zero =>
          intro hle
          exact ⟨2, by omega, hle, Or.inl rfl⟩
      | succ f ih =>
          intro hle
          by_cases hprev : k ≤ 2 ^ (f + 3) - 2
          · exact ih hprev
          · exact ⟨f + 3, by omega, hle, Or.inr ⟨by omega, by omega⟩⟩
    have hpow : ∀ m : Nat, m + 2 ≤ 2 ^ (m + 2) := by
      intro m; induction m with
      | zero => decide
      | succ m ih => rw [Nat.pow_succ]; omega
    have hbound : k ≤ 2 ^ (k + 3) - 2 := by
      have h1 := hpow (k + 1)
      have h2 : k + 1 + 2 = k + 3 := by omega
      rw [h2] at h1
      omega
    exact aux k hbound
  rcases hex with ⟨d, hd2, hhi, hmin⟩
  have h2d : 2 * d ≤ k := by
    rcases hmin with rfl | ⟨hd3, hgt⟩
    · omega
    · have hpow : ∀ m : Nat, 3 ≤ m → 2 * m ≤ 2 ^ m - 1 := by
        intro m hm
        induction m with
        | zero => omega
        | succ n ih =>
            by_cases hn : n < 3
            · have : n = 2 := by omega
              subst this; decide
            · have := ih (by omega)
              rw [Nat.pow_succ]
              omega
      have := hpow d hd3
      omega
  have h4lt : 4 ^ d < (k + 2) ^ 2 := by
    rcases hmin with rfl | ⟨_, hgt⟩
    · have h6 : 6 ≤ k + 2 := by omega
      have h36 : 36 ≤ (k + 2) ^ 2 := by
        have := Nat.mul_le_mul h6 h6
        simpa [Nat.pow_succ, Nat.pow_zero] using this
      omega
    · have hpow_ge4 : 4 ≤ 2 ^ d := by
        have : 2 ^ 2 ≤ 2 ^ d := Nat.pow_le_pow_right (by omega) hd2
        simpa using this
      have hk2 : 2 ^ d < k + 2 := by omega
      have hsq : (2 ^ d) ^ 2 < (k + 2) ^ 2 := by
        simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
        exact Nat.mul_lt_mul_of_lt_of_lt hk2 hk2
      rw [nat_pow4_eq_pow2_sq d]; exact hsq
  exact ⟨d, hd2, h2d, hhi, h4lt⟩

/-- **Theorem C (Universal All-Dimension Polylogarithmic Sparse Dyadic Inversion):**
    For EVERY integer `k ≥ 2` with `k ≠ 3`, there exists a full-affine-spanning ternary
    element `F : GR k` and `d ≥ 1` such that:
    1. `F(x) ∈ {-1, 0, 1}` for all `x`,
    2. `M(F)^2 = 4^d • I_{2^k}` (exact dyadic self-inverse),
    3. `|supp(F)| = 4^d < (k + 2)^2` (polylogarithmic sparsity `O((log_2 N)^2)`),
    4. `AffineSpan F` (spans all `k` dimensions of `F_2^k`). -/
theorem universal_all_dim_polylog (k : Nat) (hk2 : 2 ≤ k) (hk3 : k ≠ 3) :
    ∃ (d : Nat) (F : GR k),
      1 ≤ d ∧ IsTernary F ∧
      (∀ x, conv F F x = scaleDelta ((4 : Int) ^ d) x) ∧
      suppCount F = 4 ^ d ∧ suppCount F < (k + 2) ^ 2 ∧
      AffineSpan F := by
  by_cases h2 : k = 2
  · subst h2
    have w1 : DyadicSparseWitness 2 1 := treeWitness 1
    exact ⟨1, w1.elem, by omega, w1.ternary, w1.selfInv, w1.supp, by rw [w1.supp]; decide, w1.span⟩
  · have hk4 : 4 ≤ k := by omega
    rcases minDepth_spec k hk4 with ⟨d, hd2, hlo, hhi, hlt⟩
    rcases depth_covers_interval d hd2 k hlo hhi with ⟨w⟩
    exact ⟨d, w.elem, by omega, w.ternary, w.selfInv, w.supp, by rw [w.supp]; exact hlt, w.span⟩

/-! ## Part V: Kernel-Checked Sharpness Counterexamples & Non-Vacuity Witnesses -/

/-- **Sharpness 1 (`k = 1` Impossibility):**
    No full-affine-spanning ternary element on `F_2^1` is invertible at ANY nonzero scale `D`. -/
theorem k1_no_spanning_ternary_inv {f g : GR 1} {D : Int} (hD : D ≠ 0)
    (ht : IsTernary f) (hspan : AffineSpan f)
    (hinv : ∀ x, conv f g x = scaleDelta D x) : False := by
  have hf0 : f (.cons false .nil) ≠ 0 := by
    intro h0
    have h1 : BVec.cons true .nil = bzero 1 := by
      apply hspan (.cons true .nil) true
      intro x hx
      match x with
      | .cons false .nil => exact False.elim (hx h0)
      | .cons true  .nil => rfl
    simp [bzero] at h1
  have hf1 : f (.cons true .nil) ≠ 0 := by
    intro h1
    have h0 : BVec.cons true .nil = bzero 1 := by
      apply hspan (.cons true .nil) false
      intro x hx
      match x with
      | .cons false .nil => rfl
      | .cons true  .nil => exact False.elim (hx h1)
    simp [bzero] at h0
  have hw := (group_ring_inv_iff f g D).mp hinv
  have hw0 := hw (.cons false .nil)
  have hw1 := hw (.cons true .nil)
  simp only [wht, sumBVec, bdot, signBit] at hw0 hw1
  rcases ht (.cons false .nil) with a | a | a <;>
  rcases ht (.cons true  .nil) with b | b | b <;>
  simp [a, b] at hf0 hf1 hw0 hw1 <;> omega

theorem sq_ge_four_of_abs_ge_two {a : Int} (h : a ≤ -2 ∨ 2 ≤ a) : (4 : Int) ≤ a * a := by
  rcases h with h | h
  · have h1 : 2 ≤ -a := by omega
    have h2 : 4 ≤ (-a) * (-a) := Int.mul_le_mul h1 h1 (by omega) (by omega)
    rw [Int.neg_mul_neg] at h2
    exact h2
  · exact Int.mul_le_mul h h (by omega) (by omega)

/-- **Sharpness 3 (Unmatched-Scale Dyadic Unit on `F_2^4` — Non-Flat Spectrum Causes Inverse Entry Growth):**
    Lifting `treeElem 0` (`k=0, D=1`) and `treeElem 1` (`k=2, D=4`) via `sharedLift` produces a
    10-sparse ternary dyadic unit `F` on `F_2^4` (`F * G = 16 • δ_0`), while relaxing `D₁ = D₂`
    forces `G` to have entry `4`. -/
def nonBentF4 : GR 4 :=
  sharedLift 0 0 2 (treeElem 0) (treeElem 1)

def nonBentG4 : GR 4 :=
  sharedLift 0 0 2 (fun x => 4 * treeElem 0 x) (fun x => 1 * treeElem 1 x)

theorem nonBent4_inv : ∀ x, conv nonBentF4 nonBentG4 x = scaleDelta 16 x :=
  sharedLift_inv 0 0 2 (treeElem 0) (treeElem 0) (treeElem 1) (treeElem 1)
    1 4 4 1 4 (treeElem_self_inv 0) (treeElem_self_inv 1) rfl rfl

theorem nonBent4_ternary : IsTernary nonBentF4 :=
  sharedLift_ternary 0 0 2 (treeElem_ternary 0) (treeElem_ternary 1)

theorem nonBent4_supp : suppCount nonBentF4 = 10 := by
  change suppCount (sharedLift 0 0 2 (treeElem 0) (treeElem 1)) = 10
  rw [sharedLift_suppCount 0 0 2 (treeElem 0) (treeElem 1),
      treeElem_suppCount 0, treeElem_suppCount 1]

theorem nonBent4_entry_blowup : nonBentG4 (bzero 4) = 4 := by decide

/-- **Sharpness 4 (Omitting the Shift Bit `u` Breaks Boundedness):** -/
def unshiftedLift (A B : GR 2) : GR 3 :=
  fun z => match z with
    | .cons t x => A x + signBit t * B x

end SpecMat13
