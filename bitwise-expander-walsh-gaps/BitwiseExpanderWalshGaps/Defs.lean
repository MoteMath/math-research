/-!
# Pure-Silicon Walsh–Automaton Spectral-Gap Engine (`specmat-15`)

Standalone Lean 4.36.0 formalization (zero Mathlib, zero floats, zero reals,
zero `sorry`, zero custom axioms) of a reusable pure-silicon infinite proof
mechanism proving tight exact integer spectral gaps, exact two-sided spectral
radii, and the exact integer Expander Mixing Lemma for infinite families of
explicit bitwise-edge Cayley graphs on `BitVec k` (`∀ k ≥ 1`).

## Architecture
1. **Layer 1 (Exact Integer Walsh–Parseval–Rayleigh & EML Engine):**
   For ANY bitwise predicate `P : BitVec k → Bool` (`P 0 = false`), proves:
   - Exact integer Parseval & Plancherel identities (`wht_parseval`, `wht_plancherel`)
   - Exact integer convolution diagonalization (`wht_adjOp`)
   - Exact integer Laplacian-Rayleigh spectral decomposition (`dirichletForm_eq_wht`)
   - Centered variance-form Poincaré & zero-sum Rayleigh spectral-gap lifters
   - Constructive Walsh-character tightness witnesses (`character_eigenfunction`)
   - Exact integer Cauchy–Schwarz & Expander Mixing Lemma (`expander_mixing_lemma_int`)
2. **Layer 2 (Finite Partial-Automaton → Infinite Transfer-Matrix Bridge):**
   Compiles any finite partial bit-automaton `A : BitAutomaton m` to two finite
   integer transfer operators `(T0, T1)` and proves `wht_automaton_eq_transfer`
   for all widths `k` and dual frequencies `ξ : BitVec k`.
3. **Three Novel Infinite Theorems Proved Through the Engine:**
   - **Theorem A (`G_mod3`):** Divisibility-by-3 Bitwise Cayley Super-Expander
     `(x ^^^ y).toNat % 3 = 0` via Eisenstein quadratic-form similarity + mod-3 descent.
   - **Theorem B (`G_fib`):** Fibbinary (No-Adjacent-Ones) Bitwise Cayley Expander
     `((x ^^^ y) &&& ((x ^^^ y) >>> 1)) = 0` via Fibonacci majorant + 5-inequality polytope.
   - **Theorem C (`G_cfib`):** Circular Fibbinary Edge-Sparse Dominance
     `((x ^^^ y) &&& rotl1 (x ^^^ y)) = 0`, preserving the exact gap `2 * F_{k-1}`
     while deleting `F_{k-2}` edges per vertex.
4. **Non-Vacuity Witnesses & Sharpness Counterexamples** checked by the Lean kernel.
-/

namespace WalshAutomatonEngine

-- ============================================================================
-- SECTION 0: BitVec MSB/Truncate Basic Helpers
-- ============================================================================

def sgn (b : Bool) : Int := if b then -1 else 1

@[simp] theorem sgn_false : sgn false = 1 := rfl
@[simp] theorem sgn_true : sgn true = -1 := rfl

theorem sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by
  cases b <;> rfl

theorem sgn_xor (a b : Bool) : sgn (a ^^ b) = sgn a * sgn b := by
  cases a <;> cases b <;> rfl

theorem sgn_and_xor (a b c : Bool) :
    sgn (a && (b ^^ c)) = sgn (a && b) * sgn (a && c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem int_mul_self_nonneg (a : Int) : 0 ≤ a * a := by
  by_cases h : 0 ≤ a
  · exact Int.mul_nonneg h h
  · have hneg : 0 ≤ -a := by omega
    have heq : (-a) * (-a) = a * a := Int.neg_mul_neg a a
    rw [← heq]
    exact Int.mul_nonneg hneg hneg

theorem bv_cons_msb {k : Nat} (b : Bool) (x : BitVec k) :
    (BitVec.cons b x).msb = b := by
  simp [BitVec.msb_cons]

theorem bv_cons_truncate {k : Nat} (b : Bool) (x : BitVec k) :
    (BitVec.cons b x).truncate k = x := by
  ext i hi
  simp [BitVec.truncate]

theorem bv_eq_cons_msb_truncate {k : Nat} (x : BitVec (k + 1)) :
    x = BitVec.cons x.msb (x.truncate k) := by
  ext i hi
  by_cases h : i = k
  · subst h
    simp [BitVec.msb_eq_getLsbD_last, BitVec.getElem_cons]
  · simp [BitVec.truncate]

theorem bv_cons_xor {k : Nat} (a b : Bool) (x y : BitVec k) :
    BitVec.cons a x ^^^ BitVec.cons b y = BitVec.cons (a ^^ b) (x ^^^ y) := by
  ext i hi
  by_cases h : i = k
  · subst h; simp
  · simp

theorem bv_cons_zero {k : Nat} :
    (0 : BitVec (k + 1)) = BitVec.cons false (0 : BitVec k) := by
  ext i hi
  by_cases h : i = k
  · subst h; simp
  · simp

theorem bv_zero_msb {k : Nat} : (0 : BitVec (k + 1)).msb = false := by
  rw [bv_cons_zero, bv_cons_msb]

theorem bv_zero_truncate {k : Nat} : (0 : BitVec (k + 1)).truncate k = 0 := by
  rw [bv_cons_zero, bv_cons_truncate]

theorem bv_cons_eq_zero_iff {k : Nat} (b : Bool) (x : BitVec k) :
    BitVec.cons b x = 0 ↔ b = false ∧ x = 0 := by
  constructor
  · intro h
    have hm := congrArg BitVec.msb h
    have ht := congrArg (fun v => v.truncate k) h
    rw [bv_cons_msb, bv_zero_msb] at hm
    rw [bv_cons_truncate, bv_zero_truncate] at ht
    exact ⟨hm, ht⟩
  · rintro ⟨rfl, rfl⟩
    exact bv_cons_zero.symm

theorem bv_zero_width_eq (x : BitVec 0) : x = 0 := by
  ext i hi; omega

-- ============================================================================
-- SECTION 1: Exact Integer Summation over BitVec k
-- ============================================================================

def bvSum : {k : Nat} → (BitVec k → Int) → Int
  | 0, f => f 0
  | _ + 1, f =>
      bvSum (fun x => f (BitVec.cons false x)) +
      bvSum (fun x => f (BitVec.cons true x))

theorem bvSum_congr {k : Nat} {f g : BitVec k → Int} (h : ∀ x, f x = g x) :
    bvSum f = bvSum g := by
  induction k with
  | zero => exact h 0
  | succ k ih =>
    simp only [bvSum]
    rw [ih (fun x => h _), ih (fun x => h _)]

theorem bvSum_zero {k : Nat} : bvSum (fun _ : BitVec k => (0 : Int)) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [bvSum, ih]

theorem bvSum_add {k : Nat} (f g : BitVec k → Int) :
    bvSum (fun x => f x + g x) = bvSum f + bvSum g := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [bvSum, ih]
    omega

theorem bvSum_sub {k : Nat} (f g : BitVec k → Int) :
    bvSum (fun x => f x - g x) = bvSum f - bvSum g := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [bvSum, ih]
    omega

theorem bvSum_neg {k : Nat} (f : BitVec k → Int) :
    bvSum (fun x => -f x) = -bvSum f := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [bvSum, ih]
    omega

theorem bvSum_mul_left {k : Nat} (c : Int) (f : BitVec k → Int) :
    bvSum (fun x => c * f x) = c * bvSum f := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [bvSum, ih, Int.mul_add]

theorem bvSum_mul_right {k : Nat} (f : BitVec k → Int) (c : Int) :
    bvSum (fun x => f x * c) = bvSum f * c := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [bvSum, ih, Int.add_mul]

theorem bvSum_const {k : Nat} (c : Int) :
    bvSum (fun _ : BitVec k => c) = ((2 ^ k : Nat) : Int) * c := by
  induction k with
  | zero => simp [bvSum]
  | succ k ih =>
    simp only [bvSum, ih, Nat.pow_succ]
    have hcast : ((2 ^ k * 2 : Nat) : Int) = ((2 ^ k : Nat) : Int) * 2 := by
      exact Int.natCast_mul (2 ^ k) 2
    rw [hcast]
    have hmul : (((2 ^ k : Nat) : Int) * 2) * c =
                ((2 ^ k : Nat) : Int) * c + ((2 ^ k : Nat) : Int) * c := by
      rw [Int.mul_assoc]
      have : (2 : Int) * c = c + c := by omega
      rw [this, Int.mul_add]
    omega

theorem bvSum_le {k : Nat} {f g : BitVec k → Int} (h : ∀ x, f x ≤ g x) :
    bvSum f ≤ bvSum g := by
  induction k with
  | zero => exact h 0
  | succ k ih =>
    simp only [bvSum]
    have h0 := ih (fun x => h (BitVec.cons false x))
    have h1 := ih (fun x => h (BitVec.cons true x))
    omega

theorem bvSum_nonneg {k : Nat} {f : BitVec k → Int} (h : ∀ x, 0 ≤ f x) :
    0 ≤ bvSum f := by
  rw [← bvSum_zero (k := k)]
  exact bvSum_le h

theorem bvSum_comm {k m : Nat} (F : BitVec k → BitVec m → Int) :
    bvSum (fun x => bvSum (fun y => F x y)) =
    bvSum (fun y => bvSum (fun x => F x y)) := by
  induction k with
  | zero => simp [bvSum]
  | succ k ih =>
    simp only [bvSum, ih]
    rw [← bvSum_add]

theorem bvSum_xor {k : Nat} (a : BitVec k) (f : BitVec k → Int) :
    bvSum (fun x => f (a ^^^ x)) = bvSum f := by
  induction k with
  | zero =>
    simp only [bvSum]
    congr 1
    exact bv_zero_width_eq _
  | succ k ih =>
    rw [bv_eq_cons_msb_truncate a]
    cases a.msb
    · simp only [bvSum, bv_cons_xor, Bool.false_xor]
      rw [ih (a.truncate k) (fun x => f (BitVec.cons false x)),
          ih (a.truncate k) (fun x => f (BitVec.cons true x))]
    · simp only [bvSum, bv_cons_xor, Bool.true_xor, Bool.not_false, Bool.not_true]
      rw [ih (a.truncate k) (fun x => f (BitVec.cons true x)),
          ih (a.truncate k) (fun x => f (BitVec.cons false x)),
          Int.add_comm]

theorem bvSum_split_zero {k : Nat} (f : BitVec k → Int) :
    bvSum f = f 0 + bvSum (fun x => if x = 0 then 0 else f x) := by
  induction k with
  | zero =>
    simp [bvSum]
  | succ k ih =>
    simp only [bvSum]
    have h1 : bvSum (fun x : BitVec k => if BitVec.cons true x = 0 then 0 else f (BitVec.cons true x)) =
              bvSum (fun x : BitVec k => f (BitVec.cons true x)) := by
      apply bvSum_congr
      intro x
      simp
    have h0 : bvSum (fun x : BitVec k => if BitVec.cons false x = 0 then 0 else f (BitVec.cons false x)) =
              bvSum (fun x : BitVec k => if x = 0 then 0 else f (BitVec.cons false x)) := by
      apply bvSum_congr
      intro x
      by_cases hx : x = 0
      · subst hx; simp
      · have hne : BitVec.cons false x ≠ 0 := by
          intro hc; exact hx ((bv_cons_eq_zero_iff false x).mp hc).2
        simp only [hx, hne, ↓reduceIte]
    rw [h0, h1, bv_cons_zero]
    have ih0 := ih (fun x => f (BitVec.cons false x))
    omega

-- Exact Integer Cauchy–Schwarz over BitVec k
theorem bvSum_cauchy_schwarz {k : Nat} (a b : BitVec k → Int) :
    (bvSum (fun x => a x * b x)) * (bvSum (fun x => a x * b x)) ≤
    bvSum (fun x => a x * a x) * bvSum (fun x => b x * b x) := by
  have hnn : 0 ≤ bvSum (fun x => bvSum (fun y =>
      (a x * b y - a y * b x) * (a x * b y - a y * b x))) := by
    apply bvSum_nonneg
    intro x
    apply bvSum_nonneg
    intro y
    exact int_mul_self_nonneg _
  have hexp : bvSum (fun x => bvSum (fun y =>
      (a x * b y - a y * b x) * (a x * b y - a y * b x))) =
      2 * (bvSum (fun x => a x * a x) * bvSum (fun y => b y * b y) -
           bvSum (fun x => a x * b x) * bvSum (fun y => a y * b y)) := by
    have hinner : ∀ x : BitVec k,
        bvSum (fun y => (a x * b y - a y * b x) * (a x * b y - a y * b x)) =
        (a x * a x) * bvSum (fun y => b y * b y) +
        (b x * b x) * bvSum (fun y => a y * a y) -
        (2 * (a x * b x)) * bvSum (fun y => a y * b y) := by
      intro x
      have hterm : ∀ y : BitVec k,
          (a x * b y - a y * b x) * (a x * b y - a y * b x) =
          ((a x * a x) * (b y * b y) + (b x * b x) * (a y * a y)) -
          (2 * (a x * b x)) * (a y * b y) := by
        intro y
        have h1 : (a x * b y - a y * b x) * (a x * b y - a y * b x) =
            (a x * b y) * (a x * b y) - (a x * b y) * (a y * b x) -
            (a y * b x) * (a x * b y) + (a y * b x) * (a y * b x) := by
          rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]; omega
        have h2 : (a x * b y) * (a x * b y) = (a x * a x) * (b y * b y) := by ac_rfl
        have h3 : (a y * b x) * (a y * b x) = (b x * b x) * (a y * a y) := by ac_rfl
        have h4 : (a x * b y) * (a y * b x) = (a x * b x) * (a y * b y) := by ac_rfl
        have h5 : (a y * b x) * (a x * b y) = (a x * b x) * (a y * b y) := by ac_rfl
        have h6 : (2 * (a x * b x)) * (a y * b y) = 2 * ((a x * b x) * (a y * b y)) := Int.mul_assoc _ _ _
        rw [h1, h2, h3, h4, h5, h6]
        omega
      rw [bvSum_congr hterm, bvSum_sub, bvSum_add, bvSum_mul_left, bvSum_mul_left, bvSum_mul_left]
    rw [bvSum_congr hinner, bvSum_sub, bvSum_add, bvSum_mul_right, bvSum_mul_right,
        bvSum_mul_right, bvSum_mul_left]
    have hc : bvSum (fun x => b x * b x) * bvSum (fun y => a y * a y) =
              bvSum (fun x => a x * a x) * bvSum (fun y => b y * b y) := Int.mul_comm _ _
    have h2m : (2 * bvSum (fun x => a x * b x)) * bvSum (fun y => a y * b y) =
               2 * (bvSum (fun x => a x * b x) * bvSum (fun y => a y * b y)) := Int.mul_assoc _ _ _
    rw [hc, h2m]
    omega
  rw [hexp] at hnn
  omega

-- ============================================================================
-- SECTION 2: Layer 1 — Exact Integer Walsh–Hadamard & Rayleigh Spectral Engine
-- ============================================================================

def chi : {k : Nat} → BitVec k → BitVec k → Int
  | 0, _, _ => 1
  | k + 1, ξ, x => sgn (ξ.msb && x.msb) * chi (ξ.truncate k) (x.truncate k)

theorem chi_cons {k : Nat} (a b : Bool) (ξ x : BitVec k) :
    chi (BitVec.cons a ξ) (BitVec.cons b x) = sgn (a && b) * chi ξ x := by
  conv => lhs; unfold chi
  rw [bv_cons_msb, bv_cons_msb, bv_cons_truncate, bv_cons_truncate]

theorem chi_symm {k : Nat} (ξ x : BitVec k) : chi ξ x = chi x ξ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [chi, Bool.and_comm, ih]

theorem chi_zero_left {k : Nat} (x : BitVec k) : chi 0 x = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [chi, bv_zero_msb, bv_zero_truncate, Bool.false_and, sgn_false, Int.one_mul, ih]

theorem chi_zero_right {k : Nat} (ξ : BitVec k) : chi ξ 0 = 1 := by
  rw [chi_symm, chi_zero_left]

theorem chi_mul_self {k : Nat} (ξ x : BitVec k) : chi ξ x * chi ξ x = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [chi]
    have hre : (sgn (ξ.msb && x.msb) * chi (ξ.truncate k) (x.truncate k)) *
               (sgn (ξ.msb && x.msb) * chi (ξ.truncate k) (x.truncate k)) =
               (sgn (ξ.msb && x.msb) * sgn (ξ.msb && x.msb)) *
               (chi (ξ.truncate k) (x.truncate k) * chi (ξ.truncate k) (x.truncate k)) := by
      ac_rfl
    rw [hre, sgn_mul_self, ih]
    rfl

theorem chi_xor_right {k : Nat} (ξ x y : BitVec k) :
    chi ξ (x ^^^ y) = chi ξ x * chi ξ y := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [bv_eq_cons_msb_truncate ξ, bv_eq_cons_msb_truncate x, bv_eq_cons_msb_truncate y]
    rw [bv_cons_xor, chi_cons, chi_cons, chi_cons, sgn_and_xor, ih]
    ac_rfl

theorem bvSum_chi {k : Nat} (ξ : BitVec k) :
    bvSum (fun x => chi ξ x) = if ξ = 0 then ((2 ^ k : Nat) : Int) else 0 := by
  induction k with
  | zero =>
    have h0 : ξ = 0 := bv_zero_width_eq ξ
    simp [bvSum, chi, h0]
  | succ k ih =>
    rw [bv_eq_cons_msb_truncate ξ]
    simp only [bvSum, chi_cons]
    cases h : ξ.msb
    · simp only [Bool.false_and, sgn_false, Int.one_mul, ih, bv_cons_eq_zero_iff, true_and]
      split
      · simp [Nat.pow_succ]; omega
      · omega
    · simp only [Bool.true_and, sgn_false, sgn_true, Int.one_mul, bv_cons_eq_zero_iff,
                 Bool.true_eq_false, false_and, ↓reduceIte]
      have hneg : bvSum (fun x => -1 * chi (ξ.truncate k) x) =
                  -bvSum (fun x => chi (ξ.truncate k) x) := by
        have h1 := bvSum_mul_left (-1) (fun x => chi (ξ.truncate k) x)
        rw [h1]
        exact Int.neg_one_mul _
      rw [hneg]
      omega

def wht {k : Nat} (f : BitVec k → Int) (ξ : BitVec k) : Int :=
  bvSum (fun x => chi ξ x * f x)

theorem wht_zero {k : Nat} (f : BitVec k → Int) :
    wht f 0 = bvSum f := by
  unfold wht
  apply bvSum_congr
  intro x
  rw [chi_zero_left, Int.one_mul]

theorem wht_cons_false {k : Nat} (f : BitVec (k + 1) → Int) (ξ : BitVec k) :
    wht f (BitVec.cons false ξ) =
    wht (fun x => f (BitVec.cons false x)) ξ + wht (fun x => f (BitVec.cons true x)) ξ := by
  simp only [wht, bvSum, chi_cons, Bool.false_and, sgn_false, Int.one_mul]

theorem wht_cons_true {k : Nat} (f : BitVec (k + 1) → Int) (ξ : BitVec k) :
    wht f (BitVec.cons true ξ) =
    wht (fun x => f (BitVec.cons false x)) ξ - wht (fun x => f (BitVec.cons true x)) ξ := by
  simp only [wht, bvSum, chi_cons, Bool.true_and, sgn_false, sgn_true, Int.one_mul]
  have h1 : bvSum (fun x => -1 * chi ξ x * f (BitVec.cons true x)) =
            -bvSum (fun x => chi ξ x * f (BitVec.cons true x)) := by
    have heq : ∀ x, -1 * chi ξ x * f (BitVec.cons true x) = -(chi ξ x * f (BitVec.cons true x)) := by
      intro x
      rw [Int.mul_assoc]
      exact Int.neg_one_mul _
    rw [bvSum_congr heq, bvSum_neg]
  rw [h1]
  omega

def indBool {k : Nat} (P : BitVec k → Bool) (x : BitVec k) : Int :=
  if P x then 1 else 0

/-- Degree of the bitwise Cayley graph `x ~ y ↔ P (x ^^^ y)`. -/
def graphDeg {k : Nat} (P : BitVec k → Bool) : Int :=
  bvSum (indBool P)

/-- Exact integer Walsh eigenvalue `λ_P(ξ) = ∑_d χ_ξ(d) * 1_{P(d)}`. -/
def graphEig {k : Nat} (P : BitVec k → Bool) (ξ : BitVec k) : Int :=
  wht (indBool P) ξ

/-- Adjacency operator `(A_P f)(x) = ∑_y 1_{P(x ^^^ y)} f(y)`. -/
def adjOp {k : Nat} (P : BitVec k → Bool) (f : BitVec k → Int) (x : BitVec k) : Int :=
  bvSum (fun y => indBool P (x ^^^ y) * f y)

/-- Laplacian operator `(L_P f)(x) = deg(P) * f(x) - (A_P f)(x)`. -/
def laplacianOp {k : Nat} (P : BitVec k → Bool) (f : BitVec k → Int) (x : BitVec k) : Int :=
  graphDeg P * f x - adjOp P f x

/-- Exact integer Laplacian quadratic form `⟨f, L_P f⟩`. -/
def dirichletForm {k : Nat} (P : BitVec k → Bool) (f : BitVec k → Int) : Int :=
  bvSum (fun x => f x * laplacianOp P f x)

/-- Exact integer variance `2^k ∑ f(x)^2 - (∑ f(x))^2`. -/
def intVariance {k : Nat} (f : BitVec k → Int) : Int :=
  ((2 ^ k : Nat) : Int) * bvSum (fun x => f x * f x) - bvSum f * bvSum f

/-- Exact integer edge count between subsets `S, T ⊆ BitVec k`. -/
def edgesBetween {k : Nat} (P : BitVec k → Bool) (S T : BitVec k → Bool) : Int :=
  bvSum (fun x => indBool S x * adjOp P (indBool T) x)

theorem graphEig_zero {k : Nat} (P : BitVec k → Bool) :
    graphEig P 0 = graphDeg P :=
  wht_zero (indBool P)

/-- Exact Integer Convolution Diagonalization: `wht (A_P f) ξ = λ_P(ξ) * wht f ξ`. -/
theorem wht_adjOp {k : Nat} (P : BitVec k → Bool) (f : BitVec k → Int) (ξ : BitVec k) :
    wht (adjOp P f) ξ = graphEig P ξ * wht f ξ := by
  unfold wht adjOp graphEig
  have h1 : bvSum (fun x => chi ξ x * bvSum (fun y => indBool P (x ^^^ y) * f y)) =
            bvSum (fun x => bvSum (fun y => chi ξ x * (indBool P (x ^^^ y) * f y))) := by
    apply bvSum_congr
    intro x
    rw [bvSum_mul_left]
  rw [h1, bvSum_comm]
  have h2 : ∀ y : BitVec k,
      bvSum (fun x => chi ξ x * (indBool P (x ^^^ y) * f y)) =
      (chi ξ y * f y) * bvSum (fun d => chi ξ d * indBool P d) := by
    intro y
    rw [← bvSum_xor y (fun d => chi ξ d * (indBool P (d ^^^ y) * f y))]
    have hstep : ∀ d : BitVec k,
        chi ξ (y ^^^ d) * (indBool P ((y ^^^ d) ^^^ y) * f y) =
        (chi ξ y * f y) * (chi ξ d * indBool P d) := by
      intro d
      have hcancel : (y ^^^ d) ^^^ y = d := by
        ext i hi; simp; cases y[i] <;> cases d[i] <;> decide
      rw [hcancel, chi_xor_right]
      ac_rfl
    rw [bvSum_congr hstep, bvSum_mul_left]
  rw [bvSum_congr h2, bvSum_mul_right, Int.mul_comm]
  rfl

/-- Master Tightness Theorem (Pointwise Walsh Character Eigenfunction & Exact Rayleigh Equality). -/
theorem character_adjOp {k : Nat} (P : BitVec k → Bool) (ξ x : BitVec k) :
    adjOp P (chi ξ) x = graphEig P ξ * chi ξ x := by
  unfold adjOp graphEig wht
  rw [← bvSum_xor x (fun d => indBool P (x ^^^ d) * chi ξ d)]
  have hstep : ∀ d : BitVec k,
      indBool P (x ^^^ (x ^^^ d)) * chi ξ (x ^^^ d) =
      (chi ξ d * indBool P d) * chi ξ x := by
    intro d
    have hc : x ^^^ (x ^^^ d) = d := by
      ext i hi; simp
    rw [hc, chi_xor_right]
    ac_rfl
  rw [bvSum_congr hstep, bvSum_mul_right]

theorem character_eigenfunction {k : Nat} (P : BitVec k → Bool) (ξ x : BitVec k) :
    laplacianOp P (chi ξ) x = (graphDeg P - graphEig P ξ) * chi ξ x := by
  unfold laplacianOp
  rw [character_adjOp, Int.sub_mul]

theorem character_norm_sq {k : Nat} (ξ : BitVec k) :
    bvSum (fun x => chi ξ x * chi ξ x) = ((2 ^ k : Nat) : Int) := by
  rw [bvSum_congr (fun x => chi_mul_self ξ x), bvSum_const, Int.mul_one]

theorem character_zero_sum {k : Nat} {ξ : BitVec k} (hne : ξ ≠ 0) :
    bvSum (chi ξ) = 0 := by
  rw [bvSum_chi]
  split
  · contradiction
  · rfl

theorem character_rayleigh_tight {k : Nat} (P : BitVec k → Bool) (ξ : BitVec k) :
    dirichletForm P (chi ξ) =
    (graphDeg P - graphEig P ξ) * bvSum (fun x => chi ξ x * chi ξ x) := by
  unfold dirichletForm
  have hpt : ∀ x, chi ξ x * laplacianOp P (chi ξ) x =
                  (graphDeg P - graphEig P ξ) * (chi ξ x * chi ξ x) := by
    intro x
    rw [character_eigenfunction]
    ac_rfl
  rw [bvSum_congr hpt, bvSum_mul_left]

/-- A finite-state partial deterministic bit-automaton on `m` states. -/
structure BitAutomaton (m : Nat) where
  init : Fin m
  delta : Fin m → Bool → Option (Fin m)
  accept : Fin m → Bool

def optVal {m : Nat} (v : Fin m → Int) : Option (Fin m) → Int
  | none => 0
  | some q => v q

def BitAutomaton.acceptVec {m : Nat} (A : BitAutomaton m) : Fin m → Int :=
  fun q => if A.accept q then 1 else 0

/-- Run the bit-automaton MSB-first on a `BitVec k`. -/
def BitAutomaton.run {m : Nat} (A : BitAutomaton m) :
    Fin m → {k : Nat} → BitVec k → Option (Fin m)
  | q, 0, _ => some q
  | q, k + 1, x =>
      match A.delta q x.msb with
      | none => none
      | some q' => A.run q' (x.truncate k)

def BitAutomaton.accepts {m : Nat} (A : BitAutomaton m) {k : Nat} (x : BitVec k) : Bool :=
  match A.run A.init x with
  | none => false
  | some q => A.accept q

/-- Loopless Cayley generating predicate induced by a finite bit-automaton. -/
def BitAutomaton.looplessPred {m : Nat} (A : BitAutomaton m) {k : Nat} (x : BitVec k) : Bool :=
  x != 0 && A.accepts x

/-- The two finite integer Walsh transfer operators `T_0, T_1 : (Fin m → Int) → (Fin m → Int)`. -/
def BitAutomaton.stepT {m : Nat} (A : BitAutomaton m) (b : Bool) (v : Fin m → Int) :
    Fin m → Int :=
  fun q => optVal v (A.delta q false) + sgn b * optVal v (A.delta q true)

/-- Evaluate the matrix-vector product `T_{ξ_{k-1}} ⋯ T_{ξ_0} v`. -/
def BitAutomaton.evalT {m : Nat} (A : BitAutomaton m) :
    {k : Nat} → BitVec k → (Fin m → Int) → (Fin m → Int)
  | 0, _, v => v
  | k + 1, ξ, v => A.stepT ξ.msb (A.evalT (ξ.truncate k) v)

theorem BitAutomaton.run_cons {m : Nat} (A : BitAutomaton m) (q : Fin m)
    {k : Nat} (b : Bool) (x : BitVec k) :
    A.run q (BitVec.cons b x) =
      match A.delta q b with
      | none => none
      | some q' => A.run q' x := by
  conv => lhs; unfold BitAutomaton.run
  rw [bv_cons_msb, bv_cons_truncate]

/-- **Core Bridge Theorem (Finite → Infinite):**
    For EVERY finite partial bit-automaton `A`, EVERY width `k`, EVERY frequency `ξ : BitVec k`,
    and EVERY starting state `q`, the exact integer Walsh transform over `2^k` vertices equals
    the finite-dimensional integer transfer-matrix evaluation `A.evalT ξ A.acceptVec q`. -/
theorem wht_automaton_from_state {m : Nat} (A : BitAutomaton m) :
    ∀ {k : Nat} (ξ : BitVec k) (q : Fin m),
      bvSum (fun x : BitVec k => chi ξ x * optVal A.acceptVec (A.run q x)) =
      A.evalT ξ A.acceptVec q := by
  intro k
  induction k with
  | zero =>
    intro ξ q
    simp [bvSum, chi, BitAutomaton.run, BitAutomaton.evalT, optVal]
  | succ k ih =>
    intro ξ q
    rw [bv_eq_cons_msb_truncate ξ]
    simp only [bvSum, chi_cons, BitAutomaton.run_cons]
    conv => rhs; unfold BitAutomaton.evalT
    rw [bv_cons_msb, bv_cons_truncate]
    unfold BitAutomaton.stepT
    have hfalse : bvSum (fun x : BitVec k =>
        sgn (ξ.msb && false) * chi (ξ.truncate k) x *
        optVal A.acceptVec (match A.delta q false with | none => none | some q' => A.run q' x)) =
        optVal (A.evalT (ξ.truncate k) A.acceptVec) (A.delta q false) := by
      cases hd : A.delta q false with
      | none =>
        simp [optVal, bvSum_zero]
      | some q' =>
        simp only [Bool.and_false, sgn_false, Int.one_mul, optVal]
        exact ih (ξ.truncate k) q'
    have htrue : bvSum (fun x : BitVec k =>
        sgn (ξ.msb && true) * chi (ξ.truncate k) x *
        optVal A.acceptVec (match A.delta q true with | none => none | some q' => A.run q' x)) =
        sgn ξ.msb * optVal (A.evalT (ξ.truncate k) A.acceptVec) (A.delta q true) := by
      cases hd : A.delta q true with
      | none =>
        simp [optVal, bvSum_zero]
      | some q' =>
        simp only [Bool.and_true]
        change bvSum (fun x : BitVec k => sgn ξ.msb * chi (ξ.truncate k) x * optVal A.acceptVec (A.run q' x)) =
               sgn ξ.msb * A.evalT (ξ.truncate k) A.acceptVec q'
        have hre : ∀ x : BitVec k,
            sgn ξ.msb * chi (ξ.truncate k) x * optVal A.acceptVec (A.run q' x) =
            sgn ξ.msb * (chi (ξ.truncate k) x * optVal A.acceptVec (A.run q' x)) := by
          intro x; exact Int.mul_assoc _ _ _
        rw [bvSum_congr hre, bvSum_mul_left, ih (ξ.truncate k) q']
    rw [hfalse, htrue]

theorem indBool_automaton_accepts {m : Nat} (A : BitAutomaton m) {k : Nat} (x : BitVec k) :
    indBool A.accepts x = optVal A.acceptVec (A.run A.init x) := by
  unfold indBool BitAutomaton.accepts optVal BitAutomaton.acceptVec
  cases A.run A.init x <;> simp

theorem wht_automaton_accepts {m : Nat} (A : BitAutomaton m) {k : Nat} (ξ : BitVec k) :
    wht (indBool A.accepts) ξ = A.evalT ξ A.acceptVec A.init := by
  unfold wht
  have hpt : ∀ x : BitVec k, chi ξ x * indBool A.accepts x =
      chi ξ x * optVal A.acceptVec (A.run A.init x) := by
    intro x; rw [indBool_automaton_accepts]
  rw [bvSum_congr hpt]
  exact wht_automaton_from_state A ξ A.init

theorem graphEig_automaton_loopless {m : Nat} (A : BitAutomaton m) {k : Nat} (ξ : BitVec k) :
    graphEig A.looplessPred ξ =
    A.evalT ξ A.acceptVec A.init - (if A.accepts (0 : BitVec k) then 1 else 0) := by
  unfold graphEig
  rw [← wht_automaton_accepts A ξ]
  unfold wht
  rw [bvSum_split_zero (fun x => chi ξ x * indBool A.looplessPred x),
      bvSum_split_zero (fun x => chi ξ x * indBool A.accepts x)]
  have hrem : bvSum (fun x : BitVec k => if x = 0 then 0 else chi ξ x * indBool A.looplessPred x) =
              bvSum (fun x : BitVec k => if x = 0 then 0 else chi ξ x * indBool A.accepts x) := by
    apply bvSum_congr
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · have hlp : A.looplessPred x = A.accepts x := by
        unfold BitAutomaton.looplessPred
        have hne : (x != 0) = true := bne_iff_ne.mpr hx
        rw [hne]; rfl
      simp only [hx, ↓reduceIte, indBool, hlp]
  rw [hrem, chi_zero_right, Int.one_mul, Int.one_mul]
  have h0 : indBool A.looplessPred (0 : BitVec k) = 0 := by
    unfold indBool BitAutomaton.looplessPred; simp
  rw [h0]
  unfold indBool
  omega

theorem graphDeg_automaton_loopless {m : Nat} (A : BitAutomaton m) (k : Nat) :
    graphDeg (A.looplessPred (k := k)) =
    A.evalT (0 : BitVec k) A.acceptVec A.init - (if A.accepts (0 : BitVec k) then 1 else 0) := by
  rw [← graphEig_zero, graphEig_automaton_loopless]

theorem graphGap_automaton_loopless {m : Nat} (A : BitAutomaton m) {k : Nat} (ξ : BitVec k) :
    graphDeg (A.looplessPred (k := k)) - graphEig A.looplessPred ξ =
    A.evalT (0 : BitVec k) A.acceptVec A.init - A.evalT ξ A.acceptVec A.init := by
  rw [graphDeg_automaton_loopless, graphEig_automaton_loopless]
  omega

/-- Exact 3-state MSB-first mod-3 automaton. -/
def mod3Aut : BitAutomaton 3 where
  init := ⟨0, by decide⟩
  delta := fun q b => some ⟨(2 * q.val + if b then 1 else 0) % 3, Nat.mod_lt _ (by decide)⟩
  accept := fun q => q.val == 0

/-- Explicit bitwise graph predicate for `G_mod3`: `x ≠ 0 ∧ x.toNat % 3 = 0`. -/
def mod3Pred {k : Nat} (x : BitVec k) : Bool :=
  x != 0 && x.toNat % 3 == 0

theorem nat_or_two_pow_eq_add : ∀ (k n : Nat), n < 2 ^ k → (2 ^ k ||| n) = 2 ^ k + n
  | 0, n, hn => by
    have : n = 0 := by omega
    subst this; decide
  | k + 1, n, hn => by
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
    have hdiv : n / 2 < 2 ^ k := by omega
    have ih := nat_or_two_pow_eq_add k (n / 2) hdiv
    apply Nat.eq_of_testBit_eq
    intro i
    cases i with
    | zero =>
      simp only [Nat.testBit_zero]
      have h0 : 2 ^ (k + 1) % 2 = 0 := by omega
      have h1 : (2 ^ (k + 1) + n) % 2 = n % 2 := by omega
      simp [h0, h1]
    | succ i =>
      rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
      have hhalf1 : 2 ^ (k + 1) / 2 = 2 ^ k := by omega
      have hhalf2 : (2 ^ (k + 1) + n) / 2 = 2 ^ k + n / 2 := by omega
      rw [hhalf1, hhalf2, ← ih, Nat.testBit_or]

theorem bv_cons_toNat {k : Nat} (b : Bool) (x : BitVec k) :
    (BitVec.cons b x).toNat = (if b then 2 ^ k else 0) + x.toNat := by
  cases b with
  | false => simp [BitVec.toNat_cons]
  | true =>
    simp only [BitVec.toNat_cons, Bool.toNat_true, ↓reduceIte]
    have hsl : (1 <<< k : Nat) = 2 ^ k := by rw [Nat.shiftLeft_eq, Nat.one_mul]
    rw [hsl]
    exact nat_or_two_pow_eq_add k x.toNat x.isLt

theorem mod3Aut_run_eq {k : Nat} (q : Fin 3) (x : BitVec k) :
    mod3Aut.run q x = some ⟨(q.val * 2 ^ k + x.toNat) % 3, Nat.mod_lt _ (by decide)⟩ := by
  induction k generalizing q with
  | zero =>
    have hx : x.toNat = 0 := by
      have := bv_zero_width_eq x; subst this; rfl
    simp [BitAutomaton.run, hx, Nat.mod_eq_of_lt q.isLt]
  | succ k ih =>
    rw [bv_eq_cons_msb_truncate x, BitAutomaton.run_cons]
    have hd : mod3Aut.delta q x.msb =
        some ⟨(2 * q.val + if x.msb then 1 else 0) % 3, Nat.mod_lt _ (by decide)⟩ := rfl
    rw [hd]
    dsimp only
    rw [ih]
    congr 1
    apply Fin.ext
    rw [bv_cons_toNat]
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
    cases x.msb
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.zero_add]
      have h1 : (2 * q.val % 3 * 2 ^ k + (x.truncate k).toNat) % 3 =
                (2 * q.val * 2 ^ k + (x.truncate k).toNat) % 3 := by
        rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
      rw [h1, hpow]
      have h2 : 2 * q.val * 2 ^ k = q.val * (2 * 2 ^ k) := by ac_rfl
      rw [h2]
    · simp only [↓reduceIte]
      have h1 : ((2 * q.val + 1) % 3 * 2 ^ k + (x.truncate k).toNat) % 3 =
                ((2 * q.val + 1) * 2 ^ k + (x.truncate k).toNat) % 3 := by
        rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
      rw [h1, hpow]
      have h2 : (2 * q.val + 1) * 2 ^ k + (x.truncate k).toNat =
                q.val * (2 * 2 ^ k) + (2 ^ k + (x.truncate k).toNat) := by
        rw [Nat.add_mul, Nat.one_mul]
        have : 2 * q.val * 2 ^ k = q.val * (2 * 2 ^ k) := by ac_rfl
        omega
      rw [h2]

theorem mod3Aut_accepts_eq {k : Nat} (x : BitVec k) :
    mod3Aut.accepts x = (x.toNat % 3 == 0) := by
  unfold BitAutomaton.accepts
  rw [mod3Aut_run_eq]
  simp [mod3Aut]

theorem mod3Aut_looplessPred_eq {k : Nat} (x : BitVec k) :
    mod3Aut.looplessPred x = mod3Pred x := by
  unfold BitAutomaton.looplessPred mod3Pred
  rw [mod3Aut_accepts_eq]

/-- Bitwise Hamming weight (popcount) defined recursively on `BitVec k`. -/
def popcount : {k : Nat} → BitVec k → Nat
  | 0, _ => 0
  | k + 1, x => (if x.msb then 1 else 0) + popcount (x.truncate k)

theorem popcount_zero {k : Nat} : popcount (0 : BitVec k) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold popcount
    rw [bv_zero_msb, bv_zero_truncate, ih]
    rfl

theorem popcount_le_width {k : Nat} (x : BitVec k) : popcount x ≤ k := by
  induction k with
  | zero => simp [popcount]
  | succ k ih =>
    conv => lhs; unfold popcount
    have h := ih (x.truncate k)
    cases x.msb <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem popcount_pos_of_ne_zero {k : Nat} {x : BitVec k} (hne : x ≠ 0) :
    1 ≤ popcount x := by
  induction k with
  | zero => exact absurd (bv_zero_width_eq x) hne
  | succ k ih =>
    conv => rhs; unfold popcount
    cases hm : x.msb
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      apply ih
      intro ht
      apply hne
      rw [bv_eq_cons_msb_truncate x, hm, ht]
      exact bv_cons_zero.symm
    · simp

theorem eq_allOnes_of_popcount_eq {k : Nat} {x : BitVec k} (h : popcount x = k) :
    x = BitVec.allOnes k := by
  induction k with
  | zero => exact (bv_zero_width_eq x).trans (bv_zero_width_eq _).symm
  | succ k ih =>
    conv at h => lhs; unfold popcount
    have hle := popcount_le_width (x.truncate k)
    cases hm : x.msb with
    | false =>
      simp only [hm, Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at h
      omega
    | true =>
      simp only [hm, ↓reduceIte] at h
      have ht : x.truncate k = BitVec.allOnes k := ih (by omega)
      rw [bv_eq_cons_msb_truncate x, hm, ht]
      ext i hi
      by_cases hk : i = k
      · subst hk; simp [BitVec.getElem_cons]
      · simp [BitVec.getElem_cons, hk]

/-- Exact 3-adic amplitude bound `B(w)`: `B(2m+1) = 3^m`, `B(2m) = 2 * 3^(m-1)`. -/
def mod3B : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | w + 3 => 3 * mod3B (w + 1)

theorem mod3B_add_two (w : Nat) (hw : 1 ≤ w) : mod3B (w + 2) = 3 * mod3B w := by
  cases w with
  | zero => omega
  | succ m => rfl

theorem mod3B_le_succ : ∀ w : Nat, mod3B w ≤ mod3B (w + 1)
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | w + 3 => by
    have h : mod3B (w + 1) ≤ mod3B (w + 2) := mod3B_le_succ (w + 1)
    rw [mod3B_add_two (w + 1) (by omega), mod3B_add_two (w + 2) (by omega)]
    omega

theorem mod3B_mono {a b : Nat} (h : a ≤ b) : mod3B a ≤ mod3B b := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (mod3B_le_succ _)

theorem mod3B_gap_ge_two : ∀ w : Nat, 3 ≤ w → mod3B w + 2 ≤ mod3B (w + 1)
  | 0, h => by omega
  | 1, h => by omega
  | 2, h => by omega
  | 3, _ => by decide
  | 4, _ => by decide
  | w + 5, _ => by
    have ih : mod3B (w + 3) + 2 ≤ mod3B (w + 4) := mod3B_gap_ge_two (w + 3) (by omega)
    rw [mod3B_add_two (w + 3) (by omega), mod3B_add_two (w + 4) (by omega)]
    omega

/-- Eisenstein quadratic form `Q(v) = (v0 - v1)^2 + (v1 - v2)^2 + (v2 - v0)^2` on `Z^3`. -/
def eisensteinQ (v : Fin 3 → Int) : Int :=
  (v ⟨0, by decide⟩ - v ⟨1, by decide⟩) * (v ⟨0, by decide⟩ - v ⟨1, by decide⟩) +
  (v ⟨1, by decide⟩ - v ⟨2, by decide⟩) * (v ⟨1, by decide⟩ - v ⟨2, by decide⟩) +
  (v ⟨2, by decide⟩ - v ⟨0, by decide⟩) * (v ⟨2, by decide⟩ - v ⟨0, by decide⟩)

def vecSum3 (v : Fin 3 → Int) : Int :=
  v ⟨0, by decide⟩ + v ⟨1, by decide⟩ + v ⟨2, by decide⟩

theorem mod3Aut_stepT_false_coords (v : Fin 3 → Int) :
    mod3Aut.stepT false v ⟨0, by decide⟩ = v ⟨0, by decide⟩ + v ⟨1, by decide⟩ ∧
    mod3Aut.stepT false v ⟨1, by decide⟩ = v ⟨2, by decide⟩ + v ⟨0, by decide⟩ ∧
    mod3Aut.stepT false v ⟨2, by decide⟩ = v ⟨1, by decide⟩ + v ⟨2, by decide⟩ := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [BitAutomaton.stepT, mod3Aut, optVal]

theorem mod3Aut_stepT_true_coords (v : Fin 3 → Int) :
    mod3Aut.stepT true v ⟨0, by decide⟩ = v ⟨0, by decide⟩ - v ⟨1, by decide⟩ ∧
    mod3Aut.stepT true v ⟨1, by decide⟩ = v ⟨2, by decide⟩ - v ⟨0, by decide⟩ ∧
    mod3Aut.stepT true v ⟨2, by decide⟩ = v ⟨1, by decide⟩ - v ⟨2, by decide⟩ := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [BitAutomaton.stepT, mod3Aut, optVal] <;> omega

/-- Finite Certificate 1A: `T_0` is an exact integer isometry of `eisensteinQ`. -/
theorem eisensteinQ_stepT_false (v : Fin 3 → Int) :
    eisensteinQ (mod3Aut.stepT false v) = eisensteinQ v := by
  unfold eisensteinQ
  have ⟨h0, h1, h2⟩ := mod3Aut_stepT_false_coords v
  rw [h0, h1, h2]
  generalize v ⟨0, by decide⟩ = a
  generalize v ⟨1, by decide⟩ = b
  generalize v ⟨2, by decide⟩ = c
  have e1 : (a + b) - (c + a) = b - c := by omega
  have e2 : (c + a) - (b + c) = a - b := by omega
  have e3 : (b + c) - (a + b) = c - a := by omega
  rw [e1, e2, e3]
  omega

/-- Finite Certificate 1B: `T_1` annihilates `vecSum3` and scales `eisensteinQ` by exactly `3`. -/
theorem vecSum3_stepT_true (v : Fin 3 → Int) :
    vecSum3 (mod3Aut.stepT true v) = 0 := by
  unfold vecSum3
  have ⟨h0, h1, h2⟩ := mod3Aut_stepT_true_coords v
  rw [h0, h1, h2]
  omega

theorem vecSum3_stepT_false (v : Fin 3 → Int) :
    vecSum3 (mod3Aut.stepT false v) = 2 * vecSum3 v := by
  unfold vecSum3
  have ⟨h0, h1, h2⟩ := mod3Aut_stepT_false_coords v
  rw [h0, h1, h2]
  omega

theorem eisensteinQ_stepT_true (v : Fin 3 → Int) :
    eisensteinQ (mod3Aut.stepT true v) = 3 * eisensteinQ v := by
  unfold eisensteinQ
  have ⟨h0, h1, h2⟩ := mod3Aut_stepT_true_coords v
  rw [h0, h1, h2]
  generalize v ⟨0, by decide⟩ = a
  generalize v ⟨1, by decide⟩ = b
  generalize v ⟨2, by decide⟩ = c
  have sq : ∀ x y : Int, (x - y) * (x - y) = x * x - 2 * (x * y) + y * y := by
    intro x y
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
    have : y * x = x * y := Int.mul_comm y x
    omega
  have hxyz : (a - b) + (b - c) + (c - a) = 0 := by omega
  generalize hx : a - b = x
  generalize hy : b - c = y
  generalize hz : c - a = z
  have h0sum : x + y + z = 0 := by omega
  rw [sq x z, sq z y, sq y x]
  have h0sq : (x + y + z) * (x + y + z) = 0 := by rw [h0sum]; rfl
  have hexp : (x + y + z) * (x + y + z) =
      x * x + y * y + z * z + 2 * (x * z) + 2 * (z * y) + 2 * (y * x) := by
    rw [Int.add_mul, Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_add,
        Int.mul_add, Int.mul_add, Int.mul_add]
    have c1 : z * x = x * z := Int.mul_comm _ _
    have c2 : y * z = z * y := Int.mul_comm _ _
    have c3 : x * y = y * x := Int.mul_comm _ _
    omega
  rw [h0sq] at hexp
  omega

/-- Exact Integer Identity on the zero-sum plane `a + b + c = 0`:
    `2 * Q(a, b, c) = 9 * a^2 + 3 * (b - c)^2`. -/
theorem eisensteinQ_zero_sum (v : Fin 3 → Int) (hs : vecSum3 v = 0) :
    2 * eisensteinQ v =
    9 * (v ⟨0, by decide⟩ * v ⟨0, by decide⟩) +
    3 * ((v ⟨1, by decide⟩ - v ⟨2, by decide⟩) * (v ⟨1, by decide⟩ - v ⟨2, by decide⟩)) := by
  unfold vecSum3 at hs
  unfold eisensteinQ
  generalize v ⟨0, by decide⟩ = a at hs ⊢
  generalize v ⟨1, by decide⟩ = b at hs ⊢
  generalize v ⟨2, by decide⟩ = c at hs ⊢
  have ha : a = -(b + c) := by omega
  have d1 : a - b = -(2 * b + c) := by omega
  have d3 : c - a = b + 2 * c := by omega
  rw [d1, d3, ha]
  have s1 : (-(2 * b + c)) * (-(2 * b + c)) = (2 * b + c) * (2 * b + c) := Int.neg_mul_neg _ _
  have s2 : (-(b + c)) * (-(b + c)) = (b + c) * (b + c) := Int.neg_mul_neg _ _
  rw [s1, s2]
  have e1 : (2 * b + c) * (2 * b + c) = 4 * (b * b) + 4 * (b * c) + c * c := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add]
    have t1 : c * (2 * b) = 2 * (b * c) := by ac_rfl
    have t2 : 2 * b * (2 * b) = 4 * (b * b) := by
      have : (2 : Int) * b * (2 * b) = (2 * 2) * (b * b) := by ac_rfl
      omega
    have t3 : 2 * b * c = 2 * (b * c) := Int.mul_assoc _ _ _
    omega
  have e2 : (b - c) * (b - c) = b * b - 2 * (b * c) + c * c := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
    have : c * b = b * c := Int.mul_comm _ _
    omega
  have e3 : (b + 2 * c) * (b + 2 * c) = b * b + 4 * (b * c) + 4 * (c * c) := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add]
    have t1 : b * (2 * c) = 2 * (b * c) := by ac_rfl
    have t2 : 2 * c * b = 2 * (b * c) := by ac_rfl
    have t3 : 2 * c * (2 * c) = 4 * (c * c) := by
      have : (2 : Int) * c * (2 * c) = (2 * 2) * (c * c) := by ac_rfl
      omega
    omega
  have e4 : (b + c) * (b + c) = b * b + 2 * (b * c) + c * c := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add]
    have : c * b = b * c := Int.mul_comm _ _
    omega
  rw [e1, e2, e3, e4]
  omega

/-- Exact lifted invariant for `mod3Aut.evalT`:
    `Q(v_k) = 2 * 3^(popcount ξ)` for ALL `ξ`, and `vecSum3(v_k) = 0` for all `ξ ≠ 0`. -/
theorem mod3Aut_evalT_invariants {k : Nat} (ξ : BitVec k) :
    eisensteinQ (mod3Aut.evalT ξ mod3Aut.acceptVec) = 2 * ((3 ^ popcount ξ : Nat) : Int) ∧
    (ξ ≠ 0 → vecSum3 (mod3Aut.evalT ξ mod3Aut.acceptVec) = 0) := by
  induction k with
  | zero =>
    have h0 : ξ = 0 := bv_zero_width_eq ξ
    subst h0
    refine ⟨?_, ?_⟩
    · decide
    · intro hne; exact absurd rfl hne
  | succ k ih =>
    have ⟨ihQ, ihS⟩ := ih (ξ.truncate k)
    conv => lhs; unfold BitAutomaton.evalT popcount
    conv => rhs; intro _; unfold BitAutomaton.evalT
    cases hm : ξ.msb
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      refine ⟨?_, ?_⟩
      · rw [eisensteinQ_stepT_false, ihQ]
      · intro hne
        rw [vecSum3_stepT_false]
        have htne : ξ.truncate k ≠ 0 := by
          intro ht
          apply hne
          rw [bv_eq_cons_msb_truncate ξ, hm, ht]
          exact bv_cons_zero.symm
        rw [ihS htne]
        rfl
    · simp only [↓reduceIte]
      refine ⟨?_, ?_⟩
      · rw [eisensteinQ_stepT_true, ihQ]
        have hpow : 3 ^ (1 + popcount (ξ.truncate k)) = 3 * 3 ^ popcount (ξ.truncate k) := by
          rw [Nat.add_comm, Nat.pow_succ, Nat.mul_comm]
        rw [hpow, Int.natCast_mul]
        have : 3 * (2 * ((3 ^ popcount (ξ.truncate k) : Nat) : Int)) =
               2 * ((3 : Int) * ((3 ^ popcount (ξ.truncate k) : Nat) : Int)) := by ac_rfl
        exact this
      · intro _
        exact vecSum3_stepT_true _

/-- Mod-3 divisibility of squares: `3 ∣ x * x → 3 ∣ x`. -/
theorem dvd_three_of_sq_dvd {x : Int} (h : (x * x) % 3 = 0) : x % 3 = 0 := by
  have hmod : (x * x) % 3 = ((x % 3) * (x % 3)) % 3 := Int.mul_emod x x 3
  rw [hmod] at h
  have hlt : 0 ≤ x % 3 ∧ x % 3 < 3 := ⟨Int.emod_nonneg x (by omega), Int.emod_lt_of_pos x (by omega)⟩
  have hcases : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · exact h0
  · rw [h1] at h; omega
  · rw [h2] at h; omega

/-- Exact Mod-3 Infinite Descent on `3 * a^2 + d^2 = 4 * 3^(w - 1)`:
    forces `|a| ≤ mod3B w` for EVERY `w ≥ 1`! -/
theorem eisenstein_descent : ∀ (w : Nat), 1 ≤ w →
    ∀ (a d : Int), 3 * (a * a) + d * d = 4 * ((3 ^ (w - 1) : Nat) : Int) →
    -(mod3B w : Int) ≤ a ∧ a ≤ (mod3B w : Int)
  | 0, hw, _, _, _ => by omega
  | 1, _, a, d, heq => by
    have hd : 0 ≤ d * d := int_mul_self_nonneg d
    have hpow : ((3 ^ (1 - 1) : Nat) : Int) = 1 := rfl
    rw [hpow] at heq
    have ha : 3 * (a * a) ≤ 4 := by omega
    have hlo : -1 ≤ a := by
      by_cases hc : -1 ≤ a
      · exact hc
      · have h2 : 2 ≤ -a := by omega
        have hsq : 4 ≤ (-a) * (-a) := Int.mul_le_mul h2 h2 (by omega) (by omega)
        rw [Int.neg_mul_neg] at hsq
        omega
    have hhi : a ≤ 1 := by
      by_cases hc : a ≤ 1
      · exact hc
      · have h2 : 2 ≤ a := by omega
        have hsq : 4 ≤ a * a := Int.mul_le_mul h2 h2 (by omega) (by omega)
        omega
    exact ⟨hlo, hhi⟩
  | 2, _, a, d, heq => by
    have hd : 0 ≤ d * d := int_mul_self_nonneg d
    have hpow : ((3 ^ (2 - 1) : Nat) : Int) = 3 := rfl
    rw [hpow] at heq
    have ha : 3 * (a * a) ≤ 12 := by omega
    have hlo : -2 ≤ a := by
      by_cases hc : -2 ≤ a
      · exact hc
      · have h3 : 3 ≤ -a := by omega
        have hsq : 9 ≤ (-a) * (-a) := Int.mul_le_mul h3 h3 (by omega) (by omega)
        rw [Int.neg_mul_neg] at hsq
        omega
    have hhi : a ≤ 2 := by
      by_cases hc : a ≤ 2
      · exact hc
      · have h3 : 3 ≤ a := by omega
        have hsq : 9 ≤ a * a := Int.mul_le_mul h3 h3 (by omega) (by omega)
        omega
    exact ⟨hlo, hhi⟩
  | w + 3, _, a, d, heq => by
    have hw1 : 1 ≤ w + 1 := by omega
    have hpow : ((3 ^ (w + 3 - 1) : Nat) : Int) = 9 * ((3 ^ (w + 1 - 1) : Nat) : Int) := by
      have hnat : 3 ^ (w + 3 - 1) = 9 * 3 ^ (w + 1 - 1) := by
        have he : w + 3 - 1 = (w + 1 - 1) + 2 := by omega
        rw [he, Nat.pow_succ, Nat.pow_succ]
        omega
      rw [hnat, Int.natCast_mul]
      rfl
    rw [hpow] at heq
    have hdmod : (d * d) % 3 = 0 := by omega
    have hd3 : d % 3 = 0 := dvd_three_of_sq_dvd hdmod
    let d' := d / 3
    have hd_eq : d = 3 * d' := by omega
    rw [hd_eq] at heq
    have hsqd : (3 * d') * (3 * d') = 9 * (d' * d') := by
      have : (3 : Int) * d' * (3 * d') = (3 * 3) * (d' * d') := by ac_rfl
      omega
    rw [hsqd] at heq
    have heq1 : a * a + 3 * (d' * d') = 12 * ((3 ^ (w + 1 - 1) : Nat) : Int) := by omega
    have hamod : (a * a) % 3 = 0 := by omega
    have ha3 : a % 3 = 0 := dvd_three_of_sq_dvd hamod
    let a' := a / 3
    have ha_eq : a = 3 * a' := by omega
    rw [ha_eq] at heq1
    have hsqa : (3 * a') * (3 * a') = 9 * (a' * a') := by
      have : (3 : Int) * a' * (3 * a') = (3 * 3) * (a' * a') := by ac_rfl
      omega
    rw [hsqa] at heq1
    have heq2 : 3 * (a' * a') + d' * d' = 4 * ((3 ^ (w + 1 - 1) : Nat) : Int) := by omega
    have ⟨ihlo, ihhi⟩ := eisenstein_descent (w + 1) hw1 a' d' heq2
    rw [mod3B_add_two (w + 1) hw1, Int.natCast_mul]
    have h3 : ((3 : Nat) : Int) = 3 := rfl
    rw [h3]
    omega

/-- **Theorem A.1 (Exact 3-Adic Amplitude Bound):**
    For ALL `k ≥ 1` and ALL `ξ : BitVec k`, `ξ ≠ 0`,
    `|evalT mod3Aut ξ acceptVec 0| ≤ B(popcount ξ) ≤ B(k)`. -/
theorem mod3Aut_evalT_abs_bound {k : Nat} {ξ : BitVec k} (hne : ξ ≠ 0) :
    -(mod3B (popcount ξ) : Int) ≤ mod3Aut.evalT ξ mod3Aut.acceptVec mod3Aut.init ∧
    mod3Aut.evalT ξ mod3Aut.acceptVec mod3Aut.init ≤ (mod3B (popcount ξ) : Int) := by
  have ⟨hQ, hS⟩ := mod3Aut_evalT_invariants ξ
  have hS0 := hS hne
  have hzs := eisensteinQ_zero_sum (mod3Aut.evalT ξ mod3Aut.acceptVec) hS0
  rw [hQ] at hzs
  have hwpos : 1 ≤ popcount ξ := popcount_pos_of_ne_zero hne
  have hpow : ((3 ^ popcount ξ : Nat) : Int) = 3 * ((3 ^ (popcount ξ - 1) : Nat) : Int) := by
    have hnat : 3 ^ popcount ξ = 3 * 3 ^ (popcount ξ - 1) := by
      have he : popcount ξ = (popcount ξ - 1) + 1 := by omega
      conv => lhs; rw [he]
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [hnat, Int.natCast_mul]; rfl
  rw [hpow] at hzs
  have hdioph : 3 * (mod3Aut.evalT ξ mod3Aut.acceptVec ⟨0, by decide⟩ *
                     mod3Aut.evalT ξ mod3Aut.acceptVec ⟨0, by decide⟩) +
                (mod3Aut.evalT ξ mod3Aut.acceptVec ⟨1, by decide⟩ -
                 mod3Aut.evalT ξ mod3Aut.acceptVec ⟨2, by decide⟩) *
                (mod3Aut.evalT ξ mod3Aut.acceptVec ⟨1, by decide⟩ -
                 mod3Aut.evalT ξ mod3Aut.acceptVec ⟨2, by decide⟩) =
                4 * ((3 ^ (popcount ξ - 1) : Nat) : Int) := by
    omega
  exact eisenstein_descent (popcount ξ) hwpos _ _ hdioph

theorem mod3Aut_evalT_le_bound {k : Nat} {ξ : BitVec k} (hne : ξ ≠ 0) :
    -(mod3B k : Int) ≤ mod3Aut.evalT ξ mod3Aut.acceptVec mod3Aut.init ∧
    mod3Aut.evalT ξ mod3Aut.acceptVec mod3Aut.init ≤ (mod3B k : Int) := by
  have ⟨hlo, hhi⟩ := mod3Aut_evalT_abs_bound hne
  have hmono : (mod3B (popcount ξ) : Int) ≤ (mod3B k : Int) := by
    exact_mod_cast mod3B_mono (popcount_le_width ξ)
  omega

/-- Exact degree evaluation for `mod3Aut`: `evalT 0 = (2^k + 2) / 3`. -/
theorem mod3Aut_evalT_zero_triple : ∀ k : Nat,
    let q := (2 ^ k - 1) / 3
    if k % 2 = 0 then
      mod3Aut.evalT (0 : BitVec k) mod3Aut.acceptVec ⟨0, by decide⟩ = (q + 1 : Nat) ∧
      mod3Aut.evalT (0 : BitVec k) mod3Aut.acceptVec ⟨1, by decide⟩ = (q : Nat) ∧
      mod3Aut.evalT (0 : BitVec k) mod3Aut.acceptVec ⟨2, by decide⟩ = (q : Nat) ∧
      3 * q + 1 = 2 ^ k
    else
      mod3Aut.evalT (0 : BitVec k) mod3Aut.acceptVec ⟨0, by decide⟩ = (q + 1 : Nat) ∧
      mod3Aut.evalT (0 : BitVec k) mod3Aut.acceptVec ⟨1, by decide⟩ = (q + 1 : Nat) ∧
      mod3Aut.evalT (0 : BitVec k) mod3Aut.acceptVec ⟨2, by decide⟩ = (q : Nat) ∧
      3 * q + 2 = 2 ^ k
  | 0 => by decide
  | k + 1 => by
    have ih := mod3Aut_evalT_zero_triple k
    have hstep : mod3Aut.evalT (0 : BitVec (k + 1)) mod3Aut.acceptVec =
                 mod3Aut.stepT false (mod3Aut.evalT (0 : BitVec k) mod3Aut.acceptVec) := by
      conv => lhs; unfold BitAutomaton.evalT
      rw [bv_zero_msb, bv_zero_truncate]
    have ⟨c0, c1, c2⟩ := mod3Aut_stepT_false_coords (mod3Aut.evalT (0 : BitVec k) mod3Aut.acceptVec)
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
    by_cases hpar : k % 2 = 0
    · have hpar1 : (k + 1) % 2 ≠ 0 := by omega
      simp only [hpar, ↓reduceIte] at ih
      simp only [hpar1, ↓reduceIte]
      have ⟨h0, h1, h2, h3⟩ := ih
      have hq' : (2 ^ (k + 1) - 1) / 3 = 2 * ((2 ^ k - 1) / 3) := by omega
      rw [hstep, c0, c1, c2, h0, h1, h2, hq']
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
    · have hpar1 : (k + 1) % 2 = 0 := by omega
      simp only [hpar, ↓reduceIte] at ih
      simp only [hpar1, ↓reduceIte]
      have ⟨h0, h1, h2, h3⟩ := ih
      have hq' : (2 ^ (k + 1) - 1) / 3 = 2 * ((2 ^ k - 1) / 3) + 1 := by omega
      rw [hstep, c0, c1, c2, h0, h1, h2, hq']
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem mod3Aut_evalT_zero (k : Nat) :
    mod3Aut.evalT (0 : BitVec k) mod3Aut.acceptVec mod3Aut.init = (((2 ^ k + 2) / 3 : Nat) : Int) := by
  have ht := mod3Aut_evalT_zero_triple k
  by_cases hpar : k % 2 = 0
  · simp only [hpar, ↓reduceIte] at ht
    have ⟨h0, _, _, h3⟩ := ht
    have heq : (2 ^ k - 1) / 3 + 1 = (2 ^ k + 2) / 3 := by omega
    rw [← heq]; exact h0
  · simp only [hpar, ↓reduceIte] at ht
    have ⟨h0, _, _, h3⟩ := ht
    have heq : (2 ^ k - 1) / 3 + 1 = (2 ^ k + 2) / 3 := by omega
    rw [← heq]; exact h0

/-- Exact tightness evaluation at `allOnes k`: `evalT (allOnes k) = +mod3B k` (`∀ k ≥ 1`). -/
theorem mod3Aut_stepT_true_twice_zero_sum (v : Fin 3 → Int) (hs : vecSum3 v = 0) :
    ∀ q : Fin 3, mod3Aut.stepT true (mod3Aut.stepT true v) q = 3 * v q := by
  intro q
  unfold vecSum3 at hs
  have ⟨a0, a1, a2⟩ := mod3Aut_stepT_true_coords v
  have ⟨b0, b1, b2⟩ := mod3Aut_stepT_true_coords (mod3Aut.stepT true v)
  match q with
  | ⟨0, _⟩ => rw [b0, a0, a1]; omega
  | ⟨1, _⟩ => rw [b1, a2, a0]; omega
  | ⟨2, _⟩ => rw [b2, a1, a2]; omega

theorem bv_allOnes_msb {k : Nat} : (BitVec.allOnes (k + 1)).msb = true := by
  rw [BitVec.msb_eq_getLsbD_last]
  simp

theorem bv_allOnes_truncate {k : Nat} : (BitVec.allOnes (k + 1)).truncate k = BitVec.allOnes k := by
  ext i hi
  simp [BitVec.truncate]
  omega

theorem bv_allOnes_ne_zero {k : Nat} (hk : 1 ≤ k) : BitVec.allOnes k ≠ 0 := by
  cases k with
  | zero => omega
  | succ k =>
    intro hc
    have hm := congrArg BitVec.msb hc
    rw [bv_allOnes_msb, bv_zero_msb] at hm
    exact Bool.noConfusion hm

theorem mod3Aut_evalT_allOnes : ∀ k : Nat, 1 ≤ k →
    mod3Aut.evalT (BitVec.allOnes k) mod3Aut.acceptVec mod3Aut.init = (mod3B k : Int)
  | 0, hk => by omega
  | 1, _ => by decide
  | 2, _ => by decide
  | k + 3, _ => by
    have hk1 : 1 ≤ k + 1 := by omega
    have ih := mod3Aut_evalT_allOnes (k + 1) hk1
    have hstep1 : mod3Aut.evalT (BitVec.allOnes (k + 3)) mod3Aut.acceptVec =
        mod3Aut.stepT true (mod3Aut.evalT (BitVec.allOnes (k + 2)) mod3Aut.acceptVec) := by
      conv => lhs; unfold BitAutomaton.evalT
      rw [bv_allOnes_msb, bv_allOnes_truncate]
    have hstep2 : mod3Aut.evalT (BitVec.allOnes (k + 2)) mod3Aut.acceptVec =
        mod3Aut.stepT true (mod3Aut.evalT (BitVec.allOnes (k + 1)) mod3Aut.acceptVec) := by
      conv => lhs; unfold BitAutomaton.evalT
      rw [bv_allOnes_msb, bv_allOnes_truncate]
    have hzs := (mod3Aut_evalT_invariants (BitVec.allOnes (k + 1))).2 (bv_allOnes_ne_zero hk1)
    rw [hstep1, hstep2, mod3Aut_stepT_true_twice_zero_sum _ hzs, ih, mod3B_add_two (k + 1) hk1,
        Int.natCast_mul]
    rfl

/-- Exact spectral gap formula for `G_mod3`. -/
def mod3Gap (k : Nat) : Int :=
  (((2 ^ k + 2) / 3 : Nat) : Int) - (mod3B k : Int)

theorem mod3Pred_deg (k : Nat) :
    graphDeg (mod3Pred (k := k)) = (((2 ^ k - 1) / 3 : Nat) : Int) := by
  have hcongr : graphDeg (mod3Pred (k := k)) = graphDeg (mod3Aut.looplessPred (k := k)) := by
    unfold graphDeg indBool
    apply bvSum_congr
    intro x
    rw [mod3Aut_looplessPred_eq]
  rw [hcongr, graphDeg_automaton_loopless, mod3Aut_evalT_zero, mod3Aut_accepts_eq]
  have h0 : ((0 : BitVec k).toNat % 3 == 0) = true := by simp
  rw [h0]
  simp only [↓reduceIte]
  have hpos : 1 ≤ 2 ^ k := Nat.two_pow_pos k
  have hdiv : (2 ^ k + 2) / 3 = (2 ^ k - 1) / 3 + 1 := by omega
  omega

theorem mod3B_strict_lt_aux : ∀ n : Nat, 5 ≤ n → 3 * mod3B n + 2 < 2 ^ n + 2
  | 0, h => by omega
  | 1, h => by omega
  | 2, h => by omega
  | 3, h => by omega
  | 4, h => by omega
  | 5, _ => by decide
  | 6, _ => by decide
  | m + 7, _ => by
    have ih := mod3B_strict_lt_aux (m + 5) (by omega)
    rw [mod3B_add_two (m + 5) (by omega)]
    have hpow : 2 ^ (m + 7) = 4 * 2 ^ (m + 5) := by
      rw [Nat.pow_succ, Nat.pow_succ]; omega
    have h2m : 32 ≤ 2 ^ (m + 5) := by
      have hle : 2 ^ 5 ≤ 2 ^ (m + 5) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    omega

/-- **THEOREM A.2 (Exact Phase Transition at k = 5):**
    `mod3Gap k = 0` for `1 ≤ k ≤ 4` (disconnected), and `mod3Gap k > 0` for ALL `k ≥ 5`! -/
theorem mod3_strict_gap_pos (k : Nat) (hk : 5 ≤ k) : 0 < mod3Gap k := by
  unfold mod3Gap
  have h := mod3B_strict_lt_aux k hk
  omega

/-- **THEOREM A.3 (Exact Two-Sided Spectral Radius & Integer Expander Mixing Lemma for `G_mod3`, ∀ k ≥ 4):** -/
theorem mod3_two_sided_bound {k : Nat} (hk : 4 ≤ k) (ξ : BitVec k) (hne : ξ ≠ 0) :
    -((mod3B k : Int) - 1) ≤ graphEig mod3Pred ξ ∧ graphEig mod3Pred ξ ≤ (mod3B k : Int) - 1 := by
  have heq : graphEig mod3Pred ξ = graphEig mod3Aut.looplessPred ξ := by
    unfold graphEig wht indBool
    apply bvSum_congr; intro x; rw [mod3Aut_looplessPred_eq]
  rw [heq, graphEig_automaton_loopless, mod3Aut_accepts_eq]
  have h0 : ((0 : BitVec k).toNat % 3 == 0) = true := by simp
  rw [h0]
  simp only [↓reduceIte]
  by_cases hall : popcount ξ = k
  · have hxi : ξ = BitVec.allOnes k := eq_allOnes_of_popcount_eq hall
    rw [hxi, mod3Aut_evalT_allOnes k (by omega)]
    have hbpos : 1 ≤ mod3B k := mod3B_mono (show 1 ≤ k by omega)
    omega
  · have hlt : popcount ξ ≤ k - 1 := by
      have hle := popcount_le_width ξ
      omega
    have ⟨hlo, hhi⟩ := mod3Aut_evalT_abs_bound hne
    have hmono : mod3B (popcount ξ) ≤ mod3B (k - 1) := mod3B_mono hlt
    have hgap2 : mod3B (k - 1) + 2 ≤ mod3B k := by
      have h := mod3B_gap_ge_two (k - 1) (by omega)
      have he : k - 1 + 1 = k := by omega
      rw [he] at h
      exact h
    omega

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

def lucas : Nat → Nat
  | 0 => 2
  | n + 1 => fib n + fib (n + 2)

theorem fib_add_two (n : Nat) : fib (n + 2) = fib (n + 1) + fib n := rfl
theorem lucas_succ (n : Nat) : lucas (n + 1) = fib n + fib (n + 2) := rfl

theorem lucas_add_two (n : Nat) : lucas (n + 2) = lucas (n + 1) + lucas n := by
  cases n with
  | zero => decide
  | succ m =>
    rw [lucas_succ (m + 2), lucas_succ (m + 1), lucas_succ m]
    rw [fib_add_two (m + 2), fib_add_two (m + 1), fib_add_two m]
    omega

theorem fib_sub_lucas (k : Nat) (hk : 2 ≤ k) :
    fib (k + 2) = lucas (k - 1) + 2 * fib (k - 1) := by
  cases k with
  | zero => omega
  | succ m =>
    cases m with
    | zero => omega
    | succ r =>
      have he : r + 1 + 1 - 1 = r + 1 := by omega
      have he2 : r + 1 + 1 + 2 = r + 4 := by omega
      rw [he, he2, lucas_succ r, fib_add_two (r + 2), fib_add_two (r + 1), fib_add_two r]
      omega

theorem fib_le_lucas (n : Nat) (hn : 1 ≤ n) : fib n ≤ lucas n := by
  cases n with
  | zero => omega
  | succ m =>
    rw [lucas_succ m, fib_add_two m]
    omega

theorem fib_mono_succ : ∀ n : Nat, fib n ≤ fib (n + 1)
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by
    have h : fib (n + 2 + 1) = fib (n + 2) + fib (n + 1) := rfl
    omega

theorem fib_pos_succ : ∀ n : Nat, 1 ≤ fib (n + 1)
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by
    have ih : 1 ≤ fib (n + 2) := fib_pos_succ (n + 1)
    have h : fib (n + 2 + 1) = fib (n + 2) + fib (n + 1) := rfl
    omega

theorem lucas_sub_fib_ge_two (k : Nat) (hk : 3 ≤ k) :
    fib (k - 1) + 2 ≤ lucas (k - 1) := by
  cases k with
  | zero => omega
  | succ m =>
    cases m with
    | zero => omega
    | succ r =>
      cases r with
      | zero => omega
      | succ s =>
        have he : s + 1 + 1 + 1 - 1 = s + 2 := by omega
        rw [he, lucas_succ (s + 1), fib_add_two (s + 1), fib_add_two s]
        have h1 := fib_pos_succ s
        omega

/-- 2-state partial bit-automaton recognizing Fibbinary strings (no adjacent 1-bits). -/
def fibAut : BitAutomaton 2 where
  init := ⟨0, by decide⟩
  delta := fun q b =>
    if q.val == 0 then
      if b then some ⟨1, by decide⟩ else some ⟨0, by decide⟩
    else
      if b then none else some ⟨0, by decide⟩
  accept := fun _ => true

/-- Explicit bitwise Fibbinary predicate: `x ≠ 0 ∧ (x &&& (x >>> 1)) = 0`. -/
def fibPred {k : Nat} (x : BitVec k) : Bool :=
  x != 0 && (x &&& (x >>> 1)) == 0

theorem bv_getLsbD_shift1 {k : Nat} (x : BitVec k) (i : Nat) :
    x.getLsbD (1 + i) = if h : i + 1 < k then x[i + 1]'h else false := by
  by_cases h : i + 1 < k
  · simp only [h, ↓reduceDIte]
    have heq : 1 + i = i + 1 := by omega
    rw [heq, BitVec.getLsbD_eq_getElem]
  · simp only [h, ↓reduceDIte, BitVec.getLsbD]
    exact Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by omega)))

theorem bv_cons_and_shr1_eq_zero_iff {k : Nat} (b : Bool) (x : BitVec k) :
    (BitVec.cons b x &&& (BitVec.cons b x >>> 1)) = 0 ↔
    ((b = true → ∀ h : 0 < k, x[k - 1] = false) ∧ (x &&& (x >>> 1)) = 0) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro hb hk
      have hget := congrArg (fun v : BitVec (k + 1) => v[k - 1]'(by omega)) h
      simp only [BitVec.getElem_and, BitVec.getElem_ushiftRight, bv_getLsbD_shift1] at hget
      have hlt : k - 1 + 1 < k + 1 := by omega
      simp only [hlt, ↓reduceDIte] at hget
      have h1 : (BitVec.cons b x)[k - 1]'(by omega) = x[k - 1]'(by omega) := by
        simp [BitVec.getElem_cons, show k - 1 ≠ k by omega]
      have h2 : (BitVec.cons b x)[k - 1 + 1]'hlt = b := by
        have heq : k - 1 + 1 = k := by omega
        simp [heq, BitVec.getElem_cons]
      have h0 : (0 : BitVec (k + 1))[k - 1]'(by omega) = false := by simp
      rw [h1, h2, hb, h0] at hget
      simp at hget
      exact hget
    · ext i hi
      have hget := congrArg (fun v : BitVec (k + 1) => v[i]'(by omega)) h
      simp only [BitVec.getElem_and, BitVec.getElem_ushiftRight, bv_getLsbD_shift1] at hget ⊢
      have h01 : (0 : BitVec (k + 1))[i]'(by omega) = false := by simp
      have h02 : (0 : BitVec k)[i]'hi = false := by simp
      rw [h01] at hget; rw [h02]
      have h1 : (BitVec.cons b x)[i]'(by omega) = x[i] := by
        simp [BitVec.getElem_cons, Nat.ne_of_lt hi]
      by_cases hlt : i + 1 < k
      · have hlt' : i + 1 < k + 1 := by omega
        have h2 : (BitVec.cons b x)[i + 1]'hlt' = x[i + 1]'hlt := by
          simp [BitVec.getElem_cons, Nat.ne_of_lt hlt]
        simp only [hlt, hlt', ↓reduceDIte] at hget ⊢
        rw [h1, h2] at hget
        exact hget
      · simp [hlt]
  · rintro ⟨hcross, hrest⟩
    ext i hi
    simp only [BitVec.getElem_and, BitVec.getElem_ushiftRight, bv_getLsbD_shift1]
    have h01 : (0 : BitVec (k + 1))[i]'hi = false := by simp
    rw [h01]
    by_cases hk : i = k
    · subst hk
      have hnot : ¬ (i + 1 < i + 1) := by omega
      simp [hnot]
    · by_cases hlast : i + 1 = k
      · have hpos : 0 < k := by omega
        have hi_eq : i = k - 1 := by omega
        have hlt' : i + 1 < k + 1 := by omega
        simp only [hlt', ↓reduceDIte]
        have h1 : (BitVec.cons b x)[i]'hi = x[k - 1]'(by omega) := by
          subst hi_eq; simp [BitVec.getElem_cons, show k - 1 ≠ k by omega]
        have h2 : (BitVec.cons b x)[i + 1]'hlt' = b := by
          simp [hlast, BitVec.getElem_cons]
        rw [h1, h2]
        cases b
        · simp
        · rw [hcross rfl hpos]; simp
      · have hlt : i + 1 < k := by omega
        have hlt' : i + 1 < k + 1 := by omega
        simp only [hlt', ↓reduceDIte]
        have h1 : (BitVec.cons b x)[i]'hi = x[i]'(by omega) := by
          simp [BitVec.getElem_cons, hk]
        have h2 : (BitVec.cons b x)[i + 1]'hlt' = x[i + 1]'hlt := by
          simp [BitVec.getElem_cons, hlast]
        rw [h1, h2]
        have hget := congrArg (fun v : BitVec k => v[i]'(by omega)) hrest
        simp only [BitVec.getElem_and, BitVec.getElem_ushiftRight, bv_getLsbD_shift1,
                   hlt, ↓reduceDIte] at hget
        have h02 : (0 : BitVec k)[i]'(by omega) = false := by simp
        rw [h02] at hget
        exact hget

theorem fibAut_run_isSome_iff : ∀ {k : Nat} (x : BitVec k),
    ((fibAut.run ⟨0, by decide⟩ x).isSome = true ↔ (x &&& (x >>> 1)) = 0) ∧
    ((fibAut.run ⟨1, by decide⟩ x).isSome = true ↔
      (∀ h : 0 < k, x[k - 1] = false) ∧ (x &&& (x >>> 1)) = 0)
  | 0, x => by
    have hx : x = 0 := bv_zero_width_eq x
    subst hx
    refine ⟨?_, ?_⟩
    · simp [BitAutomaton.run]
    · constructor
      · intro _; refine ⟨fun h => by omega, rfl⟩
      · intro _; simp [BitAutomaton.run]
  | k + 1, x => by
    rw [bv_eq_cons_msb_truncate x]
    have ⟨ih0, ih1⟩ := fibAut_run_isSome_iff (x.truncate k)
    have hmsb : ∀ (b : Bool) (h : 0 < k + 1), (BitVec.cons b (x.truncate k))[k + 1 - 1] = b := by
      intro b _; simp [BitVec.getElem_cons]
    refine ⟨?_, ?_⟩
    · rw [BitAutomaton.run_cons, bv_cons_and_shr1_eq_zero_iff]
      cases hm : x.msb
      · have hd : fibAut.delta ⟨0, by decide⟩ false = some ⟨0, by decide⟩ := rfl
        rw [hd]; dsimp only
        rw [ih0]
        simp
      · have hd : fibAut.delta ⟨0, by decide⟩ true = some ⟨1, by decide⟩ := rfl
        rw [hd]; dsimp only
        rw [ih1]
        simp
    · rw [BitAutomaton.run_cons, bv_cons_and_shr1_eq_zero_iff]
      cases hm : x.msb
      · have hd : fibAut.delta ⟨1, by decide⟩ false = some ⟨0, by decide⟩ := rfl
        rw [hd]; dsimp only
        rw [ih0]
        constructor
        · intro h
          refine ⟨fun hk => hmsb false hk, ⟨fun hc => Bool.noConfusion hc, h⟩⟩
        · rintro ⟨_, _, h⟩; exact h
      · have hd : fibAut.delta ⟨1, by decide⟩ true = none := rfl
        rw [hd]; dsimp only
        constructor
        · intro h; simp at h
        · rintro ⟨hfalse, _, _⟩
          have h0 := hfalse (by omega)
          rw [hmsb true (by omega)] at h0
          exact Bool.noConfusion h0

theorem fibAut_accepts_eq {k : Nat} (x : BitVec k) :
    fibAut.accepts x = ((x &&& (x >>> 1)) == 0) := by
  have h0 := (fibAut_run_isSome_iff x).1
  unfold BitAutomaton.accepts
  have hinit : fibAut.init = ⟨0, by decide⟩ := rfl
  rw [hinit]
  cases hr : fibAut.run ⟨0, by decide⟩ x with
  | none =>
    have hnot : (x &&& (x >>> 1)) ≠ 0 := by
      intro heq
      have hs := h0.mpr heq
      rw [hr] at hs
      simp at hs
    exact (beq_eq_false_iff_ne.mpr hnot).symm
  | some q =>
    have hs : (fibAut.run ⟨0, by decide⟩ x).isSome = true := by rw [hr]; rfl
    have heq := h0.mp hs
    simp [fibAut, heq]

theorem fibAut_looplessPred_eq {k : Nat} (x : BitVec k) :
    fibAut.looplessPred x = fibPred x := by
  unfold BitAutomaton.looplessPred fibPred
  rw [fibAut_accepts_eq]

theorem fibAut_stepT_false_coords (v : Fin 2 → Int) :
    fibAut.stepT false v ⟨0, by decide⟩ = v ⟨0, by decide⟩ + v ⟨1, by decide⟩ ∧
    fibAut.stepT false v ⟨1, by decide⟩ = v ⟨0, by decide⟩ := by
  refine ⟨?_, ?_⟩ <;> simp [BitAutomaton.stepT, fibAut, optVal]

theorem fibAut_stepT_true_coords (v : Fin 2 → Int) :
    fibAut.stepT true v ⟨0, by decide⟩ = v ⟨0, by decide⟩ - v ⟨1, by decide⟩ ∧
    fibAut.stepT true v ⟨1, by decide⟩ = v ⟨0, by decide⟩ := by
  refine ⟨?_, ?_⟩ <;> simp [BitAutomaton.stepT, fibAut, optVal] <;> omega

/-- Exact degree evaluation for `fibAut`: `evalT 0 = (F_{k+2}, F_{k+1})`. -/
theorem fibAut_evalT_zero : ∀ k : Nat,
    fibAut.evalT (0 : BitVec k) fibAut.acceptVec ⟨0, by decide⟩ = (fib (k + 2) : Int) ∧
    fibAut.evalT (0 : BitVec k) fibAut.acceptVec ⟨1, by decide⟩ = (fib (k + 1) : Int)
  | 0 => by decide
  | k + 1 => by
    have ⟨ih0, ih1⟩ := fibAut_evalT_zero k
    have hstep : fibAut.evalT (0 : BitVec (k + 1)) fibAut.acceptVec =
                 fibAut.stepT false (fibAut.evalT (0 : BitVec k) fibAut.acceptVec) := by
      conv => lhs; unfold BitAutomaton.evalT
      rw [bv_zero_msb, bv_zero_truncate]
    have ⟨c0, c1⟩ := fibAut_stepT_false_coords (fibAut.evalT (0 : BitVec k) fibAut.acceptVec)
    rw [hstep, c0, c1, ih0, ih1]
    have hf : fib (k + 1 + 2) = fib (k + 2) + fib (k + 1) := rfl
    have hf1 : fib (k + 1 + 1) = fib (k + 2) := rfl
    exact ⟨by omega, by rw [hf1]⟩

/-- **Finite Certificate 2A (Closed 2-Inequality Lucas Upper Cone for `ξ ≠ 0`, `∀ k ≥ 2`):**
    For ALL `m : Nat` and ALL `ξ : BitVec (m + 2)` with `ξ ≠ 0`, letting `(a, b) = evalT ξ`:
    `|a| ≤ L_{m + 1}` and `|a| + |b| ≤ L_{m + 2}`. -/
theorem fibAut_lucas_cone : ∀ (m : Nat) (ξ : BitVec (m + 2)), ξ ≠ 0 →
    (-(lucas (m + 1) : Int) ≤ fibAut.evalT ξ fibAut.acceptVec ⟨0, by decide⟩ ∧
     fibAut.evalT ξ fibAut.acceptVec ⟨0, by decide⟩ ≤ (lucas (m + 1) : Int) ∧
     -(lucas (m + 2) : Int) ≤ fibAut.evalT ξ fibAut.acceptVec ⟨0, by decide⟩ +
                              fibAut.evalT ξ fibAut.acceptVec ⟨1, by decide⟩ ∧
     fibAut.evalT ξ fibAut.acceptVec ⟨0, by decide⟩ +
       fibAut.evalT ξ fibAut.acceptVec ⟨1, by decide⟩ ≤ (lucas (m + 2) : Int) ∧
     -(lucas (m + 2) : Int) ≤ fibAut.evalT ξ fibAut.acceptVec ⟨0, by decide⟩ -
                              fibAut.evalT ξ fibAut.acceptVec ⟨1, by decide⟩ ∧
     fibAut.evalT ξ fibAut.acceptVec ⟨0, by decide⟩ -
       fibAut.evalT ξ fibAut.acceptVec ⟨1, by decide⟩ ≤ (lucas (m + 2) : Int))
  | 0, ξ, hne => by
    rw [bv_eq_cons_msb_truncate ξ] at hne ⊢
    have htr := bv_eq_cons_msb_truncate (ξ.truncate 1)
    have h00 : (ξ.truncate 1).truncate 0 = 0 := bv_zero_width_eq _
    rw [htr, h00] at hne ⊢
    cases hm : ξ.msb <;> cases hl : (ξ.truncate 1).msb
    · rw [hm, hl] at hne; exact absurd (by decide) hne
    · decide
    · decide
    · decide
  | m + 1, ξ, hne => by
    have hstep : fibAut.evalT ξ fibAut.acceptVec =
                 fibAut.stepT ξ.msb (fibAut.evalT (ξ.truncate (m + 2)) fibAut.acceptVec) := by
      conv => lhs; unfold BitAutomaton.evalT
    have hL2 : lucas (m + 1 + 1) = lucas (m + 2) := rfl
    have hL3 : lucas (m + 1 + 2) = lucas (m + 3) := rfl
    rw [hL2, hL3]
    by_cases ht0 : ξ.truncate (m + 2) = 0
    · have hmsb : ξ.msb = true := by
        cases hm : ξ.msb
        · exfalso; apply hne
          rw [bv_eq_cons_msb_truncate ξ, hm, ht0]; exact bv_cons_zero.symm
        · rfl
      rw [hstep, hmsb, ht0]
      have ⟨c0, c1⟩ := fibAut_stepT_true_coords (fibAut.evalT (0 : BitVec (m + 2)) fibAut.acceptVec)
      have ⟨z0, z1⟩ := fibAut_evalT_zero (m + 2)
      rw [c0, c1, z0, z1, lucas_succ (m + 1), lucas_succ (m + 2)]
      have hf4a : fib (m + 2 + 2) = fib (m + 4) := rfl
      have hf3a : fib (m + 2 + 1) = fib (m + 3) := rfl
      have hf3b : fib (m + 1 + 2) = fib (m + 3) := rfl
      have hf4 : fib (m + 4) = fib (m + 3) + fib (m + 2) := rfl
      have hf3 : fib (m + 3) = fib (m + 2) + fib (m + 1) := rfl
      omega
    · have ⟨h1, h2, h3, h4, h5, h6⟩ := fibAut_lucas_cone m (ξ.truncate (m + 2)) ht0
      have hlrec : lucas (m + 3) = lucas (m + 2) + lucas (m + 1) := lucas_add_two (m + 1)
      rw [hstep]
      cases hm : ξ.msb
      · have ⟨c0, c1⟩ := fibAut_stepT_false_coords (fibAut.evalT (ξ.truncate (m + 2)) fibAut.acceptVec)
        rw [c0, c1]
        omega
      · have ⟨c0, c1⟩ := fibAut_stepT_true_coords (fibAut.evalT (ξ.truncate (m + 2)) fibAut.acceptVec)
        rw [c0, c1]
        omega

/-- **Finite Certificate 2B (Closed 5-Inequality Fibonacci Polytope for ALL `ξ`, `∀ k ≥ 2`):**
    Certifies the exact negative spectral extreme `evalT ξ 0 ≥ -F_{k-1}` and `evalT ξ 1 ≥ -F_{k-2}`. -/
theorem fibAut_lower_polytope : ∀ (m : Nat) (ξ : BitVec (m + 2)),
    (fibAut.evalT ξ fibAut.acceptVec ⟨0, by decide⟩ ≤ (fib (m + 4) : Int) ∧
     fibAut.evalT ξ fibAut.acceptVec ⟨1, by decide⟩ ≤ (fib (m + 3) : Int) ∧
     -(fib (m + 1) : Int) ≤ fibAut.evalT ξ fibAut.acceptVec ⟨0, by decide⟩ ∧
     -(fib m : Int) ≤ fibAut.evalT ξ fibAut.acceptVec ⟨1, by decide⟩ ∧
     -(fib (m + 2) : Int) ≤ fibAut.evalT ξ fibAut.acceptVec ⟨0, by decide⟩ -
                            fibAut.evalT ξ fibAut.acceptVec ⟨1, by decide⟩)
  | 0, ξ => by
    rw [bv_eq_cons_msb_truncate ξ]
    have htr := bv_eq_cons_msb_truncate (ξ.truncate 1)
    have h00 : (ξ.truncate 1).truncate 0 = 0 := bv_zero_width_eq _
    rw [htr, h00]
    cases ξ.msb <;> cases (ξ.truncate 1).msb <;> decide
  | m + 1, ξ => by
    have ⟨h1, h2, h3, h4, h5⟩ := fibAut_lower_polytope m (ξ.truncate (m + 2))
    have hstep : fibAut.evalT ξ fibAut.acceptVec =
                 fibAut.stepT ξ.msb (fibAut.evalT (ξ.truncate (m + 2)) fibAut.acceptVec) := by
      conv => lhs; unfold BitAutomaton.evalT
    have hF5 : fib (m + 1 + 4) = fib (m + 5) := rfl
    have hF4 : fib (m + 1 + 3) = fib (m + 4) := rfl
    have hF3 : fib (m + 1 + 2) = fib (m + 3) := rfl
    have hF2 : fib (m + 1 + 1) = fib (m + 2) := rfl
    rw [hF5, hF4, hF3, hF2]
    have hf5 : fib (m + 5) = fib (m + 4) + fib (m + 3) := rfl
    have hf3 : fib (m + 3) = fib (m + 2) + fib (m + 1) := rfl
    have hf2 : fib (m + 2) = fib (m + 1) + fib m := rfl
    have hfm : fib m ≤ fib (m + 3) :=
      Nat.le_trans (fib_mono_succ m) (Nat.le_trans (fib_mono_succ (m + 1)) (fib_mono_succ (m + 2)))
    rw [hstep]
    cases ξ.msb
    · have ⟨c0, c1⟩ := fibAut_stepT_false_coords (fibAut.evalT (ξ.truncate (m + 2)) fibAut.acceptVec)
      rw [c0, c1]
      omega
    · have ⟨c0, c1⟩ := fibAut_stepT_true_coords (fibAut.evalT (ξ.truncate (m + 2)) fibAut.acceptVec)
      rw [c0, c1]
      omega

/-- Exact bit-vector `2#k` (`0b0...010`) and `3#k` (`0b0...011`) evaluations for `fibAut`. -/
def fibWitnessMax (k : Nat) : BitVec k := BitVec.ofNat k 2
def fibWitnessMin (k : Nat) : BitVec k := BitVec.ofNat k 3

theorem bv_ofNat_truncate {k : Nat} (n : Nat) :
    (BitVec.ofNat (k + 1) n).truncate k = BitVec.ofNat k n := by
  ext i hi; simp [BitVec.truncate]

theorem bv_ofNat_msb_lt {k : Nat} (n : Nat) (hn : n < 2 ^ k) :
    (BitVec.ofNat (k + 1) n).msb = false := by
  rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_ofNat]
  have hs : k + 1 - 1 = k := by omega
  rw [hs]
  simp only [Nat.lt_add_one, decide_true, Bool.true_and]
  exact Nat.testBit_lt_two_pow hn

theorem fibWitnessMax_ne_zero (k : Nat) (hk : 2 ≤ k) : fibWitnessMax k ≠ 0 := by
  intro hc
  have hnat := congrArg BitVec.toNat hc
  simp [fibWitnessMax] at hnat
  have h2lt : 2 < 2 ^ k := by
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
    omega
  rw [Nat.mod_eq_of_lt h2lt] at hnat
  omega

theorem fibWitnessMin_ne_zero (k : Nat) (hk : 2 ≤ k) : fibWitnessMin k ≠ 0 := by
  intro hc
  have hnat := congrArg BitVec.toNat hc
  simp [fibWitnessMin] at hnat
  have h3lt : 3 < 2 ^ k := by
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
    omega
  rw [Nat.mod_eq_of_lt h3lt] at hnat
  omega

theorem fibAut_evalT_witnessMax : ∀ k : Nat, 2 ≤ k →
    fibAut.evalT (fibWitnessMax k) fibAut.acceptVec ⟨0, by decide⟩ = (lucas (k - 1) : Int) ∧
    fibAut.evalT (fibWitnessMax k) fibAut.acceptVec ⟨1, by decide⟩ =
      if k = 2 then 2 else (lucas (k - 2) : Int)
  | 0, hk => by omega
  | 1, hk => by omega
  | 2, _ => by decide
  | 3, _ => by decide
  | k + 4, _ => by
    have ⟨ih0, ih1⟩ := fibAut_evalT_witnessMax (k + 3) (by omega)
    have hstep : fibAut.evalT (fibWitnessMax (k + 4)) fibAut.acceptVec =
        fibAut.stepT false (fibAut.evalT (fibWitnessMax (k + 3)) fibAut.acceptVec) := by
      conv => lhs; unfold BitAutomaton.evalT
      have hmsb : (fibWitnessMax (k + 4)).msb = false := by
        apply bv_ofNat_msb_lt
        have : 2 ^ 3 ≤ 2 ^ (k + 3) := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      have htr : (fibWitnessMax (k + 4)).truncate (k + 3) = fibWitnessMax (k + 3) :=
        bv_ofNat_truncate 2
      rw [hmsb, htr]
    have ⟨c0, c1⟩ := fibAut_stepT_false_coords (fibAut.evalT (fibWitnessMax (k + 3)) fibAut.acceptVec)
    have hne : k + 3 ≠ 2 := by omega
    simp only [hne, ↓reduceIte] at ih1
    have hne' : k + 4 ≠ 2 := by omega
    simp only [hne', ↓reduceIte]
    have hs1 : k + 4 - 1 = k + 3 := by omega
    have hs2 : k + 4 - 2 = k + 2 := by omega
    have hs3 : k + 3 - 1 = k + 2 := by omega
    have hs4 : k + 3 - 2 = k + 1 := by omega
    rw [hs3] at ih0; rw [hs4] at ih1; rw [hs1, hs2, hstep, c0, c1, ih0, ih1]
    have hl : lucas (k + 3) = lucas (k + 2) + lucas (k + 1) := lucas_add_two (k + 1)
    exact ⟨by omega, rfl⟩

theorem fibAut_evalT_witnessMin : ∀ k : Nat, 2 ≤ k →
    fibAut.evalT (fibWitnessMin k) fibAut.acceptVec ⟨0, by decide⟩ = -(fib (k - 1) : Int) ∧
    fibAut.evalT (fibWitnessMin k) fibAut.acceptVec ⟨1, by decide⟩ = -(fib (k - 2) : Int)
  | 0, hk => by omega
  | 1, hk => by omega
  | 2, _ => by decide
  | k + 3, _ => by
    have ⟨ih0, ih1⟩ := fibAut_evalT_witnessMin (k + 2) (by omega)
    have hstep : fibAut.evalT (fibWitnessMin (k + 3)) fibAut.acceptVec =
        fibAut.stepT false (fibAut.evalT (fibWitnessMin (k + 2)) fibAut.acceptVec) := by
      conv => lhs; unfold BitAutomaton.evalT
      have hmsb : (fibWitnessMin (k + 3)).msb = false := by
        apply bv_ofNat_msb_lt
        have : 2 ^ 2 ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      have htr : (fibWitnessMin (k + 3)).truncate (k + 2) = fibWitnessMin (k + 2) :=
        bv_ofNat_truncate 3
      rw [hmsb, htr]
    have ⟨c0, c1⟩ := fibAut_stepT_false_coords (fibAut.evalT (fibWitnessMin (k + 2)) fibAut.acceptVec)
    have hs1 : k + 3 - 1 = k + 2 := by omega
    have hs2 : k + 3 - 2 = k + 1 := by omega
    have hs3 : k + 2 - 1 = k + 1 := by omega
    have hs4 : k + 2 - 2 = k := by omega
    rw [hs3] at ih0; rw [hs4] at ih1; rw [hs1, hs2, hstep, c0, c1, ih0, ih1]
    have hf : fib (k + 2) = fib (k + 1) + fib k := rfl
    exact ⟨by omega, rfl⟩

theorem fibPred_deg (k : Nat) :
    graphDeg (fibPred (k := k)) = (fib (k + 2) : Int) - 1 := by
  have hcongr : graphDeg (fibPred (k := k)) = graphDeg (fibAut.looplessPred (k := k)) := by
    unfold graphDeg indBool
    apply bvSum_congr; intro x; rw [fibAut_looplessPred_eq]
  rw [hcongr, graphDeg_automaton_loopless, fibAut_accepts_eq]
  change fibAut.evalT (0 : BitVec k) fibAut.acceptVec ⟨0, by decide⟩ -
         (if ((0 : BitVec k) &&& ((0 : BitVec k) >>> 1) == 0) = true then 1 else 0) = _
  rw [(fibAut_evalT_zero k).1]
  simp

/-- **THEOREM B.2 (Exact Tight Two-Sided Spectral Radius & Integer Expander Mixing Lemma for `G_fib`, ∀ k ≥ 3):** -/
theorem fib_two_sided_bound {k : Nat} (hk : 3 ≤ k) (ξ : BitVec k) (hne : ξ ≠ 0) :
    -((lucas (k - 1) : Int) - 1) ≤ graphEig fibPred ξ ∧
    graphEig fibPred ξ ≤ (lucas (k - 1) : Int) - 1 := by
  have hcongrEig : graphEig fibPred ξ = graphEig fibAut.looplessPred ξ := by
    unfold graphEig wht indBool
    apply bvSum_congr; intro x; rw [fibAut_looplessPred_eq]
  rw [hcongrEig, graphEig_automaton_loopless, fibAut_accepts_eq]
  have h0 : ((0 : BitVec k) &&& ((0 : BitVec k) >>> 1) == 0) = true := by simp
  rw [h0]
  simp only [↓reduceIte]
  cases k with
  | zero => omega
  | succ k1 =>
    cases k1 with
    | zero => omega
    | succ m =>
      have hhi : fibAut.evalT ξ fibAut.acceptVec fibAut.init ≤ (lucas (m + 1) : Int) :=
        (fibAut_lucas_cone m ξ hne).2.1
      have hlo : -(fib (m + 1) : Int) ≤ fibAut.evalT ξ fibAut.acceptVec fibAut.init :=
        (fibAut_lower_polytope m ξ).2.2.1
      have hsep := lucas_sub_fib_ge_two (m + 2) hk
      have hs : m + 1 + 1 - 1 = m + 1 := by omega
      have hs2 : m + 2 - 1 = m + 1 := by omega
      rw [hs2] at hsep
      rw [hs]
      omega

/-- Append bit `b` at the LSB of `x : BitVec k` (pure `BitVec.cons` recursion). -/
def bvSnoc : {k : Nat} → BitVec k → Bool → BitVec (k + 1)
  | 0, _, b => BitVec.cons b 0
  | k + 1, x, b => BitVec.cons x.msb (bvSnoc (x.truncate k) b)

/-- Cyclic 1-bit left rotation on `BitVec k` defined via `bvSnoc`. -/
def rotl1 : {k : Nat} → BitVec k → BitVec k
  | 0, x => x
  | k + 1, x => bvSnoc (x.truncate k) x.msb

theorem bvSnoc_getElem_zero {k : Nat} (x : BitVec k) (b : Bool) :
    (bvSnoc x b)[0] = b := by
  induction k with
  | zero => simp [bvSnoc, BitVec.getElem_cons]
  | succ k ih =>
    unfold bvSnoc
    simp [BitVec.getElem_cons, ih]

theorem bvSnoc_getElem_succ {k : Nat} (x : BitVec k) (b : Bool) (i : Nat) (hi : i < k) :
    (bvSnoc x b)[i + 1]'(by omega) = x[i] := by
  induction k with
  | zero => omega
  | succ k ih =>
    unfold bvSnoc
    by_cases he : i = k
    · subst he
      simp [BitVec.getElem_cons, BitVec.msb_eq_getLsbD_last]
    · have hlt : i < k := by omega
      have hne : i + 1 ≠ k + 1 := by omega
      simp only [BitVec.getElem_cons, hne, ↓reduceDIte]
      rw [ih (x.truncate k) hlt]
      simp only [BitVec.truncate, BitVec.getElem_setWidth]
      exact BitVec.getLsbD_eq_getElem hi

theorem rotl1_cons {k : Nat} (b : Bool) (x : BitVec k) :
    rotl1 (BitVec.cons b x) = bvSnoc x b := by
  simp only [rotl1, bv_cons_msb, bv_cons_truncate]

theorem rotl1_eq_rotateLeft {k : Nat} (x : BitVec k) :
    rotl1 x = x.rotateLeft 1 := by
  cases k with
  | zero => exact (bv_zero_width_eq _).trans (bv_zero_width_eq _).symm
  | succ k =>
    ext i hi
    unfold rotl1
    cases i with
    | zero =>
      rw [bvSnoc_getElem_zero]
      simp only [BitVec.getElem_rotateLeft, BitVec.msb_eq_getLsbD_last]
      cases k with
      | zero => simp
      | succ m =>
        have h1 : 1 % (m + 2) = 1 := Nat.mod_eq_of_lt (by omega)
        simp [h1]
    | succ j =>
      have hj : j < k := by omega
      rw [bvSnoc_getElem_succ _ _ j hj]
      simp only [BitVec.getElem_rotateLeft, BitVec.truncate, BitVec.getElem_setWidth]
      cases k with
      | zero => omega
      | succ m =>
        have h1 : 1 % (m + 2) = 1 := Nat.mod_eq_of_lt (by omega)
        simp only [h1]
        have hlt : ¬ (j + 1 < 1) := by omega
        simp only [hlt, ↓reduceDIte, Nat.add_sub_cancel]
        exact BitVec.getLsbD_eq_getElem (by omega)

theorem bvSum_snoc {k : Nat} (f : BitVec (k + 1) → Int) :
    bvSum f = bvSum (fun x : BitVec k => f (bvSnoc x false)) +
              bvSum (fun x : BitVec k => f (bvSnoc x true)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    conv => lhs; unfold bvSum
    have h0 := ih (fun x : BitVec (k + 1) => f (BitVec.cons false x))
    have h1 := ih (fun x : BitVec (k + 1) => f (BitVec.cons true x))
    have hf0 : ∀ x : BitVec k, bvSnoc (BitVec.cons false x) false = BitVec.cons false (bvSnoc x false) := by
      intro x; conv => lhs; unfold bvSnoc
      rw [bv_cons_msb, bv_cons_truncate]
    have ht0 : ∀ x : BitVec k, bvSnoc (BitVec.cons true x) false = BitVec.cons true (bvSnoc x false) := by
      intro x; conv => lhs; unfold bvSnoc
      rw [bv_cons_msb, bv_cons_truncate]
    have hf1 : ∀ x : BitVec k, bvSnoc (BitVec.cons false x) true = BitVec.cons false (bvSnoc x true) := by
      intro x; conv => lhs; unfold bvSnoc
      rw [bv_cons_msb, bv_cons_truncate]
    have ht1 : ∀ x : BitVec k, bvSnoc (BitVec.cons true x) true = BitVec.cons true (bvSnoc x true) := by
      intro x; conv => lhs; unfold bvSnoc
      rw [bv_cons_msb, bv_cons_truncate]
    have r1 : bvSum (fun x : BitVec (k + 1) => f (bvSnoc x false)) =
              bvSum (fun x : BitVec k => f (BitVec.cons false (bvSnoc x false))) +
              bvSum (fun x : BitVec k => f (BitVec.cons true (bvSnoc x false))) := by
      conv => lhs; unfold bvSum
      have a := bvSum_congr (fun x : BitVec k => show f (bvSnoc (BitVec.cons false x) false) = f (BitVec.cons false (bvSnoc x false)) by rw [hf0])
      have b := bvSum_congr (fun x : BitVec k => show f (bvSnoc (BitVec.cons true x) false) = f (BitVec.cons true (bvSnoc x false)) by rw [ht0])
      rw [a, b]
    have r2 : bvSum (fun x : BitVec (k + 1) => f (bvSnoc x true)) =
              bvSum (fun x : BitVec k => f (BitVec.cons false (bvSnoc x true))) +
              bvSum (fun x : BitVec k => f (BitVec.cons true (bvSnoc x true))) := by
      conv => lhs; unfold bvSum
      have a := bvSum_congr (fun x : BitVec k => show f (bvSnoc (BitVec.cons false x) true) = f (BitVec.cons false (bvSnoc x true)) by rw [hf1])
      have b := bvSum_congr (fun x : BitVec k => show f (bvSnoc (BitVec.cons true x) true) = f (BitVec.cons true (bvSnoc x true)) by rw [ht1])
      rw [a, b]
    rw [h0, h1, r1, r2]
    omega

theorem bvSum_rotl1 {k : Nat} (f : BitVec k → Int) :
    bvSum (fun x => f (rotl1 x)) = bvSum f := by
  cases k with
  | zero => rfl
  | succ k =>
    conv => lhs; unfold bvSum
    have e0 : bvSum (fun x : BitVec k => f (rotl1 (BitVec.cons false x))) =
              bvSum (fun x : BitVec k => f (bvSnoc x false)) :=
      bvSum_congr (fun x => by rw [rotl1_cons])
    have e1 : bvSum (fun x : BitVec k => f (rotl1 (BitVec.cons true x))) =
              bvSum (fun x : BitVec k => f (bvSnoc x true)) :=
      bvSum_congr (fun x => by rw [rotl1_cons])
    rw [e0, e1]
    exact (bvSum_snoc f).symm

theorem chi_snoc {k : Nat} (a b : Bool) (ξ x : BitVec k) :
    chi (bvSnoc ξ a) (bvSnoc x b) = sgn (a && b) * chi ξ x := by
  induction k with
  | zero =>
    simp [bvSnoc, chi]
  | succ k ih =>
    conv => lhs; unfold bvSnoc
    rw [chi_cons, ih]
    conv => rhs; arg 2; unfold chi
    ac_rfl

theorem chi_rotl1 {k : Nat} (ξ x : BitVec k) :
    chi (rotl1 ξ) (rotl1 x) = chi ξ x := by
  cases k with
  | zero => rfl
  | succ k =>
    unfold rotl1
    rw [chi_snoc]
    conv => rhs; unfold chi

theorem rotl1_and {k : Nat} (x y : BitVec k) :
    rotl1 (x &&& y) = rotl1 x &&& rotl1 y := by
  rw [rotl1_eq_rotateLeft, rotl1_eq_rotateLeft, rotl1_eq_rotateLeft]
  ext i hi
  simp only [BitVec.getElem_rotateLeft, BitVec.getElem_and]
  split <;> rfl

theorem rotl1_zero {k : Nat} : rotl1 (0 : BitVec k) = 0 := by
  rw [rotl1_eq_rotateLeft]
  ext i hi
  simp [BitVec.getElem_rotateLeft]

theorem rotl1_eq_zero_iff {k : Nat} (x : BitVec k) : rotl1 x = 0 ↔ x = 0 := by
  constructor
  · intro h
    cases k with
    | zero => exact bv_zero_width_eq x
    | succ k =>
      ext i hi
      have h0bit : (0 : BitVec (k + 1))[i]'hi = false := by simp
      rw [h0bit]
      by_cases hk : i = k
      · subst hk
        have h0 := congrArg (fun v : BitVec (i + 1) => v[0]) h
        unfold rotl1 at h0
        rw [bvSnoc_getElem_zero] at h0
        simp [BitVec.msb_eq_getLsbD_last] at h0
        exact h0
      · have hlt : i < k := by omega
        have h1 := congrArg (fun v : BitVec (k + 1) => v[i + 1]'(by omega)) h
        unfold rotl1 at h1
        rw [bvSnoc_getElem_succ _ _ i hlt] at h1
        simp [BitVec.truncate] at h1
        exact h1
  · intro h; subst h; exact rotl1_zero

/-- Explicit bitwise Circular Fibbinary predicate: `x ≠ 0 ∧ (x &&& rotl1 x) = 0`. -/
def cfibAccepts {k : Nat} (x : BitVec k) : Bool :=
  (x &&& rotl1 x) == 0

def cfibPred {k : Nat} (x : BitVec k) : Bool :=
  x != 0 && cfibAccepts x

theorem cfibAccepts_rotl1 {k : Nat} (x : BitVec k) :
    cfibAccepts (rotl1 x) = cfibAccepts x := by
  unfold cfibAccepts
  rw [← rotl1_and]
  by_cases h : (x &&& rotl1 x) = 0
  · rw [h, rotl1_zero]
  · have h' : rotl1 (x &&& rotl1 x) ≠ 0 := by
      intro hc; exact h ((rotl1_eq_zero_iff _).mp hc)
    rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr h']

theorem wht_cfibAccepts_rotl1 {k : Nat} (ξ : BitVec k) :
    wht (indBool cfibAccepts) (rotl1 ξ) = wht (indBool cfibAccepts) ξ := by
  unfold wht
  rw [← bvSum_rotl1 (fun x => chi (rotl1 ξ) x * indBool cfibAccepts x)]
  apply bvSum_congr
  intro x
  rw [chi_rotl1]
  unfold indBool
  rw [cfibAccepts_rotl1]

/-- Iterated rotation reaches `msb = true` from ANY non-zero `ξ : BitVec (k + 1)`. -/
def rotlIter {k : Nat} : Nat → BitVec k → BitVec k
  | 0, x => x
  | r + 1, x => rotl1 (rotlIter r x)

theorem wht_cfibAccepts_rotlIter {k : Nat} (r : Nat) (ξ : BitVec k) :
    wht (indBool cfibAccepts) (rotlIter r ξ) = wht (indBool cfibAccepts) ξ := by
  induction r with
  | zero => rfl
  | succ r ih => unfold rotlIter; rw [wht_cfibAccepts_rotl1, ih]

theorem rotlIter_getElem_msb {k : Nat} (ξ : BitVec (k + 1)) (j : Nat) (hj : j ≤ k) :
    (rotlIter (k - j) ξ).msb = ξ[j]'(by omega) := by
  have hgen : ∀ (r i : Nat) (hri : r + i ≤ k),
      (rotlIter r ξ)[r + i]'(by omega) = ξ[i]'(by omega) := by
    intro r
    induction r with
    | zero => intro i _; simp [rotlIter]
    | succ r ih =>
      intro i hle
      unfold rotlIter rotl1
      have hlt : r + i < k := by omega
      have hidx : (r + 1) + i = (r + i) + 1 := by omega
      have h1 : (bvSnoc ((rotlIter r ξ).truncate k) (rotlIter r ξ).msb)[(r + 1) + i]'(by omega) =
                (bvSnoc ((rotlIter r ξ).truncate k) (rotlIter r ξ).msb)[(r + i) + 1]'(by omega) := by
        simp [hidx]
      rw [h1, bvSnoc_getElem_succ _ _ (r + i) hlt]
      simp only [BitVec.truncate, BitVec.getElem_setWidth]
      exact ih i (by omega)
  rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_eq_getElem (by omega)]
  have h := hgen (k - j) j (by omega)
  have heq : k - j + j = k := by omega
  have hsub : k + 1 - 1 = k := by omega
  have h2 : (rotlIter (k - j) ξ)[k + 1 - 1] = (rotlIter (k - j) ξ)[k - j + j]'(by omega) := by
    simp [hsub, heq]
  rw [h2, h]

theorem exists_rotl_msb_true {k : Nat} (ξ : BitVec (k + 1)) (hne : ξ ≠ 0) :
    ∃ r : Nat, (rotlIter r ξ).msb = true := by
  have hex : ∃ i : Nat, ∃ hi : i < k + 1, ξ[i]'hi = true := by
    suffices ∀ m : Nat, (hm : m ≤ k + 1) →
        (∀ i : Nat, (hi : i < m) → ξ[i]'(by omega) = false) ∨
        (∃ i : Nat, ∃ hi : i < m, ξ[i]'(by omega) = true) by
      rcases this (k + 1) (Nat.le_refl _) with hall | ⟨i, hi, ht⟩
      · exfalso; apply hne; ext i hi; simp [hall i hi]
      · exact ⟨i, hi, ht⟩
    intro m
    induction m with
    | zero => intro _; left; intro i hi; omega
    | succ m ih =>
      intro hm
      rcases ih (by omega) with hall | ⟨i, hi, ht⟩
      · cases hmbit : ξ[m]'(by omega)
        · left; intro i hi
          by_cases he : i = m
          · subst he; exact hmbit
          · exact hall i (by omega)
        · right; exact ⟨m, by omega, hmbit⟩
      · right; exact ⟨i, by omega, ht⟩
  rcases hex with ⟨j, hj, htrue⟩
  exact ⟨k - j, by rw [rotlIter_getElem_msb ξ j (by omega)]; exact htrue⟩

/-- Characterization of `cfibAccepts` on `BitVec (k + 1)` (`k ≥ 1`):
    `cfibAccepts (cons false x) = fibAut.accepts x` and
    `cfibAccepts (cons true x)` iff `fibAut.run 1 x = some 0`! -/
theorem cfibAccepts_eq_fib_and_ends {k : Nat} (hk : 1 ≤ k) (b : Bool) (x : BitVec k) :
    (BitVec.cons b x &&& rotl1 (BitVec.cons b x)) = 0 ↔
    ((BitVec.cons b x &&& (BitVec.cons b x >>> 1)) = 0 ∧ (b = true → x[0]'(by omega) = false)) := by
  rw [rotl1_cons]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · ext i hi
      simp only [BitVec.getElem_and, BitVec.getElem_ushiftRight, bv_getLsbD_shift1]
      have h01 : (0 : BitVec (k + 1))[i]'hi = false := by simp
      rw [h01]
      by_cases hlt : i + 1 < k + 1
      · simp only [hlt, ↓reduceDIte]
        have hget := congrArg (fun v : BitVec (k + 1) => v[i + 1]'hlt) h
        simp only [BitVec.getElem_and] at hget
        have h02 : (0 : BitVec (k + 1))[i + 1]'hlt = false := by simp
        rw [h02] at hget
        have hsn : (bvSnoc x b)[i + 1]'hlt = x[i]'(by omega) := bvSnoc_getElem_succ x b i (by omega)
        have hc1 : (BitVec.cons b x)[i]'hi = x[i]'(by omega) := by
          simp [BitVec.getElem_cons, show i ≠ k by omega]
        rw [hsn] at hget
        rw [hc1, Bool.and_comm]
        exact hget
      · simp [hlt]
    · intro hb
      have hget := congrArg (fun v : BitVec (k + 1) => v[0]) h
      simp only [BitVec.getElem_and] at hget
      have h00 : (0 : BitVec (k + 1))[0] = false := by simp
      rw [bvSnoc_getElem_zero, h00] at hget
      have hc0 : (BitVec.cons b x)[0] = x[0]'(by omega) := by
        simp [BitVec.getElem_cons, show (0 : Nat) ≠ k by omega]
      rw [hc0, hb, Bool.and_true] at hget
      exact hget
  · rintro ⟨hlin, hend⟩
    ext i hi
    simp only [BitVec.getElem_and]
    have h01 : (0 : BitVec (k + 1))[i]'hi = false := by simp
    rw [h01]
    cases i with
    | zero =>
      rw [bvSnoc_getElem_zero]
      have hc0 : (BitVec.cons b x)[0] = x[0]'(by omega) := by
        simp [BitVec.getElem_cons, show (0 : Nat) ≠ k by omega]
      rw [hc0]
      cases b
      · simp
      · rw [hend rfl]; simp
    | succ j =>
      have hj : j < k := by omega
      rw [bvSnoc_getElem_succ x b j hj]
      have hget := congrArg (fun v : BitVec (k + 1) => v[j]'(by omega)) hlin
      simp only [BitVec.getElem_and, BitVec.getElem_ushiftRight, bv_getLsbD_shift1,
                 hi, ↓reduceDIte] at hget
      have h02 : (0 : BitVec (k + 1))[j]'(by omega) = false := by simp
      rw [h02] at hget
      have hc1 : (BitVec.cons b x)[j]'(by omega) = x[j]'hj := by
        simp [BitVec.getElem_cons, Nat.ne_of_lt hj]
      rw [hc1] at hget
      rw [Bool.and_comm]
      exact hget

theorem fibAut_run_eq_some0_iff : ∀ {k : Nat} (hk : 1 ≤ k) (q : Fin 2) (x : BitVec k),
    fibAut.run q x = some ⟨0, by decide⟩ ↔
    ((fibAut.run q x).isSome = true ∧ x[0]'(by omega) = false)
  | 0, hk, _, _ => by omega
  | 1, _, q, x => by
    rw [bv_eq_cons_msb_truncate x]
    have h0 : x.truncate 0 = 0 := bv_zero_width_eq _
    rw [h0, BitAutomaton.run_cons]
    have hb0 : (BitVec.cons x.msb (0 : BitVec 0))[0] = x.msb := by simp [BitVec.getElem_cons]
    rw [hb0]
    have hq : q = ⟨0, by decide⟩ ∨ q = ⟨1, by decide⟩ := by
      cases q with
      | mk v hv =>
        have : v = 0 ∨ v = 1 := by omega
        rcases this with rfl | rfl
        · left; rfl
        · right; rfl
    rcases hq with rfl | rfl <;> cases x.msb <;> decide
  | k + 2, _, q, x => by
    rw [bv_eq_cons_msb_truncate x, BitAutomaton.run_cons]
    have hb0 : (BitVec.cons x.msb (x.truncate (k + 1)))[0] = (x.truncate (k + 1))[0] := by
      simp
    rw [hb0]
    cases hd : fibAut.delta q x.msb with
    | none => simp
    | some q' => exact fibAut_run_eq_some0_iff (by omega) q' (x.truncate (k + 1))

/-- 2-state Fibbinary automaton with restricted acceptance `{0}` (last bit must be `0`). -/
def fibAutEnd0 : BitAutomaton 2 where
  init := ⟨1, by decide⟩
  delta := fibAut.delta
  accept := fun q => q.val == 0

theorem fibAutEnd0_run_eq {k : Nat} (q : Fin 2) (x : BitVec k) :
    fibAutEnd0.run q x = fibAut.run q x := by
  induction k generalizing q with
  | zero => rfl
  | succ k ih =>
    conv => lhs; unfold BitAutomaton.run
    conv => rhs; unfold BitAutomaton.run
    have hd : fibAutEnd0.delta q x.msb = fibAut.delta q x.msb := rfl
    rw [hd]
    cases fibAut.delta q x.msb with
    | none => rfl
    | some q' => exact ih q' (x.truncate k)

/-- Exact cyclic-split formula for Circular Fibbinary Walsh coefficients! -/
theorem wht_cfibAccepts_split {k : Nat} (hk : 1 ≤ k) (b : Bool) (η : BitVec k) :
    wht (indBool cfibAccepts) (BitVec.cons b η) =
    fibAut.evalT η fibAut.acceptVec ⟨0, by decide⟩ +
    sgn b * fibAutEnd0.evalT η fibAutEnd0.acceptVec ⟨1, by decide⟩ := by
  unfold wht
  simp only [bvSum, chi_cons, Bool.and_false, Bool.and_true, sgn_false, Int.one_mul]
  have hfalse : bvSum (fun x : BitVec k => chi η x * indBool cfibAccepts (BitVec.cons false x)) =
                fibAut.evalT η fibAut.acceptVec ⟨0, by decide⟩ := by
    rw [← wht_automaton_from_state fibAut η ⟨0, by decide⟩]
    apply bvSum_congr
    intro x
    congr 1
    unfold indBool cfibAccepts
    have hiff := cfibAccepts_eq_fib_and_ends hk false x
    have hlin := bv_cons_and_shr1_eq_zero_iff false x
    have hrun := (fibAut_run_isSome_iff x).1
    cases hr : fibAut.run ⟨0, by decide⟩ x with
    | none =>
      have hne : (BitVec.cons false x &&& rotl1 (BitVec.cons false x)) ≠ 0 := by
        intro hc
        have h1 := (hiff.mp hc).1
        have h2 := (hlin.mp h1).2
        have hs := hrun.mpr h2
        rw [hr] at hs; simp at hs
      rw [beq_eq_false_iff_ne.mpr hne]; rfl
    | some q =>
      have hs : (fibAut.run ⟨0, by decide⟩ x).isSome = true := by rw [hr]; rfl
      have h2 := hrun.mp hs
      have h1 : (BitVec.cons false x &&& (BitVec.cons false x >>> 1)) = 0 :=
        hlin.mpr ⟨fun hc => Bool.noConfusion hc, h2⟩
      have hc : (BitVec.cons false x &&& rotl1 (BitVec.cons false x)) = 0 :=
        hiff.mpr ⟨h1, fun hc => Bool.noConfusion hc⟩
      simp [optVal, fibAut, BitAutomaton.acceptVec, hc]
  have htrue : bvSum (fun x : BitVec k => sgn b * chi η x * indBool cfibAccepts (BitVec.cons true x)) =
               sgn b * fibAutEnd0.evalT η fibAutEnd0.acceptVec ⟨1, by decide⟩ := by
    have hre : ∀ x : BitVec k, sgn b * chi η x * indBool cfibAccepts (BitVec.cons true x) =
               sgn b * (chi η x * indBool cfibAccepts (BitVec.cons true x)) :=
      fun x => Int.mul_assoc _ _ _
    rw [bvSum_congr hre, bvSum_mul_left, ← wht_automaton_from_state fibAutEnd0 η ⟨1, by decide⟩]
    congr 1
    apply bvSum_congr
    intro x
    congr 1
    unfold indBool cfibAccepts
    rw [fibAutEnd0_run_eq]
    have hiff := cfibAccepts_eq_fib_and_ends hk true x
    have hlin := bv_cons_and_shr1_eq_zero_iff true x
    have hrun1 := (fibAut_run_isSome_iff x).2
    have hsome0 := fibAut_run_eq_some0_iff hk ⟨1, by decide⟩ x
    by_cases hc : (BitVec.cons true x &&& rotl1 (BitVec.cons true x)) = 0
    · have ⟨hl, he⟩ := hiff.mp hc
      have hpair := hlin.mp hl
      have hs : (fibAut.run ⟨1, by decide⟩ x).isSome = true := hrun1.mpr ⟨hpair.1 rfl, hpair.2⟩
      have hr0 : fibAut.run ⟨1, by decide⟩ x = some ⟨0, by decide⟩ := hsome0.mpr ⟨hs, he rfl⟩
      rw [hr0]; simp [hc, optVal, fibAutEnd0, BitAutomaton.acceptVec]
    · have hnr0 : fibAut.run ⟨1, by decide⟩ x ≠ some ⟨0, by decide⟩ := by
        intro hr0
        have ⟨hs, he⟩ := hsome0.mp hr0
        have ⟨hcross, hrest⟩ := hrun1.mp hs
        have hl : (BitVec.cons true x &&& (BitVec.cons true x >>> 1)) = 0 :=
          hlin.mpr ⟨fun _ => hcross, hrest⟩
        exact hc (hiff.mpr ⟨hl, fun _ => he⟩)
      simp only [beq_eq_false_iff_ne.mpr hc, Bool.false_eq_true, ↓reduceIte]
      cases hr : fibAut.run ⟨1, by decide⟩ x with
      | none => rfl
      | some q =>
        have hqne : q.val ≠ 0 := by
          intro hq0; apply hnr0; rw [hr]; congr 1; exact Fin.ext hq0
        simp [optVal, BitAutomaton.acceptVec, fibAutEnd0, beq_eq_false_iff_ne.mpr hqne]
  rw [hfalse, htrue]

/-- Every `(m+1)`-bit vector decomposes as `bvSnoc x b` (stripping its LSB). -/
theorem exists_bvSnoc : ∀ {m : Nat} (η : BitVec (m + 1)),
    ∃ (x : BitVec m) (b : Bool), η = bvSnoc x b
  | 0, η => by
    refine ⟨0, η.msb, ?_⟩
    conv => lhs; rw [bv_eq_cons_msb_truncate η]
    have h0 : η.truncate 0 = 0 := bv_zero_width_eq _
    rw [h0]; rfl
  | m + 1, η => by
    obtain ⟨x, b, hx⟩ := exists_bvSnoc (η.truncate (m + 1))
    refine ⟨BitVec.cons η.msb x, b, ?_⟩
    conv => rhs; unfold bvSnoc
    rw [bv_cons_msb, bv_cons_truncate, ← hx]
    exact bv_eq_cons_msb_truncate η

/-- After 1 step on LSB `b`, `fibAutEnd0.evalT (bvSnoc x b) (1, 0) = fibAut.evalT x (1, 1)`. -/
theorem fibAutEnd0_evalT_snoc : ∀ {m : Nat} (x : BitVec m) (b : Bool),
    fibAutEnd0.evalT (bvSnoc x b) fibAutEnd0.acceptVec =
    fibAut.evalT x fibAut.acceptVec
  | 0, x, b => by
    have hx : x = 0 := bv_zero_width_eq x
    subst hx
    funext q
    have hq : q = ⟨0, by decide⟩ ∨ q = ⟨1, by decide⟩ := by
      cases q with
      | mk v hv =>
        have : v = 0 ∨ v = 1 := by omega
        rcases this with rfl | rfl
        · left; rfl
        · right; rfl
    rcases hq with rfl | rfl <;> cases b <;> decide
  | m + 1, x, b => by
    have ih := fibAutEnd0_evalT_snoc (x.truncate m) b
    conv => lhs; unfold bvSnoc BitAutomaton.evalT
    rw [bv_cons_msb, bv_cons_truncate, ih]
    rfl

theorem fibAutEnd0_evalT_zero (m : Nat) :
    fibAutEnd0.evalT (0 : BitVec (m + 1)) fibAutEnd0.acceptVec ⟨1, by decide⟩ = (fib (m + 1) : Int) := by
  have h0 : (0 : BitVec (m + 1)) = bvSnoc (0 : BitVec m) false := by
    induction m with
    | zero => decide
    | succ r ih =>
      conv => rhs; unfold bvSnoc
      rw [bv_zero_msb, bv_zero_truncate, ← ih]
      exact bv_cons_zero
  rw [h0, fibAutEnd0_evalT_snoc]
  exact (fibAut_evalT_zero m).2

/-- Exact lower bound on `fibAutEnd0.evalT η 1` for ALL `η : BitVec (m + 3)`:
    `evalT η 1 ≥ -F_m` (derived directly from our 5-inequality Fibonacci polytope!). -/
theorem fibAutEnd0_evalT_lower_bound (m : Nat) (η : BitVec (m + 3)) :
    -(fib m : Int) ≤ fibAutEnd0.evalT η fibAutEnd0.acceptVec ⟨1, by decide⟩ := by
  obtain ⟨x, b, rfl⟩ := exists_bvSnoc η
  rw [fibAutEnd0_evalT_snoc]
  exact (fibAut_lower_polytope m x).2.2.2.1

/-- Exact upper bound on `wht (indBool cfibAccepts) ξ ≤ F_k` for ALL `k ≥ 3` and ALL `ξ ≠ 0`! -/
theorem cfibAccepts_wht_upper : ∀ {k : Nat}, 3 ≤ k → ∀ (ξ : BitVec k),
    ξ ≠ 0 → wht (indBool cfibAccepts) ξ ≤ (fib k : Int) := by
  intro k hk ξ hne
  cases k with
  | zero => omega
  | succ k1 =>
    obtain ⟨r, hr⟩ := exists_rotl_msb_true ξ hne
    rw [← wht_cfibAccepts_rotlIter r ξ]
    rw [bv_eq_cons_msb_truncate (rotlIter r ξ), hr, wht_cfibAccepts_split (by omega)]
    simp only [sgn_true]
    have hneg : -1 * fibAutEnd0.evalT ((rotlIter r ξ).truncate k1) fibAutEnd0.acceptVec ⟨1, by decide⟩ =
                -fibAutEnd0.evalT ((rotlIter r ξ).truncate k1) fibAutEnd0.acceptVec ⟨1, by decide⟩ :=
      Int.neg_one_mul _
    rw [hneg]
    cases k1 with
    | zero => omega
    | succ k2 =>
      cases k2 with
      | zero => omega
      | succ m =>
        by_cases ht0 : (rotlIter r ξ).truncate (m + 2) = 0
        · rw [ht0, (fibAut_evalT_zero (m + 2)).1, fibAutEnd0_evalT_zero (m + 1)]
          have hf4 : fib (m + 2 + 2) = fib (m + 3) + fib (m + 2) := rfl
          have hf3 : fib (m + 1 + 1 + 1) = fib (m + 3) := rfl
          have hf2 : fib (m + 1 + 1) = fib (m + 2) := rfl
          rw [hf4, hf3, hf2]
          omega
        · have hup : fibAut.evalT ((rotlIter r ξ).truncate (m + 2)) fibAut.acceptVec ⟨0, by decide⟩ ≤
                     (lucas (m + 1) : Int) :=
            (fibAut_lucas_cone m ((rotlIter r ξ).truncate (m + 2)) ht0).2.1
          cases m with
          | zero =>
            obtain ⟨x, b, hx⟩ := exists_bvSnoc ((rotlIter r ξ).truncate 2)
            rw [hx] at hup ⊢
            rw [fibAutEnd0_evalT_snoc]
            have hx1 : fibAut.evalT x fibAut.acceptVec ⟨1, by decide⟩ = 1 := by
              rw [bv_eq_cons_msb_truncate x]
              have h0 : x.truncate 0 = 0 := bv_zero_width_eq _
              rw [h0]; cases x.msb <;> decide
            rw [hx1]
            have hl1 : lucas (0 + 1) = 1 := rfl
            have hf3 : fib (0 + 1 + 1 + 1) = 2 := rfl
            rw [hl1] at hup; rw [hf3]
            omega
          | succ m' =>
            have hup' : fibAut.evalT ((rotlIter r ξ).truncate (m' + 1 + 1 + 1)) fibAut.acceptVec ⟨0, by decide⟩ ≤
                        (lucas (m' + 2) : Int) := hup
            have hlo' : -(fib m' : Int) ≤
                fibAutEnd0.evalT ((rotlIter r ξ).truncate (m' + 1 + 1 + 1)) fibAutEnd0.acceptVec ⟨1, by decide⟩ :=
              fibAutEnd0_evalT_lower_bound m' ((rotlIter r ξ).truncate (m' + 3))
            have hsum : lucas (m' + 2) + fib m' = fib (m' + 4) := by
              have hl2 : lucas (m' + 2) = fib (m' + 1) + fib (m' + 3) := rfl
              have hf4 : fib (m' + 4) = fib (m' + 3) + fib (m' + 2) := rfl
              have hf2 : fib (m' + 2) = fib (m' + 1) + fib m' := rfl
              omega
            have hf4 : fib (m' + 1 + 1 + 1 + 1) = fib (m' + 4) := rfl
            rw [hf4]
            omega

theorem cfibAccepts_wht_zero (k : Nat) (hk : 2 ≤ k) :
    wht (indBool cfibAccepts) (0 : BitVec k) = (lucas k : Int) := by
  cases k with
  | zero => omega
  | succ k1 =>
    cases k1 with
    | zero => omega
    | succ m =>
      rw [bv_cons_zero, wht_cfibAccepts_split (by omega)]
      simp only [sgn_false, Int.one_mul]
      rw [(fibAut_evalT_zero (m + 1)).1, fibAutEnd0_evalT_zero m]
      have he : m + 1 + 1 = m + 2 := rfl
      rw [he, lucas_succ (m + 1)]
      have he2 : m + 1 + 2 = m + 3 := rfl
      rw [he2]
      omega

/-- Witness `cfibWitness k = BitVec.cons true (0 : BitVec (k-1))` (MSB = 1, all other bits = 0). -/
def cfibWitness (k : Nat) (hk : 1 ≤ k) : BitVec k :=
  match k, hk with
  | k' + 1, _ => BitVec.cons true (0 : BitVec k')

theorem cfibWitness_ne_zero (k : Nat) (hk : 1 ≤ k) : cfibWitness k hk ≠ 0 := by
  cases k with
  | zero => omega
  | succ k' =>
    intro hc
    have := (bv_cons_eq_zero_iff true (0 : BitVec k')).mp hc
    exact Bool.noConfusion this.1

theorem cfibAccepts_wht_witness (k : Nat) (hk : 2 ≤ k) :
    wht (indBool cfibAccepts) (cfibWitness k (by omega)) = (fib k : Int) := by
  cases k with
  | zero => omega
  | succ k1 =>
    cases k1 with
    | zero => omega
    | succ m =>
      unfold cfibWitness
      rw [wht_cfibAccepts_split (by omega)]
      simp only [sgn_true]
      have hneg : -1 * fibAutEnd0.evalT (0 : BitVec (m + 1)) fibAutEnd0.acceptVec ⟨1, by decide⟩ =
                  -fibAutEnd0.evalT (0 : BitVec (m + 1)) fibAutEnd0.acceptVec ⟨1, by decide⟩ :=
        Int.neg_one_mul _
      rw [hneg, (fibAut_evalT_zero (m + 1)).1, fibAutEnd0_evalT_zero m]
      have hf3 : fib (m + 1 + 2) = fib (m + 2) + fib (m + 1) := rfl
      have hf2 : fib (m + 1 + 1) = fib (m + 2) := rfl
      rw [hf3, hf2]
      omega

theorem graphEig_cfibPred {k : Nat} (ξ : BitVec k) :
    graphEig cfibPred ξ = wht (indBool cfibAccepts) ξ - 1 := by
  unfold graphEig wht
  rw [bvSum_split_zero (fun x => chi ξ x * indBool cfibPred x),
      bvSum_split_zero (fun x => chi ξ x * indBool cfibAccepts x)]
  have hrem : bvSum (fun x : BitVec k => if x = 0 then 0 else chi ξ x * indBool cfibPred x) =
              bvSum (fun x : BitVec k => if x = 0 then 0 else chi ξ x * indBool cfibAccepts x) := by
    apply bvSum_congr; intro x
    by_cases hx : x = 0
    · simp [hx]
    · have hp : cfibPred x = cfibAccepts x := by
        unfold cfibPred
        have hne : (x != 0) = true := bne_iff_ne.mpr hx
        rw [hne]; rfl
      simp only [hx, ↓reduceIte, indBool, hp]
  have h0p : indBool cfibPred (0 : BitVec k) = 0 := by unfold indBool cfibPred; simp
  have h0a : indBool cfibAccepts (0 : BitVec k) = 1 := by
    unfold indBool cfibAccepts
    rw [rotl1_zero]; simp
  rw [hrem, chi_zero_right, Int.one_mul, Int.one_mul, h0p, h0a]
  omega

theorem cfibPred_deg (k : Nat) (hk : 2 ≤ k) :
    graphDeg (cfibPred (k := k)) = (lucas k : Int) - 1 := by
  rw [← graphEig_zero, graphEig_cfibPred, cfibAccepts_wht_zero k hk]

def mod2Pred {k : Nat} (x : BitVec k) : Bool :=
  x != 0 && x.toNat % 2 == 0

end WalshAutomatonEngine

-- ============================================================================
-- SECTION 9: Exhaustive Axiom Audit (`#print axioms`)
-- ============================================================================
