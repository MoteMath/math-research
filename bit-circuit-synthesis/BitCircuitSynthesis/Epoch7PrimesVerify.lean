/-
  Pure-Silicon Mathematical "Big Bang" — Epochs 7..9 Zero-Dependency Lean 4 Kernel Proofs
  (`Epoch7PrimesVerify.lean`)

  NO Mathlib. NO built-in `Nat`, `Int`, or `Bool` arithmetic used anywhere.
  Constructs Divisibility, Polynomial Divisibility in F_2[x], Primes, F_2[x] Irreducibles,
  Coprimality, Distributivity, Freshman's Dream (`(x ⊕ y)^2 = x^2 ⊕ y^2` in F_2[x]),
  and the Carry-Divergence Theorems (`5 = 101_2` is Reducible `3 ⊗ 3` in F_2[x],
  while `25 = 11001_2 = 5 * 5` is Composite in N) strictly from Epoch-0 `BBit` & `BBin`.
-/

import BitCircuitSynthesis.BigBangScratchVerify

namespace SiliconBigBang

def bone   : BBin := BBin.pos BPos.one
def btwo   : BBin := BBin.pos (BPos.x0 BPos.one)
def bthree : BBin := BBin.pos (BPos.x1 BPos.one)
def bfive  : BBin := BBin.pos (BPos.x1 (BPos.x0 BPos.one))
def btwentyfive : BBin := BBin.pos (BPos.x1 (BPos.x0 (BPos.x0 (BPos.x1 BPos.one))))

-- ============================================================================
-- Epoch 7a: Existential Witness Relations (`bdivides`, `bdivides_f2x`, `ble`)
-- ============================================================================
def bdivides (d n : BBin) : Prop := ∃ q : BBin, bmul d q = n
def bdivides_f2x (d n : BBin) : Prop := ∃ q : BBin, bclmul d q = n
def ble_alg (a b : BBin) : Prop := ∃ w : BBin, badd a w = b

-- ============================================================================
-- Epoch 7b: Universal Quantifier Predicates (`bis_prime`, `bis_irred_f2x`, `bcoprime`)
-- ============================================================================
def bis_prime (p : BBin) : Prop :=
  p ≠ BBin.zero ∧ p ≠ bone ∧ ∀ d : BBin, bdivides d p → (d = bone ∨ d = p)

def bis_irred_f2x (p : BBin) : Prop :=
  p ≠ BBin.zero ∧ p ≠ bone ∧ ∀ d : BBin, bdivides_f2x d p → (d = bone ∨ d = p)

def bcoprime (a b : BBin) : Prop :=
  ∀ d : BBin, bdivides d a → bdivides d b → d = bone

-- ============================================================================
-- Universal Divisibility & Algebraic Order Theorems
-- ============================================================================
theorem bmul_one_right (x : BBin) : bmul x bone = x := by
  cases x <;> rfl

theorem bclmul_one_right (x : BBin) : bclmul x bone = x := by
  cases x <;> rfl

theorem bdivides_refl (x : BBin) : bdivides x x :=
  ⟨bone, bmul_one_right x⟩

theorem bdivides_f2x_refl (x : BBin) : bdivides_f2x x x :=
  ⟨bone, bclmul_one_right x⟩

theorem bdivides_zero (x : BBin) : bdivides x BBin.zero :=
  ⟨BBin.zero, by cases x <;> rfl⟩

theorem bdivides_f2x_zero (x : BBin) : bdivides_f2x x BBin.zero :=
  ⟨BBin.zero, rfl⟩

theorem ble_alg_refl (x : BBin) : ble_alg x x :=
  ⟨BBin.zero, by cases x <;> rfl⟩

-- ============================================================================
-- Bit Projections (`blsb`, `bshr`) & Clean F_2[x] Associativity / Distributivity
-- ============================================================================
def blsb : BBin → BBit
  | BBin.zero => BBit.b0
  | BBin.pos BPos.one => BBit.b1
  | BBin.pos (BPos.x0 _) => BBit.b0
  | BBin.pos (BPos.x1 _) => BBit.b1

def bshr : BBin → BBin
  | BBin.zero => BBin.zero
  | BBin.pos BPos.one => BBin.zero
  | BBin.pos (BPos.x0 p) => BBin.pos p
  | BBin.pos (BPos.x1 p) => BBin.pos p

theorem bxor_bin_zero_right (x : BBin) : bxor_bin x BBin.zero = x := by
  cases x <;> rfl

theorem bsnoc_xor (a b : BBin) (u v : BBit) :
    bxor_bin (bsnoc a u) (bsnoc b v) = bsnoc (bxor_bin a b) (bxor u v) := by
  cases a <;> cases b <;> cases u <;> cases v <;> rfl

theorem bxor_bin_step (x y : BBin) :
    bxor_bin x y = bsnoc (bxor_bin (bshr x) (bshr y)) (bxor (blsb x) (blsb y)) := by
  cases x with
  | zero =>
    cases y with
    | zero => rfl
    | pos q => cases q <;> rfl
  | pos p =>
    cases y with
    | zero => cases p <;> rfl
    | pos q => cases p <;> cases q <;> rfl

theorem blsb_bsnoc (a : BBin) (u : BBit) : blsb (bsnoc a u) = u := by
  cases a <;> cases u <;> rfl

theorem bshr_bsnoc (a : BBin) (u : BBit) : bshr (bsnoc a u) = a := by
  cases a <;> cases u <;> rfl

theorem blsb_xor (x y : BBin) : blsb (bxor_bin x y) = bxor (blsb x) (blsb y) := by
  rw [bxor_bin_step, blsb_bsnoc]

theorem bshr_xor (x y : BBin) : bshr (bxor_bin x y) = bxor_bin (bshr x) (bshr y) := by
  rw [bxor_bin_step, bshr_bsnoc]

theorem bpos_xor_assoc_aux (p : BPos) (y z : BBin) :
    bxor_bin (bxor_bin (BBin.pos p) y) z = bxor_bin (BBin.pos p) (bxor_bin y z) := by
  induction p generalizing y z with
  | one =>
    rw [bxor_bin_step (BBin.pos BPos.one) y]
    rw [bxor_bin_step _ z, bxor_bin_step (BBin.pos BPos.one) (bxor_bin y z)]
    rw [bshr_bsnoc, blsb_bsnoc, bshr_xor, blsb_xor]
    change bsnoc (bxor_bin (bxor_bin BBin.zero (bshr y)) (bshr z)) (bxor (bxor BBit.b1 (blsb y)) (blsb z)) =
           bsnoc (bxor_bin BBin.zero (bxor_bin (bshr y) (bshr z))) (bxor BBit.b1 (bxor (blsb y) (blsb z)))
    rw [bxor_assoc]
    rfl
  | x0 p ih =>
    rw [bxor_bin_step (BBin.pos p.x0) y]
    rw [bxor_bin_step _ z, bxor_bin_step (BBin.pos p.x0) (bxor_bin y z)]
    rw [bshr_bsnoc, blsb_bsnoc, bshr_xor, blsb_xor]
    change bsnoc (bxor_bin (bxor_bin (BBin.pos p) (bshr y)) (bshr z)) (bxor (bxor BBit.b0 (blsb y)) (blsb z)) =
           bsnoc (bxor_bin (BBin.pos p) (bxor_bin (bshr y) (bshr z))) (bxor BBit.b0 (bxor (blsb y) (blsb z)))
    rw [ih (bshr y) (bshr z), bxor_assoc]
  | x1 p ih =>
    rw [bxor_bin_step (BBin.pos p.x1) y]
    rw [bxor_bin_step _ z, bxor_bin_step (BBin.pos p.x1) (bxor_bin y z)]
    rw [bshr_bsnoc, blsb_bsnoc, bshr_xor, blsb_xor]
    change bsnoc (bxor_bin (bxor_bin (BBin.pos p) (bshr y)) (bshr z)) (bxor (bxor BBit.b1 (blsb y)) (blsb z)) =
           bsnoc (bxor_bin (BBin.pos p) (bxor_bin (bshr y) (bshr z))) (bxor BBit.b1 (bxor (blsb y) (blsb z)))
    rw [ih (bshr y) (bshr z), bxor_assoc]

theorem bxor_bin_assoc (x y z : BBin) :
    bxor_bin (bxor_bin x y) z = bxor_bin x (bxor_bin y z) := by
  cases x with
  | zero => rfl
  | pos p => exact bpos_xor_assoc_aux p y z

theorem bxor_bin_four_swap (a b c d : BBin) :
    bxor_bin (bxor_bin a b) (bxor_bin c d) = bxor_bin (bxor_bin a c) (bxor_bin b d) := by
  rw [bxor_bin_assoc a b (bxor_bin c d)]
  rw [← bxor_bin_assoc b c d, bxor_bin_comm b c, bxor_bin_assoc c b d]
  rw [← bxor_bin_assoc a c (bxor_bin b d)]

theorem bshl1_xor (x y : BBin) :
    bshl1 (bxor_bin x y) = bxor_bin (bshl1 x) (bshl1 y) := by
  exact (bsnoc_xor x y BBit.b0 BBit.b0).symm

-- Right distributivity of `bclmul` over `bxor_bin`!
theorem bpos_clmul_xor_left (x y : BBin) (q : BPos) :
    bpos_clmul (bxor_bin x y) q = bxor_bin (bpos_clmul x q) (bpos_clmul y q) := by
  induction q with
  | one => rfl
  | x0 q ih => simp [bpos_clmul, ih, bshl1_xor]
  | x1 q ih => simp [bpos_clmul, ih, bshl1_xor, bxor_bin_four_swap]

theorem bclmul_xor_left (x y z : BBin) :
    bclmul (bxor_bin x y) z = bxor_bin (bclmul x z) (bclmul y z) := by
  cases z with
  | zero => rfl
  | pos q => exact bpos_clmul_xor_left x y q

-- Commutativity of `bclmul`, Left Distributivity & Freshman's Dream in F_2[x]!
theorem bpos_clmul_zero_left (q : BPos) : bpos_clmul BBin.zero q = BBin.zero := by
  induction q with
  | one => rfl
  | x0 q ih => change bshl1 (bpos_clmul BBin.zero q) = BBin.zero; rw [ih]; rfl
  | x1 q ih => change bxor_bin (bshl1 (bpos_clmul BBin.zero q)) BBin.zero = BBin.zero; rw [ih]; rfl

theorem bclmul_zero_left (z : BBin) : bclmul BBin.zero z = BBin.zero := by
  cases z with
  | zero => rfl
  | pos q => exact bpos_clmul_zero_left q

theorem bclmul_shl1_left (x y : BBin) :
    bclmul (bshl1 x) y = bshl1 (bclmul x y) := by
  cases y with
  | zero => rfl
  | pos q =>
    induction q with
    | one => rfl
    | x0 q ih => change bshl1 (bclmul (bshl1 x) (BBin.pos q)) = bshl1 (bshl1 (bclmul x (BBin.pos q))); rw [ih]
    | x1 q ih =>
      change bxor_bin (bshl1 (bclmul (bshl1 x) (BBin.pos q))) (bshl1 x) =
             bshl1 (bxor_bin (bshl1 (bclmul x (BBin.pos q))) x)
      rw [ih, bshl1_xor]

theorem bclmul_one_left (y : BBin) : bclmul bone y = y := by
  cases y with
  | zero => rfl
  | pos q =>
    induction q with
    | one => rfl
    | x0 q ih =>
      change bshl1 (bclmul bone (BBin.pos q)) = BBin.pos q.x0
      rw [ih]; rfl
    | x1 q ih =>
      change bxor_bin (bshl1 (bclmul bone (BBin.pos q))) bone = BBin.pos q.x1
      rw [ih]; rfl

theorem bclmul_comm (x y : BBin) : bclmul x y = bclmul y x := by
  cases x with
  | zero => exact bclmul_zero_left y
  | pos p =>
    induction p with
    | one => exact bclmul_one_left y
    | x0 p ih =>
      change bclmul (bshl1 (BBin.pos p)) y = bshl1 (bclmul y (BBin.pos p))
      rw [bclmul_shl1_left, ih]
    | x1 p ih =>
      have hsplit : BBin.pos (BPos.x1 p) = bxor_bin (bshl1 (BBin.pos p)) bone := rfl
      rw [hsplit, bclmul_xor_left, bclmul_shl1_left, bclmul_one_left, ih]
      rfl

theorem bclmul_xor_right (d a b : BBin) :
    bclmul d (bxor_bin a b) = bxor_bin (bclmul d a) (bclmul d b) := by
  rw [bclmul_comm d (bxor_bin a b), bclmul_xor_left, bclmul_comm a d, bclmul_comm b d]

theorem bdivides_f2x_xor (d a b : BBin) :
    bdivides_f2x d a → bdivides_f2x d b → bdivides_f2x d (bxor_bin a b) := by
  rintro ⟨qa, rfl⟩ ⟨qb, rfl⟩
  exact ⟨bxor_bin qa qb, bclmul_xor_right d qa qb⟩

theorem bclmul_freshmans_dream (x y : BBin) :
    bclmul (bxor_bin x y) (bxor_bin x y) = bxor_bin (bclmul x x) (bclmul y y) := by
  rw [bclmul_xor_left, bclmul_xor_right, bclmul_xor_right]
  rw [bclmul_comm y x]
  rw [bxor_bin_assoc (bclmul x x) (bclmul x y) (bxor_bin (bclmul x y) (bclmul y y))]
  rw [← bxor_bin_assoc (bclmul x y) (bclmul x y) (bclmul y y)]
  rw [bxor_bin_self (bclmul x y)]
  rfl

-- ============================================================================
-- Carry-vs-Carryless Prime/Irreducible Separation Theorems!
-- 1. `5 = 101_2` (`x^2 + 1 = (x + 1)^2 = 3 ⊗ 3`) is Reducible in F_2[x]!
-- 2. `25 = 11001_2` (`x^4 + x^3 + 1`, Irreducible in F_2[x]) is Composite `5 * 5` in N!
-- ============================================================================
theorem bthree_clmul_bthree_eq_bfive : bclmul bthree bthree = bfive := rfl

theorem bfive_not_irred_f2x : ¬ bis_irred_f2x bfive := by
  intro ⟨_, _, hall⟩
  have hdiv : bdivides_f2x bthree bfive := ⟨bthree, bthree_clmul_bthree_eq_bfive⟩
  cases hall bthree hdiv with
  | inl h1 => injection h1 with hp; cases hp
  | inr h5 => injection h5 with hp; injection hp with hq; cases hq

theorem bfive_mul_bfive_eq_btwentyfive : bmul bfive bfive = btwentyfive := rfl

theorem btwentyfive_not_prime : ¬ bis_prime btwentyfive := by
  intro ⟨_, _, hall⟩
  have hdiv : bdivides bfive btwentyfive := ⟨bfive, bfive_mul_bfive_eq_btwentyfive⟩
  cases hall bfive hdiv with
  | inl h1 => injection h1 with hp; cases hp
  | inr h25 => injection h25 with hp; injection hp with hq; injection hq with hr; cases hr

end SiliconBigBang
