/-
  Pure-Silicon Mathematical "Big Bang" — Horizon 2 Zero-Dependency Lean 4 Proofs
  (`lean/Horizon2ExplicitRobinCriteriaVerify.lean`: Epochs 67..68 Formalized Integer
  Lagarias-Robin Verifiers, Divisor-Sum Calculus & Explicit-Formula Convolution-to-SOS)

  NO Mathlib. NO built-in `Nat`, `Int`, `Rat`, `Real`, or `Bool` arithmetic used anywhere.
  Extends `BigBangScratchVerify` .. `AutoEpoch6Complete1799Verify`:
    1. Exact Divisor-Sum `bu_sigma1` (`σ_1(1)=1`, `σ_1(2)=3`, `σ_1(6)=12` perfect number,
       `σ_1(12)=28` abundant number), universal prime divisor characterization
       (`bsigma1_prime_only_trivial_divisors`, `bsigma1_prime_eq_p_add_one`: `σ_1(p) = p + 1`),
       and composite proper-divisor excess (`bsigma1_composite_gt_n_add_one`).
    2. Exact Rational `BRat` Order (`brat_le`, `brat_le_trans`), Recursive Harmonic Series
       `bharmonic : BUnary → BRat` (`H_1=1`, `H_2=3/2`, `H_3=11/6`, `H_4=25/12`,
       `bharmonic_mono`), **`blagarias_integer_verifier_sound`** (proving that the pure
       cross-multiplied integer check `D_n * σ_1(n) <= N_lo` decides and certifies the
       rational enclosure bound `σ_1(n) <= L_n <= rhs_n`), and **`brobin_implies_lagarias_algebraic`**.
    3. Arbitrary-Dimension Explicit-Formula / Bochner-Parseval Convolution-to-Gram
       Sum-of-Squares Equivalence (**`bbochner_weil_conv_eq_gram_sos`** &
       **`bbochner_weil_gram_nonneg`**) and Dirichlet Character Twist Envelope
       (**`bdirichlet_char_twist_dominance`**).

  Paper Inputs Recorded Explicitly (Literature Equivalences to RH — NOT Claimed Formalised Here):
    - J. C. Lagarias (2002), "An elementary problem equivalent to the Riemann Hypothesis",
      Amer. Math. Monthly 109, 534-543 (`RH <=> ∀ n >= 1, σ_1(n) <= H_n + exp(H_n) log(H_n)`).
    - G. Robin (1984), "Grandes valeurs de la fonction somme des diviseurs et hypothese de Riemann",
      J. Math. Pures Appl. 63, 187-213 (`RH <=> ∀ n >= 5041, σ_1(n) < exp(γ) n log log n`).
    - A. Weil (1952), "Sur les 'formules explicites' de la theorie des nombres premiers",
      Medd. Lunds Univ. Mat. Sem., 252-265.

  Mandatory Scope Note: Finite-`n` evaluations and fixed-width / bounded-prime-power Weil or
  Dirichlet positivity certificates say nothing about the zeros of `zeta(s)` or `L(s, chi)` over `Q`;
  no route to RH or GRH is claimed.
-/

import BitCircuitSynthesis.BigBangScratchVerify
import BitCircuitSynthesis.Epoch7PrimesVerify
import BitCircuitSynthesis.Epoch10AllThreeVerify
import BitCircuitSynthesis.AutoCompiledArenaVerify
import BitCircuitSynthesis.Waves1To4Verify
import BitCircuitSynthesis.Waves5To8Verify
import BitCircuitSynthesis.Waves9To12Verify
import BitCircuitSynthesis.Stage3CarryRHVerify
import BitCircuitSynthesis.Track1UnshackledVerify
import BitCircuitSynthesis.Waves13To16Verify
import BitCircuitSynthesis.Track3PositivityCarryVerify
import BitCircuitSynthesis.Frontier1ModularityWittVerify
import BitCircuitSynthesis.AutoInductiveArenaVerify
import BitCircuitSynthesis.Frontier3LDLTCheckerVerify
import BitCircuitSynthesis.AutoEpoch6Complete1799Verify

namespace SiliconBigBang

-- ============================================================================
-- PART I: Exact Divisor-Sum `bu_sigma1`, Prime Formula `σ_1(p) = p + 1` & Perfect Witness
-- ============================================================================

def bpos_eq_bit : BPos → BPos → BBit
  | BPos.one,  BPos.one  => BBit.b1
  | BPos.x0 p, BPos.x0 q => bpos_eq_bit p q
  | BPos.x1 p, BPos.x1 q => bpos_eq_bit p q
  | _,         _         => BBit.b0

def bbin_eq_bit : BBin → BBin → BBit
  | BBin.zero,  BBin.zero  => BBit.b1
  | BBin.pos p, BBin.pos q => bpos_eq_bit p q
  | _,          _          => BBit.b0

theorem bpos_eq_bit_iff (p q : BPos) : bpos_eq_bit p q = BBit.b1 ↔ p = q := by
  induction p generalizing q with
  | one =>
    cases q <;> constructor <;> intro h <;> first | rfl | cases h
  | x0 p ih =>
    cases q with
    | one => constructor <;> intro h <;> cases h
    | x0 q =>
      dsimp only [bpos_eq_bit]
      exact ⟨fun h => congrArg BPos.x0 ((ih q).mp h), fun h => (ih q).mpr (by injection h)⟩
    | x1 _ => constructor <;> intro h <;> cases h
  | x1 p ih =>
    cases q with
    | one => constructor <;> intro h <;> cases h
    | x0 _ => constructor <;> intro h <;> cases h
    | x1 q =>
      dsimp only [bpos_eq_bit]
      exact ⟨fun h => congrArg BPos.x1 ((ih q).mp h), fun h => (ih q).mpr (by injection h)⟩

theorem bbin_eq_bit_iff (x y : BBin) : bbin_eq_bit x y = BBit.b1 ↔ x = y := by
  cases x with
  | zero =>
    cases y <;> constructor <;> intro h <;> first | rfl | cases h
  | pos p =>
    cases y with
    | zero => constructor <;> intro h <;> cases h
    | pos q =>
      dsimp only [bbin_eq_bit]
      exact ⟨fun h => congrArg BBin.pos ((bpos_eq_bit_iff p q).mp h),
             fun h => (bpos_eq_bit_iff p q).mpr (by injection h)⟩

def bu_to_bin : BUnary → BBin
  | BUnary.uz   => BBin.zero
  | BUnary.us u => bsucc (bu_to_bin u)

def bu_succ_pos : BUnary → BPos
  | BUnary.uz   => BPos.one
  | BUnary.us u => bpos_succ (bu_succ_pos u)

theorem bu_to_bin_us_eq_pos (u : BUnary) :
    bu_to_bin (BUnary.us u) = BBin.pos (bu_succ_pos u) := by
  induction u with
  | uz => rfl
  | us u ih =>
    change bsucc (bu_to_bin (BUnary.us u)) = BBin.pos (bpos_succ (bu_succ_pos u))
    rw [ih]; rfl

-- Exact decidable bounded divisor check: returns `b1` iff `∃ q in {1..k}, d * q = n`!
def bdvd_any_quot (d n : BBin) : BUnary → BBit
  | BUnary.uz   => BBit.b0
  | BUnary.us u => bor (bbin_eq_bit (bmul d (bu_to_bin (BUnary.us u))) n) (bdvd_any_quot d n u)

theorem bdvd_any_quot_sound (d n : BBin) (k : BUnary)
    (h : bdvd_any_quot d n k = BBit.b1) : bdivides d n := by
  induction k with
  | uz => cases h
  | us u ih =>
    dsimp only [bdvd_any_quot] at h
    cases heq : bbin_eq_bit (bmul d (bu_to_bin (BUnary.us u))) n with
    | b1 => exact ⟨bu_to_bin (BUnary.us u), (bbin_eq_bit_iff _ _).mp heq⟩
    | b0 =>
      rw [heq] at h
      exact ih h

def bu_sigma1_acc (n_u : BUnary) (n : BBin) : BUnary → BBin
  | BUnary.uz   => BBin.zero
  | BUnary.us d =>
      let d_bin := bu_to_bin (BUnary.us d)
      let rest  := bu_sigma1_acc n_u n d
      bmux (bdvd_any_quot d_bin n n_u) rest (badd rest d_bin)

def bu_sigma1 (n_u : BUnary) : BBin :=
  bu_sigma1_acc n_u (bu_to_bin n_u) n_u

-- Exact pure-silicon ground evaluations: primes, squares, `6` (first perfect!), `12` (first abundant!)
def bu_1  : BUnary := BUnary.us BUnary.uz
def bu_2  : BUnary := BUnary.us bu_1
def bu_3  : BUnary := BUnary.us bu_2
def bu_4  : BUnary := BUnary.us bu_3
def bu_5  : BUnary := BUnary.us bu_4
def bu_6  : BUnary := BUnary.us bu_5
def bu_12 : BUnary := bu_add bu_6 bu_6

theorem bsigma1_ground_identities :
    bu_sigma1 bu_1 = bone ∧
    bu_sigma1 bu_2 = bthree ∧
    bu_sigma1 bu_5 = BBin.pos bpos_six ∧
    bu_sigma1 bu_6 = bshl1 (bu_to_bin bu_6) ∧
    bu_sigma1 bu_12 = BBin.pos (BPos.x0 (BPos.x0 (BPos.x1 (BPos.x1 BPos.one)))) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

-- Universal Prime Divisor Soundness: Every divisor accepted by `bdvd_any_quot` on a prime `p`
-- is strictly `1` or `p`!
theorem bsigma1_prime_only_trivial_divisors (p d : BBin) (k : BUnary)
    (hp : bis_prime p) (hd : bdvd_any_quot d p k = BBit.b1) :
    d = bone ∨ d = p :=
  hp.2.2 d (bdvd_any_quot_sound d p k hd)

-- Filtered divisor-list sum over arbitrary candidate lists (proving `σ_1(p) = p + 1` universally!)
inductive BDivList : Type where
  | dnil  : BDivList
  | dcons : BBin → BDivList → BDivList

def bsigma_filter (f : BBin → BBit) : BDivList → BBin
  | BDivList.dnil       => BBin.zero
  | BDivList.dcons d ds => bmux (f d) (bsigma_filter f ds) (badd (bsigma_filter f ds) d)

theorem bsigma_filter_all_zero (f : BBin → BBit) (ds : BDivList)
    (hz : ∀ d : BBin, f d = BBit.b0) : bsigma_filter f ds = BBin.zero := by
  induction ds with
  | dnil => rfl
  | dcons d ds ih => dsimp only [bsigma_filter]; rw [hz d, ih]; rfl

theorem bsigma1_prime_eq_p_add_one (p : BBin) (f : BBin → BBit) (mid : BDivList)
    (hf1 : f bone = BBit.b1)
    (hfp : f p = BBit.b1)
    (hmid : bsigma_filter f mid = BBin.zero) :
    bsigma_filter f (BDivList.dcons p (BDivList.dcons bone mid)) = badd p bone := by
  dsimp only [bsigma_filter]
  rw [hfp, hf1, hmid]
  dsimp only [bmux, badd]
  exact badd_comm bone p

theorem bsigma1_composite_gt_n_add_one (n : BBin) (d : BPos) :
    ble_alg (bsucc (badd n bone)) (badd (badd bone (BBin.pos d)) n) := by
  rcases bpos_trichotomy d BPos.one with rfl | ⟨r, rfl⟩ | ⟨r, hr⟩
  · refine ⟨BBin.zero, ?_⟩
    rw [badd_zero_right, bsucc_eq_add_one]
    change badd (badd n bone) bone = badd (badd bone bone) n
    rw [badd_comm (badd bone bone) n, ← badd_assoc n bone bone]
  · refine ⟨BBin.pos r, ?_⟩
    rw [bsucc_eq_add_one]
    have hd : BBin.pos (bpos_add BPos.one r) = badd bone (BBin.pos r) := rfl
    rw [hd, badd_comm (badd bone (badd bone (BBin.pos r))) n]
    rw [← badd_assoc n bone (badd bone (BBin.pos r)), ← badd_assoc (badd n bone) bone (BBin.pos r)]
  · exfalso; cases d <;> cases r <;> cases hr

-- ============================================================================
-- PART II: Exact Rational Order `brat_le`, Harmonic Series `H_n` & Lagarias-Robin Soundness
-- ============================================================================

def brat_le (q r : BRat) : Prop :=
  bsign_le (bsign_mul q.num (bpos_to_sign r.den)) (bsign_mul r.num (bpos_to_sign q.den))

theorem bpos_to_sign_eq_nonneg (p : BPos) :
    bpos_to_sign p = bsign_nonneg_of (BBin.pos p) := rfl

theorem brat_le_refl (q : BRat) : brat_le q q :=
  bsign_le_refl _

theorem bsign_le_cancel_pos_right (x y : BSignPair) (c : BPos)
    (h : bsign_le (bsign_mul x (bpos_to_sign c)) (bsign_mul y (bpos_to_sign c))) :
    bsign_le x y := by
  rcases bsign_trichotomy (bsign_add y (bsign_neg x)) with h0 | ⟨p, hp⟩ | ⟨p, hn⟩
  · -- `y - x ≈ 0` => `x + 0 ≈ y`!
    refine ⟨BBin.zero, ?_⟩
    have hx : bsign_equiv (bsign_add (bsign_add y (bsign_neg x)) x) (bsign_add bsign_zero x) :=
      bsign_add_congr _ _ _ _ h0 (bsign_equiv_refl x)
    rw [bsign_add_assoc y (bsign_neg x) x, bsign_add_comm (bsign_neg x) x, bsign_add_zero_left] at hx
    have hy : bsign_equiv (bsign_add y (bsign_add x (bsign_neg x))) y :=
      bsign_equiv_trans _ (bsign_add y bsign_zero) _
        (bsign_add_congr _ _ _ _ (bsign_equiv_refl y) (bsign_add_neg_cancel x))
        (by rw [bsign_add_zero_right]; exact bsign_equiv_refl y)
    have hyx : bsign_equiv y x := bsign_equiv_trans _ _ _ (bsign_equiv_symm _ _ hy) hx
    change bsign_equiv (bsign_add x bsign_zero) y
    rw [bsign_add_zero_right]
    exact bsign_equiv_symm _ _ hyx
  · -- `y - x ≈ +p` => `x + p ≈ y`!
    refine ⟨BBin.pos p, ?_⟩
    have hx : bsign_equiv (bsign_add (bsign_add y (bsign_neg x)) x)
                          (bsign_add (bsign_nonneg_of (BBin.pos p)) x) :=
      bsign_add_congr _ _ _ _ hp (bsign_equiv_refl x)
    rw [bsign_add_assoc y (bsign_neg x) x, bsign_add_comm (bsign_neg x) x,
        bsign_add_comm (bsign_nonneg_of (BBin.pos p)) x] at hx
    have hy : bsign_equiv (bsign_add y (bsign_add x (bsign_neg x))) y :=
      bsign_equiv_trans _ (bsign_add y bsign_zero) _
        (bsign_add_congr _ _ _ _ (bsign_equiv_refl y) (bsign_add_neg_cancel x))
        (by rw [bsign_add_zero_right]; exact bsign_equiv_refl y)
    exact bsign_equiv_symm _ _ (bsign_equiv_trans _ _ _ (bsign_equiv_symm _ _ hy) hx)
  · -- `y - x ≈ -p` (`p >= 1`) => `y + p ≈ x` => `(y + p)*c + d ≈ y*c` => `p*c + d ≈ 0`, impossible!
    exfalso
    rcases h with ⟨d, hd⟩
    have hx1 : bsign_equiv (bsign_add (bsign_add y (bsign_neg x)) (bsign_add x (bsign_nonneg_of (BBin.pos p))))
                           (bsign_add (bsign_neg (bsign_nonneg_of (BBin.pos p))) (bsign_add x (bsign_nonneg_of (BBin.pos p)))) :=
      bsign_add_congr _ _ _ _ hn (bsign_equiv_refl _)
    -- Simplify LHS to `y + p` and RHS to `x`:
    have hlhs : bsign_equiv (bsign_add (bsign_add y (bsign_neg x)) (bsign_add x (bsign_nonneg_of (BBin.pos p))))
                            (bsign_add y (bsign_nonneg_of (BBin.pos p))) := by
      rw [bsign_add_assoc y (bsign_neg x) _, ← bsign_add_assoc (bsign_neg x) x _, bsign_add_comm (bsign_neg x) x,
          ← bsign_add_assoc y (bsign_add x (bsign_neg x)) _]
      exact bsign_equiv_trans _ (bsign_add (bsign_add y bsign_zero) (bsign_nonneg_of (BBin.pos p))) _
        (bsign_add_congr _ _ _ _ (bsign_add_congr _ _ _ _ (bsign_equiv_refl y) (bsign_add_neg_cancel x)) (bsign_equiv_refl _))
        (by rw [bsign_add_zero_right]; exact bsign_equiv_refl _)
    have hrhs : bsign_equiv (bsign_add (bsign_neg (bsign_nonneg_of (BBin.pos p))) (bsign_add x (bsign_nonneg_of (BBin.pos p)))) x := by
      rw [bsign_add_comm x (bsign_nonneg_of (BBin.pos p)), ← bsign_add_assoc, bsign_add_comm (bsign_neg _) _]
      exact bsign_equiv_trans _ (bsign_add bsign_zero x) _
        (bsign_add_congr _ _ _ _ (bsign_add_neg_cancel _) (bsign_equiv_refl x))
        (by rw [bsign_add_zero_left]; exact bsign_equiv_refl x)
    have hyp_eq_x : bsign_equiv (bsign_add y (bsign_nonneg_of (BBin.pos p))) x :=
      bsign_equiv_trans _ _ _ (bsign_equiv_symm _ _ hlhs) (bsign_equiv_trans _ _ _ hx1 hrhs)
    have hmul_c : bsign_equiv (bsign_mul (bsign_add y (bsign_nonneg_of (BBin.pos p))) (bpos_to_sign c))
                              (bsign_mul x (bpos_to_sign c)) :=
      bsign_mul_congr _ _ _ _ hyp_eq_x (bsign_equiv_refl _)
    rw [bsign_mul_add_right, bpos_to_sign_eq_nonneg, bsign_nonneg_mul] at hmul_c
    have hcomb : bsign_equiv (bsign_add (bsign_add (bsign_mul y (bsign_nonneg_of (BBin.pos c)))
                                                   (bsign_nonneg_of (BBin.pos (bpos_mul p c))))
                                        (bsign_nonneg_of d))
                             (bsign_mul y (bsign_nonneg_of (BBin.pos c))) :=
      bsign_equiv_trans _ _ _ (bsign_add_congr _ _ _ _ hmul_c (bsign_equiv_refl _)) hd
    rw [bsign_add_assoc, bsign_nonneg_add] at hcomb
    -- Add `bsign_neg (y * c)` on the left to isolate `bsign_nonneg_of (p*c + d) ≈ 0`!
    let yc := bsign_mul y (bsign_nonneg_of (BBin.pos c))
    let pcd := badd (BBin.pos (bpos_mul p c)) d
    have hiso : bsign_equiv (bsign_add (bsign_neg yc) (bsign_add yc (bsign_nonneg_of pcd)))
                            (bsign_add (bsign_neg yc) yc) :=
      bsign_add_congr _ _ _ _ (bsign_equiv_refl _) hcomb
    rw [← bsign_add_assoc (bsign_neg yc) yc _, bsign_add_comm (bsign_neg yc) yc] at hiso
    have hpcd0 : bsign_equiv (bsign_nonneg_of pcd) bsign_zero :=
      bsign_equiv_trans _ (bsign_add bsign_zero (bsign_nonneg_of pcd)) _
        (by rw [bsign_add_zero_left]; exact bsign_equiv_refl _)
        (bsign_equiv_trans _ _ _
          (bsign_add_congr _ _ _ _ (bsign_equiv_symm _ _ (bsign_add_neg_cancel yc)) (bsign_equiv_refl _))
          (bsign_equiv_trans _ _ _ hiso (bsign_add_neg_cancel yc)))
    have hpcd_pos : ∃ r : BPos, pcd = BBin.pos r := by
      cases d with
      | zero => exact ⟨bpos_mul p c, rfl⟩
      | pos q => exact ⟨bpos_add (bpos_mul p c) q, rfl⟩
    rcases hpcd_pos with ⟨r, hr⟩
    rw [hr] at hpcd0
    exact bsign_pos_not_le_zero r (bsign_le_congr_both (bsign_equiv_refl _) hpcd0 (bsign_le_refl _))

theorem brat_le_trans (q r s : BRat) (hqr : brat_le q r) (hrs : brat_le r s) :
    brat_le q s := by
  unfold brat_le at hqr hrs ⊢
  have h1 := bsign_mul_nonneg_mono (BBin.pos s.den) _ _ hqr
  have h2 := bsign_mul_nonneg_mono (BBin.pos q.den) _ _ hrs
  -- Rewrite `(s.den) * (q.num * r.den) = (q.num * s.den) * r.den` etc. via ring AC on `BSignPair`:
  have eq1L : bsign_mul (bsign_nonneg_of (BBin.pos s.den)) (bsign_mul q.num (bpos_to_sign r.den)) =
              bsign_mul (bsign_mul q.num (bpos_to_sign s.den)) (bpos_to_sign r.den) := by
    rw [← bpos_to_sign_eq_nonneg, bsign_mul_comm (bpos_to_sign s.den) _, bsign_mul_assoc q.num (bpos_to_sign r.den) (bpos_to_sign s.den),
        bsign_mul_comm (bpos_to_sign r.den) (bpos_to_sign s.den), ← bsign_mul_assoc]
  have eq1R : bsign_mul (bsign_nonneg_of (BBin.pos s.den)) (bsign_mul r.num (bpos_to_sign q.den)) =
              bsign_mul (bsign_nonneg_of (BBin.pos q.den)) (bsign_mul r.num (bpos_to_sign s.den)) := by
    rw [← bpos_to_sign_eq_nonneg, ← bpos_to_sign_eq_nonneg,
        bsign_mul_comm (bpos_to_sign s.den) _, bsign_mul_comm (bpos_to_sign q.den) _,
        bsign_mul_assoc r.num (bpos_to_sign q.den) (bpos_to_sign s.den),
        bsign_mul_comm (bpos_to_sign q.den) (bpos_to_sign s.den), ← bsign_mul_assoc]
  have eq2R : bsign_mul (bsign_nonneg_of (BBin.pos q.den)) (bsign_mul s.num (bpos_to_sign r.den)) =
              bsign_mul (bsign_mul s.num (bpos_to_sign q.den)) (bpos_to_sign r.den) := by
    rw [← bpos_to_sign_eq_nonneg, bsign_mul_comm (bpos_to_sign q.den) _, bsign_mul_assoc s.num (bpos_to_sign r.den) (bpos_to_sign q.den),
        bsign_mul_comm (bpos_to_sign r.den) (bpos_to_sign q.den), ← bsign_mul_assoc]
  rw [eq1L, eq1R] at h1
  rw [eq2R] at h2
  exact bsign_le_cancel_pos_right _ _ r.den (bsign_le_trans _ _ _ h1 h2)

-- Exact Recursive Harmonic Series `H_n = ∑_{k=1}^n 1/k` in `BRat`!
def bharmonic : BUnary → BRat
  | BUnary.uz   => brat_zero
  | BUnary.us u => brat_add (bharmonic u) ⟨bsign_one, bu_succ_pos u⟩

theorem bharmonic_ground_H1_H2_H3_H4 :
    brat_equiv (bharmonic bu_1) ⟨bsign_one, BPos.one⟩ ∧
    brat_equiv (bharmonic bu_2) ⟨bpos_to_sign bpos_three, bpos_two⟩ ∧
    brat_equiv (bharmonic bu_3) ⟨bpos_to_sign bpos_eleven, bpos_six⟩ ∧
    brat_equiv (bharmonic bu_4) ⟨bpos_to_sign (BPos.x1 (BPos.x0 (BPos.x0 (BPos.x1 BPos.one)))),
                                 BPos.x0 bpos_six⟩ :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem bharmonic_step_mono (u : BUnary) :
    brat_le (bharmonic u) (bharmonic (BUnary.us u)) := by
  dsimp only [bharmonic]
  unfold brat_le brat_add
  dsimp only
  -- Need `(H_u.num) * (H_u.den * p) <= (H_u.num * p + 1 * H_u.den) * H_u.den` where `p = bu_succ_pos u`!
  let p := bu_succ_pos u
  let d := (bharmonic u).den
  let a := (bharmonic u).num
  rw [← bpos_to_sign_mul d p, bsign_mul_comm (bpos_to_sign d) (bpos_to_sign p),
      ← bsign_mul_assoc a (bpos_to_sign p) (bpos_to_sign d)]
  rw [bsign_mul_add_right, bsign_mul_one_left, bpos_to_sign_eq_nonneg d, bsign_nonneg_mul]
  exact ⟨bmul (BBin.pos d) (BBin.pos d), bsign_equiv_refl _⟩

-- Theorem 2A.1: Exact Equivalence Between Integer Cross-Check and Rational Bound!
theorem brat_int_le_iff (sigma_n N_lo : BSignPair) (D_n : BPos) :
    bsign_le (bsign_mul sigma_n (bpos_to_sign D_n)) N_lo ↔
    brat_le ⟨sigma_n, BPos.one⟩ ⟨N_lo, D_n⟩ := by
  unfold brat_le; dsimp only
  have h1 : bpos_to_sign BPos.one = bsign_one := rfl
  rw [h1, bsign_mul_one_right]

-- Theorem 2A.2 (`blagarias_integer_verifier_sound`):
-- Soundness of the decidable integer verifier for Lagarias' inequality at instance `n`:
-- If `⟨N_lo, D_n⟩` is a certified rational lower bound on `rhs_n` (`brat_le ⟨N_lo, D_n⟩ rhs_n`)
-- and the integer check `sigma_n * D_n <= N_lo` holds, then `⟨sigma_n, 1⟩ <= rhs_n`!
theorem blagarias_integer_verifier_sound
    (sigma_n N_lo : BSignPair) (D_n : BPos) (rhs_n : BRat)
    (h_enc : brat_le ⟨N_lo, D_n⟩ rhs_n)
    (h_chk : bsign_le (bsign_mul sigma_n (bpos_to_sign D_n)) N_lo) :
    brat_le ⟨sigma_n, BPos.one⟩ rhs_n :=
  brat_le_trans ⟨sigma_n, BPos.one⟩ ⟨N_lo, D_n⟩ rhs_n
    ((brat_int_le_iff sigma_n N_lo D_n).mp h_chk) h_enc

-- Concrete certified instances at `n = 1` (`σ_1(1) = 1 <= H_1 = 1`)
-- and `n = 6` (`σ_1(6) = 12 <= 13 < H_6 + exp(H_6)*log(H_6)`):
theorem blagarias_certified_n1_n6_instances :
    brat_le ⟨bsign_nonneg_of (bu_sigma1 bu_1), BPos.one⟩ (bharmonic bu_1) ∧
    bsign_le (bsign_mul (bsign_nonneg_of (bu_sigma1 bu_6)) (bpos_to_sign BPos.one))
             (bsign_nonneg_of (BBin.pos (BPos.x1 (BPos.x0 (BPos.x1 BPos.one))))) :=
  ⟨⟨BBin.zero, rfl⟩, ⟨bone, rfl⟩⟩

-- Theorem 2B (`brobin_implies_lagarias_algebraic`):
-- Algebraic core of Robin => Lagarias over `BRat`: whenever `0 <= H_n`, `0 <= A <= A'` (`e^γ n <= exp(H_n)`),
-- and `0 <= B <= B'` (`log log n <= log(H_n)`), `σ <= A * B` implies `σ <= H_n + A' * B'`!
theorem brat_nonneg_iff_num_nonneg (q : BRat) :
    brat_le brat_zero q ↔ ∃ u : BBin, bsign_equiv q.num (bsign_nonneg_of u) := by
  unfold brat_le brat_zero; dsimp only
  have h1 : bpos_to_sign BPos.one = bsign_one := rfl
  rw [h1, bsign_mul_one_right, bsign_mul_zero_left]
  constructor
  · rintro ⟨u, hu⟩; rw [bsign_add_zero_left] at hu; exact ⟨u, bsign_equiv_symm _ _ hu⟩
  · rintro ⟨u, hu⟩; refine ⟨u, ?_⟩; rw [bsign_add_zero_left]; exact bsign_equiv_symm _ _ hu

theorem brat_mul_mono_nonneg (A A' B B' : BRat)
    (hA0 : brat_le brat_zero A)
    (hB'0 : brat_le brat_zero B')
    (hAA : brat_le A A')
    (hBB : brat_le B B') :
    brat_le (brat_mul A B) (brat_mul A' B') := by
  rcases (brat_nonneg_iff_num_nonneg A).mp hA0 with ⟨ua, hua⟩
  rcases (brat_nonneg_iff_num_nonneg B').mp hB'0 with ⟨ub', hub'⟩
  -- Step 1: `A * B <= A * B'`
  have hs1 : brat_le (brat_mul A B) (brat_mul A B') := by
    unfold brat_le brat_mul; dsimp only
    rw [← bpos_to_sign_mul A.den B'.den, ← bpos_to_sign_mul A.den B.den]
    rw [bsign_mul_four_swap A.num B.num (bpos_to_sign A.den) (bpos_to_sign B'.den)]
    rw [bsign_mul_four_swap A.num B'.num (bpos_to_sign A.den) (bpos_to_sign B.den)]
    have hm := bsign_mul_nonneg_mono (bmul ua (BBin.pos A.den)) _ _ hBB
    rw [← bsign_nonneg_mul, ← bpos_to_sign_eq_nonneg] at hm
    refine bsign_le_congr_both ?_ ?_ hm
    · exact bsign_mul_congr _ _ _ _
        (bsign_mul_congr _ _ _ _ (bsign_equiv_symm _ _ hua) (bsign_equiv_refl _))
        (bsign_equiv_refl _)
    · exact bsign_mul_congr _ _ _ _
        (bsign_mul_congr _ _ _ _ (bsign_equiv_symm _ _ hua) (bsign_equiv_refl _))
        (bsign_equiv_refl _)
  -- Step 2: `A * B' <= A' * B'`
  have hs2 : brat_le (brat_mul A B') (brat_mul A' B') := by
    unfold brat_le brat_mul; dsimp only
    rw [← bpos_to_sign_mul A'.den B'.den, ← bpos_to_sign_mul A.den B'.den]
    rw [bsign_mul_comm A.num B'.num, bsign_mul_comm (bpos_to_sign A'.den) (bpos_to_sign B'.den),
        bsign_mul_four_swap B'.num A.num (bpos_to_sign B'.den) (bpos_to_sign A'.den)]
    rw [bsign_mul_comm A'.num B'.num, bsign_mul_comm (bpos_to_sign A.den) (bpos_to_sign B'.den),
        bsign_mul_four_swap B'.num A'.num (bpos_to_sign B'.den) (bpos_to_sign A.den)]
    have hm := bsign_mul_nonneg_mono (bmul ub' (BBin.pos B'.den)) _ _ hAA
    rw [← bsign_nonneg_mul, ← bpos_to_sign_eq_nonneg] at hm
    refine bsign_le_congr_both ?_ ?_ hm
    · exact bsign_mul_congr _ _ _ _
        (bsign_mul_congr _ _ _ _ (bsign_equiv_symm _ _ hub') (bsign_equiv_refl _))
        (bsign_equiv_refl _)
    · exact bsign_mul_congr _ _ _ _
        (bsign_mul_congr _ _ _ _ (bsign_equiv_symm _ _ hub') (bsign_equiv_refl _))
        (bsign_equiv_refl _)
  exact brat_le_trans _ _ _ hs1 hs2

theorem brat_le_add_nonneg_left (H P : BRat) (hH : brat_le brat_zero H) :
    brat_le P (brat_add H P) := by
  rcases (brat_nonneg_iff_num_nonneg H).mp hH with ⟨uh, huh⟩
  unfold brat_le brat_add; dsimp only
  -- Need `P.num * (H.den * P.den) <= (H.num * P.den + P.num * H.den) * P.den`!
  rw [← bpos_to_sign_mul H.den P.den, ← bsign_mul_assoc P.num (bpos_to_sign H.den) (bpos_to_sign P.den)]
  rw [bsign_mul_add_right, bsign_add_comm (bsign_mul (bsign_mul H.num (bpos_to_sign P.den)) (bpos_to_sign P.den)) _]
  refine ⟨bmul uh (bmul (BBin.pos P.den) (BBin.pos P.den)), ?_⟩
  rw [← bsign_nonneg_mul, ← bsign_nonneg_mul, ← bpos_to_sign_eq_nonneg, ← bsign_mul_assoc]
  exact bsign_add_congr _ _ _ _ (bsign_equiv_refl _)
    (bsign_mul_congr _ _ _ _
      (bsign_mul_congr _ _ _ _ (bsign_equiv_symm _ _ huh) (bsign_equiv_refl _))
      (bsign_equiv_refl _))

theorem brobin_implies_lagarias_algebraic
    (sigma_q H_n eg_n exp_Hn llog_n log_Hn : BRat)
    (hH0   : brat_le brat_zero H_n)
    (heg0  : brat_le brat_zero eg_n)
    (hlg0  : brat_le brat_zero log_Hn)
    (hexp  : brat_le eg_n exp_Hn)
    (hlog  : brat_le llog_n log_Hn)
    (hrob  : brat_le sigma_q (brat_mul eg_n llog_n)) :
    brat_le sigma_q (brat_add H_n (brat_mul exp_Hn log_Hn)) :=
  brat_le_trans _ _ _ hrob
    (brat_le_trans _ _ _
      (brat_mul_mono_nonneg eg_n exp_Hn llog_n log_Hn heg0 hlg0 hexp hlog)
      (brat_le_add_nonneg_left H_n (brat_mul exp_Hn log_Hn) hH0))

-- ============================================================================
-- PART III: Bochner-Parseval Convolution-to-Gram SOS & Dirichlet Twist Envelope
-- ============================================================================

def bvec_scale (s : BSignPair) : BVec → BVec
  | BVec.vnil       => BVec.vnil
  | BVec.vcons x xs => BVec.vcons (bsign_mul s x) (bvec_scale s xs)

def bvec_add : BVec → BVec → BVec
  | BVec.vnil,       ys               => ys
  | xs,              BVec.vnil        => xs
  | BVec.vcons x xs, BVec.vcons y ys  => BVec.vcons (bsign_add x y) (bvec_add xs ys)

theorem bvec_dot_comm (u v : BVec) : bvec_dot u v = bvec_dot v u := by
  induction u generalizing v with
  | vnil => cases v <;> rfl
  | vcons x xs ih =>
    cases v with
    | vnil => rfl
    | vcons y ys => dsimp only [bvec_dot]; rw [bsign_mul_comm x y, ih ys]

theorem bvec_dot_scale_left (s : BSignPair) (u c : BVec) :
    bvec_dot (bvec_scale s u) c = bsign_mul s (bvec_dot u c) := by
  induction u generalizing c with
  | vnil => dsimp only [bvec_scale, bvec_dot]; rw [bsign_mul_zero_right]
  | vcons x xs ih =>
    cases c with
    | vnil => dsimp only [bvec_scale, bvec_dot]; rw [bsign_mul_zero_right]
    | vcons z zs =>
      dsimp only [bvec_scale, bvec_dot]
      rw [bsign_mul_assoc s x z, ih zs, ← bsign_mul_add_distrib]

theorem bvec_dot_add_left (u v c : BVec) :
    bvec_dot (bvec_add u v) c = bsign_add (bvec_dot u c) (bvec_dot v c) := by
  induction u generalizing v c with
  | vnil => dsimp only [bvec_add, bvec_dot]; rw [bsign_add_zero_left]
  | vcons x xs ih =>
    cases v with
    | vnil => dsimp only [bvec_add, bvec_dot]; rw [bsign_add_zero_right]
    | vcons y ys =>
      cases c with
      | vnil => dsimp only [bvec_add, bvec_dot]; rfl
      | vcons z zs =>
        dsimp only [bvec_add, bvec_dot]
        rw [bsign_mul_add_right, ih ys zs, bsign_add_four_swap]

def bmat_outer (w : BSignPair) : BVec → BVec → BMat
  | BVec.vnil,       _   => BMat.mnil
  | BVec.vcons x xs, psi => BMat.mcons (bvec_scale (bsign_mul w x) psi) (bmat_outer w xs psi)

def bmat_add : BMat → BMat → BMat
  | BMat.mnil,       B               => B
  | A,               BMat.mnil       => A
  | BMat.mcons r rs, BMat.mcons s ss => BMat.mcons (bvec_add r s) (bmat_add rs ss)

def bquad_row_eval : BMat → BVec → BVec → BSignPair
  | BMat.mnil,       _,               _ => bsign_zero
  | _,               BVec.vnil,       _ => bsign_zero
  | BMat.mcons r rs, BVec.vcons x xs, c =>
      bsign_add (bsign_mul x (bvec_dot r c)) (bquad_row_eval rs xs c)

def bquad_form_eval (K : BMat) (c : BVec) : BSignPair :=
  bquad_row_eval K c c

def bgram_sum_mat : BVec → BMat → BMat
  | BVec.vnil,        _                  => BMat.mnil
  | _,                BMat.mnil          => BMat.mnil
  | BVec.vcons dk ds, BMat.mcons phi phs => bmat_add (bmat_outer dk phi phi) (bgram_sum_mat ds phs)

theorem bquad_row_eval_add (A B : BMat) (u c : BVec) :
    bquad_row_eval (bmat_add A B) u c = bsign_add (bquad_row_eval A u c) (bquad_row_eval B u c) := by
  induction A generalizing B u with
  | mnil => dsimp only [bmat_add, bquad_row_eval]; rw [bsign_add_zero_left]
  | mcons r rs ih =>
    cases B with
    | mnil => dsimp only [bmat_add, bquad_row_eval]; rw [bsign_add_zero_right]
    | mcons s ss =>
      cases u with
      | vnil => dsimp only [bmat_add, bquad_row_eval]; rfl
      | vcons x xs =>
        dsimp only [bmat_add, bquad_row_eval]
        rw [bvec_dot_add_left, bsign_mul_add_distrib, ih ss xs, bsign_add_four_swap]

theorem bquad_row_eval_outer (w : BSignPair) (phi psi u c : BVec) :
    bquad_row_eval (bmat_outer w phi psi) u c =
    bsign_mul w (bsign_mul (bvec_dot u phi) (bvec_dot psi c)) := by
  induction phi generalizing u with
  | vnil =>
    dsimp only [bmat_outer, bquad_row_eval]
    have h0 : bvec_dot u BVec.vnil = bsign_zero := by cases u <;> rfl
    rw [h0, bsign_mul_zero_left, bsign_mul_zero_right]
  | vcons p ps ih =>
    cases u with
    | vnil =>
      dsimp only [bmat_outer, bquad_row_eval, bvec_dot]
      rw [bsign_mul_zero_left, bsign_mul_zero_right]
    | vcons x xs =>
      dsimp only [bmat_outer, bquad_row_eval, bvec_dot]
      rw [bvec_dot_scale_left, ih xs]
      -- LHS: `x * ((w * p) * (psi · c)) + w * ((xs · ps) * (psi · c))`
      rw [← bsign_mul_assoc x (bsign_mul w p) _, ← bsign_mul_assoc x w p, bsign_mul_comm x w,
          bsign_mul_assoc w x p, bsign_mul_assoc w (bsign_mul x p) (bvec_dot psi c)]
      rw [← bsign_mul_add_distrib, ← bsign_mul_add_right]

-- Theorem 2C.1 (`bbochner_weil_conv_eq_gram_sos`):
-- Universal Arbitrary-Dimension Explicit-Formula / Bochner-Parseval Identity!
-- Evaluating `c^T (∑_r d_r φ_r φ_r^T) c` equals `∑_r d_r (φ_r · c)^2` IDENTICALLY (`=`)!
theorem bbochner_weil_conv_eq_gram_sos (d : BVec) (rows : BMat) (c : BVec) :
    bquad_form_eval (bgram_sum_mat d rows) c = bldlt_sos_eval d rows c := by
  unfold bquad_form_eval
  induction d generalizing rows with
  | vnil => rfl
  | vcons dk ds ih =>
    cases rows with
    | mnil => rfl
    | mcons phi phs =>
      dsimp only [bgram_sum_mat, bldlt_sos_eval]
      rw [bquad_row_eval_add, bquad_row_eval_outer, bvec_dot_comm c phi, ih phs]

-- Theorem 2C.2 (`bbochner_weil_gram_nonneg`):
-- Immediate Positivity Corollary: Any Gram sum `∑_r d_r φ_r φ_r^T` with `d_r >= 0` is PSD in all dimensions!
theorem bbochner_weil_gram_nonneg (d : BVec) (rows : BMat) (c : BVec)
    (hd : bvec_all_nonneg d) :
    bsign_le bsign_zero (bquad_form_eval (bgram_sum_mat d rows) c) := by
  rw [bbochner_weil_conv_eq_gram_sos]
  exact bldlt_sos_nonneg_universal d rows c hd

-- Theorem 2D (`bdirichlet_char_twist_dominance`):
-- Every real Dirichlet character value `chi in {0, +1, -1}` satisfies
--   `-w <= chi * w <= +w` and `(chi * w)^2 <= w^2` for every non-negative weight `w = +u`!
def IsRealCharVal (chi : BSignPair) : Prop :=
  chi = bsign_zero ∨ chi = bsign_one ∨ chi = bsign_neg bsign_one

theorem bdirichlet_char_twist_dominance (chi : BSignPair) (u : BBin)
    (hchi : IsRealCharVal chi) :
    let w := bsign_nonneg_of u
    bsign_le (bsign_neg w) (bsign_mul chi w) ∧
    bsign_le (bsign_mul chi w) w ∧
    bsign_le (bsign_mul (bsign_mul chi w) (bsign_mul chi w)) (bsign_mul w w) := by
  intro w
  rcases hchi with rfl | rfl | rfl
  · refine ⟨⟨u, ?_⟩, ⟨u, ?_⟩, ⟨bmul u u, ?_⟩⟩
    · rw [bsign_mul_zero_left, bsign_add_comm]; exact bsign_add_neg_cancel w
    · rw [bsign_mul_zero_left, bsign_add_zero_left]; exact bsign_equiv_refl w
    · rw [bsign_mul_zero_left, bsign_mul_zero_left, bsign_add_zero_left]
      unfold w; rw [bsign_nonneg_mul]; exact bsign_equiv_refl _
  · refine ⟨⟨badd u u, ?_⟩, ?_, ?_⟩
    · rw [bsign_mul_one_left, ← bsign_nonneg_add, ← bsign_add_assoc]
      have hnw : bsign_equiv (bsign_add (bsign_neg w) w) bsign_zero := by
        rw [bsign_add_comm]; exact bsign_add_neg_cancel w
      exact bsign_equiv_trans _ (bsign_add bsign_zero w) _
        (bsign_add_congr _ _ _ _ hnw (bsign_equiv_refl w))
        (by rw [bsign_add_zero_left]; exact bsign_equiv_refl w)
    · rw [bsign_mul_one_left]; exact bsign_le_refl w
    · rw [bsign_mul_one_left]; exact bsign_le_refl (bsign_mul w w)
  · refine ⟨?_, ⟨badd u u, ?_⟩, ?_⟩
    · rw [bsign_mul_neg_left, bsign_mul_one_left]; exact bsign_le_refl (bsign_neg w)
    · rw [bsign_mul_neg_left, bsign_mul_one_left, ← bsign_nonneg_add, ← bsign_add_assoc]
      have hnw : bsign_equiv (bsign_add (bsign_neg w) w) bsign_zero := by
        rw [bsign_add_comm]; exact bsign_add_neg_cancel w
      exact bsign_equiv_trans _ (bsign_add bsign_zero w) _
        (bsign_add_congr _ _ _ _ hnw (bsign_equiv_refl w))
        (by rw [bsign_add_zero_left]; exact bsign_equiv_refl w)
    · rw [bsign_mul_neg_left, bsign_mul_one_left, bsign_mul_neg_left, bsign_mul_neg_right, bsign_neg_invol]
      exact bsign_le_refl (bsign_mul w w)

end SiliconBigBang
