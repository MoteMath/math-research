/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MersenneFermatBitfoldCrt.Defs

/-!
# Proofs (`mersenne-fermat-bitfold-crt`)

Bit-folding programs, symbolic envelope compiler, Mersenne and Fermat thresholds, carry conservation, dyadic Fermat-Mersenne tower and CRT idempotents.
-/

namespace BitFoldEngine


-- ============================================================================
-- Section 0: Small Arithmetic Helpers (Core Lean 4.36.0 only)
-- ============================================================================

theorem two_pow_pos (n : Nat) : (0 : Int) < (2 : Int) ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Int.pow_succ]
    omega

theorem two_pow_ge_two {k : Nat} (hk : 1 ≤ k) : (2 : Int) ≤ (2 : Int) ^ k := by
  cases k with
  | zero => omega
  | succ m =>
    have h := two_pow_pos m
    rw [Int.pow_succ]
    omega

theorem nat_two_pow_pos (n : Nat) : 0 < 2 ^ n := Nat.two_pow_pos n

theorem nat_two_pow_ge_two {k : Nat} (hk : 1 ≤ k) : 2 ≤ 2 ^ k := by
  cases k with
  | zero => omega
  | succ m =>
    have h := Nat.two_pow_pos m
    rw [Nat.pow_succ]
    omega

theorem cast_nat_add (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by omega

theorem cast_nat_mul (a b : Nat) : ((a * b : Nat) : Int) = (a : Int) * (b : Int) := rfl

theorem cast_nat_pow (a n : Nat) : ((a ^ n : Nat) : Int) = (a : Int) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.pow_succ, Int.pow_succ, cast_nat_mul, ih]

-- ============================================================================
-- Section 1: Multi-Level Bit-Folding Language & Congruence Compiler
-- ============================================================================

inductive FoldSign where
  | pos  -- Mersenne fold: x ↦ (x mod 2^(m*k)) + (x / 2^(m*k))  [mod 2^(m*k) - 1]
  | neg  -- Fermat fold:   x ↦ (x mod 2^(m*k)) - (x / 2^(m*k))  [mod 2^(m*k) + 1]
  deriving DecidableEq, Repr

structure FoldStep where
  mult : Nat
  sign : FoldSign
  deriving DecidableEq, Repr

def modulus (k : Nat) : FoldSign → Int
  | .pos => (2 : Int) ^ k - 1
  | .neg => (2 : Int) ^ k + 1

theorem modulus_pos {k : Nat} (hk : 1 ≤ k) (s : FoldSign) : (0 : Int) < modulus k s := by
  have h2 := two_pow_ge_two hk
  cases s <;> simp [modulus] <;> omega

def evalStep (k : Nat) (st : FoldStep) (x : Int) : Int :=
  let w : Int := (2 : Int) ^ (st.mult * k)
  match st.sign with
  | .pos => x % w + x / w
  | .neg => x % w - x / w

def evalProg (k : Nat) (prog : List FoldStep) (x : Int) : Int :=
  prog.foldl (fun acc st => evalStep k st acc) x

def checkStepCong (target : FoldSign) (st : FoldStep) : Bool :=
  (st.mult ≥ 1) &&
  match target with
  | .pos => st.sign == .pos
  | .neg => (st.sign == .pos) == (st.mult % 2 == 0)

def checkCong (target : FoldSign) (prog : List FoldStep) : Bool :=
  prog.all (checkStepCong target)

/-- Core divisibility lemma: `(2^k - 1) ∣ (2^(m*k) - 1)` for all `m`. -/
theorem mersenne_dvd_mersenne (k m : Nat) :
    ((2 : Int) ^ k - 1) ∣ ((2 : Int) ^ (m * k) - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rcases ih with ⟨q, hq⟩
    refine ⟨(2 : Int) ^ k * q + 1, ?_⟩
    have hpow : (2 : Int) ^ ((m + 1) * k) = (2 : Int) ^ k * (2 : Int) ^ (m * k) := by
      rw [Nat.succ_mul, Int.pow_add, Int.mul_comm]
    rw [hpow]
    have h1 : (2 : Int) ^ (m * k) = ((2 : Int) ^ k - 1) * q + 1 := by omega
    rw [h1]
    calc (2 : Int) ^ k * (((2 : Int) ^ k - 1) * q + 1) - 1
        = ((2 : Int) ^ k - 1) * ((2 : Int) ^ k * q) + ((2 : Int) ^ k - 1) := by
            rw [Int.mul_add, Int.mul_one, ← Int.mul_assoc, Int.mul_comm ((2 : Int) ^ k) ((2 : Int) ^ k - 1),
                Int.mul_assoc, Int.add_sub_assoc]
      _ = ((2 : Int) ^ k - 1) * ((2 : Int) ^ k * q + 1) := by
            rw [Int.mul_add, Int.mul_one]

/-- Parity divisibility law for Fermat modulus `2^k + 1`:
    - `m` even → `(2^k + 1) ∣ (2^(m*k) - 1)`
    - `m` odd  → `(2^k + 1) ∣ (2^(m*k) + 1)` -/
theorem fermat_parity_dvd (k m : Nat) :
    ((2 : Int) ^ k + 1) ∣ ((2 : Int) ^ (m * k) - if m % 2 = 0 then (1 : Int) else -1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hpow : (2 : Int) ^ ((m + 1) * k) = (2 : Int) ^ k * (2 : Int) ^ (m * k) := by
      rw [Nat.succ_mul, Int.pow_add, Int.mul_comm]
    by_cases hm : m % 2 = 0
    · have hms : (m + 1) % 2 = 1 := by omega
      simp only [hm, ↓reduceIte] at ih
      simp only [hms, show (1 : Nat) ≠ 0 by decide, ↓reduceIte]
      rcases ih with ⟨q, hq⟩
      refine ⟨(2 : Int) ^ k * q + 1, ?_⟩
      rw [hpow]
      have h1 : (2 : Int) ^ (m * k) = ((2 : Int) ^ k + 1) * q + 1 := by omega
      rw [h1]
      have : (2 : Int) ^ k * (((2 : Int) ^ k + 1) * q + 1) - (-1)
           = ((2 : Int) ^ k + 1) * ((2 : Int) ^ k * q + 1) := by
        rw [Int.mul_add, Int.mul_one, ← Int.mul_assoc,
            Int.mul_comm ((2 : Int) ^ k) ((2 : Int) ^ k + 1), Int.mul_assoc,
            Int.mul_add, Int.mul_one]
        omega
      exact this
    · have hms : (m + 1) % 2 = 0 := by omega
      simp only [hm, ↓reduceIte] at ih
      simp only [hms, ↓reduceIte]
      rcases ih with ⟨q, hq⟩
      refine ⟨(2 : Int) ^ k * q - 1, ?_⟩
      rw [hpow]
      have h1 : (2 : Int) ^ (m * k) = ((2 : Int) ^ k + 1) * q - 1 := by omega
      rw [h1]
      have : (2 : Int) ^ k * (((2 : Int) ^ k + 1) * q - 1) - 1
           = ((2 : Int) ^ k + 1) * ((2 : Int) ^ k * q - 1) := by
        rw [Int.mul_sub, Int.mul_one, ← Int.mul_assoc,
            Int.mul_comm ((2 : Int) ^ k) ((2 : Int) ^ k + 1), Int.mul_assoc,
            Int.mul_sub, Int.mul_one]
        omega
      exact this

theorem int_emod_eq_of_dvd_sub {a b m : Int} (h : m ∣ (a - b)) : a % m = b % m := by
  rcases h with ⟨q, hq⟩
  have ha : a = b + m * q := by omega
  rw [ha, Int.add_mul_emod_self_left]

theorem evalStep_congruent {target : FoldSign} {st : FoldStep}
    (hchk : checkStepCong target st = true) (k : Nat) (x : Int) :
    evalStep k st x % modulus k target = x % modulus k target := by
  have hdiv : x = (2 : Int) ^ (st.mult * k) * (x / (2 : Int) ^ (st.mult * k)) +
                  x % (2 : Int) ^ (st.mult * k) := by
    have h := Int.emod_add_mul_ediv x ((2 : Int) ^ (st.mult * k))
    omega
  cases target with
  | pos =>
    have hsign : st.sign = .pos := by
      simp [checkStepCong] at hchk
      exact hchk.2
    simp only [evalStep, hsign, modulus]
    apply int_emod_eq_of_dvd_sub
    have hdvd := mersenne_dvd_mersenne k st.mult
    rcases hdvd with ⟨q, hq⟩
    refine ⟨-(q * (x / (2 : Int) ^ (st.mult * k))), ?_⟩
    have hdiff : (x % (2 : Int) ^ (st.mult * k) + x / (2 : Int) ^ (st.mult * k)) - x =
        -(((2 : Int) ^ (st.mult * k) - 1) * (x / (2 : Int) ^ (st.mult * k))) := by
      rw [Int.sub_mul, Int.one_mul]
      omega
    rw [hdiff, hq, Int.mul_assoc, Int.mul_neg]
  | neg =>
    simp only [checkStepCong, Bool.and_eq_true, decide_eq_true_eq] at hchk
    have hpar := hchk.2
    have hdvd := fermat_parity_dvd k st.mult
    rcases hdvd with ⟨q, hq⟩
    cases hs : st.sign with
    | pos =>
      have heven : st.mult % 2 = 0 := by
        simp [hs] at hpar
        exact hpar
      simp only [heven, ↓reduceIte] at hq
      simp only [evalStep, hs, modulus]
      apply int_emod_eq_of_dvd_sub
      refine ⟨-(q * (x / (2 : Int) ^ (st.mult * k))), ?_⟩
      have hdiff : (x % (2 : Int) ^ (st.mult * k) + x / (2 : Int) ^ (st.mult * k)) - x =
          -(((2 : Int) ^ (st.mult * k) - 1) * (x / (2 : Int) ^ (st.mult * k))) := by
        rw [Int.sub_mul, Int.one_mul]
        omega
      rw [hdiff, hq, Int.mul_assoc, Int.mul_neg]
    | neg =>
      have hodd : st.mult % 2 ≠ 0 := by
        simp [hs] at hpar
        intro h0
        simp [h0] at hpar
      simp only [hodd, ↓reduceIte] at hq
      simp only [evalStep, hs, modulus]
      apply int_emod_eq_of_dvd_sub
      refine ⟨-(q * (x / (2 : Int) ^ (st.mult * k))), ?_⟩
      have hdiff : (x % (2 : Int) ^ (st.mult * k) - x / (2 : Int) ^ (st.mult * k)) - x =
          -(((2 : Int) ^ (st.mult * k) - (-1)) * (x / (2 : Int) ^ (st.mult * k))) := by
        rw [Int.sub_mul]
        omega
      rw [hdiff, hq, Int.mul_assoc, Int.mul_neg]

/-- **Theorem 1 (Finite-to-Infinite Congruence Compiler):**
    Any finite folding program accepted by `checkCong target prog` preserves
    residues modulo `2^k - 1` (if `target = .pos`) or `2^k + 1` (if `target = .neg`)
    for ALL `k ≥ 1` and ALL `x : Int`. -/
theorem prog_congruent_of_check (target : FoldSign) (prog : List FoldStep)
    (hchk : checkCong target prog = true) (k : Nat) (x : Int) :
    evalProg k prog x % modulus k target = x % modulus k target := by
  induction prog generalizing x with
  | nil => rfl
  | cons st rest ih =>
    simp only [checkCong, List.all_cons, Bool.and_eq_true] at hchk
    change evalProg k rest (evalStep k st x) % modulus k target = x % modulus k target
    rw [ih hchk.2 (evalStep k st x), evalStep_congruent hchk.1 k x]

/-- **Sharpness Witness 1:** Violating the stride-parity law (`F(2)` for target `2^k + 1`)
    breaks congruence for EVERY `k ≥ 1` at `x = 2^(2k)`. -/
theorem fermat_even_stride_neg_fails (k : Nat) (hk : 1 ≤ k) :
    evalProg k [⟨2, .neg⟩] ((2 : Int) ^ (2 * k)) % modulus k .neg ≠
    ((2 : Int) ^ (2 * k)) % modulus k .neg := by
  have hpos : (0 : Int) < (2 : Int) ^ (2 * k) := two_pow_pos (2 * k)
  have hstep : evalProg k [⟨2, .neg⟩] ((2 : Int) ^ (2 * k)) = -1 := by
    simp [evalProg, evalStep, Int.emod_self, Int.ediv_self (Int.ne_of_gt hpos)]
  rw [hstep]
  have h2k : (2 : Int) ^ (2 * k) = ((2 : Int) ^ k + 1) * ((2 : Int) ^ k - 1) + 1 := by
    have hp : (2 : Int) ^ (2 * k) = (2 : Int) ^ k * (2 : Int) ^ k := by
      rw [Nat.two_mul, Int.pow_add]
    rw [hp, Int.add_mul, Int.mul_sub, Int.mul_one, Int.one_mul]
    omega
  have hm_ge3 : (3 : Int) ≤ modulus k .neg := by
    have := two_pow_ge_two hk
    simp [modulus]; omega
  have hlhs : (-1 : Int) % modulus k .neg = modulus k .neg - 1 := by
    have h1 : (-1 : Int) = modulus k .neg * (-1) + (modulus k .neg - 1) := by omega
    rw [h1, Int.mul_add_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
  have hrhs : ((2 : Int) ^ (2 * k)) % modulus k .neg = 1 := by
    rw [h2k]
    simp only [modulus]
    rw [Int.mul_add_emod_self_left, Int.emod_eq_of_lt (by omega) (by simp [modulus] at hm_ge3; omega)]
  rw [hlhs, hrhs]
  omega

-- ============================================================================
-- Section 2: Symbolic Base-B Polynomial Envelope Compiler (Finite → Infinite)
-- ============================================================================

abbrev SymPoly := List Int

def evalPoly (B : Int) : SymPoly → Int
  | [] => 0
  | c :: cs => c + B * evalPoly B cs

def polyAdd : SymPoly → SymPoly → SymPoly
  | [], q => q
  | p, [] => p
  | a :: ps, b :: qs => (a + b) :: polyAdd ps qs

def polyNeg (p : SymPoly) : SymPoly := p.map (- ·)

def polySub (p q : SymPoly) : SymPoly := polyAdd p (polyNeg q)

def polyScale (a : Int) (p : SymPoly) : SymPoly := p.map (a * ·)

def polyMul : SymPoly → SymPoly → SymPoly
  | [], _ => []
  | a :: ps, q => polyAdd (polyScale a q) (0 :: polyMul ps q)

def polyMonomial : Nat → Int → SymPoly
  | 0, c => [c]
  | m + 1, c => 0 :: polyMonomial m c

/-- `shiftPoly B0 p` computes `Q(t) = P(t + B0)` so `evalPoly B p = evalPoly (B - B0) Q`. -/
def shiftPoly (B0 : Int) : SymPoly → SymPoly
  | [] => []
  | c :: cs => polyAdd [c] (polyMul [B0, 1] (shiftPoly B0 cs))

def isNonnegFrom (B0 : Int) (p : SymPoly) : Bool :=
  (shiftPoly B0 p).all (fun c => decide (0 ≤ c))

def symLe (B0 : Int) (p q : SymPoly) : Bool :=
  isNonnegFrom B0 (polySub q p)

def symLt (B0 : Int) (p q : SymPoly) : Bool :=
  isNonnegFrom B0 (polySub (polySub q p) [1])

theorem evalPoly_add (B : Int) (p q : SymPoly) :
    evalPoly B (polyAdd p q) = evalPoly B p + evalPoly B q := by
  induction p generalizing q with
  | nil => simp [polyAdd, evalPoly]
  | cons a ps ih =>
    cases q with
    | nil => simp [polyAdd, evalPoly]
    | cons b qs =>
      simp only [polyAdd, evalPoly, ih qs, Int.mul_add]
      omega

theorem evalPoly_neg (B : Int) (p : SymPoly) :
    evalPoly B (polyNeg p) = -evalPoly B p := by
  induction p with
  | nil => simp [polyNeg, evalPoly]
  | cons a ps ih =>
    simp only [polyNeg, List.map_cons, evalPoly] at *
    rw [ih, Int.mul_neg]
    omega

theorem evalPoly_sub (B : Int) (p q : SymPoly) :
    evalPoly B (polySub p q) = evalPoly B p - evalPoly B q := by
  rw [polySub, evalPoly_add, evalPoly_neg]
  omega

theorem evalPoly_scale (B a : Int) (p : SymPoly) :
    evalPoly B (polyScale a p) = a * evalPoly B p := by
  induction p with
  | nil => simp [polyScale, evalPoly]
  | cons c cs ih =>
    simp only [polyScale, List.map_cons, evalPoly] at *
    rw [ih, Int.mul_add, ← Int.mul_assoc, Int.mul_comm B a, Int.mul_assoc]

theorem evalPoly_mul (B : Int) (p q : SymPoly) :
    evalPoly B (polyMul p q) = evalPoly B p * evalPoly B q := by
  induction p with
  | nil => simp [polyMul, evalPoly]
  | cons a ps ih =>
    simp only [polyMul, evalPoly_add, evalPoly_scale, evalPoly, ih, Int.add_mul, Int.mul_assoc]
    omega

theorem evalPoly_monomial (B c : Int) (m : Nat) :
    evalPoly B (polyMonomial m c) = c * B ^ m := by
  induction m with
  | zero => simp [polyMonomial, evalPoly]
  | succ m ih =>
    simp only [polyMonomial, evalPoly, ih, Int.zero_add, Int.pow_succ]
    rw [← Int.mul_assoc, Int.mul_comm B c, Int.mul_assoc, Int.mul_comm B (B ^ m)]

theorem evalPoly_shift (B B0 : Int) (p : SymPoly) :
    evalPoly (B - B0) (shiftPoly B0 p) = evalPoly B p := by
  induction p with
  | nil => simp [shiftPoly, evalPoly]
  | cons c cs ih =>
    simp only [shiftPoly, evalPoly_add, evalPoly_mul, evalPoly, ih]
    have h1 : B0 + (B - B0) * (1 + (B - B0) * 0) = B := by omega
    rw [h1]
    omega

theorem evalPoly_nonneg_of_all_nonneg {t : Int} (ht : 0 ≤ t) {q : SymPoly}
    (hall : q.all (fun c => decide (0 ≤ c)) = true) : 0 ≤ evalPoly t q := by
  induction q with
  | nil => simp [evalPoly]
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hall
    simp only [evalPoly]
    have hrec := ih hall.2
    have hmul : 0 ≤ t * evalPoly t cs := Int.mul_nonneg ht hrec
    omega

theorem evalPoly_nonneg_of_check {B0 B : Int} {p : SymPoly}
    (hchk : isNonnegFrom B0 p = true) (hB : B0 ≤ B) : 0 ≤ evalPoly B p := by
  rw [← evalPoly_shift B B0 p]
  exact evalPoly_nonneg_of_all_nonneg (by omega) hchk

theorem evalPoly_le_of_symLe {B0 B : Int} {p q : SymPoly}
    (hchk : symLe B0 p q = true) (hB : B0 ≤ B) : evalPoly B p ≤ evalPoly B q := by
  have h := evalPoly_nonneg_of_check hchk hB
  rw [evalPoly_sub] at h
  omega

theorem evalPoly_lt_of_symLt {B0 B : Int} {p q : SymPoly}
    (hchk : symLt B0 p q = true) (hB : B0 ≤ B) : evalPoly B p < evalPoly B q := by
  have h := evalPoly_nonneg_of_check hchk hB
  simp only [evalPoly_sub, evalPoly] at h
  omega

theorem evalPoly_take_drop (B : Int) (m : Nat) (p : SymPoly) :
    evalPoly B p = evalPoly B (p.take m) + B ^ m * evalPoly B (p.drop m) := by
  induction m generalizing p with
  | zero => simp [evalPoly]
  | succ m ih =>
    cases p with
    | nil => simp [evalPoly]
    | cons c cs =>
      simp only [List.take_succ_cons, List.drop_succ_cons, evalPoly]
      rw [ih cs, Int.mul_add, Int.pow_succ, Int.mul_comm (B ^ m) B, Int.mul_assoc]
      omega

/-- Exact symbolic Euclidean division by `B^m` with decidable range verification. -/
def tryDivModAdj (B0 : Int) (m : Nat) (q0 r0 : SymPoly) (adj : Int) : Option (SymPoly × SymPoly) :=
  let q := polyAdd q0 [adj]
  let r := polySub r0 (polyMonomial m adj)
  if symLe B0 [] r && symLt B0 r (polyMonomial m 1) then some (q, r) else none

def symDivMod (B0 : Int) (m : Nat) (p : SymPoly) : Option (SymPoly × SymPoly) :=
  let r0 := p.take m
  let q0 := p.drop m
  let guess := evalPoly B0 r0 / (B0 ^ m)
  let cands : List Int := [0, guess, -1, 1, guess - 1, guess + 1]
  cands.findSome? (tryDivModAdj B0 m q0 r0)

theorem tryDivModAdj_sound {B0 B : Int} {m : Nat} {p : SymPoly} {adj : Int} {q r : SymPoly}
    (hB : B0 ≤ B) (h : tryDivModAdj B0 m (p.drop m) (p.take m) adj = some (q, r)) :
    evalPoly B p = B ^ m * evalPoly B q + evalPoly B r ∧
    0 ≤ evalPoly B r ∧ evalPoly B r < B ^ m := by
  simp only [tryDivModAdj] at h
  split at h
  · rename_i hcond
    injection h with hqr
    have hq : q = polyAdd (p.drop m) [adj] := congrArg Prod.fst hqr.symm
    have hr : r = polySub (p.take m) (polyMonomial m adj) := congrArg Prod.snd hqr.symm
    simp only [Bool.and_eq_true] at hcond
    have hr_nonneg := evalPoly_le_of_symLe hcond.1 hB
    have hr_lt := evalPoly_lt_of_symLt hcond.2 hB
    rw [evalPoly] at hr_nonneg
    rw [evalPoly_monomial, Int.one_mul] at hr_lt
    rw [← hr] at hr_nonneg hr_lt
    refine ⟨?_, hr_nonneg, hr_lt⟩
    rw [hq, hr, evalPoly_add, evalPoly_sub, evalPoly_monomial, evalPoly, evalPoly]
    have htd := evalPoly_take_drop B m p
    have h0 : adj + B * 0 = adj := by omega
    rw [h0, htd, Int.mul_add, Int.mul_comm (B ^ m) adj]
    omega
  · cases h

theorem findSome_sound {α β : Type} {f : α → Option β} {xs : List α} {y : β}
    (h : xs.findSome? f = some y) : ∃ x ∈ xs, f x = some y := by
  induction xs with
  | nil => simp at h
  | cons a as ih =>
    simp only [List.findSome?_cons] at h
    cases hfa : f a with
    | none =>
      rw [hfa] at h
      rcases ih h with ⟨x, hx, hfx⟩
      exact ⟨x, List.mem_cons_of_mem a hx, hfx⟩
    | some b =>
      rw [hfa] at h
      injection h with hby
      subst hby
      exact ⟨a, List.mem_cons_self, hfa⟩

theorem symDivMod_sound {B0 B : Int} {m : Nat} {p q r : SymPoly}
    (hB : B0 ≤ B) (h : symDivMod B0 m p = some (q, r)) :
    evalPoly B p = B ^ m * evalPoly B q + evalPoly B r ∧
    0 ≤ evalPoly B r ∧ evalPoly B r < B ^ m := by
  simp only [symDivMod] at h
  rcases findSome_sound h with ⟨adj, _, hadj⟩
  exact tryDivModAdj_sound hB hadj

/-- One symbolic abstract-interpretation step for `FoldStep` on envelope `(L, U)`. -/
def stepSymEnv (B0 : Int) (st : FoldStep) (env : SymPoly × SymPoly) : Option (SymPoly × SymPoly) :=
  let (L, U) := env
  if !symLe B0 L U then none
  else
    match symDivMod B0 st.mult L, symDivMod B0 st.mult U with
    | some (qL, rL), some (qU, rU) =>
      let bm_m1 := polySub (polyMonomial st.mult 1) [1]
      let bm_m2 := polySub (polyMonomial st.mult 1) [2]
      let sameQ := symLe B0 qU qL
      match st.sign with
      | .pos =>
        if sameQ then some (polyAdd rL qL, polyAdd rU qU)
        else if symLe B0 rU bm_m2 then some (qL, polyAdd qU bm_m2)
        else some (qL, polyAdd qU bm_m1)
      | .neg =>
        if sameQ then some (polySub rL qU, polySub rU qL)
        else some (polyNeg qU, polySub bm_m1 qL)
    | _, _ => none

def runSymEnv (B0 : Int) : List FoldStep → SymPoly × SymPoly → Option (SymPoly × SymPoly)
  | [], env => some env
  | st :: rest, env =>
    match stepSymEnv B0 st env with
    | none => none
    | some env' => runSymEnv B0 rest env'

def checkCircuit (target : FoldSign) (B0 : Int) (prog : List FoldStep)
    (initEnv goalEnv : SymPoly × SymPoly) : Bool :=
  checkCong target prog &&
  match runSymEnv B0 prog initEnv with
  | none => false
  | some (L_out, U_out) => symLe B0 goalEnv.1 L_out && symLe B0 U_out goalEnv.2

theorem int_ediv_unique {x w q r : Int} (hw : 0 < w)
    (heq : x = w * q + r) (hr0 : 0 ≤ r) (hrw : r < w) :
    x / w = q ∧ x % w = r := by
  have hq : x / w = q := by
    rw [heq, Int.mul_add_ediv_left _ _ (Int.ne_of_gt hw), Int.ediv_eq_zero_of_lt hr0 hrw]
    omega
  have hr : x % w = r := by
    rw [heq, Int.mul_add_emod_self_left, Int.emod_eq_of_lt hr0 hrw]
  exact ⟨hq, hr⟩

theorem int_ediv_mono {a b w : Int} (hw : 0 < w) (hab : a ≤ b) : a / w ≤ b / w := by
  have ha := Int.emod_add_mul_ediv a w
  have hb := Int.emod_add_mul_ediv b w
  have hra0 := Int.emod_nonneg a (Int.ne_of_gt hw)
  have hraw := Int.emod_lt_of_pos a hw
  have hrb0 := Int.emod_nonneg b (Int.ne_of_gt hw)
  have hrbw := Int.emod_lt_of_pos b hw
  exact Decidable.byContradiction fun hlt => by
    have hge : b / w + 1 ≤ a / w := by omega
    have hmul : w * (b / w + 1) ≤ w * (a / w) := Int.mul_le_mul_of_nonneg_left hge (by omega)
    rw [Int.mul_add, Int.mul_one] at hmul
    omega

theorem stepSymEnv_sound {B0 : Int} {k : Nat} {st : FoldStep} {L U L' U' : SymPoly}
    (_hk : 1 ≤ k) (hB : B0 ≤ (2 : Int) ^ k)
    (hstep : stepSymEnv B0 st (L, U) = some (L', U'))
    {x : Int} (hxL : evalPoly ((2 : Int) ^ k) L ≤ x) (hxU : x ≤ evalPoly ((2 : Int) ^ k) U) :
    evalPoly ((2 : Int) ^ k) L' ≤ evalStep k st x ∧
    evalStep k st x ≤ evalPoly ((2 : Int) ^ k) U' := by
  let B : Int := (2 : Int) ^ k
  let w : Int := (2 : Int) ^ (st.mult * k)
  have hw_eq : w = B ^ st.mult := by
    change (2 : Int) ^ (st.mult * k) = ((2 : Int) ^ k) ^ st.mult
    rw [Nat.mul_comm, Int.pow_mul]
  have hw_pos : 0 < w := two_pow_pos (st.mult * k)
  simp only [stepSymEnv] at hstep
  split at hstep
  · cases hstep
  · cases hdmL : symDivMod B0 st.mult L with
    | none => rw [hdmL] at hstep; cases hstep
    | some qrL =>
      rcases qrL with ⟨qL, rL⟩
      cases hdmU : symDivMod B0 st.mult U with
      | none => rw [hdmL, hdmU] at hstep; cases hstep
      | some qrU =>
        rcases qrU with ⟨qU, rU⟩
        rw [hdmL, hdmU] at hstep
        have ⟨heqL, hrL0, hrLw⟩ := symDivMod_sound hB hdmL
        have ⟨heqU, hrU0, hrUw⟩ := symDivMod_sound hB hdmU
        change evalPoly B L = B ^ st.mult * evalPoly B qL + evalPoly B rL at heqL
        change evalPoly B U = B ^ st.mult * evalPoly B qU + evalPoly B rU at heqU
        change 0 ≤ evalPoly B rL at hrL0
        change evalPoly B rL < B ^ st.mult at hrLw
        change 0 ≤ evalPoly B rU at hrU0
        change evalPoly B rU < B ^ st.mult at hrUw
        rw [← hw_eq] at heqL hrLw heqU hrUw
        have ⟨hqL_eq, hrL_eq⟩ := int_ediv_unique hw_pos heqL hrL0 hrLw
        have ⟨hqU_eq, hrU_eq⟩ := int_ediv_unique hw_pos heqU hrU0 hrUw
        have hq_ge : evalPoly B qL ≤ x / w := by
          rw [← hqL_eq]; exact int_ediv_mono hw_pos hxL
        have hq_le : x / w ≤ evalPoly B qU := by
          rw [← hqU_eq]; exact int_ediv_mono hw_pos hxU
        have hr_nonneg : 0 ≤ x % w := Int.emod_nonneg x (Int.ne_of_gt hw_pos)
        have hr_lt : x % w < w := Int.emod_lt_of_pos x hw_pos
        have hx_split : x = w * (x / w) + x % w := by
          have := Int.emod_add_mul_ediv x w; omega
        have hr_ge_if_eqL : x / w = evalPoly B qL → evalPoly B rL ≤ x % w := by
          intro hq
          have hxL' : evalPoly B L ≤ x := hxL
          rw [hq] at hx_split; omega
        have hr_le_if_eqU : x / w = evalPoly B qU → x % w ≤ evalPoly B rU := by
          intro hq
          have hxU' : x ≤ evalPoly B U := hxU
          rw [hq] at hx_split; omega
        cases hsign : st.sign with
        | pos =>
          rw [hsign] at hstep
          dsimp only at hstep
          simp only [evalStep, hsign]
          change evalPoly B L' ≤ x % w + x / w ∧ x % w + x / w ≤ evalPoly B U'
          by_cases hsame : symLe B0 qU qL = true
          · rw [hsame] at hstep
            simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hstep
            rcases hstep with ⟨rfl, rfl⟩
            have hqU_le_qL : evalPoly B qU ≤ evalPoly B qL := evalPoly_le_of_symLe hsame hB
            have hq_eq : x / w = evalPoly B qL := by omega
            have hq_eq' : x / w = evalPoly B qU := by omega
            have h1 := hr_ge_if_eqL hq_eq
            have h2 := hr_le_if_eqU hq_eq'
            simp only [evalPoly_add]; omega
          · simp only [hsame, Bool.false_eq_true, ↓reduceIte] at hstep
            by_cases hrU_small : symLe B0 rU (polySub (polyMonomial st.mult 1) [2]) = true
            · rw [hrU_small] at hstep
              simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hstep
              rcases hstep with ⟨rfl, rfl⟩
              have hrU_bd : evalPoly B rU ≤ evalPoly B (polySub (polyMonomial st.mult 1) [2]) :=
                evalPoly_le_of_symLe hrU_small hB
              simp only [evalPoly_sub, evalPoly_monomial, evalPoly, Int.one_mul, ← hw_eq] at hrU_bd
              simp only [evalPoly_add, evalPoly_sub, evalPoly_monomial, evalPoly, Int.one_mul, ← hw_eq]
              constructor
              · omega
              · by_cases htop : x / w = evalPoly B qU
                · have := hr_le_if_eqU htop; omega
                · omega
            · simp only [hrU_small, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hstep
              rcases hstep with ⟨rfl, rfl⟩
              simp only [evalPoly_add, evalPoly_sub, evalPoly_monomial, evalPoly, Int.one_mul, ← hw_eq]
              omega
        | neg =>
          rw [hsign] at hstep
          dsimp only at hstep
          simp only [evalStep, hsign]
          change evalPoly B L' ≤ x % w - x / w ∧ x % w - x / w ≤ evalPoly B U'
          by_cases hsame : symLe B0 qU qL = true
          · rw [hsame] at hstep
            simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hstep
            rcases hstep with ⟨rfl, rfl⟩
            have hqU_le_qL : evalPoly B qU ≤ evalPoly B qL := evalPoly_le_of_symLe hsame hB
            have hq_eq : x / w = evalPoly B qL := by omega
            have hq_eq' : x / w = evalPoly B qU := by omega
            have h1 := hr_ge_if_eqL hq_eq
            have h2 := hr_le_if_eqU hq_eq'
            simp only [evalPoly_sub]; omega
          · simp only [hsame, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hstep
            rcases hstep with ⟨rfl, rfl⟩
            simp only [evalPoly_neg, evalPoly_sub, evalPoly_monomial, evalPoly, Int.one_mul, ← hw_eq]
            omega

theorem runSymEnv_sound {B0 : Int} {k : Nat} {prog : List FoldStep} {env env' : SymPoly × SymPoly}
    (hk : 1 ≤ k) (hB : B0 ≤ (2 : Int) ^ k)
    (hrun : runSymEnv B0 prog env = some env')
    {x : Int} (hxL : evalPoly ((2 : Int) ^ k) env.1 ≤ x)
    (hxU : x ≤ evalPoly ((2 : Int) ^ k) env.2) :
    evalPoly ((2 : Int) ^ k) env'.1 ≤ evalProg k prog x ∧
    evalProg k prog x ≤ evalPoly ((2 : Int) ^ k) env'.2 := by
  induction prog generalizing env x with
  | nil =>
    simp only [runSymEnv, Option.some.injEq] at hrun
    subst hrun
    exact ⟨hxL, hxU⟩
  | cons st rest ih =>
    simp only [runSymEnv] at hrun
    cases hs : stepSymEnv B0 st env with
    | none => rw [hs] at hrun; cases hrun
    | some env1 =>
      rw [hs] at hrun
      have ⟨h1, h2⟩ := stepSymEnv_sound hk hB hs hxL hxU
      exact ih hrun h1 h2

/-- **Theorem 2 (Master Finite-to-Infinite Bit-Folding Circuit Compiler Soundness):**
    If the finite boolean check `checkCircuit target B0 prog initEnv goalEnv = true`,
    then for ALL `k ≥ 1` with `2^k ≥ B0` and ALL `x` in `initEnv(2^k)`:
    1. `evalProg k prog x ≡ x (mod 2^k ± 1)` (exact congruence)
    2. `evalProg k prog x ∈ goalEnv(2^k)` (exact carry-absorption envelope). -/
theorem circuit_sound_of_check (target : FoldSign) (B0 : Int) (prog : List FoldStep)
    (initEnv goalEnv : SymPoly × SymPoly)
    (hchk : checkCircuit target B0 prog initEnv goalEnv = true)
    {k : Nat} (hk : 1 ≤ k) (hB : B0 ≤ (2 : Int) ^ k)
    {x : Int} (hxL : evalPoly ((2 : Int) ^ k) initEnv.1 ≤ x)
    (hxU : x ≤ evalPoly ((2 : Int) ^ k) initEnv.2) :
    evalProg k prog x % modulus k target = x % modulus k target ∧
    evalPoly ((2 : Int) ^ k) goalEnv.1 ≤ evalProg k prog x ∧
    evalProg k prog x ≤ evalPoly ((2 : Int) ^ k) goalEnv.2 := by
  simp only [checkCircuit, Bool.and_eq_true] at hchk
  rcases hchk with ⟨hcong, hrun_chk⟩
  cases hrun : runSymEnv B0 prog initEnv with
  | none => rw [hrun] at hrun_chk; cases hrun_chk
  | some outEnv =>
    rw [hrun] at hrun_chk
    simp only [Bool.and_eq_true] at hrun_chk
    have ⟨hL_out, hU_out⟩ := runSymEnv_sound hk hB hrun hxL hxU
    have hL_goal := evalPoly_le_of_symLe hrun_chk.1 hB
    have hU_goal := evalPoly_le_of_symLe hrun_chk.2 hB
    exact ⟨prog_congruent_of_check target prog hcong k x, by omega, by omega⟩

/-- **Canonical Fermat Compiler Corollary:**
    Any Fermat circuit whose certified output envelope fits in `[0, 2^k]` computes
    the EXACT branchless non-negative Euclidean remainder `x % (2^k + 1)`! -/
theorem canonical_fermat_circuit_of_check (B0 : Int) (prog : List FoldStep)
    (initEnv : SymPoly × SymPoly)
    (hchk : checkCircuit .neg B0 prog initEnv ([], [0, 1]) = true)
    {k : Nat} (hk : 1 ≤ k) (hB : B0 ≤ (2 : Int) ^ k)
    {x : Int} (hxL : evalPoly ((2 : Int) ^ k) initEnv.1 ≤ x)
    (hxU : x ≤ evalPoly ((2 : Int) ^ k) initEnv.2) :
    evalProg k prog x = x % ((2 : Int) ^ k + 1) := by
  have ⟨hcong, hL, hU⟩ := circuit_sound_of_check .neg B0 prog initEnv ([], [0, 1]) hchk hk hB hxL hxU
  simp only [evalPoly, modulus] at hcong hL hU
  rw [← hcong]
  exact (Int.emod_eq_of_lt (by omega) (by omega)).symm

-- ============================================================================
-- Compiled Infinite Theorems (Each Discharged in 1 Line via `by decide`!)
-- ============================================================================

/-- Compiled Infinite Theorem 2.1: 2-round Mersenne EAC on any 2k-bit unsigned input
    absorbs all carries into `[0, 2^k - 1]` for ALL `k ≥ 1`. -/
theorem compiled_mersenne_2round_eac :
    ∀ (k : Nat), 1 ≤ k → ∀ (x : Int), 0 ≤ x → x ≤ (2 : Int) ^ (2 * k) - 1 →
      let y := evalProg k [⟨1, .pos⟩, ⟨1, .pos⟩] x
      y % ((2 : Int) ^ k - 1) = x % ((2 : Int) ^ k - 1) ∧ 0 ≤ y ∧ y ≤ (2 : Int) ^ k - 1 := by
  intro k hk x hx0 hxU
  have hchk : checkCircuit .pos 2 [⟨1, .pos⟩, ⟨1, .pos⟩] ([], [-1, 0, 1]) ([], [-1, 1]) = true := by
    decide
  have hU' : x ≤ evalPoly ((2 : Int) ^ k) [-1, 0, 1] := by
    simp [evalPoly]
    have hp : (2 : Int) ^ (2 * k) = (2 : Int) ^ k * (2 : Int) ^ k := by
      rw [Nat.two_mul, Int.pow_add]
    omega
  have hres := circuit_sound_of_check .pos 2 [⟨1, .pos⟩, ⟨1, .pos⟩] ([], [-1, 0, 1]) ([], [-1, 1])
    hchk hk (two_pow_ge_two hk) (by simp [evalPoly]; omega) hU'
  simp [evalPoly, modulus] at hres
  exact ⟨hres.1, by omega, by omega⟩

/-- Compiled Infinite Theorem 2.2: 4-step hybrid circuit `[M(2), M(2), F(1), F(1)]`
    computes EXACT branchless canonical `x % (2^k + 1)` on all `4k`-bit unsigned inputs
    for ALL `k ≥ 1`! -/
theorem compiled_fermat_4step_canonical :
    ∀ (k : Nat), 1 ≤ k → ∀ (x : Int), 0 ≤ x → x ≤ (2 : Int) ^ (4 * k) - 1 →
      evalProg k [⟨2, .pos⟩, ⟨2, .pos⟩, ⟨1, .neg⟩, ⟨1, .neg⟩] x = x % ((2 : Int) ^ k + 1) := by
  intro k hk x hx0 hxU
  have hchk : checkCircuit .neg 2 [⟨2, .pos⟩, ⟨2, .pos⟩, ⟨1, .neg⟩, ⟨1, .neg⟩]
      ([], [-1, 0, 0, 0, 1]) ([], [0, 1]) = true := by decide
  have hU' : x ≤ evalPoly ((2 : Int) ^ k) [-1, 0, 0, 0, 1] := by
    simp [evalPoly]
    have hp : (2 : Int) ^ (4 * k) =
        (2 : Int) ^ k * ((2 : Int) ^ k * ((2 : Int) ^ k * (2 : Int) ^ k)) := by
      have : 4 * k = k + (k + (k + k)) := by omega
      rw [this, Int.pow_add, Int.pow_add, Int.pow_add]
    omega
  exact canonical_fermat_circuit_of_check 2 [⟨2, .pos⟩, ⟨2, .pos⟩, ⟨1, .neg⟩, ⟨1, .neg⟩]
    ([], [-1, 0, 0, 0, 1]) hchk hk (two_pow_ge_two hk) (by simp [evalPoly]; omega) hU'

/-- Compiled Infinite Theorem 2.3: 5-step compact dyadic circuit `[M(4), M(2), M(2), F(1), F(1)]`
    computes EXACT branchless canonical `x % (2^k + 1)` on ALL `8k`-bit unsigned inputs
    for ALL `k ≥ 1`! -/
theorem compiled_fermat_5step_8limb_canonical :
    ∀ (k : Nat), 1 ≤ k → ∀ (x : Int), 0 ≤ x → x ≤ (2 : Int) ^ (8 * k) - 1 →
      evalProg k [⟨4, .pos⟩, ⟨2, .pos⟩, ⟨2, .pos⟩, ⟨1, .neg⟩, ⟨1, .neg⟩] x =
      x % ((2 : Int) ^ k + 1) := by
  intro k hk x hx0 hxU
  have hchk : checkCircuit .neg 2 [⟨4, .pos⟩, ⟨2, .pos⟩, ⟨2, .pos⟩, ⟨1, .neg⟩, ⟨1, .neg⟩]
      ([], [-1, 0, 0, 0, 0, 0, 0, 0, 1]) ([], [0, 1]) = true := by decide
  have hU' : x ≤ evalPoly ((2 : Int) ^ k) [-1, 0, 0, 0, 0, 0, 0, 0, 1] := by
    simp [evalPoly]
    have hp : (2 : Int) ^ (8 * k) =
        (2 : Int) ^ k * ((2 : Int) ^ k * ((2 : Int) ^ k * ((2 : Int) ^ k *
        ((2 : Int) ^ k * ((2 : Int) ^ k * ((2 : Int) ^ k * (2 : Int) ^ k)))))) := by
      have : 8 * k = k + (k + (k + (k + (k + (k + (k + k)))))) := by omega
      rw [this, Int.pow_add, Int.pow_add, Int.pow_add, Int.pow_add,
          Int.pow_add, Int.pow_add, Int.pow_add]
    omega
  exact canonical_fermat_circuit_of_check 2
    [⟨4, .pos⟩, ⟨2, .pos⟩, ⟨2, .pos⟩, ⟨1, .neg⟩, ⟨1, .neg⟩]
    ([], [-1, 0, 0, 0, 0, 0, 0, 0, 1]) hchk hk (two_pow_ge_two hk) (by simp [evalPoly]; omega) hU'

/-- Compiled Infinite Theorem 2.4: 5-step single-pass dyadic Mersenne circuit
    `[M(4), M(2), M(1), M(1), M(1)]` absorbs ALL `8k`-bit carries into `[0, 2^k - 1]`
    for ALL `k ≥ 2` (and FAILS at `k = 1`, `x = 207` below!). -/
theorem compiled_mersenne_5step_8limb_k_ge_2 :
    ∀ (k : Nat), 2 ≤ k → ∀ (x : Int), 0 ≤ x → x ≤ (2 : Int) ^ (8 * k) - 1 →
      let y := evalProg k [⟨4, .pos⟩, ⟨2, .pos⟩, ⟨1, .pos⟩, ⟨1, .pos⟩, ⟨1, .pos⟩] x
      y % ((2 : Int) ^ k - 1) = x % ((2 : Int) ^ k - 1) ∧ 0 ≤ y ∧ y ≤ (2 : Int) ^ k - 1 := by
  intro k hk x hx0 hxU
  have hchk : checkCircuit .pos 4 [⟨4, .pos⟩, ⟨2, .pos⟩, ⟨1, .pos⟩, ⟨1, .pos⟩, ⟨1, .pos⟩]
      ([], [-1, 0, 0, 0, 0, 0, 0, 0, 1]) ([], [-1, 1]) = true := by decide
  have hB4 : (4 : Int) ≤ (2 : Int) ^ k := by
    cases k with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ m' =>
        have hpos := two_pow_pos m'
        rw [Int.pow_succ, Int.pow_succ]
        omega
  have hU' : x ≤ evalPoly ((2 : Int) ^ k) [-1, 0, 0, 0, 0, 0, 0, 0, 1] := by
    simp [evalPoly]
    have hp : (2 : Int) ^ (8 * k) =
        (2 : Int) ^ k * ((2 : Int) ^ k * ((2 : Int) ^ k * ((2 : Int) ^ k *
        ((2 : Int) ^ k * ((2 : Int) ^ k * ((2 : Int) ^ k * (2 : Int) ^ k)))))) := by
      have : 8 * k = k + (k + (k + (k + (k + (k + (k + k)))))) := by omega
      rw [this, Int.pow_add, Int.pow_add, Int.pow_add, Int.pow_add,
          Int.pow_add, Int.pow_add, Int.pow_add]
    omega
  have hres := circuit_sound_of_check .pos 4
    [⟨4, .pos⟩, ⟨2, .pos⟩, ⟨1, .pos⟩, ⟨1, .pos⟩, ⟨1, .pos⟩]
    ([], [-1, 0, 0, 0, 0, 0, 0, 0, 1]) ([], [-1, 1])
    hchk (by omega) hB4 (by simp [evalPoly]; omega) hU'
  simp [evalPoly, modulus] at hres
  exact ⟨hres.1, by omega, by omega⟩

/-- **Sharpness Witness 2:** For `k = 1` (`B = 2 < 4`), `x = 207 < 2^8` genuinely overflows
    the 5-step single-pass dyadic Mersenne circuit (`eval = 2 ≥ 2^1`), proving `k ≥ 2` is tight! -/
theorem compiled_mersenne_5step_k1_sharp :
    (0 : Int) ≤ 207 ∧ (207 : Int) ≤ (2 : Int) ^ (8 * 1) - 1 ∧
    evalProg 1 [⟨4, .pos⟩, ⟨2, .pos⟩, ⟨1, .pos⟩, ⟨1, .pos⟩, ⟨1, .pos⟩] 207 = 2 := by
  decide

theorem foldM_pos_of_pos {k n : Nat} (hn : 0 < n) : 0 < foldM k n := by
  have hdiv := Nat.div_add_mod n (2 ^ k)
  unfold foldM
  by_cases hq : n / 2 ^ k = 0
  · rw [hq, Nat.mul_zero, Nat.zero_add] at hdiv; omega
  · have := Nat.pos_of_ne_zero hq; omega

theorem foldM_mod_eq (k n : Nat) : foldM k n % (2 ^ k - 1) = n % (2 ^ k - 1) := by
  by_cases hk : k = 0
  · subst hk; simp [foldM, Nat.mod_one]
  · have h2 : 2 ≤ 2 ^ k := nat_two_pow_ge_two (by omega)
    have hsplit : n = (2 ^ k - 1) * (n / 2 ^ k) + (n % 2 ^ k + n / 2 ^ k) := by
      have h := Nat.div_add_mod n (2 ^ k)
      have hmul : 2 ^ k * (n / 2 ^ k) = (2 ^ k - 1) * (n / 2 ^ k) + n / 2 ^ k := by
        rw [Nat.sub_mul, Nat.one_mul]
        have : n / 2 ^ k ≤ 2 ^ k * (n / 2 ^ k) := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos k)
        omega
      omega
    unfold foldM
    conv => rhs; rw [hsplit]
    rw [Nat.mul_add_mod]

theorem canonM_eq_of_lt {k n : Nat} (hk : 1 ≤ k) (hn : n < 2 ^ k) :
    canonM k n = n := by
  have h2 := nat_two_pow_ge_two hk
  unfold canonM
  by_cases h0 : n = 0
  · simp [h0]
  · simp only [h0, ↓reduceIte]
    have hlt : n - 1 < 2 ^ k - 1 := by omega
    rw [Nat.mod_eq_of_lt hlt]
    omega

theorem canonM_foldM {k n : Nat} (hk : 1 ≤ k) : canonM k (foldM k n) = canonM k n := by
  have h2 := nat_two_pow_ge_two hk
  by_cases h0 : n = 0
  · subst h0; simp [foldM, canonM]
  · have hpos : 0 < foldM k n := foldM_pos_of_pos (by omega)
    have hne : foldM k n ≠ 0 := by omega
    simp only [canonM, h0, hne, ↓reduceIte]
    have hmod := foldM_mod_eq k n
    have h1 : (foldM k n - 1) % (2 ^ k - 1) = (n - 1) % (2 ^ k - 1) := by
      by_cases hm : 2 ^ k - 1 = 1
      · simp [hm, Nat.mod_one]
      · have hm2 : 2 ≤ 2 ^ k - 1 := by omega
        -- Since foldM k n ≥ 1 and n ≥ 1, both have same mod (2^k - 1), so subtracting 1 preserves mod.
        have hstep (a : Nat) (ha : 1 ≤ a) :
            (a - 1) % (2 ^ k - 1) =
              if a % (2 ^ k - 1) = 0 then (2 ^ k - 1) - 1 else a % (2 ^ k - 1) - 1 := by
          have ha_eq : a = (a - 1) + 1 := by omega
          have hr := Nat.mod_lt (a - 1) (show 0 < 2 ^ k - 1 by omega)
          have hadd : a % (2 ^ k - 1) = ((a - 1) % (2 ^ k - 1) + 1) % (2 ^ k - 1) := by
            conv => lhs; rw [ha_eq]
            rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < 2 ^ k - 1 by omega)]
          by_cases htop : (a - 1) % (2 ^ k - 1) + 1 = 2 ^ k - 1
          · rw [htop, Nat.mod_self] at hadd
            simp [hadd]; omega
          · have hlt : (a - 1) % (2 ^ k - 1) + 1 < 2 ^ k - 1 := by omega
            rw [Nat.mod_eq_of_lt hlt] at hadd
            simp [hadd]
        rw [hstep (foldM k n) (by omega), hstep n (by omega), hmod]
    rw [h1]

theorem canonM_iterFoldM {k r n : Nat} (hk : 1 ≤ k) :
    canonM k (iterFoldM k r n) = canonM k n := by
  induction r generalizing n with
  | zero => rfl
  | succ r ih =>
    simp only [iterFoldM]
    rw [ih, canonM_foldM hk]

/-- Single-step exact inverse-minimum inequality for `foldM`:
    `foldM k n < 2^(r*k) + 2^k - 1` whenever `n < 2^((r+1)*k) + 2^k - 1`. -/
theorem foldM_lt_threshold {k r n : Nat} (hk : 1 ≤ k)
    (hn : n < 2 ^ ((r + 1) * k) + 2 ^ k - 1) :
    foldM k n < 2 ^ (r * k) + 2 ^ k - 1 := by
  have h2 := nat_two_pow_ge_two hk
  have hpow : 2 ^ ((r + 1) * k) = 2 ^ k * 2 ^ (r * k) := by
    rw [Nat.succ_mul, Nat.pow_add, Nat.mul_comm]
  have hsplit := Nat.div_add_mod n (2 ^ k)
  have hrem := Nat.mod_lt n (Nat.two_pow_pos k)
  unfold foldM
  have hq_le : n / 2 ^ k ≤ 2 ^ (r * k) := by
    by_cases hgt : 2 ^ (r * k) + 1 ≤ n / 2 ^ k
    · have hmul : 2 ^ k * (2 ^ (r * k) + 1) ≤ 2 ^ k * (n / 2 ^ k) :=
        Nat.mul_le_mul_left (2 ^ k) hgt
      rw [Nat.mul_add, Nat.mul_one] at hmul
      omega
    · omega
  by_cases htop : n / 2 ^ k = 2 ^ (r * k)
  · rw [htop] at hsplit
    have hr_lt : n % 2 ^ k < 2 ^ k - 1 := by omega
    omega
  · omega

/-- **Theorem 3A (Mersenne Exact Carry-Absorption Threshold):**
    For ALL `k ≥ 1`, ALL `r ≥ 1`, and ALL `n < 2^(r*k) + 2^k - 1`,
    `r` folds absorb every carry into `[0, 2^k - 1]` and equal `canonM k n`! -/
theorem mersenne_exact_threshold (k r n : Nat) (hk : 1 ≤ k) (hr : 1 ≤ r)
    (hn : n < 2 ^ (r * k) + 2 ^ k - 1) :
    iterFoldM k r n < 2 ^ k ∧ iterFoldM k r n = canonM k n := by
  have hlt : iterFoldM k r n < 2 ^ k := by
    induction r generalizing n with
    | zero => omega
    | succ r ih =>
      cases r with
      | zero =>
        simp only [iterFoldM, Nat.zero_add, Nat.one_mul] at *
        have h := foldM_lt_threshold (r := 0) hk (by simpa using hn)
        simp only [Nat.zero_mul, Nat.pow_zero] at h
        have h2 := nat_two_pow_ge_two hk
        omega
      | succ r' =>
        simp only [iterFoldM]
        exact ih (foldM k n) (by omega) (foldM_lt_threshold hk hn)
  refine ⟨hlt, ?_⟩
  rw [← canonM_iterFoldM (r := r) hk, canonM_eq_of_lt hk hlt]

/-- **Exact Sharpness Witness 3A:** At `n = 2^(r*k) + 2^k - 1`, `r` folds land at
    EXACTLY `2^k` (overflowing `k` bits by 1) for ALL `k ≥ 1` and ALL `r ≥ 1`! -/
theorem mersenne_threshold_sharp (k r : Nat) (hk : 1 ≤ k) (hr : 1 ≤ r) :
    iterFoldM k r (2 ^ (r * k) + 2 ^ k - 1) = 2 ^ k := by
  have h2 := nat_two_pow_ge_two hk
  induction r with
  | zero => omega
  | succ r ih =>
    have hpow : 2 ^ ((r + 1) * k) = 2 ^ k * 2 ^ (r * k) := by
      rw [Nat.succ_mul, Nat.pow_add, Nat.mul_comm]
    have hstep : foldM k (2 ^ ((r + 1) * k) + 2 ^ k - 1) = 2 ^ (r * k) + 2 ^ k - 1 := by
      unfold foldM
      have heq : 2 ^ ((r + 1) * k) + 2 ^ k - 1 = (2 ^ k - 1) + 2 ^ k * 2 ^ (r * k) := by
        rw [hpow]; omega
      have hdiv0 : (2 ^ k - 1) / 2 ^ k = 0 := Nat.div_eq_of_lt (by omega)
      have hmod0 : (2 ^ k - 1) % 2 ^ k = 2 ^ k - 1 := Nat.mod_eq_of_lt (by omega)
      rw [heq, Nat.add_mul_mod_self_left, hmod0,
          Nat.add_mul_div_left _ _ (Nat.two_pow_pos k), hdiv0]
      have hp := Nat.two_pow_pos (r * k)
      omega
    cases r with
    | zero =>
      simp only [iterFoldM]
      rw [hstep]
      simp only [Nat.zero_mul, Nat.pow_zero]
      omega
    | succ r' =>
      simp only [iterFoldM]
      rw [hstep]
      exact ih (by omega)

/-- Single-step sign-flipping involution of the Fermat envelope:
    `[-2^((r+1)*k), 2^((r+1)*k) + 2^k - 1] ↦ [-2^(r*k), 2^(r*k) + 2^k - 1]`. -/
theorem foldF_step_envelope {k r : Nat} {x : Int}
    (hxL : -((2 : Int) ^ ((r + 1) * k)) ≤ x)
    (hxU : x ≤ (2 : Int) ^ ((r + 1) * k) + (2 : Int) ^ k - 1) :
    -((2 : Int) ^ (r * k)) ≤ foldF k x ∧
    foldF k x ≤ (2 : Int) ^ (r * k) + (2 : Int) ^ k - 1 := by
  have hw_pos : (0 : Int) < (2 : Int) ^ k := two_pow_pos k
  have hpow : (2 : Int) ^ ((r + 1) * k) = (2 : Int) ^ k * (2 : Int) ^ (r * k) := by
    rw [Nat.succ_mul, Int.pow_add, Int.mul_comm]
  have hL_div : (-((2 : Int) ^ ((r + 1) * k))) / (2 : Int) ^ k = -((2 : Int) ^ (r * k)) := by
    have heq : -((2 : Int) ^ ((r + 1) * k)) = (2 : Int) ^ k * (-((2 : Int) ^ (r * k))) + 0 := by
      rw [hpow, Int.mul_neg]; omega
    exact (int_ediv_unique hw_pos heq (by omega) hw_pos).1
  have hU_div : ((2 : Int) ^ ((r + 1) * k) + (2 : Int) ^ k - 1) / (2 : Int) ^ k = (2 : Int) ^ (r * k) := by
    have heq : (2 : Int) ^ ((r + 1) * k) + (2 : Int) ^ k - 1 =
        (2 : Int) ^ k * (2 : Int) ^ (r * k) + ((2 : Int) ^ k - 1) := by
      rw [hpow]; omega
    exact (int_ediv_unique hw_pos heq (by omega) (by omega)).1
  have hqL : -((2 : Int) ^ (r * k)) ≤ x / (2 : Int) ^ k := by
    rw [← hL_div]; exact int_ediv_mono hw_pos hxL
  have hqU : x / (2 : Int) ^ k ≤ (2 : Int) ^ (r * k) := by
    rw [← hU_div]; exact int_ediv_mono hw_pos hxU
  have hr0 : 0 ≤ x % (2 : Int) ^ k := Int.emod_nonneg x (Int.ne_of_gt hw_pos)
  have hrw : x % (2 : Int) ^ k < (2 : Int) ^ k := Int.emod_lt_of_pos x hw_pos
  unfold foldF
  omega

/-- **Theorem 3B.1 (Signed Fermat Exact Asymmetric Absorbing Envelope):**
    For ALL `k ≥ 1`, ALL `r : Nat`, and ALL `x ∈ [-2^(r*k), 2^(r*k) + 2^k - 1]`,
    `r` signed Fermat folds land inside the exact attractor `[-1, 2^k]`! -/
theorem fermat_exact_envelope (k r : Nat) (x : Int)
    (hxL : -((2 : Int) ^ (r * k)) ≤ x)
    (hxU : x ≤ (2 : Int) ^ (r * k) + (2 : Int) ^ k - 1) :
    -1 ≤ iterFoldF k r x ∧ iterFoldF k r x ≤ (2 : Int) ^ k := by
  induction r generalizing x with
  | zero =>
    simp only [iterFoldF, Nat.zero_mul, Int.pow_zero] at *
    omega
  | succ r ih =>
    simp only [iterFoldF]
    have ⟨h1, h2⟩ := foldF_step_envelope hxL hxU
    exact ih (foldF k x) h1 h2

/-- Helper: one step of `foldF` swaps the two sharp boundary sequences
    `2^((r+1)*k) + 2^k ↦ -(2^(r*k) + 1)` and `-(2^((r+1)*k) + 1) ↦ 2^(r*k) + 2^k`. -/
theorem foldF_upper_witness_step (k r : Nat) :
    foldF k ((2 : Int) ^ ((r + 1) * k) + (2 : Int) ^ k) = -((2 : Int) ^ (r * k) + 1) := by
  have hw_pos : (0 : Int) < (2 : Int) ^ k := two_pow_pos k
  have hpow : (2 : Int) ^ ((r + 1) * k) = (2 : Int) ^ k * (2 : Int) ^ (r * k) := by
    rw [Nat.succ_mul, Int.pow_add, Int.mul_comm]
  have heq : (2 : Int) ^ ((r + 1) * k) + (2 : Int) ^ k =
      (2 : Int) ^ k * ((2 : Int) ^ (r * k) + 1) + 0 := by
    rw [hpow, Int.mul_add, Int.mul_one]; omega
  have ⟨hq, hr⟩ := int_ediv_unique hw_pos heq (by omega) hw_pos
  unfold foldF; rw [hq, hr]; omega

theorem foldF_lower_witness_step (k r : Nat) :
    foldF k (-((2 : Int) ^ ((r + 1) * k) + 1)) = (2 : Int) ^ (r * k) + (2 : Int) ^ k := by
  have hw_pos : (0 : Int) < (2 : Int) ^ k := two_pow_pos k
  have hpow : (2 : Int) ^ ((r + 1) * k) = (2 : Int) ^ k * (2 : Int) ^ (r * k) := by
    rw [Nat.succ_mul, Int.pow_add, Int.mul_comm]
  have heq : -((2 : Int) ^ ((r + 1) * k) + 1) =
      (2 : Int) ^ k * (-((2 : Int) ^ (r * k) + 1)) + ((2 : Int) ^ k - 1) := by
    rw [hpow, Int.mul_neg, Int.mul_add, Int.mul_one]; omega
  have ⟨hq, hr⟩ := int_ediv_unique hw_pos heq (by omega) (by omega)
  unfold foldF; rw [hq, hr]; omega

/-- **Theorem 3B.2 (Exact Dual-End Alternating Sharpness for Signed Fermat Folding):**
    Just 1 unit past EITHER boundary of `[-2^(r*k), 2^(r*k) + 2^k - 1]`,
    `r` folds escape the attractor `[-1, 2^k]`, alternating between `-2` and `2^k + 1`
    according to the parity of `r`! -/
theorem fermat_dual_end_sharp (k r : Nat) :
    iterFoldF k r ((2 : Int) ^ (r * k) + (2 : Int) ^ k) =
      (if r % 2 = 1 then -2 else (2 : Int) ^ k + 1) ∧
    iterFoldF k r (-((2 : Int) ^ (r * k) + 1)) =
      (if r % 2 = 1 then (2 : Int) ^ k + 1 else -2) := by
  induction r with
  | zero =>
    simp only [iterFoldF, Nat.zero_mul, Int.pow_zero]
    constructor <;> omega
  | succ r ih =>
    simp only [iterFoldF, foldF_upper_witness_step, foldF_lower_witness_step]
    by_cases hp : r % 2 = 1
    · have hps : (r + 1) % 2 ≠ 1 := by omega
      simp only [hp, ↓reduceIte] at ih
      simp only [hps, ↓reduceIte]
      exact ⟨ih.2, ih.1⟩
    · have hps : (r + 1) % 2 = 1 := by omega
      simp only [hp, ↓reduceIte] at ih
      simp only [hps, ↓reduceIte]
      exact ⟨ih.2, ih.1⟩

/-- **Theorem 3B.3 (Exact Attractor Dichotomy on `[-1, 2^k]`):**
    - Every `x ∈ [0, 2^k - 1]` is a fixed point of `foldF k`.
    - `{-1, 2^k}` is an exact 2-cycle (`foldF k (-1) = 2^k`, `foldF k (2^k) = -1`). -/
theorem fermat_attractor_dichotomy (k : Nat) :
    (∀ x : Int, 0 ≤ x → x < (2 : Int) ^ k → foldF k x = x) ∧
    foldF k (-1) = (2 : Int) ^ k ∧
    foldF k ((2 : Int) ^ k) = -1 := by
  have hw_pos : (0 : Int) < (2 : Int) ^ k := two_pow_pos k
  refine ⟨?_, ?_, ?_⟩
  · intro x hx0 hxw
    unfold foldF
    rw [Int.emod_eq_of_lt hx0 hxw, Int.ediv_eq_zero_of_lt hx0 hxw]
    omega
  · have heq : (-1 : Int) = (2 : Int) ^ k * (-1) + ((2 : Int) ^ k - 1) := by omega
    have ⟨hq, hr⟩ := int_ediv_unique hw_pos heq (by omega) (by omega)
    unfold foldF; rw [hq, hr]; omega
  · have heq : (2 : Int) ^ k = (2 : Int) ^ k * 1 + 0 := by omega
    have ⟨hq, hr⟩ := int_ediv_unique hw_pos heq (by omega) hw_pos
    unfold foldF; rw [hq, hr]; omega

/-- **Theorem 3B.4 (Branchless Fermat Canonicalization):**
    For ALL `k ≥ 1` and ALL `x ∈ [-(2^k - 1), 2^k - 1]`, a SINGLE signed Fermat fold
    computes the exact canonical non-negative remainder `x % (2^k + 1) ∈ [0, 2^k]`! -/
theorem fermat_branchless_canonical (k : Nat) (x : Int)
    (hxL : -((2 : Int) ^ k - 1) ≤ x) (hxU : x ≤ (2 : Int) ^ k - 1) :
    foldF k x = x % ((2 : Int) ^ k + 1) := by
  have hw_pos : (0 : Int) < (2 : Int) ^ k := two_pow_pos k
  by_cases hx0 : 0 ≤ x
  · have hfp := (fermat_attractor_dichotomy k).1 x hx0 (by omega)
    rw [hfp, Int.emod_eq_of_lt hx0 (by omega)]
  · have heq : x = (2 : Int) ^ k * (-1) + ((2 : Int) ^ k + x) := by omega
    have ⟨hq, hr⟩ := int_ediv_unique hw_pos heq (by omega) (by omega)
    have hfold : foldF k x = x + ((2 : Int) ^ k + 1) := by
      unfold foldF; rw [hq, hr]; omega
    rw [hfold]
    have hx_split : x = ((2 : Int) ^ k + 1) * (-1) + (x + ((2 : Int) ^ k + 1)) := by omega
    conv => rhs; rw [hx_split]
    rw [Int.mul_add_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]

theorem popcount_zero : popcount 0 = 0 := by
  rw [popcount]; simp

theorem popcount_step {n : Nat} (hn : n ≠ 0) :
    popcount n = n % 2 + popcount (n / 2) := by
  conv => lhs; rw [popcount]
  simp [hn]

theorem popcount_div_mod_two (n : Nat) :
    popcount n = n % 2 + popcount (n / 2) := by
  by_cases h : n = 0
  · subst h; simp [popcount_zero]
  · exact popcount_step h

/-- First-principles Kummer–Legendre Carry-Popcount Identity with carry-in `c ≤ 1`:
    `carryCountAux a b c + popcount (a + b + c) = popcount a + popcount b + c`. -/
theorem carryCountAux_add_popcount (a b c : Nat) (hc : c ≤ 1) :
    carryCountAux a b c + popcount (a + b + c) = popcount a + popcount b + c := by
  by_cases hz : a = 0 ∧ b = 0 ∧ c = 0
  · rcases hz with ⟨rfl, rfl, rfl⟩
    rw [carryCountAux]; simp [popcount_zero]
  · have hcin : (a % 2 + b % 2 + c) / 2 ≤ 1 := by omega
    have hrec := carryCountAux_add_popcount (a / 2) (b / 2) ((a % 2 + b % 2 + c) / 2) hcin
    have hcstep : carryCountAux a b c =
        (a % 2 + b % 2 + c) / 2 + carryCountAux (a / 2) (b / 2) ((a % 2 + b % 2 + c) / 2) := by
      conv => lhs; rw [carryCountAux]
      simp [hz]
    have hsum_mod : (a + b + c) % 2 = (a % 2 + b % 2 + c) % 2 := by omega
    have hsum_div : (a + b + c) / 2 = a / 2 + b / 2 + (a % 2 + b % 2 + c) / 2 := by omega
    have hp_sum : popcount (a + b + c) =
        (a % 2 + b % 2 + c) % 2 + popcount (a / 2 + b / 2 + (a % 2 + b % 2 + c) / 2) := by
      rw [popcount_div_mod_two, hsum_mod, hsum_div]
    have hp_a := popcount_div_mod_two a
    have hp_b := popcount_div_mod_two b
    omega
termination_by a + b + c
decreasing_by
  have : a / 2 + b / 2 + (a % 2 + b % 2 + c) / 2 < a + b + c := by omega
  exact this

theorem carryCount_add_popcount (a b : Nat) :
    carryCount a b + popcount (a + b) = popcount a + popcount b := by
  have h := carryCountAux_add_popcount a b 0 (by decide)
  simpa [carryCount] using h

/-- Disjoint bit-split additivity of `popcount`: `s_2(n % 2^w) + s_2(n / 2^w) = s_2(n)`. -/
theorem popcount_split (w n : Nat) :
    popcount (n % 2 ^ w) + popcount (n / 2 ^ w) = popcount n := by
  induction w generalizing n with
  | zero => simp [Nat.mod_one, popcount_zero]
  | succ w ih =>
    have hpow : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
    have hmod_bit : (n % (2 * 2 ^ w)) % 2 = n % 2 := by
      have := Nat.mod_mod_of_dvd n (show 2 ∣ 2 * 2 ^ w from ⟨2 ^ w, rfl⟩)
      exact this
    have hmod_div2 : (n % (2 * 2 ^ w)) / 2 = (n / 2) % 2 ^ w := by
      rw [Nat.mod_mul_right_div_self]
    have hdiv_step : n / (2 * 2 ^ w) = (n / 2) / 2 ^ w := by
      rw [Nat.div_div_eq_div_mul]
    rw [hpow, popcount_div_mod_two (n % (2 * 2 ^ w)), hmod_bit, hmod_div2, hdiv_step,
        popcount_div_mod_two n]
    have hrec := ih (n / 2)
    omega

theorem natMersenne_step_canon {k m n : Nat} (hk : 1 ≤ k) (hm : 1 ≤ m) :
    canonM k (n % 2 ^ (m * k) + n / 2 ^ (m * k)) = canonM k n := by
  have h2 := nat_two_pow_ge_two hk
  have hmk : 1 ≤ m * k := Nat.mul_pos hm hk
  by_cases h0 : n = 0
  · subst h0; simp [canonM]
  · have hpos : 0 < n % 2 ^ (m * k) + n / 2 ^ (m * k) := foldM_pos_of_pos (by omega)
    have hne : n % 2 ^ (m * k) + n / 2 ^ (m * k) ≠ 0 := by omega
    simp only [canonM, h0, hne, ↓reduceIte]
    -- Show (n % 2^(m*k) + n / 2^(m*k)) % (2^k - 1) = n % (2^k - 1)
    have hdvd_int := mersenne_dvd_mersenne k m
    have hdvd : (2 ^ k - 1) ∣ (2 ^ (m * k) - 1) := by
      rcases hdvd_int with ⟨q, hq⟩
      have hpos_mk : 1 ≤ 2 ^ (m * k) := Nat.two_pow_pos (m * k)
      have hpos_k : 1 ≤ 2 ^ k - 1 := by omega
      have hq_nonneg : 0 ≤ q := by
        have h1 : (0 : Int) ≤ (2 : Int) ^ (m * k) - 1 := by
          have := two_pow_pos (m * k); omega
        have h2i : (0 : Int) < (2 : Int) ^ k - 1 := by
          have := two_pow_ge_two hk; omega
        exact Decidable.byContradiction fun hlt => by
          have hneg : q ≤ -1 := by omega
          have hmul : ((2 : Int) ^ k - 1) * q ≤ ((2 : Int) ^ k - 1) * (-1) :=
            Int.mul_le_mul_of_nonneg_left hneg (by omega)
          omega
      refine ⟨q.toNat, ?_⟩
      have hcast : ((2 ^ (m * k) - 1 : Nat) : Int) = ((2 ^ k - 1 : Nat) : Int) * (q.toNat : Int) := by
        have hqeq : (q.toNat : Int) = q := Int.toNat_of_nonneg hq_nonneg
        rw [hqeq]
        have h1 : ((2 ^ (m * k) - 1 : Nat) : Int) = (2 : Int) ^ (m * k) - 1 := by
          rw [Int.ofNat_sub hpos_mk]; simp
        have h2 : ((2 ^ k - 1 : Nat) : Int) = (2 : Int) ^ k - 1 := by
          rw [Int.ofNat_sub (by omega)]; simp
        rw [h1, h2, hq]
      exact Int.ofNat.inj hcast
    rcases hdvd with ⟨d, hd⟩
    have hmod_eq : (n % 2 ^ (m * k) + n / 2 ^ (m * k)) % (2 ^ k - 1) = n % (2 ^ k - 1) := by
      have hsplit := Nat.div_add_mod n (2 ^ (m * k))
      have hmk_pos : 1 ≤ 2 ^ (m * k) := Nat.two_pow_pos (m * k)
      have heq : n = (2 ^ k - 1) * (d * (n / 2 ^ (m * k))) + (n % 2 ^ (m * k) + n / 2 ^ (m * k)) := by
        have hmul : 2 ^ (m * k) * (n / 2 ^ (m * k)) =
            (2 ^ (m * k) - 1) * (n / 2 ^ (m * k)) + n / 2 ^ (m * k) := by
          rw [Nat.sub_mul, Nat.one_mul]
          have : n / 2 ^ (m * k) ≤ 2 ^ (m * k) * (n / 2 ^ (m * k)) :=
            Nat.le_mul_of_pos_left _ (Nat.two_pow_pos (m * k))
          omega
        rw [hd, Nat.mul_assoc] at hmul
        omega
      conv => rhs; rw [heq]
      rw [Nat.mul_add_mod]
    by_cases hm1 : 2 ^ k - 1 = 1
    · simp [hm1, Nat.mod_one]
    · have hm2 : 2 ≤ 2 ^ k - 1 := by omega
      have hstep (a : Nat) (ha : 1 ≤ a) :
          (a - 1) % (2 ^ k - 1) =
            if a % (2 ^ k - 1) = 0 then (2 ^ k - 1) - 1 else a % (2 ^ k - 1) - 1 := by
        have ha_eq : a = (a - 1) + 1 := by omega
        have hr := Nat.mod_lt (a - 1) (show 0 < 2 ^ k - 1 by omega)
        have hadd : a % (2 ^ k - 1) = ((a - 1) % (2 ^ k - 1) + 1) % (2 ^ k - 1) := by
          conv => lhs; rw [ha_eq]
          rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < 2 ^ k - 1 by omega)]
        by_cases htop : (a - 1) % (2 ^ k - 1) + 1 = 2 ^ k - 1
        · rw [htop, Nat.mod_self] at hadd; simp [hadd]; omega
        · have hlt : (a - 1) % (2 ^ k - 1) + 1 < 2 ^ k - 1 := by omega
          rw [Nat.mod_eq_of_lt hlt] at hadd
          simp [hadd]
      rw [hstep _ (by omega), hstep n (by omega), hmod_eq]

/-- Exact carry-popcount invariant at EVERY intermediate stage of ANY Mersenne folding program! -/
theorem carryNatMersenne_invariant (k : Nat) (strides : List Nat) (n : Nat) :
    carryNatMersenne k strides n + popcount (evalNatMersenne k strides n) = popcount n := by
  induction strides generalizing n with
  | nil => simp [carryNatMersenne, evalNatMersenne]
  | cons m ms ih =>
    simp only [carryNatMersenne, evalNatMersenne]
    have hrec := ih (n % 2 ^ (m * k) + n / 2 ^ (m * k))
    have hadd := carryCount_add_popcount (n % 2 ^ (m * k)) (n / 2 ^ (m * k))
    have hsp := popcount_split (m * k) n
    omega

theorem evalNatMersenne_canon {k : Nat} (hk : 1 ≤ k) {strides : List Nat}
    (hpos : strides.all (fun m => decide (1 ≤ m)) = true) (n : Nat) :
    canonM k (evalNatMersenne k strides n) = canonM k n := by
  induction strides generalizing n with
  | nil => rfl
  | cons m ms ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hpos
    simp only [evalNatMersenne]
    rw [ih hpos.2, natMersenne_step_canon hk hpos.1]

/-- **Theorem 4 (Schedule-Invariant Total-Carry Conservation Law):**
    For ALL `k ≥ 1`, ALL `n : Nat`, and ANY positive Mersenne folding schedule `strides`
    that absorbs `n` into `[0, 2^k - 1]`:
    1. Its final value is uniquely `canonM k n` (independent of schedule topology);
    2. The total binary carries absorbed across all folds equals EXACTLY
       `popcount n - popcount (canonM k n)` (topological carry conservation!). -/
theorem total_carry_conservation {k : Nat} (hk : 1 ≤ k) {strides : List Nat}
    (hpos : strides.all (fun m => decide (1 ≤ m)) = true) {n : Nat}
    (habsorb : evalNatMersenne k strides n < 2 ^ k) :
    evalNatMersenne k strides n = canonM k n ∧
    carryNatMersenne k strides n = popcount n - popcount (canonM k n) := by
  have hcanon : evalNatMersenne k strides n = canonM k n := by
    rw [← canonM_eq_of_lt hk habsorb, evalNatMersenne_canon hk hpos n]
  have hinv := carryNatMersenne_invariant k strides n
  rw [hcanon] at hinv
  exact ⟨hcanon, by omega⟩

/-- **Topological Schedule-Invariance Corollary:**
    Any two distinct absorbing Mersenne folding topologies `s₁, s₂` (e.g., sequential vs dyadic tree)
    absorb the EXACT SAME total number of binary carries on every `n : Nat`! -/
theorem carry_schedule_invariance {k : Nat} (hk : 1 ≤ k) {s1 s2 : List Nat}
    (hp1 : s1.all (fun m => decide (1 ≤ m)) = true)
    (hp2 : s2.all (fun m => decide (1 ≤ m)) = true)
    {n : Nat}
    (ha1 : evalNatMersenne k s1 n < 2 ^ k)
    (ha2 : evalNatMersenne k s2 n < 2 ^ k) :
    evalNatMersenne k s1 n = evalNatMersenne k s2 n ∧
    carryNatMersenne k s1 n = carryNatMersenne k s2 n := by
  have ⟨hf1, hc1⟩ := total_carry_conservation hk hp1 ha1
  have ⟨hf2, hc2⟩ := total_carry_conservation hk hp2 ha2
  exact ⟨hf1.trans hf2.symm, hc1.trans hc2.symm⟩

/-- **Theorem 5A (Dyadic Fermat–Mersenne Tower Factorization):**
    `2^(2^d * k) - 1 = (2^k - 1) * ∏_{j < d} (2^(2^j * k) + 1)` for all `d, k : Nat`. -/
theorem tower_factorization (d k : Nat) :
    (2 ^ k - 1) * fermatProd d k = towerMod d k := by
  induction d with
  | zero => simp [fermatProd, towerMod]
  | succ d ih =>
    simp only [fermatProd, towerMod, fermatFactor] at *
    rw [← Nat.mul_assoc, ih]
    have hpow : 2 ^ (2 ^ (d + 1) * k) = 2 ^ (2 ^ d * k) * 2 ^ (2 ^ d * k) := by
      have hexp : 2 ^ (d + 1) * k = 2 ^ d * k + 2 ^ d * k := by
        rw [Nat.pow_succ, Nat.mul_two, Nat.add_mul]
      rw [hexp, Nat.pow_add]
    have hpos : 1 ≤ 2 ^ (2 ^ d * k) := Nat.two_pow_pos (2 ^ d * k)
    rw [hpow, Nat.mul_add, Nat.mul_one, Nat.sub_mul, Nat.one_mul]
    have hle : 2 ^ (2 ^ d * k) ≤ 2 ^ (2 ^ d * k) * 2 ^ (2 ^ d * k) :=
      Nat.le_mul_of_pos_left _ hpos
    omega

/-- Pure-silicon algebraic Bézout CRT combining lemma (zero `gcd`/`Coprime` needed!):
    if `(2^w - 1) ∣ Δ` and `(2^w + 1) ∣ Δ` for `w ≥ 1`, then `(2^(2w) - 1) ∣ Δ`. -/
theorem coprime_mersenne_fermat_dvd {w : Nat} (hw : 1 ≤ w) {Δ : Int}
    (hM : ((2 : Int) ^ w - 1) ∣ Δ) (hF : ((2 : Int) ^ w + 1) ∣ Δ) :
    ((2 : Int) ^ (2 * w) - 1) ∣ Δ := by
  rcases hM with ⟨u, hu⟩
  rcases hF with ⟨v, hv⟩
  have hsq : ((2 : Int) ^ w - 1) * ((2 : Int) ^ w + 1) = (2 : Int) ^ (2 * w) - 1 := by
    have hp : (2 : Int) ^ (2 * w) = (2 : Int) ^ w * (2 : Int) ^ w := by
      rw [Nat.two_mul, Int.pow_add]
    rw [hp, Int.mul_add, Int.mul_one, Int.sub_mul, Int.one_mul]
    omega
  have h2Δ : ((2 : Int) ^ (2 * w) - 1) * (u - v) = 2 * Δ := by
    rw [Int.mul_sub, ← hsq]
    have h1 : (((2 : Int) ^ w - 1) * ((2 : Int) ^ w + 1)) * u = ((2 : Int) ^ w + 1) * Δ := by
      rw [hu, Int.mul_comm ((2 : Int) ^ w - 1) ((2 : Int) ^ w + 1), Int.mul_assoc]
    have h2 : (((2 : Int) ^ w - 1) * ((2 : Int) ^ w + 1)) * v = ((2 : Int) ^ w - 1) * Δ := by
      rw [hv, Int.mul_assoc]
    rw [h1, h2, Int.add_mul, Int.sub_mul, Int.one_mul]
    omega
  have hpow2 : (2 : Int) ^ (2 * w - 1) * 2 = (2 : Int) ^ (2 * w) := by
    have hsub : 2 * w = (2 * w - 1) + 1 := by omega
    conv => rhs; rw [hsub, Int.pow_succ]
  refine ⟨(2 : Int) ^ (2 * w - 1) * (u - v) - Δ, ?_⟩
  rw [Int.mul_sub, ← Int.mul_assoc, Int.mul_comm ((2 : Int) ^ (2 * w) - 1) ((2 : Int) ^ (2 * w - 1)),
      Int.mul_assoc, h2Δ, ← Int.mul_assoc, hpow2, Int.sub_mul, Int.one_mul]
  omega

/-- Inductive CRT Uniqueness for the entire `d`-level Fermat–Mersenne Tower. -/
theorem tower_crt_dvd (d k : Nat) (hk : 1 ≤ k) {Δ : Int}
    (hM : ((2 : Int) ^ k - 1) ∣ Δ)
    (hF : ∀ j, j < d → ((2 : Int) ^ (2 ^ j * k) + 1) ∣ Δ) :
    ((2 : Int) ^ (2 ^ d * k) - 1) ∣ Δ := by
  induction d with
  | zero => simpa using hM
  | succ d ih =>
    have hprev := ih (fun j hj => hF j (by omega))
    have hcur := hF d (by omega)
    have hw : 1 ≤ 2 ^ d * k := Nat.mul_pos (Nat.two_pow_pos d) hk
    have hcomb := coprime_mersenne_fermat_dvd hw hprev hcur
    have hexp : 2 * (2 ^ d * k) = 2 ^ (d + 1) * k := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ d) 2, Nat.mul_assoc]
    rwa [hexp] at hcomb

/-- Factor divisibility helpers into `2^(2^d * k) - 1`. -/
theorem mersenne_dvd_tower (d k : Nat) :
    ((2 : Int) ^ k - 1) ∣ ((2 : Int) ^ (2 ^ d * k) - 1) :=
  mersenne_dvd_mersenne k (2 ^ d)

theorem fermat_dvd_tower {d k j : Nat} (hj : j < d) :
    ((2 : Int) ^ (2 ^ j * k) + 1) ∣ ((2 : Int) ^ (2 ^ d * k) - 1) := by
  have hdvd_nat : fermatFactor j k ∣ towerMod d k := by
    rw [← tower_factorization d k]
    suffices h : fermatFactor j k ∣ fermatProd d k by
      rcases h with ⟨q, hq⟩
      exact ⟨(2 ^ k - 1) * q, by rw [hq, Nat.mul_left_comm]⟩
    induction d with
    | zero => omega
    | succ d ih =>
      simp only [fermatProd]
      by_cases heq : j = d
      · subst heq; exact ⟨fermatProd j k, Nat.mul_comm _ _⟩
      · rcases ih (by omega) with ⟨q, hq⟩
        exact ⟨q * fermatFactor d k, by rw [hq, Nat.mul_assoc]⟩
  rcases hdvd_nat with ⟨q, hq⟩
  refine ⟨(q : Int), ?_⟩
  have hcast : ((towerMod d k : Nat) : Int) = ((fermatFactor j k : Nat) : Int) * (q : Int) := by
    rw [hq]; simp
  have h1 : ((towerMod d k : Nat) : Int) = (2 : Int) ^ (2 ^ d * k) - 1 := by
    unfold towerMod
    rw [Int.ofNat_sub (Nat.two_pow_pos _)]; simp
  have h2 : ((fermatFactor j k : Nat) : Int) = (2 : Int) ^ (2 ^ j * k) + 1 := by
    unfold fermatFactor; simp
  rw [← h1, ← h2]
  exact hcast

/-- Cancellation of `2^s` modulo any divisor `D` of `2^W - 1` (pure silicon inverse `2^(W-s)`!). -/
theorem dvd_of_dvd_pow_two_mul {W s : Nat} (hs : s ≤ W) {D A : Int}
    (hDW : D ∣ ((2 : Int) ^ W - 1)) (hmul : D ∣ ((2 : Int) ^ s * A)) : D ∣ A := by
  rcases hDW with ⟨q1, hq1⟩
  rcases hmul with ⟨q2, hq2⟩
  refine ⟨(2 : Int) ^ (W - s) * q2 - q1 * A, ?_⟩
  have hpow : (2 : Int) ^ (W - s) * (2 : Int) ^ s = (2 : Int) ^ W := by
    rw [← Int.pow_add, Nat.sub_add_cancel hs]
  have h1 : D * ((2 : Int) ^ (W - s) * q2) = (2 : Int) ^ W * A := by
    rw [← Int.mul_assoc, Int.mul_comm D ((2 : Int) ^ (W - s)), Int.mul_assoc, ← hq2,
        ← Int.mul_assoc, hpow]
  have h2 : D * (q1 * A) = ((2 : Int) ^ W - 1) * A := by
    rw [← Int.mul_assoc, ← hq1]
  rw [Int.mul_sub, h1, h2, Int.sub_mul, Int.one_mul]
  omega

theorem rotR_lt {W x s : Nat} (hs : s ≤ W) (hx : x < 2 ^ W) : rotR W x s < 2 ^ W := by
  unfold rotR
  have hpow : 2 ^ W = 2 ^ (W - s) * 2 ^ s := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hs]
  have hq : x / 2 ^ s < 2 ^ (W - s) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos s), ← hpow]
    exact hx
  have hr : x % 2 ^ s < 2 ^ s := Nat.mod_lt x (Nat.two_pow_pos s)
  have hle : (x % 2 ^ s + 1) * 2 ^ (W - s) ≤ 2 ^ s * 2 ^ (W - s) :=
    Nat.mul_le_mul_right _ hr
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (2 ^ s) (2 ^ (W - s)), ← hpow] at hle
  omega

theorem rotR_popcount {W x s : Nat} (hs : s ≤ W) (hx : x < 2 ^ W) :
    popcount (rotR W x s) = popcount x := by
  unfold rotR
  have hpow : 2 ^ W = 2 ^ (W - s) * 2 ^ s := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hs]
  have hq : x / 2 ^ s < 2 ^ (W - s) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos s), ← hpow]
    exact hx
  have hsp := popcount_split (W - s) (x / 2 ^ s + (x % 2 ^ s) * 2 ^ (W - s))
  have hmod : (x / 2 ^ s + (x % 2 ^ s) * 2 ^ (W - s)) % 2 ^ (W - s) = x / 2 ^ s := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq]
  have hdiv : (x / 2 ^ s + (x % 2 ^ s) * 2 ^ (W - s)) / 2 ^ (W - s) = x % 2 ^ s := by
    rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos (W - s)), Nat.div_eq_of_lt hq, Nat.zero_add]
  rw [hmod, hdiv] at hsp
  have hsp2 := popcount_split s x
  omega

theorem rotR_mul_pow_sub_dvd {W x s : Nat} (hs : s ≤ W) :
    ((2 : Int) ^ W - 1) ∣ ((2 : Int) ^ s * (rotR W x s : Int) - (x : Int)) := by
  refine ⟨((x % 2 ^ s : Nat) : Int), ?_⟩
  have hnat : 2 ^ s * rotR W x s = x + (2 ^ W - 1) * (x % 2 ^ s) := by
    unfold rotR
    have hpow : 2 ^ s * 2 ^ (W - s) = 2 ^ W := by
      rw [← Nat.pow_add, Nat.add_sub_of_le hs]
    have hsplit := Nat.div_add_mod x (2 ^ s)
    rw [Nat.mul_add, Nat.mul_left_comm, hpow]
    have hmul : (2 ^ W - 1) * (x % 2 ^ s) + x % 2 ^ s = 2 ^ W * (x % 2 ^ s) := by
      rw [Nat.sub_mul, Nat.one_mul]
      have : x % 2 ^ s ≤ 2 ^ W * (x % 2 ^ s) := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos W)
      omega
    rw [Nat.mul_comm (x % 2 ^ s) (2 ^ W)]
    omega
  have hcast : ((2 ^ s * rotR W x s : Nat) : Int) = ((x + (2 ^ W - 1) * (x % 2 ^ s) : Nat) : Int) := by
    rw [hnat]
  have hsub : ((2 ^ W - 1 : Nat) : Int) = (2 : Int) ^ W - 1 := by
    rw [Int.ofNat_sub (Nat.two_pow_pos W), cast_nat_pow]; rfl
  rw [cast_nat_mul, cast_nat_pow, cast_nat_add, cast_nat_mul, hsub] at hcast
  change (2 : Int) ^ s * (rotR W x s : Int) = (x : Int) + ((2 : Int) ^ W - 1) * ((x % 2 ^ s : Nat) : Int) at hcast
  omega

theorem geoSum_lt {step c : Nat} (hstep : 1 ≤ step) : geoSum step c < 2 ^ (c * step) := by
  induction c with
  | zero => simp [geoSum]
  | succ c ih =>
    simp only [geoSum]
    have hpow : 2 ^ ((c + 1) * step) = 2 ^ step * 2 ^ (c * step) := by
      rw [Nat.succ_mul, Nat.pow_add, Nat.mul_comm]
    have hle : 2 ^ step * (geoSum step c + 1) ≤ 2 ^ step * 2 ^ (c * step) :=
      Nat.mul_le_mul_left _ ih
    have h2 : 2 ≤ 2 ^ step := nat_two_pow_ge_two hstep
    rw [Nat.mul_add, Nat.mul_one, ← hpow] at hle
    omega

theorem popcount_add_shift {w a b : Nat} (ha : a < 2 ^ w) :
    popcount (a + 2 ^ w * b) = popcount a + popcount b := by
  have hsp := popcount_split w (a + 2 ^ w * b)
  have hmod : (a + 2 ^ w * b) % 2 ^ w = a := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  have hdiv : (a + 2 ^ w * b) / 2 ^ w = b := by
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos w), Nat.div_eq_of_lt ha, Nat.zero_add]
  rw [hmod, hdiv] at hsp
  exact hsp.symm

theorem popcount_mul_pow_two (w b : Nat) : popcount (2 ^ w * b) = popcount b := by
  have h := popcount_add_shift (w := w) (a := 0) (b := b) (Nat.two_pow_pos w)
  simpa [popcount_zero] using h

theorem popcount_one : popcount 1 = 1 := by
  rw [popcount_step (by decide)]
  simp [popcount_zero]

theorem popcount_all_ones (w : Nat) : popcount (2 ^ w - 1) = w := by
  induction w with
  | zero => simp [popcount_zero]
  | succ w ih =>
    have hpow : 2 ^ (w + 1) - 1 = 1 + 2 * (2 ^ w - 1) := by
      have hp := Nat.two_pow_pos w
      rw [Nat.pow_succ]; omega
    rw [hpow]
    have h := popcount_add_shift (w := 1) (a := 1) (b := 2 ^ w - 1) (by decide)
    simp only [Nat.pow_one] at h
    rw [h, ih, popcount_one]
    omega

theorem popcount_mul_geoSum {step c a : Nat} (ha : a < 2 ^ step) :
    popcount (a * geoSum step c) = c * popcount a := by
  induction c with
  | zero => simp [geoSum, popcount_zero]
  | succ c ih =>
    simp only [geoSum, Nat.mul_add, Nat.mul_one, Nat.mul_left_comm a (2 ^ step)]
    rw [popcount_add_shift ha, ih, Nat.succ_mul]
    omega

theorem geoSum_popcount {step c : Nat} (hstep : 1 ≤ step) :
    popcount (geoSum step c) = c := by
  have h := popcount_mul_geoSum (step := step) (c := c) (a := 1) (by
    have := nat_two_pow_ge_two hstep; omega)
  simpa [popcount_one] using h

/-- Exact doubling factorization of `geoSum`:
    `geoSum step (2 * m) = (1 + 2^(m * step)) * geoSum step m`. -/
theorem geoSum_add (step m n : Nat) :
    geoSum step (m + n) = geoSum step m + 2 ^ (m * step) * geoSum step n := by
  induction m with
  | zero => simp [geoSum]
  | succ m ih =>
    have h1 : (m + 1) + n = (m + n) + 1 := by omega
    rw [h1, geoSum, geoSum, ih, Nat.mul_add]
    have hpow : 2 ^ step * 2 ^ (m * step) = 2 ^ ((m + 1) * step) := by
      rw [Nat.succ_mul, Nat.pow_add, Nat.mul_comm]
    rw [← Nat.mul_assoc, hpow]
    omega

theorem geoSum_double (step m : Nat) :
    geoSum step (2 * m) = (1 + 2 ^ (m * step)) * geoSum step m := by
  have h := geoSum_add step m m
  rw [← Nat.two_mul] at h
  rw [h, Nat.add_mul, Nat.one_mul]

/-- Fermat factor divisibility of `geoSum`: for any `t < e`,
    `(2^(2^t * step) + 1) ∣ geoSum step (2^e)`. -/
theorem fermat_dvd_geoSum (step e t : Nat) (ht : t < e) :
    (2 ^ (2 ^ t * step) + 1) ∣ geoSum step (2 ^ e) := by
  induction e with
  | zero => omega
  | succ e ih =>
    have h2e : 2 ^ (e + 1) = 2 * 2 ^ e := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [h2e, geoSum_double]
    by_cases heq : t = e
    · subst heq
      exact ⟨geoSum step (2 ^ t), by rw [Nat.add_comm]⟩
    · rcases ih (by omega) with ⟨q, hq⟩
      exact ⟨(1 + 2 ^ (2 ^ e * step)) * q, by rw [hq, Nat.mul_left_comm]⟩

/-- Congruence of `geoSum step c` modulo any divisor of `2^step - 1`: `geoSum step c ≡ c`. -/
theorem geoSum_sub_count_dvd (step c : Nat) :
    ((2 : Int) ^ step - 1) ∣ ((geoSum step c : Int) - (c : Int)) := by
  induction c with
  | zero => simp [geoSum]
  | succ c ih =>
    rcases ih with ⟨q, hq⟩
    refine ⟨(2 : Int) ^ step * q + (c : Int), ?_⟩
    simp only [geoSum]
    rw [cast_nat_add, cast_nat_mul, cast_nat_pow, cast_nat_add]
    change (1 : Int) + (2 : Int) ^ step * (geoSum step c : Int) - ((c : Int) + 1) =
        ((2 : Int) ^ step - 1) * ((2 : Int) ^ step * q + (c : Int))
    have h1 : (geoSum step c : Int) = ((2 : Int) ^ step - 1) * q + (c : Int) := by omega
    rw [h1, Int.mul_add, ← Int.mul_assoc,
        Int.mul_comm ((2 : Int) ^ step) ((2 : Int) ^ step - 1), Int.mul_assoc,
        Int.mul_add]
    have h2 : ((2 : Int) ^ step - 1) * (c : Int) = (2 : Int) ^ step * (c : Int) - (c : Int) := by
      rw [Int.sub_mul, Int.one_mul]
    rw [h2]
    omega

theorem lt_two_pow_self (d : Nat) : d < 2 ^ d := by
  induction d with
  | zero => decide
  | succ d ih =>
    rw [Nat.pow_succ]
    omega

theorem d_le_width {d k : Nat} (hk : 1 ≤ k) : d ≤ 2 ^ d * k := by
  have h1 := lt_two_pow_self d
  have h2 : 2 ^ d ≤ 2 ^ d * k := Nat.le_mul_of_pos_right _ hk
  omega

theorem rademacherHiWave_lt {d k j : Nat} (hk : 1 ≤ k) (hj : j < d) :
    rademacherHiWave d k j < 2 ^ (2 ^ d * k) := by
  unfold rademacherHiWave
  let w := 2 ^ j * k
  have hw : 1 ≤ w := Nat.mul_pos (Nat.two_pow_pos j) hk
  have h2w : 2 ^ (j + 1) * k = 2 * w := by
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ j) 2, Nat.mul_assoc]
  have hblock_lt : (2 ^ w - 1) * 2 ^ w < 2 ^ (2 * w) := by
    have hpow : 2 ^ (2 * w) = 2 ^ w * 2 ^ w := by rw [Nat.two_mul, Nat.pow_add]
    have hp : 1 ≤ 2 ^ w := Nat.two_pow_pos w
    rw [hpow, Nat.sub_mul, Nat.one_mul]
    have hle : 2 ^ w ≤ 2 ^ w * 2 ^ w := Nat.le_mul_of_pos_left _ hp
    omega
  have hgeo_lt : geoSum (2 * w) (2 ^ (d - 1 - j)) < 2 ^ (2 ^ (d - 1 - j) * (2 * w)) :=
    geoSum_lt (by omega)
  have hexp_eq : 2 ^ (d - 1 - j) * (2 * w) = 2 ^ d * k := by
    have h1 : 2 ^ (d - 1 - j) * (2 * 2 ^ j) = 2 ^ d := by
      rw [← Nat.pow_succ', ← Nat.pow_add]
      have : (d - 1 - j) + (j + 1) = d := by omega
      rw [this]
    calc 2 ^ (d - 1 - j) * (2 * (2 ^ j * k))
        = (2 ^ (d - 1 - j) * (2 * 2 ^ j)) * k := by
          rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_assoc (2 ^ (d - 1 - j)) 2 (2 ^ j)]
      _ = 2 ^ d * k := by rw [h1]
  rw [h2w]
  -- Use exact algebraic bound: ((2^w - 1) * 2^w) ≤ 2^(2*w) - 1, and (2^(2*w) - 1) * geoSum (2*w) c = 2^(c*2w) - 1!
  have hgeo_exact : (2 ^ (2 * w) - 1) * geoSum (2 * w) (2 ^ (d - 1 - j)) =
      2 ^ (2 ^ (d - 1 - j) * (2 * w)) - 1 := by
    clear hgeo_lt hexp_eq
    generalize 2 ^ (d - 1 - j) = c
    induction c with
    | zero => simp [geoSum]
    | succ c ih =>
      simp only [geoSum, Nat.mul_add, Nat.mul_one, Nat.mul_left_comm (2 ^ (2 * w) - 1) (2 ^ (2 * w)), ih]
      have hpow : 2 ^ ((c + 1) * (2 * w)) = 2 ^ (2 * w) * 2 ^ (c * (2 * w)) := by
        rw [Nat.succ_mul, Nat.pow_add, Nat.mul_comm]
      rw [hpow, Nat.mul_sub, Nat.mul_one]
      have hp1 : 1 ≤ 2 ^ (2 * w) := Nat.two_pow_pos _
      have hp2 : 1 ≤ 2 ^ (c * (2 * w)) := Nat.two_pow_pos _
      have hle : 2 ^ (2 * w) ≤ 2 ^ (2 * w) * 2 ^ (c * (2 * w)) := Nat.le_mul_of_pos_right _ hp2
      omega
  have hle_mul : (2 ^ w - 1) * 2 ^ w * geoSum (2 * w) (2 ^ (d - 1 - j)) ≤
      (2 ^ (2 * w) - 1) * geoSum (2 * w) (2 ^ (d - 1 - j)) :=
    Nat.mul_le_mul_right _ (by omega)
  rw [hgeo_exact, hexp_eq] at hle_mul
  have hp : 1 ≤ 2 ^ (2 ^ d * k) := Nat.two_pow_pos _
  change (2 ^ w - 1) * 2 ^ w * geoSum (2 * w) (2 ^ (d - 1 - j)) < 2 ^ (2 ^ d * k)
  omega

/-- **Theorem 5B (Exact Popcount Laws for Rademacher CRT Idempotents):**
    For ALL `d : Nat`, ALL `k ≥ 1`, and ALL `j < d`:
    - `popcount (idemM d k) = 2 ^ d` (sparse comb of `2^d` bits)
    - `popcount (idemF d k j) = 2 ^ (d - 1) * k` (exact half-weight `W / 2` Rademacher square wave!). -/
theorem idemM_popcount (d k : Nat) (hk : 1 ≤ k) :
    popcount (idemM d k) = 2 ^ d := by
  unfold idemM mersenneComb
  rw [rotR_popcount (d_le_width hk) (geoSum_lt hk), geoSum_popcount hk]

theorem idemF_popcount (d k j : Nat) (hk : 1 ≤ k) (hj : j < d) :
    popcount (idemF d k j) = 2 ^ (d - 1) * k := by
  have hd_le : d - j ≤ 2 ^ d * k := Nat.le_trans (Nat.sub_le d j) (d_le_width hk)
  unfold idemF
  rw [rotR_popcount hd_le (rademacherHiWave_lt hk hj)]
  unfold rademacherHiWave
  let w := 2 ^ j * k
  have h2w : 2 ^ (j + 1) * k = 2 * w := by
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ j) 2, Nat.mul_assoc]
  have hblock_lt : (2 ^ w - 1) * 2 ^ w < 2 ^ (2 * w) := by
    have hpow : 2 ^ (2 * w) = 2 ^ w * 2 ^ w := by rw [Nat.two_mul, Nat.pow_add]
    have hp : 1 ≤ 2 ^ w := Nat.two_pow_pos w
    rw [hpow, Nat.sub_mul, Nat.one_mul]
    have hle : 2 ^ w ≤ 2 ^ w * 2 ^ w := Nat.le_mul_of_pos_left _ hp
    omega
  rw [h2w, popcount_mul_geoSum hblock_lt, Nat.mul_comm (2 ^ w - 1) (2 ^ w),
      popcount_mul_pow_two, popcount_all_ones]
  have hexp : 2 ^ (d - 1 - j) * 2 ^ j = 2 ^ (d - 1) := by
    rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
  calc 2 ^ (d - 1 - j) * (2 ^ j * k) = (2 ^ (d - 1 - j) * 2 ^ j) * k := by rw [Nat.mul_assoc]
    _ = 2 ^ (d - 1) * k := by rw [hexp]

/-- **Theorem 5C (Exact CRT Projection Laws for `idemM` and `idemF`):** -/
theorem idemM_crt_mersenne (d k : Nat) (hk : 1 ≤ k) :
    ((2 : Int) ^ k - 1) ∣ ((idemM d k : Int) - 1) := by
  have hd_le := d_le_width (d := d) hk
  have hrot := rotR_mul_pow_sub_dvd (W := 2 ^ d * k) (x := mersenneComb d k) hd_le
  have hDW := mersenne_dvd_tower d k
  have hrotD : ((2 : Int) ^ k - 1) ∣ ((2 : Int) ^ d * (idemM d k : Int) - (mersenneComb d k : Int)) :=
    Int.dvd_trans hDW hrot
  have hcomb : ((2 : Int) ^ k - 1) ∣ ((mersenneComb d k : Int) - ((2 ^ d : Nat) : Int)) :=
    geoSum_sub_count_dvd k (2 ^ d)
  have hsum : ((2 : Int) ^ k - 1) ∣ ((2 : Int) ^ d * ((idemM d k : Int) - 1)) := by
    rcases hrotD with ⟨q1, hq1⟩
    rcases hcomb with ⟨q2, hq2⟩
    refine ⟨q1 + q2, ?_⟩
    rw [Int.mul_add, ← hq1, ← hq2, Int.mul_sub, Int.mul_one]
    have hp : ((2 ^ d : Nat) : Int) = (2 : Int) ^ d := cast_nat_pow 2 d
    rw [hp]
    omega
  exact dvd_of_dvd_pow_two_mul hd_le hDW hsum

theorem idemM_crt_fermat (d k r : Nat) (hk : 1 ≤ k) (hr : r < d) :
    ((2 : Int) ^ (2 ^ r * k) + 1) ∣ (idemM d k : Int) := by
  have hd_le := d_le_width (d := d) hk
  have hDW := fermat_dvd_tower (k := k) hr
  have hrotD : ((2 : Int) ^ (2 ^ r * k) + 1) ∣
      ((2 : Int) ^ d * (idemM d k : Int) - (mersenneComb d k : Int)) :=
    Int.dvd_trans hDW (rotR_mul_pow_sub_dvd hd_le)
  have hcomb_nat : (2 ^ (2 ^ r * k) + 1) ∣ mersenneComb d k := fermat_dvd_geoSum k d r hr
  have hcomb : ((2 : Int) ^ (2 ^ r * k) + 1) ∣ (mersenneComb d k : Int) := by
    rcases hcomb_nat with ⟨q, hq⟩
    refine ⟨(q : Int), ?_⟩
    have h1 : ((mersenneComb d k : Nat) : Int) = (((2 ^ (2 ^ r * k) + 1) * q : Nat) : Int) := by rw [hq]
    rw [cast_nat_mul, cast_nat_add, cast_nat_pow] at h1
    exact h1
  have hmul : ((2 : Int) ^ (2 ^ r * k) + 1) ∣ ((2 : Int) ^ d * (idemM d k : Int)) := by
    rcases hrotD with ⟨q1, hq1⟩
    rcases hcomb with ⟨q2, hq2⟩
    exact ⟨q1 + q2, by rw [Int.mul_add, ← hq1, ← hq2]; omega⟩
  exact dvd_of_dvd_pow_two_mul hd_le hDW hmul

theorem idemF_crt_mersenne (d k j : Nat) (hk : 1 ≤ k) (_hj : j < d) :
    ((2 : Int) ^ k - 1) ∣ (idemF d k j : Int) := by
  have hs_le : d - j ≤ 2 ^ d * k := Nat.le_trans (Nat.sub_le d j) (d_le_width hk)
  have hDW := mersenne_dvd_tower d k
  have hrotD : ((2 : Int) ^ k - 1) ∣
      ((2 : Int) ^ (d - j) * (idemF d k j : Int) - (rademacherHiWave d k j : Int)) :=
    Int.dvd_trans hDW (rotR_mul_pow_sub_dvd hs_le)
  have hwave : ((2 : Int) ^ k - 1) ∣ (rademacherHiWave d k j : Int) := by
    have h1 := mersenne_dvd_mersenne k (2 ^ j)
    rcases h1 with ⟨q, hq⟩
    unfold rademacherHiWave
    refine ⟨q * ((2 : Int) ^ (2 ^ j * k) * (geoSum (2 ^ (j + 1) * k) (2 ^ (d - 1 - j)) : Int)), ?_⟩
    have hsub : ((2 ^ (2 ^ j * k) - 1 : Nat) : Int) = (2 : Int) ^ (2 ^ j * k) - 1 := by
      rw [Int.ofNat_sub (Nat.two_pow_pos _), cast_nat_pow]; rfl
    rw [cast_nat_mul, cast_nat_mul, hsub, cast_nat_pow]
    change (((2 : Int) ^ (2 ^ j * k) - 1) * (2 : Int) ^ (2 ^ j * k)) *
        (geoSum (2 ^ (j + 1) * k) (2 ^ (d - 1 - j)) : Int) =
      ((2 : Int) ^ k - 1) * (q * ((2 : Int) ^ (2 ^ j * k) * (geoSum (2 ^ (j + 1) * k) (2 ^ (d - 1 - j)) : Int)))
    rw [hq, Int.mul_assoc, Int.mul_assoc]
  have hmul : ((2 : Int) ^ k - 1) ∣ ((2 : Int) ^ (d - j) * (idemF d k j : Int)) := by
    rcases hrotD with ⟨q1, hq1⟩
    rcases hwave with ⟨q2, hq2⟩
    exact ⟨q1 + q2, by rw [Int.mul_add, ← hq1, ← hq2]; omega⟩
  exact dvd_of_dvd_pow_two_mul hs_le hDW hmul

theorem idemF_crt_fermat (d k j r : Nat) (hk : 1 ≤ k) (hj : j < d) (hr : r < d) :
    ((2 : Int) ^ (2 ^ r * k) + 1) ∣ ((idemF d k j : Int) - if r = j then 1 else 0) := by
  have hs_le : d - j ≤ 2 ^ d * k := Nat.le_trans (Nat.sub_le d j) (d_le_width hk)
  have hDW := fermat_dvd_tower (k := k) hr
  have hrotD : ((2 : Int) ^ (2 ^ r * k) + 1) ∣
      ((2 : Int) ^ (d - j) * (idemF d k j : Int) - (rademacherHiWave d k j : Int)) :=
    Int.dvd_trans hDW (rotR_mul_pow_sub_dvd hs_le)
  by_cases hlt : r < j
  · have hne : r ≠ j := by omega
    simp only [hne, ↓reduceIte, Int.sub_zero]
    have h1 := fermat_dvd_tower (d := j) (k := k) hlt
    have hwave : ((2 : Int) ^ (2 ^ r * k) + 1) ∣ (rademacherHiWave d k j : Int) := by
      rcases h1 with ⟨q, hq⟩
      unfold rademacherHiWave
      refine ⟨q * ((2 : Int) ^ (2 ^ j * k) * (geoSum (2 ^ (j + 1) * k) (2 ^ (d - 1 - j)) : Int)), ?_⟩
      have hsub : ((2 ^ (2 ^ j * k) - 1 : Nat) : Int) = (2 : Int) ^ (2 ^ j * k) - 1 := by
        rw [Int.ofNat_sub (Nat.two_pow_pos _), cast_nat_pow]; rfl
      rw [cast_nat_mul, cast_nat_mul, hsub, cast_nat_pow]
      change (((2 : Int) ^ (2 ^ j * k) - 1) * (2 : Int) ^ (2 ^ j * k)) *
          (geoSum (2 ^ (j + 1) * k) (2 ^ (d - 1 - j)) : Int) =
        ((2 : Int) ^ (2 ^ r * k) + 1) * (q * ((2 : Int) ^ (2 ^ j * k) * (geoSum (2 ^ (j + 1) * k) (2 ^ (d - 1 - j)) : Int)))
      rw [hq, Int.mul_assoc, Int.mul_assoc]
    have hmul : ((2 : Int) ^ (2 ^ r * k) + 1) ∣ ((2 : Int) ^ (d - j) * (idemF d k j : Int)) := by
      rcases hrotD with ⟨q1, hq1⟩
      rcases hwave with ⟨q2, hq2⟩
      exact ⟨q1 + q2, by rw [Int.mul_add, ← hq1, ← hq2]; omega⟩
    exact dvd_of_dvd_pow_two_mul hs_le hDW hmul
  · by_cases heq : r = j
    · subst heq
      simp only [↓reduceIte]
      let w := 2 ^ r * k
      have h2w : 2 ^ (r + 1) * k = 2 * w := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ r) 2, Nat.mul_assoc]
      have hblk : ((2 : Int) ^ w + 1) ∣ (((2 : Int) ^ w - 1) * (2 : Int) ^ w - 2) := by
        refine ⟨(2 : Int) ^ w - 2, ?_⟩
        rw [Int.add_mul, Int.mul_sub, Int.sub_mul, Int.one_mul]
        omega
      have hsq : ((2 : Int) ^ w + 1) ∣ ((2 : Int) ^ (2 * w) - 1) := by
        refine ⟨(2 : Int) ^ w - 1, ?_⟩
        have hp : (2 : Int) ^ (2 * w) = (2 : Int) ^ w * (2 : Int) ^ w := by
          rw [Nat.two_mul, Int.pow_add]
        rw [hp, Int.add_mul, Int.mul_sub, Int.mul_one, Int.one_mul]
        omega
      have hgeo : ((2 : Int) ^ w + 1) ∣
          ((geoSum (2 * w) (2 ^ (d - 1 - r)) : Int) - ((2 ^ (d - 1 - r) : Nat) : Int)) :=
        Int.dvd_trans hsq (geoSum_sub_count_dvd (2 * w) (2 ^ (d - 1 - r)))
      have hwave : ((2 : Int) ^ w + 1) ∣ ((rademacherHiWave d k r : Int) - (2 : Int) ^ (d - r)) := by
        unfold rademacherHiWave
        rw [h2w]
        have hsub : ((2 ^ w - 1 : Nat) : Int) = (2 : Int) ^ w - 1 := by
          rw [Int.ofNat_sub (Nat.two_pow_pos _), cast_nat_pow]; rfl
        rw [cast_nat_mul, cast_nat_mul, hsub, cast_nat_pow]
        rcases hblk with ⟨q1, hq1⟩
        rcases hgeo with ⟨q2, hq2⟩
        have hpow_dr : (2 : Int) * (2 : Int) ^ (d - 1 - r) = (2 : Int) ^ (d - r) := by
          have hexp : d - r = (d - 1 - r) + 1 := by omega
          conv => rhs; rw [hexp, Int.pow_succ]
          rw [Int.mul_comm]
        have hpow_cast : ((2 ^ (d - 1 - r) : Nat) : Int) = (2 : Int) ^ (d - 1 - r) :=
          cast_nat_pow 2 (d - 1 - r)
        rw [hpow_cast] at hq2
        refine ⟨q1 * (geoSum (2 * w) (2 ^ (d - 1 - r)) : Int) + 2 * q2, ?_⟩
        have hA : ((2 : Int) ^ w - 1) * (2 : Int) ^ w = ((2 : Int) ^ w + 1) * q1 + 2 := by omega
        have hB : (geoSum (2 * w) (2 ^ (d - 1 - r)) : Int) =
            ((2 : Int) ^ w + 1) * q2 + (2 : Int) ^ (d - 1 - r) := by omega
        have h2q : 2 * (((2 : Int) ^ w + 1) * q2) = ((2 : Int) ^ w + 1) * (2 * q2) := by
          rw [← Int.mul_assoc, Int.mul_comm 2 ((2 : Int) ^ w + 1), Int.mul_assoc]
        calc (((2 : Int) ^ w - 1) * (2 : Int) ^ w) * (geoSum (2 * w) (2 ^ (d - 1 - r)) : Int) -
              (2 : Int) ^ (d - r)
            = (((2 : Int) ^ w + 1) * q1 + 2) * (geoSum (2 * w) (2 ^ (d - 1 - r)) : Int) -
              (2 : Int) ^ (d - r) := by rw [hA]
          _ = ((2 : Int) ^ w + 1) * (q1 * (geoSum (2 * w) (2 ^ (d - 1 - r)) : Int)) +
              2 * (((2 : Int) ^ w + 1) * q2 + (2 : Int) ^ (d - 1 - r)) - (2 : Int) ^ (d - r) := by
                rw [Int.add_mul, Int.mul_assoc, hB]
          _ = ((2 : Int) ^ w + 1) * (q1 * (geoSum (2 * w) (2 ^ (d - 1 - r)) : Int) + 2 * q2) := by
                rw [Int.mul_add, h2q, hpow_dr, Int.mul_add]
                omega
      have hmul : ((2 : Int) ^ w + 1) ∣ ((2 : Int) ^ (d - r) * ((idemF d k r : Int) - 1)) := by
        rcases hrotD with ⟨q1, hq1⟩
        rcases hwave with ⟨q2, hq2⟩
        exact ⟨q1 + q2, by rw [Int.mul_add, ← hq1, ← hq2, Int.mul_sub, Int.mul_one]; omega⟩
      exact dvd_of_dvd_pow_two_mul hs_le hDW hmul
    · have hgt : j < r := by omega
      simp only [heq, ↓reduceIte, Int.sub_zero]
      have hgeo_nat : (2 ^ (2 ^ r * k) + 1) ∣ geoSum (2 ^ (j + 1) * k) (2 ^ (d - 1 - j)) := by
        have hstep := fermat_dvd_geoSum (2 ^ (j + 1) * k) (d - 1 - j) (r - (j + 1)) (by omega)
        have hexp : 2 ^ (r - (j + 1)) * (2 ^ (j + 1) * k) = 2 ^ r * k := by
          rw [← Nat.mul_assoc, ← Nat.pow_add, Nat.sub_add_cancel (by omega)]
        rwa [hexp] at hstep
      have hwave : ((2 : Int) ^ (2 ^ r * k) + 1) ∣ (rademacherHiWave d k j : Int) := by
        rcases hgeo_nat with ⟨q, hq⟩
        unfold rademacherHiWave
        refine ⟨(((2 ^ (2 ^ j * k) - 1) * 2 ^ (2 ^ j * k) : Nat) : Int) * (q : Int), ?_⟩
        have hcast : ((geoSum (2 ^ (j + 1) * k) (2 ^ (d - 1 - j)) : Nat) : Int) =
            ((2 : Int) ^ (2 ^ r * k) + 1) * (q : Int) := by
          rw [hq, cast_nat_mul, cast_nat_add, cast_nat_pow]; rfl
        rw [cast_nat_mul, hcast, ← Int.mul_assoc, Int.mul_comm _ ((2 : Int) ^ (2 ^ r * k) + 1), Int.mul_assoc]
      have hmul : ((2 : Int) ^ (2 ^ r * k) + 1) ∣ ((2 : Int) ^ (d - j) * (idemF d k j : Int)) := by
        rcases hrotD with ⟨q1, hq1⟩
        rcases hwave with ⟨q2, hq2⟩
        exact ⟨q1 + q2, by rw [Int.mul_add, ← hq1, ← hq2]; omega⟩
      exact dvd_of_dvd_pow_two_mul hs_le hDW hmul

/-- **Theorem 5D (Idempotence, Pairwise Orthogonality & Partition of Unity mod `2^(2^d * k) - 1`):** -/
theorem idemM_idempotent (d k : Nat) (hk : 1 ≤ k) :
    ((2 : Int) ^ (2 ^ d * k) - 1) ∣ ((idemM d k : Int) * (idemM d k : Int) - (idemM d k : Int)) := by
  apply tower_crt_dvd d k hk
  · rcases idemM_crt_mersenne d k hk with ⟨q, hq⟩
    refine ⟨(idemM d k : Int) * q, ?_⟩
    rw [← Int.mul_assoc, Int.mul_comm ((2 : Int) ^ k - 1) (idemM d k : Int), Int.mul_assoc,
        ← hq, Int.mul_sub, Int.mul_one]
  · intro r hr
    rcases idemM_crt_fermat d k r hk hr with ⟨q, hq⟩
    refine ⟨((idemM d k : Int) - 1) * q, ?_⟩
    rw [← Int.mul_assoc, Int.mul_comm ((2 : Int) ^ (2 ^ r * k) + 1) ((idemM d k : Int) - 1),
        Int.mul_assoc, ← hq, Int.sub_mul, Int.one_mul]

theorem idemF_idempotent (d k j : Nat) (hk : 1 ≤ k) (hj : j < d) :
    ((2 : Int) ^ (2 ^ d * k) - 1) ∣ ((idemF d k j : Int) * (idemF d k j : Int) - (idemF d k j : Int)) := by
  apply tower_crt_dvd d k hk
  · rcases idemF_crt_mersenne d k j hk hj with ⟨q, hq⟩
    refine ⟨((idemF d k j : Int) - 1) * q, ?_⟩
    rw [← Int.mul_assoc, Int.mul_comm ((2 : Int) ^ k - 1) ((idemF d k j : Int) - 1),
        Int.mul_assoc, ← hq, Int.sub_mul, Int.one_mul]
  · intro r hr
    have h := idemF_crt_fermat d k j r hk hj hr
    by_cases heq : r = j
    · subst heq
      simp only [↓reduceIte] at h
      rcases h with ⟨q, hq⟩
      refine ⟨(idemF d k r : Int) * q, ?_⟩
      rw [← Int.mul_assoc, Int.mul_comm ((2 : Int) ^ (2 ^ r * k) + 1) (idemF d k r : Int),
          Int.mul_assoc, ← hq, Int.mul_sub, Int.mul_one]
    · simp only [heq, ↓reduceIte, Int.sub_zero] at h
      rcases h with ⟨q, hq⟩
      refine ⟨((idemF d k j : Int) - 1) * q, ?_⟩
      rw [← Int.mul_assoc, Int.mul_comm ((2 : Int) ^ (2 ^ r * k) + 1) ((idemF d k j : Int) - 1),
          Int.mul_assoc, ← hq, Int.sub_mul, Int.one_mul]

theorem idem_orthogonal_MF (d k j : Nat) (hk : 1 ≤ k) (hj : j < d) :
    ((2 : Int) ^ (2 ^ d * k) - 1) ∣ ((idemM d k : Int) * (idemF d k j : Int)) := by
  apply tower_crt_dvd d k hk
  · rcases idemF_crt_mersenne d k j hk hj with ⟨q, hq⟩
    exact ⟨(idemM d k : Int) * q, by rw [← Int.mul_assoc, Int.mul_comm _ (idemM d k : Int), Int.mul_assoc, ← hq]⟩
  · intro r hr
    rcases idemM_crt_fermat d k r hk hr with ⟨q, hq⟩
    exact ⟨q * (idemF d k j : Int), by rw [← Int.mul_assoc, ← hq]⟩

theorem idem_orthogonal_FF (d k i j : Nat) (hk : 1 ≤ k) (hi : i < d) (hj : j < d) (hne : i ≠ j) :
    ((2 : Int) ^ (2 ^ d * k) - 1) ∣ ((idemF d k i : Int) * (idemF d k j : Int)) := by
  apply tower_crt_dvd d k hk
  · rcases idemF_crt_mersenne d k i hk hi with ⟨q, hq⟩
    exact ⟨q * (idemF d k j : Int), by rw [← Int.mul_assoc, ← hq]⟩
  · intro r hr
    by_cases hri : r = i
    · have hrj : r ≠ j := by omega
      have h := idemF_crt_fermat d k j r hk hj hr
      simp only [hrj, ↓reduceIte, Int.sub_zero] at h
      rcases h with ⟨q, hq⟩
      exact ⟨(idemF d k i : Int) * q, by rw [← Int.mul_assoc, Int.mul_comm _ (idemF d k i : Int), Int.mul_assoc, ← hq]⟩
    · have h := idemF_crt_fermat d k i r hk hi hr
      simp only [hri, ↓reduceIte, Int.sub_zero] at h
      rcases h with ⟨q, hq⟩
      exact ⟨q * (idemF d k j : Int), by rw [← Int.mul_assoc, ← hq]⟩

theorem sumIdemF_dvd_mersenne (d k m : Nat) (hk : 1 ≤ k) (hm : m ≤ d) :
    ((2 : Int) ^ k - 1) ∣ sumIdemF d k m := by
  induction m with
  | zero => simp [sumIdemF]
  | succ m ih =>
    simp only [sumIdemF]
    exact Int.dvd_add (ih (by omega)) (idemF_crt_mersenne d k m hk (by omega))

theorem sumIdemF_dvd_fermat (d k m r : Nat) (hk : 1 ≤ k) (hm : m ≤ d) (hr : r < d) :
    ((2 : Int) ^ (2 ^ r * k) + 1) ∣ (sumIdemF d k m - if r < m then 1 else 0) := by
  induction m with
  | zero => simp [sumIdemF]
  | succ m ih =>
    simp only [sumIdemF]
    have hprev := ih (by omega)
    have hcur := idemF_crt_fermat d k m r hk (by omega) hr
    by_cases hlt : r < m
    · have hlts : r < m + 1 := by omega
      have hne : r ≠ m := by omega
      simp only [hlt, hlts, hne, ↓reduceIte, Int.sub_zero] at hprev hcur ⊢
      rcases hprev with ⟨q1, hq1⟩
      rcases hcur with ⟨q2, hq2⟩
      exact ⟨q1 + q2, by rw [Int.mul_add, ← hq1, ← hq2]; omega⟩
    · by_cases heq : r = m
      · subst heq
        have hlts : r < r + 1 := by omega
        have hnlt : ¬(r < r) := by omega
        simp only [hnlt, ↓reduceIte, Int.sub_zero] at hprev
        simp only [↓reduceIte] at hcur
        simp only [hlts, ↓reduceIte]
        rcases hprev with ⟨q1, hq1⟩
        rcases hcur with ⟨q2, hq2⟩
        exact ⟨q1 + q2, by rw [Int.mul_add, ← hq1, ← hq2]; omega⟩
      · have hnlts : ¬(r < m + 1) := by omega
        simp only [hlt, hnlts, heq, ↓reduceIte, Int.sub_zero] at hprev hcur ⊢
        exact Int.dvd_add hprev hcur

theorem idem_partition_of_unity (d k : Nat) (hk : 1 ≤ k) :
    ((2 : Int) ^ (2 ^ d * k) - 1) ∣ ((idemM d k : Int) + sumIdemF d k d - 1) := by
  apply tower_crt_dvd d k hk
  · rcases idemM_crt_mersenne d k hk with ⟨q1, hq1⟩
    rcases sumIdemF_dvd_mersenne d k d hk (Nat.le_refl d) with ⟨q2, hq2⟩
    exact ⟨q1 + q2, by rw [Int.mul_add, ← hq1, ← hq2]; omega⟩
  · intro r hr
    rcases idemM_crt_fermat d k r hk hr with ⟨q1, hq1⟩
    have hf := sumIdemF_dvd_fermat d k d r hk (Nat.le_refl d) hr
    simp only [hr, ↓reduceIte] at hf
    rcases hf with ⟨q2, hq2⟩
    exact ⟨q1 + q2, by rw [Int.mul_add, ← hq1, ← hq2]; omega⟩

theorem butterflyLift_exact {w : Nat} (hw : 1 ≤ w) {x a b : Int}
    (ha : ((2 : Int) ^ w - 1) ∣ (a - x))
    (hb : ((2 : Int) ^ w + 1) ∣ (b - x)) :
    ((2 : Int) ^ (2 * w) - 1) ∣ (butterflyLift w a b - x) := by
  have hpow2 : (2 : Int) ^ (w - 1) * 2 = (2 : Int) ^ w := by
    have hsub : w = (w - 1) + 1 := by omega
    conv => rhs; rw [hsub, Int.pow_succ]
  apply coprime_mersenne_fermat_dvd hw
  · have h1 : ((2 : Int) ^ w - 1) ∣ (butterflyLift w a b - a) := by
      refine ⟨(2 : Int) ^ (w - 1) * (a + b) + a, ?_⟩
      unfold butterflyLift
      have hlin : (a + b) * (2 : Int) ^ w + (a - b) =
          (a + b) * ((2 : Int) ^ w - 1) + 2 * a := by
        rw [Int.mul_sub, Int.mul_one]; omega
      calc (2 : Int) ^ (w - 1) * ((a + b) * (2 : Int) ^ w + (a - b)) - a
          = (2 : Int) ^ (w - 1) * ((a + b) * ((2 : Int) ^ w - 1) + 2 * a) - a := by rw [hlin]
        _ = (2 : Int) ^ (w - 1) * ((a + b) * ((2 : Int) ^ w - 1)) +
            ((2 : Int) ^ (w - 1) * 2) * a - a := by
              rw [Int.mul_add, Int.mul_assoc ((2 : Int) ^ (w - 1)) 2 a]
        _ = ((2 : Int) ^ w - 1) * ((2 : Int) ^ (w - 1) * (a + b)) + ((2 : Int) ^ w - 1) * a := by
              have hA : (2 : Int) ^ (w - 1) * ((a + b) * ((2 : Int) ^ w - 1)) =
                  ((2 : Int) ^ w - 1) * ((2 : Int) ^ (w - 1) * (a + b)) := by
                rw [← Int.mul_assoc, Int.mul_comm ((2 : Int) ^ (w - 1) * (a + b)) ((2 : Int) ^ w - 1)]
              have hB : (2 : Int) ^ w * a - a = ((2 : Int) ^ w - 1) * a := by
                rw [Int.sub_mul, Int.one_mul]
              rw [hpow2, hA]; omega
        _ = ((2 : Int) ^ w - 1) * ((2 : Int) ^ (w - 1) * (a + b) + a) := by
              rw [← Int.mul_add]
    rcases h1 with ⟨q1, hq1⟩
    rcases ha with ⟨q2, hq2⟩
    exact ⟨q1 + q2, by rw [Int.mul_add, ← hq1, ← hq2]; omega⟩
  · have h1 : ((2 : Int) ^ w + 1) ∣ (butterflyLift w a b - b) := by
      refine ⟨(2 : Int) ^ (w - 1) * (a + b) - b, ?_⟩
      unfold butterflyLift
      have hlin : (a + b) * (2 : Int) ^ w + (a - b) =
          (a + b) * ((2 : Int) ^ w + 1) - 2 * b := by
        rw [Int.mul_add, Int.mul_one]; omega
      calc (2 : Int) ^ (w - 1) * ((a + b) * (2 : Int) ^ w + (a - b)) - b
          = (2 : Int) ^ (w - 1) * ((a + b) * ((2 : Int) ^ w + 1) - 2 * b) - b := by rw [hlin]
        _ = (2 : Int) ^ (w - 1) * ((a + b) * ((2 : Int) ^ w + 1)) -
            ((2 : Int) ^ (w - 1) * 2) * b - b := by
              rw [Int.mul_sub, Int.mul_assoc ((2 : Int) ^ (w - 1)) 2 b]
        _ = ((2 : Int) ^ w + 1) * ((2 : Int) ^ (w - 1) * (a + b)) - ((2 : Int) ^ w + 1) * b := by
              have hA : (2 : Int) ^ (w - 1) * ((a + b) * ((2 : Int) ^ w + 1)) =
                  ((2 : Int) ^ w + 1) * ((2 : Int) ^ (w - 1) * (a + b)) := by
                rw [← Int.mul_assoc, Int.mul_comm ((2 : Int) ^ (w - 1) * (a + b)) ((2 : Int) ^ w + 1)]
              have hB : ((2 : Int) ^ w + 1) * b = (2 : Int) ^ w * b + b := by
                rw [Int.add_mul, Int.one_mul]
              rw [hpow2, hA, hB]; omega
        _ = ((2 : Int) ^ w + 1) * ((2 : Int) ^ (w - 1) * (a + b) - b) := by
              rw [Int.mul_sub]
    rcases h1 with ⟨q1, hq1⟩
    rcases hb with ⟨q2, hq2⟩
    exact ⟨q1 + q2, by rw [Int.mul_add, ← hq1, ← hq2]; omega⟩

theorem dyadicFoldTree_len (d k : Nat) (x : Int) :
    (dyadicFoldTree d k x).2.length = d := by
  induction d generalizing x with
  | zero => simp [dyadicFoldTree]
  | succ d ih =>
    simp only [dyadicFoldTree]
    have h := ih (x % (2 : Int) ^ (2 ^ d * k) + x / (2 : Int) ^ (2 ^ d * k))
    simp [h]

theorem dyadic_butterfly_dvd (d k : Nat) (hk : 1 ≤ k) (x : Int) :
    ((2 : Int) ^ (2 ^ d * k) - 1) ∣ (dyadicButterflyRecon d k (dyadicFoldTree d k x) - x) := by
  induction d generalizing x with
  | zero => simp [dyadicFoldTree, dyadicButterflyRecon]
  | succ d ih =>
    let w := 2 ^ d * k
    have hw : 1 ≤ w := Nat.mul_pos (Nat.two_pow_pos d) hk
    let yM := x % (2 : Int) ^ w + x / (2 : Int) ^ w
    let yF := x % (2 : Int) ^ w - x / (2 : Int) ^ w
    have hlen : (dyadicFoldTree d k yM).2.length = d := dyadicFoldTree_len d k yM
    have htake : ((dyadicFoldTree d k yM).2 ++ [yF]).take d = (dyadicFoldTree d k yM).2 := by
      rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    have hget : ((dyadicFoldTree d k yM).2 ++ [yF]).getD d 0 = yF := by
      simp [List.getD, hlen]
    have hrec_eq : dyadicButterflyRecon (d + 1) k (dyadicFoldTree (d + 1) k x) =
        butterflyLift w (dyadicButterflyRecon d k (dyadicFoldTree d k yM)) yF := by
      simp only [dyadicFoldTree, dyadicButterflyRecon]
      rw [htake, hget]
    rw [hrec_eq]
    have hsplit : x = (2 : Int) ^ w * (x / (2 : Int) ^ w) + x % (2 : Int) ^ w := by
      have := Int.emod_add_mul_ediv x ((2 : Int) ^ w); omega
    have hyM_sub : ((2 : Int) ^ w - 1) ∣ (yM - x) := by
      refine ⟨-(x / (2 : Int) ^ w), ?_⟩
      rw [Int.mul_neg, Int.sub_mul, Int.one_mul]; omega
    have hyF_sub : ((2 : Int) ^ w + 1) ∣ (yF - x) := by
      refine ⟨-(x / (2 : Int) ^ w), ?_⟩
      rw [Int.mul_neg, Int.add_mul, Int.one_mul]; omega
    have ha : ((2 : Int) ^ w - 1) ∣ (dyadicButterflyRecon d k (dyadicFoldTree d k yM) - x) := by
      rcases ih yM with ⟨q1, hq1⟩
      rcases hyM_sub with ⟨q2, hq2⟩
      exact ⟨q1 + q2, by rw [Int.mul_add, ← hq1, ← hq2]; omega⟩
    have hcomb := butterflyLift_exact hw ha hyF_sub
    have hexp : 2 * w = 2 ^ (d + 1) * k := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ d) 2, Nat.mul_assoc]
    rwa [hexp] at hcomb

/-- **Theorem 5E (Pure-Silicon Dyadic Bit-Folding Tree ↔ Butterfly Exact Isomorphism):**
    For ALL tower depths `d : Nat`, ALL base limb widths `k ≥ 1`, and ALL integers `x : Int`,
    folding `x` down the `d`-level Mersenne/Fermat binary tree and lifting via the
    pure bit-shift butterfly recovers `x mod (2^(2^d * k) - 1)` EXACTLY! -/
theorem dyadic_butterfly_exact (d k : Nat) (hk : 1 ≤ k) (x : Int) :
    dyadicButterflyRecon d k (dyadicFoldTree d k x) % ((2 : Int) ^ (2 ^ d * k) - 1) =
    x % ((2 : Int) ^ (2 ^ d * k) - 1) :=
  int_emod_eq_of_dvd_sub (dyadic_butterfly_dvd d k hk x)

-- ============================================================================
-- Section 6: Kernel-Checked Non-Vacuity Witnesses & Axiom Audit
-- ============================================================================

/-- Non-Vacuity Witness 1: Concrete instantiation of the 5-step canonical Fermat circuit
    at `k = 3` (`2^3 + 1 = 9`, `8k = 24`-bit input `x = 12345678 < 2^24`). -/
example :
    evalProg 3 [⟨4, .pos⟩, ⟨2, .pos⟩, ⟨2, .pos⟩, ⟨1, .neg⟩, ⟨1, .neg⟩] 12345678 =
    (12345678 : Int) % 9 :=
  compiled_fermat_5step_8limb_canonical 3 (by decide) 12345678 (by decide) (by decide)

/-- Non-Vacuity Witness 2: Concrete instantiation of exact carry conservation comparing
    sequential `[1,1,1,1,1]` vs dyadic `[4,2,2,1,1]` on `k = 3`, `n = 4095 = 2^12 - 1`. -/
example :
    evalNatMersenne 3 [1, 1, 1, 1, 1] 4095 = evalNatMersenne 3 [4, 2, 2, 1, 1] 4095 ∧
    carryNatMersenne 3 [1, 1, 1, 1, 1] 4095 = carryNatMersenne 3 [4, 2, 2, 1, 1] 4095 ∧
    carryNatMersenne 3 [4, 2, 2, 1, 1] 4095 = 9 := by
  have hcons := total_carry_conservation (k := 3) (by decide)
    (strides := [4, 2, 2, 1, 1]) (by decide) (n := 4095) (by decide)
  have hinv := carry_schedule_invariance (k := 3) (by decide)
    (s1 := [1, 1, 1, 1, 1]) (s2 := [4, 2, 2, 1, 1]) (by decide) (by decide)
    (n := 4095) (by decide) (by decide)
  have hp4095 : popcount 4095 = 12 := popcount_all_ones 12
  have hp7 : popcount (canonM 3 4095) = 3 := by
    have hcanon : canonM 3 4095 = 2 ^ 3 - 1 := by decide
    rw [hcanon]
    exact popcount_all_ones 3
  refine ⟨hinv.1, hinv.2, ?_⟩
  rw [hcons.2, hp4095, hp7]

/-- Negative / Mutation Rejection Tests on the Finite-to-Infinite Compiler:
    mutating stride parity or weakening `B0` from `4` to `2` is deterministically rejected! -/
example :
    checkCong .neg [⟨2, .neg⟩] = false ∧
    checkCong .pos [⟨1, .neg⟩] = false ∧
    checkCircuit .pos 2 [⟨4, .pos⟩, ⟨2, .pos⟩, ⟨1, .pos⟩, ⟨1, .pos⟩, ⟨1, .pos⟩]
      ([], [-1, 0, 0, 0, 0, 0, 0, 0, 1]) ([], [-1, 1]) = false := by
  decide

/-- Non-Vacuity Witness 3: Concrete Rademacher idempotent popcounts at `d = 3, k = 3` (`W = 24`):
    `popcount(idemM 3 3) = 8 = 2^3` and `popcount(idemF 3 3 j) = 12 = W/2` for `j = 0, 1, 2`. -/
example :
    popcount (idemM 3 3) = 8 ∧
    popcount (idemF 3 3 0) = 12 ∧
    popcount (idemF 3 3 1) = 12 ∧
    popcount (idemF 3 3 2) = 12 :=
  ⟨idemM_popcount 3 3 (by decide),
   idemF_popcount 3 3 0 (by decide) (by decide),
   idemF_popcount 3 3 1 (by decide) (by decide),
   idemF_popcount 3 3 2 (by decide) (by decide)⟩

/-- Non-Vacuity Witness 4: Concrete dual-end sharpness of signed Fermat folding at `k = 4, r = 3`:
    inside `[-4096, 4111]` lands in `[-1, 16]`; at `4112` lands at `-2`; at `-4097` lands at `17`. -/
example :
    (-1 ≤ iterFoldF 4 3 4111 ∧ iterFoldF 4 3 4111 ≤ 16) ∧
    iterFoldF 4 3 4112 = -2 ∧
    iterFoldF 4 3 (-4097) = 17 := by
  refine ⟨fermat_exact_envelope 4 3 4111 (by decide) (by decide), ?_, ?_⟩
  · exact (fermat_dual_end_sharp 4 3).1
  · exact (fermat_dual_end_sharp 4 3).2

-- ============================================================================
-- Section 7: Generalized Crandall (2^k - c) Bit-Folding & Exact 3-Round
--            Phase-Transition Iff Theorem (∀ c ≥ 2, ∀ k with 2^k > c)
-- ============================================================================

/-- Generalized Crandall bit-fold modulo `2^k - c` (e.g. `c = 1` Mersenne,
    `c = 19` Curve25519 `2^255 - 19`, arbitrary pseudo-Mersenne moduli). -/
def foldCrandall (k c n : Nat) : Nat := n % 2 ^ k + c * (n / 2 ^ k)

/-- Exact congruence invariance of Crandall bit-folding modulo `2^k - c`. -/
theorem foldCrandall_mod_eq (k c n : Nat) (hB : c < 2 ^ k) :
    foldCrandall k c n % (2 ^ k - c) = n % (2 ^ k - c) := by
  have hsplit := Nat.div_add_mod n (2 ^ k)
  have heq : n = (2 ^ k - c) * (n / 2 ^ k) + (n % 2 ^ k + c * (n / 2 ^ k)) := by
    have hmul : 2 ^ k * (n / 2 ^ k) = (2 ^ k - c) * (n / 2 ^ k) + c * (n / 2 ^ k) := by
      rw [Nat.sub_mul]
      have hle : c * (n / 2 ^ k) ≤ 2 ^ k * (n / 2 ^ k) := Nat.mul_le_mul_right _ (by omega)
      omega
    omega
  unfold foldCrandall
  conv => rhs; rw [heq]
  rw [Nat.mul_add_mod]

/-- Exact 1-round Crandall threshold `2 * 2^k - c` (with single-integer sharpness). -/
theorem crandall_1round_threshold (k c : Nat) (hc : 1 ≤ c) (hB : c < 2 ^ k) :
    (∀ n, n < 2 * 2 ^ k - c → foldCrandall k c n < 2 ^ k) ∧
    foldCrandall k c (2 * 2 ^ k - c) = 2 ^ k := by
  constructor
  · intro n hn
    have hsplit := Nat.div_add_mod n (2 ^ k)
    have hrem := Nat.mod_lt n (Nat.two_pow_pos k)
    have hq_le : n / 2 ^ k ≤ 1 := by
      by_cases hgt : 2 ≤ n / 2 ^ k
      · have hmul : 2 * 2 ^ k ≤ 2 ^ k * (n / 2 ^ k) := by
          rw [Nat.mul_comm 2 (2 ^ k)]
          exact Nat.mul_le_mul_left _ hgt
        omega
      · omega
    unfold foldCrandall
    by_cases hq0 : n / 2 ^ k = 0
    · rw [hq0, Nat.mul_zero, Nat.add_zero]; exact hrem
    · have hq1 : n / 2 ^ k = 1 := Nat.le_antisymm hq_le (Nat.pos_of_ne_zero hq0)
      rw [hq1, Nat.mul_one] at hsplit ⊢
      omega
  · unfold foldCrandall
    have heq : 2 * 2 ^ k - c = (2 ^ k - c) + 2 ^ k * 1 := by omega
    have hlt : 2 ^ k - c < 2 ^ k := by omega
    rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt,
        Nat.add_mul_div_left _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hlt]
    omega

/-- **Theorem 7A (Universal 2-Round Impossibility for Crandall `c ≥ 2`):**
    Unlike Mersenne (`c = 1`), 2 Crandall folds NEVER absorb `[0, 2^(2k) - 1]` for ANY `c ≥ 2`
    and ANY `k` with `c < 2^k`: `n = 2^(2k) - 1` always lands at `2^k + c^2 - c - 1 ≥ 2^k + 1`! -/
theorem crandall_2round_always_fails (k c : Nat) (hc : 2 ≤ c) (hB : c < 2 ^ k) :
    foldCrandall k c (foldCrandall k c (2 ^ (2 * k) - 1)) = 2 ^ k + c * c - c - 1 ∧
    2 ^ k + 1 ≤ foldCrandall k c (foldCrandall k c (2 ^ (2 * k) - 1)) := by
  let B := 2 ^ k
  have hB_pos : 0 < B := Nat.two_pow_pos k
  have hsq : 2 ^ (2 * k) = B * B := by rw [Nat.two_mul, Nat.pow_add]
  have h1 : foldCrandall k c (2 ^ (2 * k) - 1) = c * B + (B - c - 1) := by
    unfold foldCrandall
    have heq : 2 ^ (2 * k) - 1 = (B - 1) + B * (B - 1) := by
      rw [hsq, Nat.mul_sub, Nat.mul_one]
      have hle : B ≤ B * B := Nat.le_mul_of_pos_left _ hB_pos
      omega
    have hlt : B - 1 < B := by omega
    rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt,
        Nat.add_mul_div_left _ _ hB_pos, Nat.div_eq_of_lt hlt, Nat.zero_add,
        Nat.mul_sub, Nat.mul_one]
    have hle : c ≤ c * B := Nat.le_mul_of_pos_right _ hB_pos
    omega
  have h2 : foldCrandall k c (c * B + (B - c - 1)) = B + c * c - c - 1 := by
    unfold foldCrandall
    have heq : c * B + (B - c - 1) = (B - c - 1) + B * c := by rw [Nat.mul_comm, Nat.add_comm]
    have hlt : B - c - 1 < B := by omega
    rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt,
        Nat.add_mul_div_left _ _ hB_pos, Nat.div_eq_of_lt hlt, Nat.zero_add]
    have hcc : c ≤ c * c := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hcc_ge : c + 2 ≤ c * c := by
    have hmul : c * 2 ≤ c * c := Nat.mul_le_mul_left c hc
    omega
  rw [h1, h2]
  exact ⟨rfl, by omega⟩

/-- **Theorem 7B (Exact Crandall 3-Round Phase-Transition Iff Theorem):**
    For ALL `c ≥ 2` and ALL `k ≥ 1` with `c < 2^k`:
    3 Crandall folds absorb ALL `2k`-bit products `n < 2^(2k)` into `[0, 2^k - 1]`
    **IF AND ONLY IF** `c^2 ≤ 2^k`!
    (Necessity constructs a closed-form universal counterexample `n* < 2^(2k)` whenever `c < 2^k < c^2`.) -/
theorem crandall_3round_iff_sq_le_base (k c : Nat) (hc : 2 ≤ c) (hB : c < 2 ^ k) :
    (∀ n, n < 2 ^ (2 * k) →
      foldCrandall k c (foldCrandall k c (foldCrandall k c n)) < 2 ^ k) ↔ c * c ≤ 2 ^ k := by
  let B := 2 ^ k
  have hB_pos : 0 < B := Nat.two_pow_pos k
  have hsq : 2 ^ (2 * k) = B * B := by rw [Nat.two_mul, Nat.pow_add]
  constructor
  · -- Necessity: if B < c^2, construct explicit counterexample n* < B^2 with F^3(n*) ≥ B!
    intro hall
    exact Decidable.byContradiction fun hnot => by
      have hlt_cc : B < c * c := by omega
      let q1 := B / c
      have hq1_lt : q1 < c := by
        rw [Nat.div_lt_iff_lt_mul (by omega : 0 < c)]
        exact hlt_cc
      have hq1_le : q1 ≤ c - 1 := by omega
      let y1 := q1 * B + (B - 1)
      have hy1_lt : y1 < c * B := by
        have hmul : (q1 + 1) * B ≤ c * B := Nat.mul_le_mul_right B (by omega)
        rw [Nat.add_mul, Nat.one_mul] at hmul
        omega
      let nStar := (y1 / c) * B + (y1 % c)
      have hnStar_q : y1 / c < B := by
        rw [Nat.div_lt_iff_lt_mul (by omega : 0 < c), Nat.mul_comm]
        exact hy1_lt
      have hnStar_r : y1 % c < B := Nat.lt_trans (Nat.mod_lt y1 (by omega)) hB
      have hnStar_lt : nStar < 2 ^ (2 * k) := by
        rw [hsq]
        have hmul : (y1 / c + 1) * B ≤ B * B := Nat.mul_le_mul_right B hnStar_q
        rw [Nat.add_mul, Nat.one_mul] at hmul
        omega
      -- Step 1: foldCrandall k c nStar = y1
      have hf1 : foldCrandall k c nStar = y1 := by
        unfold foldCrandall
        have heq : nStar = (y1 % c) + B * (y1 / c) := by
          change (y1 / c) * B + (y1 % c) = (y1 % c) + B * (y1 / c)
          rw [Nat.mul_comm, Nat.add_comm]
        rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hnStar_r,
            Nat.add_mul_div_left _ _ hB_pos, Nat.div_eq_of_lt hnStar_r, Nat.zero_add]
        have hdiv := Nat.div_add_mod y1 c
        omega
      -- Step 2: foldCrandall k c y1 = (B - 1) + c * q1 = B + (B - 1 - B % c)
      have hB_mod : B % c < c := Nat.mod_lt B (by omega)
      have hB_split : c * q1 + B % c = B := Nat.div_add_mod B c
      have hf2 : foldCrandall k c y1 = (B - 1 - B % c) + B * 1 := by
        unfold foldCrandall
        have heq : y1 = (B - 1) + B * q1 := by
          change q1 * B + (B - 1) = (B - 1) + B * q1
          rw [Nat.mul_comm, Nat.add_comm]
        have hlt1 : B - 1 < B := by omega
        rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt1,
            Nat.add_mul_div_left _ _ hB_pos, Nat.div_eq_of_lt hlt1, Nat.zero_add]
        omega
      -- Step 3: foldCrandall k c (hf2) = (B - 1 - B % c) + c ≥ B!
      have hf3 : B ≤ foldCrandall k c ((B - 1 - B % c) + B * 1) := by
        unfold foldCrandall
        have hlt2 : B - 1 - B % c < B := by omega
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt2,
            Nat.add_mul_div_left _ _ hB_pos, Nat.div_eq_of_lt hlt2, Nat.zero_add, Nat.mul_one]
        omega
      have hbad := hall nStar hnStar_lt
      rw [hf1, hf2] at hbad
      omega
  · -- Sufficiency: if c^2 ≤ B, every n < B^2 absorbs in ≤ 3 Crandall folds!
    intro hcc n hn
    rw [hsq] at hn
    have hq0_le : n / B ≤ B - 1 := by
      have hlt : n / B < B := by rw [Nat.div_lt_iff_lt_mul hB_pos]; exact hn
      omega
    have hr0_lt : n % B < B := Nat.mod_lt n hB_pos
    let y1 := foldCrandall k c n
    have hy1_le : y1 ≤ c * B + (B - c - 1) := by
      have hmul : c * (n / B) ≤ c * (B - 1) := Nat.mul_le_mul_left c hq0_le
      rw [Nat.mul_sub, Nat.mul_one] at hmul
      have hle : c ≤ c * B := Nat.le_mul_of_pos_right _ hB_pos
      change n % B + c * (n / B) ≤ c * B + (B - c - 1)
      omega
    have hq1_le : y1 / B ≤ c := by
      have hlt : y1 / B < c + 1 := by
        rw [Nat.div_lt_iff_lt_mul hB_pos, Nat.add_mul, Nat.one_mul]
        omega
      omega
    have hsplit1 := Nat.div_add_mod y1 B
    have hr1_lt : y1 % B < B := Nat.mod_lt y1 hB_pos
    let y2 := foldCrandall k c y1
    have hy2_le : y2 ≤ B + c * c - c - 1 := by
      have hcc_ge : c ≤ c * c := Nat.le_mul_of_pos_right _ (by omega)
      change y1 % B + c * (y1 / B) ≤ B + c * c - c - 1
      by_cases htop : y1 / B = c
      · rw [htop, Nat.mul_comm B c] at hsplit1
        rw [htop]
        omega
      · have hq1_lt : y1 / B ≤ c - 1 := by omega
        have hmul : c * (y1 / B) ≤ c * (c - 1) := Nat.mul_le_mul_left c hq1_lt
        rw [Nat.mul_sub, Nat.mul_one] at hmul
        omega
    have hy2_lt : y2 < 2 * B - c := by omega
    exact (crandall_1round_threshold k c (by omega) hB).1 y2 hy2_lt

/-- **Crypto Non-Vacuity Witness (Curve25519 `2^255 - 19`):**
    3 Crandall folds absorb EVERY 510-bit product `n < 2^510` into `[0, 2^255 - 1]`! -/
theorem curve25519_3round_absorb :
    ∀ n, n < 2 ^ (2 * 255) →
      foldCrandall 255 19 (foldCrandall 255 19 (foldCrandall 255 19 n)) < 2 ^ 255 := by
  have hB : 19 < 2 ^ 255 := by decide
  have hcc : 19 * 19 ≤ 2 ^ 255 := by decide
  exact (crandall_3round_iff_sq_le_base 255 19 (by decide) hB).2 hcc

/-- **Crandall Sharpness Witness (`c = 5, k = 4, 2^4 = 16 < 25 = 5^2`):**
    At `c = 5, k = 4`, `n = 251 < 2^8` overflows 3 Crandall folds (`F^3(251) = 20 ≥ 16`). -/
theorem crandall_3round_sharp_c5_k4 :
    251 < 2 ^ (2 * 4) ∧
    foldCrandall 4 5 (foldCrandall 4 5 (foldCrandall 4 5 251)) = 20 := by
  decide

-- ============================================================================
-- Section 8: Universal Minimum-Round Lower Bound & Exact (d+2)-Step
--            Depth-Optimality Dichotomy for 2^d-Limb Bit-Folding Circuits
-- ============================================================================

/-- Universal maximum input capacity `capBound B t` absorbable by ANY `t`-step
    multi-level Mersenne folding schedule (arbitrary strides `m_1, ..., m_t ≥ 1`). -/
def capBound (B : Nat) : Nat → Nat
  | 0 => B - 1
  | 1 => 2 * B - 2
  | t + 2 => (capBound B (t + 1) + 3) * (capBound B (t + 1) + 3) / 4 - 1

/-- Pure-integer AM-GM inequality: `4 * a * b ≤ (a + b) * (a + b)`. -/
theorem four_mul_le_sq_add (a b : Nat) : 4 * (a * b) ≤ (a + b) * (a + b) := by
  have haux (x d : Nat) : 4 * (x * (x + d)) ≤ (x + (x + d)) * (x + (x + d)) := by
    have hlhs : 4 * (x * (x + d)) = 4 * (x * x) + 4 * (x * d) := by
      rw [Nat.mul_add, Nat.mul_add]
    have hrhs : (x + (x + d)) * (x + (x + d)) = 4 * (x * x) + 4 * (x * d) + d * d := by
      have h2 : x + (x + d) = 2 * x + d := by omega
      rw [h2, Nat.add_mul, Nat.mul_add, Nat.mul_add]
      have h4 : (2 * x) * (2 * x) = 4 * (x * x) := by
        rw [Nat.mul_assoc, Nat.mul_left_comm x 2 x, ← Nat.mul_assoc]
      have h2d : (2 * x) * d = 2 * (x * d) := by rw [Nat.mul_assoc]
      have hd2 : d * (2 * x) = 2 * (x * d) := by rw [Nat.mul_comm d (2 * x), Nat.mul_assoc]
      rw [h4, h2d, hd2]
      omega
    omega
  by_cases h : a ≤ b
  · have hdiff : b = a + (b - a) := by omega
    rw [hdiff]; exact haux a (b - a)
  · have hdiff : a = b + (a - b) := by omega
    rw [hdiff, Nat.mul_comm (b + (a - b)) b, Nat.add_comm (b + (a - b)) b]
    exact haux b (a - b)

/-- Contiguous-image surjectivity of a single Mersenne fold `x ↦ x % W + x / W`:
    on `[0, U]` with `W ≤ U` and `q = U / W ≥ 1`, every `y ≤ W + q - 2` is attained by some `x ≤ U`! -/
theorem fold_surjective_on_prefix {W U y : Nat} (hW : 1 ≤ W) (hWU : W ≤ U)
    (hy : y ≤ W + U / W - 2) :
    ∃ x, x ≤ U ∧ x % W + x / W = y := by
  have hq : 1 ≤ U / W := by
    rw [Nat.le_div_iff_mul_le hW]; omega
  by_cases hlt : y < W
  · refine ⟨y, by omega, ?_⟩
    rw [Nat.mod_eq_of_lt hlt, Nat.div_eq_of_lt hlt, Nat.add_zero]
  · let j := y - (W - 1)
    have hj_pos : 1 ≤ j := by omega
    have hj_lt : j < U / W := by omega
    let x := (W - 1) + W * j
    have hx_le : x ≤ U := by
      have hmul : W * (j + 1) ≤ W * (U / W) := Nat.mul_le_mul_left W (by omega)
      have hsplit := Nat.div_add_mod U W
      rw [Nat.mul_add, Nat.mul_one] at hmul
      omega
    refine ⟨x, hx_le, ?_⟩
    have hW1 : W - 1 < W := by omega
    change ((W - 1) + W * j) % W + ((W - 1) + W * j) / W = y
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hW1,
        Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt hW1, Nat.zero_add]
    omega

/-- **Theorem 8A (Universal Schedule Capacity Bound):**
    For ALL `k ≥ 1`, ALL positive Mersenne schedules `strides` of length `t`, and ALL `U`:
    if `evalNatMersenne k strides n < 2^k` for every `n ≤ U`, then `U ≤ capBound (2^k) t`! -/
theorem mersenne_schedule_capacity_bound {k : Nat} (hk : 1 ≤ k) :
    ∀ (strides : List Nat),
      strides.all (fun m => decide (1 ≤ m)) = true →
      ∀ (U : Nat), (∀ n, n ≤ U → evalNatMersenne k strides n < 2 ^ k) →
      U ≤ capBound (2 ^ k) strides.length
  | [], _, U, hall => by
    have hU := hall U (Nat.le_refl U)
    simp only [evalNatMersenne, List.length_nil, capBound] at *
    omega
  | [m], hpos, U, hall => by
    simp only [List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq] at hpos
    simp only [List.length_singleton, capBound]
    have h2 := nat_two_pow_ge_two hk
    by_cases hm1 : m = 1
    · subst hm1
      exact Decidable.byContradiction fun hgt => by
        have hbad := hall (2 * 2 ^ k - 1) (by omega)
        simp only [evalNatMersenne, Nat.one_mul] at hbad
        have heq : 2 * 2 ^ k - 1 = (2 ^ k - 1) + 2 ^ k * 1 := by omega
        have hlt : 2 ^ k - 1 < 2 ^ k := by omega
        rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt,
            Nat.add_mul_div_left _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hlt] at hbad
        omega
    · have hm2 : 2 ≤ m := by omega
      have hmk : 2 * k ≤ m * k := Nat.mul_le_mul_right k hm2
      have hpow_le : 2 ^ (2 * k) ≤ 2 ^ (m * k) := Nat.pow_le_pow_right (by decide) hmk
      have hlt_mk : 2 ^ k < 2 ^ (m * k) := by
        have hsq : 2 ^ (2 * k) = 2 ^ k * 2 ^ k := by rw [Nat.two_mul, Nat.pow_add]
        have hmul : 2 ^ k * 2 ≤ 2 ^ k * 2 ^ k := Nat.mul_le_mul_left _ h2
        omega
      exact Decidable.byContradiction fun hgt => by
        have hbad := hall (2 ^ k) (by omega)
        simp only [evalNatMersenne] at hbad
        rw [Nat.mod_eq_of_lt hlt_mk, Nat.div_eq_of_lt hlt_mk] at hbad
        omega
  | m :: m2 :: rest, hpos, U, hall => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hpos
    let W := 2 ^ (m * k)
    have hW_pos : 1 ≤ W := Nat.two_pow_pos (m * k)
    have hrest_pos : (m2 :: rest).all (fun s => decide (1 ≤ s)) = true := by
      simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq]
      exact hpos.2
    have hih := mersenne_schedule_capacity_bound hk (m2 :: rest) hrest_pos
    let C := capBound (2 ^ k) (m2 :: rest).length
    have hcap_eq : capBound (2 ^ k) (m :: m2 :: rest).length = (C + 3) * (C + 3) / 4 - 1 := by
      simp only [List.length_cons, capBound, C]
    rw [hcap_eq]
    by_cases hUW : U < W
    · have hsub : ∀ y, y ≤ U → evalNatMersenne k (m2 :: rest) y < 2 ^ k := by
        intro y hy
        have h := hall y hy
        simp only [evalNatMersenne] at h
        have hyW : y < W := by omega
        rw [Nat.mod_eq_of_lt hyW, Nat.div_eq_of_lt hyW, Nat.add_zero] at h
        exact h
      have hUC : U ≤ C := hih U hsub
      have h4 : 4 * (U + 1) ≤ (C + 3) * (C + 3) := by
        have hmul : (U + 3) * (U + 3) ≤ (C + 3) * (C + 3) :=
          Nat.mul_le_mul (by omega) (by omega)
        have hquad : 4 * (U + 1) ≤ (U + 3) * (U + 3) := by
          rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
          omega
        exact Nat.le_trans hquad hmul
      have hdiv : U + 1 ≤ (C + 3) * (C + 3) / 4 := by
        rw [Nat.le_div_iff_mul_le (by decide : 0 < 4)]
        omega
      omega
    · have hWU : W ≤ U := by omega
      let q := U / W
      have hq : 1 ≤ q := by rw [Nat.le_div_iff_mul_le hW_pos]; omega
      have hsub : ∀ y, y ≤ W + q - 2 → evalNatMersenne k (m2 :: rest) y < 2 ^ k := by
        intro y hy
        rcases fold_surjective_on_prefix hW_pos hWU hy with ⟨x, hxU, hfx⟩
        have h := hall x hxU
        simp only [evalNatMersenne] at h
        rw [hfx] at h
        exact h
      have hWqC : W + q - 2 ≤ C := hih (W + q - 2) hsub
      have hsplit : W * q + U % W = U := Nat.div_add_mod U W
      have hrem := Nat.mod_lt U hW_pos
      have hU_le : U + 1 ≤ W * (q + 1) := by
        rw [Nat.mul_add, Nat.mul_one]; omega
      have h4 : 4 * (U + 1) ≤ (C + 3) * (C + 3) := by
        calc 4 * (U + 1) ≤ 4 * (W * (q + 1)) := Nat.mul_le_mul_left 4 hU_le
          _ ≤ (W + (q + 1)) * (W + (q + 1)) := four_mul_le_sq_add W (q + 1)
          _ ≤ (C + 3) * (C + 3) := Nat.mul_le_mul (by omega) (by omega)
      have hdiv : U + 1 ≤ (C + 3) * (C + 3) / 4 := by
        rw [Nat.le_div_iff_mul_le (by decide : 0 < 4)]
        omega
      omega

/-- Exact growth invariant: `capBound B (d + 1) + 3 ≤ B ^ (2 ^ d)` for ALL `d ≥ 2`, `B ≥ 4`. -/
theorem capBound_le_pow {B d : Nat} (hB : 4 ≤ B) (hd : 2 ≤ d) :
    capBound B (d + 1) + 3 ≤ B ^ (2 ^ d) := by
  induction d with
  | zero => omega
  | succ d ih =>
    cases d with
    | zero => omega
    | succ d' =>
      cases d' with
      | zero =>
        -- Base case d = 2: capBound B 3 + 3 ≤ B^4 for all B ≥ 4!
        simp only [capBound]
        have hC2_le : capBound B 2 ≤ B * B + B := by
          simp only [capBound]
          have h1 : 2 * B - 2 + 3 = 2 * B + 1 := by omega
          rw [h1]
          have hsq : (2 * B + 1) * (2 * B + 1) = 4 * (B * B + B) + 1 := by
            rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.one_mul]
            have : (2 * B) * (2 * B) = 4 * (B * B) := by
              rw [Nat.mul_assoc, Nat.mul_left_comm B 2 B, ← Nat.mul_assoc]
            omega
          have hdiv : (4 * (B * B + B) + 1) / 4 = B * B + B := by
            rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by decide : 0 < 4)]
            omega
          rw [hsq, hdiv]; omega
        -- For B ≥ 4: (B^2 + B + 3) ≤ 2 * (B^2 - 1), so (C2 + 3)^2 / 4 + 2 ≤ (B^2 - 1)^2 + 2 ≤ B^4!
        have hBB : 4 * B ≤ B * B := Nat.mul_le_mul_right B hB
        have hlin : (2 * B - 2 + 3) * (2 * B - 2 + 3) / 4 - 1 + 3 ≤ 2 * (B * B - 1) := by
          have : (2 * B - 2 + 3) * (2 * B - 2 + 3) / 4 - 1 = capBound B 2 := rfl
          rw [this]; omega
        have hsq_le : ((2 * B - 2 + 3) * (2 * B - 2 + 3) / 4 - 1 + 3) *
            ((2 * B - 2 + 3) * (2 * B - 2 + 3) / 4 - 1 + 3) ≤
            4 * ((B * B - 1) * (B * B - 1)) := by
          have hm := Nat.mul_le_mul hlin hlin
          have h4 : (2 * (B * B - 1)) * (2 * (B * B - 1)) = 4 * ((B * B - 1) * (B * B - 1)) := by
            rw [Nat.mul_assoc, Nat.mul_left_comm (B * B - 1) 2 (B * B - 1), ← Nat.mul_assoc]
          rwa [h4] at hm
        have hdiv_le : ((2 * B - 2 + 3) * (2 * B - 2 + 3) / 4 - 1 + 3) *
            ((2 * B - 2 + 3) * (2 * B - 2 + 3) / 4 - 1 + 3) / 4 ≤
            (B * B - 1) * (B * B - 1) := by
          rw [Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 4)]
          omega
        have hB4 : B ^ (2 ^ 2) = (B * B) * (B * B) := by
          have : 2 ^ 2 = 4 := by decide
          rw [this, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
          rw [Nat.mul_assoc]
        have hexpand : (B * B - 1) * (B * B - 1) + 2 ≤ (B * B) * (B * B) := by
          rw [Nat.sub_mul, Nat.mul_sub, Nat.one_mul, Nat.mul_one]
          have h1 : B * B ≤ (B * B) * (B * B) := Nat.le_mul_of_pos_left _ (by omega)
          have h2 : 2 * (B * B) ≤ (B * B) * (B * B) := Nat.mul_le_mul_right _ (by omega)
          omega
        have hf1 : 1 ≤ ((2 * B - 2 + 3) * (2 * B - 2 + 3) / 4 - 1 + 3) *
            ((2 * B - 2 + 3) * (2 * B - 2 + 3) / 4 - 1 + 3) / 4 := by
          rw [Nat.le_div_iff_mul_le (by decide : 0 < 4)]
          have h3 : 3 ≤ (2 * B - 2 + 3) * (2 * B - 2 + 3) / 4 - 1 + 3 := by omega
          have := Nat.mul_le_mul h3 h3
          omega
        rw [hB4]
        omega
      | succ d'' =>
        -- Inductive step: let m = d'' + 2 ≥ 2, assume capBound B (m + 1) + 3 ≤ B^(2^m)
        have hprev := ih (by omega)
        let m := d'' + 2
        change capBound B (m + 2) + 3 ≤ B ^ (2 ^ (m + 1))
        simp only [capBound]
        have hsq_le : (capBound B (m + 1) + 3) * (capBound B (m + 1) + 3) ≤
            B ^ (2 ^ m) * B ^ (2 ^ m) := Nat.mul_le_mul hprev hprev
        have hpow_sq : B ^ (2 ^ (m + 1)) = B ^ (2 ^ m) * B ^ (2 ^ m) := by
          rw [Nat.pow_succ, Nat.mul_two, Nat.pow_add]
        have hbig : 16 ≤ B ^ (2 ^ m) * B ^ (2 ^ m) := by
          have hm1 : 1 ≤ 2 ^ m := Nat.two_pow_pos m
          have hB1 : 4 ≤ B ^ (2 ^ m) := by
            have := Nat.pow_le_pow_right (by decide : 0 < 4) hm1
            have := Nat.pow_le_pow_left hB (2 ^ m)
            omega
          exact Nat.le_trans (by decide : 16 ≤ 4 * 4) (Nat.mul_le_mul hB1 hB1)
        have hdiv_le : (capBound B (m + 1) + 3) * (capBound B (m + 1) + 3) / 4 ≤
            B ^ (2 ^ m) * B ^ (2 ^ m) / 4 := Nat.div_le_div_right hsq_le
        rw [hpow_sq]
        omega

theorem capBound_mono {B : Nat} (hB : 2 ≤ B) {t1 t2 : Nat} (h : t1 ≤ t2) :
    capBound B t1 ≤ capBound B t2 := by
  induction h with
  | refl => exact Nat.le_refl _
  | @step m _ ih =>
    apply Nat.le_trans ih
    cases m with
    | zero => simp only [capBound]; omega
    | succ m' =>
      simp only [capBound]
      let C := capBound B (m' + 1)
      have h4 : 4 * (C + 1) ≤ (C + 3) * (C + 3) := by
        rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
      have hdiv : C + 1 ≤ (C + 3) * (C + 3) / 4 := by
        rw [Nat.le_div_iff_mul_le (by decide : 0 < 4)]; omega
      change C ≤ (C + 3) * (C + 3) / 4 - 1
      omega

/-- **Theorem 8B (Universal Information-Theoretic Minimum-Round Lower Bound):**
    For ALL `d ≥ 2`, ALL `k ≥ 2`, and ALL multi-level Mersenne folding schedules `strides`
    of length `≤ d + 1` (with ANY arbitrary strides `m_i ≥ 1`), there EXISTS an input
    `n < 2^(2^d * k)` that fails to absorb (`evalNatMersenne k strides n ≥ 2^k`)! -/
theorem mersenne_min_rounds_lower_bound (d k : Nat) (hd : 2 ≤ d) (hk : 2 ≤ k)
    (strides : List Nat) (hpos : strides.all (fun m => decide (1 ≤ m)) = true)
    (hlen : strides.length ≤ d + 1) :
    ∃ n, n < 2 ^ (2 ^ d * k) ∧ 2 ^ k ≤ evalNatMersenne k strides n := by
  have hB4 : 4 ≤ 2 ^ k := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hk
    simpa using this
  have hcap := capBound_le_pow hB4 hd
  have hmono := capBound_mono (B := 2 ^ k) (by omega) hlen
  have hpow_eq : (2 ^ k) ^ (2 ^ d) = 2 ^ (2 ^ d * k) := by
    rw [← Nat.pow_mul, Nat.mul_comm]
  rw [hpow_eq] at hcap
  -- By contradiction: if every n ≤ 2^(2^d * k) - 1 absorbed, then 2^(2^d * k) - 1 ≤ capBound!
  exact Decidable.byContradiction fun hno => by
    have hall : ∀ n, n ≤ 2 ^ (2 ^ d * k) - 1 → evalNatMersenne k strides n < 2 ^ k := by
      intro n hn
      exact Decidable.byContradiction fun hge =>
        hno ⟨n, by have := Nat.two_pow_pos (2 ^ d * k); omega, by omega⟩
    have hbd := mersenne_schedule_capacity_bound (by omega) strides hpos (2 ^ (2 ^ d * k) - 1) hall
    omega

-- ----------------------------------------------------------------------------
-- Matching Parametric (d + 2)-Step Dyadic Upper Bound (Exact Depth Optimality!)
-- ----------------------------------------------------------------------------

/-- Single-pass dyadic halving schedule `[2^(d-1), 2^(d-2), ..., 2, 1]` of length `d`. -/
def dyadicHalve : Nat → List Nat
  | 0 => []
  | d + 1 => 2 ^ d :: dyadicHalve d

/-- Exact depth-optimal `(d + 2)`-step dyadic Mersenne schedule. -/
def dyadicOptimalSchedule (d : Nat) : List Nat := dyadicHalve d ++ [1, 1]

theorem dyadicHalve_len (d : Nat) : (dyadicHalve d).length = d := by
  induction d with
  | zero => rfl
  | succ d ih => simp [dyadicHalve, ih]

theorem dyadicOptimalSchedule_len (d : Nat) : (dyadicOptimalSchedule d).length = d + 2 := by
  simp [dyadicOptimalSchedule, dyadicHalve_len]

theorem dyadicOptimalSchedule_pos (d : Nat) :
    (dyadicOptimalSchedule d).all (fun m => decide (1 ≤ m)) = true := by
  unfold dyadicOptimalSchedule
  rw [List.all_append]
  suffices h : (dyadicHalve d).all (fun m => decide (1 ≤ m)) = true by
    simp [h]
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [dyadicHalve, List.all_cons, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨Nat.two_pow_pos d, ih⟩

theorem evalNatMersenne_append (k : Nat) (s1 s2 : List Nat) (n : Nat) :
    evalNatMersenne k (s1 ++ s2) n = evalNatMersenne k s2 (evalNatMersenne k s1 n) := by
  induction s1 generalizing n with
  | nil => rfl
  | cons m ms ih =>
    simp only [List.cons_append, evalNatMersenne]
    exact ih _

/-- Single-pass dyadic halving invariant: for ALL `d ≥ 1`, `c ≥ 1`, `k ≥ 1`,
    if `n ≤ c * (2^k)^(2^d) - 1`, then `evalNatMersenne k (dyadicHalve d) n ≤ (c + d) * 2^k - 2`! -/
theorem dyadicHalve_bound (k : Nat) (hk : 1 ≤ k) :
    ∀ (d c n : Nat), 1 ≤ d → 1 ≤ c → n ≤ c * 2 ^ (2 ^ d * k) - 1 →
      evalNatMersenne k (dyadicHalve d) n ≤ (c + d) * 2 ^ k - 2
  | 0, _, _, hd, _, _ => by omega
  | 1, c, n, _, hc, hn => by
    simp only [dyadicHalve, evalNatMersenne, Nat.pow_zero, Nat.one_mul] at *
    have h2 := nat_two_pow_ge_two hk
    have hsq : 2 ^ (2 * k) = 2 ^ k * 2 ^ k := by rw [Nat.two_mul, Nat.pow_add]
    have hpow : 2 ^ (2 ^ 1 * k) = 2 ^ k * 2 ^ k := by simpa using hsq
    rw [hpow] at hn
    have hq_le : n / 2 ^ k ≤ c * 2 ^ k - 1 := by
      have hlt : n / 2 ^ k < c * 2 ^ k := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k), Nat.mul_assoc]
        have hpos : 1 ≤ c * (2 ^ k * 2 ^ k) :=
          Nat.mul_pos hc (Nat.mul_pos (Nat.two_pow_pos k) (Nat.two_pow_pos k))
        omega
      omega
    have hr_lt : n % 2 ^ k < 2 ^ k := Nat.mod_lt n (Nat.two_pow_pos k)
    have hadd : (c + 1) * 2 ^ k = c * 2 ^ k + 2 ^ k := by rw [Nat.add_mul, Nat.one_mul]
    have hcB : 1 ≤ c * 2 ^ k := Nat.mul_pos hc (Nat.two_pow_pos k)
    omega
  | d + 2, c, n, _, hc, hn => by
    simp only [dyadicHalve, evalNatMersenne]
    let W := 2 ^ (2 ^ (d + 1) * k)
    have hW_pos : 0 < W := Nat.two_pow_pos _
    have hW_sq : 2 ^ (2 ^ (d + 2) * k) = W * W := by
      have hexp : 2 ^ (d + 2) * k = 2 ^ (d + 1) * k + 2 ^ (d + 1) * k := by
        rw [Nat.pow_succ, Nat.mul_two, Nat.add_mul]
      rw [hexp, Nat.pow_add]
    rw [hW_sq] at hn
    have hq_le : n / W ≤ c * W - 1 := by
      have hlt : n / W < c * W := by
        rw [Nat.div_lt_iff_lt_mul hW_pos, Nat.mul_assoc]
        have hpos : 1 ≤ c * (W * W) := Nat.mul_pos hc (Nat.mul_pos hW_pos hW_pos)
        omega
      omega
    have hr_lt : n % W < W := Nat.mod_lt n hW_pos
    have hnext : n % W + n / W ≤ (c + 1) * W - 1 := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    have hrec := dyadicHalve_bound k hk (d + 1) (c + 1) (n % W + n / W) (by omega) (by omega) hnext
    have heq : (c + 1) + (d + 1) = c + (d + 2) := by omega
    rwa [heq] at hrec

/-- **Theorem 8C (Exact Matching `(d + 2)`-Step Parametric Dyadic Upper Bound):**
    For ALL `d ≥ 1`, ALL `k ≥ 1` with `d ≤ 2^k`, and ALL `n < 2^(2^d * k)`,
    the explicit `(d + 2)`-step schedule `dyadicOptimalSchedule d` absorbs ALL carries
    into `[0, 2^k - 1]` and equals `canonM k n`! -/
theorem dyadic_mersenne_d_plus_2_upper (d k n : Nat) (hd : 1 ≤ d) (hk : 1 ≤ k)
    (hdB : d ≤ 2 ^ k) (hn : n < 2 ^ (2 ^ d * k)) :
    evalNatMersenne k (dyadicOptimalSchedule d) n < 2 ^ k ∧
    evalNatMersenne k (dyadicOptimalSchedule d) n = canonM k n := by
  have h2 := nat_two_pow_ge_two hk
  have hpos_p : 1 ≤ 2 ^ (2 ^ d * k) := Nat.two_pow_pos _
  have hmid : evalNatMersenne k (dyadicHalve d) n ≤ (1 + d) * 2 ^ k - 2 :=
    dyadicHalve_bound k hk d 1 n hd (by decide) (by rw [Nat.one_mul]; omega)
  let y := evalNatMersenne k (dyadicHalve d) n
  have hy_le : y ≤ (1 + d) * 2 ^ k - 2 := hmid
  have h1dB : 2 ≤ (1 + d) * 2 ^ k := by
    have := Nat.mul_le_mul_right (2 ^ k) (show 1 ≤ 1 + d by omega)
    omega
  have hfold1 : foldM k y < 2 ^ (1 * k) + 2 ^ k - 1 := by
    have hsplit := Nat.div_add_mod y (2 ^ k)
    have hrem := Nat.mod_lt y (Nat.two_pow_pos k)
    have hq_le : y / 2 ^ k ≤ d := by
      have hlt : y / 2 ^ k < d + 1 := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)]
        have : (d + 1) * 2 ^ k = (1 + d) * 2 ^ k := by rw [Nat.add_comm]
        omega
      omega
    unfold foldM
    simp only [Nat.one_mul]
    by_cases htop : y / 2 ^ k = d
    · rw [htop, Nat.mul_comm (2 ^ k) d] at hsplit
      have : (1 + d) * 2 ^ k = d * 2 ^ k + 2 ^ k := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
      omega
    · omega
  have hfold2 : foldM k (foldM k y) < 2 ^ k := by
    have h := (mersenne_exact_threshold k 1 (foldM k y) hk (by decide) hfold1).1
    simpa [iterFoldM] using h
  have heval_eq : evalNatMersenne k (dyadicOptimalSchedule d) n = foldM k (foldM k y) := by
    unfold dyadicOptimalSchedule
    rw [evalNatMersenne_append]
    simp [evalNatMersenne, foldM, y]
  rw [heval_eq]
  refine ⟨hfold2, ?_⟩
  rw [← heval_eq]
  exact (total_carry_conservation hk (dyadicOptimalSchedule_pos d) (by rwa [heval_eq])).1

/-- **Theorem 8D (Exact Depth-Optimality Dichotomy for `2^d`-Limb Mersenne Reduction):**
    For ALL `d ≥ 2` and ALL `k ≥ 2` with `d ≤ 2^k`, the EXACT minimum depth of ANY
    multi-level Mersenne folding circuit absorbing `[0, 2^(2^d * k) - 1]` into `[0, 2^k - 1]`
    is `d + 2`:
    - Achievable in `d + 2` folds (`dyadicOptimalSchedule d`),
    - Impossible in `≤ d + 1` folds for ANY choice of strides! -/
theorem mersenne_exact_min_depth_dichotomy (d k : Nat) (hd : 2 ≤ d) (hk : 2 ≤ k) (hdB : d ≤ 2 ^ k) :
    (∃ sched, sched.length = d + 2 ∧ sched.all (fun m => decide (1 ≤ m)) = true ∧
      ∀ n, n < 2 ^ (2 ^ d * k) → evalNatMersenne k sched n < 2 ^ k) ∧
    (∀ sched, sched.all (fun m => decide (1 ≤ m)) = true → sched.length ≤ d + 1 →
      ∃ n, n < 2 ^ (2 ^ d * k) ∧ 2 ^ k ≤ evalNatMersenne k sched n) :=
  ⟨⟨dyadicOptimalSchedule d, dyadicOptimalSchedule_len d, dyadicOptimalSchedule_pos d,
    fun n hn => (dyadic_mersenne_d_plus_2_upper d k n (by omega) (by omega) hdB hn).1⟩,
   fun sched hpos hlen => mersenne_min_rounds_lower_bound d k hd hk sched hpos hlen⟩

/-- Compiled Infinite Theorem 8E: Depth-optimal 6-step 16-limb Mersenne circuit
    `[M(8), M(4), M(2), M(1), M(1), M(1)]` certified in 1 line via `by decide` for ALL `k ≥ 2`! -/
theorem compiled_mersenne_6step_16limb_k_ge_2 :
    ∀ (k : Nat), 2 ≤ k → ∀ (x : Int), 0 ≤ x → x ≤ (2 : Int) ^ (16 * k) - 1 →
      let y := evalProg k [⟨8, .pos⟩, ⟨4, .pos⟩, ⟨2, .pos⟩, ⟨1, .pos⟩, ⟨1, .pos⟩, ⟨1, .pos⟩] x
      y % ((2 : Int) ^ k - 1) = x % ((2 : Int) ^ k - 1) ∧ 0 ≤ y ∧ y ≤ (2 : Int) ^ k - 1 := by
  intro k hk x hx0 hxU
  have hchk : checkCircuit .pos 4
      [⟨8, .pos⟩, ⟨4, .pos⟩, ⟨2, .pos⟩, ⟨1, .pos⟩, ⟨1, .pos⟩, ⟨1, .pos⟩]
      ([], [-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) ([], [-1, 1]) = true := by
    decide
  have hB4 : (4 : Int) ≤ (2 : Int) ^ k := by
    cases k with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ m' =>
        have hpos := two_pow_pos m'
        rw [Int.pow_succ, Int.pow_succ]
        omega
  have hU' : x ≤ evalPoly ((2 : Int) ^ k) [-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] := by
    have hpoly : evalPoly ((2 : Int) ^ k) [-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] =
        ((2 : Int) ^ k) ^ 16 - 1 := by
      have h1 : evalPoly ((2 : Int) ^ k) (polySub (polyMonomial 16 1) [1]) =
          ((2 : Int) ^ k) ^ 16 - 1 := by
        rw [evalPoly_sub, evalPoly_monomial, evalPoly, evalPoly, Int.one_mul]; omega
      exact h1
    rw [hpoly, ← Int.pow_mul, Nat.mul_comm]
    exact hxU
  have hres := circuit_sound_of_check .pos 4
    [⟨8, .pos⟩, ⟨4, .pos⟩, ⟨2, .pos⟩, ⟨1, .pos⟩, ⟨1, .pos⟩, ⟨1, .pos⟩]
    ([], [-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) ([], [-1, 1])
    hchk (by omega) hB4 (by change 0 ≤ x; exact hx0) hU'
  simp [evalPoly, modulus] at hres
  exact ⟨hres.1, by omega, by omega⟩

end BitFoldEngine
