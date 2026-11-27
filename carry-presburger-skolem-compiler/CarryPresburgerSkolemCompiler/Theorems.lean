/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CarryPresburgerSkolemCompiler.Defs

/-!
# Theorems (`CarryPresburgerSkolemCompiler`)

Exact Carry-Presburger Residue-Transition Elimination Engine (CPRTE)
  Standalone Lean 4.36.0 (Zero Mathlib, Zero Sorry, Standard Axioms Only)

  A kernel-verified pure-silicon reflection compiler for quantified Nat formulas
  mixing:
    1. Linear inequalities & equalities (`linLe`, `linEq`)
    2. Arbitrary-modulus congruences (`modEq`, any modulus m ≥ 1)
    3. 4-way pointwise bitwise relations on affine terms (`bitRel4`: &, |, ^,
       zero-carry disjointness, Lucas dominance, carry-word masks, MAJ/MUX)
    4. Exact binary carry-count inequalities (`carryLe`: κ(t1, t2, cin) ≤ k,
       proved equivalent to Kummer's popcount defect s₂(a)+s₂(b)+cin-s₂(a+b+cin))
    5. Modular linear combinations of binary popcounts (`popMod`: Thue-Morse
       parity & carry-count parity mod m)
    6. Full propositional connectives (`not`, `and`, `or`, `imp`, `iff`)
    7. Both universal (∀ x) and alternating (∀ x, ∃ y) formulas via finite
       residue-carry witness tables checked by `decide`, yielding an executable
       kernel-verified constructive Skolem transducer `synthesizeY`.
-/


namespace CPRTE

private theorem strongNatInd {P : Nat → Prop} (step : ∀ n, (∀ m, m < n → P m) → P n) :
    ∀ n, P n :=
  fun n => Nat.strongRecOn n step

private theorem popcountFuel_eq (k1 k2 n : Nat) (h1 : n ≤ k1) (h2 : n ≤ k2) :
    popcountFuel k1 n = popcountFuel k2 n := by
  induction k1 generalizing k2 n with
  | zero =>
    have hn : n = 0 := by omega
    subst hn
    cases k2 <;> simp [popcountFuel]
  | succ k1 ih =>
    cases k2 with
    | zero =>
      have hn : n = 0 := by omega
      subst hn; simp [popcountFuel]
    | succ k2 =>
      simp only [popcountFuel]
      by_cases hn : n = 0
      · subst hn; simp
      · have hnb : (n == 0) = false := by simp [hn]
        simp only [hnb, Bool.false_eq_true, ↓reduceIte]
        rw [ih k2 (n / 2) (by omega) (by omega)]

theorem popcount_zero : popcount 0 = 0 := rfl

theorem popcount_step (n : Nat) (b : Bool) :
    popcount (2 * n + b.toNat) = popcount n + b.toNat := by
  cases b
  · simp only [Bool.toNat_false, Nat.add_zero]
    by_cases hn : n = 0
    · subst hn; rfl
    · unfold popcount
      have h1 : popcountFuel (2 * n) (2 * n) = popcountFuel (2 * n + 1) (2 * n) :=
        popcountFuel_eq _ _ _ (by omega) (by omega)
      rw [h1]
      simp only [popcountFuel]
      have hnb : (2 * n == 0) = false := by simp; omega
      simp only [hnb, Bool.false_eq_true, ↓reduceIte]
      have hmod : (2 * n) % 2 = 0 := by omega
      have hdiv : (2 * n) / 2 = n := by omega
      rw [hmod, hdiv, Nat.zero_add, popcountFuel_eq (2 * n) n n (by omega) (by omega)]
  · simp only [Bool.toNat_true]
    unfold popcount
    simp only [popcountFuel]
    have hnb : (2 * n + 1 == 0) = false := by simp
    simp only [hnb, Bool.false_eq_true, ↓reduceIte]
    have hmod : (2 * n + 1) % 2 = 1 := by omega
    have hdiv : (2 * n + 1) / 2 = n := by omega
    rw [hmod, hdiv, popcountFuel_eq (2 * n) n n (by omega) (by omega), Nat.add_comm]

private theorem carryCountFuel_eq (k1 k2 a b : Nat) (cin : Bool)
    (h1 : a + b ≤ k1) (h2 : a + b ≤ k2) :
    carryCountFuel k1 a b cin = carryCountFuel k2 a b cin := by
  induction k1 generalizing k2 a b cin with
  | zero =>
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha; subst hb
    cases k2 <;> simp [carryCountFuel]
  | succ k1 ih =>
    cases k2 with
    | zero =>
      have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst ha; subst hb; simp [carryCountFuel]
    | succ k2 =>
      simp only [carryCountFuel]
      by_cases h0 : a = 0 ∧ b = 0
      · rcases h0 with ⟨rfl, rfl⟩; simp
      · have hnb : (a == 0 && b == 0) = false := by
          cases ha : (a == 0) <;> cases hb : (b == 0) <;> simp_all
        simp only [hnb, Bool.false_eq_true, ↓reduceIte]
        rw [ih k2 (a / 2) (b / 2) _ (by omega) (by omega)]

theorem carryCount_zero_zero (cin : Bool) : carryCount 0 0 cin = 0 := rfl

theorem carryCount_step (a b : Nat) (ba bb cin : Bool) :
    carryCount (2 * a + ba.toNat) (2 * b + bb.toNat) cin =
      (decide (ba.toNat + bb.toNat + cin.toNat ≥ 2)).toNat +
        carryCount a b (decide (ba.toNat + bb.toNat + cin.toNat ≥ 2)) := by
  by_cases h0 : 2 * a + ba.toNat = 0 ∧ 2 * b + bb.toNat = 0
  · have ha : a = 0 := by cases ba <;> simp at h0 <;> omega
    have hb : b = 0 := by cases bb <;> simp at h0 <;> omega
    have hba : ba = false := by cases ba <;> simp at h0 ⊢
    have hbb : bb = false := by cases bb <;> simp at h0 ⊢
    subst ha; subst hb; subst hba; subst hbb
    cases cin <;> rfl
  · unfold carryCount
    rw [carryCountFuel_eq _ (2 * a + ba.toNat + (2 * b + bb.toNat) + 1) _ _ _ (by omega) (by omega)]
    simp only [carryCountFuel]
    have hnb : ((2 * a + ba.toNat == 0) && (2 * b + bb.toNat == 0)) = false := by
      cases h1 : (2 * a + ba.toNat == 0) <;> cases h2 : (2 * b + bb.toNat == 0) <;> simp_all
    simp only [hnb, Bool.false_eq_true, ↓reduceIte]
    have hma : (2 * a + ba.toNat) % 2 = ba.toNat := by cases ba <;> simp <;> omega
    have hmb : (2 * b + bb.toNat) % 2 = bb.toNat := by cases bb <;> simp <;> omega
    have hda : (2 * a + ba.toNat) / 2 = a := by cases ba <;> simp <;> omega
    have hdb : (2 * b + bb.toNat) / 2 = b := by cases bb <;> simp <;> omega
    simp only [hma, hmb, hda, hdb]
    rw [carryCountFuel_eq _ (a + b) a b _ (by omega) (by omega)]

/-- Kummer's Popcount-Defect Identity: exact binary carry count equals
    `popcount a + popcount b + cin - popcount (a + b + cin)`. -/
theorem carryCount_eq_popcount_defect (a b : Nat) (cin : Bool) :
    carryCount a b cin + popcount (a + b + cin.toNat) =
      popcount a + popcount b + cin.toNat := by
  suffices h : ∀ m a b cin, a + b = m →
      carryCount a b cin + popcount (a + b + cin.toNat) =
        popcount a + popcount b + cin.toNat from h (a + b) a b cin rfl
  intro m
  refine strongNatInd (P := fun m => ∀ a b cin, a + b = m →
      carryCount a b cin + popcount (a + b + cin.toNat) =
        popcount a + popcount b + cin.toNat) ?_ m
  intro m ih a b cin hm
  by_cases h0 : a = 0 ∧ b = 0
  · rcases h0 with ⟨rfl, rfl⟩
    cases cin
    · simp [carryCount_zero_zero, popcount_zero]
    · have hp1 : popcount 1 = 1 := by simpa [popcount_zero] using popcount_step 0 true
      simp [carryCount_zero_zero, popcount_zero, hp1]
  · let ba := decide (a % 2 = 1)
    let bb := decide (b % 2 = 1)
    have ha_eq : a = 2 * (a / 2) + ba.toNat := by
      show a = 2 * (a / 2) + (decide (a % 2 = 1)).toNat
      by_cases h1 : a % 2 = 1 <;> simp [h1] <;> omega
    have hb_eq : b = 2 * (b / 2) + bb.toNat := by
      show b = 2 * (b / 2) + (decide (b % 2 = 1)).toNat
      by_cases h1 : b % 2 = 1 <;> simp [h1] <;> omega
    let s := ba.toNat + bb.toNat + cin.toNat
    let cout := decide (s ≥ 2)
    let bitSum := decide (s % 2 = 1)
    have hbit : 2 * cout.toNat + bitSum.toNat = ba.toNat + bb.toNat + cin.toNat := by
      show 2 * (decide (ba.toNat + bb.toNat + cin.toNat ≥ 2)).toNat +
           (decide ((ba.toNat + bb.toNat + cin.toNat) % 2 = 1)).toNat =
           ba.toNat + bb.toNat + cin.toNat
      cases ba <;> cases bb <;> cases cin <;> decide
    have hsum_eq : a + b + cin.toNat =
        2 * (a / 2 + b / 2 + cout.toNat) + bitSum.toNat := by
      omega
    have hlt : a / 2 + b / 2 < m := by omega
    have hih := ih (a / 2 + b / 2) hlt (a / 2) (b / 2) cout rfl
    have hc : carryCount a b cin = cout.toNat + carryCount (a / 2) (b / 2) cout := by
      conv => lhs; rw [ha_eq, hb_eq]
      exact carryCount_step (a / 2) (b / 2) ba bb cin
    have hpa : popcount a = popcount (a / 2) + ba.toNat := by
      conv => lhs; rw [ha_eq]
      exact popcount_step (a / 2) ba
    have hpb : popcount b = popcount (b / 2) + bb.toNat := by
      conv => lhs; rw [hb_eq]
      exact popcount_step (b / 2) bb
    have hps : popcount (a + b + cin.toNat) =
        popcount (a / 2 + b / 2 + cout.toNat) + bitSum.toNat := by
      rw [hsum_eq]
      exact popcount_step (a / 2 + b / 2 + cout.toNat) bitSum
    omega

theorem carryCount_eq_zero_iff_land_eq_zero (a b : Nat) :
    carryCount a b false = 0 ↔ a &&& b = 0 := by
  suffices h : ∀ m a b, a + b = m → (carryCount a b false = 0 ↔ a &&& b = 0) from
    h (a + b) a b rfl
  intro m
  refine strongNatInd (P := fun m => ∀ a b, a + b = m →
      (carryCount a b false = 0 ↔ a &&& b = 0)) ?_ m
  intro m ih a b hm
  by_cases h0 : a = 0 ∧ b = 0
  · rcases h0 with ⟨rfl, rfl⟩
    simp [carryCount_zero_zero]
  · let ba := decide (a % 2 = 1)
    let bb := decide (b % 2 = 1)
    have ha_eq : a = 2 * (a / 2) + ba.toNat := by
      show a = 2 * (a / 2) + (decide (a % 2 = 1)).toNat
      by_cases h1 : a % 2 = 1 <;> simp [h1] <;> omega
    have hb_eq : b = 2 * (b / 2) + bb.toNat := by
      show b = 2 * (b / 2) + (decide (b % 2 = 1)).toNat
      by_cases h1 : b % 2 = 1 <;> simp [h1] <;> omega
    have hta : Nat.testBit a 0 = ba := by
      rw [Nat.testBit_zero]
    have htb : Nat.testBit b 0 = bb := by
      rw [Nat.testBit_zero]
    have hc : carryCount a b false =
        (decide (ba.toNat + bb.toNat + 0 ≥ 2)).toNat +
          carryCount (a / 2) (b / 2) (decide (ba.toNat + bb.toNat + 0 ≥ 2)) := by
      conv => lhs; rw [ha_eq, hb_eq]
      exact carryCount_step (a / 2) (b / 2) ba bb false
    have hland_iff : a &&& b = 0 ↔ (ba && bb) = false ∧ (a / 2) &&& (b / 2) = 0 := by
      constructor
      · intro hl
        constructor
        · have h0b : Nat.testBit (a &&& b) 0 = false := by rw [hl]; simp
          rw [Nat.testBit_and, hta, htb] at h0b
          exact h0b
        · apply Nat.eq_of_testBit_eq
          intro k
          have hk : Nat.testBit (a &&& b) (k + 1) = false := by rw [hl]; simp
          rw [Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ] at hk
          rw [Nat.testBit_and, Nat.zero_testBit]
          exact hk
      · rintro ⟨hlow, hhi⟩
        apply Nat.eq_of_testBit_eq
        intro k
        cases k with
        | zero =>
          rw [Nat.testBit_and, Nat.zero_testBit, hta, htb]
          exact hlow
        | succ k =>
          rw [Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ, Nat.zero_testBit]
          have hk : Nat.testBit ((a / 2) &&& (b / 2)) k = false := by rw [hhi]; simp
          rw [Nat.testBit_and] at hk
          exact hk
    have hlt : a / 2 + b / 2 < m := by omega
    have hih := ih (a / 2 + b / 2) hlt (a / 2) (b / 2) rfl
    rw [hc, hland_iff]
    cases ba <;> cases bb <;> simp [hih]

def bitRel4Sem (mask v1 v2 v3 v4 : Nat) : Prop :=
  ∀ k : Nat, Nat.testBit mask
    (bitIdx4 (Nat.testBit v1 k) (Nat.testBit v2 k)
             (Nat.testBit v3 k) (Nat.testBit v4 k)) = true

private theorem bitRel4Fuel_eq (k1 k2 mask v1 v2 v3 v4 : Nat)
    (h1 : v1 + v2 + v3 + v4 ≤ k1) (h2 : v1 + v2 + v3 + v4 ≤ k2) :
    bitRel4Fuel k1 mask v1 v2 v3 v4 = bitRel4Fuel k2 mask v1 v2 v3 v4 := by
  induction k1 generalizing k2 v1 v2 v3 v4 with
  | zero =>
    have h0 : v1 = 0 ∧ v2 = 0 ∧ v3 = 0 ∧ v4 = 0 := by omega
    rcases h0 with ⟨rfl, rfl, rfl, rfl⟩
    cases k2 <;> simp [bitRel4Fuel]
  | succ k1 ih =>
    cases k2 with
    | zero =>
      have h0 : v1 = 0 ∧ v2 = 0 ∧ v3 = 0 ∧ v4 = 0 := by omega
      rcases h0 with ⟨rfl, rfl, rfl, rfl⟩
      simp [bitRel4Fuel]
    | succ k2 =>
      simp only [bitRel4Fuel]
      by_cases h0 : v1 = 0 ∧ v2 = 0 ∧ v3 = 0 ∧ v4 = 0
      · rcases h0 with ⟨rfl, rfl, rfl, rfl⟩; simp
      · have hnb : (v1 == 0 && v2 == 0 && v3 == 0 && v4 == 0) = false := by
          cases c1 : (v1 == 0) <;> cases c2 : (v2 == 0) <;>
            cases c3 : (v3 == 0) <;> cases c4 : (v4 == 0) <;> simp_all
        simp only [hnb, Bool.false_eq_true, ↓reduceIte]
        rw [ih k2 (v1 / 2) (v2 / 2) (v3 / 2) (v4 / 2) (by omega) (by omega)]

private theorem testBit_two_mul_add_zero (n : Nat) (b : Bool) :
    Nat.testBit (2 * n + b.toNat) 0 = b := by
  rw [Nat.testBit_zero]
  cases b <;> simp <;> omega

private theorem testBit_two_mul_add_succ (n : Nat) (b : Bool) (k : Nat) :
    Nat.testBit (2 * n + b.toNat) (k + 1) = Nat.testBit n k := by
  rw [Nat.testBit_succ]
  have hdiv : (2 * n + b.toNat) / 2 = n := by cases b <;> simp <;> omega
  rw [hdiv]

theorem bitRel4Sem_step (mask v1 v2 v3 v4 : Nat) (b1 b2 b3 b4 : Bool) :
    bitRel4Sem mask (2 * v1 + b1.toNat) (2 * v2 + b2.toNat)
                    (2 * v3 + b3.toNat) (2 * v4 + b4.toNat) ↔
      Nat.testBit mask (bitIdx4 b1 b2 b3 b4) = true ∧ bitRel4Sem mask v1 v2 v3 v4 := by
  constructor
  · intro h
    constructor
    · have h0 := h 0
      simp only [testBit_two_mul_add_zero] at h0
      exact h0
    · intro k
      have hk := h (k + 1)
      simp only [testBit_two_mul_add_succ] at hk
      exact hk
  · rintro ⟨h0, hrec⟩ k
    cases k with
    | zero =>
      simp only [testBit_two_mul_add_zero]
      exact h0
    | succ k =>
      simp only [testBit_two_mul_add_succ]
      exact hrec k

theorem bitRel4Dec_iff (mask v1 v2 v3 v4 : Nat) :
    bitRel4Dec mask v1 v2 v3 v4 = true ↔ bitRel4Sem mask v1 v2 v3 v4 := by
  suffices h : ∀ m v1 v2 v3 v4, v1 + v2 + v3 + v4 = m →
      (bitRel4Dec mask v1 v2 v3 v4 = true ↔ bitRel4Sem mask v1 v2 v3 v4) from
    h (v1 + v2 + v3 + v4) v1 v2 v3 v4 rfl
  intro m
  refine strongNatInd (P := fun m => ∀ v1 v2 v3 v4, v1 + v2 + v3 + v4 = m →
      (bitRel4Dec mask v1 v2 v3 v4 = true ↔ bitRel4Sem mask v1 v2 v3 v4)) ?_ m
  intro m ih v1 v2 v3 v4 hm
  by_cases h0 : v1 = 0 ∧ v2 = 0 ∧ v3 = 0 ∧ v4 = 0
  · rcases h0 with ⟨rfl, rfl, rfl, rfl⟩
    unfold bitRel4Dec
    simp [bitRel4Fuel, bitRel4Sem, bitIdx4]
  · conv => lhs; unfold bitRel4Dec
    rw [bitRel4Fuel_eq _ (v1 + v2 + v3 + v4 + 1) _ _ _ _ _ (by omega) (by omega)]
    simp only [bitRel4Fuel]
    have hnb : (v1 == 0 && v2 == 0 && v3 == 0 && v4 == 0) = false := by
      cases c1 : (v1 == 0) <;> cases c2 : (v2 == 0) <;>
        cases c3 : (v3 == 0) <;> cases c4 : (v4 == 0) <;> simp_all
    simp only [hnb, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true]
    rw [bitRel4Fuel_eq _ (v1 / 2 + v2 / 2 + v3 / 2 + v4 / 2) _ _ _ _ _ (by omega) (by omega)]
    change (Nat.testBit mask (bitIdx4 (decide (v1 % 2 = 1)) (decide (v2 % 2 = 1))
                                      (decide (v3 % 2 = 1)) (decide (v4 % 2 = 1))) = true ∧
            bitRel4Dec mask (v1 / 2) (v2 / 2) (v3 / 2) (v4 / 2) = true) ↔
           bitRel4Sem mask v1 v2 v3 v4
    have hlt : v1 / 2 + v2 / 2 + v3 / 2 + v4 / 2 < m := by omega
    have hih := ih (v1 / 2 + v2 / 2 + v3 / 2 + v4 / 2) hlt
                   (v1 / 2) (v2 / 2) (v3 / 2) (v4 / 2) rfl
    rw [hih]
    have hv1 : v1 = 2 * (v1 / 2) + (decide (v1 % 2 = 1)).toNat := by
      by_cases h1 : v1 % 2 = 1 <;> simp [h1] <;> omega
    have hv2 : v2 = 2 * (v2 / 2) + (decide (v2 % 2 = 1)).toNat := by
      by_cases h1 : v2 % 2 = 1 <;> simp [h1] <;> omega
    have hv3 : v3 = 2 * (v3 / 2) + (decide (v3 % 2 = 1)).toNat := by
      by_cases h1 : v3 % 2 = 1 <;> simp [h1] <;> omega
    have hv4 : v4 = 2 * (v4 / 2) + (decide (v4 % 2 = 1)).toNat := by
      by_cases h1 : v4 % 2 = 1 <;> simp [h1] <;> omega
    conv => rhs; rw [hv1, hv2, hv3, hv4]
    exact (bitRel4Sem_step mask (v1 / 2) (v2 / 2) (v3 / 2) (v4 / 2)
      (decide (v1 % 2 = 1)) (decide (v2 % 2 = 1))
      (decide (v3 % 2 = 1)) (decide (v4 % 2 = 1))).symm

theorem bitRel4Dec_step (mask v1 v2 v3 v4 : Nat) (b1 b2 b3 b4 : Bool) :
    bitRel4Dec mask (2 * v1 + b1.toNat) (2 * v2 + b2.toNat)
                    (2 * v3 + b3.toNat) (2 * v4 + b4.toNat) =
      (Nat.testBit mask (bitIdx4 b1 b2 b3 b4) && bitRel4Dec mask v1 v2 v3 v4) := by
  apply Bool.eq_iff_iff.mpr
  rw [bitRel4Dec_iff, bitRel4Sem_step, Bool.and_eq_true, bitRel4Dec_iff]

/-- Concrete 16-bit truth-table constants for common pointwise bitwise relations -/
def maskAndZero : Nat := 0x0FFF   -- ¬(b1 ∧ b2)            : t1 &&& t2 = 0
def maskXor3Eq0 : Nat := 0x3CC3   -- (b1 ^^ b2 ^^ b3) = 0  : (t1 ^^^ t2 ^^^ t3) = 0
def maskSubset  : Nat := 0xF0FF   -- b1 → b2               : t1 &&& t2 = t1

theorem bitRel4Dec_andZero_iff (a b : Nat) :
    bitRel4Dec maskAndZero a b 0 0 = true ↔ a &&& b = 0 := by
  rw [bitRel4Dec_iff]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro k
    have hk := h k
    rw [Nat.testBit_and, Nat.zero_testBit]
    have h0 : Nat.testBit 0 k = false := Nat.zero_testBit k
    rw [h0] at hk
    cases ha : Nat.testBit a k <;> cases hb : Nat.testBit b k <;>
      simp [ha, hb, bitIdx4, maskAndZero] at hk ⊢
    exact absurd hk (by decide)
  · intro h k
    have hk : Nat.testBit (a &&& b) k = false := by rw [h]; simp
    rw [Nat.testBit_and] at hk
    have h0 : Nat.testBit 0 k = false := Nat.zero_testBit k
    rw [h0]
    cases ha : Nat.testBit a k <;> cases hb : Nat.testBit b k <;>
      simp [ha, hb, bitIdx4, maskAndZero] at hk ⊢ <;> decide

theorem bitRel4Dec_xor3Eq0_iff (a b c : Nat) :
    bitRel4Dec maskXor3Eq0 a b c 0 = true ↔ (a ^^^ b ^^^ c) = 0 := by
  rw [bitRel4Dec_iff]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro k
    have hk := h k
    rw [Nat.testBit_xor, Nat.testBit_xor, Nat.zero_testBit]
    have h0 : Nat.testBit 0 k = false := Nat.zero_testBit k
    rw [h0] at hk
    cases ha : Nat.testBit a k <;> cases hb : Nat.testBit b k <;> cases hc : Nat.testBit c k <;>
      simp [ha, hb, hc, bitIdx4, maskXor3Eq0] at hk ⊢ <;> exact absurd hk (by decide)
  · intro h k
    have hk : Nat.testBit (a ^^^ b ^^^ c) k = false := by rw [h]; simp
    rw [Nat.testBit_xor, Nat.testBit_xor] at hk
    have h0 : Nat.testBit 0 k = false := Nat.zero_testBit k
    rw [h0]
    cases ha : Nat.testBit a k <;> cases hb : Nat.testBit b k <;> cases hc : Nat.testBit c k <;>
      simp [ha, hb, hc, bitIdx4, maskXor3Eq0] at hk ⊢ <;> decide

theorem vecStep_length (vs : List Nat) (bs : List Bool) (h : vs.length = bs.length) :
    (vecStep vs bs).length = vs.length := by
  induction vs generalizing bs with
  | nil => cases bs <;> simp [vecStep] at h ⊢
  | cons v vs ih =>
    cases bs with
    | nil => simp at h
    | cons b bs =>
      simp only [List.length_cons, Nat.succ.injEq] at h
      simp [vecStep, ih bs h]

theorem vecStep_append (v1 v2 : List Nat) (b1 b2 : List Bool)
    (h1 : v1.length = b1.length) :
    vecStep (v1 ++ v2) (b1 ++ b2) = vecStep v1 b1 ++ vecStep v2 b2 := by
  induction v1 generalizing b1 with
  | nil =>
    cases b1 with
    | nil => rfl
    | cons _ _ => simp at h1
  | cons v vs ih =>
    cases b1 with
    | nil => simp at h1
    | cons b bs =>
      simp only [List.length_cons, Nat.succ.injEq] at h1
      simp [vecStep, ih bs h1]

theorem vecDiv2_length (x : List Nat) : (vecDiv2 x).length = x.length := by
  induction x with
  | nil => rfl
  | cons _ xs ih => simp [vecDiv2, ih]

theorem vecMod2Bits_length (x : List Nat) : (vecMod2Bits x).length = x.length := by
  induction x with
  | nil => rfl
  | cons _ xs ih => simp [vecMod2Bits, ih]

theorem vecStep_vecDiv2_vecMod2Bits (x : List Nat) :
    vecStep (vecDiv2 x) (vecMod2Bits x) = x := by
  induction x with
  | nil => rfl
  | cons v vs ih =>
    simp only [vecDiv2, vecMod2Bits, vecStep, ih, List.cons.injEq, and_true]
    by_cases hm : v % 2 = 1 <;> simp [hm] <;> omega

theorem vecSum_eq_zero_iff (x : List Nat) :
    vecSum x = 0 ↔ x = List.replicate x.length 0 := by
  induction x with
  | nil => simp [vecSum]
  | cons v vs ih =>
    simp only [vecSum, List.length_cons, List.replicate_succ, List.cons.injEq]
    constructor
    · intro h
      have hv : v = 0 := by omega
      have hvs : vecSum vs = 0 := by omega
      exact ⟨hv, ih.mp hvs⟩
    · rintro ⟨rfl, hvs⟩
      have := ih.mpr hvs
      omega

theorem vecSum_vecDiv2_lt (x : List Nat) (h : vecSum x ≠ 0) :
    vecSum (vecDiv2 x) < vecSum x := by
  induction x with
  | nil => simp [vecSum] at h
  | cons v vs ih =>
    simp only [vecDiv2, vecSum] at h ⊢
    by_cases hvs : vecSum vs = 0
    · have hv : v > 0 := by omega
      have hdiv : vecSum (vecDiv2 vs) ≤ vecSum vs := by
        have hrep := (vecSum_eq_zero_iff vs).mp hvs
        clear h ih hv hvs
        induction vs with
        | nil => simp [vecDiv2, vecSum]
        | cons u us ihu =>
          simp only [List.length_cons, List.replicate_succ, List.cons.injEq] at hrep
          rcases hrep with ⟨rfl, hrep'⟩
          simp only [vecDiv2, vecSum]
          have := ihu hrep'
          omega
      omega
    · have hlt := ih hvs
      omega

theorem dotNat_vecStep (cs : List Nat) (vs : List Nat) (bs : List Bool)
    (h : vs.length = bs.length) :
    dotNat cs (vecStep vs bs) = 2 * dotNat cs vs + dotNatBool cs bs := by
  induction cs generalizing vs bs with
  | nil => simp [dotNat, dotNatBool]
  | cons c cs ih =>
    cases vs with
    | nil =>
      cases bs with
      | nil => simp [vecStep, dotNat, dotNatBool]
      | cons _ _ => simp at h
    | cons v vs =>
      cases bs with
      | nil => simp at h
      | cons b bs =>
        simp only [List.length_cons, Nat.succ.injEq] at h
        simp only [vecStep, dotNat, dotNatBool, ih vs bs h]
        have hmul : c * (2 * v + b.toNat) = 2 * (c * v) + c * b.toNat := by
          rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm c 2, Nat.mul_assoc]
        omega

theorem dotInt_vecStep (cs : List Int) (vs : List Nat) (bs : List Bool)
    (h : vs.length = bs.length) :
    dotInt cs (vecStep vs bs) = 2 * dotInt cs vs + dotIntBool cs bs := by
  induction cs generalizing vs bs with
  | nil => simp [dotInt, dotIntBool]
  | cons c cs ih =>
    cases vs with
    | nil =>
      cases bs with
      | nil => simp [vecStep, dotInt, dotIntBool]
      | cons _ _ => simp at h
    | cons v vs =>
      cases bs with
      | nil => simp at h
      | cons b bs =>
        simp only [List.length_cons, Nat.succ.injEq] at h
        simp only [vecStep, dotInt, dotIntBool, ih vs bs h]
        have hcast : ((2 * v + b.toNat : Nat) : Int) = 2 * (v : Int) + (b.toNat : Int) := by
          omega
        rw [hcast]
        have hmul : c * (2 * (v : Int) + (b.toNat : Int)) =
            2 * (c * (v : Int)) + c * (b.toNat : Int) := by
          rw [Int.mul_add, ← Int.mul_assoc, Int.mul_comm c 2, Int.mul_assoc]
        omega

theorem dotInt_nonneg_of_all_nonneg (cs : List Int) (vs : List Nat)
    (h : cs.all (fun c => decide (0 ≤ c)) = true) :
    0 ≤ dotInt cs vs := by
  induction cs generalizing vs with
  | nil => simp [dotInt]
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    cases vs with
    | nil => simp [dotInt]
    | cons v vs =>
      simp only [dotInt]
      have h1 : 0 ≤ c * (v : Int) := Int.mul_nonneg h.1 (Int.natCast_nonneg v)
      have h2 : 0 ≤ dotInt cs vs := ih vs h.2
      omega

theorem dotInt_nonpos_of_all_nonpos (cs : List Int) (vs : List Nat)
    (h : cs.all (fun c => decide (c ≤ 0)) = true) :
    dotInt cs vs ≤ 0 := by
  induction cs generalizing vs with
  | nil => simp [dotInt]
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    cases vs with
    | nil => simp [dotInt]
    | cons v vs =>
      simp only [dotInt]
      have h1 : c * (v : Int) ≤ 0 := by
        have hneg : 0 ≤ (-c) * (v : Int) := Int.mul_nonneg (by omega) (Int.natCast_nonneg v)
        rw [Int.neg_mul] at hneg
        omega
      have h2 : dotInt cs vs ≤ 0 := ih vs h.2
      omega

theorem dotNat_zero_of_all_zero (cs : List Nat) (vs : List Nat)
    (h : cs.all (fun c => c == 0) = true) :
    dotNat cs vs = 0 := by
  induction cs generalizing vs with
  | nil => simp [dotNat]
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    cases vs with
    | nil => simp [dotNat]
    | cons v vs =>
      simp [dotNat, h.1, ih vs h.2]

theorem dotInt_zero_of_all_zero (cs : List Int) (vs : List Nat)
    (h : cs.all (fun c => c == 0) = true) :
    dotInt cs vs = 0 := by
  induction cs generalizing vs with
  | nil => simp [dotInt]
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    cases vs with
    | nil => simp [dotInt]
    | cons v vs =>
      simp [dotInt, h.1, ih vs h.2]

private theorem eqNatAff_eq {a b : NatAff} (h : eqNatAff a b = true) : a = b := by
  cases a; cases b
  simp only [eqNatAff, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩; rfl

private theorem eqIntAff_eq {a b : IntAff} (h : eqIntAff a b = true) : a = b := by
  cases a; cases b
  simp only [eqIntAff, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩; rfl

theorem NatAff.eval_vecStep (t : NatAff) (vs : List Nat) (bs : List Bool)
    (h : vs.length = bs.length) :
    t.eval (vecStep vs bs) =
      2 * (t.step bs).2.eval vs + (t.step bs).1.toNat := by
  simp only [NatAff.eval, NatAff.step, dotNat_vecStep t.coeffs vs bs h]
  by_cases hm : (dotNatBool t.coeffs bs + t.carry) % 2 = 1 <;> simp [hm] <;> omega

private theorem eqPopTerms_eq {a b : List (Int × NatAff)} (h : eqPopTerms a b = true) : a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp [eqPopTerms] at h ⊢
  | cons p1 r1 ih =>
    cases b with
    | nil => simp [eqPopTerms] at h
    | cons p2 r2 =>
      rcases p1 with ⟨w1, t1⟩; rcases p2 with ⟨w2, t2⟩
      simp only [eqPopTerms, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1.1, eqNatAff_eq h.1.2, ih h.2]

private theorem eqAtom_eq {a b : Atom} (h : eqAtom a b = true) : a = b := by
  cases a <;> cases b <;> simp only [eqAtom, Bool.and_eq_true, beq_iff_eq] at h <;>
    try exact absurd h (by decide)
  · rw [eqIntAff_eq h]
  · rw [eqIntAff_eq h]
  · rcases h with ⟨⟨rfl, rfl⟩, rfl⟩; rfl
  · rcases h with ⟨⟨⟨⟨rfl, h1⟩, h2⟩, h3⟩, h4⟩
    rw [eqNatAff_eq h1, eqNatAff_eq h2, eqNatAff_eq h3, eqNatAff_eq h4]
  · rcases h with ⟨⟨⟨rfl, rfl⟩, h1⟩, h2⟩
    rw [eqNatAff_eq h1, eqNatAff_eq h2]
  · rcases h with ⟨⟨rfl, rfl⟩, ht⟩
    rw [eqPopTerms_eq ht]

private theorem eqFormula_eq {p q : Formula} (h : eqFormula p q = true) : p = q := by
  induction p generalizing q with
  | tt => cases q <;> simp [eqFormula] at h ⊢
  | ff => cases q <;> simp [eqFormula] at h ⊢
  | atom a1 =>
    cases q <;> simp [eqFormula] at h
    rw [eqAtom_eq h]
  | not f1 ih =>
    cases q <;> simp [eqFormula] at h
    rw [ih h]
  | and a1 b1 iha ihb =>
    cases q <;> simp [eqFormula] at h
    rw [iha h.1, ihb h.2]
  | or a1 b1 iha ihb =>
    cases q <;> simp [eqFormula] at h
    rw [iha h.1, ihb h.2]

def Formula.imp (a b : Formula) : Formula := .or (.not a) b
def Formula.iff (a b : Formula) : Formula := .and (Formula.imp a b) (Formula.imp b a)

theorem evalFormulaBool_mkNot (f : Formula) (v : List Nat) :
    evalFormulaBool (mkNot f) v = !(evalFormulaBool f v) := by
  cases f <;> simp [mkNot, evalFormulaBool]

theorem evalFormulaBool_mkAnd (f1 f2 : Formula) (v : List Nat) :
    evalFormulaBool (mkAnd f1 f2) v = (evalFormulaBool f1 v && evalFormulaBool f2 v) := by
  cases he : eqFormula f1 f2
  · cases f1 <;> cases f2 <;> simp [mkAnd, he, evalFormulaBool]
  · have h := eqFormula_eq he
    subst h
    cases f1 <;> simp [mkAnd, he, evalFormulaBool]

theorem evalFormulaBool_mkOr (f1 f2 : Formula) (v : List Nat) :
    evalFormulaBool (mkOr f1 f2) v = (evalFormulaBool f1 v || evalFormulaBool f2 v) := by
  cases he : eqFormula f1 f2
  · cases f1 <;> cases f2 <;> simp [mkOr, he, evalFormulaBool]
  · have h := eqFormula_eq he
    subst h
    cases f1 <;> simp [mkOr, he, evalFormulaBool]

theorem evalFormulaBool_bigOr_iff (fs : List Formula) (v : List Nat) :
    evalFormulaBool (bigOr fs) v = true ↔ ∃ f ∈ fs, evalFormulaBool f v = true := by
  induction fs with
  | nil => simp [bigOr, evalFormulaBool]
  | cons f fs ih =>
    cases fs with
    | nil => simp [bigOr]
    | cons f2 fs2 =>
      simp only [bigOr, evalFormulaBool_mkOr, Bool.or_eq_true, ih, List.mem_cons]
      constructor
      · rintro (hf | ⟨g, hg, hgv⟩)
        · exact ⟨f, Or.inl rfl, hf⟩
        · exact ⟨g, Or.inr hg, hgv⟩
      · rintro ⟨g, rfl | hg, hgv⟩
        · exact Or.inl hgv
        · exact Or.inr ⟨g, hg, hgv⟩

theorem evalFormulaBool_simpAtom (a : Atom) (v : List Nat) :
    evalFormulaBool (simpAtom a) v = evalAtomBool a v := by
  cases a with
  | linLe t =>
    simp only [simpAtom]
    split
    · rename_i h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      have hle := dotInt_nonpos_of_all_nonpos t.coeffs v h.1
      simp [evalFormulaBool, evalAtomBool]
      omega
    · split
      · rename_i h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        have hge := dotInt_nonneg_of_all_nonneg t.coeffs v h.1
        simp [evalFormulaBool, evalAtomBool]
        omega
      · rfl
  | linEq t =>
    simp only [simpAtom]
    split
    · rename_i hz
      have h0 := dotInt_zero_of_all_zero t.coeffs v hz
      split
      · rename_i hr
        simp only [beq_iff_eq] at hr
        simp [evalFormulaBool, evalAtomBool, h0, hr]
      · rename_i hr
        simp only [beq_iff_eq] at hr
        simp only [evalFormulaBool, evalAtomBool, h0]
        have hne : (0 : Int) ≠ t.rhs := fun h => hr h.symm
        simp [hne]
    · split
      · rename_i h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        have hge := dotInt_nonneg_of_all_nonneg t.coeffs v h.1
        simp [evalFormulaBool, evalAtomBool]
        omega
      · split
        · rename_i h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          have hle := dotInt_nonpos_of_all_nonpos t.coeffs v h.1
          simp [evalFormulaBool, evalAtomBool]
          omega
        · rfl
  | modEq cs m r =>
    simp only [simpAtom]
    split
    · rename_i hm
      have hcases : m = 0 ∨ m = 1 := by omega
      rcases hcases with rfl | rfl
      · simp [evalFormulaBool, evalAtomBool]
      · simp [evalFormulaBool, evalAtomBool]
    · simp [evalFormulaBool, evalAtomBool]
  | bitRel4 mask t1 t2 t3 t4 =>
    simp only [simpAtom]
    split
    · rename_i h
      simp only [Bool.and_eq_true] at h
      have h1 := dotNat_zero_of_all_zero t1.coeffs v h.1.1.1
      have h2 := dotNat_zero_of_all_zero t2.coeffs v h.1.1.2
      have h3 := dotNat_zero_of_all_zero t3.coeffs v h.1.2
      have h4 := dotNat_zero_of_all_zero t4.coeffs v h.2
      simp only [evalAtomBool, NatAff.eval, h1, h2, h3, h4, Nat.zero_add]
      cases hb : bitRel4Dec mask t1.carry t2.carry t3.carry t4.carry <;>
        simp [evalFormulaBool]
    · rfl
  | carryLe t1 t2 cin k =>
    simp only [simpAtom]
    split
    · rename_i h
      simp only [Bool.and_eq_true] at h
      have h1 := dotNat_zero_of_all_zero t1.coeffs v h.1
      have h2 := dotNat_zero_of_all_zero t2.coeffs v h.2
      simp only [evalAtomBool, NatAff.eval, h1, h2, Nat.zero_add]
      by_cases hk : carryCount t1.carry t2.carry cin ≤ k <;>
        simp [hk, evalFormulaBool]
    · rfl
  | popMod terms m r =>
    simp only [simpAtom]
    split
    · rename_i hm
      have hcases : m = 0 ∨ m = 1 := by omega
      rcases hcases with rfl | rfl
      · simp [evalFormulaBool, evalAtomBool]
      · simp [evalFormulaBool, evalAtomBool]
    · simp [evalFormulaBool, evalAtomBool]

theorem evalPopSum_vecStep (terms : List (Int × NatAff)) (vs : List Nat) (bs : List Bool)
    (h : vs.length = bs.length) :
    evalPopSum terms (vecStep vs bs) =
      evalPopSum (stepPopTerms terms bs).2 vs + (stepPopTerms terms bs).1 := by
  induction terms with
  | nil => simp [evalPopSum, stepPopTerms]
  | cons wt rest ih =>
    rcases wt with ⟨w, t⟩
    simp only [evalPopSum, stepPopTerms, NatAff.eval_vecStep t vs bs h,
               popcount_step, ih]
    have hcast : ((popcount ((t.step bs).2.eval vs) + (t.step bs).1.toNat : Nat) : Int) =
        (popcount ((t.step bs).2.eval vs) : Int) + ((t.step bs).1.toNat : Int) := by
      omega
    rw [hcast, Int.mul_add]
    omega

/-! ### Exact Modular Arithmetic Halving Lemmas (All Moduli m ≥ 1) -/

private theorem int_emod_eq_iff_dvd (a b : Int) (m : Nat) (_hm : 0 < m) :
    a % (m : Int) = b % (m : Int) ↔ (m : Int) ∣ (a - b) := by
  constructor
  · intro h
    refine ⟨a / (m : Int) - b / (m : Int), ?_⟩
    have ha := Int.emod_add_mul_ediv a (m : Int)
    have hb := Int.emod_add_mul_ediv b (m : Int)
    rw [Int.mul_sub]
    omega
  · rintro ⟨q, hq⟩
    have hab : a = b + (m : Int) * q := by omega
    rw [hab, Int.add_mul_emod_self_left]

private theorem toNat_mod_cast (x : Int) (m : Nat) (hm : 0 < m) :
    (((x % (m : Int)).toNat % m : Nat) : Int) = x % (m : Int) := by
  have h1 : 0 ≤ x % (m : Int) := Int.emod_nonneg x (by omega)
  have h2 : x % (m : Int) < (m : Int) := Int.emod_lt_of_pos x (by omega)
  have hlt : (x % (m : Int)).toNat < m := by omega
  rw [Nat.mod_eq_of_lt hlt]
  omega

private theorem mod_step_even (u s : Int) (m r : Nat) (hm : 0 < m) (heven : m % 2 = 0) :
    (2 * u + s) % (m : Int) = ((r % m : Nat) : Int) ↔
      ((r : Int) - s) % 2 = 0 ∧
        u % ((m / 2 : Nat) : Int) =
          ((((((r : Int) - s) / 2) % ((m / 2 : Nat) : Int)).toNat % (m / 2) : Nat) : Int) := by
  have hm'pos : 0 < m / 2 := by omega
  have hr_eq : ((r % m : Nat) : Int) = (r : Int) % (m : Int) := by omega
  rw [hr_eq, int_emod_eq_iff_dvd _ _ m hm]
  let v : Int := (r : Int) - s
  have hsub : 2 * u + s - (r : Int) = 2 * u - v := by omega
  rw [hsub]
  change (m : Int) ∣ 2 * u - v ↔ v % 2 = 0 ∧
      u % ((m / 2 : Nat) : Int) =
        ((((v / 2) % ((m / 2 : Nat) : Int)).toNat % (m / 2) : Nat) : Int)
  rw [toNat_mod_cast (v / 2) (m / 2) hm'pos, int_emod_eq_iff_dvd _ _ (m / 2) hm'pos]
  constructor
  · rintro ⟨q, hq⟩
    have hv : v = 2 * (u - ((m / 2 : Nat) : Int) * q) := by
      have hmcast : (m : Int) = 2 * ((m / 2 : Nat) : Int) := by omega
      rw [hmcast] at hq
      have : 2 * ((m / 2 : Nat) : Int) * q = 2 * (((m / 2 : Nat) : Int) * q) :=
        Int.mul_assoc 2 ((m / 2 : Nat) : Int) q
      omega
    have hveven : v % 2 = 0 := by omega
    have hvdiv : v / 2 = u - ((m / 2 : Nat) : Int) * q := by omega
    exact ⟨hveven, ⟨q, by omega⟩⟩
  · rintro ⟨hveven, ⟨q, hq⟩⟩
    have hv : v = 2 * (v / 2) := by omega
    refine ⟨q, ?_⟩
    have hmcast : (m : Int) = 2 * ((m / 2 : Nat) : Int) := by omega
    rw [hmcast, Int.mul_assoc]
    omega

private theorem mod_step_odd (u s : Int) (m r : Nat) (hm : 0 < m) (hodd : m % 2 = 1) :
    (2 * u + s) % (m : Int) = ((r % m : Nat) : Int) ↔
      u % (m : Int) =
        ((((((m + 1) / 2 : Nat) : Int) * ((r : Int) - s)) % (m : Int)).toNat % m : Nat) := by
  have hr_eq : ((r % m : Nat) : Int) = (r : Int) % (m : Int) := by omega
  rw [hr_eq, int_emod_eq_iff_dvd _ _ m hm]
  let v : Int := (r : Int) - s
  let inv2 : Int := (((m + 1) / 2 : Nat) : Int)
  have h2inv : 2 * inv2 = (m : Int) + 1 := by omega
  change (m : Int) ∣ 2 * u + s - (r : Int) ↔
      u % (m : Int) = ((((inv2 * v) % (m : Int)).toNat % m : Nat) : Int)
  rw [toNat_mod_cast (inv2 * v) m hm, int_emod_eq_iff_dvd _ _ m hm]
  have hsub : 2 * u + s - (r : Int) = 2 * u - v := by omega
  rw [hsub]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨inv2 * q - u, ?_⟩
    have h1 : inv2 * (2 * u - v) = inv2 * ((m : Int) * q) := congrArg (inv2 * ·) hq
    have h2 : inv2 * (2 * u - v) = (2 * inv2) * u - inv2 * v := by
      rw [Int.mul_sub, ← Int.mul_assoc, Int.mul_comm inv2 2]
    have h3 : inv2 * ((m : Int) * q) = (m : Int) * (inv2 * q) := by
      rw [← Int.mul_assoc, Int.mul_comm inv2 (m : Int), Int.mul_assoc]
    rw [h2, h2inv, Int.add_mul, Int.one_mul, h3] at h1
    have h4 : (m : Int) * (inv2 * q - u) = (m : Int) * (inv2 * q) - (m : Int) * u :=
      Int.mul_sub (m : Int) (inv2 * q) u
    omega
  · rintro ⟨q, hq⟩
    refine ⟨2 * q + v, ?_⟩
    have h1 : 2 * (u - inv2 * v) = 2 * ((m : Int) * q) := congrArg (2 * ·) hq
    have h2 : 2 * (u - inv2 * v) = 2 * u - (2 * inv2) * v := by
      rw [Int.mul_sub, ← Int.mul_assoc]
    have h3 : 2 * ((m : Int) * q) = (m : Int) * (2 * q) := by
      rw [← Int.mul_assoc, Int.mul_comm 2 (m : Int), Int.mul_assoc]
    rw [h2, h2inv, Int.add_mul, Int.one_mul, h3] at h1
    rw [Int.mul_add]
    omega

theorem evalFormulaBool_stepAtom (a : Atom) (vs : List Nat) (bs : List Bool)
    (h : vs.length = bs.length) :
    evalFormulaBool (stepAtom a bs) vs = evalAtomBool a (vecStep vs bs) := by
  cases a with
  | linLe t =>
    simp only [stepAtom, evalFormulaBool_simpAtom, evalAtomBool, dotInt_vecStep t.coeffs vs bs h]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  | linEq t =>
    simp only [stepAtom]
    split
    · rename_i heven
      simp only [beq_iff_eq] at heven
      simp only [evalFormulaBool_simpAtom, evalAtomBool, dotInt_vecStep t.coeffs vs bs h]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      omega
    · rename_i hodd
      simp only [beq_iff_eq] at hodd
      simp only [evalFormulaBool, evalAtomBool, dotInt_vecStep t.coeffs vs bs h]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.false_eq_true, decide_eq_true_eq, false_iff]
      omega
  | modEq cs m r =>
    simp only [stepAtom]
    split
    · rename_i hm
      have hcases : m = 0 ∨ m = 1 := by omega
      rcases hcases with rfl | rfl
      · simp [evalFormulaBool, evalAtomBool]
      · simp [evalFormulaBool, evalAtomBool]
    · rename_i hm
      have hmpos : 0 < m := by omega
      have hm0 : (m == 0) = false := by simp; omega
      split
      · rename_i hev
        simp only [beq_iff_eq] at hev
        split
        · rename_i hvev
          simp only [beq_iff_eq] at hvev
          simp only [evalFormulaBool_simpAtom, evalAtomBool,
                     dotInt_vecStep cs vs bs h, hm0]
          have hm'0 : (m / 2 == 0) = false := by simp; omega
          simp only [hm'0, Bool.false_eq_true, ↓reduceIte]
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq]
          have hstep := mod_step_even (dotInt cs vs) (dotIntBool cs bs) m r hmpos hev
          rw [hstep]
          exact ⟨fun hu => ⟨hvev, hu⟩, fun ⟨_, hu⟩ => hu⟩
        · rename_i hvodd
          simp only [beq_iff_eq] at hvodd
          simp only [evalFormulaBool, evalAtomBool, dotInt_vecStep cs vs bs h, hm0,
                     Bool.false_eq_true, ↓reduceIte]
          apply Bool.eq_iff_iff.mpr
          simp only [Bool.false_eq_true, decide_eq_true_eq, false_iff]
          have hstep := mod_step_even (dotInt cs vs) (dotIntBool cs bs) m r hmpos hev
          rw [hstep]
          intro ⟨hvev, _⟩
          exact hvodd hvev
      · rename_i hodd
        simp only [beq_iff_eq] at hodd
        have hodd1 : m % 2 = 1 := by omega
        simp only [evalFormulaBool_simpAtom, evalAtomBool,
                   dotInt_vecStep cs vs bs h, hm0, Bool.false_eq_true, ↓reduceIte]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        exact (mod_step_odd (dotInt cs vs) (dotIntBool cs bs) m r hmpos hodd1).symm
  | bitRel4 mask t1 t2 t3 t4 =>
    simp only [stepAtom, evalAtomBool,
               NatAff.eval_vecStep t1 vs bs h, NatAff.eval_vecStep t2 vs bs h,
               NatAff.eval_vecStep t3 vs bs h, NatAff.eval_vecStep t4 vs bs h,
               bitRel4Dec_step]
    split
    · rename_i hbit
      simp only [evalFormulaBool_simpAtom, evalAtomBool, hbit, Bool.true_and]
    · rename_i hbit
      have hbf : Nat.testBit mask (bitIdx4 (t1.step bs).1 (t2.step bs).1
                                           (t3.step bs).1 (t4.step bs).1) = false := by
        cases hc : Nat.testBit mask (bitIdx4 (t1.step bs).1 (t2.step bs).1
                                             (t3.step bs).1 (t4.step bs).1) <;> simp_all
      simp [evalFormulaBool, hbf]
  | carryLe t1 t2 cin k =>
    simp only [stepAtom, evalAtomBool,
               NatAff.eval_vecStep t1 vs bs h, NatAff.eval_vecStep t2 vs bs h,
               carryCount_step]
    split
    · rename_i hcout
      simp only [hcout, Bool.toNat_true]
      split
      · rename_i hk0
        simp only [beq_iff_eq] at hk0
        subst hk0
        simp [evalFormulaBool]
      · rename_i hk0
        simp only [beq_iff_eq] at hk0
        simp only [evalFormulaBool_simpAtom, evalAtomBool]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        omega
    · rename_i hcout
      have hcf : decide ((t1.step bs).1.toNat + (t2.step bs).1.toNat + cin.toNat ≥ 2) = false := by
        cases hc : decide ((t1.step bs).1.toNat + (t2.step bs).1.toNat + cin.toNat ≥ 2) <;> simp_all
      simp only [hcf, Bool.toNat_false, Nat.zero_add, evalFormulaBool_simpAtom, evalAtomBool]
  | popMod terms m r =>
    simp only [stepAtom]
    split
    · rename_i hm
      have hcases : m = 0 ∨ m = 1 := by omega
      rcases hcases with rfl | rfl
      · simp [evalFormulaBool, evalAtomBool]
      · simp [evalFormulaBool, evalAtomBool]
    · rename_i hm
      have hmpos : 0 < m := by omega
      have hm0 : (m == 0) = false := by simp; omega
      simp only [evalFormulaBool_simpAtom, evalAtomBool, hm0,
                 Bool.false_eq_true, ↓reduceIte, evalPopSum_vecStep terms vs bs h]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      let u := evalPopSum (stepPopTerms terms bs).2 vs
      let delta := (stepPopTerms terms bs).1
      have hr_eq : ((r % m : Nat) : Int) = (r : Int) % (m : Int) := by omega
      change u % (m : Int) = (((((r : Int) - delta) % (m : Int)).toNat % m : Nat) : Int) ↔
        (u + delta) % (m : Int) = ((r % m : Nat) : Int)
      rw [toNat_mod_cast ((r : Int) - delta) m hmpos, hr_eq,
          int_emod_eq_iff_dvd _ _ m hmpos, int_emod_eq_iff_dvd _ _ m hmpos]
      have hsub : u - ((r : Int) - delta) = u + delta - (r : Int) := by omega
      rw [hsub]

/-- Master Exact Derivative Theorem for all Carry-Presburger Formulas -/
theorem evalFormulaBool_stepFormula (f : Formula) (vs : List Nat) (bs : List Bool)
    (h : vs.length = bs.length) :
    evalFormulaBool (stepFormula f bs) vs = evalFormulaBool f (vecStep vs bs) := by
  induction f with
  | tt => rfl
  | ff => rfl
  | atom a => exact evalFormulaBool_stepAtom a vs bs h
  | not f1 ih => simp [stepFormula, evalFormulaBool_mkNot, evalFormulaBool, ih]
  | and f1 f2 ih1 ih2 => simp [stepFormula, evalFormulaBool_mkAnd, evalFormulaBool, ih1, ih2]
  | or f1 f2 ih1 ih2 => simp [stepFormula, evalFormulaBool_mkOr, evalFormulaBool, ih1, ih2]

theorem entailsAtom_sound (a1 a2 : Atom) (v : List Nat)
    (he : entailsAtom a1 a2 = true) (h1 : evalAtomBool a1 v = true) :
    evalAtomBool a2 v = true := by
  cases a1 with
  | linLe t1 =>
    cases a2 with
    | linLe t2 =>
      simp only [entailsAtom, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at he
      simp only [evalAtomBool, decide_eq_true_eq] at h1 ⊢
      rw [← he.1]; omega
    | _ => simp [entailsAtom, eqAtom] at he
  | linEq t1 =>
    cases a2 with
    | linLe t2 =>
      simp only [entailsAtom, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at he
      simp only [evalAtomBool, decide_eq_true_eq] at h1 ⊢
      rw [← he.1]; omega
    | modEq c2 m2 r2 =>
      simp only [entailsAtom, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at he
      simp only [evalAtomBool, decide_eq_true_eq] at h1 ⊢
      rcases he.2 with hm0 | hmod
      · simp [hm0]
      · rw [← he.1, h1]
        split
        · rfl
        · simp [hmod]
    | linEq t2 =>
      simp only [entailsAtom] at he; rw [← eqAtom_eq he]; exact h1
    | _ => simp [entailsAtom, eqAtom] at he
  | carryLe a1 b1 cin1 k1 =>
    cases a2 with
    | carryLe a2 b2 cin2 k2 =>
      simp only [entailsAtom, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at he
      rcases he with ⟨⟨⟨rfl, hk⟩, ha⟩, hb⟩
      rw [eqNatAff_eq ha, eqNatAff_eq hb] at h1
      simp only [evalAtomBool, decide_eq_true_eq] at h1 ⊢
      omega
    | _ => simp [entailsAtom, eqAtom] at he
  | modEq c1 m1 r1 =>
    cases a2 <;> simp only [entailsAtom] at he
    · cases he
    · cases he
    · rw [← eqAtom_eq he]; exact h1
    · cases he
    · cases he
    · cases he
  | bitRel4 mask1 t1 t2 t3 t4 =>
    cases a2 <;> simp only [entailsAtom] at he
    · cases he
    · cases he
    · cases he
    · rw [← eqAtom_eq he]; exact h1
    · cases he
    · cases he
  | popMod terms1 m1 r1 =>
    cases a2 <;> simp only [entailsAtom] at he
    · cases he
    · cases he
    · cases he
    · cases he
    · cases he
    · rw [← eqAtom_eq he]; exact h1

private theorem entailsFuel_sound (fuel : Nat) (p q : Formula) (v : List Nat)
    (he : entailsFuel fuel p q = true) (hp : evalFormulaBool p v = true) :
    evalFormulaBool q v = true := by
  induction fuel generalizing p q with
  | zero => cases he
  | succ fuel ih =>
    cases heq : eqFormula p q
    · simp only [entailsFuel, heq, Bool.false_eq_true, ↓reduceIte] at he
      cases p with
      | ff => simp [evalFormulaBool] at hp
      | or p1 p2 =>
        cases q with
        | tt => rfl
        | _ =>
          dsimp only at he
          simp only [Bool.and_eq_true] at he
          simp only [evalFormulaBool, Bool.or_eq_true] at hp
          rcases hp with hp1 | hp2
          · exact ih p1 _ he.1 hp1
          · exact ih p2 _ he.2 hp2
      | tt =>
        cases q with
        | tt => rfl
        | or q1 q2 =>
          dsimp only at he
          simp only [Bool.or_eq_true] at he
          simp only [evalFormulaBool, Bool.or_eq_true]
          rcases he with h1 | h2
          · exact Or.inl (ih .tt q1 h1 hp)
          · exact Or.inr (ih .tt q2 h2 hp)
        | and q1 q2 =>
          dsimp only at he
          simp only [Bool.and_eq_true] at he
          simp only [evalFormulaBool, Bool.and_eq_true]
          exact ⟨ih .tt q1 he.1 hp, ih .tt q2 he.2 hp⟩
        | _ => dsimp only at he; cases he
      | atom a1 =>
        cases q with
        | tt => rfl
        | atom a2 => exact entailsAtom_sound a1 a2 v he hp
        | or q1 q2 =>
          dsimp only at he
          simp only [Bool.or_eq_true] at he
          simp only [evalFormulaBool, Bool.or_eq_true]
          rcases he with h1 | h2
          · exact Or.inl (ih (.atom a1) q1 h1 hp)
          · exact Or.inr (ih (.atom a1) q2 h2 hp)
        | and q1 q2 =>
          dsimp only at he
          simp only [Bool.and_eq_true] at he
          simp only [evalFormulaBool, Bool.and_eq_true]
          exact ⟨ih (.atom a1) q1 he.1 hp, ih (.atom a1) q2 he.2 hp⟩
        | _ => dsimp only at he; cases he
      | not p1 =>
        cases q with
        | tt => rfl
        | not q1 =>
          dsimp only at he
          simp only [evalFormulaBool, Bool.not_eq_true'] at hp ⊢
          cases hq : evalFormulaBool q1 v
          · rfl
          · have h1 := ih q1 p1 he hq
            rw [h1] at hp
            exact absurd hp (by decide)
        | or q1 q2 =>
          dsimp only at he
          simp only [Bool.or_eq_true] at he
          simp only [evalFormulaBool, Bool.or_eq_true]
          rcases he with h1 | h2
          · exact Or.inl (ih (.not p1) q1 h1 hp)
          · exact Or.inr (ih (.not p1) q2 h2 hp)
        | and q1 q2 =>
          dsimp only at he
          simp only [Bool.and_eq_true] at he
          simp only [evalFormulaBool, Bool.and_eq_true]
          exact ⟨ih (.not p1) q1 he.1 hp, ih (.not p1) q2 he.2 hp⟩
        | _ => dsimp only at he; cases he
      | and p1 p2 =>
        cases q with
        | tt => rfl
        | or q1 q2 =>
          dsimp only at he
          simp only [Bool.or_eq_true] at he
          simp only [evalFormulaBool, Bool.or_eq_true]
          rcases he with h1 | h2
          · exact Or.inl (ih (.and p1 p2) q1 h1 hp)
          · exact Or.inr (ih (.and p1 p2) q2 h2 hp)
        | and q1 q2 =>
          dsimp only at he
          simp only [Bool.and_eq_true] at he
          simp only [evalFormulaBool, Bool.and_eq_true]
          exact ⟨ih (.and p1 p2) q1 he.1 hp, ih (.and p1 p2) q2 he.2 hp⟩
        | _ =>
          dsimp only at he
          simp only [Bool.or_eq_true] at he
          simp only [evalFormulaBool, Bool.and_eq_true] at hp
          rcases he with h1 | h2
          · exact ih p1 _ h1 hp.1
          · exact ih p2 _ h2 hp.2
    · rw [← eqFormula_eq heq]; exact hp

theorem entails_sound (p q : Formula) (v : List Nat)
    (he : entails p q = true) (hp : evalFormulaBool p v = true) :
    evalFormulaBool q v = true :=
  entailsFuel_sound (formulaSize p + formulaSize q) p q v he hp

theorem indexOfBits_lt (bs : List Bool) : indexOfBits bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [indexOfBits]
  | cons b bs ih =>
    simp only [indexOfBits, List.length_cons, Nat.pow_succ]
    cases b <;> simp <;> omega

theorem bitsOfIndex_indexOfBits (bs : List Bool) :
    bitsOfIndex bs.length (indexOfBits bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons, bitsOfIndex, indexOfBits]
    cases b
    · simp only [Bool.toNat_false, Nat.zero_add]
      have hm : (2 * indexOfBits bs) % 2 = 0 := by omega
      have hd : (2 * indexOfBits bs) / 2 = indexOfBits bs := by omega
      simp [hm, hd, ih]
    · simp only [Bool.toNat_true]
      have hm : (1 + 2 * indexOfBits bs) % 2 = 1 := by omega
      have hd : (1 + 2 * indexOfBits bs) / 2 = indexOfBits bs := by omega
      simp [hm, hd, ih]

private theorem checkTransList_getD (cert : Cert) (f : Formula)
    (ts : List (List (List Bool) × Nat)) (start k : Nat)
    (hchk : checkTransList cert f start ts = true) (hk : k < ts.length) :
    let pair := ts.getD k ([], 0)
    let uList := pair.1
    let nextIdx := pair.2
    let b := bitsOfIndex cert.d (start + k)
    uList ≠ [] ∧
    (∀ u ∈ uList, u.length = cert.e) ∧
    nextIdx < cert.entries.length ∧
    entails (cert.entries.getD nextIdx defaultEntry).formula
            (bigOr (uList.map (fun u => stepFormula f (b ++ u)))) = true := by
  induction ts generalizing start k with
  | nil => simp at hk
  | cons hd tl ih =>
    rcases hd with ⟨uList, nextIdx⟩
    simp only [checkTransList, Bool.and_eq_true, Bool.not_eq_true',
               List.isEmpty_eq_false_iff_exists_mem, List.all_eq_true,
               beq_iff_eq, decide_eq_true_eq] at hchk
    rcases hchk with ⟨⟨⟨⟨hne, hall⟩, hlt⟩, hent⟩, hrest⟩
    cases k with
    | zero =>
      simp only [List.getD_cons_zero, Nat.add_zero]
      refine ⟨?_, hall, hlt, hent⟩
      intro hemp
      rcases hne with ⟨u, hu⟩
      rw [hemp] at hu
      exact absurd hu List.not_mem_nil
    | succ k' =>
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at hk
      have hrec := ih (start + 1) k' hrest hk
      have hadd : start + 1 + k' = start + (k' + 1) := by omega
      rw [hadd] at hrec
      simpa [List.getD_cons_succ] using hrec

private theorem pickWitnessU_sound (f : Formula) (b : List Bool) (x' y' : List Nat)
    (uList : List (List Bool)) (e : Nat)
    (hall : ∀ u ∈ uList, u.length = e)
    (hex : ∃ u ∈ uList, evalFormulaBool (stepFormula f (b ++ u)) (x' ++ y') = true) :
    let u := pickWitnessU f b x' y' uList
    u.length = e ∧ evalFormulaBool (stepFormula f (b ++ u)) (x' ++ y') = true := by
  induction uList with
  | nil =>
    rcases hex with ⟨_, hmem, _⟩
    exact absurd hmem List.not_mem_nil
  | cons u us ih =>
    simp only [pickWitnessU]
    split
    · rename_i hok
      exact ⟨hall u List.mem_cons_self, hok⟩
    · rename_i hno
      apply ih
      · intro v hv; exact hall v (List.mem_cons_of_mem u hv)
      · rcases hex with ⟨v, hmem, hok⟩
        rcases List.mem_cons.mp hmem with rfl | hv
        · exact absurd hok hno
        · exact ⟨v, hv, hok⟩

private theorem list_getD_mem {α : Type} (xs : List α) (i : Nat) (d : α) (hi : i < xs.length) :
    xs.getD i d ∈ xs := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ i' =>
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at hi
      exact List.mem_cons_of_mem x (ih i' hi)

/-- Master Inductive Soundness Theorem for `synthesizeFuel` -/
private theorem synthesizeFuel_sound (fuel : Nat) (cert : Cert) (hc : checkCert cert = true)
    (stIdx : Nat) (hst : stIdx < cert.entries.length)
    (x : List Nat) (hx : x.length = cert.d) (hfuel : vecSum x ≤ fuel) :
    (synthesizeFuel fuel cert stIdx x).length = cert.e ∧
      evalFormulaBool (cert.entries.getD stIdx defaultEntry).formula
        (x ++ synthesizeFuel fuel cert stIdx x) = true := by
  induction fuel generalizing stIdx x with
  | zero =>
    have hz : vecSum x = 0 := by omega
    have hc_all : ∀ entry ∈ cert.entries, checkEntry cert entry = true := by
      simp only [checkCert, Bool.and_eq_true, List.all_eq_true] at hc
      exact hc.2
    have hmem : cert.entries.getD stIdx defaultEntry ∈ cert.entries :=
      list_getD_mem cert.entries stIdx defaultEntry hst
    have hentry := hc_all _ hmem
    simp only [checkEntry, Bool.and_eq_true, beq_iff_eq] at hentry
    rcases hentry with ⟨⟨⟨hlenY, hbase⟩, _⟩, _⟩
    simp only [synthesizeFuel]
    have hxrep : x = List.replicate cert.d 0 := by
      rw [← hx]; exact (vecSum_eq_zero_iff x).mp hz
    rw [hxrep]
    exact ⟨hlenY, hbase⟩
  | succ fuel ih =>
    have hc_all : ∀ entry ∈ cert.entries, checkEntry cert entry = true := by
      simp only [checkCert, Bool.and_eq_true, List.all_eq_true] at hc
      exact hc.2
    have hmem : cert.entries.getD stIdx defaultEntry ∈ cert.entries :=
      list_getD_mem cert.entries stIdx defaultEntry hst
    have hentry := hc_all _ hmem
    simp only [checkEntry, Bool.and_eq_true, beq_iff_eq] at hentry
    rcases hentry with ⟨⟨⟨hlenY, hbase⟩, hlenT⟩, htrans⟩
    by_cases hz : vecSum x = 0
    · simp only [synthesizeFuel, hz, beq_self_eq_true, ↓reduceIte]
      have hxrep : x = List.replicate cert.d 0 := by
        rw [← hx]; exact (vecSum_eq_zero_iff x).mp hz
      rw [hxrep]
      exact ⟨hlenY, hbase⟩
    · have hzb : (vecSum x == 0) = false := by simp [hz]
      simp only [synthesizeFuel, hzb, Bool.false_eq_true, ↓reduceIte]
      let entry := cert.entries.getD stIdx defaultEntry
      let b := vecMod2Bits x
      let x' := vecDiv2 x
      let idx := indexOfBits b
      let pair := entry.trans.getD idx ([], 0)
      let y' := synthesizeFuel fuel cert pair.2 x'
      let u := pickWitnessU entry.formula b x' y' pair.1
      have hb_len : b.length = cert.d := by rw [vecMod2Bits_length, hx]
      have hx'_len : x'.length = cert.d := by rw [vecDiv2_length, hx]
      have hidx_lt : idx < entry.trans.length := by
        rw [hlenT, ← hb_len]
        exact indexOfBits_lt b
      have hstep_chk := checkTransList_getD cert entry.formula entry.trans 0 idx htrans hidx_lt
      simp only [Nat.zero_add] at hstep_chk
      have hbits_eq : bitsOfIndex cert.d idx = b := by
        rw [← hb_len]
        exact bitsOfIndex_indexOfBits b
      rw [hbits_eq] at hstep_chk
      rcases hstep_chk with ⟨_, hallU, hnext_lt, hentails⟩
      have hlt_sum : vecSum x' ≤ fuel := by
        show vecSum (vecDiv2 x) ≤ fuel
        have hlt := vecSum_vecDiv2_lt x hz
        omega
      have hih := ih pair.2 hnext_lt x' hx'_len hlt_sum
      have hstepped_true :
          evalFormulaBool (bigOr (pair.1.map (fun w => stepFormula entry.formula (b ++ w))))
                          (x' ++ y') = true :=
        entails_sound _ _ (x' ++ y') hentails hih.2
      rw [evalFormulaBool_bigOr_iff] at hstepped_true
      have hex : ∃ w ∈ pair.1,
          evalFormulaBool (stepFormula entry.formula (b ++ w)) (x' ++ y') = true := by
        rcases hstepped_true with ⟨g, hg, hgv⟩
        rw [List.mem_map] at hg
        rcases hg with ⟨w, hw, rfl⟩
        exact ⟨w, hw, hgv⟩
      have hpick := pickWitnessU_sound entry.formula b x' y' pair.1 cert.e hallU hex
      have hy_len : (vecStep y' u).length = cert.e := by
        have hlen_eq : y'.length = u.length := hih.1.trans hpick.1.symm
        rw [vecStep_length y' u hlen_eq, hih.1]
      have hlen_xy : (x' ++ y').length = (b ++ u).length := by
        have h1 : y'.length = u.length := hih.1.trans hpick.1.symm
        simp [hx'_len, hb_len, h1]
      have heval_step := evalFormulaBool_stepFormula entry.formula (x' ++ y') (b ++ u) hlen_xy
      have hpick2 : evalFormulaBool entry.formula (vecStep (x' ++ y') (b ++ u)) = true := by
        rw [← heval_step]
        exact hpick.2
      have hvec_eq : vecStep (x' ++ y') (b ++ u) = x ++ vecStep y' u := by
        rw [vecStep_append x' y' b u (by rw [hx'_len, hb_len]),
            vecStep_vecDiv2_vecMod2Bits x]
      rw [hvec_eq] at hpick2
      exact ⟨hy_len, hpick2⟩

theorem synthesizeFrom_sound (cert : Cert) (hc : checkCert cert = true)
    (stIdx : Nat) (hst : stIdx < cert.entries.length)
    (x : List Nat) (hx : x.length = cert.d) :
    (synthesizeFrom cert stIdx x).length = cert.e ∧
      evalFormulaBool (cert.entries.getD stIdx defaultEntry).formula
        (x ++ synthesizeFrom cert stIdx x) = true :=
  synthesizeFuel_sound (vecSum x) cert hc stIdx hst x hx (Nat.le_refl _)

/-- Master Constructive Skolem Theorem -/
theorem synthesizeY_sound (cert : Cert) (hc : checkCert cert = true)
    (x : List Nat) (hx : x.length = cert.d) :
    (synthesizeY cert x).length = cert.e ∧
      evalFormulaBool (cert.entries.getD 0 defaultEntry).formula (x ++ synthesizeY cert x) = true := by
  have hpos : 0 < cert.entries.length := by
    simp only [checkCert, Bool.and_eq_true, decide_eq_true_eq] at hc
    exact hc.1
  exact synthesizeFrom_sound cert hc 0 hpos x hx

/-- Master Existential Soundness Meta-Theorem (`∀ x, ∃ y, Φ(x, y)`) -/
theorem cert_sound (cert : Cert) (hc : checkCert cert = true) :
    ∀ x : List Nat, x.length = cert.d →
      ∃ y : List Nat, y.length = cert.e ∧
        evalFormulaBool (cert.entries.getD 0 defaultEntry).formula (x ++ y) = true := by
  intro x hx
  exact ⟨synthesizeY cert x, synthesizeY_sound cert hc x hx⟩

/-- Master Universal Soundness Meta-Theorem (`∀ x, Φ(x)` when `e = 0`) -/
theorem cert_sound_univ (cert : Cert) (hc : checkCert cert = true) (he : cert.e = 0) :
    ∀ x : List Nat, x.length = cert.d →
      evalFormulaBool (cert.entries.getD 0 defaultEntry).formula x = true := by
  intro x hx
  rcases cert_sound cert hc x hx with ⟨y, hylen, hok⟩
  have hy0 : y = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst hy0
  simpa using hok

/-! ### Convenience Helpers for Readable Formula Construction -/

def natAff (cs : List Nat) (c : Nat := 0) : NatAff := { coeffs := cs, carry := c }
def intAff (cs : List Int) (rhs : Int) : IntAff := { coeffs := cs, rhs := rhs }

def fLinLe (cs : List Int) (rhs : Int) : Formula := .atom (.linLe (intAff cs rhs))
def fLinEq (cs : List Int) (rhs : Int) : Formula := .atom (.linEq (intAff cs rhs))
def fModEq (cs : List Int) (m r : Nat) : Formula := .atom (.modEq cs m r)
def fDisj (t1 t2 : NatAff) : Formula := .atom (.bitRel4 maskAndZero t1 t2 (natAff []) (natAff []))
def fXor3Zero (t1 t2 t3 : NatAff) : Formula := .atom (.bitRel4 maskXor3Eq0 t1 t2 t3 (natAff []))
def fCarryLe (t1 t2 : NatAff) (cin : Bool) (k : Nat) : Formula := .atom (.carryLe t1 t2 cin k)
def fPopMod (terms : List (Int × NatAff)) (m r : Nat) : Formula := .atom (.popMod terms m r)



/-! ## Section 6: Finite Pure-Data Residue-Carry Witness Certificates (20 Theorems) -/

def cert_ternary_k0_r0 : Cert := {
  d := 1,
  e := 1,
  entries := [
    { formula := .and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 5)), baseY := [0], trans := [([[false], [true]], 1), ([[false]], 2)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 2))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 1))), baseY := [0], trans := [([[false], [true]], 3), ([[false]], 4)] },
    { formula := .and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 5)), baseY := [1], trans := [([[false], [true]], 5), ([[false]], 0)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 1))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] (-1)))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 0)))), baseY := [0], trans := [([[false], [true]], 6), ([[false]], 7)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 3))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 3))), baseY := [0], trans := [([[false], [true]], 8), ([[false]], 9)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 1))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 2))), baseY := [0], trans := [([[false], [true]], 10), ([[false]], 11)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 0))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 0))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] (-1))))), baseY := [0], trans := [([[false], [true]], 12), ([[false]], 13)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 2))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 3))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 2)))), baseY := [0], trans := [([[false], [true]], 14), ([[false]], 15)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 1))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 0))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 1)))), baseY := [0], trans := [([[false], [true]], 16), ([[false]], 17)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 4))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 4))), baseY := [0], trans := [([[false], [true]], 18), ([[false]], 9)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 0))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 1))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] (-1))))), baseY := [0], trans := [([[false], [true]], 12), ([[false]], 19)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 3))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 3))), baseY := [1], trans := [([[false], [true]], 20), ([[false]], 21)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 0))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] (-1)))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 0)))), baseY := [0], trans := [([[false], [true]], 6), ([[false]], 13)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 2))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 2))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 2)))), baseY := [0], trans := [([[false], [true]], 14), ([[false]], 22)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 1))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 1))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 1)))), baseY := [0], trans := [([[false], [true]], 16), ([[false]], 22)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 4))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 3))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 3)))), baseY := [0], trans := [([[false], [true]], 23), ([[false]], 24)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 0))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 0))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 0)))), baseY := [0], trans := [([[false], [true]], 16), ([[false]], 13)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 2))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 3))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 3)))), baseY := [0], trans := [([[false], [true]], 14), ([[false]], 25)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 2))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 0))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 2)))), baseY := [0], trans := [([[false], [true]], 26), ([[false]], 17)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 3))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 2))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 2)))), baseY := [0], trans := [([[false], [true]], 14), ([[false]], 27)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 0))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 1))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 1)))), baseY := [0], trans := [([[false], [true]], 16), ([[false]], 28)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 4))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 4))), baseY := [0], trans := [([[false], [true]], 29), ([[false]], 30)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 3))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 3))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 3)))), baseY := [0], trans := [([[false], [true]], 14), ([[false]], 24)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 2))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 1))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 1)))), baseY := [0], trans := [([[false], [true]], 31), ([[false]], 22)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 4))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 4))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 4)))), baseY := [0], trans := [([[false], [true]], 13), ([[false]], 24)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 4))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 3))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 4)))), baseY := [0], trans := [([[false], [true]], 32), ([[false]], 24)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 1))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 1))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 0)))), baseY := [0], trans := [([[false], [true]], 16), ([[false]], 33)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 3))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 4))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 3)))), baseY := [0], trans := [([[false], [true]], 34), ([[false]], 24)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 3))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 2))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 3)))), baseY := [0], trans := [([[false], [true]], 14), ([[false]], 35)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 2))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 2))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 0)))), baseY := [0], trans := [([[false], [true]], 8), ([[false]], 33)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 4))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 4))), baseY := [1], trans := [([[false], [true]], 36), ([[false]], 21)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 1))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 0))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 0)))), baseY := [0], trans := [([[false], [true]], 16), ([[false]], 7)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 2))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 2))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 1)))), baseY := [0], trans := [([[false], [true]], 8), ([[false]], 22)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 3))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 3))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 2)))), baseY := [0], trans := [([[false], [true]], 14), ([[false]], 37)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 1))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 1))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 2)))), baseY := [0], trans := [([[false], [true]], 38), ([[false]], 22)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 3))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 4))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 4)))), baseY := [0], trans := [([[false], [true]], 39), ([[false]], 24)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 0))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 2))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 2)))), baseY := [0], trans := [([[false], [true]], 20), ([[false]], 28)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 4))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 4))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 3)))), baseY := [0], trans := [([[false], [true]], 40), ([[false]], 24)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 0))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 1))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 0)))), baseY := [0], trans := [([[false], [true]], 16), ([[false]], 19)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 1))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 2))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 2)))), baseY := [0], trans := [([[false], [true]], 20), ([[false]], 22)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 2))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 1))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 2)))), baseY := [0], trans := [([[false], [true]], 26), ([[false]], 22)] }
  ]
}

def cert_ternary_k0_r1 : Cert := {
  d := 1,
  e := 1,
  entries := [
    { formula := .and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 5)), baseY := [1], trans := [([[false], [true]], 1), ([[false]], 2)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 1))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 2))), baseY := [0], trans := [([[false], [true]], 3), ([[false]], 4)] },
    { formula := .and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 5)), baseY := [0], trans := [([[false], [true]], 5), ([[false]], 0)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 0))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 1))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] (-1))))), baseY := [0], trans := [([[false], [true]], 6), ([[false]], 7)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 3))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 3))), baseY := [1], trans := [([[false], [true]], 8), ([[false]], 9)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 2))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 1))), baseY := [0], trans := [([[false], [true]], 10), ([[false]], 11)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 0))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] (-1)))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 0)))), baseY := [0], trans := [([[false], [true]], 12), ([[false]], 13)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 3))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 2))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 2)))), baseY := [0], trans := [([[false], [true]], 14), ([[false]], 15)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 0))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 1))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 1)))), baseY := [0], trans := [([[false], [true]], 16), ([[false]], 17)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 4))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 4))), baseY := [0], trans := [([[false], [true]], 18), ([[false]], 19)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 1))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] (-1)))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 0)))), baseY := [0], trans := [([[false], [true]], 12), ([[false]], 20)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 3))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 3))), baseY := [0], trans := [([[false], [true]], 21), ([[false]], 22)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 0))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 0))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] (-1))))), baseY := [0], trans := [([[false], [true]], 6), ([[false]], 13)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 2))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 2))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 2)))), baseY := [0], trans := [([[false], [true]], 14), ([[false]], 23)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 1))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 1))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 1)))), baseY := [0], trans := [([[false], [true]], 16), ([[false]], 23)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 3))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 4))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 3)))), baseY := [0], trans := [([[false], [true]], 24), ([[false]], 25)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 0))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 0))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 0)))), baseY := [0], trans := [([[false], [true]], 16), ([[false]], 13)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 3))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 2))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 3)))), baseY := [0], trans := [([[false], [true]], 14), ([[false]], 26)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 2))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 2))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 0)))), baseY := [0], trans := [([[false], [true]], 21), ([[false]], 27)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 4))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 4))), baseY := [1], trans := [([[false], [true]], 28), ([[false]], 9)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 2))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 3))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 2)))), baseY := [0], trans := [([[false], [true]], 14), ([[false]], 29)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 1))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 0))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 1)))), baseY := [0], trans := [([[false], [true]], 16), ([[false]], 30)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 4))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 4))), baseY := [0], trans := [([[false], [true]], 31), ([[false]], 22)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 3))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 3))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 3)))), baseY := [0], trans := [([[false], [true]], 14), ([[false]], 25)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 1))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 1))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 2)))), baseY := [0], trans := [([[false], [true]], 32), ([[false]], 23)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 4))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 4))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 4)))), baseY := [0], trans := [([[false], [true]], 13), ([[false]], 25)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 3))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 4))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 4)))), baseY := [0], trans := [([[false], [true]], 33), ([[false]], 25)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 3))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 3))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 2)))), baseY := [0], trans := [([[false], [true]], 14), ([[false]], 34)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 0))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 2))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 2)))), baseY := [0], trans := [([[false], [true]], 8), ([[false]], 17)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 4))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 3))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 3)))), baseY := [0], trans := [([[false], [true]], 35), ([[false]], 25)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 2))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 3))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 3)))), baseY := [0], trans := [([[false], [true]], 14), ([[false]], 36)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 2))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 0))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 2)))), baseY := [0], trans := [([[false], [true]], 37), ([[false]], 30)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 0))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 1))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 0)))), baseY := [0], trans := [([[false], [true]], 16), ([[false]], 7)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 1))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 2))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 2)))), baseY := [0], trans := [([[false], [true]], 8), ([[false]], 23)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 4))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 4))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 3)))), baseY := [0], trans := [([[false], [true]], 38), ([[false]], 25)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 2))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 1))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 1)))), baseY := [0], trans := [([[false], [true]], 39), ([[false]], 23)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 4))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 3))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 4)))), baseY := [0], trans := [([[false], [true]], 40), ([[false]], 25)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 1))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 1))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 0)))), baseY := [0], trans := [([[false], [true]], 16), ([[false]], 27)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 2))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 1))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 2)))), baseY := [0], trans := [([[false], [true]], 37), ([[false]], 23)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 1))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 0))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 0)))), baseY := [0], trans := [([[false], [true]], 16), ([[false]], 20)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-5, 3] 2))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-5, 3] 2))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-5, 3] 1)))), baseY := [0], trans := [([[false], [true]], 21), ([[false]], 23)] }
  ]
}

def cert_ternary_k0_r2 : Cert := {
  d := 1,
  e := 1,
  entries := [
    { formula := .and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-2, 1] 2)), baseY := [2], trans := [([[false], [true]], 1), ([[false]], 0)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-2, 1] 1))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-2, 1] 0))), baseY := [1], trans := [([[false], [true]], 2), ([[false]], 3)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-2, 1] 0))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-2, 1] 0))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-2, 1] 0)))), baseY := [0], trans := [([[false], [true]], 2), ([[false]], 4)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-2, 1] 1))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-2, 1] 1))), baseY := [0], trans := [([[false], [true]], 2), ([[false]], 5)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 0) (fLinLe [-2, 1] 1))) (.or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-2, 1] 1))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-2, 1] 1)))), baseY := [0], trans := [([[false], [true]], 2), ([[false]], 4)] },
    { formula := .or (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 1) (fLinLe [-2, 1] 1))) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (.and (fModEq [1, 1] 3 2) (fLinLe [-2, 1] 1))), baseY := [1], trans := [([[false], [true]], 2), ([[false]], 3)] }
  ]
}

def cert_ternary_k1_r0 : Cert := {
  d := 1,
  e := 1,
  entries := [
    { formula := .and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 1)), baseY := [0], trans := [([[false], [true]], 1), ([[false], [true]], 2)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))), baseY := [0], trans := [([[false], [true]], 3), ([[false], [true]], 4)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 1))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0))), baseY := [1], trans := [([[false], [true]], 5), ([[false], [true]], 6)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0)))), baseY := [0], trans := [([[false], [true]], 7), ([[false], [true]], 8)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0))))), baseY := [0], trans := [([[false], [true]], 9), ([[false], [true]], 4)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0)))), baseY := [0], trans := [([[false], [true]], 10), ([[false], [true]], 11)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 1))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))), baseY := [0], trans := [([[false], [true]], 12), ([[false], [true]], 2)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] (-1))))), baseY := [0], trans := [([[false], [true]], 3), ([[false], [true]], 13)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0))))))), baseY := [0], trans := [([[false], [true]], 14), ([[false], [true]], 15)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0))))), baseY := [0], trans := [([[false], [true]], 10), ([[false], [true]], 8)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] (-1)))))), baseY := [0], trans := [([[false], [true]], 9), ([[false], [true]], 13)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0)))))), baseY := [0], trans := [([[false], [true]], 16), ([[false], [true]], 17)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0)))), baseY := [0], trans := [([[false], [true]], 9), ([[false], [true]], 18)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0))))))), baseY := [0], trans := [([[false], [true]], 14), ([[false], [true]], 15)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0)))), baseY := [0], trans := [([[false], [true]], 14), ([[false], [true]], 15)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0))))))), baseY := [0], trans := [([[false], [true]], 14), ([[false], [true]], 15)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0))))), baseY := [0], trans := [([[false], [true]], 16), ([[false], [true]], 19)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0)))))), baseY := [0], trans := [([[false], [true]], 10), ([[false], [true]], 11)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0)))))), baseY := [0], trans := [([[false], [true]], 9), ([[false], [true]], 18)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] (-1)))))))), baseY := [0], trans := [([[false], [true]], 14), ([[false], [true]], 15)] }
  ]
}

def cert_ternary_k1_r1 : Cert := {
  d := 1,
  e := 1,
  entries := [
    { formula := .and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 1)), baseY := [1], trans := [([[false], [true]], 1), ([[false], [true]], 2)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0))), baseY := [0], trans := [([[false], [true]], 3), ([[false], [true]], 4)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 1))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))), baseY := [0], trans := [([[false], [true]], 5), ([[false], [true]], 6)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] (-1))))), baseY := [0], trans := [([[false], [true]], 7), ([[false], [true]], 8)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0))))), baseY := [0], trans := [([[false], [true]], 9), ([[false], [true]], 10)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0)))), baseY := [0], trans := [([[false], [true]], 11), ([[false], [true]], 12)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 1))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0))), baseY := [1], trans := [([[false], [true]], 13), ([[false], [true]], 2)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0)))), baseY := [0], trans := [([[false], [true]], 3), ([[false], [true]], 14)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0))))))), baseY := [0], trans := [([[false], [true]], 15), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0))))), baseY := [0], trans := [([[false], [true]], 9), ([[false], [true]], 17)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0))))), baseY := [0], trans := [([[false], [true]], 18), ([[false], [true]], 4)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0))))), baseY := [0], trans := [([[false], [true]], 18), ([[false], [true]], 14)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0)))))), baseY := [0], trans := [([[false], [true]], 11), ([[false], [true]], 12)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0)))), baseY := [0], trans := [([[false], [true]], 18), ([[false], [true]], 19)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0))))))), baseY := [0], trans := [([[false], [true]], 15), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0)))), baseY := [0], trans := [([[false], [true]], 15), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0))))))), baseY := [0], trans := [([[false], [true]], 15), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] (-1)))))))), baseY := [0], trans := [([[false], [true]], 15), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] (-1)))))), baseY := [0], trans := [([[false], [true]], 11), ([[false], [true]], 8)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0)))))), baseY := [0], trans := [([[false], [true]], 9), ([[false], [true]], 20)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 1] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 1] 0)))))), baseY := [0], trans := [([[false], [true]], 18), ([[false], [true]], 19)] }
  ]
}

def cert_ternary_k1_r2 : Cert := {
  d := 1,
  e := 1,
  entries := [
    { formula := .and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 4)), baseY := [2], trans := [([[false], [true]], 1), ([[false], [true]], 2)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 2))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 1))), baseY := [1], trans := [([[false], [true]], 3), ([[false], [true]], 4)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 1))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 2))), baseY := [0], trans := [([[false], [true]], 5), ([[false], [true]], 6)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 1)))), baseY := [0], trans := [([[false], [true]], 7), ([[false], [true]], 8)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 1))))), baseY := [0], trans := [([[false], [true]], 9), ([[false], [true]], 10)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 1))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0)))), baseY := [0], trans := [([[false], [true]], 11), ([[false], [true]], 12)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 1))), baseY := [0], trans := [([[false], [true]], 13), ([[false], [true]], 6)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0)))), baseY := [0], trans := [([[false], [true]], 7), ([[false], [true]], 14)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 1))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] (-1)))))))), baseY := [0], trans := [([[false], [true]], 7), ([[false], [true]], 8)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] (-1)))))), baseY := [0], trans := [([[false], [true]], 15), ([[false], [true]], 14)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 1))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0))))), baseY := [0], trans := [([[false], [true]], 11), ([[false], [true]], 4)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0))))), baseY := [0], trans := [([[false], [true]], 11), ([[false], [true]], 14)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0)))))), baseY := [0], trans := [([[false], [true]], 9), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] (-1))))), baseY := [0], trans := [([[false], [true]], 17), ([[false], [true]], 18)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] (-1)))))))), baseY := [0], trans := [([[false], [true]], 7), ([[false], [true]], 14)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0))))), baseY := [0], trans := [([[false], [true]], 9), ([[false], [true]], 14)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0)))))), baseY := [0], trans := [([[false], [true]], 11), ([[false], [true]], 12)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0))))), baseY := [0], trans := [([[false], [true]], 19), ([[false], [true]], 14)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0)))))), baseY := [0], trans := [([[false], [true]], 9), ([[false], [true]], 20)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] (-1)))))), baseY := [0], trans := [([[false], [true]], 17), ([[false], [true]], 14)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] (-1))))))), baseY := [0], trans := [([[false], [true]], 11), ([[false], [true]], 18)] }
  ]
}

def cert_ternary_k2_r0 : Cert := {
  d := 1,
  e := 1,
  entries := [
    { formula := .and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 7)), baseY := [0], trans := [([[false], [true]], 1), ([[false], [true]], 2)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 3))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 1))), baseY := [0], trans := [([[false], [true]], 3), ([[false], [true]], 4)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 4))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 2))), baseY := [1], trans := [([[false], [true]], 5), ([[false], [true]], 6)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0)))), baseY := [0], trans := [([[false], [true]], 7), ([[false], [true]], 8)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 2))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))))), baseY := [0], trans := [([[false], [true]], 9), ([[false], [true]], 10)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 2))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))))), baseY := [0], trans := [([[false], [true]], 11), ([[false], [true]], 12)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 2))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 1))))), baseY := [0], trans := [([[false], [true]], 13), ([[false], [true]], 14)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1))))), baseY := [0], trans := [([[false], [true]], 15), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))))))), baseY := [0], trans := [([[false], [true]], 17), ([[false], [true]], 18)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 1))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2)))))))), baseY := [0], trans := [([[false], [true]], 19), ([[false], [true]], 20)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))))))), baseY := [0], trans := [([[false], [true]], 21), ([[false], [true]], 10)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))))), baseY := [0], trans := [([[false], [true]], 22), ([[false], [true]], 23)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 1))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2)))))))), baseY := [0], trans := [([[false], [true]], 24), ([[false], [true]], 25)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0)))))), baseY := [0], trans := [([[false], [true]], 26), ([[false], [true]], 27)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))))), baseY := [0], trans := [([[false], [true]], 28), ([[false], [true]], 29)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0)))), baseY := [0], trans := [([[false], [true]], 7), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2)))))))), baseY := [0], trans := [([[false], [true]], 17), ([[false], [true]], 30)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-3)))))))), baseY := [0], trans := [([[false], [true]], 31), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2)))))))))), baseY := [0], trans := [([[false], [true]], 17), ([[false], [true]], 32)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))))), baseY := [0], trans := [([[false], [true]], 22), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 1))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2)))))))))), baseY := [0], trans := [([[false], [true]], 33), ([[false], [true]], 34)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-3))))))))), baseY := [0], trans := [([[false], [true]], 35), ([[false], [true]], 36)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))))), baseY := [0], trans := [([[false], [true]], 19), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2)))))))), baseY := [0], trans := [([[false], [true]], 17), ([[false], [true]], 32)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-3)))))))), baseY := [0], trans := [([[false], [true]], 37), ([[false], [true]], 38)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 1))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1))))))))), baseY := [0], trans := [([[false], [true]], 39), ([[false], [true]], 40)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1))))))), baseY := [0], trans := [([[false], [true]], 41), ([[false], [true]], 36)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))))))), baseY := [0], trans := [([[false], [true]], 42), ([[false], [true]], 43)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-3))))))), baseY := [0], trans := [([[false], [true]], 44), ([[false], [true]], 45)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))))), baseY := [0], trans := [([[false], [true]], 46), ([[false], [true]], 14)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2))))))))))), baseY := [0], trans := [([[false], [true]], 17), ([[false], [true]], 30)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0)))), baseY := [0], trans := [([[false], [true]], 31), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))))))))), baseY := [0], trans := [([[false], [true]], 17), ([[false], [true]], 18)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-4)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-3))))))))), baseY := [0], trans := [([[false], [true]], 37), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2)))))))))), baseY := [0], trans := [([[false], [true]], 17), ([[false], [true]], 34)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))))), baseY := [0], trans := [([[false], [true]], 47), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2)))))))))), baseY := [0], trans := [([[false], [true]], 33), ([[false], [true]], 30)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))))), baseY := [0], trans := [([[false], [true]], 37), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-3)))))))))), baseY := [0], trans := [([[false], [true]], 48), ([[false], [true]], 30)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2)))))))), baseY := [0], trans := [([[false], [true]], 22), ([[false], [true]], 49)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 1))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2)))))))), baseY := [0], trans := [([[false], [true]], 24), ([[false], [true]], 25)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1))))))), baseY := [0], trans := [([[false], [true]], 50), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-3)))))))), baseY := [0], trans := [([[false], [true]], 19), ([[false], [true]], 36)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2))))))))), baseY := [0], trans := [([[false], [true]], 42), ([[false], [true]], 51)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2))))))), baseY := [0], trans := [([[false], [true]], 52), ([[false], [true]], 49)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-3))))))))), baseY := [0], trans := [([[false], [true]], 53), ([[false], [true]], 54)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1))))))), baseY := [0], trans := [([[false], [true]], 55), ([[false], [true]], 56)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))))), baseY := [0], trans := [([[false], [true]], 35), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-4))))))))), baseY := [0], trans := [([[false], [true]], 22), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2)))))))))), baseY := [0], trans := [([[false], [true]], 57), ([[false], [true]], 30)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1))))))), baseY := [0], trans := [([[false], [true]], 41), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))))))), baseY := [0], trans := [([[false], [true]], 42), ([[false], [true]], 43)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))))), baseY := [0], trans := [([[false], [true]], 58), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-4))))))))), baseY := [0], trans := [([[false], [true]], 59), ([[false], [true]], 38)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1))))))))), baseY := [0], trans := [([[false], [true]], 39), ([[false], [true]], 60)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1))))))), baseY := [0], trans := [([[false], [true]], 61), ([[false], [true]], 36)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2))))))))), baseY := [0], trans := [([[false], [true]], 62), ([[false], [true]], 63)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-4)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-3))))))))), baseY := [0], trans := [([[false], [true]], 19), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))))), baseY := [0], trans := [([[false], [true]], 52), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0)))))), baseY := [0], trans := [([[false], [true]], 64), ([[false], [true]], 38)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2))))))))), baseY := [0], trans := [([[false], [true]], 24), ([[false], [true]], 54)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))))), baseY := [0], trans := [([[false], [true]], 65), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-4)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-3))))))))), baseY := [0], trans := [([[false], [true]], 66), ([[false], [true]], 36)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2))))))))), baseY := [0], trans := [([[false], [true]], 42), ([[false], [true]], 63)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1))))))), baseY := [0], trans := [([[false], [true]], 67), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))))), baseY := [0], trans := [([[false], [true]], 61), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2))))))), baseY := [0], trans := [([[false], [true]], 68), ([[false], [true]], 49)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0)))))), baseY := [0], trans := [([[false], [true]], 64), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0)))))), baseY := [0], trans := [([[false], [true]], 69), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1))))))), baseY := [0], trans := [([[false], [true]], 68), ([[false], [true]], 16)] }
  ]
}

def cert_ternary_k2_r1 : Cert := {
  d := 1,
  e := 1,
  entries := [
    { formula := .and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 6)), baseY := [1], trans := [([[false], [true]], 1), ([[false], [true]], 2)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 1))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 3))), baseY := [0], trans := [([[false], [true]], 3), ([[false], [true]], 4)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 3))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 1))), baseY := [0], trans := [([[false], [true]], 5), ([[false], [true]], 6)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 1))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1))))), baseY := [0], trans := [([[false], [true]], 7), ([[false], [true]], 8)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 2))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))))), baseY := [0], trans := [([[false], [true]], 9), ([[false], [true]], 10)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))))), baseY := [0], trans := [([[false], [true]], 11), ([[false], [true]], 12)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 2))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))))), baseY := [0], trans := [([[false], [true]], 13), ([[false], [true]], 14)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0)))), baseY := [0], trans := [([[false], [true]], 15), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2)))))))), baseY := [0], trans := [([[false], [true]], 17), ([[false], [true]], 18)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-3)))))))), baseY := [0], trans := [([[false], [true]], 19), ([[false], [true]], 20)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 1))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))))))), baseY := [0], trans := [([[false], [true]], 21), ([[false], [true]], 22)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))))), baseY := [0], trans := [([[false], [true]], 23), ([[false], [true]], 24)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))))))), baseY := [0], trans := [([[false], [true]], 25), ([[false], [true]], 26)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 1))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2))))))), baseY := [0], trans := [([[false], [true]], 27), ([[false], [true]], 28)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))))), baseY := [0], trans := [([[false], [true]], 29), ([[false], [true]], 30)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1))))), baseY := [0], trans := [([[false], [true]], 7), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2)))))))), baseY := [0], trans := [([[false], [true]], 17), ([[false], [true]], 31)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-3)))))))), baseY := [0], trans := [([[false], [true]], 32), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))))))))), baseY := [0], trans := [([[false], [true]], 17), ([[false], [true]], 33)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))))), baseY := [0], trans := [([[false], [true]], 19), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-3)))))))))), baseY := [0], trans := [([[false], [true]], 34), ([[false], [true]], 18)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2))))))))), baseY := [0], trans := [([[false], [true]], 35), ([[false], [true]], 36)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 1))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))))))), baseY := [0], trans := [([[false], [true]], 37), ([[false], [true]], 10)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))))), baseY := [0], trans := [([[false], [true]], 38), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2)))))))))), baseY := [0], trans := [([[false], [true]], 39), ([[false], [true]], 31)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-3)))))))), baseY := [0], trans := [([[false], [true]], 40), ([[false], [true]], 24)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2))))))))), baseY := [0], trans := [([[false], [true]], 25), ([[false], [true]], 41)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2))))))), baseY := [0], trans := [([[false], [true]], 42), ([[false], [true]], 36)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 1))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2)))))))), baseY := [0], trans := [([[false], [true]], 43), ([[false], [true]], 44)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1))))))), baseY := [0], trans := [([[false], [true]], 45), ([[false], [true]], 46)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))))), baseY := [0], trans := [([[false], [true]], 47), ([[false], [true]], 14)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2))))))))))), baseY := [0], trans := [([[false], [true]], 17), ([[false], [true]], 31)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0)))), baseY := [0], trans := [([[false], [true]], 32), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2)))))))))), baseY := [0], trans := [([[false], [true]], 17), ([[false], [true]], 18)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-4))))))))), baseY := [0], trans := [([[false], [true]], 48), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))))), baseY := [0], trans := [([[false], [true]], 49), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2)))))))))), baseY := [0], trans := [([[false], [true]], 50), ([[false], [true]], 31)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-3))))))))), baseY := [0], trans := [([[false], [true]], 51), ([[false], [true]], 52)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))))), baseY := [0], trans := [([[false], [true]], 23), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-4)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-3))))))))), baseY := [0], trans := [([[false], [true]], 19), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))))), baseY := [0], trans := [([[false], [true]], 48), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))))))), baseY := [0], trans := [([[false], [true]], 25), ([[false], [true]], 26)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0)))))), baseY := [0], trans := [([[false], [true]], 53), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-3)))))))), baseY := [0], trans := [([[false], [true]], 19), ([[false], [true]], 52)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 1))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1))))))))), baseY := [0], trans := [([[false], [true]], 54), ([[false], [true]], 55)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1))))))), baseY := [0], trans := [([[false], [true]], 56), ([[false], [true]], 24)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2))))))))), baseY := [0], trans := [([[false], [true]], 57), ([[false], [true]], 58)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-3))))))), baseY := [0], trans := [([[false], [true]], 59), ([[false], [true]], 60)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))))), baseY := [0], trans := [([[false], [true]], 40), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))))), baseY := [0], trans := [([[false], [true]], 35), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-4)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-3))))))))), baseY := [0], trans := [([[false], [true]], 40), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))))), baseY := [0], trans := [([[false], [true]], 51), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-3)))))))))), baseY := [0], trans := [([[false], [true]], 34), ([[false], [true]], 31)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1))))))), baseY := [0], trans := [([[false], [true]], 42), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2)))))))), baseY := [0], trans := [([[false], [true]], 48), ([[false], [true]], 36)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 1))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2)))))))), baseY := [0], trans := [([[false], [true]], 43), ([[false], [true]], 44)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))))), baseY := [0], trans := [([[false], [true]], 61), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-4)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-3))))))))), baseY := [0], trans := [([[false], [true]], 27), ([[false], [true]], 24)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2))))))))), baseY := [0], trans := [([[false], [true]], 25), ([[false], [true]], 58)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2))))))), baseY := [0], trans := [([[false], [true]], 62), ([[false], [true]], 36)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-3))))))))), baseY := [0], trans := [([[false], [true]], 63), ([[false], [true]], 64)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))))), baseY := [0], trans := [([[false], [true]], 56), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))))), baseY := [0], trans := [([[false], [true]], 65), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-3)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-4))))))))), baseY := [0], trans := [([[false], [true]], 66), ([[false], [true]], 52)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1))))))))), baseY := [0], trans := [([[false], [true]], 54), ([[false], [true]], 67)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1)))))), baseY := [0], trans := [([[false], [true]], 62), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0)))))), baseY := [0], trans := [([[false], [true]], 68), ([[false], [true]], 52)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-2))))))))), baseY := [0], trans := [([[false], [true]], 43), ([[false], [true]], 64)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] (-1))))))), baseY := [0], trans := [([[false], [true]], 69), ([[false], [true]], 16)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 4] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 4] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 4] 0)))))), baseY := [0], trans := [([[false], [true]], 68), ([[false], [true]], 16)] }
  ]
}

def cert_ternary_k2_r2 : Cert := {
  d := 1,
  e := 1,
  entries := [
    { formula := .and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 4)), baseY := [2], trans := [([[false], [true]], 1), ([[false], [true]], 2)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 2))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 1))), baseY := [1], trans := [([[false], [true]], 3), ([[false], [true]], 4)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 1))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 2))), baseY := [0], trans := [([[false], [true]], 5), ([[false], [true]], 6)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 1)))), baseY := [0], trans := [([[false], [true]], 7), ([[false], [true]], 8)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 1))))), baseY := [0], trans := [([[false], [true]], 9), ([[false], [true]], 10)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0))))), baseY := [0], trans := [([[false], [true]], 11), ([[false], [true]], 12)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 1))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0))))), baseY := [0], trans := [([[false], [true]], 13), ([[false], [true]], 14)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0)))), baseY := [0], trans := [([[false], [true]], 7), ([[false], [true]], 15)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 1))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] (-1)))))))), baseY := [0], trans := [([[false], [true]], 16), ([[false], [true]], 17)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] (-1)))))))), baseY := [0], trans := [([[false], [true]], 18), ([[false], [true]], 15)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 1))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0)))))), baseY := [0], trans := [([[false], [true]], 19), ([[false], [true]], 20)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0))))), baseY := [0], trans := [([[false], [true]], 11), ([[false], [true]], 15)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] (-1)))))))), baseY := [0], trans := [([[false], [true]], 21), ([[false], [true]], 22)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] (-1))))))), baseY := [0], trans := [([[false], [true]], 23), ([[false], [true]], 24)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 1))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] (-1)))))), baseY := [0], trans := [([[false], [true]], 13), ([[false], [true]], 14)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] (-1)))))))), baseY := [0], trans := [([[false], [true]], 25), ([[false], [true]], 26)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] (-2)))))))), baseY := [0], trans := [([[false], [true]], 7), ([[false], [true]], 15)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] (-1)))))))))), baseY := [0], trans := [([[false], [true]], 16), ([[false], [true]], 17)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0))))), baseY := [0], trans := [([[false], [true]], 27), ([[false], [true]], 15)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] (-1)))))))), baseY := [0], trans := [([[false], [true]], 11), ([[false], [true]], 15)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 1))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0)))))), baseY := [0], trans := [([[false], [true]], 9), ([[false], [true]], 10)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] (-1)))))))), baseY := [0], trans := [([[false], [true]], 18), ([[false], [true]], 15)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0)))))))), baseY := [0], trans := [([[false], [true]], 28), ([[false], [true]], 29)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] (-1)))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0)))))), baseY := [0], trans := [([[false], [true]], 30), ([[false], [true]], 15)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] (-1)))))))), baseY := [0], trans := [([[false], [true]], 31), ([[false], [true]], 32)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] (-2)))))))), baseY := [0], trans := [([[false], [true]], 7), ([[false], [true]], 15)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] (-1))))))))))), baseY := [0], trans := [([[false], [true]], 25), ([[false], [true]], 26)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] (-1)))))), baseY := [0], trans := [([[false], [true]], 18), ([[false], [true]], 15)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] (-1)))))))), baseY := [0], trans := [([[false], [true]], 11), ([[false], [true]], 15)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 1))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0))))))), baseY := [0], trans := [([[false], [true]], 21), ([[false], [true]], 22)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] (-1))))))), baseY := [0], trans := [([[false], [true]], 23), ([[false], [true]], 15)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] (-1)))))))), baseY := [0], trans := [([[false], [true]], 18), ([[false], [true]], 15)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] (-1))))))))), baseY := [0], trans := [([[false], [true]], 33), ([[false], [true]], 34)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] (-2)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] (-2)))))))), baseY := [0], trans := [([[false], [true]], 11), ([[false], [true]], 15)] },
    { formula := .or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 0) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] 0))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (.and (fModEq [1, 1] 3 1) (fLinLe [-1, 2] (-1)))) (.or (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0))) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (.and (fModEq [1, 1] 3 2) (fLinLe [-1, 2] 0)))))))), baseY := [0], trans := [([[false], [true]], 31), ([[false], [true]], 32)] }
  ]
}

def cert_lb_k0_r0 : Cert := {
  d := 2,
  e := 0,
  entries := [
    { formula := .or (.not (.and (fDisj (natAff [1, 0] 1) (natAff [1, 0])) (.and (fModEq [1, 0] 3 1) (.and (fDisj (natAff [3, 0] 2) (natAff [0, 1])) (fModEq [3, 1] 3 1))))) (fLinLe [15, -3] (-15)), baseY := [], trans := [([[]], 1), ([[]], 2), ([[]], 3), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 2) (.and (fDisj (natAff [3, 0] 1) (natAff [0, 1])) (fModEq [3, 1] 3 2))))) (fLinLe [15, -3] (-8)), baseY := [], trans := [([[]], 5), ([[]], 4), ([[]], 4), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0] 1) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0] 2) (natAff [0, 1])) (fModEq [3, 1] 3 2))))) (fLinLe [15, -3] (-15)), baseY := [], trans := [([[]], 6), ([[]], 0), ([[]], 7), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 2) (.and (fDisj (natAff [3, 0] 1) (natAff [0, 1])) (fModEq [3, 1] 3 0))))) (fLinLe [15, -3] (-6)), baseY := [], trans := [([[]], 8), ([[]], 4), ([[]], 4), ([[]], 4)] },
    { formula := .tt, baseY := [], trans := [([[]], 4), ([[]], 4), ([[]], 4), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 1) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 1))))) (fLinLe [15, -3] (-4)), baseY := [], trans := [([[]], 9), ([[]], 4), ([[]], 10), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0] 1) (natAff [0, 1])) (fModEq [3, 1] 3 1))))) (fLinLe [15, -3] (-8)), baseY := [], trans := [([[]], 11), ([[]], 4), ([[]], 4), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0] 1) (natAff [0, 1])) (fModEq [3, 1] 3 2))))) (fLinLe [15, -3] (-6)), baseY := [], trans := [([[]], 12), ([[]], 4), ([[]], 4), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 1) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 0))))) (fLinLe [15, -3] (-3)), baseY := [], trans := [([[]], 13), ([[]], 4), ([[]], 14), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 2) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 2))))) (fLinLe [15, -3] (-2)), baseY := [], trans := [([[]], 15), ([[]], 4), ([[]], 16), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 2) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 0))))) (fLinLe [15, -3] (-1)), baseY := [], trans := [([[]], 17), ([[]], 4), ([[]], 18), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 2))))) (fLinLe [15, -3] (-4)), baseY := [], trans := [([[]], 19), ([[]], 4), ([[]], 20), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 1))))) (fLinLe [15, -3] (-3)), baseY := [], trans := [([[]], 21), ([[]], 4), ([[]], 22), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 2) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 0))))) (fLinLe [15, -3] (-2)), baseY := [], trans := [([[]], 17), ([[]], 4), ([[]], 23), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 2) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 1))))) (fLinLe [15, -3] 0), baseY := [], trans := [([[]], 16), ([[]], 4), ([[]], 24), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 1) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 1))))) (fLinLe [15, -3] (-1)), baseY := [], trans := [([[]], 25), ([[]], 4), ([[]], 26), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 1) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 2))))) (fLinLe [15, -3] 0), baseY := [], trans := [([[]], 14), ([[]], 4), ([[]], 27), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 1) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 0))))) (fLinLe [15, -3] (-1)), baseY := [], trans := [([[]], 10), ([[]], 4), ([[]], 28), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 1) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 1))))) (fLinLe [15, -3] 1), baseY := [], trans := [([[]], 29), ([[]], 4), ([[]], 30), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 1))))) (fLinLe [15, -3] (-2)), baseY := [], trans := [([[]], 20), ([[]], 4), ([[]], 22), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 2))))) (fLinLe [15, -3] (-1)), baseY := [], trans := [([[]], 31), ([[]], 4), ([[]], 32), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 2))))) (fLinLe [15, -3] (-2)), baseY := [], trans := [([[]], 31), ([[]], 4), ([[]], 33), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 0))))) (fLinLe [15, -3] 0), baseY := [], trans := [([[]], 22), ([[]], 4), ([[]], 34), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 1) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 1))))) (fLinLe [15, -3] 0), baseY := [], trans := [([[]], 29), ([[]], 4), ([[]], 26), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 1) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 0))))) (fLinLe [15, -3] 1), baseY := [], trans := [([[]], 35), ([[]], 4), ([[]], 36), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 2) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 2))))) (fLinLe [15, -3] (-1)), baseY := [], trans := [([[]], 15), ([[]], 4), ([[]], 37), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 2) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 0))))) (fLinLe [15, -3] 1), baseY := [], trans := [([[]], 38), ([[]], 4), ([[]], 39), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 2) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 2))))) (fLinLe [15, -3] 1), baseY := [], trans := [([[]], 23), ([[]], 4), ([[]], 40), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 2) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 1))))) (fLinLe [15, -3] 1), baseY := [], trans := [([[]], 16), ([[]], 4), ([[]], 41), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 2) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 2))))) (fLinLe [15, -3] 0), baseY := [], trans := [([[]], 23), ([[]], 4), ([[]], 37), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 2) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 0))))) (fLinLe [15, -3] 2), baseY := [], trans := [([[]], 24), ([[]], 4), ([[]], 39), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 1))))) (fLinLe [15, -3] (-1)), baseY := [], trans := [([[]], 20), ([[]], 4), ([[]], 42), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 2))))) (fLinLe [15, -3] 1), baseY := [], trans := [([[]], 43), ([[]], 4), ([[]], 44), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 2))))) (fLinLe [15, -3] 0), baseY := [], trans := [([[]], 43), ([[]], 4), ([[]], 32), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 1))))) (fLinLe [15, -3] 1), baseY := [], trans := [([[]], 33), ([[]], 4), ([[]], 45), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 2) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 0))))) (fLinLe [15, -3] 0), baseY := [], trans := [([[]], 38), ([[]], 4), ([[]], 18), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 2) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 1))))) (fLinLe [15, -3] 2), baseY := [], trans := [([[]], 37), ([[]], 4), ([[]], 41), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 1) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 2))))) (fLinLe [15, -3] 1), baseY := [], trans := [([[]], 14), ([[]], 4), ([[]], 46), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 1) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 0))))) (fLinLe [15, -3] 0), baseY := [], trans := [([[]], 35), ([[]], 4), ([[]], 28), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 1) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 1))))) (fLinLe [15, -3] 2), baseY := [], trans := [([[]], 27), ([[]], 4), ([[]], 30), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 1) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 2))))) (fLinLe [15, -3] 2), baseY := [], trans := [([[]], 28), ([[]], 4), ([[]], 46), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 1) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 0))))) (fLinLe [15, -3] 2), baseY := [], trans := [([[]], 26), ([[]], 4), ([[]], 36), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 0))))) (fLinLe [15, -3] 1), baseY := [], trans := [([[]], 22), ([[]], 4), ([[]], 47), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 1))))) (fLinLe [15, -3] 0), baseY := [], trans := [([[]], 33), ([[]], 4), ([[]], 42), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 2))))) (fLinLe [15, -3] 2), baseY := [], trans := [([[]], 34), ([[]], 4), ([[]], 44), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 0))))) (fLinLe [15, -3] 2), baseY := [], trans := [([[]], 42), ([[]], 4), ([[]], 47), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 2) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 2))))) (fLinLe [15, -3] 2), baseY := [], trans := [([[]], 18), ([[]], 4), ([[]], 40), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 1))))) (fLinLe [15, -3] 2), baseY := [], trans := [([[]], 32), ([[]], 4), ([[]], 45), ([[]], 4)] }
  ]
}

def cert_lb_k0_r1 : Cert := {
  d := 2,
  e := 0,
  entries := [
    { formula := .or (.not (.and (fDisj (natAff [1, 0] 1) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0] 2) (natAff [0, 1])) (fModEq [3, 1] 3 2))))) (fLinLe [15, -3] (-15)), baseY := [], trans := [([[]], 1), ([[]], 2), ([[]], 3), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0] 1) (natAff [0, 1])) (fModEq [3, 1] 3 1))))) (fLinLe [15, -3] (-8)), baseY := [], trans := [([[]], 5), ([[]], 4), ([[]], 4), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0] 1) (natAff [1, 0])) (.and (fModEq [1, 0] 3 1) (.and (fDisj (natAff [3, 0] 2) (natAff [0, 1])) (fModEq [3, 1] 3 1))))) (fLinLe [15, -3] (-15)), baseY := [], trans := [([[]], 6), ([[]], 0), ([[]], 7), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0] 1) (natAff [0, 1])) (fModEq [3, 1] 3 2))))) (fLinLe [15, -3] (-6)), baseY := [], trans := [([[]], 8), ([[]], 4), ([[]], 4), ([[]], 4)] },
    { formula := .tt, baseY := [], trans := [([[]], 4), ([[]], 4), ([[]], 4), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 2))))) (fLinLe [15, -3] (-4)), baseY := [], trans := [([[]], 9), ([[]], 4), ([[]], 10), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 2) (.and (fDisj (natAff [3, 0] 1) (natAff [0, 1])) (fModEq [3, 1] 3 2))))) (fLinLe [15, -3] (-8)), baseY := [], trans := [([[]], 11), ([[]], 4), ([[]], 4), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 2) (.and (fDisj (natAff [3, 0] 1) (natAff [0, 1])) (fModEq [3, 1] 3 0))))) (fLinLe [15, -3] (-6)), baseY := [], trans := [([[]], 12), ([[]], 4), ([[]], 4), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 1))))) (fLinLe [15, -3] (-3)), baseY := [], trans := [([[]], 13), ([[]], 4), ([[]], 14), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 1))))) (fLinLe [15, -3] (-2)), baseY := [], trans := [([[]], 10), ([[]], 4), ([[]], 14), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 2))))) (fLinLe [15, -3] (-1)), baseY := [], trans := [([[]], 15), ([[]], 4), ([[]], 16), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 1) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 1))))) (fLinLe [15, -3] (-4)), baseY := [], trans := [([[]], 17), ([[]], 4), ([[]], 18), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 1) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 0))))) (fLinLe [15, -3] (-3)), baseY := [], trans := [([[]], 19), ([[]], 4), ([[]], 20), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 2))))) (fLinLe [15, -3] (-2)), baseY := [], trans := [([[]], 15), ([[]], 4), ([[]], 21), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 0))))) (fLinLe [15, -3] 0), baseY := [], trans := [([[]], 14), ([[]], 4), ([[]], 22), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 1))))) (fLinLe [15, -3] (-1)), baseY := [], trans := [([[]], 10), ([[]], 4), ([[]], 23), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 2))))) (fLinLe [15, -3] 1), baseY := [], trans := [([[]], 24), ([[]], 4), ([[]], 25), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 2) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 2))))) (fLinLe [15, -3] (-2)), baseY := [], trans := [([[]], 26), ([[]], 4), ([[]], 27), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 2) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 0))))) (fLinLe [15, -3] (-1)), baseY := [], trans := [([[]], 28), ([[]], 4), ([[]], 29), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 2) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 0))))) (fLinLe [15, -3] (-2)), baseY := [], trans := [([[]], 28), ([[]], 4), ([[]], 30), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 2) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 1))))) (fLinLe [15, -3] 0), baseY := [], trans := [([[]], 27), ([[]], 4), ([[]], 31), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 2))))) (fLinLe [15, -3] 0), baseY := [], trans := [([[]], 24), ([[]], 4), ([[]], 16), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 1))))) (fLinLe [15, -3] 1), baseY := [], trans := [([[]], 21), ([[]], 4), ([[]], 32), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 0))))) (fLinLe [15, -3] 1), baseY := [], trans := [([[]], 14), ([[]], 4), ([[]], 33), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 1))))) (fLinLe [15, -3] 0), baseY := [], trans := [([[]], 21), ([[]], 4), ([[]], 23), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 2))))) (fLinLe [15, -3] 2), baseY := [], trans := [([[]], 22), ([[]], 4), ([[]], 25), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 1) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 1))))) (fLinLe [15, -3] (-1)), baseY := [], trans := [([[]], 34), ([[]], 4), ([[]], 35), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 1) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 2))))) (fLinLe [15, -3] 0), baseY := [], trans := [([[]], 20), ([[]], 4), ([[]], 36), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 1) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 0))))) (fLinLe [15, -3] (-1)), baseY := [], trans := [([[]], 18), ([[]], 4), ([[]], 37), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 1) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 1))))) (fLinLe [15, -3] 1), baseY := [], trans := [([[]], 38), ([[]], 4), ([[]], 39), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 1) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 1))))) (fLinLe [15, -3] 0), baseY := [], trans := [([[]], 38), ([[]], 4), ([[]], 35), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 1) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 0))))) (fLinLe [15, -3] 1), baseY := [], trans := [([[]], 40), ([[]], 4), ([[]], 41), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 0))))) (fLinLe [15, -3] 2), baseY := [], trans := [([[]], 23), ([[]], 4), ([[]], 33), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 0) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 1))))) (fLinLe [15, -3] 2), baseY := [], trans := [([[]], 16), ([[]], 4), ([[]], 32), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 2) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 2))))) (fLinLe [15, -3] (-1)), baseY := [], trans := [([[]], 26), ([[]], 4), ([[]], 42), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 2) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 0))))) (fLinLe [15, -3] 1), baseY := [], trans := [([[]], 43), ([[]], 4), ([[]], 44), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 2) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 2))))) (fLinLe [15, -3] 1), baseY := [], trans := [([[]], 30), ([[]], 4), ([[]], 45), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 2) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 1))))) (fLinLe [15, -3] 1), baseY := [], trans := [([[]], 27), ([[]], 4), ([[]], 46), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 2) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 2))))) (fLinLe [15, -3] 0), baseY := [], trans := [([[]], 30), ([[]], 4), ([[]], 42), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 2) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 0))))) (fLinLe [15, -3] 2), baseY := [], trans := [([[]], 31), ([[]], 4), ([[]], 44), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 2) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 0))))) (fLinLe [15, -3] 0), baseY := [], trans := [([[]], 43), ([[]], 4), ([[]], 29), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 2) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 1))))) (fLinLe [15, -3] 2), baseY := [], trans := [([[]], 42), ([[]], 4), ([[]], 46), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 1) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 2))))) (fLinLe [15, -3] 1), baseY := [], trans := [([[]], 20), ([[]], 4), ([[]], 47), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 1) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 0))))) (fLinLe [15, -3] 0), baseY := [], trans := [([[]], 40), ([[]], 4), ([[]], 37), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 1) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 1))))) (fLinLe [15, -3] 2), baseY := [], trans := [([[]], 36), ([[]], 4), ([[]], 39), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 1) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 2))))) (fLinLe [15, -3] 2), baseY := [], trans := [([[]], 37), ([[]], 4), ([[]], 47), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 1) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 0))))) (fLinLe [15, -3] 2), baseY := [], trans := [([[]], 35), ([[]], 4), ([[]], 41), ([[]], 4)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fModEq [1, 0] 3 2) (.and (fDisj (natAff [3, 0]) (natAff [0, 1])) (fModEq [3, 1] 3 2))))) (fLinLe [15, -3] 2), baseY := [], trans := [([[]], 29), ([[]], 4), ([[]], 45), ([[]], 4)] }
  ]
}

def cert_lb_k0_r2 : Cert := {
  d := 2,
  e := 0,
  entries := [
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0] 1)) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (fModEq [1, 1] 3 2)))) (fLinLe [2, -1] (-2)), baseY := [], trans := [([[]], 1), ([[]], 0), ([[]], 2), ([[]], 3)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (fModEq [1, 1] 3 1)))) (fLinLe [2, -1] (-1)), baseY := [], trans := [([[]], 2), ([[]], 3), ([[]], 4), ([[]], 3)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (fModEq [1, 1] 3 2)))) (fLinLe [2, -1] (-1)), baseY := [], trans := [([[]], 1), ([[]], 3), ([[]], 5), ([[]], 3)] },
    { formula := .tt, baseY := [], trans := [([[]], 3), ([[]], 3), ([[]], 3), ([[]], 3)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (fModEq [1, 1] 3 0)))) (fLinLe [2, -1] 0), baseY := [], trans := [([[]], 4), ([[]], 3), ([[]], 6), ([[]], 3)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (fModEq [1, 1] 3 2)))) (fLinLe [2, -1] 0), baseY := [], trans := [([[]], 6), ([[]], 3), ([[]], 5), ([[]], 3)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fDisj (natAff [1, 0]) (natAff [0, 1])) (fModEq [1, 1] 3 1)))) (fLinLe [2, -1] 0), baseY := [], trans := [([[]], 5), ([[]], 3), ([[]], 4), ([[]], 3)] }
  ]
}

def cert_lb_k2_r2 : Cert := {
  d := 2,
  e := 0,
  entries := [
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0] 1)) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (fModEq [1, 1] 3 2)))) (fLinLe [1, -2] (-1)), baseY := [], trans := [([[]], 1), ([[]], 0), ([[]], 2), ([[]], 3)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (fModEq [1, 1] 3 1)))) (fLinLe [1, -2] (-1)), baseY := [], trans := [([[]], 4), ([[]], 5), ([[]], 6), ([[]], 5)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (fModEq [1, 1] 3 2)))) (fLinLe [1, -2] 0), baseY := [], trans := [([[]], 7), ([[]], 5), ([[]], 8), ([[]], 5)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0] 1)) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 1) (fModEq [1, 1] 3 0)))) (fLinLe [1, -2] 0), baseY := [], trans := [([[]], 9), ([[]], 10), ([[]], 11), ([[]], 12)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (fModEq [1, 1] 3 2)))) (fLinLe [1, -2] (-1)), baseY := [], trans := [([[]], 1), ([[]], 5), ([[]], 2), ([[]], 5)] },
    { formula := .tt, baseY := [], trans := [([[]], 5), ([[]], 5), ([[]], 5), ([[]], 5)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (fModEq [1, 1] 3 0)))) (fLinLe [1, -2] 0), baseY := [], trans := [([[]], 6), ([[]], 5), ([[]], 13), ([[]], 5)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (fModEq [1, 1] 3 1)))) (fLinLe [1, -2] 0), baseY := [], trans := [([[]], 2), ([[]], 5), ([[]], 14), ([[]], 5)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (fModEq [1, 1] 3 2)))) (fLinLe [1, -2] 1), baseY := [], trans := [([[]], 7), ([[]], 5), ([[]], 8), ([[]], 5)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (fModEq [1, 1] 3 0)))) (fLinLe [1, -2] 0), baseY := [], trans := [([[]], 9), ([[]], 5), ([[]], 15), ([[]], 5)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0] 1)) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (fModEq [1, 1] 3 1)))) (fLinLe [1, -2] (-1)), baseY := [], trans := [([[]], 16), ([[]], 5), ([[]], 5), ([[]], 5)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (fModEq [1, 1] 3 1)))) (fLinLe [1, -2] 1), baseY := [], trans := [([[]], 17), ([[]], 5), ([[]], 5), ([[]], 5)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0] 1)) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0) (fModEq [1, 1] 3 2)))) (fLinLe [1, -2] 0), baseY := [], trans := [([[]], 18), ([[]], 5), ([[]], 5), ([[]], 5)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (fModEq [1, 1] 3 1)))) (fLinLe [1, -2] 1), baseY := [], trans := [([[]], 2), ([[]], 5), ([[]], 14), ([[]], 5)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 2) (fModEq [1, 1] 3 0)))) (fLinLe [1, -2] 1), baseY := [], trans := [([[]], 6), ([[]], 5), ([[]], 13), ([[]], 5)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (fModEq [1, 1] 3 1)))) (fLinLe [1, -2] 1), baseY := [], trans := [([[]], 19), ([[]], 5), ([[]], 20), ([[]], 5)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (fModEq [1, 1] 3 2)))) (fLinLe [1, -2] (-1)), baseY := [], trans := [([[]], 21), ([[]], 5), ([[]], 17), ([[]], 5)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (fModEq [1, 1] 3 2)))) (fLinLe [1, -2] 0), baseY := [], trans := [([[]], 18), ([[]], 5), ([[]], 22), ([[]], 5)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (fModEq [1, 1] 3 1)))) (fLinLe [1, -2] 0), baseY := [], trans := [([[]], 17), ([[]], 5), ([[]], 23), ([[]], 5)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (fModEq [1, 1] 3 2)))) (fLinLe [1, -2] 0), baseY := [], trans := [([[]], 24), ([[]], 5), ([[]], 25), ([[]], 5)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (fModEq [1, 1] 3 0)))) (fLinLe [1, -2] 1), baseY := [], trans := [([[]], 9), ([[]], 5), ([[]], 15), ([[]], 5)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (fModEq [1, 1] 3 1)))) (fLinLe [1, -2] (-1)), baseY := [], trans := [([[]], 16), ([[]], 5), ([[]], 26), ([[]], 5)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (fModEq [1, 1] 3 2)))) (fLinLe [1, -2] 1), baseY := [], trans := [([[]], 18), ([[]], 5), ([[]], 22), ([[]], 5)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (fModEq [1, 1] 3 0)))) (fLinLe [1, -2] 1), baseY := [], trans := [([[]], 26), ([[]], 5), ([[]], 27), ([[]], 5)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (fModEq [1, 1] 3 1)))) (fLinLe [1, -2] 0), baseY := [], trans := [([[]], 19), ([[]], 5), ([[]], 20), ([[]], 5)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1) (fModEq [1, 1] 3 2)))) (fLinLe [1, -2] 1), baseY := [], trans := [([[]], 24), ([[]], 5), ([[]], 25), ([[]], 5)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (fModEq [1, 1] 3 0)))) (fLinLe [1, -2] 0), baseY := [], trans := [([[]], 26), ([[]], 5), ([[]], 27), ([[]], 5)] },
    { formula := .or (.not (.and (fDisj (natAff [1, 0]) (natAff [1, 0])) (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0) (fModEq [1, 1] 3 1)))) (fLinLe [1, -2] 1), baseY := [], trans := [([[]], 17), ([[]], 5), ([[]], 23), ([[]], 5)] }
  ]
}

def cert_mersenne_collatz_3 : Cert := {
  d := 1,
  e := 0,
  entries := [
    { formula := .and (.or (.not (fDisj (natAff [1]) (natAff [3] 1))) (fDisj (natAff [3] 1) (natAff [3]))) (.or (.not (fDisj (natAff [3] 1) (natAff [3]))) (fDisj (natAff [1]) (natAff [3] 1))), baseY := [], trans := [([[]], 1), ([[]], 2)] },
    { formula := .and (.or (.not (fDisj (natAff [1]) (natAff [3]))) (fDisj (natAff [3]) (natAff [3]))) (.or (.not (fDisj (natAff [3]) (natAff [3]))) (fDisj (natAff [1]) (natAff [3]))), baseY := [], trans := [([[]], 1), ([[]], 3)] },
    { formula := .and (.or (.not (fDisj (natAff [1]) (natAff [3] 2))) (fDisj (natAff [3] 2) (natAff [3] 1))) (.or (.not (fDisj (natAff [3] 2) (natAff [3] 1))) (fDisj (natAff [1]) (natAff [3] 2))), baseY := [], trans := [([[]], 0), ([[]], 4)] },
    { formula := .tt, baseY := [], trans := [([[]], 3), ([[]], 3)] },
    { formula := .not (fDisj (natAff [3] 2) (natAff [3] 2)), baseY := [], trans := [([[]], 5), ([[]], 3)] },
    { formula := .not (fDisj (natAff [3] 1) (natAff [3] 1)), baseY := [], trans := [([[]], 3), ([[]], 4)] }
  ]
}

def cert_mersenne_collatz_7 : Cert := {
  d := 1,
  e := 0,
  entries := [
    { formula := .and (.or (.not (fDisj (natAff [1]) (natAff [7] 1))) (fDisj (natAff [7] 1) (natAff [7]))) (.or (.not (fDisj (natAff [7] 1) (natAff [7]))) (fDisj (natAff [1]) (natAff [7] 1))), baseY := [], trans := [([[]], 1), ([[]], 2)] },
    { formula := .and (.or (.not (fDisj (natAff [1]) (natAff [7]))) (fDisj (natAff [7]) (natAff [7]))) (.or (.not (fDisj (natAff [7]) (natAff [7]))) (fDisj (natAff [1]) (natAff [7]))), baseY := [], trans := [([[]], 1), ([[]], 3)] },
    { formula := .and (.or (.not (fDisj (natAff [1]) (natAff [7] 4))) (fDisj (natAff [7] 4) (natAff [7] 3))) (.or (.not (fDisj (natAff [7] 4) (natAff [7] 3))) (fDisj (natAff [1]) (natAff [7] 4))), baseY := [], trans := [([[]], 4), ([[]], 5)] },
    { formula := .tt, baseY := [], trans := [([[]], 3), ([[]], 3)] },
    { formula := .and (.or (.not (fDisj (natAff [1]) (natAff [7] 2))) (fDisj (natAff [7] 2) (natAff [7] 1))) (.or (.not (fDisj (natAff [7] 2) (natAff [7] 1))) (fDisj (natAff [1]) (natAff [7] 2))), baseY := [], trans := [([[]], 0), ([[]], 6)] },
    { formula := .not (fDisj (natAff [7] 5) (natAff [7] 5)), baseY := [], trans := [([[]], 3), ([[]], 7)] },
    { formula := .not (fDisj (natAff [7] 4) (natAff [7] 4)), baseY := [], trans := [([[]], 8), ([[]], 3)] },
    { formula := .not (fDisj (natAff [7] 6) (natAff [7] 6)), baseY := [], trans := [([[]], 9), ([[]], 3)] },
    { formula := .not (fDisj (natAff [7] 2) (natAff [7] 2)), baseY := [], trans := [([[]], 10), ([[]], 3)] },
    { formula := .not (fDisj (natAff [7] 3) (natAff [7] 3)), baseY := [], trans := [([[]], 3), ([[]], 5)] },
    { formula := .not (fDisj (natAff [7] 1) (natAff [7] 1)), baseY := [], trans := [([[]], 3), ([[]], 6)] }
  ]
}

def cert_mersenne_collatz_15 : Cert := {
  d := 1,
  e := 0,
  entries := [
    { formula := .and (.or (.not (fDisj (natAff [1]) (natAff [15] 1))) (fDisj (natAff [15] 1) (natAff [15]))) (.or (.not (fDisj (natAff [15] 1) (natAff [15]))) (fDisj (natAff [1]) (natAff [15] 1))), baseY := [], trans := [([[]], 1), ([[]], 2)] },
    { formula := .and (.or (.not (fDisj (natAff [1]) (natAff [15]))) (fDisj (natAff [15]) (natAff [15]))) (.or (.not (fDisj (natAff [15]) (natAff [15]))) (fDisj (natAff [1]) (natAff [15]))), baseY := [], trans := [([[]], 1), ([[]], 3)] },
    { formula := .and (.or (.not (fDisj (natAff [1]) (natAff [15] 8))) (fDisj (natAff [15] 8) (natAff [15] 7))) (.or (.not (fDisj (natAff [15] 8) (natAff [15] 7))) (fDisj (natAff [1]) (natAff [15] 8))), baseY := [], trans := [([[]], 4), ([[]], 5)] },
    { formula := .tt, baseY := [], trans := [([[]], 3), ([[]], 3)] },
    { formula := .and (.or (.not (fDisj (natAff [1]) (natAff [15] 4))) (fDisj (natAff [15] 4) (natAff [15] 3))) (.or (.not (fDisj (natAff [15] 4) (natAff [15] 3))) (fDisj (natAff [1]) (natAff [15] 4))), baseY := [], trans := [([[]], 6), ([[]], 7)] },
    { formula := .not (fDisj (natAff [15] 11) (natAff [15] 11)), baseY := [], trans := [([[]], 3), ([[]], 8)] },
    { formula := .and (.or (.not (fDisj (natAff [1]) (natAff [15] 2))) (fDisj (natAff [15] 2) (natAff [15] 1))) (.or (.not (fDisj (natAff [15] 2) (natAff [15] 1))) (fDisj (natAff [1]) (natAff [15] 2))), baseY := [], trans := [([[]], 0), ([[]], 9)] },
    { formula := .not (fDisj (natAff [15] 9) (natAff [15] 9)), baseY := [], trans := [([[]], 3), ([[]], 10)] },
    { formula := .not (fDisj (natAff [15] 13) (natAff [15] 13)), baseY := [], trans := [([[]], 3), ([[]], 11)] },
    { formula := .not (fDisj (natAff [15] 8) (natAff [15] 8)), baseY := [], trans := [([[]], 12), ([[]], 3)] },
    { formula := .not (fDisj (natAff [15] 12) (natAff [15] 12)), baseY := [], trans := [([[]], 13), ([[]], 3)] },
    { formula := .not (fDisj (natAff [15] 14) (natAff [15] 14)), baseY := [], trans := [([[]], 14), ([[]], 3)] },
    { formula := .not (fDisj (natAff [15] 4) (natAff [15] 4)), baseY := [], trans := [([[]], 15), ([[]], 3)] },
    { formula := .not (fDisj (natAff [15] 6) (natAff [15] 6)), baseY := [], trans := [([[]], 16), ([[]], 3)] },
    { formula := .not (fDisj (natAff [15] 7) (natAff [15] 7)), baseY := [], trans := [([[]], 3), ([[]], 5)] },
    { formula := .not (fDisj (natAff [15] 2) (natAff [15] 2)), baseY := [], trans := [([[]], 17), ([[]], 3)] },
    { formula := .not (fDisj (natAff [15] 3) (natAff [15] 3)), baseY := [], trans := [([[]], 3), ([[]], 7)] },
    { formula := .not (fDisj (natAff [15] 1) (natAff [15] 1)), baseY := [], trans := [([[]], 3), ([[]], 9)] }
  ]
}

def cert_mc3_pop_sparse : Cert := {
  d := 1,
  e := 0,
  entries := [
    { formula := .or (.not (fDisj (natAff [1]) (natAff [3] 1))) (.and (fPopMod [(1, natAff [3] 1)] 2 1) (fDisj (natAff [1]) (natAff [2]))), baseY := [], trans := [([[]], 1), ([[]], 2)] },
    { formula := .or (.not (fDisj (natAff [1]) (natAff [3]))) (.and (fPopMod [(1, natAff [3])] 2 0) (fDisj (natAff [1]) (natAff [2]))), baseY := [], trans := [([[]], 1), ([[]], 3)] },
    { formula := .or (.not (fDisj (natAff [1]) (natAff [3] 2))) (.and (fPopMod [(1, natAff [3] 2)] 2 1) (fDisj (natAff [1]) (natAff [2] 1))), baseY := [], trans := [([[]], 0), ([[]], 3)] },
    { formula := .tt, baseY := [], trans := [([[]], 3), ([[]], 3)] }
  ]
}

def cert_carry1_parity_disj : Cert := {
  d := 2,
  e := 0,
  entries := [
    { formula := .or (.not (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 1)) (.and (.or (.not (fPopMod [(1, natAff [1, 0]), (1, natAff [0, 1]), ((-1), natAff [1, 1])] 2 0)) (fDisj (natAff [1, 0]) (natAff [0, 1]))) (.or (.not (fDisj (natAff [1, 0]) (natAff [0, 1]))) (fPopMod [(1, natAff [1, 0]), (1, natAff [0, 1]), ((-1), natAff [1, 1])] 2 0))), baseY := [], trans := [([[]], 0), ([[]], 0), ([[]], 0), ([[]], 1)] },
    { formula := .or (.not (fCarryLe (natAff [1, 0]) (natAff [0, 1]) true 0)) (.not (fPopMod [(1, natAff [1, 0]), (1, natAff [0, 1]), ((-1), natAff [1, 1] 1)] 2 0)), baseY := [], trans := [([[]], 2), ([[]], 3), ([[]], 3), ([[]], 3)] },
    { formula := .or (.not (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false 0)) (.not (fPopMod [(1, natAff [1, 0]), (1, natAff [0, 1]), ((-1), natAff [1, 1])] 2 1)), baseY := [], trans := [([[]], 2), ([[]], 2), ([[]], 2), ([[]], 3)] },
    { formula := .tt, baseY := [], trans := [([[]], 3), ([[]], 3), ([[]], 3), ([[]], 3)] }
  ]
}

def cert_carry_word_zero : Cert := {
  d := 2,
  e := 0,
  entries := [
    { formula := .and (.or (.not (fXor3Zero (natAff [1, 1]) (natAff [1, 0]) (natAff [0, 1]))) (fDisj (natAff [1, 0]) (natAff [0, 1]))) (.or (.not (fDisj (natAff [1, 0]) (natAff [0, 1]))) (fXor3Zero (natAff [1, 1]) (natAff [1, 0]) (natAff [0, 1]))), baseY := [], trans := [([[]], 0), ([[]], 0), ([[]], 0), ([[]], 1)] },
    { formula := .not (fXor3Zero (natAff [1, 1] 1) (natAff [1, 0]) (natAff [0, 1])), baseY := [], trans := [([[]], 2), ([[]], 2), ([[]], 2), ([[]], 2)] },
    { formula := .tt, baseY := [], trans := [([[]], 2), ([[]], 2), ([[]], 2), ([[]], 2)] }
  ]
}

def cert_sparse_triple_evil : Cert := {
  d := 1,
  e := 0,
  entries := [
    { formula := .or (.not (fDisj (natAff [1]) (natAff [2]))) (fPopMod [(1, natAff [3])] 2 0), baseY := [], trans := [([[]], 0), ([[]], 1)] },
    { formula := .or (.not (fDisj (natAff [1]) (natAff [2] 1))) (fPopMod [(1, natAff [3] 1)] 2 1), baseY := [], trans := [([[]], 0), ([[]], 2)] },
    { formula := .tt, baseY := [], trans := [([[]], 2), ([[]], 2)] }
  ]
}


/-! ## Section 7: Bridge Lemmas Connecting evalFormulaBool to Native Lean 4 Nat Predicates -/

private theorem eval_ternary_k0_iff (r qy px c0 x y : Nat) :
    evalFormulaBool
      (.and (fDisj (natAff [1, 0]) (natAff [0, 1]))
            (.and (fModEq [1, 1] 3 r) (fLinLe [- (px : Int), (qy : Int)] (c0 : Int))))
      [x, y] = true ↔
    x &&& y = 0 ∧ (x + y) % 3 = r % 3 ∧ qy * y ≤ px * x + c0 := by
  simp only [evalFormulaBool, Bool.and_eq_true, fDisj, fModEq, fLinLe, intAff, natAff,
             evalAtomBool, NatAff.eval, dotNat, dotInt, Nat.one_mul, Nat.zero_mul,
             Nat.add_zero, Nat.zero_add, Int.one_mul, Int.add_zero,
             bitRel4Dec_andZero_iff, decide_eq_true_eq,
             show (3 == 0) = false by decide, Bool.false_eq_true, ↓reduceIte]
  constructor
  · rintro ⟨hd, hm, hle⟩
    refine ⟨hd, ?_, ?_⟩
    · omega
    · have : -((px : Int) * (x : Int)) + (qy : Int) * (y : Int) ≤ (c0 : Int) := by
        simpa [Int.neg_mul] using hle
      omega
  · rintro ⟨hd, hm, hle⟩
    refine ⟨hd, ?_, ?_⟩
    · omega
    · rw [Int.neg_mul]; omega

private theorem eval_ternary_carry_iff (K r qy px c0 x y : Nat) :
    evalFormulaBool
      (.and (fCarryLe (natAff [1, 0]) (natAff [0, 1]) false K)
            (.and (fModEq [1, 1] 3 r) (fLinLe [- (px : Int), (qy : Int)] (c0 : Int))))
      [x, y] = true ↔
    carryCount x y false ≤ K ∧ (x + y) % 3 = r % 3 ∧ qy * y ≤ px * x + c0 := by
  simp only [evalFormulaBool, Bool.and_eq_true, fCarryLe, fModEq, fLinLe, intAff, natAff,
             evalAtomBool, NatAff.eval, dotNat, dotInt, Nat.one_mul, Nat.zero_mul,
             Nat.add_zero, Nat.zero_add, Int.one_mul, Int.add_zero,
             decide_eq_true_eq,
             show (3 == 0) = false by decide, Bool.false_eq_true, ↓reduceIte]
  constructor
  · rintro ⟨hc, hm, hle⟩
    refine ⟨hc, ?_, ?_⟩
    · omega
    · have : -((px : Int) * (x : Int)) + (qy : Int) * (y : Int) ≤ (c0 : Int) := by
        simpa [Int.neg_mul] using hle
      omega
  · rintro ⟨hc, hm, hle⟩
    refine ⟨hc, ?_, ?_⟩
    · omega
    · rw [Int.neg_mul]; omega

/-! ## Section 8: Family I — Bounded-Carry Ternary Completion Phase-Transition Theorems (∀ x, ∃ y) -/

theorem cert_ternary_k0_r0_valid : checkCert cert_ternary_k0_r0 = true := by decide
theorem cert_ternary_k0_r1_valid : checkCert cert_ternary_k0_r1 = true := by decide
theorem cert_ternary_k0_r2_valid : checkCert cert_ternary_k0_r2 = true := by decide
theorem cert_ternary_k1_r0_valid : checkCert cert_ternary_k1_r0 = true := by decide
theorem cert_ternary_k1_r1_valid : checkCert cert_ternary_k1_r1 = true := by decide
theorem cert_ternary_k1_r2_valid : checkCert cert_ternary_k1_r2 = true := by decide
theorem cert_ternary_k2_r0_valid : checkCert cert_ternary_k2_r0 = true := by decide
theorem cert_ternary_k2_r1_valid : checkCert cert_ternary_k2_r1 = true := by decide
theorem cert_ternary_k2_r2_valid : checkCert cert_ternary_k2_r2 = true := by decide

/-- (K=0, r=0): Exact sharp slope 5/3 (3y ≤ 5x + 5) for zero-carry mod-3 completion. -/
theorem ternary_zero_carry_r0 (x : Nat) :
    ∃ y : Nat, x &&& y = 0 ∧ (x + y) % 3 = 0 ∧ 3 * y ≤ 5 * x + 5 := by
  rcases cert_sound cert_ternary_k0_r0 cert_ternary_k0_r0_valid [x] rfl with ⟨ys, hlen, hok⟩
  match ys, hlen with
  | [y], _ =>
    exact ⟨y, by simpa using (eval_ternary_k0_iff 0 3 5 5 x y).mp hok⟩

/-- Constructive executable Skolem witness for (K=0, r=0). -/
def skolem_k0_r0 (x : Nat) : Nat := (synthesizeY cert_ternary_k0_r0 [x]).getD 0 0

theorem skolem_k0_r0_spec (x : Nat) :
    x &&& skolem_k0_r0 x = 0 ∧ (x + skolem_k0_r0 x) % 3 = 0 ∧ 3 * skolem_k0_r0 x ≤ 5 * x + 5 := by
  have h := synthesizeY_sound cert_ternary_k0_r0 cert_ternary_k0_r0_valid [x] rfl
  unfold skolem_k0_r0
  generalize hy : synthesizeY cert_ternary_k0_r0 [x] = ys at h ⊢
  match ys, h with
  | [y], ⟨_, hok⟩ =>
    simpa using (eval_ternary_k0_iff 0 3 5 5 x y).mp hok

/-- (K=0, r=1): Exact sharp slope 5/3 (3y ≤ 5x + 5). -/
theorem ternary_zero_carry_r1 (x : Nat) :
    ∃ y : Nat, x &&& y = 0 ∧ (x + y) % 3 = 1 ∧ 3 * y ≤ 5 * x + 5 := by
  rcases cert_sound cert_ternary_k0_r1 cert_ternary_k0_r1_valid [x] rfl with ⟨ys, hlen, hok⟩
  match ys, hlen with
  | [y], _ =>
    exact ⟨y, by simpa using (eval_ternary_k0_iff 1 3 5 5 x y).mp hok⟩

/-- (K=0, r=2): Exact sharp slope 2 (y ≤ 2x + 2). -/
theorem ternary_zero_carry_r2 (x : Nat) :
    ∃ y : Nat, x &&& y = 0 ∧ (x + y) % 3 = 2 ∧ y ≤ 2 * x + 2 := by
  rcases cert_sound cert_ternary_k0_r2 cert_ternary_k0_r2_valid [x] rfl with ⟨ys, hlen, hok⟩
  match ys, hlen with
  | [y], _ =>
    exact ⟨y, by simpa using (eval_ternary_k0_iff 2 1 2 2 x y).mp hok⟩

/-- (K=1, r=0): Slope collapses from 5/3 to 1 (y ≤ x + 1). -/
theorem ternary_carry1_r0 (x : Nat) :
    ∃ y : Nat, carryCount x y false ≤ 1 ∧ (x + y) % 3 = 0 ∧ y ≤ x + 1 := by
  rcases cert_sound cert_ternary_k1_r0 cert_ternary_k1_r0_valid [x] rfl with ⟨ys, hlen, hok⟩
  match ys, hlen with
  | [y], _ =>
    exact ⟨y, by simpa using (eval_ternary_carry_iff 1 0 1 1 1 x y).mp hok⟩

/-- (K=1, r=1): Slope collapses from 5/3 to 1 (y ≤ x + 1). -/
theorem ternary_carry1_r1 (x : Nat) :
    ∃ y : Nat, carryCount x y false ≤ 1 ∧ (x + y) % 3 = 1 ∧ y ≤ x + 1 := by
  rcases cert_sound cert_ternary_k1_r1 cert_ternary_k1_r1_valid [x] rfl with ⟨ys, hlen, hok⟩
  match ys, hlen with
  | [y], _ =>
    exact ⟨y, by simpa using (eval_ternary_carry_iff 1 1 1 1 1 x y).mp hok⟩

/-- (K=1, r=2): 4× phase-transition collapse from slope 2 down to 1/2 (2y ≤ x + 4)! -/
theorem ternary_carry1_r2 (x : Nat) :
    ∃ y : Nat, carryCount x y false ≤ 1 ∧ (x + y) % 3 = 2 ∧ 2 * y ≤ x + 4 := by
  rcases cert_sound cert_ternary_k1_r2 cert_ternary_k1_r2_valid [x] rfl with ⟨ys, hlen, hok⟩
  match ys, hlen with
  | [y], _ =>
    exact ⟨y, by simpa using (eval_ternary_carry_iff 1 2 2 1 4 x y).mp hok⟩

/-- (K=2, r=0): Slope drops to 1/4 (4y ≤ x + 7), overtaking r=2! -/
theorem ternary_carry2_r0 (x : Nat) :
    ∃ y : Nat, carryCount x y false ≤ 2 ∧ (x + y) % 3 = 0 ∧ 4 * y ≤ x + 7 := by
  rcases cert_sound cert_ternary_k2_r0 cert_ternary_k2_r0_valid [x] rfl with ⟨ys, hlen, hok⟩
  match ys, hlen with
  | [y], _ =>
    exact ⟨y, by simpa using (eval_ternary_carry_iff 2 0 4 1 7 x y).mp hok⟩

/-- (K=2, r=1): Slope drops to 1/4 (4y ≤ x + 6), overtaking r=2! -/
theorem ternary_carry2_r1 (x : Nat) :
    ∃ y : Nat, carryCount x y false ≤ 2 ∧ (x + y) % 3 = 1 ∧ 4 * y ≤ x + 6 := by
  rcases cert_sound cert_ternary_k2_r1 cert_ternary_k2_r1_valid [x] rfl with ⟨ys, hlen, hok⟩
  match ys, hlen with
  | [y], _ =>
    exact ⟨y, by simpa using (eval_ternary_carry_iff 2 1 4 1 6 x y).mp hok⟩

/-- (K=2, r=2): Remains at slope 1/2 (2y ≤ x + 4), matched by lower bound below! -/
theorem ternary_carry2_r2 (x : Nat) :
    ∃ y : Nat, carryCount x y false ≤ 2 ∧ (x + y) % 3 = 2 ∧ 2 * y ≤ x + 4 := by
  rcases cert_sound cert_ternary_k2_r2 cert_ternary_k2_r2_valid [x] rfl with ⟨ys, hlen, hok⟩
  match ys, hlen with
  | [y], _ =>
    exact ⟨y, by simpa using (eval_ternary_carry_iff 2 2 2 1 4 x y).mp hok⟩

/-! ## Section 9: Family II — Matching Infinite Extremal Lower Bounds (∀ z y / ∀ x y) -/

theorem cert_lb_k0_r0_valid : checkCert cert_lb_k0_r0 = true := by decide
theorem cert_lb_k0_r1_valid : checkCert cert_lb_k0_r1 = true := by decide
theorem cert_lb_k0_r2_valid : checkCert cert_lb_k0_r2 = true := by decide
theorem cert_lb_k2_r2_valid : checkCert cert_lb_k2_r2 = true := by decide

/-- Infinite Matching Lower Bound for (K=0, r=0): on x = 3z + 2 = 3·2^(2k+1) - 1,
    every zero-carry multiple of 3 satisfies 3y ≥ 5x + 5, proving exact slope 5/3! -/
theorem ternary_zero_carry_r0_lower_bound (z y : Nat)
    (hp : (z + 1) &&& z = 0) (hz : z % 3 = 1)
    (hd : (3 * z + 2) &&& y = 0) (hm : (3 * z + 2 + y) % 3 = 0) :
    5 * (3 * z + 2) + 5 ≤ 3 * y := by
  have h := cert_sound_univ cert_lb_k0_r0 cert_lb_k0_r0_valid rfl [z, y] rfl
  simp only [cert_lb_k0_r0, List.getD_cons_zero, evalFormulaBool, Bool.or_eq_true,
             Bool.not_eq_true', Bool.and_eq_false_iff,
             fDisj, fModEq, fLinLe, intAff, natAff, evalAtomBool, NatAff.eval,
             dotNat, dotInt, Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
             Int.one_mul, Int.zero_mul, Int.add_zero,
             decide_eq_true_eq, show (3 == 0) = false by decide,
             Bool.false_eq_true, ↓reduceIte] at h
  rcases h with hneg | hle
  · exfalso
    rcases hneg with h1 | h2
    · exact absurd ((bitRel4Dec_andZero_iff (z + 1) z).mpr hp) (by simp [h1])
    · rcases h2 with h2 | h3
      · have : (z : Int) % 3 = 1 := by omega
        simp [this] at h2
      · rcases h3 with h3 | h4
        · exact absurd ((bitRel4Dec_andZero_iff (3 * z + 2) y).mpr hd) (by simp [h3])
        · have : (3 * (z : Int) + (y : Int)) % 3 = 1 := by omega
          simp [this] at h4
  · omega

/-- Infinite Matching Lower Bound for (K=0, r=1): on x = 3z + 2 = 3·2^(2k) - 1,
    every zero-carry completion ≡ 1 (mod 3) satisfies 3y ≥ 5x + 5, proving exact slope 5/3! -/
theorem ternary_zero_carry_r1_lower_bound (z y : Nat)
    (hp : (z + 1) &&& z = 0) (hz : z % 3 = 0)
    (hd : (3 * z + 2) &&& y = 0) (hm : (3 * z + 2 + y) % 3 = 1) :
    5 * (3 * z + 2) + 5 ≤ 3 * y := by
  have h := cert_sound_univ cert_lb_k0_r1 cert_lb_k0_r1_valid rfl [z, y] rfl
  simp only [cert_lb_k0_r1, List.getD_cons_zero, evalFormulaBool, Bool.or_eq_true,
             Bool.not_eq_true', Bool.and_eq_false_iff,
             fDisj, fModEq, fLinLe, intAff, natAff, evalAtomBool, NatAff.eval,
             dotNat, dotInt, Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
             Int.one_mul, Int.zero_mul, Int.add_zero,
             decide_eq_true_eq, show (3 == 0) = false by decide,
             Bool.false_eq_true, ↓reduceIte] at h
  rcases h with hneg | hle
  · exfalso
    rcases hneg with h1 | h2
    · exact absurd ((bitRel4Dec_andZero_iff (z + 1) z).mpr hp) (by simp [h1])
    · rcases h2 with h2 | h3
      · have : (z : Int) % 3 = 0 := by omega
        simp [this] at h2
      · rcases h3 with h3 | h4
        · exact absurd ((bitRel4Dec_andZero_iff (3 * z + 2) y).mpr hd) (by simp [h3])
        · have : (3 * (z : Int) + (y : Int)) % 3 = 2 := by omega
          simp [this] at h4
  · omega

/-- Infinite Matching Lower Bound for (K=0, r=2): on every Mersenne x = 2^k - 1,
    every zero-carry completion ≡ 2 (mod 3) satisfies y ≥ 2x + 2, proving exact slope 2! -/
theorem ternary_zero_carry_r2_lower_bound (x y : Nat)
    (hmer : x &&& (x + 1) = 0) (hd : x &&& y = 0) (hm : (x + y) % 3 = 2) :
    2 * x + 2 ≤ y := by
  have h := cert_sound_univ cert_lb_k0_r2 cert_lb_k0_r2_valid rfl [x, y] rfl
  simp only [cert_lb_k0_r2, List.getD_cons_zero, evalFormulaBool, Bool.or_eq_true,
             Bool.not_eq_true', Bool.and_eq_false_iff,
             fDisj, fModEq, fLinLe, intAff, natAff, evalAtomBool, NatAff.eval,
             dotNat, dotInt, Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
             Int.one_mul, Int.add_zero,
             decide_eq_true_eq, show (3 == 0) = false by decide,
             Bool.false_eq_true, ↓reduceIte] at h
  rcases h with hneg | hle
  · exfalso
    rcases hneg with h1 | h2
    · exact absurd ((bitRel4Dec_andZero_iff x (x + 1)).mpr hmer) (by simp [h1])
    · rcases h2 with h2 | h3
      · exact absurd ((bitRel4Dec_andZero_iff x y).mpr hd) (by simp [h2])
      · have : ((x : Int) + (y : Int)) % 3 = 2 := by omega
        simp [this] at h3
  · omega

/-- Infinite Phase-Transition Barrier for (K=2, r=2): on every Mersenne x = 2^k - 1,
    even with carry budget K=2, every completion ≡ 2 (mod 3) satisfies 2y ≥ x + 1! -/
theorem ternary_carry2_r2_lower_bound (x y : Nat)
    (hmer : x &&& (x + 1) = 0) (hc : carryCount x y false ≤ 2) (hm : (x + y) % 3 = 2) :
    x + 1 ≤ 2 * y := by
  have h := cert_sound_univ cert_lb_k2_r2 cert_lb_k2_r2_valid rfl [x, y] rfl
  simp only [cert_lb_k2_r2, List.getD_cons_zero, evalFormulaBool, Bool.or_eq_true,
             Bool.not_eq_true', Bool.and_eq_false_iff,
             fDisj, fCarryLe, fModEq, fLinLe, intAff, natAff, evalAtomBool, NatAff.eval,
             dotNat, dotInt, Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
             Int.one_mul, Int.add_zero,
             decide_eq_true_eq, show (3 == 0) = false by decide,
             Bool.false_eq_true, ↓reduceIte] at h
  rcases h with hneg | hle
  · exfalso
    rcases hneg with h1 | h2
    · exact absurd ((bitRel4Dec_andZero_iff x (x + 1)).mpr hmer) (by simp [h1])
    · rcases h2 with h2 | h3
      · simp [hc] at h2
      · have : ((x : Int) + (y : Int)) % 3 = 2 := by omega
        simp [this] at h3
  · omega

/-! ## Section 10: Family III — Mersenne-Collatz Affine Zero-Carry Rigidity (∀ x) -/

theorem cert_mersenne_collatz_3_valid : checkCert cert_mersenne_collatz_3 = true := by decide
theorem cert_mersenne_collatz_7_valid : checkCert cert_mersenne_collatz_7 = true := by decide
theorem cert_mersenne_collatz_15_valid : checkCert cert_mersenne_collatz_15 = true := by decide
theorem cert_mc3_pop_sparse_valid : checkCert cert_mc3_pop_sparse = true := by decide

theorem mersenne_collatz_rigidity_3 (x : Nat) :
    x &&& (3 * x + 1) = 0 ↔ (3 * x + 1) &&& (3 * x) = 0 := by
  have h := cert_sound_univ cert_mersenne_collatz_3 cert_mersenne_collatz_3_valid rfl [x] rfl
  simp only [cert_mersenne_collatz_3, List.getD_cons_zero, evalFormulaBool, Bool.and_eq_true,
             Bool.or_eq_true, Bool.not_eq_true', fDisj, natAff, evalAtomBool, NatAff.eval,
             dotNat, Nat.one_mul, Nat.add_zero, bitRel4Dec_andZero_iff] at h
  have ha := bitRel4Dec_andZero_iff x (3 * x + 1)
  have hb := bitRel4Dec_andZero_iff (3 * x + 1) (3 * x)
  constructor
  · intro h1
    rcases h.1 with hna | hok
    · exact absurd (ha.mpr h1) (by simp [hna])
    · exact hok
  · intro h2
    rcases h.2 with hnb | hok
    · exact absurd (hb.mpr h2) (by simp [hnb])
    · exact hok

theorem mersenne_collatz_rigidity_7 (x : Nat) :
    x &&& (7 * x + 1) = 0 ↔ (7 * x + 1) &&& (7 * x) = 0 := by
  have h := cert_sound_univ cert_mersenne_collatz_7 cert_mersenne_collatz_7_valid rfl [x] rfl
  simp only [cert_mersenne_collatz_7, List.getD_cons_zero, evalFormulaBool, Bool.and_eq_true,
             Bool.or_eq_true, Bool.not_eq_true', fDisj, natAff, evalAtomBool, NatAff.eval,
             dotNat, Nat.one_mul, Nat.add_zero, bitRel4Dec_andZero_iff] at h
  have ha := bitRel4Dec_andZero_iff x (7 * x + 1)
  have hb := bitRel4Dec_andZero_iff (7 * x + 1) (7 * x)
  constructor
  · intro h1
    rcases h.1 with hna | hok
    · exact absurd (ha.mpr h1) (by simp [hna])
    · exact hok
  · intro h2
    rcases h.2 with hnb | hok
    · exact absurd (hb.mpr h2) (by simp [hnb])
    · exact hok

theorem mersenne_collatz_rigidity_15 (x : Nat) :
    x &&& (15 * x + 1) = 0 ↔ (15 * x + 1) &&& (15 * x) = 0 := by
  have h := cert_sound_univ cert_mersenne_collatz_15 cert_mersenne_collatz_15_valid rfl [x] rfl
  simp only [cert_mersenne_collatz_15, List.getD_cons_zero, evalFormulaBool, Bool.and_eq_true,
             Bool.or_eq_true, Bool.not_eq_true', fDisj, natAff, evalAtomBool, NatAff.eval,
             dotNat, Nat.one_mul, Nat.add_zero, bitRel4Dec_andZero_iff] at h
  have ha := bitRel4Dec_andZero_iff x (15 * x + 1)
  have hb := bitRel4Dec_andZero_iff (15 * x + 1) (15 * x)
  constructor
  · intro h1
    rcases h.1 with hna | hok
    · exact absurd (ha.mpr h1) (by simp [hna])
    · exact hok
  · intro h2
    rcases h.2 with hnb | hok
    · exact absurd (hb.mpr h2) (by simp [hnb])
    · exact hok

theorem mersenne_collatz_popcount_sparse_3 (x : Nat) (hx : x &&& (3 * x + 1) = 0) :
    popcount (3 * x + 1) % 2 = 1 ∧ x &&& (2 * x) = 0 := by
  have h := cert_sound_univ cert_mc3_pop_sparse cert_mc3_pop_sparse_valid rfl [x] rfl
  simp only [cert_mc3_pop_sparse, List.getD_cons_zero, evalFormulaBool, Bool.or_eq_true,
             Bool.not_eq_true', Bool.and_eq_true, fDisj, fPopMod, natAff, evalAtomBool,
             evalPopSum, NatAff.eval, dotNat, Nat.one_mul, Nat.add_zero, Int.one_mul,
             Int.add_zero, bitRel4Dec_andZero_iff, decide_eq_true_eq,
             show (2 == 0) = false by decide, Bool.false_eq_true, ↓reduceIte] at h
  rcases h with hna | ⟨hpop, hsp⟩
  · exact absurd ((bitRel4Dec_andZero_iff x (3 * x + 1)).mpr hx) (by simp [hna])
  · exact ⟨by omega, hsp⟩

/-! ## Section 11: Family IV — Carry-Parity, Popcount-Mod, and Carry-Word Coupling Laws -/

theorem cert_carry1_parity_disj_valid : checkCert cert_carry1_parity_disj = true := by decide
theorem cert_carry_word_zero_valid : checkCert cert_carry_word_zero = true := by decide
theorem cert_sparse_triple_evil_valid : checkCert cert_sparse_triple_evil = true := by decide

/-- Mixing carryLe, popMod, and itRel4: when at most 1 carry occurs,
    even carry-defect parity is equivalent to zero-carry disjointness! -/
theorem bounded_carry1_parity_iff_disjoint (x y : Nat) (hc : carryCount x y false ≤ 1) :
    (((popcount x : Int) + (popcount y : Int) - (popcount (x + y) : Int)) % 2 = 0) ↔
      x &&& y = 0 := by
  have h := cert_sound_univ cert_carry1_parity_disj cert_carry1_parity_disj_valid rfl [x, y] rfl
  simp only [cert_carry1_parity_disj, List.getD_cons_zero, evalFormulaBool, Bool.or_eq_true,
             Bool.not_eq_true', Bool.and_eq_true, fCarryLe, fPopMod, fDisj, natAff,
             evalAtomBool, evalPopSum, NatAff.eval, dotNat, Nat.one_mul, Nat.zero_mul,
             Nat.add_zero, Nat.zero_add, Int.one_mul, Int.neg_mul, Int.add_zero,
             decide_eq_true_eq, show (2 == 0) = false by decide,
             Bool.false_eq_true, ↓reduceIte] at h
  rcases h with hnc | ⟨h1, h2⟩
  · exfalso; simp [hc] at hnc
  · have hpar_eq : ((popcount x : Int) + ((popcount y : Int) + -(popcount (x + y) : Int))) =
        ((popcount x : Int) + (popcount y : Int) - (popcount (x + y) : Int)) := by omega
    rw [hpar_eq] at h1 h2
    have hd := bitRel4Dec_andZero_iff x y
    constructor
    · intro hp
      rcases h1 with hnp | hok
      · simp [hp] at hnp
      · exact hd.mp hok
    · intro hxy
      rcases h2 with hnd | hok
      · exact absurd (hd.mpr hxy) (by simp [hnd])
      · exact hok

/-- Full 3-input itRel4 (maskXor3Eq0): exact carry-word (x+y) ^^^ x ^^^ y vanishes iff x &&& y = 0. -/
theorem carry_word_zero_iff_disjoint (x y : Nat) :
    ((x + y) ^^^ x ^^^ y = 0) ↔ x &&& y = 0 := by
  have h := cert_sound_univ cert_carry_word_zero cert_carry_word_zero_valid rfl [x, y] rfl
  simp only [cert_carry_word_zero, List.getD_cons_zero, evalFormulaBool, Bool.and_eq_true,
             Bool.or_eq_true, Bool.not_eq_true', fXor3Zero, fDisj, natAff, evalAtomBool,
             NatAff.eval, dotNat, Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add] at h
  have hx := bitRel4Dec_xor3Eq0_iff (x + y) x y
  have hd := bitRel4Dec_andZero_iff x y
  constructor
  · intro h1
    rcases h.1 with hnx | hok
    · exact absurd (hx.mpr h1) (by simp [hnx])
    · exact hd.mp hok
  · intro h2
    rcases h.2 with hnd | hok
    · exact absurd (hd.mpr h2) (by simp [hnd])
    · exact hx.mp hok

/-- Every binary-sparse number (x &&& 2x = 0) has an evil triple (popcount (3x) even). -/
theorem sparse_triple_evil (x : Nat) (hsp : x &&& (2 * x) = 0) :
    popcount (3 * x) % 2 = 0 := by
  have h := cert_sound_univ cert_sparse_triple_evil cert_sparse_triple_evil_valid rfl [x] rfl
  simp only [cert_sparse_triple_evil, List.getD_cons_zero, evalFormulaBool, Bool.or_eq_true,
             Bool.not_eq_true', fDisj, fPopMod, natAff, evalAtomBool, evalPopSum,
             NatAff.eval, dotNat, Nat.one_mul, Nat.add_zero, Int.one_mul, Int.add_zero,
             decide_eq_true_eq, show (2 == 0) = false by decide,
             Bool.false_eq_true, ↓reduceIte] at h
  rcases h with hns | hok
  · exact absurd ((bitRel4Dec_andZero_iff x (2 * x)).mpr hsp) (by simp [hns])
  · omega

/-! ## Section 12: Kernel-Checked Non-Vacuity Witnesses, Sharpness Counterexamples,
       and Hostile Certificate Mutation Tests -/

/-- Non-vacuity: concrete witnesses showing every conditional theorem's hypotheses are inhabited,
    plus exact equality attainment for every lower bound! -/
theorem nonvacuity_lb_k0_r0 :
    let z := 1; let y := 10
    (z + 1) &&& z = 0 ∧ z % 3 = 1 ∧ (3 * z + 2) &&& y = 0 ∧ (3 * z + 2 + y) % 3 = 0 ∧
      3 * y = 5 * (3 * z + 2) + 5 := by decide

theorem nonvacuity_lb_k0_r0_large :
    let z := 31; let y := 160
    (z + 1) &&& z = 0 ∧ z % 3 = 1 ∧ (3 * z + 2) &&& y = 0 ∧ (3 * z + 2 + y) % 3 = 0 ∧
      3 * y = 5 * (3 * z + 2) + 5 := by decide

theorem nonvacuity_lb_k0_r1 :
    let z := 3; let y := 20
    (z + 1) &&& z = 0 ∧ z % 3 = 0 ∧ (3 * z + 2) &&& y = 0 ∧ (3 * z + 2 + y) % 3 = 1 ∧
      3 * y = 5 * (3 * z + 2) + 5 := by decide

theorem nonvacuity_lb_k0_r2 :
    let x := 15; let y := 32
    x &&& (x + 1) = 0 ∧ x &&& y = 0 ∧ (x + y) % 3 = 2 ∧ y = 2 * x + 2 := by decide

theorem nonvacuity_lb_k2_r2 :
    let x := 127; let y := 64
    x &&& (x + 1) = 0 ∧ carryCount x y false ≤ 2 ∧ (x + y) % 3 = 2 ∧ 2 * y = x + 1 := by decide

theorem nonvacuity_mersenne_collatz :
    (21 &&& (3 * 21 + 1) = 0) ∧ (73 &&& (7 * 73 + 1) = 0) ∧ (273 &&& (15 * 273 + 1) = 0) := by
  decide

theorem nonvacuity_skolem_k0_r0_examples :
    skolem_k0_r0 0 = 0 ∧ skolem_k0_r0 1 = 2 ∧ skolem_k0_r0 5 = 10 ∧
    skolem_k0_r0 23 = 40 ∧ skolem_k0_r0 95 = 160 := by decide

/-- Sharpness counterexamples (proving constants & hypotheses CANNOT be weakened by even 1): -/
theorem sharp_k0_r0_fails_at_5 :
    ¬ ∃ y : Nat, 5 &&& y = 0 ∧ (5 + y) % 3 = 0 ∧ 3 * y ≤ 5 * 5 + 4 := by
  rintro ⟨y, hd, hm, hle⟩
  have hchk : ∀ y : Fin 10, ¬ (5 &&& y.val = 0 ∧ (5 + y.val) % 3 = 0) := by decide
  exact hchk ⟨y, by omega⟩ ⟨hd, hm⟩

theorem sharp_k0_r1_fails_at_2 :
    ¬ ∃ y : Nat, 2 &&& y = 0 ∧ (2 + y) % 3 = 1 ∧ 3 * y ≤ 5 * 2 + 4 := by
  rintro ⟨y, hd, hm, hle⟩
  have hchk : ∀ y : Fin 5, ¬ (2 &&& y.val = 0 ∧ (2 + y.val) % 3 = 1) := by decide
  exact hchk ⟨y, by omega⟩ ⟨hd, hm⟩

theorem sharp_k0_r2_fails_at_0 :
    ¬ ∃ y : Nat, 0 &&& y = 0 ∧ (0 + y) % 3 = 2 ∧ y ≤ 2 * 0 + 1 := by
  rintro ⟨y, _, hm, hle⟩; omega

theorem sharp_k1_r0_fails_at_1 :
    ¬ ∃ y : Nat, carryCount 1 y false ≤ 1 ∧ (1 + y) % 3 = 0 ∧ y ≤ 1 := by
  rintro ⟨y, _, hm, hle⟩; omega

theorem sharp_k1_r2_fails_at_0 :
    ¬ ∃ y : Nat, carryCount 0 y false ≤ 1 ∧ (0 + y) % 3 = 2 ∧ 2 * y ≤ 0 + 3 := by
  rintro ⟨y, _, hm, hle⟩; omega

theorem sharp_k2_r0_fails_at_1 :
    ¬ ∃ y : Nat, carryCount 1 y false ≤ 2 ∧ (1 + y) % 3 = 0 ∧ 4 * y ≤ 1 + 6 := by
  rintro ⟨y, _, hm, hle⟩; omega

theorem sharp_k2_r1_fails_at_2 :
    ¬ ∃ y : Nat, carryCount 2 y false ≤ 2 ∧ (2 + y) % 3 = 1 ∧ 4 * y ≤ 2 + 5 := by
  rintro ⟨y, _, hm, hle⟩; omega

/-- Non-Mersenne a = 5 breaks affine zero-carry rigidity at x = 1! -/
theorem sharp_non_mersenne_5_counterexample :
    1 &&& (5 * 1 + 1) = 0 ∧ (5 * 1 + 1) &&& (5 * 1) ≠ 0 := by decide

/-- Relaxing carryCount ≤ 1 to ≤ 2 breaks parity-iff-disjointness at (3, 1)! -/
theorem sharp_carry2_breaks_parity_disjoint :
    carryCount 3 1 false ≤ 2 ∧
    (((popcount 3 : Int) + (popcount 1 : Int) - (popcount (3 + 1) : Int)) % 2 = 0) ∧
    3 &&& 1 ≠ 0 := by decide

/-! ### Kernel-Checked Hostile Certificate Mutation Tests (checkCert bad = false) -/

def badCert_empty : Cert := { d := 1, e := 1, entries := [] }

def badCert_bad_baseY : Cert :=
  match cert_ternary_k0_r2.entries with
  | e0 :: rest => { cert_ternary_k0_r2 with entries := { e0 with baseY := [0] } :: rest }
  | [] => cert_ternary_k0_r2

def badCert_wrong_nextIdx : Cert :=
  match cert_ternary_k0_r2.entries with
  | e0 :: rest =>
    match e0.trans with
    | (u0, n0) :: tRest =>
      { cert_ternary_k0_r2 with
        entries := { e0 with trans := (u0, (n0 + 1) % cert_ternary_k0_r2.entries.length) :: tRest } :: rest }
    | [] => cert_ternary_k0_r2
  | [] => cert_ternary_k0_r2

def badCert_tightened_false_root : Cert :=
  match cert_ternary_k0_r2.entries with
  | e0 :: rest =>
    let badF : Formula :=
      .and (fDisj (natAff [1, 0]) (natAff [0, 1]))
           (.and (fModEq [1, 1] 3 2) (fLinLe [-2, 1] 1))
    { cert_ternary_k0_r2 with entries := { e0 with formula := badF } :: rest }
  | [] => cert_ternary_k0_r2

def badCert_empty_uList : Cert :=
  match cert_ternary_k0_r2.entries with
  | e0 :: rest =>
    match e0.trans with
    | (_, n0) :: tRest =>
      { cert_ternary_k0_r2 with entries := { e0 with trans := ([], n0) :: tRest } :: rest }
    | [] => cert_ternary_k0_r2
  | [] => cert_ternary_k0_r2

def badCert_truncated_trans : Cert :=
  match cert_ternary_k0_r2.entries with
  | e0 :: rest =>
    { cert_ternary_k0_r2 with entries := { e0 with trans := e0.trans.take 1 } :: rest }
  | [] => cert_ternary_k0_r2

theorem hostile_reject_empty          : checkCert badCert_empty = false := by decide
theorem hostile_reject_bad_baseY      : checkCert badCert_bad_baseY = false := by decide
theorem hostile_reject_wrong_nextIdx  : checkCert badCert_wrong_nextIdx = false := by decide
theorem hostile_reject_false_root     : checkCert badCert_tightened_false_root = false := by decide
theorem hostile_reject_empty_uList    : checkCert badCert_empty_uList = false := by decide
theorem hostile_reject_truncated      : checkCert badCert_truncated_trans = false := by decide

/-! ## Section 13: Exhaustive Axiom Audits -/


end CPRTE

