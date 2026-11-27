/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DualrailTropicalCarryHorizon.Defs

/-!
# Theorems (`dualrail-tropical-carry-horizon`)

Full proofs of the headline infinite theorems of Dual-rail signed-digit addition with exact carry horizon and potential certificates.
-/

namespace DualRailCompiler

theorem drVal_drNeg (d : DR) : drVal (drNeg d) = - drVal d := by
  cases d with
  | mk p n => cases p <;> cases n <;> decide

theorem prefixVal_zero (w : Nat) : prefixVal w drStreamZero = 0 := by
  induction w with
  | zero => rfl
  | succ w ih =>
    simp [prefixVal, drStreamZero, drVal, ih]

theorem prefixVal_neg (w : Nat) (x : Nat → DR) :
    prefixVal w (drStreamNeg x) = - prefixVal w x := by
  induction w with
  | zero => rfl
  | succ w ih =>
    simp only [prefixVal, drStreamNeg, drVal_drNeg, ih]
    rw [Int.neg_mul]
    omega

theorem natBitSum_mod_two_pow (n : Nat) : ∀ k : Nat,
    natBitSum k (fun i => n.testBit i) = n % 2 ^ k := by
  intro k
  induction k with
  | zero => simp [natBitSum, Nat.mod_one]
  | succ k ih =>
    simp only [natBitSum, ih]
    have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := by rw [Nat.pow_succ]
    have hdiv : n % 2 ^ (k + 1) = n % 2 ^ k + ((n / 2 ^ k) % 2) * 2 ^ k := by
      have h1 : 2 ^ k * (n / 2 ^ k) + n % 2 ^ k = n := Nat.div_add_mod n (2 ^ k)
      have h2 : 2 * (n / 2 ^ k / 2) + (n / 2 ^ k) % 2 = n / 2 ^ k := Nat.div_add_mod (n / 2 ^ k) 2
      have hdecomp : n = (n % 2 ^ k + ((n / 2 ^ k) % 2) * 2 ^ k) + (2 ^ k * 2) * (n / 2 ^ k / 2) := by
        calc n = 2 ^ k * (n / 2 ^ k) + n % 2 ^ k := h1.symm
          _ = 2 ^ k * (2 * (n / 2 ^ k / 2) + (n / 2 ^ k) % 2) + n % 2 ^ k := by rw [h2]
          _ = (2 ^ k * 2) * (n / 2 ^ k / 2) + 2 ^ k * ((n / 2 ^ k) % 2) + n % 2 ^ k := by
              rw [Nat.mul_add, Nat.mul_assoc]
          _ = (n % 2 ^ k + ((n / 2 ^ k) % 2) * 2 ^ k) + (2 ^ k * 2) * (n / 2 ^ k / 2) := by
              rw [Nat.mul_comm (2 ^ k) ((n / 2 ^ k) % 2)]; omega
      have hlt1 : n % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
      have hlt2 : (n / 2 ^ k) % 2 < 2 := Nat.mod_lt _ (by decide)
      have hlt : n % 2 ^ k + ((n / 2 ^ k) % 2) * 2 ^ k < 2 ^ k * 2 := by
        have hle : ((n / 2 ^ k) % 2) * 2 ^ k ≤ 1 * 2 ^ k := Nat.mul_le_mul_right _ (by omega)
        omega
      rw [hpow]
      conv => lhs; rw [hdecomp]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    have hbit : (if n.testBit k then 1 else 0) = (n / 2 ^ k) % 2 := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      have hlt : (n / 2 ^ k) % 2 < 2 := Nat.mod_lt _ (by decide)
      by_cases h1 : (n / 2 ^ k) % 2 = 1 <;> simp [h1] <;> omega
    rw [hdiv, hbit]

theorem prefixVal_eq_natBitSum_sub (w : Nat) (x : Nat → DR) :
    prefixVal w x =
      (natBitSum w (fun i => (x i).1) : Int) - (natBitSum w (fun i => (x i).2) : Int) := by
  induction w with
  | zero => rfl
  | succ w ih =>
    simp only [prefixVal, natBitSum, ih, drVal]
    by_cases hp : (x w).1 = true <;> by_cases hn : (x w).2 = true <;>
      simp [hp, hn] <;> omega

/-- Exact bridge theorem connecting BitVec w dual-rail pairs to stream prefixVal. -/
theorem prefixVal_ofBitVecPair {w : Nat} (P N : BitVec w) :
    prefixVal w (ofBitVecPair P N) = (P.toNat : Int) - (N.toNat : Int) := by
  rw [prefixVal_eq_natBitSum_sub]
  have hP : natBitSum w (fun i => (ofBitVecPair P N i).1) = P.toNat := by
    have heq : (fun i => (ofBitVecPair P N i).1) = (fun i => P.toNat.testBit i) := by
      funext i
      simp [ofBitVecPair, BitVec.getLsbD]
    rw [heq, natBitSum_mod_two_pow, Nat.mod_eq_of_lt P.isLt]
  have hN : natBitSum w (fun i => (ofBitVecPair P N i).2) = N.toNat := by
    have heq : (fun i => (ofBitVecPair P N i).2) = (fun i => N.toNat.testBit i) := by
      funext i
      simp [ofBitVecPair, BitVec.getLsbD]
    rw [heq, natBitSum_mod_two_pow, Nat.mod_eq_of_lt N.isLt]
  rw [hP, hN]

-- ============================================================================
-- SECTION 2: ENGINE 1 — Finite-State Carry-Potential & Relational Equivalence Compiler
-- ============================================================================

namespace DRTransducer

/--
  META-THEOREM 1A (Carry-Potential Finite -> Infinite Lifting Theorem):
  A finite single-slice potential check lifts to an exact integer conservation law
  across ALL bit-widths w : Nat and ALL input streams u : Nat -> α.
-/
theorem potential_lift_all_widths (T : DRTransducer α m) (target : α → Int) (φ : Fin m → Int)
    (hcert : T.ValidPotential target φ) (q : Fin m) (u : Nat → α) (w : Nat) :
    prefixVal w (T.runOut q u) + ((2 ^ w : Nat) : Int) * φ (T.runState q u w) =
      prefixSum target w u + φ q := by
  induction w with
  | zero =>
    simp [prefixVal, prefixSum, runState]
  | succ w ih =>
    have hstep := hcert (T.runState q u w) (u w)
    have hpow : ((2 ^ (w + 1) : Nat) : Int) = 2 * ((2 ^ w : Nat) : Int) := by
      have : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
      omega
    simp only [prefixVal, prefixSum, runOut, runState]
    rw [hpow]
    have hmul :
        (drVal (T.step (T.runState q u w) (u w)).2 +
          2 * φ (T.step (T.runState q u w) (u w)).1) * ((2 ^ w : Nat) : Int) =
        (target (u w) + φ (T.runState q u w)) * ((2 ^ w : Nat) : Int) :=
      congrArg (· * ((2 ^ w : Nat) : Int)) hstep
    have hdistL :
        (drVal (T.step (T.runState q u w) (u w)).2 +
          2 * φ (T.step (T.runState q u w) (u w)).1) * ((2 ^ w : Nat) : Int) =
        drVal (T.step (T.runState q u w) (u w)).2 * ((2 ^ w : Nat) : Int) +
          2 * ((2 ^ w : Nat) : Int) * φ (T.step (T.runState q u w) (u w)).1 := by
      rw [Int.add_mul, Int.mul_assoc, Int.mul_comm (φ _) ((2 ^ w : Nat) : Int), ← Int.mul_assoc]
    have hdistR :
        (target (u w) + φ (T.runState q u w)) * ((2 ^ w : Nat) : Int) =
        target (u w) * ((2 ^ w : Nat) : Int) +
          ((2 ^ w : Nat) : Int) * φ (T.runState q u w) := by
      rw [Int.add_mul, Int.mul_comm (φ _) ((2 ^ w : Nat) : Int)]
    rw [hdistL, hdistR] at hmul
    omega

/--
  META-THEOREM 1B (Relational Bisimulation Finite -> Infinite Lifting Theorem):
  A finite relational difference-potential ψ on Fin m₁ × Fin m₂ certifies exact
  integer discrepancy and mod-2^w semantic equivalence between ANY two transducers
  T₁, T₂ across ALL bit-widths w : Nat.
-/
theorem relational_bisim_lift (T₁ : DRTransducer α m₁) (T₂ : DRTransducer α m₂)
    (ψ : Fin m₁ → Fin m₂ → Int) (hcert : ValidRelInvariant T₁ T₂ ψ)
    (q₁ : Fin m₁) (q₂ : Fin m₂) (u : Nat → α) (w : Nat) :
    prefixVal w (T₁.runOut q₁ u) - prefixVal w (T₂.runOut q₂ u) +
      ((2 ^ w : Nat) : Int) * ψ (T₁.runState q₁ u w) (T₂.runState q₂ u w) = ψ q₁ q₂ := by
  induction w with
  | zero =>
    simp [prefixVal, runState]
  | succ w ih =>
    have hstep := hcert (T₁.runState q₁ u w) (T₂.runState q₂ u w) (u w)
    have hpow : ((2 ^ (w + 1) : Nat) : Int) = 2 * ((2 ^ w : Nat) : Int) := by
      have : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
      omega
    simp only [prefixVal, runOut, runState]
    rw [hpow]
    have hmul :
        (drVal (T₁.step (T₁.runState q₁ u w) (u w)).2 -
          drVal (T₂.step (T₂.runState q₂ u w) (u w)).2 +
          2 * ψ (T₁.step (T₁.runState q₁ u w) (u w)).1
                (T₂.step (T₂.runState q₂ u w) (u w)).1) * ((2 ^ w : Nat) : Int) =
        ψ (T₁.runState q₁ u w) (T₂.runState q₂ u w) * ((2 ^ w : Nat) : Int) :=
      congrArg (· * ((2 ^ w : Nat) : Int)) hstep
    have hdistL :
        (drVal (T₁.step (T₁.runState q₁ u w) (u w)).2 -
          drVal (T₂.step (T₂.runState q₂ u w) (u w)).2 +
          2 * ψ (T₁.step (T₁.runState q₁ u w) (u w)).1
                (T₂.step (T₂.runState q₂ u w) (u w)).1) * ((2 ^ w : Nat) : Int) =
        drVal (T₁.step (T₁.runState q₁ u w) (u w)).2 * ((2 ^ w : Nat) : Int) -
        drVal (T₂.step (T₂.runState q₂ u w) (u w)).2 * ((2 ^ w : Nat) : Int) +
        2 * ((2 ^ w : Nat) : Int) *
          ψ (T₁.step (T₁.runState q₁ u w) (u w)).1
            (T₂.step (T₂.runState q₂ u w) (u w)).1 := by
      rw [Int.add_mul, Int.sub_mul, Int.mul_assoc,
          Int.mul_comm (ψ _ _) ((2 ^ w : Nat) : Int), ← Int.mul_assoc]
    have hdistR :
        ψ (T₁.runState q₁ u w) (T₂.runState q₂ u w) * ((2 ^ w : Nat) : Int) =
        ((2 ^ w : Nat) : Int) * ψ (T₁.runState q₁ u w) (T₂.runState q₂ u w) :=
      Int.mul_comm _ _
    rw [hdistL, hdistR] at hmul
    omega

/-- Helper: integer congruence modulo M from an exact multiple difference. -/
theorem emod_eq_of_sub_eq_mul (a b M k : Int) (h : a - b = M * k) :
    a % M = b % M := by
  have ha : a = b + M * k := by omega
  rw [ha, Int.add_mul_emod_self_left]

/-- Modular equivalence corollary: zero initial relational potential yields exact mod-2^w equality ∀ w. -/
theorem relational_bisim_mod_eq (T₁ : DRTransducer α m₁) (T₂ : DRTransducer α m₂)
    (ψ : Fin m₁ → Fin m₂ → Int) (hcert : ValidRelInvariant T₁ T₂ ψ)
    (hinit : ψ T₁.init T₂.init = 0) (u : Nat → α) (w : Nat) :
    (prefixVal w (T₁.runOut T₁.init u)) % ((2 ^ w : Nat) : Int) =
    (prefixVal w (T₂.runOut T₂.init u)) % ((2 ^ w : Nat) : Int) := by
  have h := relational_bisim_lift T₁ T₂ ψ hcert T₁.init T₂.init u w
  rw [hinit] at h
  apply emod_eq_of_sub_eq_mul _ _ _ (- ψ (T₁.runState T₁.init u w) (T₂.runState T₂.init u w))
  have hneg : ((2 ^ w : Nat) : Int) * (- ψ (T₁.runState T₁.init u w) (T₂.runState T₂.init u w)) =
      - (((2 ^ w : Nat) : Int) * ψ (T₁.runState T₁.init u w) (T₂.runState T₂.init u w)) :=
    Int.mul_neg _ _
  omega

-- ============================================================================
-- SECTION 3: ENGINE 2 — Pair-Lyapunov Synchronization & Tropical Rail-Horizon Compiler
-- ============================================================================

theorem runState_add (T : DRTransducer α m) (q : Fin m) (u : Nat → α) (s k : Nat) :
    T.runState q u (s + k) = T.runState (T.runState q u s) (shiftStream s u) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h1 : s + (k + 1) = (s + k) + 1 := by omega
    rw [h1]
    simp [runState, shiftStream, ih]

/-- Pair-Lyapunov descent: after k steps, rank drops to 0 once k >= R q₁ q₂. -/
theorem horizon_rank_drop_gen (T : DRTransducer α m) (H : Nat) (R : Fin m → Fin m → Nat)
    (hcert : T.ValidHorizonCert H R) :
    ∀ (k : Nat) (q₁ q₂ : Fin m) (u : Nat → α),
      R q₁ q₂ ≤ k → T.runState q₁ u k = T.runState q₂ u k := by
  intro k
  induction k with
  | zero =>
    intro q₁ q₂ u hle
    exact hcert.2.2.1 q₁ q₂ (by omega)
  | succ k ih =>
    intro q₁ q₂ u hle
    by_cases heq : q₁ = q₂
    · subst heq; rfl
    · have hlt := hcert.2.2.2 q₁ q₂ (u 0) heq
      have hle' : R (T.step q₁ (u 0)).1 (T.step q₂ (u 0)).1 ≤ k := by omega
      have h1 : T.runState q₁ u (1 + k) =
          T.runState (T.step q₁ (u 0)).1 (shiftStream 1 u) k := by
        simpa [runState] using runState_add T q₁ u 1 k
      have h2 : T.runState q₂ u (1 + k) =
          T.runState (T.step q₂ (u 0)).1 (shiftStream 1 u) k := by
        simpa [runState] using runState_add T q₂ u 1 k
      have hcomm : k + 1 = 1 + k := by omega
      rw [hcomm, h1, h2]
      exact ih _ _ (shiftStream 1 u) hle'

theorem runState_eq_of_prefix_eq (T : DRTransducer α m) (q : Fin m) (u v : Nat → α) (k : Nat)
    (h : ∀ j, j < k → u j = v j) :
    T.runState q u k = T.runState q v k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [runState]
    rw [ih (fun j hj => h j (by omega)), h k (by omega)]

/--
  META-THEOREM 2A (Pair-Lyapunov Infinite-Width Carry-Boundedness Lifting Theorem):
  If ValidHorizonCert T H R holds (a finite check of size m^2 * |α|), then for EVERY
  bit index i : Nat and EVERY two input streams u, v agreeing on the causal window
  [i - H, i], the output digit at bit i is BIT-FOR-BIT IDENTICAL regardless of all
  bits at indices < i - H!
-/
theorem horizon_cert_carry_bounded (T : DRTransducer α m) (H : Nat) (R : Fin m → Fin m → Nat)
    (hcert : T.ValidHorizonCert H R) (u v : Nat → α) (i : Nat)
    (hwin : ∀ j, i - H ≤ j → j ≤ i → u j = v j) :
    T.runOut T.init u i = T.runOut T.init v i := by
  simp only [runOut]
  have hui : u i = v i := hwin i (by omega) (by omega)
  rw [hui]
  suffices hst : T.runState T.init u i = T.runState T.init v i by rw [hst]
  by_cases hi : i < H
  · have hzero : i - H = 0 := by omega
    apply runState_eq_of_prefix_eq
    intro j hj
    exact hwin j (by omega) (by omega)
  · have hsplit : i = (i - H) + H := by omega
    rw [hsplit, runState_add, runState_add]
    have hshift : ∀ j, j < H → shiftStream (i - H) u j = shiftStream (i - H) v j := by
      intro j hj
      exact hwin (i - H + j) (by omega) (by omega)
    rw [runState_eq_of_prefix_eq T (T.runState T.init v (i - H))
          (shiftStream (i - H) v) (shiftStream (i - H) u) H (fun j hj => (hshift j hj).symm)]
    exact horizon_rank_drop_gen T H R hcert H _ _ (shiftStream (i - H) u) (hcert.2.1 _ _)

end DRTransducer

/--
  META-THEOREM 2B (Tropical 2x2 Matrix Composition Theorem):
  Composing any two rail-bounded dual-rail stream operators multiplies their
  2x2 tropical lag matrices in the max-plus semiring across ALL bit indices i : Nat.
-/
theorem railBounded_comp {f g : (Nat → DR) → (Nat → DR)} {A B : TropicalMat2}
    (hf : RailBounded f A) (hg : RailBounded g B) :
    RailBounded (fun x => f (g x)) (A.mul B) := by
  constructor
  · intro x y i hp hn
    apply hf.1 (g x) (g y) i
    · intro k hkl hku
      apply hg.1 x y k
      · intro j hjl hju
        apply hp j
        · simp only [TropicalMat2.mul]; omega
        · omega
      · intro j hjl hju
        apply hn j
        · simp only [TropicalMat2.mul]; omega
        · omega
    · intro k hkl hku
      apply hg.2 x y k
      · intro j hjl hju
        apply hp j
        · simp only [TropicalMat2.mul]; omega
        · omega
      · intro j hjl hju
        apply hn j
        · simp only [TropicalMat2.mul]; omega
        · omega
  · intro x y i hp hn
    apply hf.2 (g x) (g y) i
    · intro k hkl hku
      apply hg.1 x y k
      · intro j hjl hju
        apply hp j
        · simp only [TropicalMat2.mul]; omega
        · omega
      · intro j hjl hju
        apply hn j
        · simp only [TropicalMat2.mul]; omega
        · omega
    · intro k hkl hku
      apply hg.2 x y k
      · intro j hjl hju
        apply hp j
        · simp only [TropicalMat2.mul]; omega
        · omega
      · intro j hjl hju
        apply hn j
        · simp only [TropicalMat2.mul]; omega
        · omega

/-- Any RailBounded operator with matrix M is globally carry-bounded by M.maxLag. -/
theorem railBounded_maxLag {f : (Nat → DR) → (Nat → DR)} {M : TropicalMat2}
    (hf : RailBounded f M) (x y : Nat → DR) (i : Nat)
    (hwin : ∀ j, i - M.maxLag ≤ j → j ≤ i → x j = y j) :
    f x i = f y i := by
  have h1 : (f x i).1 = (f y i).1 := by
    apply hf.1 x y i
    · intro j hjl hju
      have := hwin j (by simp only [TropicalMat2.maxLag]; omega) hju
      rw [this]
    · intro j hjl hju
      have := hwin j (by simp only [TropicalMat2.maxLag]; omega) hju
      rw [this]
  have h2 : (f x i).2 = (f y i).2 := by
    apply hf.2 x y i
    · intro j hjl hju
      have := hwin j (by simp only [TropicalMat2.maxLag]; omega) hju
      rw [this]
    · intro j hjl hju
      have := hwin j (by simp only [TropicalMat2.maxLag]; omega) hju
      rw [this]
  exact Prod.ext h1 h2

-- ============================================================================
-- SECTION 4: 2-Stage PPM/PNM Dual-Rail Avizienis Adder & Finite Kernel Certificates
-- ============================================================================

theorem aviz_validPotential :
    avizTransducer.ValidPotential (fun a => drVal a.1 + drVal a.2) avizPhi := by
  intro q ⟨⟨p1, n1⟩, ⟨p2, n2⟩⟩
  revert q p1 n1 p2 n2
  decide

theorem aviz_comm_bisim :
    DRTransducer.ValidRelInvariant avizTransducer avizCommTransducer
      (fun q₁ q₂ => avizPhi q₁ - avizPhi q₂) := by
  intro q₁ q₂ ⟨⟨p1, n1⟩, ⟨p2, n2⟩⟩
  revert q₁ q₂ p1 n1 p2 n2
  decide

theorem aviz_ripple_bisim :
    DRTransducer.ValidRelInvariant avizUnsignedTransducer rippleTransducer
      (fun q₁ q₂ => avizPhi q₁ - (q₂.val : Int)) := by
  intro q₁ q₂ ⟨p1, p2⟩
  revert q₁ q₂ p1 p2
  decide

theorem aviz_validHorizon :
    avizTransducer.ValidHorizonCert 2 avizRank := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · intro q₁ q₂ ⟨⟨p1, n1⟩, ⟨p2, n2⟩⟩ hne
    revert q₁ q₂ p1 n1 p2 n2 hne
    decide

theorem aviz_one_guard_flush :
    ∀ q : Fin 4, (avizTransducer.step q ((false, false), (false, false))).1 = ⟨0, by decide⟩ := by
  decide

-- Infinite-Width Semantic Theorems for avizAdd (lifted via Engine 1!)

theorem prefixSum_add (w : Nat) (x y : Nat → DR) :
    prefixSum (fun a : DR × DR => drVal a.1 + drVal a.2) w (fun i => (x i, y i)) =
      prefixVal w x + prefixVal w y := by
  induction w with
  | zero => rfl
  | succ w ih =>
    simp only [prefixSum, prefixVal, ih]
    rw [Int.add_mul]
    omega

/-- Exact integer equation for avizAdd across ALL bit-widths w : Nat. -/
theorem avizAdd_exact_int (w : Nat) (x y : Nat → DR) :
    prefixVal w (avizAdd x y) +
      ((2 ^ w : Nat) : Int) * avizPhi (avizTransducer.runState avizTransducer.init (fun i => (x i, y i)) w) =
    prefixVal w x + prefixVal w y := by
  have h := avizTransducer.potential_lift_all_widths
    (fun a => drVal a.1 + drVal a.2) avizPhi aviz_validPotential
    avizTransducer.init (fun i => (x i, y i)) w
  rw [prefixSum_add] at h
  have h0 : avizPhi avizTransducer.init = 0 := by decide
  rw [h0, Int.add_zero] at h
  exact h

/-- Exact mod-2^w semantics of avizAdd across ALL bit-widths w : Nat. -/
theorem avizAdd_mod_eq (w : Nat) (x y : Nat → DR) :
    (prefixVal w (avizAdd x y)) % ((2 ^ w : Nat) : Int) =
    (prefixVal w x + prefixVal w y) % ((2 ^ w : Nat) : Int) := by
  have h := avizAdd_exact_int w x y
  apply DRTransducer.emod_eq_of_sub_eq_mul _ _ _
    (- avizPhi (avizTransducer.runState avizTransducer.init (fun i => (x i, y i)) w))
  have hneg : ((2 ^ w : Nat) : Int) *
      (- avizPhi (avizTransducer.runState avizTransducer.init (fun i => (x i, y i)) w)) =
      - (((2 ^ w : Nat) : Int) *
        avizPhi (avizTransducer.runState avizTransducer.init (fun i => (x i, y i)) w)) :=
    Int.mul_neg _ _
  omega

/--
  ONE-GUARD-BIT EXACT Z FLUSH THEOREM (∀ w : Nat):
  If x w = (false, false) and y w = (false, false), then the (w + 1)-bit output of
  avizAdd equals prefixVal w x + prefixVal w y EXACTLY IN Z (zero residual carry)!
-/
theorem avizAdd_exact_flush_Z (w : Nat) (x y : Nat → DR)
    (hx : x w = (false, false)) (hy : y w = (false, false)) :
    prefixVal (w + 1) (avizAdd x y) = prefixVal w x + prefixVal w y := by
  have h := avizAdd_exact_int (w + 1) x y
  have hflush :
      avizTransducer.runState avizTransducer.init (fun i => (x i, y i)) (w + 1) =
        ⟨0, by decide⟩ := by
    simp only [DRTransducer.runState, hx, hy]
    exact aviz_one_guard_flush _
  rw [hflush] at h
  have hphi0 : avizPhi ⟨0, by decide⟩ = 0 := by decide
  rw [hphi0, Int.mul_zero, Int.add_zero] at h
  simp only [prefixVal, hx, hy, drVal, Int.sub_self, Int.zero_mul, Int.add_zero] at h
  exact h

/-- Exact BitVec w modular addition theorem for Dual-Rail Avizienis addition (∀ w : Nat). -/
theorem avizAdd_bitVec_mod_eq {w : Nat} (P₁ N₁ P₂ N₂ : BitVec w) :
    (prefixVal w (avizAdd (ofBitVecPair P₁ N₁) (ofBitVecPair P₂ N₂))) % ((2 ^ w : Nat) : Int) =
    (((P₁.toNat : Int) - (N₁.toNat : Int)) + ((P₂.toNat : Int) - (N₂.toNat : Int))) %
      ((2 ^ w : Nat) : Int) := by
  rw [avizAdd_mod_eq, prefixVal_ofBitVecPair, prefixVal_ofBitVecPair]

/-- Direct Relational Bisimulation Commutation Theorem (∀ w : Nat). -/
theorem avizAdd_comm_mod (w : Nat) (x y : Nat → DR) :
    (prefixVal w (avizAdd x y)) % ((2 ^ w : Nat) : Int) =
    (prefixVal w (avizAdd y x)) % ((2 ^ w : Nat) : Int) := by
  have h := DRTransducer.relational_bisim_mod_eq avizTransducer avizCommTransducer
    (fun q₁ q₂ => avizPhi q₁ - avizPhi q₂) aviz_comm_bisim (by decide) (fun i => (x i, y i)) w
  have hcomm : avizCommTransducer.runOut avizCommTransducer.init (fun i => (x i, y i)) =
      avizAdd y x := by
    funext k
    have hst : ∀ n,
        avizCommTransducer.runState avizCommTransducer.init (fun i => (x i, y i)) n =
        avizTransducer.runState avizTransducer.init (fun i => (y i, x i)) n := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [DRTransducer.runState, DRTransducer.runState, ih]
        rfl
    simp only [avizAdd, DRTransducer.runOut]
    rw [hst k]
    rfl
  rw [hcomm] at h
  exact h

/-- Direct Relational Bisimulation Equivalence with Ripple-Carry Binary Addition (∀ w : Nat). -/
theorem avizAdd_eq_ripple_mod (w : Nat) (p₁ p₂ : Nat → Bool) :
    (prefixVal w (avizAdd (fun i => (p₁ i, false)) (fun i => (p₂ i, false)))) % ((2 ^ w : Nat) : Int) =
    (prefixVal w (rippleTransducer.runOut rippleTransducer.init (fun i => (p₁ i, p₂ i)))) %
      ((2 ^ w : Nat) : Int) := by
  have h := DRTransducer.relational_bisim_mod_eq avizUnsignedTransducer rippleTransducer
    (fun q₁ q₂ => avizPhi q₁ - (q₂.val : Int)) aviz_ripple_bisim (by decide)
    (fun i => (p₁ i, p₂ i)) w
  have hsame : avizUnsignedTransducer.runOut avizUnsignedTransducer.init (fun i => (p₁ i, p₂ i)) =
      avizAdd (fun i => (p₁ i, false)) (fun i => (p₂ i, false)) := by
    funext k
    have hst : ∀ n,
        avizUnsignedTransducer.runState avizUnsignedTransducer.init (fun i => (p₁ i, p₂ i)) n =
        avizTransducer.runState avizTransducer.init
          (fun i => ((p₁ i, false), (p₂ i, false))) n := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [DRTransducer.runState, DRTransducer.runState, ih]
        rfl
    simp only [avizAdd, DRTransducer.runOut]
    rw [hst k]
    rfl
  rw [hsame] at h
  exact h

/-- Infinite-width H = 2 carry-boundedness of avizAdd directly from Pair-Lyapunov certificate. -/
theorem avizAdd_horizon2 (x₁ y₁ x₂ y₂ : Nat → DR) (i : Nat)
    (hwin : ∀ j, i - 2 ≤ j → j ≤ i → x₁ j = x₂ j ∧ y₁ j = y₂ j) :
    avizAdd x₁ y₁ i = avizAdd x₂ y₂ i := by
  apply DRTransducer.horizon_cert_carry_bounded avizTransducer 2 avizRank aviz_validHorizon
    (fun k => (x₁ k, y₁ k)) (fun k => (x₂ k, y₂ k)) i
  intro j hjl hju
  have h := hwin j hjl hju
  exact Prod.ext h.1 h.2

-- ============================================================================
-- SECTION 5: Exact Per-Rail Tropical Lag Matrices & Rank-1 Closed Form ∀ d >= 1
-- ============================================================================

-- Helper lemmas exposing the exact 2-stage dataflow of avizTransducer:
--   cPos_{k+1} = (ppmCell p1_k p2_k n1_k).1
--   cNeg_{k+1} = (pnmCell cPos_k (ppmCell p1_k p2_k n1_k).2 n2_k).1
--   out_k      = ((pnmCell cPos_k (ppmCell p1_k p2_k n1_k).2 n2_k).2, cNeg_k)

theorem finCPos_stateToFin (a b : Bool) : finCPos (stateToFin a b) = a := by
  cases a <;> cases b <;> decide

theorem finCNeg_stateToFin (a b : Bool) : finCNeg (stateToFin a b) = b := by
  cases a <;> cases b <;> decide

theorem aviz_cPos_succ (x y : Nat → DR) (k : Nat) :
    finCPos (avizTransducer.runState avizTransducer.init (fun i => (x i, y i)) (k + 1)) =
      (ppmCell (x k).1 (y k).1 (x k).2).1 := by
  simp [DRTransducer.runState, avizTransducer, finCPos_stateToFin]

theorem aviz_cPos_zero (x y : Nat → DR) :
    finCPos (avizTransducer.runState avizTransducer.init (fun i => (x i, y i)) 0) = false :=
  rfl

theorem aviz_cNeg_succ (x y : Nat → DR) (k : Nat) :
    finCNeg (avizTransducer.runState avizTransducer.init (fun i => (x i, y i)) (k + 1)) =
      (pnmCell
        (finCPos (avizTransducer.runState avizTransducer.init (fun i => (x i, y i)) k))
        (ppmCell (x k).1 (y k).1 (x k).2).2
        (y k).2).1 := by
  simp [DRTransducer.runState, avizTransducer, finCNeg_stateToFin]

theorem aviz_cNeg_zero (x y : Nat → DR) :
    finCNeg (avizTransducer.runState avizTransducer.init (fun i => (x i, y i)) 0) = false :=
  rfl

theorem avizAdd_fst (x y : Nat → DR) (k : Nat) :
    (avizAdd x y k).1 =
      (pnmCell
        (finCPos (avizTransducer.runState avizTransducer.init (fun i => (x i, y i)) k))
        (ppmCell (x k).1 (y k).1 (x k).2).2
        (y k).2).2 := by
  simp [avizAdd, DRTransducer.runOut, avizTransducer]

theorem avizAdd_snd (x y : Nat → DR) (k : Nat) :
    (avizAdd x y k).2 =
      finCNeg (avizTransducer.runState avizTransducer.init (fun i => (x i, y i)) k) := by
  simp [avizAdd, DRTransducer.runOut, avizTransducer]

/-- Port 1 (left operand) has exact tropical rail-lag matrix A1 = [[1, 1], [2, 2]]. -/
theorem avizPort1_railBounded (y : Nat → DR) :
    RailBounded (fun x => avizAdd x y) matPort1 := by
  constructor
  · intro x₁ x₂ i hp hn
    rw [avizAdd_fst, avizAdd_fst]
    have hpi : (x₁ i).1 = (x₂ i).1 := hp i (by simp [matPort1]) (by omega)
    have hni : (x₁ i).2 = (x₂ i).2 := hn i (by simp [matPort1]) (by omega)
    have hc : finCPos (avizTransducer.runState avizTransducer.init (fun k => (x₁ k, y k)) i) =
              finCPos (avizTransducer.runState avizTransducer.init (fun k => (x₂ k, y k)) i) := by
      cases i with
      | zero => rw [aviz_cPos_zero, aviz_cPos_zero]
      | succ k =>
        rw [aviz_cPos_succ, aviz_cPos_succ]
        have hpk := hp k (by simp [matPort1]) (by omega)
        have hnk := hn k (by simp [matPort1]) (by omega)
        rw [hpk, hnk]
    rw [hc, hpi, hni]
  · intro x₁ x₂ i hp hn
    rw [avizAdd_snd, avizAdd_snd]
    cases i with
    | zero => rw [aviz_cNeg_zero, aviz_cNeg_zero]
    | succ k =>
      rw [aviz_cNeg_succ, aviz_cNeg_succ]
      have hpk : (x₁ k).1 = (x₂ k).1 := hp k (by simp [matPort1]) (by omega)
      have hnk : (x₁ k).2 = (x₂ k).2 := hn k (by simp [matPort1]) (by omega)
      have hc : finCPos (avizTransducer.runState avizTransducer.init (fun m => (x₁ m, y m)) k) =
                finCPos (avizTransducer.runState avizTransducer.init (fun m => (x₂ m, y m)) k) := by
        cases k with
        | zero => rw [aviz_cPos_zero, aviz_cPos_zero]
        | succ k' =>
          rw [aviz_cPos_succ, aviz_cPos_succ]
          have hpk' := hp k' (by simp [matPort1]) (by omega)
          have hnk' := hn k' (by simp [matPort1]) (by omega)
          rw [hpk', hnk']
      rw [hc, hpk, hnk]

/-- Port 2 (right operand) has exact tropical rail-lag matrix A2 = [[1, 0], [2, 1]]! -/
theorem avizPort2_railBounded (y : Nat → DR) :
    RailBounded (fun x => avizAdd y x) matPort2 := by
  constructor
  · intro x₁ x₂ i hp hn
    rw [avizAdd_fst, avizAdd_fst]
    have hpi : (x₁ i).1 = (x₂ i).1 := hp i (by simp [matPort2]) (by omega)
    have hni : (x₁ i).2 = (x₂ i).2 := hn i (by simp [matPort2]) (by omega)
    have hc : finCPos (avizTransducer.runState avizTransducer.init (fun k => (y k, x₁ k)) i) =
              finCPos (avizTransducer.runState avizTransducer.init (fun k => (y k, x₂ k)) i) := by
      cases i with
      | zero => rw [aviz_cPos_zero, aviz_cPos_zero]
      | succ k =>
        rw [aviz_cPos_succ, aviz_cPos_succ]
        have hpk := hp k (by simp [matPort2]) (by omega)
        rw [hpk]
    rw [hc, hpi, hni]
  · intro x₁ x₂ i hp hn
    rw [avizAdd_snd, avizAdd_snd]
    cases i with
    | zero => rw [aviz_cNeg_zero, aviz_cNeg_zero]
    | succ k =>
      rw [aviz_cNeg_succ, aviz_cNeg_succ]
      have hpk : (x₁ k).1 = (x₂ k).1 := hp k (by simp [matPort2]) (by omega)
      have hnk : (x₁ k).2 = (x₂ k).2 := hn k (by simp [matPort2]) (by omega)
      have hc : finCPos (avizTransducer.runState avizTransducer.init (fun m => (y m, x₁ m)) k) =
                finCPos (avizTransducer.runState avizTransducer.init (fun m => (y m, x₂ m)) k) := by
        cases k with
        | zero => rw [aviz_cPos_zero, aviz_cPos_zero]
        | succ k' =>
          rw [aviz_cPos_succ, aviz_cPos_succ]
          have hpk' := hp k' (by simp [matPort2]) (by omega)
          rw [hpk']
      rw [hc, hpk, hnk]

/-- Dual-rail negation has zero carry horizon (matrix [[0,0],[0,0]]). -/
theorem drStreamNeg_railBounded : RailBounded drStreamNeg ⟨0, 0, 0, 0⟩ := by
  constructor
  · intro x y i _ hn
    simp only [drStreamNeg, drNeg]
    exact hn i (by omega) (by omega)
  · intro x y i hp _
    simp only [drStreamNeg, drNeg]
    exact hp i (by omega) (by omega)

/--
  MAIN TROPICAL RANK-1 CLOSED-FORM THEOREM (∀ d >= 1, ∀ port words w in {p1, p2}^d):
  Because both A1 = [0;1] ⊗ [1,1] and A2 = [0;1] ⊗ [1,0] are tropical rank-1 matrices,
  the exact tropical product along ANY port word (outer ++ [inner]) of depth d = outer.length + 1
  collapses to the exact closed form with scalar sum S = outer.length + countP1 outer!
-/
theorem chainMat_closed_form (outer : List Port) (inner : Port) :
    let S := outer.length + countP1 outer
    chainMat outer inner =
      ⟨S + 1, S + inner.p1Bit, S + 2, S + 1 + inner.p1Bit⟩ := by
  induction outer with
  | nil =>
    cases inner <;> rfl
  | cons p rest ih =>
    simp only [chainMat, ih]
    cases p <;> cases inner <;>
      simp only [Port.mat, matPort1, matPort2, TropicalMat2.mul, countP1, Port.p1Bit, List.length_cons] <;>
      congr 1 <;> omega

/-- Exact closed-form maximum horizon H(w) = d + 1 + countP1(outer) where d = outer.length + 1. -/
theorem chainMat_maxLag (outer : List Port) (inner : Port) :
    (chainMat outer inner).maxLag = (outer.length + 1) + 1 + countP1 outer := by
  rw [chainMat_closed_form]
  cases inner <;> simp [TropicalMat2.maxLag, Port.p1Bit] <;> omega

/--
  UNIVERSAL ARBITRARY-DEPTH PORT-CHAIN UPPER BOUND (∀ d >= 1, ∀ w in {p1, p2}^d):
  Every depth-d chain of avizAdd gates satisfies RailBounded with exact matrix chainMat.
-/
theorem evalPortChain_railBounded (stages : List (Port × (Nat → DR)))
    (inner : Port) (yInner : Nat → DR) :
    RailBounded (evalPortChain stages inner yInner) (chainMat (stages.map Prod.fst) inner) := by
  induction stages with
  | nil =>
    cases inner
    · exact avizPort1_railBounded yInner
    · exact avizPort2_railBounded yInner
  | cons hd rest ih =>
    cases hd with
    | mk p y =>
      cases p
      · exact railBounded_comp (f := fun z => avizAdd z y) (g := evalPortChain rest inner yInner)
          (avizPort1_railBounded y) ih
      · exact railBounded_comp (f := fun z => avizAdd y z) (g := evalPortChain rest inner yInner)
          (avizPort2_railBounded y) ih

/-- Corollary: Right-associated chain of depth d = k + 1 has carry horizon <= d + 1! -/
theorem rightChain_horizon_bound (ys : List (Nat → DR)) (yInner : Nat → DR) :
    RailBounded
      (evalPortChain (ys.map (fun y => (Port.p2, y))) .p2 yInner)
      ⟨ys.length + 1, ys.length, ys.length + 2, ys.length + 1⟩ := by
  have hmap : ∀ (l : List (Nat → DR)),
      (l.map (fun y => (Port.p2, y))).map Prod.fst = List.replicate l.length Port.p2 := by
    intro l
    induction l with
    | nil => rfl
    | cons _ tl ih => simp [List.replicate_succ, ih]
  have hcnt : ∀ n, countP1 (List.replicate n Port.p2) = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simpa [List.replicate_succ, countP1] using ih
  have h := evalPortChain_railBounded (ys.map (fun y => (Port.p2, y))) .p2 yInner
  rw [hmap ys, chainMat_closed_form] at h
  simpa [List.length_replicate, hcnt, Port.p1Bit] using h

-- ============================================================================
-- SECTION 6: Arbitrary-Depth DRExpr Algebra & Horizon-Halving Equivalence Compiler
-- ============================================================================

theorem emod_neg_congr (a b M : Int) (h : a % M = b % M) :
    (- a) % M = (- b) % M := by
  have ha : M * (a / M) + a % M = a := Int.mul_ediv_add_emod a M
  have hb : M * (b / M) + b % M = b := Int.mul_ediv_add_emod b M
  apply DRTransducer.emod_eq_of_sub_eq_mul _ _ M (b / M - a / M)
  rw [Int.mul_sub]
  omega

theorem emod_add_congr (a₁ b₁ a₂ b₂ M : Int)
    (h₁ : a₁ % M = b₁ % M) (h₂ : a₂ % M = b₂ % M) :
    (a₁ + a₂) % M = (b₁ + b₂) % M := by
  have ha₁ : M * (a₁ / M) + a₁ % M = a₁ := Int.mul_ediv_add_emod a₁ M
  have hb₁ : M * (b₁ / M) + b₁ % M = b₁ := Int.mul_ediv_add_emod b₁ M
  have ha₂ : M * (a₂ / M) + a₂ % M = a₂ := Int.mul_ediv_add_emod a₂ M
  have hb₂ : M * (b₂ / M) + b₂ % M = b₂ := Int.mul_ediv_add_emod b₂ M
  apply DRTransducer.emod_eq_of_sub_eq_mul _ _ M ((a₁ / M - b₁ / M) + (a₂ / M - b₂ / M))
  rw [Int.mul_add, Int.mul_sub, Int.mul_sub]
  omega

/--
  UNIVERSAL ARBITRARY-DEPTH SOUNDNESS THEOREM (∀ d, ∀ w : Nat):
  Every arbitrary-depth dual-rail circuit e : DRExpr n evaluates modulo 2^w to its
  exact ideal integer algebra expression evalInt w env e, across ALL bit-widths w!
-/
theorem evalDR_mod_eq_evalInt (w : Nat) (env : Fin n → Nat → DR) (e : DRExpr n) :
    (prefixVal w (evalDR env e)) % ((2 ^ w : Nat) : Int) =
    (evalInt w env e) % ((2 ^ w : Nat) : Int) := by
  induction e with
  | zero =>
    simp [evalDR, evalInt, prefixVal_zero]
  | var i =>
    rfl
  | neg e ih =>
    simp only [evalDR, evalInt, prefixVal_neg]
    exact emod_neg_congr _ _ _ ih
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [evalDR, evalInt]
    rw [avizAdd_mod_eq]
    exact emod_add_congr _ _ _ _ _ ih₁ ih₂
  | sub e₁ e₂ ih₁ ih₂ =>
    simp only [evalDR, evalInt, avizSub]
    rw [avizAdd_mod_eq, prefixVal_neg]
    have hneg := emod_neg_congr _ _ _ ih₂
    have hadd := emod_add_congr _ _ _ _ _ ih₁ hneg
    have hsub : evalInt w env e₁ + -evalInt w env e₂ = evalInt w env e₁ - evalInt w env e₂ := by
      omega
    rw [hsub] at hadd
    exact hadd

/-- Exact Algebraic Laws for avizAdd / avizNeg across ALL widths w : Nat. -/
theorem avizAdd_assoc_mod (w : Nat) (x y z : Nat → DR) :
    (prefixVal w (avizAdd (avizAdd x y) z)) % ((2 ^ w : Nat) : Int) =
    (prefixVal w (avizAdd x (avizAdd y z))) % ((2 ^ w : Nat) : Int) := by
  let env : Fin 3 → Nat → DR := fun i => match i.val with | 0 => x | 1 => y | _ => z
  have h1 := evalDR_mod_eq_evalInt w env (.add (.add (.var ⟨0, by decide⟩) (.var ⟨1, by decide⟩)) (.var ⟨2, by decide⟩))
  have h2 := evalDR_mod_eq_evalInt w env (.add (.var ⟨0, by decide⟩) (.add (.var ⟨1, by decide⟩) (.var ⟨2, by decide⟩)))
  simp only [evalDR, evalInt, env] at h1 h2
  rw [h1, h2]
  congr 1
  omega

theorem avizNeg_add_mod (w : Nat) (x y : Nat → DR) :
    (prefixVal w (drStreamNeg (avizAdd x y))) % ((2 ^ w : Nat) : Int) =
    (prefixVal w (avizAdd (drStreamNeg x) (drStreamNeg y))) % ((2 ^ w : Nat) : Int) := by
  let env : Fin 2 → Nat → DR := fun i => match i.val with | 0 => x | _ => y
  have h1 := evalDR_mod_eq_evalInt w env (.neg (.add (.var ⟨0, by decide⟩) (.var ⟨1, by decide⟩)))
  have h2 := evalDR_mod_eq_evalInt w env (.add (.neg (.var ⟨0, by decide⟩)) (.neg (.var ⟨1, by decide⟩)))
  simp only [evalDR, evalInt, env] at h1 h2
  rw [h1, h2]
  congr 1
  omega

theorem avizAdd_neg_cancel_mod (w : Nat) (x : Nat → DR) :
    (prefixVal w (avizAdd x (drStreamNeg x))) % ((2 ^ w : Nat) : Int) = 0 := by
  rw [avizAdd_mod_eq, prefixVal_neg]
  have h0 : prefixVal w x + -prefixVal w x = 0 := by omega
  rw [h0]
  simp

-- Horizon-Halving Equivalence Compiler:
-- Flattens ANY DRExpr n by pushing all negations to leaves and emitting a
-- strictly RIGHT-ASSOCIATED Port-2 chain (cutting chain horizon from 2d to d + 1!).

theorem atomsInt_append (w : Nat) (env : Fin n → Nat → DR) (l₁ l₂ : List (Bool × Fin n)) :
    atomsInt w env (l₁ ++ l₂) = atomsInt w env l₁ + atomsInt w env l₂ := by
  induction l₁ with
  | nil => simp [atomsInt]
  | cons hd tl ih =>
    cases hd with
    | mk b i =>
      cases b <;> simp only [List.cons_append, atomsInt, ih] <;> omega

theorem atomsInt_flatten (w : Nat) (env : Fin n → Nat → DR) (e : DRExpr n) :
    ∀ negSign : Bool,
      atomsInt w env (flattenAtoms negSign e) =
        if negSign then - evalInt w env e else evalInt w env e := by
  induction e with
  | zero =>
    intro s; cases s <;> simp [flattenAtoms, atomsInt, evalInt]
  | var i =>
    intro s; cases s <;> simp [flattenAtoms, atomsInt, evalInt]
  | neg e ih =>
    intro s
    simp only [flattenAtoms, evalInt, ih (!s)]
    cases s <;> simp
  | add e₁ e₂ ih₁ ih₂ =>
    intro s
    simp only [flattenAtoms, evalInt, atomsInt_append, ih₁ s, ih₂ s]
    cases s <;> simp <;> omega
  | sub e₁ e₂ ih₁ ih₂ =>
    intro s
    simp only [flattenAtoms, evalInt, atomsInt_append, ih₁ s, ih₂ (!s)]
    cases s <;> simp <;> omega

theorem evalRightChain_mod_eq_atomsInt (w : Nat) (env : Fin n → Nat → DR)
    (l : List (Bool × Fin n)) :
    (prefixVal w (evalRightChain env l)) % ((2 ^ w : Nat) : Int) =
    (atomsInt w env l) % ((2 ^ w : Nat) : Int) := by
  induction l with
  | nil =>
    simp [evalRightChain, atomsInt, prefixVal_zero]
  | cons a rest ih =>
    cases rest with
    | nil =>
      cases a with
      | mk b i =>
        cases b <;> simp [evalRightChain, evalAtom, atomsInt, prefixVal_neg]
    | cons a₂ rest₂ =>
      simp only [evalRightChain]
      rw [avizAdd_mod_eq]
      have ha : prefixVal w (evalAtom env a) =
          (if a.1 then - prefixVal w (env a.2) else prefixVal w (env a.2)) := by
        cases a with
        | mk b i => cases b <;> simp [evalAtom, prefixVal_neg]
      rw [ha]
      have hsum : (if a.1 then - prefixVal w (env a.2) else prefixVal w (env a.2)) +
          atomsInt w env (a₂ :: rest₂) = atomsInt w env (a :: a₂ :: rest₂) := by
        cases a with
        | mk b i => cases b <;> simp [atomsInt]
      rw [← hsum]
      exact emod_add_congr _ _ _ _ _ rfl ih

/--
  MAIN COMPILER EQUIVALENCE THEOREM (∀ arbitrary-depth e : DRExpr n, ∀ width w : Nat):
  Compiling e into a flat right-associated Port-2 chain preserves exact mod-2^w semantics
  for ALL bit-widths w and ALL environments env!
-/
theorem compileRight_equiv_all_widths (w : Nat) (env : Fin n → Nat → DR) (e : DRExpr n) :
    (prefixVal w (evalRightChain env (flattenAtoms false e))) % ((2 ^ w : Nat) : Int) =
    (prefixVal w (evalDR env e)) % ((2 ^ w : Nat) : Int) := by
  rw [evalRightChain_mod_eq_atomsInt, atomsInt_flatten, evalDR_mod_eq_evalInt]
  simp

/--
  Per-rail simultaneous horizon induction for right-associated Port-2 chains:
  For ANY atom list l of length m (i.e. d = m - 1 addition stages):
    - p_out at bit i depends ONLY on input environments in [i - (m - 1), i],
    - n_out at bit i depends ONLY on input environments in [i - m, i]!
  (Hence for d >= 1 stages, carry horizon is <= d + 1, halving the 2d left-chain horizon!)
-/
theorem evalRightChain_rail_horizon (env₁ env₂ : Fin n → Nat → DR) (l : List (Bool × Fin n)) :
    (∀ i : Nat,
      (∀ (v : Fin n) (j : Nat), i - (l.length - 1) ≤ j → j ≤ i → env₁ v j = env₂ v j) →
      (evalRightChain env₁ l i).1 = (evalRightChain env₂ l i).1) ∧
    (∀ i : Nat,
      (∀ (v : Fin n) (j : Nat), i - l.length ≤ j → j ≤ i → env₁ v j = env₂ v j) →
      (evalRightChain env₁ l i).2 = (evalRightChain env₂ l i).2) := by
  induction l with
  | nil =>
    exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | cons a rest ih =>
    cases rest with
    | nil =>
      constructor
      · intro i hwin
        have heq := hwin a.2 i (by simp) (by omega)
        cases a with
        | mk b v => cases b <;> simp [evalRightChain, evalAtom, drStreamNeg, heq]
      · intro i hwin
        have heq := hwin a.2 i (by simp) (by omega)
        cases a with
        | mk b v => cases b <;> simp [evalRightChain, evalAtom, drStreamNeg, heq]
    | cons a₂ rest₂ =>
      -- Let t = a₂ :: rest₂ (length k + 1 >= 1), so a :: t has length k + 2.
      -- Step 1: replace left operand (evalAtom env₁ a) with (evalAtom env₂ a) via Port 1 (lag 1 on p, 2 on n)
      -- Step 2: replace right operand (evalRightChain env₁ t) with (evalRightChain env₂ t) via Port 2 (lag (1,0) on p, (2,1) on n)
      have hatom : ∀ (j : Nat), env₁ a.2 j = env₂ a.2 j → evalAtom env₁ a j = evalAtom env₂ a j := by
        intro j hj
        cases a with
        | mk b v => cases b <;> simp [evalAtom, drStreamNeg, hj]
      constructor
      · intro i hwin
        simp only [evalRightChain]
        -- Intermediate: avizAdd (evalAtom env₁ a) (evalRightChain env₁ t) i .1
        --            = avizAdd (evalAtom env₂ a) (evalRightChain env₁ t) i .1
        --            = avizAdd (evalAtom env₂ a) (evalRightChain env₂ t) i .1
        have hstep1 :
            (avizAdd (evalAtom env₁ a) (evalRightChain env₁ (a₂ :: rest₂)) i).1 =
            (avizAdd (evalAtom env₂ a) (evalRightChain env₁ (a₂ :: rest₂)) i).1 := by
          apply (avizPort1_railBounded (evalRightChain env₁ (a₂ :: rest₂))).1 _ _ i
          · intro j hjl hju
            have h := hatom j (hwin a.2 j (by simp [matPort1] at hjl ⊢; omega) hju)
            rw [h]
          · intro j hjl hju
            have h := hatom j (hwin a.2 j (by simp [matPort1] at hjl ⊢; omega) hju)
            rw [h]
        have hstep2 :
            (avizAdd (evalAtom env₂ a) (evalRightChain env₁ (a₂ :: rest₂)) i).1 =
            (avizAdd (evalAtom env₂ a) (evalRightChain env₂ (a₂ :: rest₂)) i).1 := by
          apply (avizPort2_railBounded (evalAtom env₂ a)).1 _ _ i
          · intro k hkl hku
            apply ih.1 k
            intro v j hjl hju
            apply hwin v j (by simp only [matPort2, List.length_cons] at hkl hjl ⊢; omega) (by omega)
          · intro k hkl hku
            apply ih.2 k
            intro v j hjl hju
            apply hwin v j (by simp only [matPort2, List.length_cons] at hkl hjl ⊢; omega) (by omega)
        exact hstep1.trans hstep2
      · intro i hwin
        simp only [evalRightChain]
        have hstep1 :
            (avizAdd (evalAtom env₁ a) (evalRightChain env₁ (a₂ :: rest₂)) i).2 =
            (avizAdd (evalAtom env₂ a) (evalRightChain env₁ (a₂ :: rest₂)) i).2 := by
          apply (avizPort1_railBounded (evalRightChain env₁ (a₂ :: rest₂))).2 _ _ i
          · intro j hjl hju
            have h := hatom j (hwin a.2 j (by simp only [matPort1, List.length_cons] at hjl ⊢; omega) hju)
            rw [h]
          · intro j hjl hju
            have h := hatom j (hwin a.2 j (by simp only [matPort1, List.length_cons] at hjl ⊢; omega) hju)
            rw [h]
        have hstep2 :
            (avizAdd (evalAtom env₂ a) (evalRightChain env₁ (a₂ :: rest₂)) i).2 =
            (avizAdd (evalAtom env₂ a) (evalRightChain env₂ (a₂ :: rest₂)) i).2 := by
          apply (avizPort2_railBounded (evalAtom env₂ a)).2 _ _ i
          · intro k hkl hku
            apply ih.1 k
            intro v j hjl hju
            apply hwin v j (by simp only [matPort2, List.length_cons] at hkl hjl ⊢; omega) (by omega)
          · intro k hkl hku
            apply ih.2 k
            intro v j hjl hju
            apply hwin v j (by simp only [matPort2, List.length_cons] at hkl hjl ⊢; omega) (by omega)
        exact hstep1.trans hstep2

/--
  MAIN COMPILER CARRY-HORIZON BOUND (∀ arbitrary-depth e : DRExpr n, ∀ bit index i):
  Every compiled expression `compileRight e` with m = (flattenAtoms false e).length leaf
  occurrences (i.e. d = m - 1 addition stages) has carry horizon <= m = d + 1!
  Combined with `compileRight_equiv_all_widths`, this compiles ANY arbitrary-depth
  dual-rail expression into a semantically identical circuit with 2x smaller chain horizon!
-/
theorem evalRightChain_horizon_le (env₁ env₂ : Fin n → Nat → DR) (l : List (Bool × Fin n)) (i : Nat)
    (hwin : ∀ (v : Fin n) (j : Nat), i - l.length ≤ j → j ≤ i → env₁ v j = env₂ v j) :
    evalRightChain env₁ l i = evalRightChain env₂ l i := by
  have h := evalRightChain_rail_horizon env₁ env₂ l
  apply Prod.ext
  · exact h.1 i (fun v j hjl hju => hwin v j (by omega) hju)
  · exact h.2 i hwin

-- ============================================================================
-- SECTION 7: Exact Sharpness, Constructive TailPulse Lower Bound & Impossibility
-- ============================================================================

theorem tailPulse_base (inner : Port) :
    TailPulse 2
      (evalPortChain [] inner sideInner leafZero)
      (evalPortChain [] inner sideInner leafBit0) := by
  cases inner with
  | p1 =>
    refine ⟨by decide, by decide, ?_⟩
    intro j hj
    -- For j >= 3, prove by induction that state at j is 0 and inputs at j are (0,0)
    have hst : ∀ k, 3 ≤ k →
        avizTransducer.runState avizTransducer.init (fun m => (leafZero m, sideInner m)) k = ⟨0, by decide⟩ ∧
        avizTransducer.runState avizTransducer.init (fun m => (leafBit0 m, sideInner m)) k = ⟨0, by decide⟩ := by
      intro k hk
      induction k with
      | zero => omega
      | succ k ih =>
        by_cases hk3 : k = 2
        · subst hk3; constructor <;> decide
        · have hge : 3 ≤ k := by omega
          obtain ⟨h1, h2⟩ := ih hge
          have hlk0 : leafZero k = (false, false) := rfl
          have hlk1 : leafBit0 k = (false, false) := by simp [leafBit0]; omega
          have hsk : sideInner k = (false, false) := by simp [sideInner]; omega
          simp only [DRTransducer.runState, h1, h2, hlk0, hlk1, hsk]
          constructor <;> decide
    obtain ⟨h1, h2⟩ := hst j (by omega)
    have hlj0 : leafZero j = (false, false) := rfl
    have hlj1 : leafBit0 j = (false, false) := by simp [leafBit0]; omega
    have hsj : sideInner j = (false, false) := by simp [sideInner]; omega
    simp only [evalPortChain, avizAdd, DRTransducer.runOut, h1, h2, hlj0, hlj1, hsj]
    constructor <;> decide
  | p2 =>
    refine ⟨by decide, by decide, ?_⟩
    intro j hj
    have hst : ∀ k, 3 ≤ k →
        avizTransducer.runState avizTransducer.init (fun m => (sideInner m, leafZero m)) k = ⟨0, by decide⟩ ∧
        avizTransducer.runState avizTransducer.init (fun m => (sideInner m, leafBit0 m)) k = ⟨0, by decide⟩ := by
      intro k hk
      induction k with
      | zero => omega
      | succ k ih =>
        by_cases hk3 : k = 2
        · subst hk3; constructor <;> decide
        · have hge : 3 ≤ k := by omega
          obtain ⟨h1, h2⟩ := ih hge
          have hlk0 : leafZero k = (false, false) := rfl
          have hlk1 : leafBit0 k = (false, false) := by simp [leafBit0]; omega
          have hsk : sideInner k = (false, false) := by simp [sideInner]; omega
          simp only [DRTransducer.runState, h1, h2, hlk0, hlk1, hsk]
          constructor <;> decide
    obtain ⟨h1, h2⟩ := hst j (by omega)
    have hlj0 : leafZero j = (false, false) := rfl
    have hlj1 : leafBit0 j = (false, false) := by simp [leafBit0]; omega
    have hsj : sideInner j = (false, false) := by simp [sideInner]; omega
    simp only [evalPortChain, avizAdd, DRTransducer.runOut, h1, h2, hlj0, hlj1, hsj]
    constructor <;> decide

/-- Helper for evaluating sidePort1 off its two active indices. -/
theorem sidePort1_eq_zero (T k : Nat) (h1 : k ≠ T) (h2 : k ≠ T + 1) :
    sidePort1 T k = (false, false) := by
  have hb1 : (k == T) = false := beq_false_of_ne h1
  have hb2 : (k == T + 1) = false := beq_false_of_ne h2
  simp [sidePort1, hb1, hb2]

theorem sidePort2_eq_zero (T k : Nat) (h : k ≠ T - 1) :
    sidePort2 T k = (false, false) := by
  have hb : (k == T - 1) = false := beq_false_of_ne h
  simp [sidePort2, hb]

/-- Helper: stepping avizTransducer on ((false,false),(false,false)) from any state with cPos=false yields 0! -/
theorem avizStep_zero_of_cPos_false (q : Fin 4) (hc : finCPos q = false) :
    (avizTransducer.step q ((false, false), (false, false))).1 = ⟨0, by decide⟩ := by
  revert q hc
  decide

/-- Port-1 TailPulse Induction Step: TailPulse T -> TailPulse (T + 2), independent of bits < T! -/
theorem tailPulse_step_p1 (T : Nat) (x x' : Nat → DR) (hp : TailPulse T x x') :
    TailPulse (T + 2) (avizAdd x (sidePort1 T)) (avizAdd x' (sidePort1 T)) := by
  obtain ⟨hxT, hx'T, htail⟩ := hp
  have hx1 := (htail (T + 1) (by omega)).1
  have hx'1 := (htail (T + 1) (by omega)).2
  have hx2 := (htail (T + 2) (by omega)).1
  have hx'2 := (htail (T + 2) (by omega)).2
  have hyT : sidePort1 T T = (true, false) := by simp [sidePort1]
  have hy1 : sidePort1 T (T + 1) = (false, true) := by
    have hb : ((T + 1) == T) = false := beq_false_of_ne (by omega)
    simp [sidePort1, hb]
  have hy2 : sidePort1 T (T + 2) = (false, false) := sidePort1_eq_zero T (T + 2) (by omega) (by omega)
  have hcPos1 : finCPos (avizTransducer.runState avizTransducer.init (fun m => (x m, sidePort1 T m)) (T + 1)) = false := by
    rw [aviz_cPos_succ, hxT, hyT]; decide
  have hcPos1' : finCPos (avizTransducer.runState avizTransducer.init (fun m => (x' m, sidePort1 T m)) (T + 1)) = true := by
    rw [aviz_cPos_succ, hx'T, hyT]; decide
  have hcPos2 : finCPos (avizTransducer.runState avizTransducer.init (fun m => (x m, sidePort1 T m)) (T + 2)) = false := by
    rw [aviz_cPos_succ, hx1, hy1]; decide
  have hcPos2' : finCPos (avizTransducer.runState avizTransducer.init (fun m => (x' m, sidePort1 T m)) (T + 2)) = false := by
    rw [aviz_cPos_succ, hx'1, hy1]; decide
  have hcNeg2 : finCNeg (avizTransducer.runState avizTransducer.init (fun m => (x m, sidePort1 T m)) (T + 2)) = true := by
    rw [aviz_cNeg_succ, hcPos1, hx1, hy1]; decide
  have hcNeg2' : finCNeg (avizTransducer.runState avizTransducer.init (fun m => (x' m, sidePort1 T m)) (T + 2)) = false := by
    rw [aviz_cNeg_succ, hcPos1', hx'1, hy1]; decide
  refine ⟨?_, ?_, ?_⟩
  · apply Prod.ext
    · rw [avizAdd_fst, hcPos2, hx2, hy2]; decide
    · rw [avizAdd_snd, hcNeg2]
  · apply Prod.ext
    · rw [avizAdd_fst, hcPos2', hx'2, hy2]; decide
    · rw [avizAdd_snd, hcNeg2']
  · have hst : ∀ k, T + 3 ≤ k →
        avizTransducer.runState avizTransducer.init (fun m => (x m, sidePort1 T m)) k = ⟨0, by decide⟩ ∧
        avizTransducer.runState avizTransducer.init (fun m => (x' m, sidePort1 T m)) k = ⟨0, by decide⟩ := by
      intro k hk
      induction k with
      | zero => omega
      | succ k ih =>
        by_cases hk2 : k = T + 2
        · subst hk2
          constructor
          · rw [DRTransducer.runState, hx2, hy2]
            exact avizStep_zero_of_cPos_false _ hcPos2
          · rw [DRTransducer.runState, hx'2, hy2]
            exact avizStep_zero_of_cPos_false _ hcPos2'
        · obtain ⟨h1, h2⟩ := ih (by omega)
          have hxk := (htail k (by omega)).1
          have hx'k := (htail k (by omega)).2
          have hyk := sidePort1_eq_zero T k (by omega) (by omega)
          simp only [DRTransducer.runState, h1, h2, hxk, hx'k, hyk]
          constructor <;> decide
    intro j hj
    obtain ⟨h1, h2⟩ := hst j (by omega)
    have hxj := (htail j (by omega)).1
    have hx'j := (htail j (by omega)).2
    have hyj := sidePort1_eq_zero T j (by omega) (by omega)
    simp only [avizAdd, DRTransducer.runOut, h1, h2, hxj, hx'j, hyj]
    constructor <;> decide

/-- Port-2 TailPulse Induction Step: TailPulse T -> TailPulse (T + 1) for T >= 1! -/
theorem tailPulse_step_p2 (T : Nat) (hT : 1 ≤ T) (x x' : Nat → DR) (hp : TailPulse T x x') :
    TailPulse (T + 1) (avizAdd (sidePort2 T) x) (avizAdd (sidePort2 T) x') := by
  obtain ⟨hxT, hx'T, htail⟩ := hp
  have hx1 := (htail (T + 1) (by omega)).1
  have hx'1 := (htail (T + 1) (by omega)).2
  have hyPrev : sidePort2 T (T - 1) = (false, true) := by simp [sidePort2]
  have hyT : sidePort2 T T = (false, false) := sidePort2_eq_zero T T (by omega)
  have hy1 : sidePort2 T (T + 1) = (false, false) := sidePort2_eq_zero T (T + 1) (by omega)
  have hppmKill : ∀ b : Bool, (ppmCell false b true).1 = false := by decide
  have hTsucc : T = (T - 1) + 1 := by omega
  have hcPosT : finCPos (avizTransducer.runState avizTransducer.init (fun m => (sidePort2 T m, x m)) T) = false := by
    rw [hTsucc, aviz_cPos_succ, ← hTsucc, hyPrev]
    exact hppmKill _
  have hcPosT' : finCPos (avizTransducer.runState avizTransducer.init (fun m => (sidePort2 T m, x' m)) T) = false := by
    rw [hTsucc, aviz_cPos_succ, ← hTsucc, hyPrev]
    exact hppmKill _
  have hcPos1 : finCPos (avizTransducer.runState avizTransducer.init (fun m => (sidePort2 T m, x m)) (T + 1)) = false := by
    rw [aviz_cPos_succ, hyT, hxT]; decide
  have hcPos1' : finCPos (avizTransducer.runState avizTransducer.init (fun m => (sidePort2 T m, x' m)) (T + 1)) = false := by
    rw [aviz_cPos_succ, hyT, hx'T]; decide
  have hcNeg1 : finCNeg (avizTransducer.runState avizTransducer.init (fun m => (sidePort2 T m, x m)) (T + 1)) = true := by
    rw [aviz_cNeg_succ, hcPosT, hyT, hxT]; decide
  have hcNeg1' : finCNeg (avizTransducer.runState avizTransducer.init (fun m => (sidePort2 T m, x' m)) (T + 1)) = false := by
    rw [aviz_cNeg_succ, hcPosT', hyT, hx'T]; decide
  refine ⟨?_, ?_, ?_⟩
  · apply Prod.ext
    · rw [avizAdd_fst, hcPos1, hy1, hx1]; decide
    · rw [avizAdd_snd, hcNeg1]
  · apply Prod.ext
    · rw [avizAdd_fst, hcPos1', hy1, hx'1]; decide
    · rw [avizAdd_snd, hcNeg1']
  · have hst : ∀ k, T + 2 ≤ k →
        avizTransducer.runState avizTransducer.init (fun m => (sidePort2 T m, x m)) k = ⟨0, by decide⟩ ∧
        avizTransducer.runState avizTransducer.init (fun m => (sidePort2 T m, x' m)) k = ⟨0, by decide⟩ := by
      intro k hk
      induction k with
      | zero => omega
      | succ k ih =>
        by_cases hk1 : k = T + 1
        · subst hk1
          constructor
          · rw [DRTransducer.runState, hy1, hx1]
            exact avizStep_zero_of_cPos_false _ hcPos1
          · rw [DRTransducer.runState, hy1, hx'1]
            exact avizStep_zero_of_cPos_false _ hcPos1'
        · obtain ⟨h1, h2⟩ := ih (by omega)
          have hxk := (htail k (by omega)).1
          have hx'k := (htail k (by omega)).2
          have hyk := sidePort2_eq_zero T k (by omega)
          simp only [DRTransducer.runState, h1, h2, hxk, hx'k, hyk]
          constructor <;> decide
    intro j hj
    obtain ⟨h1, h2⟩ := hst j (by omega)
    have hxj := (htail j (by omega)).1
    have hx'j := (htail j (by omega)).2
    have hyj := sidePort2_eq_zero T j (by omega)
    simp only [avizAdd, DRTransducer.runOut, h1, h2, hxj, hx'j, hyj]
    constructor <;> decide

theorem buildWitnessStages_ports (outer : List Port) :
    (buildWitnessStages outer).map Prod.fst = outer := by
  induction outer with
  | nil => rfl
  | cons p rest ih => simp [buildWitnessStages, ih]

/--
  SHARPNESS THEOREM 4A (Exact Matching Lower Bound for ALL d >= 1 and ALL 2^d Port Words):
  For EVERY port word (outer ++ [inner]) of arbitrary depth d = outer.length + 1 >= 1,
  the explicit witness inputs `leafZero` and `leafBit0` (which differ ONLY at bit 0!)
  produce STRICTLY DIFFERENT outputs at the EXACT tropical horizon index
    H = d + 1 + countP1(outer)!
-/
theorem tailPulse_exact_lower_bound (outer : List Port) (inner : Port) :
    TailPulse ((outer.length + 1) + 1 + countP1 outer)
      (evalPortChain (buildWitnessStages outer) inner sideInner leafZero)
      (evalPortChain (buildWitnessStages outer) inner sideInner leafBit0) := by
  induction outer with
  | nil =>
    simpa [buildWitnessStages, countP1] using tailPulse_base inner
  | cons p rest ih =>
    cases p with
    | p1 =>
      have hstep := tailPulse_step_p1 ((rest.length + 1) + 1 + countP1 rest) _ _ ih
      have hidx : ((rest.length + 1) + 1 + countP1 rest) + 2 =
          ((rest.length + 1) + 1) + 1 + (1 + countP1 rest) := by omega
      simpa [buildWitnessStages, evalPortChain, countP1, hidx] using hstep
    | p2 =>
      have hstep := tailPulse_step_p2 ((rest.length + 1) + 1 + countP1 rest) (by omega) _ _ ih
      have hidx : ((rest.length + 1) + 1 + countP1 rest) + 1 =
          ((rest.length + 1) + 1) + 1 + countP1 rest := by omega
      simpa [buildWitnessStages, evalPortChain, countP1, hidx] using hstep

/-- Direct corollary: outputs strictly differ at exact index H(w) while inputs differ only at bit 0! -/
theorem exact_horizon_achieved (outer : List Port) (inner : Port) :
    (∀ j, j ≠ 0 → leafZero j = leafBit0 j) ∧
    evalPortChain (buildWitnessStages outer) inner sideInner leafZero
        ((chainMat outer inner).maxLag) ≠
      evalPortChain (buildWitnessStages outer) inner sideInner leafBit0
        ((chainMat outer inner).maxLag) := by
  constructor
  · intro j hj
    simp [leafZero, leafBit0, hj]
  · rw [chainMat_maxLag]
    have htp := tailPulse_exact_lower_bound outer inner
    rw [htp.1, htp.2.1]
    decide

-- ============================================================================
-- SECTION 8: General Radix-r Horizon-1 Necessary Bound & Radix-2 Impossibility
-- ============================================================================

/--
  SHARPNESS THEOREM 4B (General Radix-r Horizon-1 Necessary Bound):
  Suppose an arbitrary (possibly dual-rail or multi-rail) radix-r (r >= 2) horizon-1
  adder maps input slice a to carry h(a) in [m, M] (attained at a_min, a_max),
  with slice sum val(a) surjecting onto [2L, 2U] (where 2(U - L) >= r - 1), such that
    L <= val(a) - r * h(a) + h(b) <= U   for ALL a, b.
  Then NECESSARILY:
    (r - 2) * (U - L) >= (r - 1) * (r - 1).
-/
theorem radix_horizon1_lower_bound {α : Type} (r L U m M : Int)
    (hr : 2 ≤ r) (hspan : r - 1 ≤ 2 * (U - L))
    (val h : α → Int)
    (hsurj : ∀ s : Int, 2 * L ≤ s → s ≤ 2 * U → ∃ a : α, val a = s)
    (hmin_le : ∀ a, m ≤ h a) (hmax_ge : ∀ a, h a ≤ M)
    (hmin_att : ∃ a, h a = m) (hmax_att : ∃ a, h a = M)
    (hvalid : ∀ a b, L ≤ val a - r * h a + h b ∧ val a - r * h a + h b ≤ U) :
    (r - 1) * (r - 1) ≤ (r - 2) * (U - L) := by
  obtain ⟨aMin, haMin⟩ := hmin_att
  obtain ⟨aMax, haMax⟩ := hmax_att
  -- Step 1: (r - 1) * m <= L
  obtain ⟨aLo, haLo⟩ := hsurj (2 * L) (by omega) (by omega)
  have hlo := (hvalid aLo aMin).1
  rw [haLo, haMin] at hlo
  have hm_le_hlo : m ≤ h aLo := hmin_le aLo
  have hr_hm : r * m ≤ r * h aLo := Int.mul_le_mul_of_nonneg_left hm_le_hlo (by omega)
  have hm_bound : (r - 1) * m ≤ L := by
    have : (r - 1) * m = r * m - m := by rw [Int.sub_mul, Int.one_mul]
    omega
  -- Step 2: U <= (r - 1) * M
  obtain ⟨aHi, haHi⟩ := hsurj (2 * U) (by omega) (by omega)
  have hhi := (hvalid aHi aMax).2
  rw [haHi, haMax] at hhi
  have hhi_le_M : h aHi ≤ M := hmax_ge aHi
  have hr_hM : r * h aHi ≤ r * M := Int.mul_le_mul_of_nonneg_left hhi_le_M (by omega)
  have hM_bound : U ≤ (r - 1) * M := by
    have : (r - 1) * M = r * M - M := by rw [Int.sub_mul, Int.one_mul]
    omega
  -- Step 3: Interval [L - m, U - M] must have width >= r - 1 (via residue class A - 1 mod r)
  let A : Int := L - m
  let B : Int := U - M
  let k : Int := (A - 1 - 2 * L) % r
  have hk_nonneg : 0 ≤ k := Int.emod_nonneg _ (by omega)
  have hk_lt : k < r := Int.emod_lt_of_pos _ (by omega)
  obtain ⟨aRes, haRes⟩ := hsurj (2 * L + k) (by omega) (by omega)
  have hv_lo := (hvalid aRes aMin).1
  have hv_hi := (hvalid aRes aMax).2
  rw [haRes, haMin] at hv_lo
  rw [haRes, haMax] at hv_hi
  let v : Int := 2 * L + k - r * h aRes
  have hv_ge_A : A ≤ v := by simp only [A, v]; omega
  have hv_le_B : v ≤ B := by simp only [B, v]; omega
  -- v - (A - 1) is divisible by r and >= 1, hence >= r!
  have hdiv_r : ∃ q : Int, v - (A - 1) = r * q := by
    let D : Int := A - 1 - 2 * L
    have hmod : r * (D / r) + D % r = D := Int.mul_ediv_add_emod D r
    refine ⟨-(D / r) - h aRes, ?_⟩
    have hmul : r * (-(D / r) - h aRes) = -(r * (D / r)) - r * h aRes := by
      rw [Int.mul_sub, Int.mul_neg]
    rw [hmul]
    have hkD : k = D % r := rfl
    have hv_def : v = 2 * L + k - r * h aRes := rfl
    omega
  obtain ⟨q, hq⟩ := hdiv_r
  have hq_pos : 1 ≤ q := by
    by_cases h1 : 1 ≤ q
    · exact h1
    · have hq0 : q ≤ 0 := by omega
      have hmul0 : r * q ≤ 0 := by
        have := Int.mul_le_mul_of_nonneg_left hq0 (by omega : 0 ≤ r)
        simpa using this
      omega
  have hr_le_rq : r ≤ r * q := by
    have := Int.mul_le_mul_of_nonneg_left hq_pos (by omega : 0 ≤ r)
    simpa using this
  have hBA : r - 1 ≤ B - A := by omega
  have hMm_le : M - m ≤ (U - L) - (r - 1) := by
    simp only [A, B] at hBA; omega
  have hMm_ge : U - L ≤ (r - 1) * (M - m) := by
    have : (r - 1) * (M - m) = (r - 1) * M - (r - 1) * m := Int.mul_sub _ _ _
    omega
  have hstep : (r - 1) * (M - m) ≤ (r - 1) * ((U - L) - (r - 1)) :=
    Int.mul_le_mul_of_nonneg_left hMm_le (by omega)
  have hexp1 : (r - 1) * ((U - L) - (r - 1)) = (r - 1) * (U - L) - (r - 1) * (r - 1) :=
    Int.mul_sub _ _ _
  have hexp2 : (r - 1) * (U - L) - (U - L) = (r - 2) * (U - L) := by
    have h1 : (r - 1) * (U - L) = ((r - 2) + 1) * (U - L) := by
      congr 1; omega
    rw [h1, Int.add_mul, Int.one_mul]
    omega
  omega

/--
  COROLLARY (RADIX-2 HORIZON-1 IMPOSSIBILITY FOR ALL CONTIGUOUS DIGIT SETS [L, U]):
  In radix r = 2, NO bounded contiguous digit set [L, U] with L < U (neither binary [0,1],
  nor dual-rail [-1,1], nor arbitrarily wide [-a, b]!) admits a horizon-1 carry-free adder,
  under ANY encoding α! Hence H = 2 achieved by our dual-rail Avizienis adder is SHARP.
-/
theorem radix2_horizon1_impossible {α : Type} (L U m M : Int) (hLU : L < U)
    (val h : α → Int)
    (hsurj : ∀ s : Int, 2 * L ≤ s → s ≤ 2 * U → ∃ a : α, val a = s)
    (hmin_le : ∀ a, m ≤ h a) (hmax_ge : ∀ a, h a ≤ M)
    (hmin_att : ∃ a, h a = m) (hmax_att : ∃ a, h a = M)
    (hvalid : ∀ a b, L ≤ val a - 2 * h a + h b ∧ val a - 2 * h a + h b ≤ U) :
    False := by
  have hbound := radix_horizon1_lower_bound 2 L U m M (by omega) (by omega)
    val h hsurj hmin_le hmax_ge hmin_att hmax_att hvalid
  omega

theorem radix3_horizon1_witness :
    ∀ s₁ s₂ : Int, -4 ≤ s₁ → s₁ ≤ 4 → -4 ≤ s₂ → s₂ ≤ 4 →
      -2 ≤ s₁ - 3 * radix3Transfer s₁ + radix3Transfer s₂ ∧
      s₁ - 3 * radix3Transfer s₁ + radix3Transfer s₂ ≤ 2 := by
  intro s₁ s₂ h1l h1u h2l h2u
  by_cases c1 : s₁ ≤ -2 <;> by_cases c2 : 2 ≤ s₁ <;>
    by_cases c3 : s₂ ≤ -2 <;> by_cases c4 : 2 ≤ s₂ <;>
    simp only [radix3Transfer, c1, c2, c3, c4, ite_true, ite_false] <;> omega

/--
  SHARPNESS THEOREM 4C (Unbounded Carry Horizon of Standard Binary Ripple-Carry Addition):
  For EVERY proposed carry horizon H : Nat, there exist two unsigned binary streams
  differing ONLY at bit 0 whose ripple-carry sum differs at bit H + 1!
-/
theorem ripple_carry_unbounded_horizon (H : Nat) :
    let x₁ : Nat → Bool := fun _ => false
    let x₂ : Nat → Bool := fun j => decide (j = 0)
    let y  : Nat → Bool := fun j => decide (j ≤ H)
    (∀ j, j ≠ 0 → x₁ j = x₂ j) ∧
    rippleTransducer.runOut rippleTransducer.init (fun j => (x₁ j, y j)) (H + 1) ≠
      rippleTransducer.runOut rippleTransducer.init (fun j => (x₂ j, y j)) (H + 1) := by
  intro x₁ x₂ y
  constructor
  · intro j hj; simp [x₁, x₂, hj]
  · have hst1 : ∀ k, k ≤ H + 1 →
        rippleTransducer.runState rippleTransducer.init (fun j => (x₁ j, y j)) k = ⟨0, by decide⟩ := by
      intro k hk
      induction k with
      | zero => rfl
      | succ k ih =>
        have hprev := ih (by omega)
        rw [DRTransducer.runState, hprev]
        by_cases hle : k ≤ H
        · have hyk : y k = true := by simp [y, hle]
          have hxk : x₁ k = false := rfl
          rw [hxk, hyk]; decide
        · have hyk : y k = false := by simp [y, hle]
          have hxk : x₁ k = false := rfl
          rw [hxk, hyk]; decide
    have hst2 : ∀ k, 1 ≤ k → k ≤ H + 1 →
        rippleTransducer.runState rippleTransducer.init (fun j => (x₂ j, y j)) k = ⟨1, by decide⟩ := by
      intro k h1 hk
      induction k with
      | zero => omega
      | succ k ih =>
        by_cases hk0 : k = 0
        · subst hk0
          change (rippleTransducer.step rippleTransducer.init (x₂ 0, y 0)).1 = ⟨1, by decide⟩
          have hx0 : x₂ 0 = true := rfl
          have hy0 : y 0 = true := by simp [y]
          rw [hx0, hy0]; decide
        · have hprev := ih (by omega) (by omega)
          rw [DRTransducer.runState, hprev]
          have hxk : x₂ k = false := by simp [x₂, hk0]
          have hyk : y k = true := by simp [y]; omega
          rw [hxk, hyk]; decide
    have hs1 := hst1 (H + 1) (by omega)
    have hs2 := hst2 (H + 1) (by omega) (by omega)
    have hx1H : x₁ (H + 1) = false := rfl
    have hx2H : x₂ (H + 1) = false := by simp [x₂]
    have hyH : y (H + 1) = false := by simp [y]
    rw [DRTransducer.runOut, DRTransducer.runOut, hs1, hs2, hx1H, hx2H, hyH]
    decide

-- ============================================================================
-- SECTION 9: Raw Bit-Level Non-Commutativity / Non-Associativity & Non-Vacuity
-- ============================================================================

/-- Raw bit-level commutativity FAILS for avizAdd (at bit-width 3, bit index 1)! -/
theorem avizAdd_not_raw_commutative :
    ∃ x y : Nat → DR, avizAdd x y 1 ≠ avizAdd y x 1 := by
  refine ⟨fun i => if i == 0 then (true, false) else if i == 1 then (false, true) else (false, false),
          fun i => if i == 0 then (false, true) else (false, false), ?_⟩
  decide

/-- Raw bit-level associativity FAILS for avizAdd (even on three redundant zeros at bit 2)! -/
theorem avizAdd_not_raw_associative :
    ∃ x y z : Nat → DR, avizAdd (avizAdd x y) z 2 ≠ avizAdd x (avizAdd y z) 2 := by
  refine ⟨fun _ => (false, false),
          fun _ => (false, false),
          fun i => if i == 1 then (true, true) else (false, false), ?_⟩
  decide

-- ============================================================================
-- SECTION 10: Constructive Non-Vacuity Witnesses & Kernel Axiom Audits
-- ============================================================================

/-- Non-vacuity witness for Engine 1 (ValidPotential & ValidRelInvariant are inhabited). -/
example : Nonempty { φ : Fin 4 → Int //
    avizTransducer.ValidPotential (fun a => drVal a.1 + drVal a.2) φ } :=
  ⟨⟨avizPhi, aviz_validPotential⟩⟩

example : Nonempty { ψ : Fin 4 → Fin 4 → Int //
    DRTransducer.ValidRelInvariant avizTransducer avizCommTransducer ψ } :=
  ⟨⟨fun q₁ q₂ => avizPhi q₁ - avizPhi q₂, aviz_comm_bisim⟩⟩

/-- Non-vacuity witness for Engine 2 (ValidHorizonCert H=2 is inhabited on avizTransducer). -/
example : Nonempty { R : Fin 4 → Fin 4 → Nat // avizTransducer.ValidHorizonCert 2 R } :=
  ⟨⟨avizRank, aviz_validHorizon⟩⟩

/-- Concrete BitVec 8 instantiation of the Dual-Rail Equivalence Compiler bridge. -/
example :
    (prefixVal 8 (avizAdd (ofBitVecPair (173#8) (42#8)) (ofBitVecPair (99#8) (15#8)))) % 256 =
    (((173 : Int) - 42) + ((99 : Int) - 15)) % 256 := by
  simpa using avizAdd_bitVec_mod_eq (173#8) (42#8) (99#8) (15#8)

/-- Concrete non-vacuity check of radix3_horizon1_witness on boundary inputs (-4, -4) and (4, 4). -/
example : -2 ≤ (-4 : Int) - 3 * radix3Transfer (-4) + radix3Transfer (-4) ∧
          (-4 : Int) - 3 * radix3Transfer (-4) + radix3Transfer (-4) ≤ 2 :=
  radix3_horizon1_witness (-4) (-4) (by omega) (by omega) (by omega) (by omega)

/-- Soundness/Completeness Rejection Test 1: Engine 2 NEVER certifies ANY finite horizon H for ripple-carry! -/
theorem no_horizon_cert_for_ripple (H : Nat) (R : Fin 2 → Fin 2 → Nat) :
    ¬ rippleTransducer.ValidHorizonCert H R := by
  intro hcert
  have hrip := ripple_carry_unbounded_horizon H
  have hbound := DRTransducer.horizon_cert_carry_bounded rippleTransducer H R hcert
    (fun j => (false, decide (j ≤ H)))
    (fun j => (decide (j = 0), decide (j ≤ H)))
    (H + 1)
    (fun j hjl _ => by
      have hj0 : j ≠ 0 := by omega
      simp [hj0])
  exact hrip.2 hbound

/-- Negative certificate mutation test: wrong potential φ ≡ 0 is kernel-rejected for avizTransducer. -/
theorem aviz_wrong_potential_rejected :
    ¬ avizTransducer.ValidPotential (fun a => drVal a.1 + drVal a.2) (fun _ => 0) := by
  intro h
  have hbad := h ⟨0, by decide⟩ ((true, false), (true, false))
  revert hbad
  decide

/-- Negative certificate mutation test: horizon H = 1 is kernel-rejected for avizRank. -/
theorem aviz_wrong_horizon1_rejected :
    ¬ avizTransducer.ValidHorizonCert 1 avizRank := by
  intro h
  have hbad := h.2.1 ⟨0, by decide⟩ ⟨2, by decide⟩
  revert hbad
  decide

/-- Exact modular equivalence between left-associated and right-associated depth-d chains ∀ d, ∀ w! -/
theorem leftChain_equiv_rightChain_mod (w : Nat) (ys : List (Nat → DR)) (yInner x : Nat → DR) :
    (prefixVal w (leftChainOp ys yInner x)) % ((2 ^ w : Nat) : Int) =
    (prefixVal w (rightChainOp ys yInner x)) % ((2 ^ w : Nat) : Int) := by
  induction ys with
  | nil =>
    simp only [leftChainOp, rightChainOp, List.map, evalPortChain]
    exact avizAdd_comm_mod w x yInner
  | cons y rest ih =>
    simp only [leftChainOp, rightChainOp, List.map, evalPortChain] at ih ⊢
    rw [avizAdd_mod_eq, avizAdd_mod_eq]
    have h1 := emod_add_congr _ _ (prefixVal w y) (prefixVal w y) ((2 ^ w : Nat) : Int) ih rfl
    have hcomm :
        prefixVal w (evalPortChain (List.map (fun y => (Port.p2, y)) rest) Port.p2 yInner x) +
          prefixVal w y =
        prefixVal w y +
          prefixVal w (evalPortChain (List.map (fun y => (Port.p2, y)) rest) Port.p2 yInner x) := by
      omega
    rw [hcomm] at h1
    exact h1

/--
  CARRY-HORIZON HALVING SEPARATION THEOREM (∀ d >= 1, ∀ bit-width w : Nat):
  For EVERY depth d = k + 1 >= 1:
    1. Left-associated and right-associated depth-d chains are semantically IDENTICAL mod 2^w ∀ w.
    2. Left-associated depth-d chain has EXACT carry horizon 2d (upper bound AND achieved witness).
    3. Right-associated depth-d chain has EXACT carry horizon d + 1 (upper bound AND achieved witness).
-/
theorem horizon_halving_exact_separation (k : Nat) :
    let d := k + 1
    (∀ (w : Nat) (ys : List (Nat → DR)) (yInner x : Nat → DR),
      (prefixVal w (leftChainOp ys yInner x)) % ((2 ^ w : Nat) : Int) =
      (prefixVal w (rightChainOp ys yInner x)) % ((2 ^ w : Nat) : Int)) ∧
    (chainMat (List.replicate k Port.p1) Port.p1).maxLag = 2 * d ∧
    (chainMat (List.replicate k Port.p2) Port.p2).maxLag = d + 1 ∧
    (evalPortChain (buildWitnessStages (List.replicate k Port.p1)) Port.p1 sideInner leafZero (2 * d) ≠
     evalPortChain (buildWitnessStages (List.replicate k Port.p1)) Port.p1 sideInner leafBit0 (2 * d)) ∧
    (evalPortChain (buildWitnessStages (List.replicate k Port.p2)) Port.p2 sideInner leafZero (d + 1) ≠
     evalPortChain (buildWitnessStages (List.replicate k Port.p2)) Port.p2 sideInner leafBit0 (d + 1)) := by
  have hcnt1 : ∀ n, countP1 (List.replicate n Port.p1) = n := by
    intro n; induction n with
    | zero => rfl
    | succ m ih => simp [List.replicate_succ, countP1, ih]; omega
  have hcnt2 : ∀ n, countP1 (List.replicate n Port.p2) = 0 := by
    intro n; induction n with
    | zero => rfl
    | succ m ih => simpa [List.replicate_succ, countP1] using ih
  have hL : (chainMat (List.replicate k Port.p1) Port.p1).maxLag = 2 * (k + 1) := by
    rw [chainMat_maxLag, List.length_replicate, hcnt1]; omega
  have hR : (chainMat (List.replicate k Port.p2) Port.p2).maxLag = (k + 1) + 1 := by
    rw [chainMat_maxLag, List.length_replicate, hcnt2]
  refine ⟨fun w ys yInner x => leftChain_equiv_rightChain_mod w ys yInner x, hL, hR, ?_, ?_⟩
  · have h := (exact_horizon_achieved (List.replicate k Port.p1) Port.p1).2
    rw [hL] at h
    exact h
  · have h := (exact_horizon_achieved (List.replicate k Port.p2) Port.p2).2
    rw [hR] at h
    exact h

end DualRailCompiler
