import Defs

namespace NegabinaryCarryParityBias

/-! ## Section 1: Pure-Init Sum, Parity, and Bit-Length Lemmas -/

private theorem signOfNat_add (a b : Nat) :
    signOfNat (a + b) = signOfNat a * signOfNat b := by
  unfold signOfNat
  by_cases ha : a % 2 = 0 <;> by_cases hb : b % 2 = 0
  · simp [ha, hb, show (a + b) % 2 = 0 by omega]
  · simp [ha, hb, show ¬ (a + b) % 2 = 0 by omega]
  · simp [ha, hb, show ¬ (a + b) % 2 = 0 by omega]
  · simp [ha, hb, show (a + b) % 2 = 0 by omega]

private theorem sumRange_congr {f g : Nat → Int} (n : Nat) (h : ∀ k, k < n → f k = g k) :
    sumRange f n = sumRange g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumRange]
    rw [ih (fun k hk => h k (by omega)), h n (by omega)]

private theorem sumRange_two_mul (f : Nat → Int) (n : Nat) :
    sumRange f (2 * n) =
      sumRange (fun k => f (2 * k)) n + sumRange (fun k => f (2 * k + 1)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h1 : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
    rw [h1]
    simp only [sumRange]
    rw [ih]
    omega

private theorem negabinCarries_zero (c : NegCarry) :
    negabinCarries 0 0 c = negabinDrain c := by
  unfold negabinCarries; simp

private theorem base2Carries_zero (c : BinCarry) :
    base2Carries 0 0 c = 0 := by
  unfold base2Carries; simp

private theorem negabinCarries_unfold (x m : Nat) (c : NegCarry) :
    negabinCarries x m c =
      (negabinStep (x % 2) (m % 2) c).1 +
        negabinCarries (x / 2) (m / 2) (negabinStep (x % 2) (m % 2) c).2 := by
  by_cases h0 : x = 0 ∧ m = 0
  · rcases h0 with ⟨rfl, rfl⟩
    cases c <;> simp [negabinCarries_zero, negabinStep, negabinDrain, NegCarry.toInt]
  · conv => lhs; unfold negabinCarries
    simp [h0]

private theorem base2Carries_unfold (x m : Nat) (c : BinCarry) :
    base2Carries x m c =
      (base2Step (x % 2) (m % 2) c).1 +
        base2Carries (x / 2) (m / 2) (base2Step (x % 2) (m % 2) c).2 := by
  by_cases h0 : x = 0 ∧ m = 0
  · rcases h0 with ⟨rfl, rfl⟩
    cases c <;> simp [base2Carries_zero, base2Step, BinCarry.toInt]
  · conv => lhs; unfold base2Carries
    simp [h0]

private theorem bitLen_zero : bitLen 0 = 0 := by
  unfold bitLen; rfl

private theorem bitLen_pos (m : Nat) (hm : 1 ≤ m) :
    bitLen m = bitLen (m / 2) + 1 := by
  conv => lhs; unfold bitLen
  simp [show m ≠ 0 by omega]

private theorem bitLen_two_mul (q : Nat) (hq : 1 ≤ q) :
    bitLen (2 * q) = bitLen q + 1 := by
  rw [bitLen_pos (2 * q) (by omega), show (2 * q) / 2 = q by omega]

private theorem bitLen_two_mul_add_one (q : Nat) :
    bitLen (2 * q + 1) = bitLen q + 1 := by
  rw [bitLen_pos (2 * q + 1) (by omega), show (2 * q + 1) / 2 = q by omega]

private theorem negabinSpec_zero :
    negabinSpec 0 = ((3, 1, 1), (0, -1, -1), (0, 1, -1)) := by
  unfold negabinSpec; rfl

private theorem negabinSpec_two_mul (q : Nat) (hq : 1 ≤ q) :
    negabinSpec (2 * q) =
      let ((b0, bp, bm), (o0, op, om), (d0, dp, dm)) := negabinSpec q
      ((2 * b0, b0 - bm, b0 - bp),
       (2 * o0, o0 - om, o0 - op),
       (2 * d0, d0 - dm, d0 - dp)) := by
  conv => lhs; unfold negabinSpec
  simp [show 2 * q ≠ 0 by omega, show (2 * q) / 2 = q by omega]

private theorem negabinSpec_two_mul_add_one (q : Nat) :
    negabinSpec (2 * q + 1) =
      let ((b0, _, bm), (o0, _, om), (d0, _, dm)) := negabinSpec q
      ((b0 - bm, -2 * bm, 2 * b0),
       (o0 - om, -2 * om, 2 * o0),
       (d0 - dm, -2 * dm, 2 * d0)) := by
  conv => lhs; unfold negabinSpec
  simp [show (2 * q + 1) / 2 = q by omega, show (2 * q + 1) % 2 = 1 by omega]

private theorem base2Spec_zero :
    base2Spec 0 = ((3, 1), (0, 2)) := by
  unfold base2Spec; rfl

private theorem base2Spec_two_mul (q : Nat) (hq : 1 ≤ q) :
    base2Spec (2 * q) =
      let ((g0, g1), (u0, u1)) := base2Spec q
      ((2 * g0, g0 - g1), (2 * u0, u0 - u1)) := by
  conv => lhs; unfold base2Spec
  simp [show 2 * q ≠ 0 by omega, show (2 * q) / 2 = q by omega]

private theorem base2Spec_two_mul_add_one (q : Nat) :
    base2Spec (2 * q + 1) =
      let ((g0, g1), (u0, u1)) := base2Spec q
      ((g0 - g1, -2 * g1), (u0 - u1, -2 * u1)) := by
  conv => lhs; unfold base2Spec
  simp [show (2 * q + 1) / 2 = q by omega, show (2 * q + 1) % 2 = 1 by omega]

/-! ### Exact Small-Constant Evaluation Lemmas (kernel-reduced via unfolding lemmas) -/

private theorem bl_1 : bitLen 1 = 1 := by rw [show (1:Nat)=2*0+1 by rfl, bitLen_two_mul_add_one, bitLen_zero]
private theorem bl_2 : bitLen 2 = 2 := by rw [show (2:Nat)=2*1 by rfl, bitLen_two_mul 1 (by omega), bl_1]
private theorem bl_3 : bitLen 3 = 2 := by rw [show (3:Nat)=2*1+1 by rfl, bitLen_two_mul_add_one, bl_1]
private theorem bl_4 : bitLen 4 = 3 := by rw [show (4:Nat)=2*2 by rfl, bitLen_two_mul 2 (by omega), bl_2]
private theorem bl_5 : bitLen 5 = 3 := by rw [show (5:Nat)=2*2+1 by rfl, bitLen_two_mul_add_one, bl_2]
private theorem bl_6 : bitLen 6 = 3 := by rw [show (6:Nat)=2*3 by rfl, bitLen_two_mul 3 (by omega), bl_3]
private theorem bl_7 : bitLen 7 = 3 := by rw [show (7:Nat)=2*3+1 by rfl, bitLen_two_mul_add_one, bl_3]
private theorem bl_12 : bitLen 12 = 4 := by rw [show (12:Nat)=2*6 by rfl, bitLen_two_mul 6 (by omega), bl_6]
private theorem bl_13 : bitLen 13 = 4 := by rw [show (13:Nat)=2*6+1 by rfl, bitLen_two_mul_add_one, bl_6]

private theorem ns_1 : negabinSpec 1 = ((2, -2, 6), (1, 2, 0), (1, 2, 0)) := by
  rw [show (1:Nat)=2*0+1 by rfl, negabinSpec_two_mul_add_one, negabinSpec_zero]; rfl
private theorem ns_2 : negabinSpec 2 = ((4, -4, 4), (2, 1, -1), (2, 1, -1)) := by
  rw [show (2:Nat)=2*1 by rfl, negabinSpec_two_mul 1 (by omega), ns_1]; rfl
private theorem ns_3 : negabinSpec 3 = ((-4, -12, 4), (1, 0, 2), (1, 0, 2)) := by
  rw [show (3:Nat)=2*1+1 by rfl, negabinSpec_two_mul_add_one, ns_1]; rfl
private theorem ns_4 : negabinSpec 4 = ((8, 0, 8), (4, 3, 1), (4, 3, 1)) := by
  rw [show (4:Nat)=2*2 by rfl, negabinSpec_two_mul 2 (by omega), ns_2]; rfl
private theorem ns_5 : negabinSpec 5 = ((0, -8, 8), (3, 2, 4), (3, 2, 4)) := by
  rw [show (5:Nat)=2*2+1 by rfl, negabinSpec_two_mul_add_one, ns_2]; rfl
private theorem ns_6 : negabinSpec 6 = ((-8, -8, 8), (2, -1, 1), (2, -1, 1)) := by
  rw [show (6:Nat)=2*3 by rfl, negabinSpec_two_mul 3 (by omega), ns_3]; rfl
private theorem ns_7 : negabinSpec 7 = ((-8, -8, -8), (-1, -4, 2), (-1, -4, 2)) := by
  rw [show (7:Nat)=2*3+1 by rfl, negabinSpec_two_mul_add_one, ns_3]; rfl
private theorem ns_9 : negabinSpec 9 = ((0, -16, 16), (3, -2, 8), (3, -2, 8)) := by
  rw [show (9:Nat)=2*4+1 by rfl, negabinSpec_two_mul_add_one, ns_4]; rfl
private theorem ns_12 : negabinSpec 12 = ((-16, -16, 0), (4, 1, 3), (4, 1, 3)) := by
  rw [show (12:Nat)=2*6 by rfl, negabinSpec_two_mul 6 (by omega), ns_6]; rfl
private theorem ns_13 : negabinSpec 13 = ((-16, -16, -16), (1, -2, 4), (1, -2, 4)) := by
  rw [show (13:Nat)=2*6+1 by rfl, negabinSpec_two_mul_add_one, ns_6]; rfl
private theorem ns_15 : negabinSpec 15 = ((0, 16, -16), (-3, -4, -2), (-3, -4, -2)) := by
  rw [show (15:Nat)=2*7+1 by rfl, negabinSpec_two_mul_add_one, ns_7]; rfl

private theorem bs_1 : base2Spec 1 = ((2, -2), (-2, -4)) := by
  rw [show (1:Nat)=2*0+1 by rfl, base2Spec_two_mul_add_one, base2Spec_zero]; rfl
private theorem bs_2 : base2Spec 2 = ((4, 4), (-4, 2)) := by
  rw [show (2:Nat)=2*1 by rfl, base2Spec_two_mul 1 (by omega), bs_1]; rfl
private theorem bs_3 : base2Spec 3 = ((4, 4), (2, 8)) := by
  rw [show (3:Nat)=2*1+1 by rfl, base2Spec_two_mul_add_one, bs_1]; rfl
private theorem bs_5 : base2Spec 5 = ((0, -8), (-6, -4)) := by
  rw [show (5:Nat)=2*2+1 by rfl, base2Spec_two_mul_add_one, bs_2]; rfl

private theorem mul_two_pow_succ (m k : Nat) : m * 2 ^ (k + 1) = 2 * (m * 2 ^ k) := by
  rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (m * 2 ^ k) 2]

private theorem negabinParitySum_split (w m : Nat) (c : NegCarry) :
    negabinParitySum (w + 1) m c =
      signOfNat (negabinStep 0 (m % 2) c).1 *
        negabinParitySum w (m / 2) (negabinStep 0 (m % 2) c).2 +
      signOfNat (negabinStep 1 (m % 2) c).1 *
        negabinParitySum w (m / 2) (negabinStep 1 (m % 2) c).2 := by
  unfold negabinParitySum
  have hpow : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ]; omega
  rw [hpow, sumRange_two_mul]
  have hmul : ∀ (a : Int) (f : Nat → Int) (n : Nat),
      sumRange (fun k => a * f k) n = a * sumRange f n := by
    intro a f n; induction n with
    | zero => simp [sumRange]
    | succ n ih => simp only [sumRange, ih]; rw [Int.mul_add]
  have heven : sumRange (fun k => signOfNat (negabinCarries (2 * k) m c)) (2 ^ w) =
      signOfNat (negabinStep 0 (m % 2) c).1 *
        sumRange (fun k => signOfNat (negabinCarries k (m / 2) (negabinStep 0 (m % 2) c).2)) (2 ^ w) := by
    rw [sumRange_congr (2 ^ w) (fun k _ => by
      rw [negabinCarries_unfold (2 * k) m c, signOfNat_add,
        show (2 * k) % 2 = 0 by omega, show (2 * k) / 2 = k by omega])]
    exact hmul _ _ _
  have hodd : sumRange (fun k => signOfNat (negabinCarries (2 * k + 1) m c)) (2 ^ w) =
      signOfNat (negabinStep 1 (m % 2) c).1 *
        sumRange (fun k => signOfNat (negabinCarries k (m / 2) (negabinStep 1 (m % 2) c).2)) (2 ^ w) := by
    rw [sumRange_congr (2 ^ w) (fun k _ => by
      rw [negabinCarries_unfold (2 * k + 1) m c, signOfNat_add,
        show (2 * k + 1) % 2 = 1 by omega, show (2 * k + 1) / 2 = k by omega])]
    exact hmul _ _ _
  rw [heven, hodd]

private theorem base2ParitySum_split (w m : Nat) (c : BinCarry) :
    base2ParitySum (w + 1) m c =
      signOfNat (base2Step 0 (m % 2) c).1 *
        base2ParitySum w (m / 2) (base2Step 0 (m % 2) c).2 +
      signOfNat (base2Step 1 (m % 2) c).1 *
        base2ParitySum w (m / 2) (base2Step 1 (m % 2) c).2 := by
  unfold base2ParitySum
  have hpow : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ]; omega
  rw [hpow, sumRange_two_mul]
  have hmul : ∀ (a : Int) (f : Nat → Int) (n : Nat),
      sumRange (fun k => a * f k) n = a * sumRange f n := by
    intro a f n; induction n with
    | zero => simp [sumRange]
    | succ n ih => simp only [sumRange, ih]; rw [Int.mul_add]
  have heven : sumRange (fun k => signOfNat (base2Carries (2 * k) m c)) (2 ^ w) =
      signOfNat (base2Step 0 (m % 2) c).1 *
        sumRange (fun k => signOfNat (base2Carries k (m / 2) (base2Step 0 (m % 2) c).2)) (2 ^ w) := by
    rw [sumRange_congr (2 ^ w) (fun k _ => by
      rw [base2Carries_unfold (2 * k) m c, signOfNat_add,
        show (2 * k) % 2 = 0 by omega, show (2 * k) / 2 = k by omega])]
    exact hmul _ _ _
  have hodd : sumRange (fun k => signOfNat (base2Carries (2 * k + 1) m c)) (2 ^ w) =
      signOfNat (base2Step 1 (m % 2) c).1 *
        sumRange (fun k => signOfNat (base2Carries k (m / 2) (base2Step 1 (m % 2) c).2)) (2 ^ w) := by
    rw [sumRange_congr (2 ^ w) (fun k _ => by
      rw [base2Carries_unfold (2 * k + 1) m c, signOfNat_add,
        show (2 * k + 1) % 2 = 1 by omega, show (2 * k + 1) / 2 = k by omega])]
    exact hmul _ _ _
  rw [heven, hodd]

/-! ## Section 2: Negabinary Transfer Recurrence, Jacobsthal Law & Spectral Decomposition -/

theorem negabinParitySum_step (w q : Nat) :
    (negabinParitySum (w + 1) (2 * q) .zero = 2 * negabinParitySum w q .zero ∧
     negabinParitySum (w + 1) (2 * q) .pos =
       negabinParitySum w q .zero - negabinParitySum w q .neg ∧
     negabinParitySum (w + 1) (2 * q) .neg =
       negabinParitySum w q .zero - negabinParitySum w q .pos) ∧
    (negabinParitySum (w + 1) (2 * q + 1) .zero =
       negabinParitySum w q .zero - negabinParitySum w q .neg ∧
     negabinParitySum (w + 1) (2 * q + 1) .pos = -2 * negabinParitySum w q .neg ∧
     negabinParitySum (w + 1) (2 * q + 1) .neg = 2 * negabinParitySum w q .zero) := by
  have he : (2 * q) % 2 = 0 ∧ (2 * q) / 2 = q := by omega
  have ho : (2 * q + 1) % 2 = 1 ∧ (2 * q + 1) / 2 = q := by omega
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · rw [negabinParitySum_split, he.1, he.2]; simp [negabinStep, NegCarry.toInt, signOfNat]; omega
  · rw [negabinParitySum_split, he.1, he.2]; simp [negabinStep, NegCarry.toInt, signOfNat]; omega
  · rw [negabinParitySum_split, he.1, he.2]; simp [negabinStep, NegCarry.toInt, signOfNat]; omega
  · rw [negabinParitySum_split, ho.1, ho.2]; simp [negabinStep, NegCarry.toInt, signOfNat]; omega
  · rw [negabinParitySum_split, ho.1, ho.2]; simp [negabinStep, NegCarry.toInt, signOfNat]; omega
  · rw [negabinParitySum_split, ho.1, ho.2]; simp [negabinStep, NegCarry.toInt, signOfNat]; omega

theorem negabinParitySum_zero (w : Nat) :
    negabinParitySum w 0 .zero = (2 ^ w : Int) ∧
    negabinParitySum w 0 .pos = jacobsthal w + 1 ∧
    negabinParitySum w 0 .neg = jacobsthal w - 1 ∧
    3 * jacobsthal w = (2 ^ w : Int) - (-1 : Int) ^ w ∧
    negabinParitySum w 0 .pos - negabinParitySum w 0 .neg = 2 := by
  induction w with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [negabinParitySum, sumRange, negabinCarries_zero, negabinDrain, signOfNat, jacobsthal]
  | succ w ih =>
    rcases ih with ⟨h0, hp, hm, hJ, _⟩
    have hstep := (negabinParitySum_step w 0).1
    simp only [Nat.mul_zero] at hstep
    have h2 : (2 ^ (w + 1) : Int) = 2 * (2 ^ w : Int) := by rw [Int.pow_succ]; omega
    have h1 : (-1 : Int) ^ (w + 1) = -((-1 : Int) ^ w) := by rw [Int.pow_succ]; omega
    have h0' : negabinParitySum (w + 1) 0 .zero = (2 ^ (w + 1) : Int) := by
      rw [hstep.1, h0, h2]
    have hp' : negabinParitySum (w + 1) 0 .pos = jacobsthal (w + 1) + 1 := by
      rw [hstep.2.1, h0, hm, jacobsthal]; omega
    have hm' : negabinParitySum (w + 1) 0 .neg = jacobsthal (w + 1) - 1 := by
      rw [hstep.2.2, h0, hp, jacobsthal]; omega
    have hJ' : 3 * jacobsthal (w + 1) = (2 ^ (w + 1) : Int) - (-1 : Int) ^ (w + 1) := by
      rw [jacobsthal, h2, h1]; omega
    exact ⟨h0', hp', hm', hJ', by omega⟩

theorem negabinParitySum_spectral (m k : Nat) :
    let ((b0, bp, bm), (o0, op, om), (d0, dp, dm)) := negabinSpec m
    3 * negabinParitySum (bitLen m + k) m .zero =
      b0 * (2 ^ k : Int) + o0 * (-1 : Int) ^ k + 3 * d0 ∧
    3 * negabinParitySum (bitLen m + k) m .pos =
      bp * (2 ^ k : Int) + op * (-1 : Int) ^ k + 3 * dp ∧
    3 * negabinParitySum (bitLen m + k) m .neg =
      bm * (2 ^ k : Int) + om * (-1 : Int) ^ k + 3 * dm := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    by_cases hm : m = 0
    · subst hm
      rw [negabinSpec_zero, bitLen_zero, Nat.zero_add]
      dsimp only
      have ⟨h0, hp, hm', hJ, _⟩ := negabinParitySum_zero k
      refine ⟨?_, ?_, ?_⟩ <;> omega
    · have hq_lt : m / 2 < m := Nat.div_lt_self (by omega) (by omega)
      have ihq := ih (m / 2) hq_lt
      by_cases hpar : m % 2 = 0
      · have hq_pos : 1 ≤ m / 2 := by omega
        have hm_eq : m = 2 * (m / 2) := by omega
        rw [hm_eq, negabinSpec_two_mul (m / 2) hq_pos, bitLen_two_mul (m / 2) hq_pos]
        have hidx : bitLen (m / 2) + 1 + k = (bitLen (m / 2) + k) + 1 := by omega
        rw [hidx]
        have hst := (negabinParitySum_step (bitLen (m / 2) + k) (m / 2)).1
        rcases hsp : negabinSpec (m / 2) with ⟨⟨b0, bp, bm⟩, ⟨o0, op, om⟩, ⟨d0, dp, dm⟩⟩
        rw [hsp] at ihq
        dsimp only at ihq ⊢
        rcases ihq with ⟨ih0, ihp, ihm⟩
        refine ⟨?_, ?_, ?_⟩
        · rw [hst.1]; grind
        · rw [hst.2.1]; grind
        · rw [hst.2.2]; grind
      · have hm_eq : m = 2 * (m / 2) + 1 := by omega
        rw [hm_eq, negabinSpec_two_mul_add_one (m / 2), bitLen_two_mul_add_one (m / 2)]
        have hidx : bitLen (m / 2) + 1 + k = (bitLen (m / 2) + k) + 1 := by omega
        rw [hidx]
        have hst := (negabinParitySum_step (bitLen (m / 2) + k) (m / 2)).2
        rcases hsp : negabinSpec (m / 2) with ⟨⟨b0, bp, bm⟩, ⟨o0, op, om⟩, ⟨d0, dp, dm⟩⟩
        rw [hsp] at ihq
        dsimp only at ihq ⊢
        rcases ihq with ⟨ih0, ihp, ihm⟩
        refine ⟨?_, ?_, ?_⟩
        · rw [hst.1]; grind
        · rw [hst.2.1]; grind
        · rw [hst.2.2]; grind

/-! ## Section 3: Universal ±1/3 Barrier and Complete Extremal Classifications -/

private theorem negabinSpec_cube (m : Nat) (hm : 4 ≤ m) :
    -(2 ^ bitLen m : Int) ≤ (negabinSpec m).1.1 ∧ (negabinSpec m).1.1 ≤ (2 ^ bitLen m : Int) ∧
    -(2 ^ bitLen m : Int) ≤ (negabinSpec m).1.2.1 ∧ (negabinSpec m).1.2.1 ≤ (2 ^ bitLen m : Int) ∧
    -(2 ^ bitLen m : Int) ≤ (negabinSpec m).1.2.2 ∧ (negabinSpec m).1.2.2 ≤ (2 ^ bitLen m : Int) := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    by_cases h8 : m < 8
    · have : m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 := by omega
      rcases this with rfl | rfl | rfl | rfl
      · simp [ns_4, bl_4]
      · simp [ns_5, bl_5]
      · simp [ns_6, bl_6]
      · simp [ns_7, bl_7]
    · have hq_ge : 4 ≤ m / 2 := by omega
      have hq_lt : m / 2 < m := Nat.div_lt_self (by omega) (by omega)
      have ihq := ih (m / 2) hq_lt hq_ge
      by_cases hpar : m % 2 = 0
      · have hm_eq : m = 2 * (m / 2) := by omega
        rw [hm_eq, negabinSpec_two_mul (m / 2) (by omega), bitLen_two_mul (m / 2) (by omega)]
        rcases hsp : negabinSpec (m / 2) with ⟨⟨b0, bp, bm⟩, _, _⟩
        rw [hsp] at ihq
        dsimp only at ihq ⊢
        have hpow : (2 ^ (bitLen (m / 2) + 1) : Int) = 2 * (2 ^ bitLen (m / 2) : Int) := by
          rw [Int.pow_succ]; omega
        rw [hpow]; omega
      · have hm_eq : m = 2 * (m / 2) + 1 := by omega
        rw [hm_eq, negabinSpec_two_mul_add_one (m / 2), bitLen_two_mul_add_one (m / 2)]
        rcases hsp : negabinSpec (m / 2) with ⟨⟨b0, bp, bm⟩, _, _⟩
        rw [hsp] at ihq
        dsimp only at ihq ⊢
        have hpow : (2 ^ (bitLen (m / 2) + 1) : Int) = 2 * (2 ^ bitLen (m / 2) : Int) := by
          rw [Int.pow_succ]; omega
        rw [hpow]; omega

theorem negabinBias_abs_le_one_third (m : Nat) (hm : 1 ≤ m) :
    -(2 ^ bitLen m : Int) ≤ (negabinSpec m).1.1 ∧
    (negabinSpec m).1.1 ≤ (2 ^ bitLen m : Int) := by
  by_cases h4 : m < 4
  · have : m = 1 ∨ m = 2 ∨ m = 3 := by omega
    rcases this with rfl | rfl | rfl
    · simp [ns_1, bl_1]
    · simp [ns_2, bl_2]
    · simp [ns_3, bl_3]
  · have hc := negabinSpec_cube m (by omega)
    exact ⟨hc.1, hc.2.1⟩

private theorem negabinSpec_two_pow_ge2 (k : Nat) (hk : 2 ≤ k) :
    (negabinSpec (2 ^ k)).1.1 = (2 ^ bitLen (2 ^ k) : Int) ∧
    0 ≤ (negabinSpec (2 ^ k)).1.2.1 ∧ (negabinSpec (2 ^ k)).1.2.1 < (2 ^ bitLen (2 ^ k) : Int) ∧
    0 < (negabinSpec (2 ^ k)).1.2.2 ∧ (negabinSpec (2 ^ k)).1.2.2 ≤ (2 ^ bitLen (2 ^ k) : Int) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk2 : k < 2
    · have : k = 1 := by omega
      subst this; simp [ns_4, bl_4]
    · have ihk := ih (by omega)
      have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
      rw [hpow, negabinSpec_two_mul (2 ^ k) (Nat.two_pow_pos k),
        bitLen_two_mul (2 ^ k) (Nat.two_pow_pos k)]
      rcases hsp : negabinSpec (2 ^ k) with ⟨⟨b0, bp, bm⟩, _, _⟩
      rw [hsp] at ihk
      dsimp only at ihk ⊢
      have hS : (2 ^ (bitLen (2 ^ k) + 1) : Int) = 2 * (2 ^ bitLen (2 ^ k) : Int) := by
        rw [Int.pow_succ]; omega
      rw [hS]; omega

private theorem negabinSpec_two_pow_props (k : Nat) :
    (negabinSpec (2 ^ k)).1.1 = (2 ^ bitLen (2 ^ k) : Int) ∧
    0 < (negabinSpec (2 ^ k)).1.2.2 := by
  by_cases hk : k < 2
  · have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl
    · simp [ns_1, bl_1]
    · simp [ns_2, bl_2]
  · have h := negabinSpec_two_pow_ge2 k (by omega)
    exact ⟨h.1, h.2.2.2.1⟩

theorem negabinBias_eq_pos_one_third_iff (m : Nat) (hm : 1 ≤ m) :
    (negabinSpec m).1.1 = (2 ^ bitLen m : Int) ↔ ∃ k : Nat, m = 2 ^ k := by
  constructor
  · intro heq
    induction m using Nat.strongRecOn with
    | ind m ih =>
      by_cases h4 : m < 4
      · have : m = 1 ∨ m = 2 ∨ m = 3 := by omega
        rcases this with rfl | rfl | rfl
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · simp [ns_3, bl_3] at heq
      · by_cases hpar : m % 2 = 0
        · have hq_pos : 1 ≤ m / 2 := by omega
          have hq_lt : m / 2 < m := Nat.div_lt_self (by omega) (by omega)
          have hm_eq : m = 2 * (m / 2) := by omega
          rw [hm_eq, negabinSpec_two_mul (m / 2) hq_pos, bitLen_two_mul (m / 2) hq_pos] at heq
          rcases hsp : negabinSpec (m / 2) with ⟨⟨b0, bp, bm⟩, _, _⟩
          rw [hsp] at heq
          dsimp only at heq
          have hS : (2 ^ (bitLen (m / 2) + 1) : Int) = 2 * (2 ^ bitLen (m / 2) : Int) := by
            rw [Int.pow_succ]; omega
          have hq_eq : (negabinSpec (m / 2)).1.1 = (2 ^ bitLen (m / 2) : Int) := by
            rw [hsp]; dsimp only; omega
          rcases ih (m / 2) hq_lt hq_pos hq_eq with ⟨r, hr⟩
          exact ⟨r + 1, by rw [hm_eq, hr, Nat.pow_succ]; omega⟩
        · have hq_ge : 2 ≤ m / 2 := by omega
          have hq_lt : m / 2 < m := Nat.div_lt_self (by omega) (by omega)
          have hm_eq : m = 2 * (m / 2) + 1 := by omega
          rw [hm_eq, negabinSpec_two_mul_add_one (m / 2), bitLen_two_mul_add_one (m / 2)] at heq
          rcases hsp : negabinSpec (m / 2) with ⟨⟨b0, bp, bm⟩, _, _⟩
          rw [hsp] at heq
          dsimp only at heq
          have hS : (2 ^ (bitLen (m / 2) + 1) : Int) = 2 * (2 ^ bitLen (m / 2) : Int) := by
            rw [Int.pow_succ]; omega
          by_cases hq4 : m / 2 < 4
          · have : m / 2 = 2 ∨ m / 2 = 3 := by omega
            rcases this with h2 | h3
            · rw [h2] at hsp heq; simp [ns_2, bl_2] at hsp heq; omega
            · rw [h3] at hsp heq; simp [ns_3, bl_3] at hsp heq; omega
          · have hcube := negabinSpec_cube (m / 2) (by omega)
            rw [hsp] at hcube; dsimp only at hcube
            have hb0_eq : (negabinSpec (m / 2)).1.1 = (2 ^ bitLen (m / 2) : Int) := by
              rw [hsp]; dsimp only; omega
            have hbm_neg : (negabinSpec (m / 2)).1.2.2 = -(2 ^ bitLen (m / 2) : Int) := by
              rw [hsp]; dsimp only; omega
            rcases ih (m / 2) hq_lt (by omega) hb0_eq with ⟨r, hr⟩
            have hpos := (negabinSpec_two_pow_props r).2
            rw [← hr] at hpos
            have h2pos : (0 : Int) < (2 ^ bitLen (m / 2) : Int) := by
              exact_mod_cast Nat.two_pow_pos (bitLen (m / 2))
            omega
  · rintro ⟨k, rfl⟩
    exact (negabinSpec_two_pow_props k).1

private theorem negabinSpec_neg_ray_invariant (m : Nat) (hm : 1 ≤ m)
    (hinv : (negabinSpec m).1.1 = -(2 ^ bitLen m : Int) ∧
            -(2 ^ bitLen m : Int) ≤ (negabinSpec m).1.2.1 ∧ (negabinSpec m).1.2.1 ≤ 0 ∧
            -(2 ^ bitLen m : Int) ≤ (negabinSpec m).1.2.2 ∧ (negabinSpec m).1.2.2 ≤ 0)
    (k : Nat) :
    (negabinSpec (m * 2 ^ k)).1.1 = -(2 ^ bitLen (m * 2 ^ k) : Int) ∧
    -(2 ^ bitLen (m * 2 ^ k) : Int) ≤ (negabinSpec (m * 2 ^ k)).1.2.1 ∧
    (negabinSpec (m * 2 ^ k)).1.2.1 ≤ 0 ∧
    -(2 ^ bitLen (m * 2 ^ k) : Int) ≤ (negabinSpec (m * 2 ^ k)).1.2.2 ∧
    (negabinSpec (m * 2 ^ k)).1.2.2 ≤ 0 := by
  induction k with
  | zero => simpa using hinv
  | succ k ih =>
    have hmul : m * 2 ^ (k + 1) = 2 * (m * 2 ^ k) := mul_two_pow_succ m k
    have hpos : 1 ≤ m * 2 ^ k := Nat.mul_pos hm (Nat.two_pow_pos k)
    rw [hmul, negabinSpec_two_mul (m * 2 ^ k) hpos, bitLen_two_mul (m * 2 ^ k) hpos]
    rcases hsp : negabinSpec (m * 2 ^ k) with ⟨⟨b0, bp, bm⟩, _, _⟩
    rw [hsp] at ih
    dsimp only at ih ⊢
    have hS : (2 ^ (bitLen (m * 2 ^ k) + 1) : Int) = 2 * (2 ^ bitLen (m * 2 ^ k) : Int) := by
      rw [Int.pow_succ]; omega
    rw [hS]; omega

private theorem negabinSpec_neg_minimizers (k : Nat) :
    (negabinSpec (3 * 2 ^ k)).1.1 = -(2 ^ bitLen (3 * 2 ^ k) : Int) ∧
    (negabinSpec (7 * 2 ^ k)).1.1 = -(2 ^ bitLen (7 * 2 ^ k) : Int) ∧
    (negabinSpec (13 * 2 ^ k)).1.1 = -(2 ^ bitLen (13 * 2 ^ k) : Int) := by
  have h7 := negabinSpec_neg_ray_invariant 7 (by omega) (by simp [ns_7, bl_7]) k
  have h13 := negabinSpec_neg_ray_invariant 13 (by omega) (by simp [ns_13, bl_13]) k
  have h3 : (negabinSpec (3 * 2 ^ k)).1.1 = -(2 ^ bitLen (3 * 2 ^ k) : Int) := by
    by_cases hk : k < 2
    · have : k = 0 ∨ k = 1 := by omega
      rcases this with rfl | rfl
      · simp [ns_3, bl_3]
      · simp [ns_6, bl_6]
    · have h12 := negabinSpec_neg_ray_invariant 12 (by omega) (by simp [ns_12, bl_12]) (k - 2)
      have heq : 12 * 2 ^ (k - 2) = 3 * 2 ^ k := by
        have h2 : 2 ^ k = 4 * 2 ^ (k - 2) := by
          have := Nat.pow_add 2 2 (k - 2)
          rw [show 2 + (k - 2) = k by omega] at this
          omega
        omega
      rw [heq] at h12
      exact h12.1
  exact ⟨h3, h7.1, h13.1⟩

theorem negabinBias_eq_neg_one_third_iff (m : Nat) (hm : 1 ≤ m) :
    (negabinSpec m).1.1 = -(2 ^ bitLen m : Int) ↔
      ∃ k : Nat, m = 3 * 2 ^ k ∨ m = 7 * 2 ^ k ∨ m = 13 * 2 ^ k := by
  constructor
  · intro heq
    induction m using Nat.strongRecOn with
    | ind m ih =>
      by_cases h8 : m < 8
      · have : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 := by omega
        rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · simp [ns_1, bl_1] at heq
        · simp [ns_2, bl_2] at heq
        · exact ⟨0, Or.inl rfl⟩
        · simp [ns_4, bl_4] at heq
        · simp [ns_5, bl_5] at heq
        · exact ⟨1, Or.inl rfl⟩
        · exact ⟨0, Or.inr (Or.inl rfl)⟩
      · by_cases hpar : m % 2 = 0
        · have hq_pos : 1 ≤ m / 2 := by omega
          have hq_lt : m / 2 < m := Nat.div_lt_self (by omega) (by omega)
          have hm_eq : m = 2 * (m / 2) := by omega
          rw [hm_eq, negabinSpec_two_mul (m / 2) hq_pos, bitLen_two_mul (m / 2) hq_pos] at heq
          rcases hsp : negabinSpec (m / 2) with ⟨⟨b0, bp, bm⟩, _, _⟩
          rw [hsp] at heq
          dsimp only at heq
          have hS : (2 ^ (bitLen (m / 2) + 1) : Int) = 2 * (2 ^ bitLen (m / 2) : Int) := by
            rw [Int.pow_succ]; omega
          have hq_eq : (negabinSpec (m / 2)).1.1 = -(2 ^ bitLen (m / 2) : Int) := by
            rw [hsp]; dsimp only; omega
          rcases ih (m / 2) hq_lt hq_pos hq_eq with ⟨r, hr | hr | hr⟩
          · exact ⟨r + 1, Or.inl (by rw [hm_eq, hr, mul_two_pow_succ])⟩
          · exact ⟨r + 1, Or.inr (Or.inl (by rw [hm_eq, hr, mul_two_pow_succ]))⟩
          · exact ⟨r + 1, Or.inr (Or.inr (by rw [hm_eq, hr, mul_two_pow_succ]))⟩
        · have hq_ge : 4 ≤ m / 2 := by omega
          have hq_lt : m / 2 < m := Nat.div_lt_self (by omega) (by omega)
          have hm_eq : m = 2 * (m / 2) + 1 := by omega
          rw [hm_eq, negabinSpec_two_mul_add_one (m / 2), bitLen_two_mul_add_one (m / 2)] at heq
          rcases hsp : negabinSpec (m / 2) with ⟨⟨b0, bp, bm⟩, _, _⟩
          rw [hsp] at heq
          dsimp only at heq
          have hS : (2 ^ (bitLen (m / 2) + 1) : Int) = 2 * (2 ^ bitLen (m / 2) : Int) := by
            rw [Int.pow_succ]; omega
          have hcube := negabinSpec_cube (m / 2) hq_ge
          rw [hsp] at hcube; dsimp only at hcube
          have hb0_eq : (negabinSpec (m / 2)).1.1 = -(2 ^ bitLen (m / 2) : Int) := by
            rw [hsp]; dsimp only; omega
          have hbm_pos : (negabinSpec (m / 2)).1.2.2 = (2 ^ bitLen (m / 2) : Int) := by
            rw [hsp]; dsimp only; omega
          have h2pos : (0 : Int) < (2 ^ bitLen (m / 2) : Int) := by
            exact_mod_cast Nat.two_pow_pos (bitLen (m / 2))
          rcases ih (m / 2) hq_lt (by omega) hb0_eq with ⟨r, hr | hr | hr⟩
          · by_cases hr2 : r < 2
            · have : r = 0 ∨ r = 1 := by omega
              rcases this with rfl | rfl
              · omega
              · have hm13 : m = 13 := by omega
                exact ⟨0, Or.inr (Or.inr hm13)⟩
            · have h12 := negabinSpec_neg_ray_invariant 12 (by omega) (by simp [ns_12, bl_12]) (r - 2)
              have heq12 : 12 * 2 ^ (r - 2) = 3 * 2 ^ r := by
                have h2 : 2 ^ r = 4 * 2 ^ (r - 2) := by
                  have := Nat.pow_add 2 2 (r - 2)
                  rw [show 2 + (r - 2) = r by omega] at this
                  omega
                omega
              rw [heq12, ← hr] at h12
              have hle0 := h12.2.2.2.2
              omega
          · have h7 := negabinSpec_neg_ray_invariant 7 (by omega) (by simp [ns_7, bl_7]) r
            rw [← hr] at h7
            have hle0 := h7.2.2.2.2
            omega
          · have h13 := negabinSpec_neg_ray_invariant 13 (by omega) (by simp [ns_13, bl_13]) r
            rw [← hr] at h13
            have hle0 := h13.2.2.2.2
            omega
  · rintro ⟨k, rfl | rfl | rfl⟩
    · exact (negabinSpec_neg_minimizers k).1
    · exact (negabinSpec_neg_minimizers k).2.1
    · exact (negabinSpec_neg_minimizers k).2.2

/-! ## Section 4: Infinite Zero-Bias Kernel & Exact Period-2 Collapse -/

private theorem negabinSpec_mul_two_pow_head (m : Nat) (hm : 1 ≤ m) (r : Nat) :
    (negabinSpec (m * 2 ^ r)).1.1 = (2 ^ r : Int) * (negabinSpec m).1.1 ∧
    (negabinSpec (m * 2 ^ r)).2.1.1 = (2 ^ r : Int) * (negabinSpec m).2.1.1 ∧
    (negabinSpec (m * 2 ^ r)).2.2.1 = (2 ^ r : Int) * (negabinSpec m).2.2.1 := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hmul : m * 2 ^ (r + 1) = 2 * (m * 2 ^ r) := mul_two_pow_succ m r
    have hpos : 1 ≤ m * 2 ^ r := Nat.mul_pos hm (Nat.two_pow_pos r)
    rw [hmul, negabinSpec_two_mul (m * 2 ^ r) hpos]
    rcases hsp : negabinSpec (m * 2 ^ r) with ⟨⟨b0, bp, bm⟩, ⟨o0, op, om⟩, ⟨d0, dp, dm⟩⟩
    rw [hsp] at ih
    dsimp only at ih ⊢
    have h2 : (2 ^ (r + 1) : Int) = 2 * (2 ^ r : Int) := by rw [Int.pow_succ]; omega
    rw [h2, ih.1, ih.2.1, ih.2.2]
    exact ⟨by grind, by grind, by grind⟩

theorem negabinZeroBias_bounded_family (r k : Nat) :
    (negabinSpec (5 * 2 ^ r)).1.1 = 0 ∧
    negabinParitySum (bitLen (5 * 2 ^ r) + k) (5 * 2 ^ r) .zero =
      (2 ^ r : Int) * (3 + (-1 : Int) ^ k) ∧
    (negabinSpec (9 * 2 ^ r)).1.1 = 0 ∧
    negabinParitySum (bitLen (9 * 2 ^ r) + k) (9 * 2 ^ r) .zero =
      (2 ^ r : Int) * (3 + (-1 : Int) ^ k) ∧
    (negabinSpec (15 * 2 ^ r)).1.1 = 0 ∧
    negabinParitySum (bitLen (15 * 2 ^ r) + k) (15 * 2 ^ r) .zero =
      -(2 ^ r : Int) * (3 + (-1 : Int) ^ k) := by
  have h5_head := negabinSpec_mul_two_pow_head 5 (by omega) r
  have h9_head := negabinSpec_mul_two_pow_head 9 (by omega) r
  have h15_head := negabinSpec_mul_two_pow_head 15 (by omega) r
  rw [ns_5] at h5_head; rw [ns_9] at h9_head; rw [ns_15] at h15_head
  dsimp only at h5_head h9_head h15_head
  have h5_sp := (negabinParitySum_spectral (5 * 2 ^ r) k).1
  have h9_sp := (negabinParitySum_spectral (9 * 2 ^ r) k).1
  have h15_sp := (negabinParitySum_spectral (15 * 2 ^ r) k).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · rw [h5_head.1, h5_head.2.1, h5_head.2.2] at h5_sp; grind
  · omega
  · rw [h9_head.1, h9_head.2.1, h9_head.2.2] at h9_sp; grind
  · omega
  · rw [h15_head.1, h15_head.2.1, h15_head.2.2] at h15_sp; grind

/-! ## Section 5: Standard Binary (Base `+2`) Spectral Decomposition & Asymmetric (-1/9, +1/3] Barrier -/

private theorem base2ParitySum_step (w q : Nat) :
    (base2ParitySum (w + 1) (2 * q) .zero = 2 * base2ParitySum w q .zero ∧
     base2ParitySum (w + 1) (2 * q) .one =
       base2ParitySum w q .zero - base2ParitySum w q .one) ∧
    (base2ParitySum (w + 1) (2 * q + 1) .zero =
       base2ParitySum w q .zero - base2ParitySum w q .one ∧
     base2ParitySum (w + 1) (2 * q + 1) .one = -2 * base2ParitySum w q .one) := by
  have he : (2 * q) % 2 = 0 ∧ (2 * q) / 2 = q := by omega
  have ho : (2 * q + 1) % 2 = 1 ∧ (2 * q + 1) / 2 = q := by omega
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [base2ParitySum_split, he.1, he.2]; simp [base2Step, BinCarry.toInt, signOfNat]; omega
  · rw [base2ParitySum_split, he.1, he.2]; simp [base2Step, BinCarry.toInt, signOfNat]; omega
  · rw [base2ParitySum_split, ho.1, ho.2]; simp [base2Step, BinCarry.toInt, signOfNat]; omega
  · rw [base2ParitySum_split, ho.1, ho.2]; simp [base2Step, BinCarry.toInt, signOfNat]; omega

private theorem base2ParitySum_zero (w : Nat) :
    base2ParitySum w 0 .zero = (2 ^ w : Int) ∧
    3 * base2ParitySum w 0 .one = (2 ^ w : Int) + 2 * (-1 : Int) ^ w := by
  induction w with
  | zero =>
    refine ⟨?_, ?_⟩ <;>
      simp [base2ParitySum, sumRange, base2Carries_zero, signOfNat]
  | succ w ih =>
    have hst := (base2ParitySum_step w 0).1
    simp only [Nat.mul_zero] at hst
    have h2 : (2 ^ (w + 1) : Int) = 2 * (2 ^ w : Int) := by rw [Int.pow_succ]; omega
    have h1 : (-1 : Int) ^ (w + 1) = -((-1 : Int) ^ w) := by rw [Int.pow_succ]; omega
    refine ⟨by rw [hst.1, ih.1, h2], ?_⟩
    rw [hst.2, ih.1, h2, h1]; omega

theorem base2ParitySum_spectral (m k : Nat) :
    let ((g0, g1), (u0, u1)) := base2Spec m
    3 * base2ParitySum (bitLen m + k) m .zero = g0 * (2 ^ k : Int) + u0 * (-1 : Int) ^ k ∧
    3 * base2ParitySum (bitLen m + k) m .one = g1 * (2 ^ k : Int) + u1 * (-1 : Int) ^ k := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    by_cases hm : m = 0
    · subst hm
      rw [base2Spec_zero, bitLen_zero, Nat.zero_add]
      dsimp only
      have ⟨h0, h1⟩ := base2ParitySum_zero k
      exact ⟨by omega, by omega⟩
    · have hq_lt : m / 2 < m := Nat.div_lt_self (by omega) (by omega)
      have ihq := ih (m / 2) hq_lt
      by_cases hpar : m % 2 = 0
      · have hq_pos : 1 ≤ m / 2 := by omega
        have hm_eq : m = 2 * (m / 2) := by omega
        rw [hm_eq, base2Spec_two_mul (m / 2) hq_pos, bitLen_two_mul (m / 2) hq_pos]
        have hidx : bitLen (m / 2) + 1 + k = (bitLen (m / 2) + k) + 1 := by omega
        rw [hidx]
        have hst := (base2ParitySum_step (bitLen (m / 2) + k) (m / 2)).1
        rcases hsp : base2Spec (m / 2) with ⟨⟨g0, g1⟩, ⟨u0, u1⟩⟩
        rw [hsp] at ihq
        dsimp only at ihq ⊢
        exact ⟨by rw [hst.1]; grind, by rw [hst.2]; grind⟩
      · have hm_eq : m = 2 * (m / 2) + 1 := by omega
        rw [hm_eq, base2Spec_two_mul_add_one (m / 2), bitLen_two_mul_add_one (m / 2)]
        have hidx : bitLen (m / 2) + 1 + k = (bitLen (m / 2) + k) + 1 := by omega
        rw [hidx]
        have hst := (base2ParitySum_step (bitLen (m / 2) + k) (m / 2)).2
        rcases hsp : base2Spec (m / 2) with ⟨⟨g0, g1⟩, ⟨u0, u1⟩⟩
        rw [hsp] at ihq
        dsimp only at ihq ⊢
        exact ⟨by rw [hst.1]; grind, by rw [hst.2]; grind⟩

private theorem base2Spec_polygon (m : Nat) (hm : 1 ≤ m) :
    -(2 ^ bitLen m : Int) < 3 * (base2Spec m).1.1 ∧
    (base2Spec m).1.1 ≤ (2 ^ bitLen m : Int) ∧
    -(2 ^ bitLen m : Int) ≤ (base2Spec m).1.2 ∧
    (base2Spec m).1.2 ≤ (2 ^ bitLen m : Int) ∧
    -2 * (2 ^ bitLen m : Int) < 3 * ((base2Spec m).1.1 - (base2Spec m).1.2) ∧
    -4 * (2 ^ bitLen m : Int) < 3 * ((base2Spec m).1.1 + (base2Spec m).1.2) := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    by_cases h1 : m = 1
    · subst h1; simp [bs_1, bl_1]
    · have hq_pos : 1 ≤ m / 2 := by omega
      have hq_lt : m / 2 < m := Nat.div_lt_self (by omega) (by omega)
      have ihq := ih (m / 2) hq_lt hq_pos
      have hS_pos : (0 : Int) < (2 ^ bitLen (m / 2) : Int) := by
        exact_mod_cast Nat.two_pow_pos (bitLen (m / 2))
      by_cases hpar : m % 2 = 0
      · have hm_eq : m = 2 * (m / 2) := by omega
        rw [hm_eq, base2Spec_two_mul (m / 2) hq_pos, bitLen_two_mul (m / 2) hq_pos]
        rcases hsp : base2Spec (m / 2) with ⟨⟨g0, g1⟩, _⟩
        rw [hsp] at ihq
        dsimp only at ihq ⊢
        have hS : (2 ^ (bitLen (m / 2) + 1) : Int) = 2 * (2 ^ bitLen (m / 2) : Int) := by
          rw [Int.pow_succ]; omega
        rw [hS]; omega
      · have hm_eq : m = 2 * (m / 2) + 1 := by omega
        rw [hm_eq, base2Spec_two_mul_add_one (m / 2), bitLen_two_mul_add_one (m / 2)]
        rcases hsp : base2Spec (m / 2) with ⟨⟨g0, g1⟩, _⟩
        rw [hsp] at ihq
        dsimp only at ihq ⊢
        have hS : (2 ^ (bitLen (m / 2) + 1) : Int) = 2 * (2 ^ bitLen (m / 2) : Int) := by
          rw [Int.pow_succ]; omega
        rw [hS]; omega

private theorem base2Spec_sharp_family (r : Nat) :
    let mr := 3 * 2 ^ (2 * r + 1) - 1
    bitLen mr = 2 * r + 3 ∧
    3 * (base2Spec mr).1.1 = -(2 ^ bitLen mr : Int) + 8 ∧
    (base2Spec mr).1.2 = -(2 ^ bitLen mr : Int) := by
  induction r with
  | zero => simp [bs_5, bl_5]
  | succ r ih =>
    let m0 := 3 * 2 ^ (2 * r + 1) - 1
    let m1 := 2 * m0 + 1
    let m2 := 2 * m1 + 1
    have hpow_pos : 1 ≤ 2 ^ (2 * r + 1) := Nat.two_pow_pos (2 * r + 1)
    have hm2_eq : 3 * 2 ^ (2 * (r + 1) + 1) - 1 = m2 := by
      have h4 : 2 ^ (2 * (r + 1) + 1) = 4 * 2 ^ (2 * r + 1) := by
        rw [show 2 * (r + 1) + 1 = (2 * r + 1) + 2 by omega, Nat.pow_add]; omega
      dsimp only [m2, m1, m0]; omega
    dsimp only
    rw [hm2_eq]
    have hlen1 : bitLen m1 = 2 * r + 4 := by
      dsimp only [m1]; rw [bitLen_two_mul_add_one m0, ih.1]
    have hlen2 : bitLen m2 = 2 * r + 5 := by
      dsimp only [m2]; rw [bitLen_two_mul_add_one m1, hlen1]
    have hsp1 : base2Spec m1 =
        let ((g0, g1), (u0, u1)) := base2Spec m0
        ((g0 - g1, -2 * g1), (u0 - u1, -2 * u1)) :=
      base2Spec_two_mul_add_one m0
    have hsp2 : base2Spec m2 =
        let ((g0, g1), (u0, u1)) := base2Spec m1
        ((g0 - g1, -2 * g1), (u0 - u1, -2 * u1)) :=
      base2Spec_two_mul_add_one m1
    rcases hsp0 : base2Spec m0 with ⟨⟨g0, g1⟩, ⟨u0, u1⟩⟩
    dsimp only at ih
    change bitLen m0 = 2 * r + 3 ∧ 3 * (base2Spec m0).1.1 = -(2 ^ bitLen m0 : Int) + 8 ∧
      (base2Spec m0).1.2 = -(2 ^ bitLen m0 : Int) at ih
    rw [hsp0] at hsp1 ih
    dsimp only at hsp1 ih
    rw [hsp1] at hsp2
    dsimp only at hsp2
    rw [hsp2, hlen2]
    dsimp only
    have h2_2 : (2 ^ (2 * r + 5) : Int) = 4 * (2 ^ (2 * r + 3) : Int) := by
      rw [show 2 * r + 5 = (2 * r + 3) + 2 by omega, Int.pow_add]; omega
    rw [ih.1] at ih
    refine ⟨by omega, ?_, ?_⟩
    · rw [h2_2]; omega
    · rw [h2_2]; omega

theorem base2Bias_asymmetric_barrier :
    (∀ m : Nat, 1 ≤ m →
      -(2 ^ bitLen m : Int) < 3 * (base2Spec m).1.1 ∧
      (base2Spec m).1.1 ≤ (2 ^ bitLen m : Int)) ∧
    (∀ r : Nat,
      let mr := 3 * 2 ^ (2 * r + 1) - 1
      bitLen mr = 2 * r + 3 ∧
      3 * (base2Spec mr).1.1 = -(2 ^ bitLen mr : Int) + 8) := by
  refine ⟨?_, ?_⟩
  · intro m hm
    have hp := base2Spec_polygon m hm
    exact ⟨hp.1, hp.2.1⟩
  · intro r
    have h := base2Spec_sharp_family r
    exact ⟨h.1, h.2.1⟩

private theorem base2Spec_pos_ray_invariant (m : Nat) (hm : 1 ≤ m)
    (hinv : (base2Spec m).1.1 = (2 ^ bitLen m : Int) ∧
            0 ≤ (base2Spec m).1.2 ∧ (base2Spec m).1.2 ≤ (2 ^ bitLen m : Int))
    (k : Nat) :
    (base2Spec (m * 2 ^ k)).1.1 = (2 ^ bitLen (m * 2 ^ k) : Int) ∧
    0 ≤ (base2Spec (m * 2 ^ k)).1.2 ∧
    (base2Spec (m * 2 ^ k)).1.2 ≤ (2 ^ bitLen (m * 2 ^ k) : Int) := by
  induction k with
  | zero => simpa using hinv
  | succ k ih =>
    have hmul : m * 2 ^ (k + 1) = 2 * (m * 2 ^ k) := mul_two_pow_succ m k
    have hpos : 1 ≤ m * 2 ^ k := Nat.mul_pos hm (Nat.two_pow_pos k)
    rw [hmul, base2Spec_two_mul (m * 2 ^ k) hpos, bitLen_two_mul (m * 2 ^ k) hpos]
    rcases hsp : base2Spec (m * 2 ^ k) with ⟨⟨g0, g1⟩, _⟩
    rw [hsp] at ih; dsimp only at ih ⊢
    have hS : (2 ^ (bitLen (m * 2 ^ k) + 1) : Int) = 2 * (2 ^ bitLen (m * 2 ^ k) : Int) := by
      rw [Int.pow_succ]; omega
    rw [hS]; omega

theorem base2Bias_eq_pos_one_third_iff (m : Nat) (hm : 1 ≤ m) :
    (base2Spec m).1.1 = (2 ^ bitLen m : Int) ↔ ∃ k : Nat, m = 2 ^ k ∨ m = 3 * 2 ^ k := by
  constructor
  · intro heq
    induction m using Nat.strongRecOn with
    | ind m ih =>
      by_cases h4 : m < 4
      · have : m = 1 ∨ m = 2 ∨ m = 3 := by omega
        rcases this with rfl | rfl | rfl
        · exact ⟨0, Or.inl rfl⟩
        · exact ⟨1, Or.inl rfl⟩
        · exact ⟨0, Or.inr rfl⟩
      · by_cases hpar : m % 2 = 0
        · have hq_pos : 1 ≤ m / 2 := by omega
          have hq_lt : m / 2 < m := Nat.div_lt_self (by omega) (by omega)
          have hm_eq : m = 2 * (m / 2) := by omega
          rw [hm_eq, base2Spec_two_mul (m / 2) hq_pos, bitLen_two_mul (m / 2) hq_pos] at heq
          rcases hsp : base2Spec (m / 2) with ⟨⟨g0, g1⟩, _⟩
          rw [hsp] at heq; dsimp only at heq
          have hS : (2 ^ (bitLen (m / 2) + 1) : Int) = 2 * (2 ^ bitLen (m / 2) : Int) := by
            rw [Int.pow_succ]; omega
          have hq_eq : (base2Spec (m / 2)).1.1 = (2 ^ bitLen (m / 2) : Int) := by
            rw [hsp]; dsimp only; omega
          rcases ih (m / 2) hq_lt hq_pos hq_eq with ⟨r, hr | hr⟩
          · exact ⟨r + 1, Or.inl (by rw [hm_eq, hr, Nat.pow_succ]; omega)⟩
          · exact ⟨r + 1, Or.inr (by rw [hm_eq, hr, mul_two_pow_succ])⟩
        · have hq_ge : 2 ≤ m / 2 := by omega
          have hq_lt : m / 2 < m := Nat.div_lt_self (by omega) (by omega)
          have hm_eq : m = 2 * (m / 2) + 1 := by omega
          rw [hm_eq, base2Spec_two_mul_add_one (m / 2), bitLen_two_mul_add_one (m / 2)] at heq
          rcases hsp : base2Spec (m / 2) with ⟨⟨g0, g1⟩, _⟩
          rw [hsp] at heq; dsimp only at heq
          have hS : (2 ^ (bitLen (m / 2) + 1) : Int) = 2 * (2 ^ bitLen (m / 2) : Int) := by
            rw [Int.pow_succ]; omega
          have hpoly := base2Spec_polygon (m / 2) (by omega)
          rw [hsp] at hpoly; dsimp only at hpoly
          have hg0_eq : (base2Spec (m / 2)).1.1 = (2 ^ bitLen (m / 2) : Int) := by
            rw [hsp]; dsimp only; omega
          have hg1_neg : (base2Spec (m / 2)).1.2 = -(2 ^ bitLen (m / 2) : Int) := by
            rw [hsp]; dsimp only; omega
          have h2pos : (0 : Int) < (2 ^ bitLen (m / 2) : Int) := by
            exact_mod_cast Nat.two_pow_pos (bitLen (m / 2))
          rcases ih (m / 2) hq_lt (by omega) hg0_eq with ⟨r, hr | hr⟩
          · have hr1 : 1 ≤ r := by
              cases r with
              | zero => simp at hr; omega
              | succ _ => omega
            have h2 := base2Spec_pos_ray_invariant 2 (by omega) (by simp [bs_2, bl_2]) (r - 1)
            have heq2 : 2 * 2 ^ (r - 1) = 2 ^ r := by
              conv => rhs; rw [show r = (r - 1) + 1 by omega, Nat.pow_succ]
              omega
            rw [heq2, ← hr] at h2
            have hge0 := h2.2.1
            omega
          · have h3 := base2Spec_pos_ray_invariant 3 (by omega) (by simp [bs_3, bl_3]) r
            rw [← hr] at h3
            have hge0 := h3.2.1
            omega
  · rintro ⟨k, rfl | rfl⟩
    · cases k with
      | zero => simp [bs_1, bl_1]
      | succ k =>
        have h2 := base2Spec_pos_ray_invariant 2 (by omega) (by simp [bs_2, bl_2]) k
        have heq2 : 2 * 2 ^ k = 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
        rw [heq2] at h2
        exact h2.1
    · exact (base2Spec_pos_ray_invariant 3 (by omega) (by simp [bs_3, bl_3]) k).1

end NegabinaryCarryParityBias
