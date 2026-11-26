/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BitSerialLutDag.FinSum

/-!
# Bit-Serial `POPCNT` Identity, LUT-vs-`POPCNT` Crossover & `int16` Overflow (`BitSerialLutDag.PopcntAndCost`)

Proves:
- Headline Theorem 4 (`popcnt_zero_lut_exact_bitserial_dot_identity`):
  Universal exact bit-serial `POPCNT` dot-product identities for binary `{-1, +1}` and
  ternary `{-1, 0, +1}` weights against arbitrary `b`-bit signed (two's-complement) or
  unsigned activations, plus exact two's-complement bit-decomposition roundtrip for all `b ≥ 1`.
- Headline Theorem 5 (`lut_vs_popcnt_amortization_crossover_exact`):
  Exact rational amortization crossover `R* = (setup_lut - setup_pop) / (steady_pop - steady_lut)`,
  the RDNA 3 no-crossover dominance theorem (`POPCNT` wins for all `M, N, K > 0`), and exact
  `gfx1100` specializations (`1/2 < 3/4` steady-state, `3/2×` `g=6` vs `g=4` lookup reduction).
- Headline Theorem 6 (`tmac_int16_overflow_threshold_exact`):
  Exact `int16` accumulation safety bounds, `K_max = 258` (symmetric `int8` `[-127, 127]`),
  and the exact two's-complement wrap-by-1 trap (`+32768 ≡ -32768 (mod 2^16)`) at `K = 256`
  for full `int8`, `K = 128` for direct INT2, and `K = 64` for direct INT3.
-/

namespace BitSerialLutDag

/-! ## Pure-`Init` `Rat` Order Helpers -/

theorem rat_sub_nonneg {a b : Rat} (h : b ≤ a) : (0 : Rat) ≤ a - b := by
  have := Rat.add_le_add_right (c := -b) |>.mpr h
  grind

theorem rat_le_of_sub_nonneg {a b : Rat} (h : (0 : Rat) ≤ a - b) : b ≤ a := by
  have := Rat.add_le_add_right (c := b) |>.mpr h
  grind

theorem rat_sub_pos {a b : Rat} (h : b < a) : (0 : Rat) < a - b := by
  have h1 : (0 : Rat) ≤ a - b := rat_sub_nonneg (Rat.le_of_lt h)
  have hne : a - b ≠ 0 := by
    intro h0
    have heq : a = b := by grind
    exact Rat.ne_of_gt h heq
  exact Rat.lt_of_le_of_ne h1 (Ne.symm hne)

theorem rat_lt_of_sub_pos {a b : Rat} (h : (0 : Rat) < a - b) : b < a := by
  have h1 : b ≤ a := rat_le_of_sub_nonneg (Rat.le_of_lt h)
  have hne : b ≠ a := by
    intro h0
    have : a - b = 0 := by grind
    exact Rat.ne_of_gt h this
  exact Rat.lt_of_le_of_ne h1 hne

theorem rat_mul_pos {a b : Rat} (ha : (0 : Rat) < a) (hb : (0 : Rat) < b) :
    (0 : Rat) < a * b := by
  have h1 : (0 : Rat) ≤ a * b := Rat.mul_nonneg (Rat.le_of_lt ha) (Rat.le_of_lt hb)
  have hne : a * b ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact Rat.ne_of_gt ha h
    | inr h => exact Rat.ne_of_gt hb h
  exact Rat.lt_of_le_of_ne h1 (Ne.symm hne)

theorem rat_inv_pos {a : Rat} (ha : (0 : Rat) < a) : (0 : Rat) < a⁻¹ := by
  have hne : a ≠ 0 := Rat.ne_of_gt ha
  by_cases hpos : (0 : Rat) < a⁻¹
  · exact hpos
  · have hle : a⁻¹ ≤ 0 := Rat.not_lt.mp hpos
    have hneg_inv : (0 : Rat) ≤ -a⁻¹ := by
      have := rat_sub_nonneg hle
      grind
    have hmul : (0 : Rat) ≤ a * (-a⁻¹) := Rat.mul_nonneg (Rat.le_of_lt ha) hneg_inv
    have hval : a * (-a⁻¹) = -1 := by
      have h1 : a * a⁻¹ = 1 := Rat.mul_inv_cancel a hne
      grind
    rw [hval] at hmul
    exact absurd hmul (by decide)

theorem rat_div_pos {a b : Rat} (ha : (0 : Rat) < a) (hb : (0 : Rat) < b) :
    (0 : Rat) < a / b := by
  rw [Rat.div_def]
  exact rat_mul_pos ha (rat_inv_pos hb)

theorem rat_mul_lt_mul_of_pos_left {a b c : Rat} (h : a < b) (hc : (0 : Rat) < c) :
    c * a < c * b := by
  apply rat_lt_of_sub_pos
  have h1 : (0 : Rat) < c * (b - a) := rat_mul_pos hc (rat_sub_pos h)
  have heq : c * b - c * a = c * (b - a) := by grind
  rw [heq]; exact h1

theorem rat_mul_lt_mul_of_pos_right {a b c : Rat} (h : a < b) (hc : (0 : Rat) < c) :
    a * c < b * c := by
  rw [Rat.mul_comm a c, Rat.mul_comm b c]
  exact rat_mul_lt_mul_of_pos_left h hc

theorem rat_mul_le_mul_of_nonneg_left {a b c : Rat} (h : a ≤ b) (hc : (0 : Rat) ≤ c) :
    c * a ≤ c * b := by
  apply rat_le_of_sub_nonneg
  have h1 : (0 : Rat) ≤ c * (b - a) := Rat.mul_nonneg hc (rat_sub_nonneg h)
  have heq : c * b - c * a = c * (b - a) := by grind
  rw [heq]; exact h1

theorem rat_add_lt_add_of_le_of_lt {a b c d : Rat} (h1 : a ≤ b) (h2 : c < d) :
    a + c < b + d := by
  apply rat_lt_of_sub_pos
  have hs1 : (0 : Rat) ≤ b - a := rat_sub_nonneg h1
  have hs2 : (0 : Rat) < d - c := rat_sub_pos h2
  have hsum : (0 : Rat) ≤ (b - a) + (d - c) := by
    have ha := (Rat.add_le_add_right (c := d - c)).mpr hs1
    have hb : (0 : Rat) ≤ d - c := Rat.le_of_lt hs2
    have h0 : (0 : Rat) + (d - c) = d - c := by grind
    rw [h0] at ha
    exact Rat.le_trans hb ha
  have hne : (b - a) + (d - c) ≠ 0 := by
    intro h0
    have hle : d - c ≤ 0 := by
      have heq : d - c = -(b - a) := by grind
      have hneg : -(b - a) ≤ 0 := by
        have := (Rat.add_le_add_right (c := -(b - a))).mpr hs1
        grind
      rw [heq]; exact hneg
    exact Rat.not_le.mpr hs2 hle
  have hpos : (0 : Rat) < (b - a) + (d - c) := Rat.lt_of_le_of_ne hsum (Ne.symm hne)
  have heq : (b + d) - (a + c) = (b - a) + (d - c) := by grind
  rw [heq]; exact hpos

/-! ## Headline Theorem 4: Universal Bit-Serial `POPCNT` Dot-Product Identity -/

theorem boolToInt_and (p q : Bool) :
    boolToInt p * boolToInt q = boolToInt (p && q) := by
  cases p <;> cases q <;> rfl

theorem popcnt_eq_finSumInt {K : Nat} (plane : Fin K → Bool) :
    (popcnt plane : Int) = finSumInt (fun i => boolToInt (plane i)) := by
  unfold popcnt
  rw [← finSumInt_ofNat]
  apply finSumInt_congr
  intro i
  cases plane i <;> rfl

theorem popcnt_binary_bitplane_identity {K : Nat} (wPlane aPlane : Fin K → Bool) :
    finSumInt (fun i => binWeight (wPlane i) * boolToInt (aPlane i)) =
      2 * (popcnt (andPlane wPlane aPlane) : Int) - (popcnt aPlane : Int) := by
  rw [popcnt_eq_finSumInt, popcnt_eq_finSumInt, ← finSumInt_mul_left, ← finSumInt_sub]
  apply finSumInt_congr
  intro i
  unfold binWeight andPlane
  rw [← boolToInt_and]
  rw [Int.sub_mul, Int.one_mul, Int.mul_assoc]

theorem popcnt_ternary_bitplane_identity {K : Nat} (wPos wNeg aPlane : Fin K → Bool) :
    finSumInt (fun i => ternWeight (wPos i) (wNeg i) * boolToInt (aPlane i)) =
      (popcnt (andPlane wPos aPlane) : Int) - (popcnt (andPlane wNeg aPlane) : Int) := by
  rw [popcnt_eq_finSumInt, popcnt_eq_finSumInt, ← finSumInt_sub]
  apply finSumInt_congr
  intro i
  unfold ternWeight andPlane
  rw [← boolToInt_and, ← boolToInt_and, Int.sub_mul]

theorem popcnt_binary_dot_exact {K b : Nat} (signed : Bool)
    (wPlane : Fin K → Bool) (aPlanes : Fin b → Fin K → Bool) :
    dotInt (fun i => binWeight (wPlane i))
      (fun i => bitsToInt b signed (fun j => aPlanes j i)) =
      popcntBinaryDot signed wPlane aPlanes := by
  unfold dotInt bitsToInt popcntBinaryDot
  have h1 : finSumInt (fun i : Fin K =>
      binWeight (wPlane i) * finSumInt (fun j : Fin b => bitWeight b signed j * boolToInt (aPlanes j i))) =
      finSumInt (fun i : Fin K =>
        finSumInt (fun j : Fin b => bitWeight b signed j * (binWeight (wPlane i) * boolToInt (aPlanes j i)))) := by
    apply finSumInt_congr
    intro i
    rw [← finSumInt_mul_left]
    apply finSumInt_congr
    intro j
    rw [← Int.mul_assoc, Int.mul_comm (binWeight (wPlane i)) (bitWeight b signed j), Int.mul_assoc]
  rw [h1, finSumInt_swap]
  apply finSumInt_congr
  intro j
  rw [finSumInt_mul_left, popcnt_binary_bitplane_identity]

theorem popcnt_ternary_dot_exact {K b : Nat} (signed : Bool)
    (wPos wNeg : Fin K → Bool) (aPlanes : Fin b → Fin K → Bool) :
    dotInt (fun i => ternWeight (wPos i) (wNeg i))
      (fun i => bitsToInt b signed (fun j => aPlanes j i)) =
      popcntTernaryDot signed wPos wNeg aPlanes := by
  unfold dotInt bitsToInt popcntTernaryDot
  have h1 : finSumInt (fun i : Fin K =>
      ternWeight (wPos i) (wNeg i) *
        finSumInt (fun j : Fin b => bitWeight b signed j * boolToInt (aPlanes j i))) =
      finSumInt (fun i : Fin K =>
        finSumInt (fun j : Fin b =>
          bitWeight b signed j * (ternWeight (wPos i) (wNeg i) * boolToInt (aPlanes j i)))) := by
    apply finSumInt_congr
    intro i
    rw [← finSumInt_mul_left]
    apply finSumInt_congr
    intro j
    rw [← Int.mul_assoc, Int.mul_comm (ternWeight (wPos i) (wNeg i)) (bitWeight b signed j), Int.mul_assoc]
  rw [h1, finSumInt_swap]
  apply finSumInt_congr
  intro j
  rw [finSumInt_mul_left, popcnt_ternary_bitplane_identity]

/-! ## Universal `b`-Bit Two's-Complement Bit-Decomposition Roundtrip -/

theorem finSumAuxNat_testBit_mod (u : Nat) :
    ∀ {b : Nat} (k : Nat) (hk : k ≤ b),
      finSumAuxNat (fun j : Fin b => 2 ^ j.val * (if u.testBit j.val then 1 else 0)) k hk =
        u % 2 ^ k
  | _, 0, _ => by simp [finSumAuxNat, Nat.mod_one]
  | b, k + 1, hk => by
    rw [finSumAuxNat, finSumAuxNat_testBit_mod u k (Nat.le_of_succ_le hk)]
    have hbit : (if u.testBit k then 1 else 0) = (u / 2 ^ k) % 2 := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      have hmod2 : (u / 2 ^ k) % 2 = 0 ∨ (u / 2 ^ k) % 2 = 1 := by omega
      rcases hmod2 with h0 | h1
      · simp [h0]
      · simp [h1]
    dsimp only
    rw [hbit]
    have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := by rw [Nat.pow_succ]
    rw [hpow]
    have hdm1 := Nat.div_add_mod u (2 ^ k)
    have hdm2 := Nat.div_add_mod (u / 2 ^ k) 2
    have hlt1 : u % 2 ^ k < 2 ^ k := Nat.mod_lt u (Nat.pow_pos (by decide))
    have hlt2 : (u / 2 ^ k) % 2 < 2 := Nat.mod_lt _ (by decide)
    have hdecomp : u = (2 ^ k * 2) * (u / 2 ^ k / 2) + (u % 2 ^ k + 2 ^ k * ((u / 2 ^ k) % 2)) := by
      have h1 : 2 ^ k * (u / 2 ^ k) = 2 ^ k * (2 * (u / 2 ^ k / 2) + (u / 2 ^ k) % 2) := by
        rw [hdm2]
      rw [Nat.mul_add, ← Nat.mul_assoc] at h1
      omega
    have hrem_lt : u % 2 ^ k + 2 ^ k * ((u / 2 ^ k) % 2) < 2 ^ k * 2 := by
      have : (u / 2 ^ k) % 2 = 0 ∨ (u / 2 ^ k) % 2 = 1 := by omega
      rcases this with h0 | h1
      · rw [h0, Nat.mul_zero]; omega
      · rw [h1, Nat.mul_one]; omega
    have hrhs : u % (2 ^ k * 2) = u % 2 ^ k + 2 ^ k * ((u / 2 ^ k) % 2) := by
      have htmp : ((2 ^ k * 2) * (u / 2 ^ k / 2) + (u % 2 ^ k + 2 ^ k * ((u / 2 ^ k) % 2))) % (2 ^ k * 2) =
          u % 2 ^ k + 2 ^ k * ((u / 2 ^ k) % 2) := by
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hrem_lt]
      rw [← hdecomp] at htmp
      exact htmp
    exact hrhs.symm

theorem unsigned_bitsToInt_mod (b u : Nat) :
    bitsToInt b false (fun j => u.testBit j.val) = ((u % 2 ^ b : Nat) : Int) := by
  unfold bitsToInt
  have h1 : finSumInt (fun j : Fin b => bitWeight b false j * boolToInt (u.testBit j.val)) =
      finSumInt (fun j : Fin b => ((2 ^ j.val * (if u.testBit j.val then 1 else 0) : Nat) : Int)) := by
    apply finSumInt_congr
    intro j
    unfold bitWeight boolToInt
    simp only [Bool.false_and]
    cases u.testBit j.val <;> simp
  rw [h1, finSumInt_ofNat]
  unfold finSumNat
  rw [finSumAuxNat_testBit_mod u b (Nat.le_refl b)]

theorem signed_bitsToInt_twosComp {b : Nat} (hb : 1 ≤ b) (x : Int)
    (hlo : -((2 ^ (b - 1) : Nat) : Int) ≤ x) (hhi : x < ((2 ^ (b - 1) : Nat) : Int)) :
    bitsToInt b true (twosCompBits b x) = x := by
  cases b with
  | zero => omega
  | succ b' =>
    have hbsub : b' + 1 - 1 = b' := by omega
    rw [hbsub] at hlo hhi
    let u : Nat := (x % ((2 ^ (b' + 1) : Nat) : Int)).toNat
    have hpow : 2 ^ (b' + 1) = 2 ^ b' + 2 ^ b' := by rw [Nat.pow_succ]; omega
    have hpos : (0 : Int) < ((2 ^ (b' + 1) : Nat) : Int) := by
      have : 0 < 2 ^ (b' + 1) := Nat.pow_pos (by decide)
      omega
    have hmod_nonneg : 0 ≤ x % ((2 ^ (b' + 1) : Nat) : Int) := Int.emod_nonneg x (by omega)
    have hmod_lt : x % ((2 ^ (b' + 1) : Nat) : Int) < ((2 ^ (b' + 1) : Nat) : Int) :=
      Int.emod_lt_of_pos x hpos
    have hu_cast : (u : Int) = x % ((2 ^ (b' + 1) : Nat) : Int) := Int.toNat_of_nonneg hmod_nonneg
    have hu_lt : u < 2 ^ (b' + 1) := by omega
    -- Split `bitsToInt (b' + 1) true` into lower `b'` bits + MSB `b'`
    unfold bitsToInt twosCompBits finSumInt
    rw [finSumAuxInt]
    have hlow : finSumAuxInt
        (fun j : Fin (b' + 1) => bitWeight (b' + 1) true j * boolToInt (u.testBit j.val))
        b' (Nat.le_succ b') = ((u % 2 ^ b' : Nat) : Int) := by
      have hcongr : finSumAuxInt
          (fun j : Fin (b' + 1) => bitWeight (b' + 1) true j * boolToInt (u.testBit j.val))
          b' (Nat.le_succ b') =
          finSumAuxInt
          (fun j : Fin (b' + 1) => ((2 ^ j.val * (if u.testBit j.val then 1 else 0) : Nat) : Int))
          b' (Nat.le_succ b') := by
        have hstep : ∀ (k : Nat) (hk : k ≤ b'),
            finSumAuxInt
              (fun j : Fin (b' + 1) => bitWeight (b' + 1) true j * boolToInt (u.testBit j.val))
              k (Nat.le_trans hk (Nat.le_succ b')) =
            finSumAuxInt
              (fun j : Fin (b' + 1) => ((2 ^ j.val * (if u.testBit j.val then 1 else 0) : Nat) : Int))
              k (Nat.le_trans hk (Nat.le_succ b')) := by
          intro k
          induction k with
          | zero => intro _; rfl
          | succ k ih =>
            intro hk
            rw [finSumAuxInt, finSumAuxInt, ih (Nat.le_of_succ_le hk)]
            have hne : (k + 1 == b' + 1) = false := by
              rw [beq_eq_false_iff_ne]; omega
            unfold bitWeight boolToInt
            simp only [Bool.true_and, hne]
            cases u.testBit k <;> simp
        exact hstep b' (Nat.le_refl b')
      rw [hcongr, finSumAuxInt_ofNat, finSumAuxNat_testBit_mod u b' (Nat.le_succ b')]
    rw [hlow]
    -- Evaluate MSB term at `j = b'`
    have hmsb_w : bitWeight (b' + 1) true ⟨b', Nat.lt_succ_self b'⟩ = -((2 ^ b' : Nat) : Int) := by
      unfold bitWeight
      simp
    rw [hmsb_w]
    -- Compare `x ≥ 0` vs `x < 0`
    by_cases hx : 0 ≤ x
    · have hmod_eq : x % ((2 ^ (b' + 1) : Nat) : Int) = x :=
        Int.emod_eq_of_lt hx (by omega)
      have hu_eq : (u : Int) = x := by omega
      have hu_lt_half : u < 2 ^ b' := by omega
      have hbit_false : u.testBit b' = false := Nat.testBit_lt_two_pow hu_lt_half
      have humod : u % 2 ^ b' = u := Nat.mod_eq_of_lt hu_lt_half
      rw [hbit_false, humod]
      unfold boolToInt
      simp only [Bool.false_eq_true, ↓reduceIte, Int.mul_zero, Int.add_zero]
      exact hu_eq
    · have hx_lt : x < 0 := by omega
      have hx_add_nonneg : 0 ≤ x + ((2 ^ (b' + 1) : Nat) : Int) := by omega
      have hx_add_lt : x + ((2 ^ (b' + 1) : Nat) : Int) < ((2 ^ (b' + 1) : Nat) : Int) := by omega
      have hmod_eq : x % ((2 ^ (b' + 1) : Nat) : Int) = x + ((2 ^ (b' + 1) : Nat) : Int) := by
        have hstep : (x + ((2 ^ (b' + 1) : Nat) : Int)) % ((2 ^ (b' + 1) : Nat) : Int) =
            x % ((2 ^ (b' + 1) : Nat) : Int) := by
          rw [Int.add_emod, Int.emod_self, Int.add_zero, Int.emod_emod]
        rw [← hstep]
        exact Int.emod_eq_of_lt hx_add_nonneg hx_add_lt
      have hu_eq : (u : Int) = x + ((2 ^ (b' + 1) : Nat) : Int) := by omega
      have hu_ge_half : 2 ^ b' ≤ u := by omega
      have hdiv : u / 2 ^ b' = 1 :=
        Nat.div_eq_of_lt_le (by omega) (by omega)
      have hbit_true : u.testBit b' = true := by
        rw [Nat.testBit_eq_decide_div_mod_eq, hdiv]
        rfl
      have humod : u % 2 ^ b' = u - 2 ^ b' := by
        have hdiv_mod := Nat.div_add_mod u (2 ^ b')
        rw [hdiv] at hdiv_mod
        omega
      rw [hbit_true, humod]
      unfold boolToInt
      simp only [↓reduceIte, Int.mul_one]
      omega

/-- Headline Theorem 4 (`popcnt_zero_lut_exact_bitserial_dot_identity`):
    Universal bit-exact bit-serial `POPCNT` dot-product identity for binary `{-1, +1}`
    and ternary `{-1, 0, +1}` weights against arbitrary `b`-bit signed/unsigned activations,
    plus universal `b`-bit two's-complement roundtrip and exact `int8` specialization. -/
theorem popcnt_zero_lut_exact_bitserial_dot_identity :
    (∀ (K b : Nat) (signed : Bool) (wPlane : Fin K → Bool) (aPlanes : Fin b → Fin K → Bool),
      dotInt (fun i => binWeight (wPlane i))
        (fun i => bitsToInt b signed (fun j => aPlanes j i)) =
        popcntBinaryDot signed wPlane aPlanes) ∧
    (∀ (K b : Nat) (signed : Bool) (wPos wNeg : Fin K → Bool) (aPlanes : Fin b → Fin K → Bool),
      dotInt (fun i => ternWeight (wPos i) (wNeg i))
        (fun i => bitsToInt b signed (fun j => aPlanes j i)) =
        popcntTernaryDot signed wPos wNeg aPlanes) ∧
    (∀ (b : Nat) (_hb : 1 ≤ b) (x : Int),
      -((2 ^ (b - 1) : Nat) : Int) ≤ x → x < ((2 ^ (b - 1) : Nat) : Int) →
      bitsToInt b true (twosCompBits b x) = x) ∧
    (∀ (K : Nat) (wPlane : Fin K → Bool) (a : Fin K → Int),
      (∀ i, -128 ≤ a i ∧ a i ≤ 127) →
      dotInt (fun i => binWeight (wPlane i)) a =
        popcntBinaryDot true wPlane (fun j i => twosCompBits 8 (a i) j)) ∧
    (∀ (K : Nat) (wPos wNeg : Fin K → Bool) (a : Fin K → Int),
      (∀ i, -128 ≤ a i ∧ a i ≤ 127) →
      dotInt (fun i => ternWeight (wPos i) (wNeg i)) a =
        popcntTernaryDot true wPos wNeg (fun j i => twosCompBits 8 (a i) j)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro K b signed wPlane aPlanes
    exact popcnt_binary_dot_exact signed wPlane aPlanes
  · intro K b signed wPos wNeg aPlanes
    exact popcnt_ternary_dot_exact signed wPos wNeg aPlanes
  · intro b hb x hlo hhi
    exact signed_bitsToInt_twosComp hb x hlo hhi
  · intro K wPlane a ha
    have hrec : ∀ i, bitsToInt 8 true (fun j => twosCompBits 8 (a i) j) = a i := by
      intro i
      exact signed_bitsToInt_twosComp (b := 8) (by decide) (a i) (ha i).1 (by have := (ha i).2; omega)
    rw [← popcnt_binary_dot_exact true wPlane (fun j i => twosCompBits 8 (a i) j)]
    unfold dotInt
    apply finSumInt_congr
    intro i
    dsimp only
    rw [hrec i]
  · intro K wPos wNeg a ha
    have hrec : ∀ i, bitsToInt 8 true (fun j => twosCompBits 8 (a i) j) = a i := by
      intro i
      exact signed_bitsToInt_twosComp (b := 8) (by decide) (a i) (ha i).1 (by have := (ha i).2; omega)
    rw [← popcnt_ternary_dot_exact true wPos wNeg (fun j i => twosCompBits 8 (a i) j)]
    unfold dotInt
    apply finSumInt_congr
    intro i
    dsimp only
    rw [hrec i]

/-! ## Headline Theorem 5: LUT vs `POPCNT` Amortization Crossover & RDNA 3 Dominance -/

/-- Exact symbolic crossover for `amortizedCost`: when LUT has higher setup cost
    (`setupPop < setupLut`) and lower steady-state cost (`steadyLut < steadyPop`),
    `POPCNT` strictly beats LUT iff reuse factor `R < (setupLut - setupPop) / (steadyPop - steadyLut)`. -/
theorem amortized_crossover_iff (setupPop setupLut steadyPop steadyLut R : Rat)
    (hR : (0 : Rat) < R) (hSteady : steadyLut < steadyPop) :
    amortizedCost setupPop steadyPop R < amortizedCost setupLut steadyLut R ↔
      R < (setupLut - setupPop) / (steadyPop - steadyLut) := by
  have hd : (0 : Rat) < steadyPop - steadyLut := rat_sub_pos hSteady
  have hR_ne : R ≠ 0 := Rat.ne_of_gt hR
  have hd_ne : steadyPop - steadyLut ≠ 0 := Rat.ne_of_gt hd
  unfold amortizedCost
  constructor
  · intro hlt
    have hmul := rat_mul_lt_mul_of_pos_right hlt hR
    have h1 : (setupPop / R + steadyPop) * R = setupPop + steadyPop * R := by
      have : setupPop / R * R = setupPop := by
        rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel R hR_ne, Rat.mul_one]
      grind
    have h2 : (setupLut / R + steadyLut) * R = setupLut + steadyLut * R := by
      have : setupLut / R * R = setupLut := by
        rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel R hR_ne, Rat.mul_one]
      grind
    rw [h1, h2] at hmul
    have h3 : (steadyPop - steadyLut) * R < setupLut - setupPop := by
      apply rat_lt_of_sub_pos
      have hpos := rat_sub_pos hmul
      have heq : (setupLut - setupPop) - (steadyPop - steadyLut) * R =
          (setupLut + steadyLut * R) - (setupPop + steadyPop * R) := by grind
      rw [heq]; exact hpos
    have hinv := rat_inv_pos hd
    have h4 := rat_mul_lt_mul_of_pos_right h3 hinv
    have hl : (steadyPop - steadyLut) * R * (steadyPop - steadyLut)⁻¹ = R := by
      have : (steadyPop - steadyLut) * (steadyPop - steadyLut)⁻¹ = 1 :=
        Rat.mul_inv_cancel _ hd_ne
      grind
    rw [hl, ← Rat.div_def] at h4
    exact h4
  · intro hlt
    have h1 := rat_mul_lt_mul_of_pos_right hlt hd
    have hr : (setupLut - setupPop) / (steadyPop - steadyLut) * (steadyPop - steadyLut) =
        setupLut - setupPop := by
      rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ hd_ne, Rat.mul_one]
    rw [hr] at h1
    have h2 : setupPop + steadyPop * R < setupLut + steadyLut * R := by
      apply rat_lt_of_sub_pos
      have hpos := rat_sub_pos h1
      have heq : (setupLut + steadyLut * R) - (setupPop + steadyPop * R) =
          (setupLut - setupPop) - R * (steadyPop - steadyLut) := by grind
      rw [heq]; exact hpos
    have hinv := rat_inv_pos hR
    have h3 := rat_mul_lt_mul_of_pos_right h2 hinv
    have hl : (setupPop + steadyPop * R) * R⁻¹ = setupPop / R + steadyPop := by
      have : R * R⁻¹ = 1 := Rat.mul_inv_cancel R hR_ne
      rw [Rat.div_def]; grind
    have hr' : (setupLut + steadyLut * R) * R⁻¹ = setupLut / R + steadyLut := by
      have : R * R⁻¹ = 1 := Rat.mul_inv_cancel R hR_ne
      rw [Rat.div_def]; grind
    rw [hl, hr'] at h3
    exact h3

theorem amortized_crossover_eq (setupPop setupLut steadyPop steadyLut : Rat)
    (hSetup : setupPop < setupLut) (hSteady : steadyLut < steadyPop) :
    let RStar := (setupLut - setupPop) / (steadyPop - steadyLut)
    (0 : Rat) < RStar ∧
    amortizedCost setupPop steadyPop RStar = amortizedCost setupLut steadyLut RStar := by
  have hs : (0 : Rat) < setupLut - setupPop := rat_sub_pos hSetup
  have hd : (0 : Rat) < steadyPop - steadyLut := rat_sub_pos hSteady
  have hRStar_pos : (0 : Rat) < (setupLut - setupPop) / (steadyPop - steadyLut) :=
    rat_div_pos hs hd
  have hRStar_ne : (setupLut - setupPop) / (steadyPop - steadyLut) ≠ 0 :=
    Rat.ne_of_gt hRStar_pos
  have hd_ne : steadyPop - steadyLut ≠ 0 := Rat.ne_of_gt hd
  refine ⟨hRStar_pos, ?_⟩
  unfold amortizedCost
  let RStar := (setupLut - setupPop) / (steadyPop - steadyLut)
  have hprod : RStar * (steadyPop - steadyLut) = setupLut - setupPop := by
    dsimp only [RStar]
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ hd_ne, Rat.mul_one]
  have hcancel : (setupLut - setupPop) / RStar = steadyPop - steadyLut := by
    rw [← hprod, Rat.div_def, Rat.mul_comm RStar (steadyPop - steadyLut), Rat.mul_assoc,
        Rat.mul_inv_cancel RStar hRStar_ne, Rat.mul_one]
  have hsub : setupLut / RStar - setupPop / RStar = (setupLut - setupPop) / RStar := by
    rw [Rat.div_def, Rat.div_def, Rat.div_def]; grind
  change setupPop / RStar + steadyPop = setupLut / RStar + steadyLut
  grind

/-- Exact RDNA 3 No-Crossover Dominance Theorem: when `cTr ≤ cBuild / g` and
    `b * cPop / W < cLut / g`, zero-LUT `POPCNT` strictly beats LUT for ALL `M, N, K, P > 0`. -/
theorem popcnt_dominates_lut_no_crossover (M N K P g W b cBuild cLut cTr cPop : Rat)
    (hM : (0 : Rat) < M) (hN : (0 : Rat) < N) (hK : (0 : Rat) < K) (hP : (0 : Rat) < P)
    (hSetup : cTr ≤ cBuild / g) (hSteady : (b * cPop) / W < cLut / g) :
    popcntGemmCost M N K P W b cTr cPop < lutGemmCost M N K P g cBuild cLut := by
  unfold popcntGemmCost lutGemmCost
  have hMK : (0 : Rat) < M * K := rat_mul_pos hM hK
  have hMNKP : (0 : Rat) < M * N * P * K := rat_mul_pos (rat_mul_pos (rat_mul_pos hM hN) hP) hK
  have h1 : M * K * cTr ≤ M * (K / g) * cBuild := by
    have hle := rat_mul_le_mul_of_nonneg_left hSetup (Rat.le_of_lt hMK)
    have heq : M * K * (cBuild / g) = M * (K / g) * cBuild := by
      rw [Rat.div_def, Rat.div_def]; grind
    rw [heq] at hle
    exact hle
  have h2 : M * N * P * (K / W) * (b * cPop) < M * N * P * (K / g) * cLut := by
    have hlt := rat_mul_lt_mul_of_pos_left hSteady hMNKP
    have heq1 : M * N * P * K * ((b * cPop) / W) = M * N * P * (K / W) * (b * cPop) := by
      rw [Rat.div_def, Rat.div_def]; grind
    have heq2 : M * N * P * K * (cLut / g) = M * N * P * (K / g) * cLut := by
      rw [Rat.div_def, Rat.div_def]; grind
    rw [heq1, heq2] at hlt
    exact hlt
  exact rat_add_lt_add_of_le_of_lt h1 h2

/-- Headline Theorem 5 (`lut_vs_popcnt_amortization_crossover_exact`):
    Exact symbolic amortization crossover `R* = (setupLut - setupPop) / (steadyPop - steadyLut)`
    explaining why zero-LUT `POPCNT` wins on small-batch LLM decode (`R < R*`), plus the
    exact RDNA 3 (`gfx1100`) no-crossover dominance theorem (`POPCNT` wins for all `M, N, K > 0`)
    and exact `gfx1100` cost ratios (`1/2 < 3/4` steady-state, `3/2×` `g=6` vs `g=4` lookups). -/
theorem lut_vs_popcnt_amortization_crossover_exact :
    (∀ (setupPop setupLut steadyPop steadyLut R : Rat),
      (0 : Rat) < R → steadyLut < steadyPop →
      (amortizedCost setupPop steadyPop R < amortizedCost setupLut steadyLut R ↔
        R < (setupLut - setupPop) / (steadyPop - steadyLut))) ∧
    (∀ (setupPop setupLut steadyPop steadyLut : Rat),
      setupPop < setupLut → steadyLut < steadyPop →
      let RStar := (setupLut - setupPop) / (steadyPop - steadyLut)
      (0 : Rat) < RStar ∧
      amortizedCost setupPop steadyPop RStar = amortizedCost setupLut steadyLut RStar) ∧
    (∀ (M N K P g W b cBuild cLut cTr cPop : Rat),
      (0 : Rat) < M → (0 : Rat) < N → (0 : Rat) < K → (0 : Rat) < P →
      cTr ≤ cBuild / g → (b * cPop) / W < cLut / g →
      popcntGemmCost M N K P W b cTr cPop < lutGemmCost M N K P g cBuild cLut) ∧
    (((8 * 2 : Rat) / 32 = 1 / 2) ∧
     ((3 : Rat) / 4 > (8 * 2 : Rat) / 32) ∧
     (((3 : Rat) / 4) / ((8 * 2 : Rat) / 32) = 3 / 2) ∧
     (((1 : Rat) / 4) / ((1 : Rat) / 6) = 3 / 2)) := by
  refine ⟨amortized_crossover_iff, amortized_crossover_eq,
    popcnt_dominates_lut_no_crossover, ?_⟩
  refine ⟨by grind, ?_, by grind, by grind⟩
  apply rat_lt_of_sub_pos
  have hdiff : (3 : Rat) / 4 - (8 * 2 : Rat) / 32 = 1 / 4 := by grind
  rw [hdiff]
  exact rat_div_pos (by decide) (by decide)

/-! ## Headline Theorem 6: Exact `int16` Overflow Thresholds & Two's-Complement Wrap-by-1 Trap -/

theorem mul_abs_bound {w a wMax aMax : Int}
    (hw : -wMax ≤ w ∧ w ≤ wMax) (ha : -aMax ≤ a ∧ a ≤ aMax)
    (_hwMax : 0 ≤ wMax) (_haMax : 0 ≤ aMax) :
    -(wMax * aMax) ≤ w * a ∧ w * a ≤ wMax * aMax := by
  have h1 : 0 ≤ (wMax - w) * (aMax - a) := Int.mul_nonneg (by omega) (by omega)
  have h2 : 0 ≤ (wMax + w) * (aMax + a) := Int.mul_nonneg (by omega) (by omega)
  have h3 : 0 ≤ (wMax - w) * (aMax + a) := Int.mul_nonneg (by omega) (by omega)
  have h4 : 0 ≤ (wMax + w) * (aMax - a) := Int.mul_nonneg (by omega) (by omega)
  have e1 : (wMax - w) * (aMax - a) + (wMax + w) * (aMax + a) = 2 * (wMax * aMax + w * a) := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.add_mul, Int.mul_add, Int.mul_add]; omega
  have e2 : (wMax - w) * (aMax + a) + (wMax + w) * (aMax - a) = 2 * (wMax * aMax - w * a) := by
    rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.add_mul, Int.mul_sub, Int.mul_sub]; omega
  omega

theorem dotInt_fitsInt16_of_bound {K : Nat} (w a : Fin K → Int) (wMax aMax : Int)
    (hwMax : 0 ≤ wMax) (haMax : 0 ≤ aMax)
    (hw : ∀ i, -wMax ≤ w i ∧ w i ≤ wMax)
    (ha : ∀ i, -aMax ≤ a i ∧ a i ≤ aMax)
    (hK : (K : Int) * (wMax * aMax) ≤ 32767) :
    fitsInt16 (dotInt w a) := by
  have hb := finSumInt_bound (fun i => w i * a i) (wMax * aMax)
    (fun i => mul_abs_bound (hw i) (ha i) hwMax haMax)
  have hneg : -(K : Int) * (wMax * aMax) = -((K : Int) * (wMax * aMax)) :=
    Int.neg_mul (K : Int) (wMax * aMax)
  unfold fitsInt16 int16Min int16Max dotInt
  omega

theorem dotInt_const (K : Nat) (cw ca : Int) :
    dotInt (fun _ : Fin K => cw) (fun _ : Fin K => ca) = (K : Int) * (cw * ca) := by
  unfold dotInt finSumInt
  have haux : ∀ (k : Nat) (hk : k ≤ K),
      finSumAuxInt (fun _ : Fin K => cw * ca) k hk = (k : Int) * (cw * ca) := by
    intro k
    induction k with
    | zero => intro _; simp [finSumAuxInt]
    | succ k ih =>
      intro hk
      rw [finSumAuxInt, ih (Nat.le_of_succ_le hk)]
      have hcast : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
      rw [hcast, Int.add_mul, Int.one_mul]
  exact haux K (Nat.le_refl K)

/-- Headline Theorem 6 (`tmac_int16_overflow_threshold_exact`):
    Proves universal `int16` accumulation safety, the exact symmetric `int8` ceiling
    `K_max = 258` (making `K_tile = 256` zero-overflow), and the exact full `int8`
    two's-complement wrap-by-1 trap (`+32768 ↦ -32768`) at `K = 256` (`wMax = 1`),
    `K = 128` (direct INT2 `wMax = 2`), and `K = 64` (direct INT3 `wMax = 4`). -/
theorem tmac_int16_overflow_threshold_exact :
    (∀ (K : Nat) (w a : Fin K → Int) (wMax aMax : Int),
      0 ≤ wMax → 0 ≤ aMax →
      (∀ i, -wMax ≤ w i ∧ w i ≤ wMax) →
      (∀ i, -aMax ≤ a i ∧ a i ≤ aMax) →
      (K : Int) * (wMax * aMax) ≤ 32767 →
      fitsInt16 (dotInt w a)) ∧
    (∀ (K : Nat) (w a : Fin K → Int),
      K ≤ 258 → (∀ i, -1 ≤ w i ∧ w i ≤ 1) → (∀ i, -127 ≤ a i ∧ a i ≤ 127) →
      fitsInt16 (dotInt w a)) ∧
    (∀ (K : Nat) (w a : Fin K → Int),
      K ≤ 255 → (∀ i, -1 ≤ w i ∧ w i ≤ 1) → (∀ i, -128 ≤ a i ∧ a i ≤ 128) →
      fitsInt16 (dotInt w a)) ∧
    (dotInt (fun _ : Fin 256 => (-1 : Int)) (fun _ : Fin 256 => (-128 : Int)) = int16Max + 1 ∧
     ¬fitsInt16 (dotInt (fun _ : Fin 256 => (-1 : Int)) (fun _ : Fin 256 => (-128 : Int))) ∧
     wrapInt16 (dotInt (fun _ : Fin 256 => (-1 : Int)) (fun _ : Fin 256 => (-128 : Int))) = int16Min) ∧
    (dotInt (fun _ : Fin 128 => (-2 : Int)) (fun _ : Fin 128 => (-128 : Int)) = int16Max + 1 ∧
     wrapInt16 (dotInt (fun _ : Fin 128 => (-2 : Int)) (fun _ : Fin 128 => (-128 : Int))) = int16Min) ∧
    (dotInt (fun _ : Fin 64 => (-4 : Int)) (fun _ : Fin 64 => (-128 : Int)) = int16Max + 1 ∧
     wrapInt16 (dotInt (fun _ : Fin 64 => (-4 : Int)) (fun _ : Fin 64 => (-128 : Int))) = int16Min) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro K w a wMax aMax hwMax haMax hw ha hK
    exact dotInt_fitsInt16_of_bound w a wMax aMax hwMax haMax hw ha hK
  · intro K w a hK hw ha
    exact dotInt_fitsInt16_of_bound w a 1 127 (by decide) (by decide) hw ha (by omega)
  · intro K w a hK hw ha
    exact dotInt_fitsInt16_of_bound w a 1 128 (by decide) (by decide) hw ha (by omega)
  · rw [dotInt_const]
    exact ⟨by decide, by unfold fitsInt16 int16Max; omega, by decide⟩
  · rw [dotInt_const]
    exact ⟨by decide, by decide⟩
  · rw [dotInt_const]
    exact ⟨by decide, by decide⟩

end BitSerialLutDag
