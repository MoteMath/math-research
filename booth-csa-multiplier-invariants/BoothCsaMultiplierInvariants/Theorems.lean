import BoothCsaMultiplierInvariants.Defs

set_option autoImplicit false

namespace SiliconBoothCSA
theorem p2_pred_double {W : Nat} (hW : 1 ≤ W) : 2 * p2 (W - 1) = p2 W := by
  have h := pow2_pred_double hW
  unfold p2; omega

theorem p2_add (a b : Nat) : p2 a * p2 b = p2 (a + b) := by
  unfold p2
  rw [← Int.natCast_mul, ← Nat.pow_add]

theorem p2_pos (n : Nat) : (0 : Int) < p2 n := by
  unfold p2; have := pow2_pos n; omega

theorem signedVal_mod (W u : Nat) : signedVal W (u % 2 ^ W) = signedVal W u := by
  simp [signedVal]

theorem signedVal_bounds {W : Nat} (hW : 1 ≤ W) (u : Nat) :
    -p2 (W - 1) ≤ signedVal W u ∧ signedVal W u < p2 (W - 1) := by
  have h2 := pow2_pred_double hW
  have hlt : u % 2 ^ W < 2 ^ W := Nat.mod_lt u (pow2_pos W)
  unfold signedVal p2
  split <;> omega

theorem signedVal_emod {W : Nat} (u : Nat) :
    (signedVal W u) % p2 W = ((u % 2 ^ W : Nat) : Int) := by
  have hlt : u % 2 ^ W < 2 ^ W := Nat.mod_lt u (pow2_pos W)
  unfold signedVal p2
  split
  · exact Int.emod_eq_of_lt (by omega) (by omega)
  · rw [Int.sub_emod_right]
    exact Int.emod_eq_of_lt (by omega) (by omega)

theorem signedVal_eq_of_range {W : Nat} (hW : 1 ≤ W) {u : Nat} {V : Int}
    (hlo : -p2 (W - 1) ≤ V) (hhi : V < p2 (W - 1))
    (hmod : ((u % 2 ^ W : Nat) : Int) = V % p2 W) :
    signedVal W u = V := by
  have h2 := p2_pred_double hW
  have hb := signedVal_bounds hW u
  have hm := signedVal_emod (W := W) u
  have hdiff : (signedVal W u - V) % p2 W = 0 := by
    rw [Int.sub_emod, hm, hmod, Int.sub_self, Int.zero_emod]
  have hdvd : p2 W ∣ (signedVal W u - V) := Int.dvd_of_emod_eq_zero hdiff
  rcases hdvd with ⟨q, hq⟩
  have hpos := p2_pos W
  have hq0 : q = 0 := by
    rcases Int.lt_trichotomy q 0 with hlt | heq | hgt
    · have hle : q ≤ -1 := by omega
      have hmul : p2 W * q ≤ p2 W * (-1) := Int.mul_le_mul_of_nonneg_left hle (by omega)
      omega
    · exact heq
    · have hge : 1 ≤ q := by omega
      have hmul : p2 W * 1 ≤ p2 W * q := Int.mul_le_mul_of_nonneg_left hge (by omega)
      omega
  rw [hq0, Int.mul_zero] at hq
  omega

private theorem int_mul_ediv_add_emod (a b : Int) : b * (a / b) + a % b = a := by
  rw [Int.add_comm]; exact Int.emod_add_mul_ediv a b

/-- Exact split of `signedVal W u` into its top `g` bits and bottom `W - g` bits. -/
theorem signedVal_split_hi_lo {g W : Nat} (hg : 1 ≤ g) (hWg : g ≤ W) (u : Nat) :
    signedVal W u =
      signedVal g ((u % 2 ^ W) / 2 ^ (W - g)) * p2 (W - g) +
      ((u % 2 ^ (W - g) : Nat) : Int) := by
  have hW : 1 ≤ W := Nat.le_trans hg hWg
  have hpow : 2 ^ g * 2 ^ (W - g) = 2 ^ W := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hWg]
  have hpow_half : 2 ^ (g - 1) * 2 ^ (W - g) = 2 ^ (W - 1) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hlo_eq : (u % 2 ^ W) % 2 ^ (W - g) = u % 2 ^ (W - g) := by
    have hdvd : 2 ^ (W - g) ∣ 2 ^ W := ⟨2 ^ g, by rw [Nat.mul_comm]; exact hpow.symm⟩
    exact Nat.mod_mod_of_dvd u hdvd
  have hdiv_lt : (u % 2 ^ W) / 2 ^ (W - g) < 2 ^ g := by
    rw [Nat.div_lt_iff_lt_mul (pow2_pos (W - g)), hpow]
    exact Nat.mod_lt u (pow2_pos W)
  have hdecomp : u % 2 ^ W = ((u % 2 ^ W) / 2 ^ (W - g)) * 2 ^ (W - g) + u % 2 ^ (W - g) := by
    rw [← hlo_eq, Nat.mul_comm]
    exact (Nat.div_add_mod (u % 2 ^ W) (2 ^ (W - g))).symm
  have hrem_lt : u % 2 ^ (W - g) < 2 ^ (W - g) := Nat.mod_lt u (pow2_pos (W - g))
  have hcmp : (u % 2 ^ W < 2 ^ (W - 1)) ↔ ((u % 2 ^ W) / 2 ^ (W - g) < 2 ^ (g - 1)) := by
    rw [← hpow_half]
    constructor
    · intro h
      rw [hdecomp] at h
      cases Nat.lt_or_ge ((u % 2 ^ W) / 2 ^ (W - g)) (2 ^ (g - 1)) with
      | inl hlt => exact hlt
      | inr hge =>
        have : 2 ^ (g - 1) * 2 ^ (W - g) ≤ ((u % 2 ^ W) / 2 ^ (W - g)) * 2 ^ (W - g) :=
          Nat.mul_le_mul_right _ hge
        omega
    · intro h
      rw [hdecomp]
      have : ((u % 2 ^ W) / 2 ^ (W - g) + 1) * 2 ^ (W - g) ≤ 2 ^ (g - 1) * 2 ^ (W - g) :=
        Nat.mul_le_mul_right _ h
      rw [Nat.add_mul, Nat.one_mul] at this
      omega
  unfold signedVal
  rw [Nat.mod_eq_of_lt hdiv_lt]
  have hd : ((u % 2 ^ W : Nat) : Int) =
      (((u % 2 ^ W) / 2 ^ (W - g) : Nat) : Int) * p2 (W - g) +
      ((u % 2 ^ (W - g) : Nat) : Int) := by
    unfold p2
    rw [← Int.natCast_mul, ← Int.natCast_add]
    exact congrArg Int.ofNat hdecomp
  have hp : p2 g * p2 (W - g) = p2 W := by
    unfold p2; rw [← Int.natCast_mul]; exact congrArg Int.ofNat hpow
  by_cases hlt : u % 2 ^ W < 2 ^ (W - 1)
  · have hlt' : (u % 2 ^ W) / 2 ^ (W - g) < 2 ^ (g - 1) := hcmp.mp hlt
    simp only [hlt, hlt', ↓reduceIte]
    exact hd
  · have hlt' : ¬ ((u % 2 ^ W) / 2 ^ (W - g) < 2 ^ (g - 1)) := fun h => hlt (hcmp.mpr h)
    simp only [hlt, hlt', ↓reduceIte]
    grind

/-! ### Exact Pure-Silicon Bitwise Arithmetic (`^^^`, `&&&`, `|||`, `<<<`) and 3:2 CSA -/

private theorem mod_two_eq_of_testBit0 (x : Nat) :
    x % 2 = if x.testBit 0 then 1 else 0 := by
  have h := Nat.testBit_zero x
  rw [h]
  by_cases hx : x % 2 = 1 <;> simp [hx] <;> omega

private theorem xor_div_two (a b : Nat) : (a ^^^ b) / 2 = (a / 2) ^^^ (b / 2) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp [Nat.testBit_div_two, Nat.testBit_xor]

private theorem and_div_two (a b : Nat) : (a &&& b) / 2 = (a / 2) &&& (b / 2) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp [Nat.testBit_div_two, Nat.testBit_and]

private theorem or_div_two (a b : Nat) : (a ||| b) / 2 = (a / 2) ||| (b / 2) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp [Nat.testBit_div_two, Nat.testBit_or]

private theorem add_eq_xor_add_two_mul_and (b c : Nat) :
    b + c = (b ^^^ c) + 2 * (b &&& c) := by
  induction b using Nat.strongRecOn generalizing c with
  | ind b ih =>
    by_cases hb : b = 0
    · subst hb; simp
    · have hlt : b / 2 < b := Nat.div_lt_self (Nat.pos_of_ne_zero hb) (by decide)
      have ih' := ih (b / 2) hlt (c / 2)
      have h1 := xor_div_two b c
      have h2 := and_div_two b c
      have hm1 := mod_two_eq_of_testBit0 (b ^^^ c)
      have hm2 := mod_two_eq_of_testBit0 (b &&& c)
      have hmb := mod_two_eq_of_testBit0 b
      have hmc := mod_two_eq_of_testBit0 c
      rw [Nat.testBit_xor] at hm1
      rw [Nat.testBit_and] at hm2
      have hdb := Nat.div_add_mod b 2
      have hdc := Nat.div_add_mod c 2
      have hdx := Nat.div_add_mod (b ^^^ c) 2
      have hdn := Nat.div_add_mod (b &&& c) 2
      have hL : b + c = 2 * (b / 2 + c / 2) + (b % 2 + c % 2) := by omega
      have hR : (b ^^^ c) + 2 * (b &&& c) =
          2 * ((b / 2 ^^^ c / 2) + 2 * (b / 2 &&& c / 2)) + ((b ^^^ c) % 2 + 2 * ((b &&& c) % 2)) := by
        rw [← h1, ← h2]; omega
      have hbit : b % 2 + c % 2 = (b ^^^ c) % 2 + 2 * ((b &&& c) % 2) := by
        rw [hmb, hmc, hm1, hm2]; cases b.testBit 0 <;> cases c.testBit 0 <;> decide
      omega

private theorem full_adder_bitwise_exact (a b c : Nat) :
    a + b + c = (a ^^^ b ^^^ c) + 2 * (((a &&& b) ||| (b &&& c)) ||| (a &&& c)) := by
  induction a using Nat.strongRecOn generalizing b c with
  | ind a ih =>
    by_cases ha : a = 0
    · subst ha
      simp only [Nat.zero_add, Nat.zero_xor, Nat.zero_and, Nat.zero_or, Nat.or_zero]
      exact add_eq_xor_add_two_mul_and b c
    · have hlt : a / 2 < a := Nat.div_lt_self (Nat.pos_of_ne_zero ha) (by decide)
      have ih' := ih (a / 2) hlt (b / 2) (c / 2)
      have h1 : (a ^^^ b ^^^ c) / 2 = (a / 2) ^^^ (b / 2) ^^^ (c / 2) := by
        rw [xor_div_two, xor_div_two]
      have h2 : (((a &&& b) ||| (b &&& c)) ||| (a &&& c)) / 2 =
          (((a / 2 &&& b / 2) ||| (b / 2 &&& c / 2)) ||| (a / 2 &&& c / 2)) := by
        rw [or_div_two, or_div_two, and_div_two, and_div_two, and_div_two]
      have hm1 := mod_two_eq_of_testBit0 (a ^^^ b ^^^ c)
      have hm2 := mod_two_eq_of_testBit0 (((a &&& b) ||| (b &&& c)) ||| (a &&& c))
      have hma := mod_two_eq_of_testBit0 a
      have hmb := mod_two_eq_of_testBit0 b
      have hmc := mod_two_eq_of_testBit0 c
      rw [Nat.testBit_xor, Nat.testBit_xor] at hm1
      rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_and, Nat.testBit_and, Nat.testBit_and] at hm2
      have hda := Nat.div_add_mod a 2
      have hdb := Nat.div_add_mod b 2
      have hdc := Nat.div_add_mod c 2
      have hdx := Nat.div_add_mod (a ^^^ b ^^^ c) 2
      have hdn := Nat.div_add_mod (((a &&& b) ||| (b &&& c)) ||| (a &&& c)) 2
      have hL : a + b + c = 2 * (a / 2 + b / 2 + c / 2) + (a % 2 + b % 2 + c % 2) := by omega
      have hR : (a ^^^ b ^^^ c) + 2 * (((a &&& b) ||| (b &&& c)) ||| (a &&& c)) =
          2 * (((a / 2) ^^^ (b / 2) ^^^ (c / 2)) + 2 * (((a / 2 &&& b / 2) ||| (b / 2 &&& c / 2)) ||| (a / 2 &&& c / 2))) +
          ((a ^^^ b ^^^ c) % 2 + 2 * ((((a &&& b) ||| (b &&& c)) ||| (a &&& c)) % 2)) := by
        rw [← h1, ← h2]; omega
      have hbit : a % 2 + b % 2 + c % 2 =
          (a ^^^ b ^^^ c) % 2 + 2 * ((((a &&& b) ||| (b &&& c)) ||| (a &&& c)) % 2) := by
        rw [hma, hmb, hmc, hm1, hm2]
        cases a.testBit 0 <;> cases b.testBit 0 <;> cases c.testBit 0 <;> decide
      omega

theorem csa3to2_exact_mod (W a b c : Nat) :
    (csaSum W a b c + csaCarry W a b c) % 2 ^ W = (a + b + c) % 2 ^ W := by
  unfold csaSum csaCarry
  rw [Nat.add_mod, Nat.mod_mod, Nat.mod_mod, ← Nat.add_mod]
  have hsh : ((((a &&& b) ||| (b &&& c)) ||| (a &&& c)) <<< 1) =
      2 * (((a &&& b) ||| (b &&& c)) ||| (a &&& c)) := by
    rw [Nat.shiftLeft_eq]
    simp [Nat.mul_comm]
  rw [hsh, ← full_adder_bitwise_exact a b c]

theorem csaCarry_even {W : Nat} (hW : 1 ≤ W) (a b c : Nat) :
    csaCarry W a b c % 2 = 0 := by
  unfold csaCarry
  have hdvd : 2 ∣ 2 ^ W := ⟨2 ^ (W - 1), by rw [pow2_pred_double hW]⟩
  rw [Nat.mod_mod_of_dvd _ hdvd, Nat.shiftLeft_eq]
  simp

/-- Zero-gate bit-0 OR injection: when `C` is even and `h ≤ 1`, `C ||| h = C + h`. -/
theorem or_bit0_eq_add_of_even {C h : Nat} (hC : C % 2 = 0) (hh : h ≤ 1) :
    (C ||| h) = C + h := by
  have hcases : h = 0 ∨ h = 1 := by omega
  rcases hcases with rfl | rfl
  · simp
  · have hdiv : (C ||| 1) / 2 = C / 2 := by
      rw [or_div_two]
      simp
    have hmod : (C ||| 1) % 2 = 1 := by
      rw [mod_two_eq_of_testBit0, Nat.testBit_or]
      have h1 : (1 : Nat).testBit 0 = true := by decide
      simp [h1]
    have hd1 := Nat.div_add_mod (C ||| 1) 2
    have hd2 := Nat.div_add_mod C 2
    omega


/-! ============================================================================
    SECTION 2: REUSABLE MECHANISM I — Finite-State Affine-Potential Transducer
               (`RadixTransducer` & `FiniteRadixCert`)
    ============================================================================ -/

theorem radixSum_add (B : Nat) (f g : Nat → Int) (n : Nat) :
    radixSum B (fun i => f i + g i) n = radixSum B f n + radixSum B g n := by
  induction n with
  | zero => simp [radixSum]
  | succ k ih =>
    simp only [radixSum, ih]; grind

theorem radixSum_sub (B : Nat) (f g : Nat → Int) (n : Nat) :
    radixSum B (fun i => f i - g i) n = radixSum B f n - radixSum B g n := by
  induction n with
  | zero => simp [radixSum]
  | succ k ih =>
    simp only [radixSum, ih]; grind

theorem radixSum_mul_const (B : Nat) (c : Int) (f : Nat → Int) (n : Nat) :
    radixSum B (fun i => c * f i) n = c * radixSum B f n := by
  induction n with
  | zero => simp [radixSum]
  | succ k ih =>
    simp only [radixSum, ih]; grind

theorem RadixTransducer.run_inv {Q A : Type} {B : Nat}
    (T : RadixTransducer Q A B) {q0 : Q} (h0 : T.inv q0) (stream : Nat → A) (n : Nat) :
    T.inv (T.run q0 stream n) := by
  induction n with
  | zero => exact h0
  | succ k ih => exact T.h_inv _ _ ih

/--
  INFINITE LIFTING THEOREM (Mechanism I):
  Finite local affine-potential balance ⟹ exact base-`B` sum identity ∀ n : Nat.
-/
theorem RadixTransducer.lift_sum {Q A : Type} {B : Nat}
    (T : RadixTransducer Q A B) {q0 : Q} (h0 : T.inv q0) (stream : Nat → A) (n : Nat) :
    radixSum B (fun i => T.delta (T.run q0 stream i) (stream i)) n =
      T.phi (T.run q0 stream n) * ((B ^ n : Nat) : Int) - T.phi q0 := by
  induction n with
  | zero =>
    simp [radixSum, RadixTransducer.run]
  | succ k ih =>
    simp only [radixSum, RadixTransducer.run, ih]
    have hbal := T.h_bal (T.run q0 stream k) (stream k) (T.run_inv h0 stream k)
    rw [hbal]
    have hpow : ((B ^ (k + 1) : Nat) : Int) = (B : Int) * ((B ^ k : Nat) : Int) := by
      rw [← Int.natCast_mul, Nat.pow_succ, Nat.mul_comm]
    rw [hpow]
    grind

theorem FiniteRadixCert.lift_sum {nQ nA B : Nat} (C : FiniteRadixCert nQ nA B)
    (hcheck : C.check = true) {q0 : Fin nQ} (h0 : C.invB q0 = true)
    (stream : Nat → Fin nA) (n : Nat) :
    let T := C.sound hcheck
    radixSum B (fun i => C.delta (T.run q0 stream i) (stream i)) n =
      C.phi (T.run q0 stream n) * ((B ^ n : Nat) : Int) - C.phi q0 :=
  (C.sound hcheck).lift_sum h0 stream n


/-! ============================================================================
    SECTION 3: REUSABLE MECHANISM II — Finite-Guard Carry-Save Normalizer Engine
               (`GuardNormalizerSpec`, `FiniteGuardCert`) & Universal Cut-Arc Barrier
    ============================================================================ -/

/--
  INFINITE-WIDTH LIFTING THEOREM (Mechanism II):
  Any finite top-`g`-bit guard specification lifts to EXACT unwrapped integer conservation
  `signedVal W S' + signedVal W C' = V` for ALL bit-widths `W ≥ g` and ALL pairs `(S, C)`
  whose modular sum lies in the allowed slabs!
-/
theorem GuardNormalizerSpec.lift_all_widths {g : Nat} (G : GuardNormalizerSpec g)
    {W : Nat} (hWg : g ≤ W) (S C : Nat) {V : Int}
    (hV_lo : -p2 (W - 1) ≤ V) (hV_hi : V < p2 (W - 1))
    (hsum : (((S + C) % 2 ^ W : Nat) : Int) = V % p2 W)
    (hallow : G.allowed (((S + C) % 2 ^ W) / 2 ^ (W - g))) :
    let (S', C') := applyTopGuard g W G.norm S C
    signedVal W S' + signedVal W C' = V := by
  have hW : 1 ≤ W := Nat.le_trans G.hg hWg
  have hpow : 2 ^ g * 2 ^ (W - g) = 2 ^ W := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hWg]
  have hpow_pos : 0 < 2 ^ (W - g) := pow2_pos (W - g)
  let shift := W - g
  let s_hi := (S % 2 ^ W) / 2 ^ shift
  let c_hi := (C % 2 ^ W) / 2 ^ shift
  let s_lo := S % 2 ^ shift
  let c_lo := C % 2 ^ shift
  let k := (s_lo + c_lo) / 2 ^ shift
  let r_lo := (s_lo + c_lo) % 2 ^ shift
  have hs_hi_lt : s_hi < 2 ^ g := by
    rw [Nat.div_lt_iff_lt_mul hpow_pos, hpow]
    exact Nat.mod_lt S (pow2_pos W)
  have hc_hi_lt : c_hi < 2 ^ g := by
    rw [Nat.div_lt_iff_lt_mul hpow_pos, hpow]
    exact Nat.mod_lt C (pow2_pos W)
  have hs_lo_lt : s_lo < 2 ^ shift := Nat.mod_lt S hpow_pos
  have hc_lo_lt : c_lo < 2 ^ shift := Nat.mod_lt C hpow_pos
  have hk_le : k ≤ 1 := by
    have : s_lo + c_lo < 2 * 2 ^ shift := by omega
    have : (s_lo + c_lo) / 2 ^ shift < 2 := by
      rw [Nat.div_lt_iff_lt_mul hpow_pos]; exact this
    omega
  have hdvd : 2 ^ shift ∣ 2 ^ W := ⟨2 ^ g, by rw [Nat.mul_comm]; exact hpow.symm⟩
  have hS_decomp : S % 2 ^ W = s_hi * 2 ^ shift + s_lo := by
    have h1 : (S % 2 ^ W) % 2 ^ shift = s_lo := Nat.mod_mod_of_dvd S hdvd
    rw [← h1, Nat.mul_comm]
    exact (Nat.div_add_mod (S % 2 ^ W) (2 ^ shift)).symm
  have hC_decomp : C % 2 ^ W = c_hi * 2 ^ shift + c_lo := by
    have h1 : (C % 2 ^ W) % 2 ^ shift = c_lo := Nat.mod_mod_of_dvd C hdvd
    rw [← h1, Nat.mul_comm]
    exact (Nat.div_add_mod (C % 2 ^ W) (2 ^ shift)).symm
  have hlo_decomp : s_lo + c_lo = k * 2 ^ shift + r_lo := by
    rw [Nat.mul_comm]
    exact (Nat.div_add_mod (s_lo + c_lo) (2 ^ shift)).symm
  have hSC_eq : (S + C) % 2 ^ W = ((s_hi + c_hi + k) % 2 ^ g) * 2 ^ shift + r_lo := by
    have h1 : (S + C) % 2 ^ W = (S % 2 ^ W + C % 2 ^ W) % 2 ^ W := Nat.add_mod S C (2 ^ W)
    rw [h1, hS_decomp, hC_decomp]
    have h2 : s_hi * 2 ^ shift + s_lo + (c_hi * 2 ^ shift + c_lo) =
        (s_hi + c_hi + k) * 2 ^ shift + r_lo := by
      have : s_hi * 2 ^ shift + c_hi * 2 ^ shift + (s_lo + c_lo) =
          (s_hi + c_hi + k) * 2 ^ shift + r_lo := by
        rw [hlo_decomp]; grind
      omega
    rw [h2]
    have hdiv_g : (s_hi + c_hi + k) = ((s_hi + c_hi + k) / 2 ^ g) * 2 ^ g + ((s_hi + c_hi + k) % 2 ^ g) := by
      rw [Nat.mul_comm]; exact (Nat.div_add_mod _ _).symm
    have h3 : (s_hi + c_hi + k) * 2 ^ shift + r_lo =
        ((s_hi + c_hi + k) / 2 ^ g) * 2 ^ W + (((s_hi + c_hi + k) % 2 ^ g) * 2 ^ shift + r_lo) := by
      calc (s_hi + c_hi + k) * 2 ^ shift + r_lo
          = (((s_hi + c_hi + k) / 2 ^ g) * 2 ^ g + ((s_hi + c_hi + k) % 2 ^ g)) * 2 ^ shift + r_lo := by rw [← hdiv_g]
        _ = ((s_hi + c_hi + k) / 2 ^ g) * (2 ^ g * 2 ^ shift) + (((s_hi + c_hi + k) % 2 ^ g) * 2 ^ shift + r_lo) := by
              rw [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
        _ = ((s_hi + c_hi + k) / 2 ^ g) * 2 ^ W + (((s_hi + c_hi + k) % 2 ^ g) * 2 ^ shift + r_lo) := by rw [hpow]
    rw [h3, Nat.mul_add_mod_self_right]
    apply Nat.mod_eq_of_lt
    have hrem : (s_hi + c_hi + k) % 2 ^ g < 2 ^ g := Nat.mod_lt _ (pow2_pos g)
    have hrlo : r_lo < 2 ^ shift := Nat.mod_lt _ hpow_pos
    have hle : ((s_hi + c_hi + k) % 2 ^ g + 1) * 2 ^ shift ≤ 2 ^ g * 2 ^ shift :=
      Nat.mul_le_mul_right _ hrem
    rw [Nat.add_mul, Nat.one_mul, hpow] at hle
    omega
  have hSC_hi : ((S + C) % 2 ^ W) / 2 ^ shift = (s_hi + c_hi + k) % 2 ^ g := by
    rw [hSC_eq, Nat.mul_comm _ (2 ^ shift), Nat.mul_add_div hpow_pos,
        Nat.div_eq_of_lt (Nat.mod_lt _ hpow_pos), Nat.add_zero]
  have hSC_lo : (S + C) % 2 ^ shift = r_lo := by
    have h1 : (S + C) % 2 ^ shift = ((S + C) % 2 ^ W) % 2 ^ shift := (Nat.mod_mod_of_dvd _ hdvd).symm
    rw [h1, hSC_eq, Nat.mul_add_mod_self_right]
    exact Nat.mod_eq_of_lt (Nat.mod_lt _ hpow_pos)
  have hV_eq : signedVal W (S + C) = V := signedVal_eq_of_range hW hV_lo hV_hi hsum
  have hV_split : V = signedVal g ((s_hi + c_hi + k) % 2 ^ g) * p2 shift + (r_lo : Int) := by
    rw [← hV_eq, signedVal_split_hi_lo G.hg hWg (S + C), hSC_hi, hSC_lo]
  have hloc := G.h_local s_hi c_hi k hs_hi_lt hc_hi_lt hk_le (hSC_hi ▸ hallow)
  dsimp only [applyTopGuard]
  let s_new := (G.norm s_hi c_hi).1
  let c_new := (G.norm s_hi c_hi).2
  let S' := (s_new % 2 ^ g) * 2 ^ shift + s_lo
  let C' := (c_new % 2 ^ g) * 2 ^ shift + c_lo
  have hS'_lt : S' < 2 ^ W := by
    have h1 : (s_new % 2 ^ g + 1) * 2 ^ shift ≤ 2 ^ g * 2 ^ shift :=
      Nat.mul_le_mul_right _ (Nat.mod_lt s_new (pow2_pos g))
    rw [Nat.add_mul, Nat.one_mul, hpow] at h1
    omega
  have hC'_lt : C' < 2 ^ W := by
    have h1 : (c_new % 2 ^ g + 1) * 2 ^ shift ≤ 2 ^ g * 2 ^ shift :=
      Nat.mul_le_mul_right _ (Nat.mod_lt c_new (pow2_pos g))
    rw [Nat.add_mul, Nat.one_mul, hpow] at h1
    omega
  have hS'_hi : (S' % 2 ^ W) / 2 ^ shift = s_new % 2 ^ g := by
    rw [Nat.mod_eq_of_lt hS'_lt]
    show ((s_new % 2 ^ g) * 2 ^ shift + s_lo) / 2 ^ shift = s_new % 2 ^ g
    rw [Nat.mul_comm _ (2 ^ shift), Nat.mul_add_div hpow_pos, Nat.div_eq_of_lt hs_lo_lt, Nat.add_zero]
  have hS'_lo : S' % 2 ^ shift = s_lo := by
    show ((s_new % 2 ^ g) * 2 ^ shift + s_lo) % 2 ^ shift = s_lo
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hs_lo_lt]
  have hC'_hi : (C' % 2 ^ W) / 2 ^ shift = c_new % 2 ^ g := by
    rw [Nat.mod_eq_of_lt hC'_lt]
    show ((c_new % 2 ^ g) * 2 ^ shift + c_lo) / 2 ^ shift = c_new % 2 ^ g
    rw [Nat.mul_comm _ (2 ^ shift), Nat.mul_add_div hpow_pos, Nat.div_eq_of_lt hc_lo_lt, Nat.add_zero]
  have hC'_lo : C' % 2 ^ shift = c_lo := by
    show ((c_new % 2 ^ g) * 2 ^ shift + c_lo) % 2 ^ shift = c_lo
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hc_lo_lt]
  show signedVal W S' + signedVal W C' = V
  rw [signedVal_split_hi_lo G.hg hWg S', signedVal_split_hi_lo G.hg hWg C',
      hS'_hi, hS'_lo, hC'_hi, hC'_lo, signedVal_mod, signedVal_mod, hV_split]
  have hlo_int : (s_lo : Int) + (c_lo : Int) = (k : Int) * p2 shift + (r_lo : Int) := by
    unfold p2
    rw [← Int.natCast_add, ← Int.natCast_mul, ← Int.natCast_add]
    exact congrArg Int.ofNat hlo_decomp
  grind

/--
  THEOREM 1 (Exact g-Bit Zero-Carry-Top Normalizer, ∀ g ≥ 2, ∀ W ≥ g):
  For ANY `g ≥ 2`, ANY width `W ≥ g`, and ANY Carry-Save pair `(S, C)` whose modular sum
  `V` lies in the asymmetric range `[-2^(W-1) + 2^(W-g), 2^(W-1) - 1]`:
    1. `signedVal W S' + signedVal W C' = V` EXACTLY IN `Int` (zero wraparound!)
    2. `C' < 2^(W - g)` (top `g` bits of `C'` are identically zero, so `C'` is non-negative!).
-/
theorem zeroCarryTop_exact {g W : Nat} (hg : 2 ≤ g) (hWg : g ≤ W) (S C : Nat) {V : Int}
    (hV_lo : -p2 (W - 1) + p2 (W - g) ≤ V)
    (hV_hi : V < p2 (W - 1))
    (hsum : (((S + C) % 2 ^ W : Nat) : Int) = V % p2 W) :
    let (S', C') := applyTopGuard g W (zeroCarryTopNorm g) S C
    signedVal W S' + signedVal W C' = V ∧ C' < 2 ^ (W - g) := by
  have hg1 : 1 ≤ g := by omega
  have hW : 1 ≤ W := by omega
  have hV_lo' : -p2 (W - 1) ≤ V := by
    have := p2_pos (W - g); omega
  have hallow : ((S + C) % 2 ^ W) / 2 ^ (W - g) ≠ 2 ^ (g - 1) := by
    intro heq
    have hV_eq : signedVal W (S + C) = V := signedVal_eq_of_range hW hV_lo' hV_hi hsum
    have hsplit := signedVal_split_hi_lo hg1 hWg (S + C)
    rw [hV_eq, heq] at hsplit
    have h2g : 2 * 2 ^ (g - 1) = 2 ^ g := pow2_pred_double hg1
    have hpow_half : p2 (g - 1) * p2 (W - g) = p2 (W - 1) := by
      rw [p2_add]; congr 1; omega
    have hsg : signedVal g (2 ^ (g - 1)) = -p2 (g - 1) := signedVal_half hg1
    rw [hsg] at hsplit
    have hrem : (S + C) % 2 ^ (W - g) < 2 ^ (W - g) := Nat.mod_lt _ (pow2_pos (W - g))
    have hremI : (((S + C) % 2 ^ (W - g) : Nat) : Int) < p2 (W - g) := by unfold p2; omega
    grind
  constructor
  · exact (zeroCarryTopSpec hg).lift_all_widths hWg S C hV_lo' hV_hi hsum hallow
  · show (0 % 2 ^ g) * 2 ^ (W - g) + C % 2 ^ (W - g) < 2 ^ (W - g)
    simp [Nat.mod_lt _ (pow2_pos (W - g))]

/-- THEOREM 2 (Dual Min-Safe g-Bit Normalizer, ∀ g ≥ 2, ∀ W ≥ g). -/
theorem minSafe_exact {g W : Nat} (hg : 2 ≤ g) (hWg : g ≤ W) (S C : Nat) {V : Int}
    (hV_lo : -p2 (W - 1) ≤ V)
    (hV_hi : V < p2 (W - 1) - p2 (W - g))
    (hsum : (((S + C) % 2 ^ W : Nat) : Int) = V % p2 W) :
    let (S', C') := applyTopGuard g W (minSafeNorm g) S C
    signedVal W S' + signedVal W C' = V := by
  have hg1 : 1 ≤ g := by omega
  have hW : 1 ≤ W := by omega
  have hV_hi' : V < p2 (W - 1) := by
    have := p2_pos (W - g); omega
  have hallow : ((S + C) % 2 ^ W) / 2 ^ (W - g) ≠ 2 ^ (g - 1) - 1 := by
    intro heq
    have hV_eq : signedVal W (S + C) = V := signedVal_eq_of_range hW hV_lo hV_hi' hsum
    have hsplit := signedVal_split_hi_lo hg1 hWg (S + C)
    rw [hV_eq, heq] at hsplit
    have hpow_half : p2 (g - 1) * p2 (W - g) = p2 (W - 1) := by
      rw [p2_add]; congr 1; omega
    have hpos_half : 1 ≤ 2 ^ (g - 1) := pow2_pos (g - 1)
    have hsg : signedVal g (2 ^ (g - 1) - 1) = ((2 ^ (g - 1) - 1 : Nat) : Int) :=
      signedVal_of_lt_half _ (by omega) hg1
    rw [hsg] at hsplit
    have hcast : ((2 ^ (g - 1) - 1 : Nat) : Int) = p2 (g - 1) - 1 := by unfold p2; omega
    have hrem : (0 : Int) ≤ (((S + C) % 2 ^ (W - g) : Nat) : Int) := by omega
    rw [hcast] at hsplit
    grind
  exact (minSafeSpec hg).lift_all_widths hWg S C hV_lo hV_hi' hsum hallow

theorem guardCert_g2_zeroCarryTop_ok : guardCert_g2_zeroCarryTop.check = true := by decide

theorem guardCert_g3_zeroCarryTop_ok : guardCert_g3_zeroCarryTop.check = true := by decide

theorem guardCert_g2_minSafe_ok : guardCert_g2_minSafe.check = true := by decide

/--
  THEOREM 3 (Exact Carry-Save Arithmetic Right Shift & k-Bit LSB Extraction, ∀ W ≥ 1, ∀ k ≥ 1):
  Once `(S', C')` is unwrapped (`signedVal W S' + signedVal W C' = V`) and `C' < 2^(W-1)`
  (automatically guaranteed by `zeroCarryTop_exact`!), arithmetic right shift of `S'`
  paired with UNSIGNED right shift of `C'` plus the 1-bit k-LSB carry `c_lsb` computes
  `ediv V (2^k)` EXACTLY IN `Int` and extracts `V mod 2^k`!
-/
theorem csa_arith_rshift_exact {W k : Nat} (hW : 1 ≤ W) (_hk : 1 ≤ k) (hkW : k ≤ W)
    {S' C' : Nat} {V : Int}
    (hsum : signedVal W S' + signedVal W C' = V)
    (hC' : C' < 2 ^ (W - 1)) :
    let rS := S' % 2 ^ k
    let rC := C' % 2 ^ k
    let p  := (rS + rC) % 2 ^ k
    let c_lsb := (rS + rC) / 2 ^ k
    (signedVal W S' / p2 k) + ((C' / 2 ^ k : Nat) : Int) + (c_lsb : Int) = V / p2 k ∧
    (p : Int) = V % p2 k := by
  have hd_pos : (0 : Int) < p2 k := p2_pos k
  have hdvd : 2 ^ k ∣ 2 ^ W := ⟨2 ^ (W - k), by rw [← Nat.pow_add, Nat.add_sub_of_le hkW]⟩
  have hS_mod : signedVal W S' % p2 k = ((S' % 2 ^ k : Nat) : Int) := by
    have hdvdI : p2 k ∣ p2 W := by
      rcases hdvd with ⟨q, hq⟩
      exact ⟨(q : Int), by unfold p2; rw [← Int.natCast_mul]; exact congrArg Int.ofNat hq⟩
    have h1 : signedVal W S' % p2 k = (signedVal W S' % p2 W) % p2 k :=
      (Int.emod_emod_of_dvd _ hdvdI).symm
    rw [h1, signedVal_emod (W := W)]
    have hnat : (S' % 2 ^ W) % 2 ^ k = S' % 2 ^ k := Nat.mod_mod_of_dvd S' hdvd
    unfold p2
    rw [← Int.natCast_emod]
    exact congrArg Int.ofNat hnat
  have hC_val : signedVal W C' = (C' : Int) := signedVal_of_lt_half C' hC' hW
  have hS_div : p2 k * (signedVal W S' / p2 k) + ((S' % 2 ^ k : Nat) : Int) = signedVal W S' := by
    rw [← hS_mod]
    exact int_mul_ediv_add_emod (signedVal W S') (p2 k)
  have hC_div : p2 k * ((C' / 2 ^ k : Nat) : Int) + ((C' % 2 ^ k : Nat) : Int) = (C' : Int) := by
    unfold p2
    rw [← Int.natCast_mul, ← Int.natCast_add]
    exact congrArg Int.ofNat (Nat.div_add_mod C' (2 ^ k))
  have hlsbI : p2 k * (((S' % 2 ^ k + C' % 2 ^ k) / 2 ^ k : Nat) : Int) +
      (((S' % 2 ^ k + C' % 2 ^ k) % 2 ^ k : Nat) : Int) =
      ((S' % 2 ^ k : Nat) : Int) + ((C' % 2 ^ k : Nat) : Int) := by
    unfold p2
    rw [← Int.natCast_mul, ← Int.natCast_add, ← Int.natCast_add]
    exact congrArg Int.ofNat (Nat.div_add_mod (S' % 2 ^ k + C' % 2 ^ k) (2 ^ k))
  have hV_decomp : V =
      p2 k * ((signedVal W S' / p2 k) + ((C' / 2 ^ k : Nat) : Int) +
        (((S' % 2 ^ k + C' % 2 ^ k) / 2 ^ k : Nat) : Int)) +
      (((S' % 2 ^ k + C' % 2 ^ k) % 2 ^ k : Nat) : Int) := by
    grind
  have hp_lt : (((S' % 2 ^ k + C' % 2 ^ k) % 2 ^ k : Nat) : Int) < p2 k := by
    unfold p2; have := Nat.mod_lt (S' % 2 ^ k + C' % 2 ^ k) (pow2_pos k); omega
  have hp_nonneg : (0 : Int) ≤ (((S' % 2 ^ k + C' % 2 ^ k) % 2 ^ k : Nat) : Int) := by omega
  dsimp only
  let Q := (signedVal W S' / p2 k) + ((C' / 2 ^ k : Nat) : Int) +
      (((S' % 2 ^ k + C' % 2 ^ k) / 2 ^ k : Nat) : Int)
  let P := (((S' % 2 ^ k + C' % 2 ^ k) % 2 ^ k : Nat) : Int)
  have hV_ediv : V / p2 k = Q := by
    rw [hV_decomp, Int.mul_comm (p2 k) Q, Int.mul_add_ediv_right _ _ (by omega),
        Int.ediv_eq_zero_of_lt hp_nonneg hp_lt, Int.add_zero]
  have hV_emod : V % p2 k = P := by
    rw [hV_decomp, Int.mul_comm (p2 k) Q, Int.mul_add_emod_self_right,
        Int.emod_eq_of_lt hp_nonneg hp_lt]
  exact ⟨hV_ediv.symm, hV_emod.symm⟩

/-! ### SHARPNESS & UNIVERSAL IMPOSSIBILITY BARRIERS -/

/--
  THEOREM 4 (Universal Carry-Save Cut-Arc Impossibility Barrier, ∀ g ≥ 1, ∀ W > g):
  NO local top-`g`-bit function `f : Nat → Nat → Nat × Nat` (leaving lower `W - g` bits
  untouched) can unwrap `(S, C)` on any domain containing BOTH `V1 = 2^(W-1) - 2^(W-g)`
  and `V2 = -2^(W-1)`!
-/
theorem cut_arc_impossibility {g W : Nat} (hg : 1 ≤ g) (hWg : g < W)
    (f : Nat → Nat → Nat × Nat) :
    let S1 := (2 ^ (g - 1) - 1) * 2 ^ (W - g)
    let C1 := 0
    let S2 := (2 ^ (g - 1) - 1) * 2 ^ (W - g) + (2 ^ (W - g) - 1)
    let C2 := 1
    let V1 : Int := p2 (W - 1) - p2 (W - g)
    let V2 : Int := -p2 (W - 1)
    (((S1 + C1) % 2 ^ W : Nat) : Int) = V1 % p2 W ∧
    (((S2 + C2) % 2 ^ W : Nat) : Int) = V2 % p2 W ∧
    ¬ (signedVal W (applyTopGuard g W f S1 C1).1 + signedVal W (applyTopGuard g W f S1 C1).2 = V1 ∧
       signedVal W (applyTopGuard g W f S2 C2).1 + signedVal W (applyTopGuard g W f S2 C2).2 = V2) := by
  have hW : 1 ≤ W := by omega
  have hWg_le : g ≤ W := by omega
  have hshift_pos : 1 ≤ W - g := by omega
  have hpow : 2 ^ g * 2 ^ (W - g) = 2 ^ W := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hWg_le]
  have hpow_half : 2 ^ (g - 1) * 2 ^ (W - g) = 2 ^ (W - 1) := by
    rw [← Nat.pow_add]; congr 1; omega
  have h2W : 2 * 2 ^ (W - 1) = 2 ^ W := pow2_pred_double hW
  have hpos_half_g : 1 ≤ 2 ^ (g - 1) := pow2_pos (g - 1)
  have hpos_shift : 2 ≤ 2 ^ (W - g) := by
    have : 2 ^ 1 ≤ 2 ^ (W - g) := Nat.pow_le_pow_right (by decide) hshift_pos
    simpa using this
  have hle_shift : 2 ^ (W - g) ≤ 2 ^ (W - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  dsimp only
  let S1 := (2 ^ (g - 1) - 1) * 2 ^ (W - g)
  let S2 := (2 ^ (g - 1) - 1) * 2 ^ (W - g) + (2 ^ (W - g) - 1)
  let V1 : Int := p2 (W - 1) - p2 (W - g)
  let V2 : Int := -p2 (W - 1)
  have hS1_eq : S1 = 2 ^ (W - 1) - 2 ^ (W - g) := by
    dsimp [S1]; rw [Nat.sub_mul, Nat.one_mul, hpow_half]
  have hS1_lt : S1 < 2 ^ W := by omega
  have hS2_eq : S2 + 1 = 2 ^ (W - 1) := by dsimp [S2]; omega
  have hS2_lt : S2 < 2 ^ W := by omega
  have h1_lt : 1 < 2 ^ W := by omega
  have h1_lt_shift : 1 < 2 ^ (W - g) := by omega
  have hV1_mod : (((S1 + 0) % 2 ^ W : Nat) : Int) = V1 % p2 W := by
    rw [Nat.add_zero, Nat.mod_eq_of_lt hS1_lt]
    have hV1_nonneg : (0 : Int) ≤ V1 := by dsimp only [V1, p2]; omega
    have hV1_lt : V1 < p2 W := by dsimp only [V1, p2]; omega
    rw [Int.emod_eq_of_lt hV1_nonneg hV1_lt, hS1_eq]
    dsimp only [V1, p2]; omega
  have hV2_mod : (((S2 + 1) % 2 ^ W : Nat) : Int) = V2 % p2 W := by
    rw [hS2_eq, Nat.mod_eq_of_lt (by omega : 2 ^ (W - 1) < 2 ^ W)]
    have : V2 % p2 W = (V2 + p2 W) % p2 W := by rw [Int.add_emod_right]
    rw [this]
    have heq : V2 + p2 W = p2 (W - 1) := by dsimp only [V2, p2]; omega
    rw [heq, Int.emod_eq_of_lt (by unfold p2; omega) (by unfold p2; omega)]
  refine ⟨hV1_mod, hV2_mod, ?_⟩
  intro ⟨hEq1, hEq2⟩
  have hS1_hi : (S1 % 2 ^ W) / 2 ^ (W - g) = 2 ^ (g - 1) - 1 := by
    rw [Nat.mod_eq_of_lt hS1_lt]
    show ((2 ^ (g - 1) - 1) * 2 ^ (W - g)) / 2 ^ (W - g) = 2 ^ (g - 1) - 1
    exact Nat.mul_div_cancel _ (pow2_pos (W - g))
  have hS2_hi : (S2 % 2 ^ W) / 2 ^ (W - g) = 2 ^ (g - 1) - 1 := by
    rw [Nat.mod_eq_of_lt hS2_lt]
    show ((2 ^ (g - 1) - 1) * 2 ^ (W - g) + (2 ^ (W - g) - 1)) / 2 ^ (W - g) = 2 ^ (g - 1) - 1
    rw [Nat.mul_comm (2 ^ (g - 1) - 1), Nat.mul_add_div (pow2_pos (W - g)),
        Nat.div_eq_of_lt (by omega), Nat.add_zero]
  have hC1_hi : (0 % 2 ^ W) / 2 ^ (W - g) = 0 := by simp
  have hC2_hi : (1 % 2 ^ W) / 2 ^ (W - g) = 0 := by
    rw [Nat.mod_eq_of_lt h1_lt, Nat.div_eq_of_lt h1_lt_shift]
  have hS1_lo : S1 % 2 ^ (W - g) = 0 := by
    show ((2 ^ (g - 1) - 1) * 2 ^ (W - g)) % 2 ^ (W - g) = 0
    exact Nat.mul_mod_left _ _
  have hS2_lo : S2 % 2 ^ (W - g) = 2 ^ (W - g) - 1 := by
    show ((2 ^ (g - 1) - 1) * 2 ^ (W - g) + (2 ^ (W - g) - 1)) % 2 ^ (W - g) = 2 ^ (W - g) - 1
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have hC1_lo : 0 % 2 ^ (W - g) = 0 := by simp
  have hC2_lo : 1 % 2 ^ (W - g) = 1 := Nat.mod_eq_of_lt h1_lt_shift
  let res := f (2 ^ (g - 1) - 1) 0
  have hA1 : applyTopGuard g W f S1 0 = ((res.1 % 2 ^ g) * 2 ^ (W - g) + 0, (res.2 % 2 ^ g) * 2 ^ (W - g) + 0) := by
    simp only [applyTopGuard, hS1_hi, hC1_hi, hS1_lo, hC1_lo]; rfl
  have hA2 : applyTopGuard g W f S2 1 =
      ((res.1 % 2 ^ g) * 2 ^ (W - g) + (2 ^ (W - g) - 1), (res.2 % 2 ^ g) * 2 ^ (W - g) + 1) := by
    simp only [applyTopGuard, hS2_hi, hC2_hi, hS2_lo, hC2_lo]; rfl
  have hsplit_form : ∀ (x r : Nat), r < 2 ^ (W - g) →
      signedVal W ((x % 2 ^ g) * 2 ^ (W - g) + r) =
        signedVal g (x % 2 ^ g) * p2 (W - g) + (r : Int) := by
    intro x r hr
    have hltW : (x % 2 ^ g) * 2 ^ (W - g) + r < 2 ^ W := by
      have h1 : (x % 2 ^ g + 1) * 2 ^ (W - g) ≤ 2 ^ g * 2 ^ (W - g) :=
        Nat.mul_le_mul_right _ (Nat.mod_lt x (pow2_pos g))
      rw [Nat.add_mul, Nat.one_mul, hpow] at h1
      omega
    rw [signedVal_split_hi_lo hg hWg_le, Nat.mod_eq_of_lt hltW,
        Nat.mul_comm (x % 2 ^ g), Nat.mul_add_div (pow2_pos (W - g)), Nat.div_eq_of_lt hr, Nat.add_zero,
        Nat.mul_comm (2 ^ (W - g)), Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hr]
  change signedVal W (applyTopGuard g W f S1 0).1 + signedVal W (applyTopGuard g W f S1 0).2 = V1 at hEq1
  change signedVal W (applyTopGuard g W f S2 1).1 + signedVal W (applyTopGuard g W f S2 1).2 = V2 at hEq2
  rw [hA1] at hEq1
  rw [hA2] at hEq2
  rw [hsplit_form res.1 0 (by omega), hsplit_form res.2 0 (by omega)] at hEq1
  rw [hsplit_form res.1 (2 ^ (W - g) - 1) (by omega), hsplit_form res.2 1 h1_lt_shift] at hEq2
  have hWpos := p2_pos W
  dsimp only [V1, V2, p2] at hEq1 hEq2
  omega

/-- Corollary: `g = 1` top-bit normalizer is impossible for ALL `W ≥ 2`. -/
theorem guard_one_impossible {W : Nat} (hW : 2 ≤ W) (f : Nat → Nat → Nat × Nat) :
    ¬ (∀ S C : Nat, ∀ V : Int,
        -p2 (W - 1) ≤ V → V < p2 (W - 1) →
        (((S + C) % 2 ^ W : Nat) : Int) = V % p2 W →
        signedVal W (applyTopGuard 1 W f S C).1 + signedVal W (applyTopGuard 1 W f S C).2 = V) := by
  intro hall
  have himp := cut_arc_impossibility (g := 1) (W := W) (by decide) (by omega) f
  rcases himp with ⟨hm1, hm2, hnot⟩
  apply hnot
  have hpos := p2_pos (W - 1)
  have h1 := hall ((2 ^ (1 - 1) - 1) * 2 ^ (W - 1)) 0 (p2 (W - 1) - p2 (W - 1)) (by omega) (by omega) hm1
  have h2 := hall ((2 ^ (1 - 1) - 1) * 2 ^ (W - 1) + (2 ^ (W - 1) - 1)) 1 (-p2 (W - 1)) (by omega) (by omega) hm2
  exact ⟨h1, h2⟩

/-- Sharpness Corollary: Naive unnormalized CSA right-shift fails with error `-2^(W-1)` at `V = 0` ∀ W ≥ 3. -/
theorem unnormalized_csa_rshift_fails {W : Nat} (hW : 3 ≤ W) :
    let S := 2 ^ (W - 1)
    let C := 2 ^ (W - 1)
    signedVal W (S + C) = 0 ∧
    (signedVal W S / 2) + (signedVal W C / 2) + (((S % 2 + C % 2) / 2 : Nat) : Int) =
      -p2 (W - 1) := by
  have hW1 : 1 ≤ W := by omega
  have h2W : 2 * 2 ^ (W - 1) = 2 ^ W := pow2_pred_double hW1
  have h2Wm1 : 2 * 2 ^ (W - 2) = 2 ^ (W - 1) := by
    have h := pow2_pred_double (W := W - 1) (by omega)
    simpa [Nat.sub_sub] using h
  have hpos_wm1 : 0 < 2 ^ (W - 1) := pow2_pos (W - 1)
  dsimp only
  have hSC : 2 ^ (W - 1) + 2 ^ (W - 1) = 2 ^ W := by omega
  have hzero : signedVal W (2 ^ (W - 1) + 2 ^ (W - 1)) = 0 := by
    rw [hSC]; unfold signedVal; simp [pow2_pos]
  have hs : signedVal W (2 ^ (W - 1)) = -p2 (W - 1) := signedVal_half hW1
  have heven : 2 ^ (W - 1) % 2 = 0 := by
    rw [← h2Wm1]; simp
  have hdiv : (-p2 (W - 1)) / 2 = -p2 (W - 2) := by
    have : -p2 (W - 1) = (-p2 (W - 2)) * 2 := by unfold p2; omega
    rw [this, Int.mul_ediv_cancel _ (by decide)]
  refine ⟨hzero, ?_⟩
  rw [hs, hdiv, heven]
  unfold p2; omega


/-! ============================================================================
    SECTION 4: Universal Radix-2^k Booth Recoding, 2-State Sign-Extension
               Cancellation (SEC), and Pure-Silicon Radix-4 Booth Tree
    ============================================================================ -/

private theorem radixSum_unsigned (k Y m : Nat) :
    radixSum (2 ^ k) (fun j => (radixDigit k Y j : Int)) m = ((Y % 2 ^ (k * m) : Nat) : Int) := by
  induction m with
  | zero => simp [radixSum]
  | succ n ih =>
    simp only [radixSum, ih]
    have hpow : (2 ^ k) ^ n = 2 ^ (k * n) := (Nat.pow_mul 2 k n).symm
    have hpow1 : 2 ^ (k * (n + 1)) = 2 ^ (k * n) * 2 ^ k := by
      rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
    have hnat : Y % 2 ^ (k * n) + radixDigit k Y n * 2 ^ (k * n) = Y % 2 ^ (k * (n + 1)) := by
      unfold radixDigit
      have hdvd : 2 ^ (k * n) ∣ 2 ^ (k * n) * 2 ^ k := ⟨2 ^ k, rfl⟩
      have hdiv := Nat.div_add_mod (Y % (2 ^ (k * n) * 2 ^ k)) (2 ^ (k * n))
      rw [Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd Y hdvd] at hdiv
      rw [hpow1]
      grind
    rw [hpow, ← Int.natCast_mul, ← Int.natCast_add, hnat]

private theorem boothTransducer_run {k : Nat} (hk : 1 ≤ k) (Y j : Nat) :
    (boothTransducer hk).run false (fun i => ⟨radixDigit k Y i, Nat.mod_lt _ (pow2_pos k)⟩) j =
      boothPrevBit k Y j := by
  induction j with
  | zero => rfl
  | succ n _ => rfl

/--
  THEOREM 5 (Universal Radix-`2^k` Booth Recoding Theorem, ∀ k ≥ 1, ∀ m ≥ 1):
  Directly discharged by Mechanism I (`RadixTransducer.lift_sum`) on the 2-state
  `boothTransducer`:
    `∑_{j=0}^{m-1} d_j(Y) * 2^(k*j) = signedVal (k * m) Y`.
-/
theorem booth_recoding_exact {k m : Nat} (hk : 1 ≤ k) (hm : 1 ≤ m) (Y : Nat) :
    radixSum (2 ^ k) (fun j => boothDigit k Y j) m = signedVal (k * m) Y := by
  let stream : Nat → Fin (2 ^ k) := fun i => ⟨radixDigit k Y i, Nat.mod_lt _ (pow2_pos k)⟩
  have hlift := (boothTransducer hk).lift_sum (q0 := false) trivial stream m
  have hrun : ∀ i, (boothTransducer hk).run false stream i = boothPrevBit k Y i :=
    boothTransducer_run hk Y
  have hdelta : radixSum (2 ^ k) (fun i => boothDigit k Y i - (radixDigit k Y i : Int)) m =
      (if boothPrevBit k Y m then (-1 : Int) else 0) * (((2 ^ k) ^ m : Nat) : Int) := by
    have h1 : (fun i => (boothTransducer hk).delta ((boothTransducer hk).run false stream i) (stream i)) =
        (fun i => boothDigit k Y i - (radixDigit k Y i : Int)) := by
      funext i; rw [hrun i]; rfl
    rw [h1, hrun m] at hlift
    dsimp only [boothTransducer] at hlift
    simpa using hlift
  rw [radixSum_sub, radixSum_unsigned] at hdelta
  have hpow : (2 ^ k) ^ m = 2 ^ (k * m) := (Nat.pow_mul 2 k m).symm
  rw [hpow] at hdelta
  have hkm : 1 ≤ k * m := Nat.mul_pos hk hm
  cases m with
  | zero => omega
  | succ n =>
    have hkn1 : k * (n + 1) = k * n + k := by rw [Nat.mul_add, Nat.mul_one]
    have hbit : boothPrevBit k Y (n + 1) =
        decide (2 ^ (k * (n + 1) - 1) ≤ Y % 2 ^ (k * (n + 1))) := by
      simp only [boothPrevBit, radixDigit]
      have hpow_hi : 2 ^ (k * n) * 2 ^ (k - 1) = 2 ^ (k * (n + 1) - 1) := by
        rw [← Nat.pow_add]; congr 1; omega
      have hpow_full : 2 ^ (k * n) * 2 ^ k = 2 ^ (k * (n + 1)) := by
        rw [← Nat.pow_add, ← hkn1]
      have h2km : 2 * 2 ^ (k * (n + 1) - 1) = 2 ^ (k * (n + 1)) := pow2_pred_double hkm
      have htop_eq : (Y / 2 ^ (k * n)) % 2 ^ k / 2 ^ (k - 1) =
          (Y % 2 ^ (k * (n + 1))) / 2 ^ (k * (n + 1) - 1) := by
        have h1 : (Y % 2 ^ (k * (n + 1))) / 2 ^ (k * n) = (Y / 2 ^ (k * n)) % 2 ^ k := by
          rw [← hpow_full, Nat.mod_mul_right_div_self]
        rw [← h1, Nat.div_div_eq_div_mul, hpow_hi]
      have hlt2 : (Y % 2 ^ (k * (n + 1))) / 2 ^ (k * (n + 1) - 1) < 2 := by
        rw [Nat.div_lt_iff_lt_mul (pow2_pos _), h2km]
        exact Nat.mod_lt Y (pow2_pos _)
      have hmod2_eq : (Y / 2 ^ (k * n)) % 2 ^ k / 2 ^ (k - 1) % 2 =
          (Y % 2 ^ (k * (n + 1))) / 2 ^ (k * (n + 1) - 1) := by
        rw [htop_eq, Nat.mod_eq_of_lt hlt2]
      simp only [hmod2_eq]
      by_cases hle : 2 ^ (k * (n + 1) - 1) ≤ Y % 2 ^ (k * (n + 1))
      · have heq1 : (Y % 2 ^ (k * (n + 1))) / 2 ^ (k * (n + 1) - 1) = 1 := by
          have hge1 : 1 ≤ (Y % 2 ^ (k * (n + 1))) / 2 ^ (k * (n + 1) - 1) := by
            rw [Nat.le_div_iff_mul_le (pow2_pos _), Nat.one_mul]; exact hle
          omega
        simp [hle, heq1]
      · have heq0 : (Y % 2 ^ (k * (n + 1))) / 2 ^ (k * (n + 1) - 1) = 0 :=
          Nat.div_eq_of_lt (Nat.lt_of_not_ge hle)
        simp [hle, heq0]
    rw [hbit] at hdelta
    unfold signedVal p2
    by_cases hlt : Y % 2 ^ (k * (n + 1)) < 2 ^ (k * (n + 1) - 1)
    · have hnot : ¬ (2 ^ (k * (n + 1) - 1) ≤ Y % 2 ^ (k * (n + 1))) := by omega
      simp only [hlt, hnot, decide_false, ↓reduceIte, Bool.false_eq_true, Int.zero_mul] at hdelta ⊢
      grind
    · have hge : 2 ^ (k * (n + 1) - 1) ≤ Y % 2 ^ (k * (n + 1)) := by omega
      simp only [hlt, hge, decide_true, ↓reduceIte] at hdelta ⊢
      grind

theorem boothCert_r2_ok : (makeBoothCert 1).check = true := by decide
theorem boothCert_r4_ok : (makeBoothCert 2).check = true := by decide
theorem boothCert_r8_ok : (makeBoothCert 3).check = true := by decide

/-! ### 2-State General Radix-2^k Sign-Extension Cancellation (SEC) Automaton -/

private theorem secTransducer_run_pos {k : Nat} (hk : 1 ≤ k) (s : Nat → Fin 2) (j : Nat) :
    (secTransducer hk).run false s j = decide (0 < j) := by
  cases j with
  | zero => rfl
  | succ n => rfl

/--
  THEOREM 6 (Universal 2-State Radix-`2^k` Sign-Extension Cancellation Law, ∀ k ≥ 1, ∀ W, ∀ m ≥ 1):
  Directly discharged by Mechanism I (`RadixTransducer.lift_sum`) on `secTransducer`:
    `∑_{j=0}^{m-1} secTerm_k(j > 0, s_j) * 2^(W + k*j) + ∑_{j=0}^{m-1} s_j * 2^(W + k*j) = 2^(W + k*m)`.
-/
theorem sec_cancellation_exact {k m : Nat} (hk : 1 ≤ k) (hm : 1 ≤ m) (W : Nat) (s : Nat → Fin 2) :
    p2 W * radixSum (2 ^ k) (fun j => secTerm k (decide (0 < j)) (s j).val) m +
    p2 W * radixSum (2 ^ k) (fun j => ((s j).val : Int)) m =
      p2 (W + k * m) := by
  have hlift := (secTransducer hk).lift_sum (q0 := false) trivial s m
  have hrun : ∀ i, (secTransducer hk).run false s i = decide (0 < i) := secTransducer_run_pos hk s
  have h1 : (fun i => (secTransducer hk).delta ((secTransducer hk).run false s i) (s i)) =
      (fun i => secTerm k (decide (0 < i)) (s i).val + ((s i).val : Int)) := by
    funext i; rw [hrun i]; rfl
  rw [h1, radixSum_add] at hlift
  have hm_pos : decide (0 < m) = true := decide_eq_true (by omega)
  have hpow : (2 ^ k) ^ m = 2 ^ (k * m) := (Nat.pow_mul 2 k m).symm
  rw [hrun m, hm_pos] at hlift
  dsimp only [secTransducer] at hlift
  simp only [↓reduceIte, Bool.false_eq_true, Int.one_mul, Int.sub_zero, hpow] at hlift
  have hpowW := p2_add W (k * m)
  unfold p2 at hpowW ⊢
  grind

theorem secCert_r2_ok : (makeSecCert 1).check = true := by decide
theorem secCert_r4_ok : (makeSecCert 2).check = true := by decide
theorem secCert_r8_ok : (makeSecCert 3).check = true := by decide

/-! ### Pure-Silicon Radix-4 Booth Partial-Product Decoder & Full Tree Theorem -/

/--
  THEOREM 7 (Exact Silicon Radix-4 Booth Partial-Product Law, ∀ w ≥ 1):
  Handles ALL 8 3-bit windows (including `-0 = 111` AND the extreme `X = -2^(w-1), d = -2`
  overflow case!) with zero extra payload bits:
    `Q + h - s * 2^(w+1) = d * signedVal w X`, with `Q < 2^(w+1)`, `h ≤ 1`, `s ≤ 1`.
-/
theorem radix4PP_exact {w : Nat} (hw : 1 ≤ w) (x_u : Nat) (q : Bool) (u2 : Nat) :
    let win3 := win3FromBits q u2
    let (Q, h, s) := radix4PP w x_u win3
    (Q : Int) + (h : Int) - (s : Int) * p2 (w + 1) =
      boothDigitLocal 2 q (u2 % 4) * signedVal w x_u ∧
    Q < 2 ^ (w + 1) ∧ h ≤ 1 ∧ s ≤ 1 := by
  have h2w : 2 * 2 ^ (w - 1) = 2 ^ w := pow2_pred_double hw
  have h2wp1 : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
  have hu_lt : x_u % 2 ^ w < 2 ^ w := Nat.mod_lt x_u (pow2_pos w)
  have hmsb_lt : (x_u % 2 ^ w) / 2 ^ (w - 1) < 2 := by
    rw [Nat.div_lt_iff_lt_mul (pow2_pos (w - 1)), h2w]; exact hu_lt
  have hmsb_cases : (x_u % 2 ^ w) / 2 ^ (w - 1) = 0 ∨ (x_u % 2 ^ w) / 2 ^ (w - 1) = 1 := by
    cases h : (x_u % 2 ^ w) / 2 ^ (w - 1) with
    | zero => exact Or.inl rfl
    | succ n => exact Or.inr (by omega)
  have hsigned : signedVal w x_u =
      ((x_u % 2 ^ w : Nat) : Int) - (((x_u % 2 ^ w) / 2 ^ (w - 1) : Nat) : Int) * p2 w := by
    unfold signedVal p2
    rcases hmsb_cases with h0 | h1
    · have hlt : x_u % 2 ^ w < 2 ^ (w - 1) := by
        cases Nat.lt_or_ge (x_u % 2 ^ w) (2 ^ (w - 1)) with
        | inl h => exact h
        | inr hge =>
          have : 1 ≤ (x_u % 2 ^ w) / 2 ^ (w - 1) := by rw [Nat.le_div_iff_mul_le (pow2_pos _)]; omega
          omega
      simp [hlt, h0]
    · have hge : ¬ (x_u % 2 ^ w < 2 ^ (w - 1)) := by
        intro hlt; have : (x_u % 2 ^ w) / 2 ^ (w - 1) = 0 := Nat.div_eq_of_lt hlt; omega
      simp [hge, h1]
  have hu_mod4 : u2 % 4 = 0 ∨ u2 % 4 = 1 ∨ u2 % 4 = 2 ∨ u2 % 4 = 3 := by omega
  have hpos_wp1 : 1 ≤ 2 ^ (w + 1) := pow2_pos (w + 1)
  have hpos_w : 1 ≤ 2 ^ w := pow2_pos w
  dsimp only [win3FromBits, radix4PP, boothDigitLocal, p2]
  rw [hsigned]
  clear hsigned
  unfold p2
  rw [h2wp1]
  have hu_lt' : x_u % 2 ^ w < 2 ^ w := hu_lt
  rcases hmsb_cases with hm | hm
  · rw [hm]
    generalize x_u % 2 ^ w = u at hu_lt' ⊢
    generalize 2 ^ w = M at hu_lt' hpos_w ⊢
    rcases hu_mod4 with hu4 | hu4 | hu4 | hu4 <;> cases q <;> rw [hu4] <;> simp <;> omega
  · rw [hm]
    generalize x_u % 2 ^ w = u at hu_lt' ⊢
    generalize 2 ^ w = M at hu_lt' hpos_w ⊢
    rcases hu_mod4 with hu4 | hu4 | hu4 | hu4 <;> cases q <;> rw [hu4] <;> simp <;> omega

/--
  THEOREM 8 (Complete Pure-Silicon Radix-4 Booth Tree + SEC Theorem, ∀ w ≥ 1, ∀ m ≥ 1):
  Combines Booth Transducer (Theorem 5) + Silicon PP (Theorem 7) + 2-State SEC (Theorem 6):
    1. `boothTreeSum w m x_u y_u = signedVal w x_u * signedVal (2*m) y_u + 2^(w + 1 + 2*m)`
       EXACTLY IN `Int`!
    2. Modulo `2^(w + 2*m)`, `boothTreeSum` equals the exact `(w + 2*m)`-bit signed product!
-/
theorem radix4_booth_tree_exact {w m : Nat} (hw : 1 ≤ w) (hm : 1 ≤ m) (x_u y_u : Nat) :
    boothTreeSum w m x_u y_u =
      signedVal w x_u * signedVal (2 * m) y_u + p2 (w + 1 + 2 * m) ∧
    boothTreeSum w m x_u y_u % p2 (w + 2 * m) =
      (signedVal w x_u * signedVal (2 * m) y_u) % p2 (w + 2 * m) := by
  let sFn : Nat → Fin 2 := fun j =>
    let win3 := win3FromBits (boothPrevBit 2 y_u j) (radixDigit 2 y_u j)
    have hs_le : (radix4PP w x_u win3).2.2 ≤ 1 :=
      (radix4PP_exact hw x_u (boothPrevBit 2 y_u j) (radixDigit 2 y_u j)).2.2.2
    ⟨(radix4PP w x_u win3).2.2, by omega⟩
  have hpp_term : ∀ j,
      let win3 := win3FromBits (boothPrevBit 2 y_u j) (radixDigit 2 y_u j)
      let (Q, h, _) := radix4PP w x_u win3
      ((Q : Int) + (h : Int)) =
        boothDigit 2 y_u j * signedVal w x_u + p2 (w + 1) * ((sFn j).val : Int) := by
    intro j
    have h1 : ((radix4PP w x_u (win3FromBits (boothPrevBit 2 y_u j) (radixDigit 2 y_u j))).1 : Int) +
              ((radix4PP w x_u (win3FromBits (boothPrevBit 2 y_u j) (radixDigit 2 y_u j))).2.1 : Int) -
              ((radix4PP w x_u (win3FromBits (boothPrevBit 2 y_u j) (radixDigit 2 y_u j))).2.2 : Int) * p2 (w + 1) =
              boothDigit 2 y_u j * signedVal w x_u := by
      have h0 := (radix4PP_exact hw x_u (boothPrevBit 2 y_u j) (radixDigit 2 y_u j)).1
      have hdig : radixDigit 2 y_u j % 4 = radixDigit 2 y_u j :=
        Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))
      rw [hdig] at h0
      exact h0
    dsimp only [sFn]
    rw [Int.mul_comm _ (p2 (w + 1))] at h1
    change ((radix4PP w x_u (win3FromBits (boothPrevBit 2 y_u j) (radixDigit 2 y_u j))).1 : Int) +
           ((radix4PP w x_u (win3FromBits (boothPrevBit 2 y_u j) (radixDigit 2 y_u j))).2.1 : Int) =
           boothDigit 2 y_u j * signedVal w x_u +
           p2 (w + 1) * ((radix4PP w x_u (win3FromBits (boothPrevBit 2 y_u j) (radixDigit 2 y_u j))).2.2 : Int)
    omega
  have hsum_pp : radixSum 4 (fun j =>
      let win3 := win3FromBits (boothPrevBit 2 y_u j) (radixDigit 2 y_u j)
      let (Q, h, _) := radix4PP w x_u win3
      (Q : Int) + (h : Int)) m =
    radixSum 4 (fun j => boothDigit 2 y_u j * signedVal w x_u) m +
    p2 (w + 1) * radixSum 4 (fun j => ((sFn j).val : Int)) m := by
    have heq : (fun j =>
        let win3 := win3FromBits (boothPrevBit 2 y_u j) (radixDigit 2 y_u j)
        let (Q, h, _) := radix4PP w x_u win3
        (Q : Int) + (h : Int)) =
      (fun j => boothDigit 2 y_u j * signedVal w x_u + p2 (w + 1) * ((sFn j).val : Int)) := by
      funext j; exact hpp_term j
    rw [heq, radixSum_add, radixSum_mul_const]
  have hsec := sec_cancellation_exact (k := 2) (by decide) hm (w + 1) sFn
  have hbooth := booth_recoding_exact (k := 2) (by decide) hm y_u
  have hmul : radixSum 4 (fun j => boothDigit 2 y_u j * signedVal w x_u) m =
      signedVal w x_u * signedVal (2 * m) y_u := by
    have : (fun j => boothDigit 2 y_u j * signedVal w x_u) =
        (fun j => signedVal w x_u * boothDigit 2 y_u j) := by funext j; grind
    rw [this, radixSum_mul_const, hbooth]
  have h1 : boothTreeSum w m x_u y_u =
      signedVal w x_u * signedVal (2 * m) y_u + p2 (w + 1 + 2 * m) := by
    unfold boothTreeSum
    rw [hsum_pp, hmul]
    have hsec_eq : p2 (w + 1) * radixSum 4 (fun j =>
        let win3 := win3FromBits (boothPrevBit 2 y_u j) (radixDigit 2 y_u j)
        let (_, _, s) := radix4PP w x_u win3
        secTerm 2 (decide (0 < j)) s) m =
      p2 (w + 1) * radixSum 4 (fun j => secTerm 2 (decide (0 < j)) (sFn j).val) m := rfl
    rw [hsec_eq]
    grind
  refine ⟨h1, ?_⟩
  rw [h1]
  have hpow : p2 (w + 1 + 2 * m) = 2 * p2 (w + 2 * m) := by
    have : w + 1 + 2 * m = (w + 2 * m) + 1 := by omega
    rw [this]; unfold p2; rw [Nat.pow_succ, Nat.mul_comm, Int.natCast_mul]; rfl
  rw [hpow, Int.add_emod, Int.mul_emod_left, Int.add_zero, Int.emod_emod]

/-- Sharpness Counterexample 1: Naive mathematical sign `s_math = 0` at `X = 0, d = -1` causes `+2^(w+1)` error ∀ w ≥ 1! -/
theorem booth_neg_zero_ghost_carry_bug {w : Nat} (_hw : 1 ≤ w) :
    let (Q, h, s_sil) := radix4PP w 0 5
    (Q : Int) + (h : Int) - (s_sil : Int) * p2 (w + 1) = 0 ∧
    (Q : Int) + (h : Int) - (0 : Int) * p2 (w + 1) = p2 (w + 1) := by
  have hpos : 1 ≤ 2 ^ (w + 1) := pow2_pos (w + 1)
  have hzero_div : 0 / 2 ^ (w - 1) = 0 := Nat.zero_div _
  dsimp only [radix4PP, p2]
  simp only [Nat.zero_mod, hzero_div, Nat.zero_mul, Nat.add_zero, Nat.sub_zero]
  omega

/-- Sharpness Counterexample 2: `X = -2^(w-1), d = -2` gives `+2^w`, overflowing `(w+1)`-bit signed range ∀ w ≥ 1! -/
theorem booth_width_w_overflow_bug {w : Nat} (hw : 1 ≤ w) :
    (-2 : Int) * signedVal w (2 ^ (w - 1)) = p2 w := by
  have h2w : 2 * 2 ^ (w - 1) = 2 ^ w := pow2_pred_double hw
  rw [signedVal_half hw]
  unfold p2; omega


/-! ============================================================================
    SECTION 5: CROWN JEWEL — End-to-End Pure-Silicon Shift-and-Add Booth-CSA
               Multipliers at Exact Minimum Register Width W = w + k
    ============================================================================ -/

private theorem int_mul_bounds {x y A B : Int}
    (hx1 : -A ≤ x) (hx2 : x ≤ A) (hy1 : -B ≤ y) (hy2 : y ≤ B) :
    -(A * B) ≤ x * y ∧ x * y ≤ A * B := by
  by_cases hx : 0 ≤ x
  · have h1 : x * (-B) ≤ x * y := Int.mul_le_mul_of_nonneg_left hy1 hx
    have h2 : x * y ≤ x * B := Int.mul_le_mul_of_nonneg_left hy2 hx
    have hB : 0 ≤ B := by omega
    have h3 : x * B ≤ A * B := Int.mul_le_mul_of_nonneg_right hx2 hB
    grind
  · have hx' : 0 ≤ -x := by omega
    have h1 : (-x) * (-B) ≤ (-x) * y := Int.mul_le_mul_of_nonneg_left hy1 hx'
    have h2 : (-x) * y ≤ (-x) * B := Int.mul_le_mul_of_nonneg_left hy2 hx'
    have hB : 0 ≤ B := by omega
    have h3 : (-x) * B ≤ A * B := Int.mul_le_mul_of_nonneg_right (by omega) hB
    grind

/--
  THEOREM 9 (Coupled Booth-Overlap Accumulator Range Bound, ∀ k ≥ 1, ∀ w ≥ 1, ∀ j ≥ 0):
  Because the Booth overlap bit couples `A_j` and `d_j`, the pre-shift accumulator `A_j'`
  satisfies `-2^(w+k-2) ≤ A_j' ≤ +2^(w+k-2)` — fitting INSIDE the `g = 2` Zero-Carry-Top
  normalizer range `[-2^(W-2), 2^(W-1) - 1]` at the EXACT minimum width `W = w + k`!
-/
theorem booth_acc_prime_bounds {k w j : Nat} (hk : 1 ≤ k) (hw : 1 ≤ w) (x_u y_u : Nat) :
    let V : Int := (signedVal w x_u * signedVal (k * (j + 1)) y_u) / p2 (k * j);
    (-p2 (w + k - 2)) ≤ V ∧ V ≤ p2 (w + k - 2) := by
  have hkj1 : 1 ≤ k * (j + 1) := Nat.mul_pos hk (Nat.succ_pos j)
  have hx := signedVal_bounds hw x_u
  have hy := signedVal_bounds hkj1 y_u
  have hmul := int_mul_bounds hx.1 (by omega) hy.1 (by omega)
  have hexp : (w - 1) + (k * (j + 1) - 1) = (w + k - 2) + k * j := by
    have : k * (j + 1) = k * j + k := by rw [Nat.mul_add, Nat.mul_one]
    omega
  have hpow : p2 (w - 1) * p2 (k * (j + 1) - 1) = p2 (w + k - 2) * p2 (k * j) := by
    rw [p2_add, p2_add, hexp]
  rw [hpow] at hmul
  have hd_pos := p2_pos (k * j)
  have hdiv_lo : -p2 (w + k - 2) = (-(p2 (w + k - 2) * p2 (k * j))) / p2 (k * j) := by
    rw [← Int.neg_mul, Int.mul_ediv_cancel _ (by omega)]
  have hdiv_hi : p2 (w + k - 2) = (p2 (w + k - 2) * p2 (k * j)) / p2 (k * j) := by
    rw [Int.mul_ediv_cancel _ (by omega)]
  dsimp only
  constructor
  · rw [hdiv_lo]; exact Int.ediv_le_ediv hd_pos hmul.1
  · rw [hdiv_hi]; exact Int.ediv_le_ediv hd_pos hmul.2

/-- Sharpness / Tightness: BOTH `+2^(w+k-2)` and `-2^(w+k-2)` are attained by `A_j'`! -/
theorem booth_acc_endpoints_tight {k w : Nat} (hk : 1 ≤ k) (hw : 1 ≤ w) :
    (signedVal w (2 ^ (w - 1)) * signedVal (k * 1) (2 ^ (k - 1))) / p2 (k * 0) = p2 (w + k - 2) ∧
    (signedVal w (2 ^ (w - 1)) * signedVal (k * (w + 1)) (2 ^ (k * (w + 1) - 1) - 1)) /
      p2 (k * w) = -p2 (w + k - 2) := by
  have hsx : signedVal w (2 ^ (w - 1)) = -p2 (w - 1) := signedVal_half hw
  constructor
  · have hsy : signedVal (k * 1) (2 ^ (k - 1)) = -p2 (k - 1) := by
      rw [Nat.mul_one]; exact signedVal_half hk
    rw [hsx, hsy, Nat.mul_zero]
    have hp0 : p2 0 = 1 := rfl
    rw [hp0, Int.ediv_one, Int.neg_mul_neg, p2_add]
    congr 1; omega
  · have hkw1 : 1 ≤ k * (w + 1) := Nat.mul_pos hk (Nat.succ_pos w)
    have hpos_y : 1 ≤ 2 ^ (k * (w + 1) - 1) := pow2_pos _
    have hsy : signedVal (k * (w + 1)) (2 ^ (k * (w + 1) - 1) - 1) =
        ((2 ^ (k * (w + 1) - 1) - 1 : Nat) : Int) :=
      signedVal_of_lt_half _ (by omega) hkw1
    rw [hsx, hsy]
    have hcast : ((2 ^ (k * (w + 1) - 1) - 1 : Nat) : Int) = p2 (k * (w + 1) - 1) - 1 := by
      unfold p2; omega
    rw [hcast]
    have hexp : (w - 1) + (k * (w + 1) - 1) = (w + k - 2) + k * w := by
      have : k * (w + 1) = k * w + k := by rw [Nat.mul_add, Nat.mul_one]
      omega
    have hpow : p2 (w - 1) * p2 (k * (w + 1) - 1) = p2 (w + k - 2) * p2 (k * w) := by
      rw [p2_add, p2_add, hexp]
    have hprod : -p2 (w - 1) * (p2 (k * (w + 1) - 1) - 1) =
        (-p2 (w + k - 2)) * p2 (k * w) + p2 (w - 1) := by grind
    have hkw_pos := p2_pos (k * w)
    rw [hprod, Int.mul_add_ediv_right _ _ (by omega)]
    have hle_exp : w - 1 < k * w := by
      have : 1 * w ≤ k * w := Nat.mul_le_mul_right w hk
      omega
    have hlt : p2 (w - 1) < p2 (k * w) := by
      unfold p2; have := Nat.pow_lt_pow_right (by decide : 1 < 2) hle_exp; omega
    have hpos_wm1 := p2_pos (w - 1)
    rw [Int.ediv_eq_zero_of_lt (by omega) hlt, Int.add_zero]

/-! ### 100% Pure-Silicon Bitwise Shift-and-Add Radix-4 Booth-CSA Multiplier (`W = w + 2`) -/

private theorem nat_mod_to_int_emod (a M : Nat) :
    ((a % M : Nat) : Int) = (a : Int) % (M : Int) :=
  (Int.natCast_emod a M).symm

private theorem radix4BoothCSARun_inv {w : Nat} (hw : 1 ≤ w) (x_u y_u j : Nat) :
    let W := w + 2
    let st := radix4BoothCSARun w x_u y_u j
    let A_j : Int :=
      if j = 0 then 0 else (signedVal w x_u * signedVal (2 * j) y_u) / p2 (2 * j)
    st.C % 2 = 0 ∧
    st.lowProd < 2 ^ (2 * j) ∧
    (((st.S + st.C) % 2 ^ W : Nat) : Int) = A_j % p2 W ∧
    A_j * p2 (2 * j) + (st.lowProd : Int) =
      (if j = 0 then 0 else signedVal w x_u * signedVal (2 * j) y_u) := by
  induction j with
  | zero =>
    simp [radix4BoothCSARun]
  | succ n ih =>
    rcases ih with ⟨hC_even, hlow_lt, hSC_mod, hcons⟩
    let W := w + 2
    have hW2 : 2 ≤ W := by omega
    have hW1 : 1 ≤ W := by omega
    let st := radix4BoothCSARun w x_u y_u n
    let A_n : Int :=
      if n = 0 then 0 else (signedVal w x_u * signedVal (2 * n) y_u) / p2 (2 * n)
    let win3 := win3FromBits (boothPrevBit 2 y_u n) (radixDigit 2 y_u n)
    let pp := radix4PP w x_u win3
    let Q := pp.1
    let h := pp.2.1
    let s := pp.2.2
    have hpp := radix4PP_exact hw x_u (boothPrevBit 2 y_u n) (radixDigit 2 y_u n)
    have hdig : radixDigit 2 y_u n % 4 = radixDigit 2 y_u n :=
      Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))
    have hpp_eq : (Q : Int) + (h : Int) - (s : Int) * p2 (w + 1) =
        boothDigit 2 y_u n * signedVal w x_u := by
      have h1 := hpp.1; simp only [hdig] at h1; exact h1
    have hh_le : h ≤ 1 := hpp.2.2.1
    have hbooth_step : signedVal (2 * (n + 1)) y_u =
        (if n = 0 then 0 else signedVal (2 * n) y_u) +
        boothDigit 2 y_u n * p2 (2 * n) := by
      have h1 := booth_recoding_exact (k := 2) (m := n + 1) (by decide) (Nat.succ_pos n) y_u
      rw [← h1]
      simp only [radixSum]
      have hpow : ((4 ^ n : Nat) : Int) = p2 (2 * n) := by
        unfold p2; exact congrArg Int.ofNat (Nat.pow_mul 2 2 n).symm
      rw [hpow]
      cases n with
      | zero => simp [radixSum]
      | succ n' =>
        have h0 := booth_recoding_exact (k := 2) (m := n' + 1) (by decide) (Nat.succ_pos n') y_u
        simp [h0]
    let A_prime : Int := A_n + boothDigit 2 y_u n * signedVal w x_u
    have hAprime_cons : A_prime * p2 (2 * n) + (st.lowProd : Int) =
        signedVal w x_u * signedVal (2 * (n + 1)) y_u := by
      rw [hbooth_step]; grind
    have hAprime_div : A_prime =
        (signedVal w x_u * signedVal (2 * (n + 1)) y_u) / p2 (2 * n) := by
      have hpos := p2_pos (2 * n)
      have hltI : (st.lowProd : Int) < p2 (2 * n) := Int.ofNat_lt.mpr hlow_lt
      rw [← hAprime_cons, Int.mul_add_ediv_right _ _ (by omega),
          Int.ediv_eq_zero_of_lt (by omega) hltI, Int.add_zero]
    have hbounds := booth_acc_prime_bounds (k := 2) (w := w) (j := n) (by decide) hw x_u y_u
    rw [← hAprime_div] at hbounds
    have h2wp1 : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
    have hposw : 0 < 2 ^ w := pow2_pos w
    have hAprime_lo : -p2 (W - 1) + p2 (W - 2) ≤ A_prime := by
      have h1 : W - 1 = w + 1 := by omega
      have h2 : W - 2 = w := by omega
      have h3 : w + 2 - 2 = w := by omega
      rw [h1, h2]; rw [h3] at hbounds; unfold p2 at *; omega
    have hAprime_hi : A_prime < p2 (W - 1) := by
      have h1 : W - 1 = w + 1 := by omega
      have h3 : w + 2 - 2 = w := by omega
      rw [h1]; rw [h3] at hbounds; unfold p2 at *; omega
    let P_raw := s * 2 ^ (w + 1) + Q
    let C_inj := st.C ||| h
    have hC_inj : C_inj = st.C + h := or_bit0_eq_add_of_even hC_even hh_le
    let S1 := csaSum W st.S C_inj P_raw
    let C1 := csaCarry W st.S C_inj P_raw
    have hS1C1_mod : (((S1 + C1) % 2 ^ W : Nat) : Int) = A_prime % p2 W := by
      dsimp only [S1, C1]
      rw [csa3to2_exact_mod, hC_inj]
      have h2W : p2 W = 2 * p2 (w + 1) := by
        have : W = (w + 1) + 1 := by omega
        rw [this]; unfold p2; rw [Nat.pow_succ, Nat.mul_comm, Int.natCast_mul]; rfl
      have hP_mod : ((P_raw + h : Nat) : Int) % p2 W =
          (boothDigit 2 y_u n * signedVal w x_u) % p2 W := by
        rw [← hpp_eq]
        have hdiff : ((P_raw + h : Nat) : Int) =
            ((Q : Int) + (h : Int) - (s : Int) * p2 (w + 1)) + (s : Int) * p2 W := by
          dsimp only [P_raw]; unfold p2 at h2W ⊢
          rw [Int.natCast_add, Int.natCast_add, Int.natCast_mul]; grind
        rw [hdiff, Int.add_mul_emod_self_right]
      have hrearr : st.S + (st.C + h) + P_raw = (st.S + st.C) + (P_raw + h) := by omega
      rw [hrearr, nat_mod_to_int_emod, Int.natCast_add, Int.add_emod,
          ← nat_mod_to_int_emod (st.S + st.C) (2 ^ W), hSC_mod, hP_mod, ← Int.add_emod]
    have hnorm := zeroCarryTop_exact (g := 2) (W := W) (by decide) hW2 S1 C1
        hAprime_lo hAprime_hi hS1C1_mod
    let S2 := (applyTopGuard 2 W (zeroCarryTopNorm 2) S1 C1).1
    let C2 := (applyTopGuard 2 W (zeroCarryTopNorm 2) S1 C1).2
    have hC2_lt_half : C2 < 2 ^ (W - 1) := by
      have : 2 ^ (W - 2) < 2 ^ (W - 1) := Nat.pow_lt_pow_right (by decide) (by omega)
      have := hnorm.2; omega
    have hshift := csa_arith_rshift_exact (W := W) (k := 2) hW1 (by decide) hW2 hnorm.1 hC2_lt_half
    let rS := S2 % 4
    let rC := C2 % 4
    let p_n := (rS + rC) % 4
    let c_lsb := (rS + rC) / 4
    let qS := ((signedVal W S2 / 4) % p2 W).toNat
    let qC := C2 / 4
    have hAn1_eq : (signedVal w x_u * signedVal (2 * (n + 1)) y_u) / p2 (2 * (n + 1)) =
        A_prime / 4 := by
      have hpow : p2 (2 * (n + 1)) = p2 (2 * n) * 4 := by
        have : 2 * (n + 1) = 2 * n + 2 := by omega
        rw [this, ← p2_add]; rfl
      have hpos := p2_pos (2 * n)
      rw [hpow, ← Int.ediv_ediv_of_nonneg (by omega), ← hAprime_div]
    dsimp only [radix4BoothCSARun, radix4BoothCSAStep]
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    refine ⟨csaCarry_even hW1 _ _ _, ?_, ?_, ?_⟩
    · show st.lowProd + p_n * 2 ^ (2 * n) < 2 ^ (2 * (n + 1))
      have hp_lt : p_n < 4 := Nat.mod_lt _ (by decide)
      have hpow : 2 ^ (2 * (n + 1)) = 4 * 2 ^ (2 * n) := by
        rw [Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_comm]
      rw [hpow]
      have hmul : (p_n + 1) * 2 ^ (2 * n) ≤ 4 * 2 ^ (2 * n) := Nat.mul_le_mul_right _ hp_lt
      rw [Nat.add_mul, Nat.one_mul] at hmul
      have hlow_lt' : st.lowProd < 2 ^ (2 * n) := hlow_lt
      omega
    · show (((csaSum W qS qC c_lsb + csaCarry W qS qC c_lsb) % 2 ^ W : Nat) : Int) =
          (signedVal w x_u * signedVal (2 * (n + 1)) y_u) / p2 (2 * (n + 1)) % p2 W
      rw [csa3to2_exact_mod, hAn1_eq]
      have hs1 : (signedVal W S2 / 4) + ((qC : Int) + (c_lsb : Int)) = A_prime / 4 := by
        have h := hshift.1
        change (signedVal W S2 / (4 : Int)) + (qC : Int) + (c_lsb : Int) = A_prime / (4 : Int) at h
        omega
      rw [← hs1, nat_mod_to_int_emod]
      have hqS_cast : (qS : Int) = (signedVal W S2 / 4) % p2 W :=
        Int.toNat_of_nonneg (Int.emod_nonneg _ (by have := p2_pos W; omega))
      rw [Int.natCast_add, Int.natCast_add, hqS_cast, Int.add_assoc, Int.add_emod, Int.emod_emod, ← Int.add_emod]
    · show ((signedVal w x_u * signedVal (2 * (n + 1)) y_u) / p2 (2 * (n + 1))) * p2 (2 * (n + 1)) +
          ((st.lowProd + p_n * 2 ^ (2 * n) : Nat) : Int) =
          signedVal w x_u * signedVal (2 * (n + 1)) y_u
      rw [hAn1_eq]
      have hs2 : (p_n : Int) = A_prime % 4 := hshift.2
      have hdiv_mod : 4 * (A_prime / 4) + (p_n : Int) = A_prime := by
        rw [hs2]; exact int_mul_ediv_add_emod A_prime 4
      have hpow : p2 (2 * (n + 1)) = 4 * p2 (2 * n) := by
        have : 2 * (n + 1) = 2 + 2 * n := by omega
        rw [this, ← p2_add]; rfl
      rw [hpow, Int.natCast_add, Int.natCast_mul]
      unfold p2 at hAprime_cons ⊢
      grind

theorem shiftAddRadix4BoothCSASilicon_exact {w m : Nat} (hw : 1 ≤ w) (hm : 1 ≤ m) (x_u y_u : Nat) :
    shiftAddRadix4BoothCSASilicon w m x_u y_u =
      signedVal w x_u * signedVal (2 * m) y_u := by
  have hinv := radix4BoothCSARun_inv hw x_u y_u m
  have hm0 : m ≠ 0 := by omega
  simp only [hm0, ↓reduceIte] at hinv
  rcases hinv with ⟨_, _, hSC_mod, hcons⟩
  let W := w + 2
  have hW2 : 2 ≤ W := by omega
  let A_m : Int := (signedVal w x_u * signedVal (2 * m) y_u) / p2 (2 * m)
  have hm_pred : m = (m - 1) + 1 := by omega
  have hb := booth_acc_prime_bounds (k := 2) (w := w) (j := m - 1) (by decide) hw x_u y_u
  have hAm_eq : A_m =
      ((signedVal w x_u * signedVal (2 * ((m - 1) + 1)) y_u) / p2 (2 * (m - 1))) / 4 := by
    have hpow : p2 (2 * ((m - 1) + 1)) = p2 (2 * (m - 1)) * 4 := by
      have : 2 * ((m - 1) + 1) = 2 * (m - 1) + 2 := by omega
      rw [this, ← p2_add]; rfl
    have hpos := p2_pos (2 * (m - 1))
    calc A_m
        = (signedVal w x_u * signedVal (2 * ((m - 1) + 1)) y_u) / p2 (2 * ((m - 1) + 1)) := by
            dsimp only [A_m]; rw [← hm_pred]
      _ = (signedVal w x_u * signedVal (2 * ((m - 1) + 1)) y_u) / (p2 (2 * (m - 1)) * 4) := by
            rw [hpow]
      _ = ((signedVal w x_u * signedVal (2 * ((m - 1) + 1)) y_u) / p2 (2 * (m - 1))) / 4 := by
            rw [← Int.ediv_ediv_of_nonneg (by omega)]
  have h2wp1 : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
  have hposw : 0 < 2 ^ w := pow2_pos w
  have hAm_lo : -p2 (W - 1) + p2 (W - 2) ≤ A_m := by
    have h1 : W - 1 = w + 1 := by omega
    have h2 : W - 2 = w := by omega
    have h3 : w + 2 - 2 = w := by omega
    rw [h1, h2, hAm_eq]; rw [h3] at hb; unfold p2 at *; omega
  have hAm_hi : A_m < p2 (W - 1) := by
    have h1 : W - 1 = w + 1 := by omega
    have h3 : w + 2 - 2 = w := by omega
    rw [h1, hAm_eq]; rw [h3] at hb; unfold p2 at *; omega
  have hfin := zeroCarryTop_exact (g := 2) (W := W) (by decide) hW2
      (radix4BoothCSARun w x_u y_u m).S (radix4BoothCSARun w x_u y_u m).C
      hAm_lo hAm_hi hSC_mod
  have hfin1 :
      signedVal W (applyTopGuard 2 W (zeroCarryTopNorm 2)
        (radix4BoothCSARun w x_u y_u m).S (radix4BoothCSARun w x_u y_u m).C).1 +
      signedVal W (applyTopGuard 2 W (zeroCarryTopNorm 2)
        (radix4BoothCSARun w x_u y_u m).S (radix4BoothCSARun w x_u y_u m).C).2 = A_m :=
    hfin.1
  unfold shiftAddRadix4BoothCSASilicon
  dsimp only
  change (signedVal W (applyTopGuard 2 W (zeroCarryTopNorm 2)
      (radix4BoothCSARun w x_u y_u m).S (radix4BoothCSARun w x_u y_u m).C).1 +
    signedVal W (applyTopGuard 2 W (zeroCarryTopNorm 2)
      (radix4BoothCSARun w x_u y_u m).S (radix4BoothCSARun w x_u y_u m).C).2) *
    p2 (2 * m) + ((radix4BoothCSARun w x_u y_u m).lowProd : Int) = _
  rw [hfin1]
  exact hcons

/-! ### General Radix-`2^k` Shift-and-Add Booth-CSA Multiplier (`W = w + k`, ∀ k ≥ 1, w ≥ 1, m ≥ 1) -/

private theorem radix2kBoothCSARun_inv {k w : Nat} (hk : 1 ≤ k) (hw : 1 ≤ w) (x_u y_u j : Nat) :
    let W := w + k
    let st := radix2kBoothCSARun k w x_u y_u j
    let A_j : Int :=
      if j = 0 then 0 else (signedVal w x_u * signedVal (k * j) y_u) / p2 (k * j)
    st.lowProd < 2 ^ (k * j) ∧
    (((st.S + st.C) % 2 ^ W : Nat) : Int) = A_j % p2 W ∧
    A_j * p2 (k * j) + (st.lowProd : Int) =
      (if j = 0 then 0 else signedVal w x_u * signedVal (k * j) y_u) := by
  induction j with
  | zero =>
    simp [radix2kBoothCSARun]
  | succ n ih =>
    rcases ih with ⟨hlow_lt, hSC_mod, hcons⟩
    let W := w + k
    have hW2 : 2 ≤ W := by omega
    have hW1 : 1 ≤ W := by omega
    have hkW : k ≤ W := by omega
    let st := radix2kBoothCSARun k w x_u y_u n
    let A_n : Int :=
      if n = 0 then 0 else (signedVal w x_u * signedVal (k * n) y_u) / p2 (k * n)
    have hbooth_step : signedVal (k * (n + 1)) y_u =
        (if n = 0 then 0 else signedVal (k * n) y_u) +
        boothDigit k y_u n * p2 (k * n) := by
      have h1 := booth_recoding_exact (k := k) (m := n + 1) hk (Nat.succ_pos n) y_u
      rw [← h1]
      simp only [radixSum]
      have hpow : (((2 ^ k) ^ n : Nat) : Int) = p2 (k * n) := by
        unfold p2; exact congrArg Int.ofNat (Nat.pow_mul 2 k n).symm
      rw [hpow]
      cases n with
      | zero => simp [radixSum]
      | succ n' =>
        have h0 := booth_recoding_exact (k := k) (m := n' + 1) hk (Nat.succ_pos n') y_u
        simp [h0]
    let A_prime : Int := A_n + boothDigit k y_u n * signedVal w x_u
    have hAprime_cons : A_prime * p2 (k * n) + (st.lowProd : Int) =
        signedVal w x_u * signedVal (k * (n + 1)) y_u := by
      rw [hbooth_step]; grind
    have hAprime_div : A_prime =
        (signedVal w x_u * signedVal (k * (n + 1)) y_u) / p2 (k * n) := by
      have hpos := p2_pos (k * n)
      have hltI : (st.lowProd : Int) < p2 (k * n) := Int.ofNat_lt.mpr hlow_lt
      rw [← hAprime_cons, Int.mul_add_ediv_right _ _ (by omega),
          Int.ediv_eq_zero_of_lt (by omega) hltI, Int.add_zero]
    have hbounds := booth_acc_prime_bounds (k := k) (w := w) (j := n) hk hw x_u y_u
    rw [← hAprime_div] at hbounds
    have h2Wm1 : 2 ^ (W - 1) = 2 * 2 ^ (W - 2) := (pow2_pred_double (by omega)).symm
    have hAprime_lo : -p2 (W - 1) + p2 (W - 2) ≤ A_prime := by
      have : W - 2 = w + k - 2 := by omega
      rw [this] at h2Wm1 ⊢; unfold p2 at *; omega
    have hAprime_hi : A_prime < p2 (W - 1) := by
      have : W - 2 = w + k - 2 := by omega
      have hpos : 0 < 2 ^ (w + k - 2) := pow2_pos _
      rw [this] at h2Wm1; unfold p2 at *; omega
    let pp_u := ((boothDigit k y_u n * signedVal w x_u) % p2 W).toNat
    let S1 := csaSum W st.S st.C pp_u
    let C1 := csaCarry W st.S st.C pp_u
    have hS1C1_mod : (((S1 + C1) % 2 ^ W : Nat) : Int) = A_prime % p2 W := by
      dsimp only [S1, C1]
      rw [csa3to2_exact_mod, nat_mod_to_int_emod]
      have hpp_cast : (pp_u : Int) = (boothDigit k y_u n * signedVal w x_u) % p2 W :=
        Int.toNat_of_nonneg (Int.emod_nonneg _ (by have := p2_pos W; omega))
      rw [Int.natCast_add, Int.add_emod, ← nat_mod_to_int_emod (st.S + st.C) (2 ^ W),
          hSC_mod, hpp_cast, Int.emod_emod, ← Int.add_emod]
    have hnorm := zeroCarryTop_exact (g := 2) (W := W) (by decide) hW2 S1 C1
        hAprime_lo hAprime_hi hS1C1_mod
    let S2 := (applyTopGuard 2 W (zeroCarryTopNorm 2) S1 C1).1
    let C2 := (applyTopGuard 2 W (zeroCarryTopNorm 2) S1 C1).2
    have hC2_lt_half : C2 < 2 ^ (W - 1) := by
      have : 2 ^ (W - 2) < 2 ^ (W - 1) := Nat.pow_lt_pow_right (by decide) (by omega)
      have := hnorm.2; omega
    have hshift := csa_arith_rshift_exact hW1 hk hkW hnorm.1 hC2_lt_half
    let rS := S2 % 2 ^ k
    let rC := C2 % 2 ^ k
    let p_n := (rS + rC) % 2 ^ k
    let c_lsb := (rS + rC) / 2 ^ k
    let qS := ((signedVal W S2 / p2 k) % p2 W).toNat
    let qC := C2 / 2 ^ k
    have hAn1_eq : (signedVal w x_u * signedVal (k * (n + 1)) y_u) / p2 (k * (n + 1)) =
        A_prime / p2 k := by
      have hpow : p2 (k * (n + 1)) = p2 (k * n) * p2 k := by
        rw [p2_add, Nat.mul_add, Nat.mul_one]
      have hpos := p2_pos (k * n)
      rw [hpow, ← Int.ediv_ediv_of_nonneg (by omega), ← hAprime_div]
    dsimp only [radix2kBoothCSARun, radix2kBoothCSAStep]
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    refine ⟨?_, ?_, ?_⟩
    · show st.lowProd + p_n * 2 ^ (k * n) < 2 ^ (k * (n + 1))
      have hp_lt : p_n < 2 ^ k := Nat.mod_lt _ (pow2_pos k)
      have hpow : 2 ^ (k * (n + 1)) = 2 ^ k * 2 ^ (k * n) := by
        rw [Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_comm]
      rw [hpow]
      have hmul : (p_n + 1) * 2 ^ (k * n) ≤ 2 ^ k * 2 ^ (k * n) := Nat.mul_le_mul_right _ hp_lt
      rw [Nat.add_mul, Nat.one_mul] at hmul
      have hlow_lt' : st.lowProd < 2 ^ (k * n) := hlow_lt
      omega
    · show (((csaSum W qS qC c_lsb + csaCarry W qS qC c_lsb) % 2 ^ W : Nat) : Int) =
          (signedVal w x_u * signedVal (k * (n + 1)) y_u) / p2 (k * (n + 1)) % p2 W
      rw [csa3to2_exact_mod, hAn1_eq]
      have hs1 : (signedVal W S2 / p2 k) + (qC : Int) + (c_lsb : Int) = A_prime / p2 k := hshift.1
      rw [← hs1, nat_mod_to_int_emod]
      have hqS_cast : (qS : Int) = (signedVal W S2 / p2 k) % p2 W :=
        Int.toNat_of_nonneg (Int.emod_nonneg _ (by have := p2_pos W; omega))
      rw [Int.natCast_add, Int.natCast_add, hqS_cast, Int.add_assoc, Int.add_assoc,
          Int.add_emod, Int.emod_emod, ← Int.add_emod]
    · show ((signedVal w x_u * signedVal (k * (n + 1)) y_u) / p2 (k * (n + 1))) * p2 (k * (n + 1)) +
          ((st.lowProd + p_n * 2 ^ (k * n) : Nat) : Int) =
          signedVal w x_u * signedVal (k * (n + 1)) y_u
      rw [hAn1_eq]
      have hs2 : (p_n : Int) = A_prime % p2 k := hshift.2
      have hdiv_mod : p2 k * (A_prime / p2 k) + (p_n : Int) = A_prime := by
        rw [hs2]; exact int_mul_ediv_add_emod A_prime (p2 k)
      have hpow : p2 (k * (n + 1)) = p2 k * p2 (k * n) := by
        rw [p2_add, Nat.mul_add, Nat.mul_one, Nat.add_comm]
      rw [hpow, Int.natCast_add, Int.natCast_mul]
      unfold p2 at hAprime_cons hdiv_mod ⊢
      grind

/--
  THEOREM 11 (Universal Radix-`2^k` Shift-and-Add Booth-CSA Multiplier Theorem,
  ∀ k ≥ 1, ∀ w ≥ 1, ∀ m ≥ 1):
  Works at the exact minimum register width `W = w + k` with `g = 2` Zero-Carry-Top
  normalization for EVERY radix `2^k` (`k ≥ 1`), EVERY width `w ≥ 1`, EVERY depth `m ≥ 1`!
-/
theorem shiftAddRadix2kBoothCSA_exact {k w m : Nat} (hk : 1 ≤ k) (hw : 1 ≤ w) (hm : 1 ≤ m)
    (x_u y_u : Nat) :
    shiftAddRadix2kBoothCSA k w m x_u y_u =
      signedVal w x_u * signedVal (k * m) y_u := by
  have hinv := radix2kBoothCSARun_inv hk hw x_u y_u m
  have hm0 : m ≠ 0 := by omega
  simp only [hm0, ↓reduceIte] at hinv
  rcases hinv with ⟨_, hSC_mod, hcons⟩
  let W := w + k
  have hW2 : 2 ≤ W := by omega
  let A_m : Int := (signedVal w x_u * signedVal (k * m) y_u) / p2 (k * m)
  have hm_pred : m = (m - 1) + 1 := by omega
  have hb := booth_acc_prime_bounds (k := k) (w := w) (j := m - 1) hk hw x_u y_u
  have hAm_eq : A_m =
      ((signedVal w x_u * signedVal (k * ((m - 1) + 1)) y_u) / p2 (k * (m - 1))) / p2 k := by
    have hpow : p2 (k * ((m - 1) + 1)) = p2 (k * (m - 1)) * p2 k := by
      rw [p2_add, Nat.mul_add, Nat.mul_one]
    have hpos := p2_pos (k * (m - 1))
    calc A_m
        = (signedVal w x_u * signedVal (k * ((m - 1) + 1)) y_u) / p2 (k * ((m - 1) + 1)) := by
            dsimp only [A_m]; rw [← hm_pred]
      _ = (signedVal w x_u * signedVal (k * ((m - 1) + 1)) y_u) / (p2 (k * (m - 1)) * p2 k) := by
            rw [hpow]
      _ = ((signedVal w x_u * signedVal (k * ((m - 1) + 1)) y_u) / p2 (k * (m - 1))) / p2 k := by
            rw [← Int.ediv_ediv_of_nonneg (by omega)]
  have h2k_ge2 : (2 : Int) ≤ p2 k := by
    unfold p2; have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk; omega
  have h2Wm1 : 2 ^ (W - 1) = 2 * 2 ^ (W - 2) := (pow2_pred_double (by omega)).symm
  have hpos_m := p2_pos (w + k - 2)
  have hAm_bounds : -p2 (w + k - 2) ≤ A_m ∧ A_m ≤ p2 (w + k - 2) := by
    rw [hAm_eq]
    let Z := (signedVal w x_u * signedVal (k * ((m - 1) + 1)) y_u) / p2 (k * (m - 1))
    have h1 : p2 (w + k - 2) * 1 ≤ p2 (w + k - 2) * p2 k :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    have hZ1 : -p2 (w + k - 2) * p2 k ≤ Z := by grind
    have hZ2 : Z ≤ p2 (w + k - 2) * p2 k := by grind
    have hd_pos := p2_pos k
    constructor
    · have : -p2 (w + k - 2) = (-p2 (w + k - 2) * p2 k) / p2 k := by
        rw [Int.mul_ediv_cancel _ (by omega)]
      rw [this]; exact Int.ediv_le_ediv hd_pos hZ1
    · have : p2 (w + k - 2) = (p2 (w + k - 2) * p2 k) / p2 k := by
        rw [Int.mul_ediv_cancel _ (by omega)]
      rw [this]; exact Int.ediv_le_ediv hd_pos hZ2
  have hAm_lo : -p2 (W - 1) + p2 (W - 2) ≤ A_m := by
    have : W - 2 = w + k - 2 := by omega
    rw [this] at h2Wm1 ⊢; unfold p2 at *; omega
  have hAm_hi : A_m < p2 (W - 1) := by
    have : W - 2 = w + k - 2 := by omega
    rw [this] at h2Wm1; unfold p2 at *; omega
  have hfin := zeroCarryTop_exact (g := 2) (W := W) (by decide) hW2
      (radix2kBoothCSARun k w x_u y_u m).S (radix2kBoothCSARun k w x_u y_u m).C
      hAm_lo hAm_hi hSC_mod
  have hfin1 :
      signedVal W (applyTopGuard 2 W (zeroCarryTopNorm 2)
        (radix2kBoothCSARun k w x_u y_u m).S (radix2kBoothCSARun k w x_u y_u m).C).1 +
      signedVal W (applyTopGuard 2 W (zeroCarryTopNorm 2)
        (radix2kBoothCSARun k w x_u y_u m).S (radix2kBoothCSARun k w x_u y_u m).C).2 = A_m :=
    hfin.1
  unfold shiftAddRadix2kBoothCSA
  dsimp only
  change (signedVal W (applyTopGuard 2 W (zeroCarryTopNorm 2)
      (radix2kBoothCSARun k w x_u y_u m).S (radix2kBoothCSARun k w x_u y_u m).C).1 +
    signedVal W (applyTopGuard 2 W (zeroCarryTopNorm 2)
      (radix2kBoothCSARun k w x_u y_u m).S (radix2kBoothCSARun k w x_u y_u m).C).2) *
    p2 (k * m) + ((radix2kBoothCSARun k w x_u y_u m).lowProd : Int) = _
  rw [hfin1]
  exact hcons


/-! ============================================================================
    SECTION 6: Constructive Non-Vacuity Witnesses & Kernel Axiom Audit
    ============================================================================ -/

/-- Non-vacuity witness 1: Pure-silicon Radix-4 Shift-and-Add Booth-CSA on extremal
    8-bit × 8-bit (`w = 8, m = 4`, `X = -128, Y = -128`, product `+16384`). -/
example : shiftAddRadix4BoothCSASilicon 8 4 128 128 = 16384 := by decide

/-- Non-vacuity witness 2: Pure-silicon Radix-4 Shift-and-Add Booth-CSA on negative × positive
    16-bit × 8-bit (`w = 16, m = 4`, `X = -32768, Y = 127`, product `-4161536`). -/
example : shiftAddRadix4BoothCSASilicon 16 4 32768 127 = -4161536 := by decide

/-- Non-vacuity witness 3: Radix-4 Booth Tree + 2-State SEC exact identity on `w = 4, m = 3`
    (`X = -8, Y = -32`, product `+256`, bias `+2^11 = 2048`, tree sum `2304`). -/
example : boothTreeSum 4 3 8 32 = 256 + 2048 := by decide

/-- Non-vacuity witness 4: Radix-8 (`k = 3`) Shift-and-Add Booth-CSA on `w = 5, m = 3`
    (`X = -16, Y = -256`, product `+4096`). -/
example : shiftAddRadix2kBoothCSA 3 5 3 16 256 = 4096 := by decide

/-- Non-vacuity witness 5: Constructive instantiation of `FiniteGuardCert` (`g = 2`)
    unwrapping `W = 8` pair `(S = 192, C = 64)` representing `V = 0`! -/
example :
    let (S', C') := applyTopGuard 2 8 (guardCert_g2_zeroCarryTop.sound guardCert_g2_zeroCarryTop_ok).norm 192 64
    signedVal 8 S' + signedVal 8 C' = 0 ∧ C' < 64 := by decide

/-- Non-vacuity witness 6: Constructive inhabitation of both proof engines via kernel `decide`. -/
theorem witness_finite_cert_inhabited :
    Nonempty (RadixTransducer (Fin 2) (Fin 4) 4) ∧
    Nonempty (GuardNormalizerSpec 2) :=
  ⟨⟨(makeBoothCert 2).sound boothCert_r4_ok⟩,
   ⟨guardCert_g2_zeroCarryTop.sound guardCert_g2_zeroCarryTop_ok⟩⟩

theorem badBoothCert_r4_rejected : badBoothCert_r4.check = false := by decide

theorem badGuardCert_g2_rejected : badGuardCert_g2_cutArc.check = false := by decide

end SiliconBoothCSA
