/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AllReduceXorVdc.RatBasic

/-!
# Pillar 2: Cross-Rank Zero-Communication XOR-VDC Stochastic Rounding

Proves Headline Theorem 3 (`cross_rank_xor_vdc_bijection_and_exact_mse`):
1. `bitrev K` is an involution on `{0, ..., 2^K - 1}`, and for `K ≤ M` the top `K` bits of
   `u_r = u_0 ^^^ (bitrev_K(r) << (M - K))` form an explicit bijection on `Fin (2^K)`.
2. Exact stratified sum law: for every `f < 2^M` and every `u_0 < 2^M`,
   `∑_{r < 2^K} 1[u_r < f] = (f / 2^(M - K)) + 1[u_0 % 2^(M - K) < f % 2^(M - K)]`.
3. Exact zero bias across all `u_0 ∈ {0, ..., 2^M - 1}` for every `f < 2^M`.
4. Exact deterministic worst-case error `< 1` ULP for every `f < 2^M` and every `u_0 < 2^M`.
5. Exact discrete averaged MSE identities on an `M`-bit grid and exact continuous-limit MSE
   scaling laws (`TP^2/12 : TP/6 : TP/12 : 1/6`, giving `64x` over independent SR and `2048x`
   over RNE at `TP = 64`).
-/

namespace AllReduceXorVdc

/-! ### 1. `bitrev` Involution and Top-`K` Bit Decomposition -/

theorem bitrev_add_msb (k b y : Nat) (hb : b < 2) (hy : y < 2 ^ k) :
    bitrev (k + 1) (b * 2 ^ k + y) = 2 * bitrev k y + b := by
  induction k generalizing y with
  | zero =>
    have hy0 : y = 0 := by omega
    subst hy0
    simp only [Nat.pow_zero, Nat.mul_one, Nat.add_zero, bitrev]
    have hbm : b % 2 = b := by omega
    rw [hbm]; omega
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
    have hmul2 : b * 2 ^ (k + 1) = 2 * (b * 2 ^ k) := by rw [hpow, Nat.mul_left_comm]
    have hmod : (b * 2 ^ (k + 1) + y) % 2 = y % 2 := by rw [hmul2]; omega
    have hdiv : (b * 2 ^ (k + 1) + y) / 2 = b * 2 ^ k + y / 2 := by rw [hmul2]; omega
    have hy2 : y / 2 < 2 ^ k := by rw [hpow] at hy; omega
    change ((b * 2 ^ (k + 1) + y) % 2) * 2 ^ (k + 1) + bitrev (k + 1) ((b * 2 ^ (k + 1) + y) / 2) =
      2 * ((y % 2) * 2 ^ k + bitrev k (y / 2)) + b
    rw [hmod, hdiv, ih (y / 2) hy2, hpow]
    have hmul3 : y % 2 * (2 * 2 ^ k) = 2 * (y % 2 * 2 ^ k) := by rw [Nat.mul_left_comm]
    omega

theorem bitrev_involutive (k r : Nat) (hr : r < 2 ^ k) :
    bitrev k (bitrev k r) = r := by
  induction k generalizing r with
  | zero => simp [bitrev]; omega
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
    have hr2 : r / 2 < 2 ^ k := by rw [hpow] at hr; omega
    change bitrev (k + 1) ((r % 2) * 2 ^ k + bitrev k (r / 2)) = r
    rw [bitrev_add_msb k (r % 2) (bitrev k (r / 2)) (by omega) (bitrev_lt k (r / 2))]
    rw [ih (r / 2) hr2]
    omega

theorem testBit_mul_two_pow_add {s h l i : Nat} (hl : l < 2 ^ s) :
    (h * 2 ^ s + l).testBit i = if i < s then l.testBit i else h.testBit (i - s) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  by_cases hi : i < s
  · simp only [hi, ↓reduceIte]
    rw [Nat.testBit_eq_decide_div_mod_eq]
    have hpow : 2 ^ s = 2 ^ i * 2 ^ (s - i) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' (Nat.le_of_lt hi)]
    have heven : 2 ^ (s - i) % 2 = 0 := by
      have h1 : s - i = (s - i - 1) + 1 := by omega
      rw [h1, Nat.pow_succ]; omega
    have hrearr : h * 2 ^ s + l = 2 ^ i * (h * 2 ^ (s - i)) + l := by
      rw [hpow]
      have h1 : h * (2 ^ i * 2 ^ (s - i)) = 2 ^ i * (h * 2 ^ (s - i)) := by
        rw [Nat.mul_left_comm]
      rw [h1]
    rw [hrearr, Nat.mul_add_div (Nat.two_pow_pos i)]
    have hmod : (h * 2 ^ (s - i) + l / 2 ^ i) % 2 = (l / 2 ^ i) % 2 := by
      have hmul : (h * 2 ^ (s - i)) % 2 = 0 := by
        rw [Nat.mul_mod, heven]; simp
      omega
    rw [hmod]
  · simp only [hi, ↓reduceIte]
    rw [Nat.testBit_eq_decide_div_mod_eq]
    have hpow : 2 ^ i = 2 ^ s * 2 ^ (i - s) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
    have hdiv : (h * 2 ^ s + l) / 2 ^ i = h / 2 ^ (i - s) := by
      rw [hpow, ← Nat.div_div_eq_div_mul]
      have h1 : (h * 2 ^ s + l) / 2 ^ s = h := by
        rw [Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos s), Nat.div_eq_of_lt hl, Nat.add_zero]
      rw [h1]
    rw [hdiv]

theorem nat_xor_shift_decomp (s h0 l0 d : Nat) (hl0 : l0 < 2 ^ s) :
    (h0 * 2 ^ s + l0) ^^^ (d <<< s) = (h0 ^^^ d) * 2 ^ s + l0 := by
  rw [Nat.shiftLeft_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, testBit_mul_two_pow_add hl0, testBit_mul_two_pow_add hl0]
  have hd0 : (d * 2 ^ s + 0).testBit i = if i < s then (0 : Nat).testBit i else d.testBit (i - s) :=
    testBit_mul_two_pow_add (Nat.two_pow_pos s)
  rw [Nat.add_zero] at hd0
  rw [hd0]
  by_cases hi : i < s
  · simp [hi]
  · simp [hi, Nat.testBit_xor]

theorem xorVdcThreshold_decomp (M K r u0 : Nat) (_hKM : K ≤ M) :
    xorVdcThreshold M K r u0 =
    (topBits M K u0 ^^^ bitrev K r) * 2 ^ (M - K) + u0 % 2 ^ (M - K) := by
  unfold xorVdcThreshold topBits
  have hdecomp : u0 = (u0 / 2 ^ (M - K)) * 2 ^ (M - K) + u0 % 2 ^ (M - K) := by
    have h := Nat.div_add_mod u0 (2 ^ (M - K))
    rw [Nat.mul_comm] at h
    exact h.symm
  have hmod : u0 % 2 ^ (M - K) < 2 ^ (M - K) := Nat.mod_lt u0 (Nat.two_pow_pos (M - K))
  conv => lhs; rw [hdecomp]
  exact nat_xor_shift_decomp (M - K) (u0 / 2 ^ (M - K)) (u0 % 2 ^ (M - K)) (bitrev K r) hmod

theorem topBits_xorVdcThreshold (M K r u0 : Nat) (hKM : K ≤ M) :
    topBits M K (xorVdcThreshold M K r u0) = topBits M K u0 ^^^ bitrev K r := by
  rw [xorVdcThreshold_decomp M K r u0 hKM]
  unfold topBits
  have hmod : u0 % 2 ^ (M - K) < 2 ^ (M - K) := Nat.mod_lt u0 (Nat.two_pow_pos (M - K))
  rw [Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos (M - K)), Nat.div_eq_of_lt hmod, Nat.add_zero]

theorem topBits_lt (M K u0 : Nat) (hKM : K ≤ M) (hu0 : u0 < 2 ^ M) :
    topBits M K u0 < 2 ^ K := by
  unfold topBits
  have hpow : 2 ^ M = 2 ^ K * 2 ^ (M - K) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' hKM]
  rw [hpow] at hu0
  exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hu0)

/-- Explicit bijection of top `K` bits of `xorVdcThreshold M K r u0` on `Fin (2^K)`. -/
theorem topBits_xorVdc_bijection (M K u0 : Nat) (hKM : K ≤ M) (hu0 : u0 < 2 ^ M) :
    (∀ r : Fin (2 ^ K), topBits M K (xorVdcThreshold M K r.val u0) < 2 ^ K) ∧
    (∀ r₁ r₂ : Fin (2 ^ K),
      topBits M K (xorVdcThreshold M K r₁.val u0) = topBits M K (xorVdcThreshold M K r₂.val u0) →
      r₁ = r₂) ∧
    (∀ y : Fin (2 ^ K), ∃ r : Fin (2 ^ K),
      topBits M K (xorVdcThreshold M K r.val u0) = y.val) := by
  have hh0 : topBits M K u0 < 2 ^ K := topBits_lt M K u0 hKM hu0
  refine ⟨?_, ?_, ?_⟩
  · intro r
    rw [topBits_xorVdcThreshold M K r.val u0 hKM]
    exact Nat.xor_lt_two_pow hh0 (bitrev_lt K r.val)
  · intro r₁ r₂ heq
    rw [topBits_xorVdcThreshold M K r₁.val u0 hKM, topBits_xorVdcThreshold M K r₂.val u0 hKM] at heq
    have hbr : bitrev K r₁.val = bitrev K r₂.val := by
      have h1 := congrArg (topBits M K u0 ^^^ ·) heq
      rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at h1
      exact h1
    have hval : r₁.val = r₂.val := by
      have h2 := congrArg (bitrev K) hbr
      rw [bitrev_involutive K r₁.val r₁.isLt, bitrev_involutive K r₂.val r₂.isLt] at h2
      exact h2
    exact Fin.ext hval
  · intro y
    let rVal := bitrev K (topBits M K u0 ^^^ y.val)
    have hrLt : rVal < 2 ^ K := bitrev_lt K _
    refine ⟨⟨rVal, hrLt⟩, ?_⟩
    rw [topBits_xorVdcThreshold M K rVal u0 hKM]
    have hxy : topBits M K u0 ^^^ y.val < 2 ^ K := Nat.xor_lt_two_pow hh0 y.isLt
    rw [bitrev_involutive K (topBits M K u0 ^^^ y.val) hxy]
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

/-! ### 2. Exact Stratified Rank-Sum Formula, Zero Bias, and `< 1` ULP Bound -/

/-- Exact stratified rank-sum identity:
    `∑_{r < 2^K} 1[u_r < f] = (f / 2^(M - K)) + 1[u_0 % 2^(M - K) < f % 2^(M - K)]`. -/
theorem xorVdcRankSum_exact (M K f u0 : Nat) (hKM : K ≤ M) (hf : f < 2 ^ M) (hu0 : u0 < 2 ^ M) :
    xorVdcRankSum M K f u0 =
    ((f / 2 ^ (M - K) : Nat) : Rat) +
      if u0 % 2 ^ (M - K) < f % 2 ^ (M - K) then (1 : Rat) else 0 := by
  unfold xorVdcRankSum xorVdcRankBit
  let R := 2 ^ (M - K)
  have hR : 0 < R := Nat.two_pow_pos (M - K)
  let q := f / R
  let rem := f % R
  let h0 := topBits M K u0
  let l0 := u0 % R
  have hh0 : h0 < 2 ^ K := topBits_lt M K u0 hKM hu0
  have hq : q < 2 ^ K := topBits_lt M K f hKM hf
  have hl0 : l0 < R := Nat.mod_lt u0 hR
  have hrem : rem < R := Nat.mod_lt f hR
  have hf_eq : f = q * R + rem := by
    have h := Nat.div_add_mod f R; rw [Nat.mul_comm] at h; exact h.symm
  have hcongr1 : sumRange (2 ^ K) (fun r => if xorVdcThreshold M K r u0 < f then (1 : Rat) else 0) =
      sumRange (2 ^ K) (fun r => if (h0 ^^^ bitrev K r) * R + l0 < q * R + rem then (1 : Rat) else 0) := by
    apply sumRange_congr
    intro r _
    rw [xorVdcThreshold_decomp M K r u0 hKM, ← hf_eq]
  rw [hcongr1]
  rw [sumRange_bitrev K (fun x => if (h0 ^^^ x) * R + l0 < q * R + rem then (1 : Rat) else 0)]
  have hcomm : sumRange (2 ^ K) (fun x => if (h0 ^^^ x) * R + l0 < q * R + rem then (1 : Rat) else 0) =
      sumRange (2 ^ K) (fun x => if (x ^^^ h0) * R + l0 < q * R + rem then (1 : Rat) else 0) := by
    apply sumRange_congr; intro x _; rw [Nat.xor_comm]
  rw [hcomm, sumRange_xor K h0 hh0 (fun y => if y * R + l0 < q * R + rem then (1 : Rat) else 0)]
  have hsplit : 2 ^ K = (q + 1) + (2 ^ K - (q + 1)) := by omega
  rw [hsplit, sumRange_append]
  have htail : sumRange (2 ^ K - (q + 1)) (fun j =>
      if (q + 1 + j) * R + l0 < q * R + rem then (1 : Rat) else 0) = 0 := by
    have h0 : sumRange (2 ^ K - (q + 1)) (fun j =>
        if (q + 1 + j) * R + l0 < q * R + rem then (1 : Rat) else 0) =
        sumRange (2 ^ K - (q + 1)) (fun _ => (0 : Rat)) := by
      apply sumRange_congr
      intro j _
      have hge : q * R + rem < (q + 1 + j) * R + l0 := by
        have h1 : (q + 1) * R ≤ (q + 1 + j) * R := Nat.mul_le_mul_right R (by omega)
        have h2 : (q + 1) * R = q * R + R := by rw [Nat.succ_mul]
        omega
      have hnot : ¬ ((q + 1 + j) * R + l0 < q * R + rem) := by omega
      simp [hnot]
    rw [h0, sumRange_const]; grind
  rw [htail, Rat.add_zero]
  change sumRange q (fun y => if y * R + l0 < q * R + rem then (1 : Rat) else 0) +
      (if q * R + l0 < q * R + rem then (1 : Rat) else 0) = _
  have hhead : sumRange q (fun y => if y * R + l0 < q * R + rem then (1 : Rat) else 0) = (q : Rat) := by
    have h1 : sumRange q (fun y => if y * R + l0 < q * R + rem then (1 : Rat) else 0) =
        sumRange q (fun _ => (1 : Rat)) := by
      apply sumRange_congr
      intro y hy
      have hlt : y * R + l0 < q * R + rem := by
        have h2 : (y + 1) * R ≤ q * R := Nat.mul_le_mul_right R (by omega)
        have h3 : (y + 1) * R = y * R + R := by rw [Nat.succ_mul]
        omega
      simp [hlt]
    rw [h1, sumRange_const]; grind
  rw [hhead]
  have hmid : (q * R + l0 < q * R + rem) ↔ (l0 < rem) := by omega
  simp only [hmid]
  rfl

/-- Exact zero bias of cross-rank XOR-VDC across all `u0 ∈ {0, ..., 2^M - 1}`. -/
theorem xorVdcBias_eq_zero (M K f : Nat) (hKM : K ≤ M) (hf : f < 2 ^ M) :
    xorVdcBias M K f = 0 := by
  unfold xorVdcBias discreteMean
  let R := 2 ^ (M - K)
  have hR : 0 < R := Nat.two_pow_pos (M - K)
  have hpow : 2 ^ M = 2 ^ K * R := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' hKM]
  have hsum : sumRange (2 ^ M) (fun u0 => xorVdcRankSum M K f u0) =
      sumRange (2 ^ M) (fun u0 => ((f / R : Nat) : Rat) + if u0 % R < f % R then (1 : Rat) else 0) := by
    apply sumRange_congr
    intro u0 hu0
    exact xorVdcRankSum_exact M K f u0 hKM hf hu0
  rw [hsum, hpow]
  have hsplit := sumRange_mul_split (2 ^ K) R hR
    (fun _ l0 => ((f / R : Nat) : Rat) + if l0 < f % R then (1 : Rat) else 0)
  rw [hsplit]
  have hinner : ∀ q : Nat,
      sumRange R (fun l0 => ((f / R : Nat) : Rat) + if l0 < f % R then (1 : Rat) else 0) =
      (f : Rat) := by
    intro _
    rw [sumRange_add, sumRange_const, sumRange_lt_indicator R (f % R) (Nat.le_of_lt (Nat.mod_lt f hR))]
    have hf_eq : R * (f / R) + f % R = f := Nat.div_add_mod f R
    have hcast : (R : Rat) * ((f / R : Nat) : Rat) + ((f % R : Nat) : Rat) = (f : Rat) := by
      rw [← rat_natCast_mul, ← rat_natCast_add, hf_eq]
    exact hcast
  have houter : sumRange (2 ^ K) (fun q =>
      sumRange R (fun l0 => ((f / R : Nat) : Rat) + if l0 < f % R then (1 : Rat) else 0)) =
      ((2 ^ K * f : Nat) : Rat) := by
    rw [sumRange_congr (fun q _ => hinner q), sumRange_const, rat_natCast_mul]
  rw [houter, ← hpow]
  grind

/-- Exact deterministic worst-case error `< 1` ULP for every `f < 2^M` and every `u0 < 2^M`. -/
theorem xorVdcRankSum_err_lt_one (M K f u0 : Nat) (hKM : K ≤ M) (hf : f < 2 ^ M) (hu0 : u0 < 2 ^ M) :
    absRat (xorVdcRankSum M K f u0 - ((2 ^ K * f : Nat) : Rat) / ((2 ^ M : Nat) : Rat)) < 1 := by
  rw [xorVdcRankSum_exact M K f u0 hKM hf hu0]
  let R := 2 ^ (M - K)
  have hR_pos : (0 : Rat) < (R : Rat) := rat_pow2_pos (M - K)
  have hR_ne : (R : Rat) ≠ 0 := Rat.ne_of_gt hR_pos
  have hpow : 2 ^ M = 2 ^ K * R := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' hKM]
  have htarget : ((2 ^ K * f : Nat) : Rat) / ((2 ^ M : Nat) : Rat) =
      ((f / R : Nat) : Rat) + ((f % R : Nat) : Rat) / (R : Rat) := by
    rw [hpow, rat_natCast_mul, rat_natCast_mul]
    have h2K_ne : ((2 ^ K : Nat) : Rat) ≠ 0 := rat_pow2_ne_zero K
    have hcancel : (((2 ^ K : Nat) : Rat) * (f : Rat)) / (((2 ^ K : Nat) : Rat) * (R : Rat)) =
        (f : Rat) / (R : Rat) := by
      rw [Rat.div_def, Rat.div_def, rat_mul_inv _ _ h2K_ne hR_ne]
      have : ((2 ^ K : Nat) : Rat) * (f : Rat) * ((R : Rat)⁻¹ * ((2 ^ K : Nat) : Rat)⁻¹) =
          (((2 ^ K : Nat) : Rat) * ((2 ^ K : Nat) : Rat)⁻¹) * ((f : Rat) * (R : Rat)⁻¹) := by grind
      rw [this, Rat.mul_inv_cancel _ h2K_ne, Rat.one_mul]
    rw [hcancel]
    have hf_eq : (f : Rat) = ((f / R : Nat) : Rat) * (R : Rat) + ((f % R : Nat) : Rat) := by
      have h := Nat.div_add_mod f R
      rw [Nat.mul_comm] at h
      rw [← rat_natCast_mul, ← rat_natCast_add, h]
    rw [hf_eq]
    have h1 : (((f / R : Nat) : Rat) * (R : Rat) + ((f % R : Nat) : Rat)) / (R : Rat) =
        ((f / R : Nat) : Rat) * ((R : Rat) / (R : Rat)) + ((f % R : Nat) : Rat) / (R : Rat) := by
      rw [Rat.div_def, Rat.div_def, Rat.div_def]; grind
    have hRR : (R : Rat) / (R : Rat) = 1 := by rw [Rat.div_def, Rat.mul_inv_cancel _ hR_ne]
    rw [h1, hRR, Rat.mul_one]
  rw [htarget]
  have hdiff :
      (((f / R : Nat) : Rat) + if u0 % R < f % R then (1 : Rat) else 0) -
      (((f / R : Nat) : Rat) + ((f % R : Nat) : Rat) / (R : Rat)) =
      (if u0 % R < f % R then (1 : Rat) else 0) - ((f % R : Nat) : Rat) / (R : Rat) := by grind
  rw [hdiff, absRat_lt_iff]
  have hrem_lt : ((f % R : Nat) : Rat) / (R : Rat) < 1 := by
    have hlt : ((f % R : Nat) : Rat) < (R : Rat) := rat_natCast_lt_natCast (Nat.mod_lt f (Nat.two_pow_pos (M - K)))
    have h := rat_div_lt_div_of_pos_right hlt hR_pos
    have hRR : (R : Rat) / (R : Rat) = 1 := by rw [Rat.div_def, Rat.mul_inv_cancel _ hR_ne]
    rw [hRR] at h
    exact h
  have hrem_nn : (0 : Rat) ≤ ((f % R : Nat) : Rat) / (R : Rat) :=
    rat_div_nonneg (rat_natCast_le_natCast (Nat.zero_le _)) hR_pos
  by_cases hlt : u0 % R < f % R
  · simp only [hlt, ↓reduceIte]
    have hrem_pos : (0 : Rat) < ((f % R : Nat) : Rat) / (R : Rat) :=
      rat_div_pos (rat_natCast_pos (by omega)) hR_pos
    constructor
    · have h1 : (0 : Rat) < 1 - ((f % R : Nat) : Rat) / (R : Rat) := rat_sub_pos hrem_lt
      exact rat_lt_trans (by decide) h1
    · have := (Rat.add_lt_add_right (c := (1 : Rat) - ((f % R : Nat) : Rat) / (R : Rat))).mpr hrem_pos
      grind
  · simp only [hlt, ↓reduceIte]
    constructor
    · have := (Rat.add_lt_add_right (c := -(1 : Rat) - ((f % R : Nat) : Rat) / (R : Rat))).mpr hrem_lt
      grind
    · have h1 : (0 : Rat) - ((f % R : Nat) : Rat) / (R : Rat) ≤ 0 := by
        have := (Rat.add_le_add_right (c := -(((f % R : Nat) : Rat) / (R : Rat)))).mpr hrem_nn
        grind
      exact rat_lt_of_le_of_lt h1 (by decide)

/-! ### 3. Exact Discrete & Continuous MSE Identities -/

/-- Exact discrete Bernoulli variance average:
    `(1 / N) * ∑_{r < N} (r / N) * (1 - r / N) = (N^2 - 1) / (6 * N^2)`. -/
theorem discreteMean_bernoulli_var (N : Nat) (hN : 0 < N) :
    discreteMean N (fun r => ((r : Rat) / (N : Rat)) * (1 - (r : Rat) / (N : Rat))) =
    (((N : Rat) * (N : Rat)) - 1) / (6 * ((N : Rat) * (N : Rat))) := by
  unfold discreteMean
  have hN_ne : (N : Rat) ≠ 0 := rat_natCast_ne_zero hN
  have hcongr : sumRange N (fun r => ((r : Rat) / (N : Rat)) * (1 - (r : Rat) / (N : Rat))) =
      sumRange N (fun r => ((r : Rat) / (N : Rat)) - (((r : Rat) * (r : Rat)) / ((N : Rat) * (N : Rat)))) := by
    apply sumRange_congr
    intro r _
    rw [Rat.div_def, Rat.div_def, rat_mul_inv _ _ hN_ne hN_ne]
    grind
  rw [hcongr, sumRange_sub, sumRange_div_const, sumRange_div_const, sumRange_nat_id, sumRange_nat_sq]
  have h1 : (((N : Rat) * ((N : Rat) - 1)) / 2 / (N : Rat) -
      ((N : Rat) * ((N : Rat) - 1) * (2 * (N : Rat) - 1)) / 6 / ((N : Rat) * (N : Rat))) / (N : Rat) *
      (6 * ((N : Rat) * (N : Rat))) = (N : Rat) * (N : Rat) - 1 := by
    have hinv : (N : Rat) * (N : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ hN_ne
    rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def]
    rw [rat_mul_inv _ _ hN_ne hN_ne]
    have hcancel1 : (N : Rat) * ((N : Rat) - 1) * (2 : Rat)⁻¹ * (N : Rat)⁻¹ =
        ((N : Rat) * (N : Rat)⁻¹) * (((N : Rat) - 1) * (2 : Rat)⁻¹) := by grind
    have hcancel2 : (N : Rat) * ((N : Rat) - 1) * (2 * (N : Rat) - 1) * (6 : Rat)⁻¹ *
        ((N : Rat)⁻¹ * (N : Rat)⁻¹) =
        ((N : Rat) * (N : Rat)⁻¹) * (((N : Rat) - 1) * (2 * (N : Rat) - 1) * (6 : Rat)⁻¹ * (N : Rat)⁻¹) := by grind
    rw [hcancel1, hcancel2, hinv, Rat.one_mul, Rat.one_mul]
    have hfin : ((((N : Rat) - 1) * (2 : Rat)⁻¹ -
        ((N : Rat) - 1) * (2 * (N : Rat) - 1) * (6 : Rat)⁻¹ * (N : Rat)⁻¹) * (N : Rat)⁻¹) *
        (6 * ((N : Rat) * (N : Rat))) =
        (3 * ((N : Rat) - 1) * (N : Rat) - ((N : Rat) - 1) * (2 * (N : Rat) - 1)) *
        ((N : Rat) * (N : Rat)⁻¹) * ((N : Rat) * (N : Rat)⁻¹) := by
      have h62 : (6 : Rat) * (2 : Rat)⁻¹ = 3 := by grind
      have h66 : (6 : Rat) * (6 : Rat)⁻¹ = 1 := by grind
      grind
    rw [hfin, hinv, Rat.mul_one, Rat.mul_one]
    grind
  have hden_ne : 6 * ((N : Rat) * (N : Rat)) ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact absurd h (by decide)
    | inr h =>
      cases Rat.mul_eq_zero.mp h with
      | inl h1 => exact hN_ne h1
      | inr h2 => exact hN_ne h2
  have hfin := congrArg (· / (6 * ((N : Rat) * (N : Rat)))) h1
  have hcancel : ∀ x : Rat, x * (6 * ((N : Rat) * (N : Rat))) / (6 * ((N : Rat) * (N : Rat))) = x := by
    intro x
    rw [Rat.div_def, Rat.mul_assoc, Rat.mul_inv_cancel _ hden_ne, Rat.mul_one]
  rw [hcancel] at hfin
  exact hfin

/-- Exact discrete averaged MSE of cross-rank XOR-VDC on an `M`-bit grid:
    `xorVdcDiscreteMse M K = (R^2 - 1) / (6 * R^2)` where `R = 2^(M - K)`. -/
theorem xorVdcDiscreteMse_exact (M K : Nat) (hKM : K ≤ M) :
    xorVdcDiscreteMse M K =
    ((((2 ^ (M - K) : Nat) : Rat) * ((2 ^ (M - K) : Nat) : Rat)) - 1) /
      (6 * (((2 ^ (M - K) : Nat) : Rat) * ((2 ^ (M - K) : Nat) : Rat))) := by
  unfold xorVdcDiscreteMse
  let R := 2 ^ (M - K)
  have hR : 0 < R := Nat.two_pow_pos (M - K)
  have hR_ne : (R : Rat) ≠ 0 := rat_pow2_ne_zero (M - K)
  have hpow : 2 ^ M = 2 ^ K * R := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' hKM]
  have h2K_ne : ((2 ^ K : Nat) : Rat) ≠ 0 := rat_pow2_ne_zero K
  have hinner_u0 : ∀ f, f < 2 ^ M →
      discreteMean (2 ^ M) (fun u0 =>
        let e := xorVdcRankSum M K f u0 - ((2 ^ K * f : Nat) : Rat) / ((2 ^ M : Nat) : Rat)
        e * e) =
      (((f % R : Nat) : Rat) / (R : Rat)) * (1 - ((f % R : Nat) : Rat) / (R : Rat)) := by
    intro f hf
    unfold discreteMean
    let p : Rat := ((f % R : Nat) : Rat) / (R : Rat)
    have htarget : ((2 ^ K * f : Nat) : Rat) / ((2 ^ M : Nat) : Rat) =
        ((f / R : Nat) : Rat) + p := by
      rw [hpow, rat_natCast_mul, rat_natCast_mul]
      have hcancel : (((2 ^ K : Nat) : Rat) * (f : Rat)) / (((2 ^ K : Nat) : Rat) * (R : Rat)) =
          (f : Rat) / (R : Rat) := by
        rw [Rat.div_def, Rat.div_def, rat_mul_inv _ _ h2K_ne hR_ne]
        have : ((2 ^ K : Nat) : Rat) * (f : Rat) * ((R : Rat)⁻¹ * ((2 ^ K : Nat) : Rat)⁻¹) =
            (((2 ^ K : Nat) : Rat) * ((2 ^ K : Nat) : Rat)⁻¹) * ((f : Rat) * (R : Rat)⁻¹) := by grind
        rw [this, Rat.mul_inv_cancel _ h2K_ne, Rat.one_mul]
      rw [hcancel]
      have hf_eq : (f : Rat) = ((f / R : Nat) : Rat) * (R : Rat) + ((f % R : Nat) : Rat) := by
        have h := Nat.div_add_mod f R; rw [Nat.mul_comm] at h
        rw [← rat_natCast_mul, ← rat_natCast_add, h]
      rw [hf_eq]
      have h1 : (((f / R : Nat) : Rat) * (R : Rat) + ((f % R : Nat) : Rat)) / (R : Rat) =
          ((f / R : Nat) : Rat) * ((R : Rat) / (R : Rat)) + p := by
        change (((f / R : Nat) : Rat) * (R : Rat) + ((f % R : Nat) : Rat)) / (R : Rat) =
          ((f / R : Nat) : Rat) * ((R : Rat) / (R : Rat)) + ((f % R : Nat) : Rat) / (R : Rat)
        rw [Rat.div_def, Rat.div_def, Rat.div_def]; grind
      have hRR : (R : Rat) / (R : Rat) = 1 := by rw [Rat.div_def, Rat.mul_inv_cancel _ hR_ne]
      rw [h1, hRR, Rat.mul_one]
    have hcongr : sumRange (2 ^ M) (fun u0 =>
        let e := xorVdcRankSum M K f u0 - ((2 ^ K * f : Nat) : Rat) / ((2 ^ M : Nat) : Rat)
        e * e) =
        sumRange (2 ^ M) (fun u0 =>
          (if u0 % R < f % R then (1 : Rat) else 0) * (1 - 2 * p) + p * p) := by
      apply sumRange_congr
      intro u0 hu0
      dsimp only
      rw [xorVdcRankSum_exact M K f u0 hKM hf hu0, htarget]
      by_cases hlt : u0 % R < f % R <;> simp [hlt] <;> grind
    rw [hcongr, hpow]
    rw [sumRange_mul_split (2 ^ K) R hR (fun _ l0 =>
      (if l0 < f % R then (1 : Rat) else 0) * (1 - 2 * p) + p * p)]
    have hRsum : ∀ q : Nat,
        sumRange R (fun l0 => (if l0 < f % R then (1 : Rat) else 0) * (1 - 2 * p) + p * p) =
        (R : Rat) * (p * (1 - p)) := by
      intro _
      rw [sumRange_add, sumRange_const]
      have hmul : sumRange R (fun l0 => (if l0 < f % R then (1 : Rat) else 0) * (1 - 2 * p)) =
          (1 - 2 * p) * sumRange R (fun l0 => if l0 < f % R then (1 : Rat) else 0) := by
        rw [← sumRange_mul_left]
        apply sumRange_congr; intro l0 _; grind
      rw [hmul, sumRange_lt_indicator R (f % R) (Nat.le_of_lt (Nat.mod_lt f hR))]
      have hpR : ((f % R : Nat) : Rat) = (R : Rat) * p := by
        change ((f % R : Nat) : Rat) = (R : Rat) * (((f % R : Nat) : Rat) / (R : Rat))
        rw [Rat.div_def]
        have : (R : Rat) * (((f % R : Nat) : Rat) * (R : Rat)⁻¹) =
            ((f % R : Nat) : Rat) * ((R : Rat) * (R : Rat)⁻¹) := by grind
        rw [this, Rat.mul_inv_cancel _ hR_ne, Rat.mul_one]
      rw [hpR]; grind
    rw [sumRange_congr (fun q _ => hRsum q), sumRange_const, rat_natCast_mul]
    have hM_ne : ((2 ^ K : Nat) : Rat) * (R : Rat) ≠ 0 := by
      intro h0
      cases Rat.mul_eq_zero.mp h0 with
      | inl h => exact h2K_ne h
      | inr h => exact hR_ne h
    rw [Rat.div_def]
    have : ((2 ^ K : Nat) : Rat) * ((R : Rat) * (p * (1 - p))) * (((2 ^ K : Nat) : Rat) * (R : Rat))⁻¹ =
        (((2 ^ K : Nat) : Rat) * (R : Rat) * (((2 ^ K : Nat) : Rat) * (R : Rat))⁻¹) * (p * (1 - p)) := by grind
    rw [this, Rat.mul_inv_cancel _ hM_ne, Rat.one_mul]
  change (sumRange (2 ^ M) (fun f =>
    discreteMean (2 ^ M) (fun u0 =>
      let e := xorVdcRankSum M K f u0 - ((2 ^ K * f : Nat) : Rat) / ((2 ^ M : Nat) : Rat)
      e * e))) / ((2 ^ M : Nat) : Rat) = _
  rw [sumRange_congr hinner_u0, hpow]
  rw [sumRange_mul_split (2 ^ K) R hR
    (fun _ rem => ((rem : Rat) / (R : Rat)) * (1 - (rem : Rat) / (R : Rat)))]
  rw [sumRange_const, rat_natCast_mul]
  have hcancel : (((2 ^ K : Nat) : Rat) *
      sumRange R (fun rem => ((rem : Rat) / (R : Rat)) * (1 - (rem : Rat) / (R : Rat)))) /
      (((2 ^ K : Nat) : Rat) * (R : Rat)) =
      discreteMean R (fun rem => ((rem : Rat) / (R : Rat)) * (1 - (rem : Rat) / (R : Rat))) := by
    unfold discreteMean
    rw [Rat.div_def, Rat.div_def, rat_mul_inv _ _ h2K_ne hR_ne]
    have : ((2 ^ K : Nat) : Rat) *
        sumRange R (fun rem => ((rem : Rat) / (R : Rat)) * (1 - (rem : Rat) / (R : Rat))) *
        ((R : Rat)⁻¹ * ((2 ^ K : Nat) : Rat)⁻¹) =
        (((2 ^ K : Nat) : Rat) * ((2 ^ K : Nat) : Rat)⁻¹) *
        (sumRange R (fun rem => ((rem : Rat) / (R : Rat)) * (1 - (rem : Rat) / (R : Rat))) * (R : Rat)⁻¹) := by grind
    rw [this, Rat.mul_inv_cancel _ h2K_ne, Rat.one_mul]
  rw [hcancel]
  exact discreteMean_bernoulli_var R hR

theorem indSrDiscreteMse_exact (M K : Nat) :
    indSrDiscreteMse M K =
    ((2 ^ K : Nat) : Rat) *
      ((((2 ^ M : Nat) : Rat) * ((2 ^ M : Nat) : Rat) - 1) /
        (6 * (((2 ^ M : Nat) : Rat) * ((2 ^ M : Nat) : Rat)))) := by
  unfold indSrDiscreteMse
  rw [discreteMean_bernoulli_var (2 ^ M) (Nat.two_pow_pos M)]

/-- **Headline Theorem 3 (Cross-Rank XOR-VDC Bijection, Zero Bias, `< 1` ULP Bound, & Exact MSE):** -/
theorem cross_rank_xor_vdc_bijection_and_exact_mse :
    (∀ (M K u0 : Nat), K ≤ M → u0 < 2 ^ M →
      (∀ r : Fin (2 ^ K), topBits M K (xorVdcThreshold M K r.val u0) < 2 ^ K) ∧
      (∀ r₁ r₂ : Fin (2 ^ K),
        topBits M K (xorVdcThreshold M K r₁.val u0) = topBits M K (xorVdcThreshold M K r₂.val u0) →
        r₁ = r₂) ∧
      (∀ y : Fin (2 ^ K), ∃ r : Fin (2 ^ K),
        topBits M K (xorVdcThreshold M K r.val u0) = y.val)) ∧
    (∀ (M K f : Nat), K ≤ M → f < 2 ^ M →
      xorVdcBias M K f = 0 ∧
      (∀ u0, u0 < 2 ^ M →
        absRat (xorVdcRankSum M K f u0 - ((2 ^ K * f : Nat) : Rat) / ((2 ^ M : Nat) : Rat)) < 1)) ∧
    (∀ (M K : Nat), K ≤ M →
      xorVdcDiscreteMse M K =
        ((((2 ^ (M - K) : Nat) : Rat) * ((2 ^ (M - K) : Nat) : Rat)) - 1) /
          (6 * (((2 ^ (M - K) : Nat) : Rat) * ((2 ^ (M - K) : Nat) : Rat))) ∧
      xorVdcDiscreteMse M K < 1 / 6 ∧
      indSrDiscreteMse M K =
        ((2 ^ K : Nat) : Rat) *
          ((((2 ^ M : Nat) : Rat) * ((2 ^ M : Nat) : Rat) - 1) /
            (6 * (((2 ^ M : Nat) : Rat) * ((2 ^ M : Nat) : Rat))))) ∧
    (∀ (tp : Nat), 1 ≤ tp →
      mseIndSr tp / mseXorVdc = (tp : Rat) ∧
      mseRne tp / mseXorVdc = ((tp : Rat) * (tp : Rat)) / 2 ∧
      mseAntithetic tp / mseXorVdc = (tp : Rat) / 2) ∧
    (mseIndSr 64 / mseXorVdc = 64 ∧
     mseRne 64 / mseXorVdc = 2048 ∧
     mseAntithetic 64 / mseXorVdc = 32) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro M K u0 hKM hu0
    exact topBits_xorVdc_bijection M K u0 hKM hu0
  · intro M K f hKM hf
    refine ⟨xorVdcBias_eq_zero M K f hKM hf, ?_⟩
    intro u0 hu0
    exact xorVdcRankSum_err_lt_one M K f u0 hKM hf hu0
  · intro M K hKM
    have hmse := xorVdcDiscreteMse_exact M K hKM
    refine ⟨hmse, ?_, indSrDiscreteMse_exact M K⟩
    rw [hmse]
    let R : Rat := ((2 ^ (M - K) : Nat) : Rat)
    have hR_pos : (0 : Rat) < R := rat_pow2_pos (M - K)
    have hR2_pos : (0 : Rat) < R * R := rat_mul_pos hR_pos hR_pos
    have h6R2_pos : (0 : Rat) < 6 * (R * R) := rat_mul_pos (by decide) hR2_pos
    have hlt : R * R - 1 < R * R := by
      have := (Rat.add_lt_add_right (c := R * R - 1)).mpr (show (0 : Rat) < 1 by decide)
      grind
    have hdiv := rat_div_lt_div_of_pos_right hlt h6R2_pos
    have hrhs : (R * R) / (6 * (R * R)) = 1 / 6 := by
      have hR2_ne : R * R ≠ 0 := Rat.ne_of_gt hR2_pos
      have h6_ne : (6 : Rat) ≠ 0 := by decide
      rw [Rat.div_def, Rat.div_def, rat_mul_inv _ _ h6_ne hR2_ne]
      have : R * R * ((R * R)⁻¹ * (6 : Rat)⁻¹) = (R * R * (R * R)⁻¹) * (6 : Rat)⁻¹ := by grind
      rw [this, Rat.mul_inv_cancel _ hR2_ne]
    rw [hrhs] at hdiv
    exact hdiv
  · intro tp _
    unfold mseIndSr mseRne mseAntithetic mseXorVdc
    refine ⟨by grind, by grind, by grind⟩
  · unfold mseIndSr mseRne mseAntithetic mseXorVdc
    refine ⟨by grind, by grind, by grind⟩

end AllReduceXorVdc
