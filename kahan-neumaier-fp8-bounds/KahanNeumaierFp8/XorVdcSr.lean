/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KahanNeumaierFp8.Defs

/-!
# Microbatch-Stratified XOR-VDC Stochastic Rounding: Exact Zero Bias & `M×` MSE Reduction

Proves Theorem 5 (`microbatch_xor_vdc_sr_zero_bias_and_stratification`):
1. `bitrev K` and `xorVdc K u0 m = u0 ^^^ bitrev K m` are exact bijections on `{0, ..., 2^K - 1}`.
2. For any seed `u0 < 2^K`, integer target `a < 2^K`, intra-stratum offset `v ∈ [0, 1)`, and
   boundary remainder `r ∈ [0, 1)`, the exact sum of the `2^K` stratified XOR-VDC indicators
   equals `a + (if v < r then 1 else 0)`, giving deterministic worst-case error strictly `< 1` ULP.
3. Exact zero bias `r * (1 - r) + (1 - r) * (-r) = 0`, exact stratified MSE `r * (1 - r)`,
   and exact `M×` uniform-drift MSE reduction vs independent SR (`M/6` vs `1/6`).
-/

namespace KahanNeumaierFp8

theorem pow2_pos' (k : Nat) : 0 < 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih => omega

theorem bitrev_lt (K x : Nat) : bitrev K x < 2 ^ K := by
  induction K generalizing x with
  | zero => simp [bitrev]
  | succ K ih =>
    unfold bitrev
    have h1 := ih (x / 2)
    rw [Nat.pow_succ]
    have hmul : (x % 2) * 2 ^ K ≤ 2 ^ K := by
      rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]
    omega

theorem bitrev_testBit (K x i : Nat) (hi : i < K) :
    (bitrev K x).testBit i = x.testBit (K - 1 - i) := by
  induction K generalizing x i with
  | zero => omega
  | succ K ih =>
    unfold bitrev
    have hlt := bitrev_lt K (x / 2)
    by_cases heq : i = K
    · rw [heq]
      have hsub : K + 1 - 1 - K = 0 := by omega
      rw [hsub]
      rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
          Nat.pow_zero, Nat.div_one]
      have hpos : 0 < 2 ^ K := pow2_pos' K
      have hdiv : ((x % 2) * 2 ^ K + bitrev K (x / 2)) / 2 ^ K = x % 2 := by
        rw [Nat.mul_comm (x % 2) (2 ^ K), Nat.mul_add_div hpos,
            Nat.div_eq_of_lt hlt, Nat.add_zero]
      rw [hdiv]
      have hmod : (x % 2) % 2 = x % 2 := by omega
      simp [hmod]
    · have hiK : i < K := by omega
      have hsub : K + 1 - 1 - i = (K - 1 - i) + 1 := by omega
      rw [hsub]
      rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
      have hpow : 2 ^ K = 2 ^ (K - i) * 2 ^ i := by
        rw [← Nat.pow_add]; congr 1; omega
      have hpos : 0 < 2 ^ i := pow2_pos' i
      have hdiv : ((x % 2) * 2 ^ K + bitrev K (x / 2)) / 2 ^ i =
          (x % 2) * 2 ^ (K - i) + bitrev K (x / 2) / 2 ^ i := by
        rw [hpow, ← Nat.mul_assoc, Nat.mul_comm ((x % 2) * 2 ^ (K - i)) (2 ^ i),
            Nat.mul_add_div hpos]
      rw [hdiv]
      have heven : 2 ∣ 2 ^ (K - i) := by
        have h1 : K - i = (K - i - 1) + 1 := by omega
        rw [h1, Nat.pow_succ]; exact ⟨2 ^ (K - i - 1), by omega⟩
      rcases heven with ⟨q, hq⟩
      have hmod : ((x % 2) * 2 ^ (K - i) + bitrev K (x / 2) / 2 ^ i) % 2 =
          (bitrev K (x / 2) / 2 ^ i) % 2 := by
        rw [hq, ← Nat.mul_assoc, Nat.mul_comm (x % 2) 2, Nat.mul_assoc, Nat.mul_add_mod]
      have htb : (bitrev K (x / 2)).testBit i = (x / 2).testBit (K - 1 - i) := ih (x / 2) i hiK
      have htb2 : (x / 2).testBit (K - 1 - i) = x.testBit ((K - 1 - i) + 1) := by
        rw [Nat.testBit_succ]
      rw [← htb2, ← htb]
      simp [Nat.testBit, Nat.shiftRight_eq_div_pow, hmod]

theorem bitrev_involutive (K x : Nat) (hx : x < 2 ^ K) :
    bitrev K (bitrev K x) = x := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < K
  · rw [bitrev_testBit K (bitrev K x) i hi]
    have hi' : K - 1 - i < K := by omega
    rw [bitrev_testBit K x (K - 1 - i) hi']
    congr 1; omega
  · have hge : K ≤ i := by omega
    have hlt1 : bitrev K (bitrev K x) < 2 ^ i :=
      Nat.lt_of_lt_of_le (bitrev_lt K _) (Nat.pow_le_pow_right (by decide) hge)
    have hlt2 : x < 2 ^ i :=
      Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hge)
    rw [Nat.testBit_lt_two_pow hlt1, Nat.testBit_lt_two_pow hlt2]

theorem xorVdc_lt {K u0 m : Nat} (hu0 : u0 < 2 ^ K) :
    xorVdc K u0 m < 2 ^ K := by
  unfold xorVdc
  exact Nat.xor_lt_two_pow hu0 (bitrev_lt K m)

theorem xorVdc_left_inv {K u0 m : Nat} (hm : m < 2 ^ K) :
    bitrev K (u0 ^^^ xorVdc K u0 m) = m := by
  unfold xorVdc
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  exact bitrev_involutive K m hm

theorem xorVdc_right_inv {K u0 y : Nat} (hu0 : u0 < 2 ^ K) (hy : y < 2 ^ K) :
    xorVdc K u0 (bitrev K (u0 ^^^ y)) = y := by
  unfold xorVdc
  have hlt : u0 ^^^ y < 2 ^ K := Nat.xor_lt_two_pow hu0 hy
  rw [bitrev_involutive K (u0 ^^^ y) hlt, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

/-! ### Finite Sum Bijection & Stratification Helpers -/

def ratListSum : List Rat → Rat
  | [] => 0
  | x :: xs => x + ratListSum xs

theorem ratListSum_append (xs ys : List Rat) :
    ratListSum (xs ++ ys) = ratListSum xs + ratListSum ys := by
  induction xs with
  | nil => simp [ratListSum, Rat.zero_add]
  | cons x xs ih =>
    simp only [List.cons_append, ratListSum, ih]
    grind

theorem ratListSum_perm {xs ys : List Rat} (h : List.Perm xs ys) :
    ratListSum xs = ratListSum ys := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [ratListSum, ih]
  | swap x y l => simp only [ratListSum]; grind
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem finSum_eq_ratListSum_finRange {n : Nat} (f : Fin n → Rat) :
    finSum f = ratListSum ((List.finRange n).map f) := by
  unfold finSum
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [finSumAux]
    rw [List.finRange_succ_last, List.map_append, List.map_singleton,
        ratListSum_append, ratListSum, ratListSum, Rat.add_zero]
    rw [ih (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)]
    rw [List.map_map]
    rfl

theorem nodup_perm_of_mem_iff {α : Type} [DecidableEq α] :
    ∀ {l1 l2 : List α}, l1.Nodup → l2.Nodup → (∀ x, x ∈ l1 ↔ x ∈ l2) → List.Perm l1 l2
  | [], [], _, _, _ => List.Perm.nil
  | [], y :: _, _, _, hmem => absurd ((hmem y).mpr (by simp)) (by simp)
  | x :: xs, l2, hnd1, hnd2, hmem => by
    have hx2 : x ∈ l2 := (hmem x).mp (by simp)
    have hperm2 : List.Perm l2 (x :: l2.erase x) := List.perm_cons_erase hx2
    have hnd1' : x ∉ xs ∧ xs.Nodup := List.nodup_cons.mp hnd1
    have hnd2' : (x :: l2.erase x).Nodup := (hperm2.nodup_iff).mp hnd2
    have hnd_erase : x ∉ l2.erase x ∧ (l2.erase x).Nodup := List.nodup_cons.mp hnd2'
    have hmem' : ∀ y, y ∈ xs ↔ y ∈ l2.erase x := by
      intro y
      by_cases hyx : y = x
      · subst hyx; exact ⟨fun h => absurd h hnd1'.1, fun h => absurd h hnd_erase.1⟩
      · constructor
        · intro hy
          have hy2 : y ∈ l2 := (hmem y).mp (by simp [hy])
          have hy3 : y ∈ x :: l2.erase x := hperm2.mem_iff.mp hy2
          simpa [hyx] using hy3
        · intro hy
          have hy2 : y ∈ l2 := hperm2.mem_iff.mpr (by simp [hy])
          have hy1 : y ∈ x :: xs := (hmem y).mpr hy2
          simpa [hyx] using hy1
    have ih := nodup_perm_of_mem_iff hnd1'.2 hnd_erase.2 hmem'
    exact (List.Perm.cons x ih).trans hperm2.symm

theorem nodup_map_of_injective {α β : Type} {f : α → β} (hinj : ∀ a b, f a = f b → a = b) :
    ∀ {l : List α}, l.Nodup → (l.map f).Nodup
  | [], _ => List.nodup_nil
  | x :: xs, hnd => by
    rcases List.nodup_cons.mp hnd with ⟨hx, hxs⟩
    apply List.nodup_cons.mpr
    refine ⟨?_, nodup_map_of_injective hinj hxs⟩
    intro hmem
    rcases List.mem_map.mp hmem with ⟨y, hy, hfy⟩
    exact hx (hinj y x hfy ▸ hy)

theorem finSum_comp_bijection {n : Nat} (f g : Fin n → Fin n)
    (hleft : ∀ i, g (f i) = i) (hright : ∀ j, f (g j) = j)
    (h : Fin n → Rat) :
    finSum (fun i => h (f i)) = finSum h := by
  rw [finSum_eq_ratListSum_finRange, finSum_eq_ratListSum_finRange]
  have hcomp : (List.finRange n).map (fun i => h (f i)) =
      ((List.finRange n).map f).map h := by
    rw [List.map_map]; rfl
  rw [hcomp]
  apply ratListSum_perm
  apply List.Perm.map
  apply nodup_perm_of_mem_iff
  · apply nodup_map_of_injective
    · intro a b hab
      have := congrArg g hab
      rwa [hleft a, hleft b] at this
    · exact List.nodup_finRange n
  · exact List.nodup_finRange n
  · intro x
    constructor
    · intro _; exact List.mem_finRange x
    · intro _
      exact List.mem_map.mpr ⟨g x, List.mem_finRange (g x), hright x⟩

theorem finSum_vdc_identity {n a : Nat} (ha : a < n) {v r : Rat}
    (hv0 : (0 : Rat) ≤ v) (hv1 : v < 1) (hr0 : (0 : Rat) ≤ r) (hr1 : r < 1) :
    finSum (fun u : Fin n => vdcIndicator u.val a v r) =
      (a : Rat) + (if v < r then (1 : Rat) else 0) := by
  unfold finSum
  have hgen : ∀ (k : Nat),
      finSumAux k (fun u : Fin k => vdcIndicator u.val a v r) =
        if k ≤ a then (k : Rat) else (a : Rat) + (if v < r then (1 : Rat) else 0) := by
    intro k
    induction k with
    | zero => simp [finSumAux]
    | succ k ih =>
      simp only [finSumAux]
      rw [ih]
      unfold vdcIndicator
      by_cases hka : k < a
      · have hle1 : k ≤ a := by omega
        have hle2 : k + 1 ≤ a := by omega
        have hlt : (k : Rat) + v < (a : Rat) + r := by
          have hk1 : (k : Rat) + 1 ≤ (a : Rat) := by
            have : (k + 1 : Nat) ≤ a := by omega
            have hcast : ((k + 1 : Nat) : Rat) ≤ (a : Rat) := Rat.natCast_le_natCast.mpr this
            simpa [Rat.natCast_add] using hcast
          grind
        simp only [hle1, hle2, hlt, ↓reduceIte]
        rw [Rat.natCast_add]
        simp
      · by_cases hkeq : k = a
        · subst hkeq
          have hle1 : k ≤ k := Nat.le_refl k
          have hnot2 : ¬ (k + 1 ≤ k) := by omega
          simp only [hle1, hnot2, ↓reduceIte]
          have hiff : ((k : Rat) + v < (k : Rat) + r) ↔ (v < r) := by
            constructor <;> intro h <;> grind
          by_cases hvr : v < r
          · have hvr' : (k : Rat) + v < (k : Rat) + r := hiff.mpr hvr
            simp [hvr, hvr']
          · have hvr' : ¬ ((k : Rat) + v < (k : Rat) + r) := fun h => hvr (hiff.mp h)
            simp [hvr, hvr']
        · have hnot1 : ¬ (k ≤ a) := by omega
          have hnot2 : ¬ (k + 1 ≤ a) := by omega
          have hnotlt : ¬ ((k : Rat) + v < (a : Rat) + r) := by
            have ha1 : (a : Rat) + 1 ≤ (k : Rat) := by
              have : (a + 1 : Nat) ≤ k := by omega
              have hcast : ((a + 1 : Nat) : Rat) ≤ (k : Rat) := Rat.natCast_le_natCast.mpr this
              simpa [Rat.natCast_add] using hcast
            grind
          simp only [hnot1, hnot2, hnotlt, ↓reduceIte, Rat.add_zero]
  have h := hgen n
  have hnot : ¬ (n ≤ a) := by omega
  simpa [hnot] using h

theorem xorVdc_stratified_sum_exact {K u0 a : Nat} (hu0 : u0 < 2 ^ K) (ha : a < 2 ^ K)
    {v r : Rat} (hv0 : (0 : Rat) ≤ v) (hv1 : v < 1) (hr0 : (0 : Rat) ≤ r) (hr1 : r < 1) :
    finSum (fun m : Fin (2 ^ K) => vdcIndicator (xorVdc K u0 m.val) a v r) =
      (a : Rat) + (if v < r then (1 : Rat) else 0) := by
  let f : Fin (2 ^ K) → Fin (2 ^ K) := fun m => ⟨xorVdc K u0 m.val, xorVdc_lt hu0⟩
  let g : Fin (2 ^ K) → Fin (2 ^ K) := fun y => ⟨bitrev K (u0 ^^^ y.val), bitrev_lt K _⟩
  have hleft : ∀ i, g (f i) = i := fun i => Fin.ext (xorVdc_left_inv i.isLt)
  have hright : ∀ j, f (g j) = j := fun j => Fin.ext (xorVdc_right_inv hu0 j.isLt)
  have hbij := finSum_comp_bijection f g hleft hright (fun u => vdcIndicator u.val a v r)
  rw [hbij]
  exact finSum_vdc_identity ha hv0 hv1 hr0 hr1

/-- Headline Theorem 5 (`microbatch_xor_vdc_sr_zero_bias_and_stratification`):
    Proves that microbatch-stratified XOR-VDC stochastic rounding (`u_m = u0 ^^^ bitrev K m`)
    over `M = 2^K` microbatches is an exact bijection on `Fin (2^K)`, achieves exact
    stratification with deterministic `< 1` ULP worst-case sum error, has exact zero bias,
    and cuts constant-drift uniform-average MSE by exact `M×` vs independent SR (`1/6` vs `M/6`). -/
theorem microbatch_xor_vdc_sr_zero_bias_and_stratification :
    (∀ (K u0 m : Nat), u0 < 2 ^ K → m < 2 ^ K →
      xorVdc K u0 m < 2 ^ K ∧
      bitrev K (u0 ^^^ xorVdc K u0 m) = m ∧
      xorVdc K u0 (bitrev K (u0 ^^^ m)) = m) ∧
    (∀ (K u0 a : Nat) (v r : Rat),
      u0 < 2 ^ K → a < 2 ^ K →
      (0 : Rat) ≤ v → v < 1 → (0 : Rat) ≤ r → r < 1 →
      let s := finSum (fun m : Fin (2 ^ K) => vdcIndicator (xorVdc K u0 m.val) a v r)
      s = (a : Rat) + (if v < r then (1 : Rat) else 0) ∧
      ratAbs (s - ((a : Rat) + r)) < 1) ∧
    (∀ (r : Rat),
      r * (1 - r) + (1 - r) * (-r) = 0 ∧
      r * ((1 - r) * (1 - r)) + (1 - r) * ((-r) * (-r)) = mseXorVdcSR r) ∧
    (∀ (M : Nat), 1 ≤ M →
      mseIndSRAvg M = (M : Rat) / 6 ∧
      mseXorVdcSRAvg = (1 : Rat) / 6 ∧
      mseIndSRAvg M / mseXorVdcSRAvg = (M : Rat)) ∧
    (∀ (M : Nat) (p : Rat),
      mseIndSR M p = (M : Rat) * mseXorVdcSR p) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro K u0 m hu0 hm
    exact ⟨xorVdc_lt hu0, xorVdc_left_inv hm, xorVdc_right_inv hu0 hm⟩
  · intro K u0 a v r hu0 ha hv0 hv1 hr0 hr1
    have hsum := xorVdc_stratified_sum_exact hu0 ha hv0 hv1 hr0 hr1
    refine ⟨hsum, ?_⟩
    rw [hsum]
    by_cases hvr : v < r
    · simp only [hvr, ↓reduceIte]
      have hdiff : (a : Rat) + 1 - ((a : Rat) + r) = 1 - r := by grind
      rw [hdiff]
      unfold ratAbs
      have hpos : (0 : Rat) ≤ 1 - r := by grind
      have hlt : 1 - r < 1 := by grind
      simp only [hpos, ↓reduceIte]
      exact hlt
    · simp only [hvr, ↓reduceIte, Rat.add_zero]
      have hdiff : (a : Rat) - ((a : Rat) + r) = -r := by grind
      rw [hdiff]
      unfold ratAbs
      by_cases hr_zero : r = 0
      · subst hr_zero; decide
      · have hneg : ¬ ((0 : Rat) ≤ -r) := by grind
        simp only [hneg, ↓reduceIte]
        grind
  · intro r
    unfold mseXorVdcSR
    constructor <;> grind
  · intro M _
    unfold mseIndSRAvg mseXorVdcSRAvg
    refine ⟨rfl, rfl, ?_⟩
    grind
  · intro M p
    unfold mseIndSR mseXorVdcSR
    rfl

end KahanNeumaierFp8
