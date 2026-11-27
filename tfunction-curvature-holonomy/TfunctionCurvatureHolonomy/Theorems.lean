/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TfunctionCurvatureHolonomy.Defs

/-!
# Generalized T-Function Single-Cycle Inductive Lifting Engine (Standalone Lean 4.34.1)

Pure-silicon finite-to-infinite proof mechanism for 1-Lipschitz 2-adic T-functions:
- Layer 1: Exact Bit-Slice Doubling Criterion (`singleCycle_succ_iff`)
- Layer 2: Universal Curvature-Holonomy Transport Law (`holonomy_succ_iff_curvatureSum_zero`)
- Layer 3: Reusable Finite->Infinite Lifting Engines:
    * Bit-flip / general fixed-point-free involution curvature annihilator
    * Multi-term F_2-linear curvature decomposition lifter
    * Universal 2-Lipschitz even-parity XOR symmetry action (instantiated on carry-mask `2*k*(x ^^^ (x+1))`)
- Novel Infinite Theorem Families:
    * Family A: 4-parameter hybrid ARX-square-run-carrymask family `hybridH a b C k`
      (exact `w <= 4` lifting iff, complete 4-bit arithmetic characterization, Bit-2 defect annihilation)
    * Family B: Arbitrary-order `d`-run family `runT d C`
      (complete iff characterization, exact failure at `w = d+1` for `C = 1`, and No-Universal-Finite-Threshold theorem)
-/


/-! ## Section 1: Core Definitions & Basic Modular/Orbit Lemmas -/

namespace SiliconTFunc

def IsTwoLipschitz (h : Nat → Nat) : Prop :=
  ∀ w x y, x % 2 ^ w = y % 2 ^ w → h x % 2 ^ (w + 1) = h y % 2 ^ (w + 1)

def IsFourLipschitz (h : Nat → Nat) : Prop :=
  ∀ w x y, x % 2 ^ w = y % 2 ^ w → h x % 2 ^ (w + 2) = h y % 2 ^ (w + 2)

def defectSum (f : Nat → Nat) (w : Nat) : Int :=
  intSum (fun r => (f r : Int) - (r : Int)) (2 ^ w)

def curvatureBit (f : Nat → Nat) (w r : Nat) : Bool :=
  (((f (r + 2 ^ w) : Int) - (f r : Int) - (2 ^ w : Int)) % (2 ^ (w + 2) : Int) == (2 ^ (w + 1) : Int))

theorem two_pow_pos (w : Nat) : 0 < 2 ^ w := Nat.pow_pos (by decide)

theorem two_pow_succ_eq (w : Nat) : 2 ^ (w + 1) = 2 ^ w + 2 ^ w := by
  rw [Nat.pow_succ]; omega

theorem iter_add (f : Nat → Nat) (a b x : Nat) :
    iter f (a + b) x = iter f a (iter f b x) := by
  induction a with
  | zero => simp [iter]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [iter, ih]

theorem iter_oneLip (hf : IsOneLipschitz f) (w k x y : Nat)
    (hxy : x % 2 ^ w = y % 2 ^ w) :
    iter f k x % 2 ^ w = iter f k y % 2 ^ w := by
  induction k with
  | zero => exact hxy
  | succ k ih => exact hf w _ _ ih

theorem testBit_eq_div_mod (x w : Nat) :
    x.testBit w = ((x / 2 ^ w) % 2 == 1) := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_comm, Nat.and_one_is_mod]
  have hlt : (x / 2 ^ w) % 2 < 2 := Nat.mod_lt _ (by decide)
  cases hmod : (x / 2 ^ w) % 2 with
  | zero => simp
  | succ k =>
    have hk : k = 0 := by omega
    subst hk
    simp

theorem mod_two_pow_succ_decomp (x w : Nat) :
    x % 2 ^ (w + 1) = x % 2 ^ w + if x.testBit w then 2 ^ w else 0 := by
  have hpos := two_pow_pos w
  have h2w := two_pow_succ_eq w
  have hdiv1 : x = 2 ^ w * (x / 2 ^ w) + x % 2 ^ w := (Nat.div_add_mod x (2 ^ w)).symm
  have hdiv2 : x / 2 ^ w = 2 * ((x / 2 ^ w) / 2) + (x / 2 ^ w) % 2 :=
    (Nat.div_add_mod (x / 2 ^ w) 2).symm
  have hlt1 : x % 2 ^ w < 2 ^ w := Nat.mod_lt x hpos
  have hlt2 : (x / 2 ^ w) % 2 < 2 := Nat.mod_lt _ (by decide)
  have h1 : x % 2 ^ (w + 1) = x % 2 ^ w + 2 ^ w * ((x / 2 ^ w) % 2) := by
    have hmul : 2 ^ w * (2 * ((x / 2 ^ w) / 2) + (x / 2 ^ w) % 2) =
        2 ^ (w + 1) * ((x / 2 ^ w) / 2) + 2 ^ w * ((x / 2 ^ w) % 2) := by
      rw [Nat.mul_add, ← Nat.mul_assoc, ← Nat.pow_succ]
    have hsplit : x = 2 ^ (w + 1) * ((x / 2 ^ w) / 2) + (x % 2 ^ w + 2 ^ w * ((x / 2 ^ w) % 2)) := by
      rw [hdiv2, hmul] at hdiv1; omega
    have hbound : x % 2 ^ w + 2 ^ w * ((x / 2 ^ w) % 2) < 2 ^ (w + 1) := by
      cases hq : (x / 2 ^ w) % 2 with
      | zero => simp; omega
      | succ k =>
        have hk : k = 0 := by omega
        subst hk; simp; omega
    calc x % 2 ^ (w + 1)
        = (2 ^ (w + 1) * ((x / 2 ^ w) / 2) + (x % 2 ^ w + 2 ^ w * ((x / 2 ^ w) % 2))) % 2 ^ (w + 1) :=
          congrArg (· % 2 ^ (w + 1)) hsplit
      _ = (x % 2 ^ w + 2 ^ w * ((x / 2 ^ w) % 2)) % 2 ^ (w + 1) := Nat.mul_add_mod _ _ _
      _ = x % 2 ^ w + 2 ^ w * ((x / 2 ^ w) % 2) := Nat.mod_eq_of_lt hbound
  rw [h1, testBit_eq_div_mod]
  cases hmod : (x / 2 ^ w) % 2 with
  | zero => simp
  | succ k =>
    have hk : k = 0 := by omega
    subst hk; simp

theorem testBit_add_two_pow_self (x w : Nat) :
    (x + 2 ^ w).testBit w = !x.testBit w := by
  rw [testBit_eq_div_mod, testBit_eq_div_mod]
  have hpos := two_pow_pos w
  rw [Nat.add_div_right x hpos]
  have hlt : (x / 2 ^ w) % 2 < 2 := Nat.mod_lt _ (by decide)
  rw [Nat.add_mod]
  cases hmod : (x / 2 ^ w) % 2 with
  | zero => decide
  | succ k =>
    have hk : k = 0 := by omega
    subst hk; decide

theorem mod_two_pow_succ_add_two_pow (x w : Nat) :
    (x + 2 ^ w) % 2 ^ (w + 1) =
      x % 2 ^ w + if !x.testBit w then 2 ^ w else 0 := by
  rw [mod_two_pow_succ_decomp (x + 2 ^ w) w, Nat.add_mod_right, testBit_add_two_pow_self]

theorem testBit_eq_of_mod_succ_eq {x y w : Nat}
    (h : x % 2 ^ (w + 1) = y % 2 ^ (w + 1)) : x.testBit w = y.testBit w := by
  have hx := mod_two_pow_succ_decomp x w
  have hy := mod_two_pow_succ_decomp y w
  have hlow : x % 2 ^ w = y % 2 ^ w := by
    have hd : 2 ^ w ∣ 2 ^ (w + 1) := Nat.pow_dvd_pow 2 (Nat.le_succ w)
    rw [← Nat.mod_mod_of_dvd x hd, ← Nat.mod_mod_of_dvd y hd, h]
  have hpos := two_pow_pos w
  cases hbx : x.testBit w <;> cases hby : y.testBit w <;> simp_all <;> omega

theorem unitDeriv_all (hf : IsOneLipschitz f) (hd : HasUnitSliceDeriv f w) (x : Nat) :
    f (x + 2 ^ w) % 2 ^ (w + 1) = (f x + 2 ^ w) % 2 ^ (w + 1) := by
  have hpos := two_pow_pos w
  have h2w := two_pow_succ_eq w
  have hr : x % 2 ^ w < 2 ^ w := Nat.mod_lt x hpos
  have hstep := hd (x % 2 ^ w) hr
  have h1 := mod_two_pow_succ_add_two_pow x w
  have h2 := mod_two_pow_succ_decomp x w
  cases hb : x.testBit w
  · rw [hb] at h1 h2
    simp only [Bool.not_false, ↓reduceIte, Bool.false_eq_true, Nat.add_zero] at h1 h2
    have hlt1 : x % 2 ^ w + 2 ^ w < 2 ^ (w + 1) := by omega
    have hlt2 : x % 2 ^ w < 2 ^ (w + 1) := by omega
    rw [hf (w + 1) (x + 2 ^ w) (x % 2 ^ w + 2 ^ w) (by rw [h1, Nat.mod_eq_of_lt hlt1])]
    rw [hstep]
    have hfx : f x % 2 ^ (w + 1) = f (x % 2 ^ w) % 2 ^ (w + 1) :=
      hf (w + 1) x (x % 2 ^ w) (by rw [h2, Nat.mod_eq_of_lt hlt2])
    rw [Nat.add_mod, ← hfx, ← Nat.add_mod]
  · rw [hb] at h1 h2
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h1 h2
    have hlt1 : x % 2 ^ w < 2 ^ (w + 1) := by omega
    have hlt2 : x % 2 ^ w + 2 ^ w < 2 ^ (w + 1) := by omega
    have hfx : f x % 2 ^ (w + 1) = f (x % 2 ^ w + 2 ^ w) % 2 ^ (w + 1) :=
      hf (w + 1) x (x % 2 ^ w + 2 ^ w) (by rw [h2, Nat.mod_eq_of_lt hlt2])
    have hfx2 : f (x + 2 ^ w) % 2 ^ (w + 1) = f (x % 2 ^ w) % 2 ^ (w + 1) :=
      hf (w + 1) (x + 2 ^ w) (x % 2 ^ w) (by rw [h1, Nat.mod_eq_of_lt hlt1])
    rw [hfx2, Nat.add_mod, hfx, hstep, ← Nat.add_mod]
    rw [Nat.add_assoc, ← h2w, Nat.add_mod_right]

theorem iter_add_two_pow (hf : IsOneLipschitz f) (hd : HasUnitSliceDeriv f w) (k x : Nat) :
    iter f k (x + 2 ^ w) % 2 ^ (w + 1) = (iter f k x + 2 ^ w) % 2 ^ (w + 1) := by
  induction k with
  | zero => simp [iter]
  | succ k ih =>
    simp only [iter]
    rw [hf (w + 1) _ _ ih]
    exact unitDeriv_all hf hd (iter f k x)

/-! ## Section 2: Finite Pigeonhole & Single-Cycle Characterizations -/

theorem fin_inj_surj : ∀ (n : Nat) (g : Nat → Nat),
    (∀ i < n, g i < n) →
    (∀ i j, i < n → j < n → g i = g j → i = j) →
    ∀ y < n, ∃ i < n, g i = y := by
  intro n
  induction n with
  | zero => intro _ _ _ y hy; omega
  | succ n ih =>
    intro g hlt hinj y hy
    by_cases hhit : ∃ i < n + 1, g i = n
    · obtain ⟨k, hk, hgk⟩ := hhit
      by_cases hyn : y = n
      · exact ⟨k, hk, hyn ▸ hgk⟩
      · have hyn' : y < n := by omega
        let g' : Nat → Nat := fun i => if i = k then g n else g i
        have hlt' : ∀ i < n, g' i < n := by
          intro i hi
          dsimp [g']
          split
          · rename_i hik
            have hne : n ≠ k := by omega
            have hgn_ne : g n ≠ n := fun hgn =>
              hne (hinj n k (Nat.lt_succ_self n) hk (hgn.trans hgk.symm))
            have hgn_lt := hlt n (Nat.lt_succ_self n)
            omega
          · rename_i hik
            have hgi_ne : g i ≠ n := fun hgi =>
              hik (hinj i k (by omega) hk (hgi.trans hgk.symm))
            have hgi_lt := hlt i (by omega)
            omega
        have hinj' : ∀ i j, i < n → j < n → g' i = g' j → i = j := by
          intro i j hi hj heq
          dsimp [g'] at heq
          split at heq <;> split at heq
          · omega
          · have := hinj n j (Nat.lt_succ_self n) (by omega) heq; omega
          · have := hinj i n (by omega) (Nat.lt_succ_self n) heq; omega
          · exact hinj i j (by omega) (by omega) heq
        obtain ⟨i, hi, hgi⟩ := ih g' hlt' hinj' y hyn'
        dsimp [g'] at hgi
        split at hgi
        · exact ⟨n, Nat.lt_succ_self n, hgi⟩
        · exact ⟨i, by omega, hgi⟩
    · have hlt' : ∀ i < n, g i < n := by
        intro i hi
        have h := hlt i (by omega)
        have hne : g i ≠ n := fun heq => hhit ⟨i, by omega, heq⟩
        omega
      have hinj' : ∀ i j, i < n → j < n → g i = g j → i = j :=
        fun i j hi hj h => hinj i j (by omega) (by omega) h
      have hgn_lt : g n < n := by
        have h := hlt n (Nat.lt_succ_self n)
        have hne : g n ≠ n := fun heq => hhit ⟨n, Nat.lt_succ_self n, heq⟩
        omega
      obtain ⟨i, hi, hgi⟩ := ih g hlt' hinj' (g n) hgn_lt
      have := hinj i n (by omega) (Nat.lt_succ_self n) hgi
      omega

theorem singleCycle_surj (hsc : IsSingleCycle f w) :
    ∀ r < 2 ^ w, ∃ k < 2 ^ w, iter f k 0 % 2 ^ w = r :=
  fin_inj_surj (2 ^ w) (fun k => iter f k 0 % 2 ^ w)
    (fun _ _ => Nat.mod_lt _ (two_pow_pos w)) hsc.distinct

theorem singleCycle_iff_no_early_return (hf : IsOneLipschitz f) (w : Nat) :
    IsSingleCycle f w ↔
      (iter f (2 ^ w) 0 % 2 ^ w = 0 ∧
       ∀ k, 0 < k → k < 2 ^ w → iter f k 0 % 2 ^ w ≠ 0) := by
  constructor
  · intro hsc
    refine ⟨hsc.period, fun k hk0 hkw heq => ?_⟩
    have := hsc.distinct k 0 hkw (two_pow_pos w) (by simpa [iter] using heq)
    omega
  · rintro ⟨hper, hno⟩
    refine ⟨hper, fun i j hi hj hij => ?_⟩
    by_cases hle : i ≤ j
    · by_cases heq : i = j
      · exact heq
      · have hstep := iter_oneLip hf w (2 ^ w - j) (iter f i 0) (iter f j 0) hij
        rw [← iter_add, ← iter_add] at hstep
        have hj1 : 2 ^ w - j + j = 2 ^ w := by omega
        rw [hj1, hper] at hstep
        exact absurd hstep (hno _ (by omega) (by omega))
    · have hstep := iter_oneLip hf w (2 ^ w - i) (iter f j 0) (iter f i 0) hij.symm
      rw [← iter_add, ← iter_add] at hstep
      have hi1 : 2 ^ w - i + i = 2 ^ w := by omega
      rw [hi1, hper] at hstep
      exact absurd hstep (hno _ (by omega) (by omega))

theorem singleCycle_bijective_mod (hf : IsOneLipschitz f) (hsc : IsSingleCycle f w) :
    ∀ x y, x < 2 ^ w → y < 2 ^ w → f x % 2 ^ w = f y % 2 ^ w → x = y := by
  intro x y hx hy hxy
  obtain ⟨ix, hix, hrx⟩ := singleCycle_surj hsc x hx
  obtain ⟨iy, hiy, hry⟩ := singleCycle_surj hsc y hy
  have h1 : iter f (ix + 1) 0 % 2 ^ w = f x % 2 ^ w := by
    simp only [iter]
    exact hf w _ _ (hrx.trans (Nat.mod_eq_of_lt hx).symm)
  have h2 : iter f (iy + 1) 0 % 2 ^ w = f y % 2 ^ w := by
    simp only [iter]
    exact hf w _ _ (hry.trans (Nat.mod_eq_of_lt hy).symm)
  have heq : iter f (ix + 1) 0 % 2 ^ w = iter f (iy + 1) 0 % 2 ^ w := by
    rw [h1, h2, hxy]
  have hmod_step : ∀ k < 2 ^ w, iter f (k + 1) 0 % 2 ^ w = iter f ((k + 1) % 2 ^ w) 0 % 2 ^ w := by
    intro k hk
    by_cases hlast : k + 1 = 2 ^ w
    · rw [hlast, Nat.mod_self, hsc.period]; simp [iter]
    · have hlt : (k + 1) % 2 ^ w = k + 1 := Nat.mod_eq_of_lt (by omega)
      rw [hlt]
  rw [hmod_step ix hix, hmod_step iy hiy] at heq
  have hidx := hsc.distinct ((ix + 1) % 2 ^ w) ((iy + 1) % 2 ^ w)
    (Nat.mod_lt _ (two_pow_pos w)) (Nat.mod_lt _ (two_pow_pos w)) heq
  have hixy : ix = iy := by
    by_cases h1l : ix + 1 = 2 ^ w <;> by_cases h2l : iy + 1 = 2 ^ w
    · omega
    · rw [h1l, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at hidx; omega
    · rw [h2l, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at hidx; omega
    · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hidx; omega
  rw [← hrx, ← hry, hixy]

theorem singleCycle_period_all (hf : IsOneLipschitz f) (hsc : IsSingleCycle f w) (x : Nat) :
    iter f (2 ^ w) x % 2 ^ w = x % 2 ^ w := by
  obtain ⟨k, _, hkx⟩ := singleCycle_surj hsc (x % 2 ^ w) (Nat.mod_lt _ (two_pow_pos w))
  rw [← hkx]
  rw [iter_oneLip hf w (2 ^ w) x (iter f k 0) hkx.symm]
  rw [← iter_add, Nat.add_comm, iter_add]
  exact iter_oneLip hf w k _ 0 hsc.period

theorem singleCycle_transitive (hf : IsOneLipschitz f) (hsc : IsSingleCycle f w) (x y : Nat) :
    ∃ k < 2 ^ w, iter f k x % 2 ^ w = y % 2 ^ w := by
  obtain ⟨kx, hkx, h1⟩ := singleCycle_surj hsc (x % 2 ^ w) (Nat.mod_lt _ (two_pow_pos w))
  obtain ⟨ky, hky, h2⟩ := singleCycle_surj hsc (y % 2 ^ w) (Nat.mod_lt _ (two_pow_pos w))
  by_cases hle : kx ≤ ky
  · refine ⟨ky - kx, by omega, ?_⟩
    rw [iter_oneLip hf w (ky - kx) x (iter f kx 0) h1.symm, ← iter_add]
    have : ky - kx + kx = ky := by omega
    rw [this, h2]
  · refine ⟨2 ^ w + ky - kx, by omega, ?_⟩
    rw [iter_oneLip hf w (2 ^ w + ky - kx) x (iter f kx 0) h1.symm, ← iter_add]
    have : 2 ^ w + ky - kx + kx = ky + 2 ^ w := by omega
    rw [this, iter_add, iter_oneLip hf w ky _ 0 hsc.period, h2]

/-! ## Section 3: Permutation Invariance for `bitXorSum` and `intSum` -/

theorem bitXorSum_congr {n : Nat} {g1 g2 : Nat → Bool}
    (h : ∀ i < n, g1 i = g2 i) : bitXorSum g1 n = bitXorSum g2 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [bitXorSum]
    rw [ih (fun i hi => h i (by omega)), h n (Nat.lt_succ_self n)]

theorem bitXorSum_update (g : Nat → Bool) (n k : Nat) (hk : k < n) (v : Bool) :
    bitXorSum (fun i => if i = k then v else g i) n =
      xor (xor (bitXorSum g n) (g k)) v := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [bitXorSum]
    by_cases hkn : k = n
    · rw [hkn]
      simp only [↓reduceIte]
      have hcongr : bitXorSum (fun i => if i = n then v else g i) n = bitXorSum g n := by
        apply bitXorSum_congr
        intro i hi
        have : i ≠ n := by omega
        simp [this]
      rw [hcongr]
      cases bitXorSum g n <;> cases g n <;> cases v <;> decide
    · have hlt : k < n := by omega
      have hne : n ≠ k := by omega
      simp only [hne, ↓reduceIte]
      rw [ih hlt]
      cases bitXorSum g n <;> cases g k <;> cases v <;> cases g n <;> decide

theorem bitXorSum_perm : ∀ (n : Nat) (p : Nat → Nat) (g : Nat → Bool),
    (∀ i < n, p i < n) →
    (∀ i j, i < n → j < n → p i = p j → i = j) →
    bitXorSum (fun i => g (p i)) n = bitXorSum g n := by
  intro n
  induction n with
  | zero => intro _ _ _ _; rfl
  | succ n ih =>
    intro p g hlt hinj
    obtain ⟨k, hk, hpk⟩ := fin_inj_surj (n + 1) p hlt hinj n (Nat.lt_succ_self n)
    by_cases hkn : k = n
    · rw [hkn] at hpk
      simp only [bitXorSum, hpk]
      congr 1
      apply ih p g
      · intro i hi
        have hpi := hlt i (by omega)
        have hne : p i ≠ n := fun heq => by
          have := hinj i n (by omega) (Nat.lt_succ_self n) (heq.trans hpk.symm)
          omega
        omega
      · intro i j hi hj h; exact hinj i j (by omega) (by omega) h
    · have hklt : k < n := by omega
      let p' : Nat → Nat := fun i => if i = k then p n else p i
      have hlt' : ∀ i < n, p' i < n := by
        intro i hi
        dsimp [p']
        split
        · have hpn := hlt n (Nat.lt_succ_self n)
          have hne : p n ≠ n := fun heq => hkn (hinj k n hk (Nat.lt_succ_self n) (hpk.trans heq.symm))
          omega
        · rename_i hik
          have hpi := hlt i (by omega)
          have hne : p i ≠ n := fun heq => hik (hinj i k (by omega) hk (heq.trans hpk.symm))
          omega
      have hinj' : ∀ i j, i < n → j < n → p' i = p' j → i = j := by
        intro i j hi hj heq
        dsimp [p'] at heq
        split at heq <;> split at heq
        · omega
        · have := hinj n j (Nat.lt_succ_self n) (by omega) heq; omega
        · have := hinj i n (by omega) (Nat.lt_succ_self n) heq; omega
        · exact hinj i j (by omega) (by omega) heq
      have hsub := ih p' g hlt' hinj'
      have hupd : bitXorSum (fun i => g (p' i)) n =
          xor (xor (bitXorSum (fun i => g (p i)) n) (g (p k))) (g (p n)) := by
        have h1 : (fun i => g (p' i)) = (fun i => if i = k then g (p n) else g (p i)) := by
          funext i; dsimp [p']; split <;> rfl
        rw [h1]
        exact bitXorSum_update (fun i => g (p i)) n k hklt (g (p n))
      rw [hupd, hpk] at hsub
      simp only [bitXorSum]
      rw [← hsub]
      cases bitXorSum (fun i => g (p i)) n <;> cases g n <;> cases g (p n) <;> decide

theorem intSum_congr {n : Nat} {g1 g2 : Nat → Int}
    (h : ∀ i < n, g1 i = g2 i) : intSum g1 n = intSum g2 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [intSum]
    rw [ih (fun i hi => h i (by omega)), h n (Nat.lt_succ_self n)]

theorem intSum_update (g : Nat → Int) (n k : Nat) (hk : k < n) (v : Int) :
    intSum (fun i => if i = k then v else g i) n =
      intSum g n - g k + v := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [intSum]
    by_cases hkn : k = n
    · rw [hkn]
      simp only [↓reduceIte]
      have hcongr : intSum (fun i => if i = n then v else g i) n = intSum g n := by
        apply intSum_congr
        intro i hi
        have : i ≠ n := by omega
        simp [this]
      rw [hcongr]; omega
    · have hlt : k < n := by omega
      have hne : n ≠ k := by omega
      simp only [hne, ↓reduceIte]
      rw [ih hlt]; omega

theorem intSum_perm : ∀ (n : Nat) (p : Nat → Nat) (g : Nat → Int),
    (∀ i < n, p i < n) →
    (∀ i j, i < n → j < n → p i = p j → i = j) →
    intSum (fun i => g (p i)) n = intSum g n := by
  intro n
  induction n with
  | zero => intro _ _ _ _; rfl
  | succ n ih =>
    intro p g hlt hinj
    obtain ⟨k, hk, hpk⟩ := fin_inj_surj (n + 1) p hlt hinj n (Nat.lt_succ_self n)
    by_cases hkn : k = n
    · rw [hkn] at hpk
      simp only [intSum, hpk]
      congr 1
      apply ih p g
      · intro i hi
        have hpi := hlt i (by omega)
        have hne : p i ≠ n := fun heq => by
          have := hinj i n (by omega) (Nat.lt_succ_self n) (heq.trans hpk.symm)
          omega
        omega
      · intro i j hi hj h; exact hinj i j (by omega) (by omega) h
    · have hklt : k < n := by omega
      let p' : Nat → Nat := fun i => if i = k then p n else p i
      have hlt' : ∀ i < n, p' i < n := by
        intro i hi
        dsimp [p']
        split
        · have hpn := hlt n (Nat.lt_succ_self n)
          have hne : p n ≠ n := fun heq => hkn (hinj k n hk (Nat.lt_succ_self n) (hpk.trans heq.symm))
          omega
        · rename_i hik
          have hpi := hlt i (by omega)
          have hne : p i ≠ n := fun heq => hik (hinj i k (by omega) hk (heq.trans hpk.symm))
          omega
      have hinj' : ∀ i j, i < n → j < n → p' i = p' j → i = j := by
        intro i j hi hj heq
        dsimp [p'] at heq
        split at heq <;> split at heq
        · omega
        · have := hinj n j (Nat.lt_succ_self n) (by omega) heq; omega
        · have := hinj i n (by omega) (Nat.lt_succ_self n) heq; omega
        · exact hinj i j (by omega) (by omega) heq
      have hsub := ih p' g hlt' hinj'
      have hupd : intSum (fun i => g (p' i)) n =
          intSum (fun i => g (p i)) n - g (p k) + g (p n) := by
        have h1 : (fun i => g (p' i)) = (fun i => if i = k then g (p n) else g (p i)) := by
          funext i; dsimp [p']; split <;> rfl
        rw [h1]
        exact intSum_update (fun i => g (p i)) n k hklt (g (p n))
      rw [hupd, hpk] at hsub
      simp only [intSum]
      omega

/-! ## Section 4: Layer 1 — Exact Bit-Slice Doubling Theorem -/

theorem orbit_bit_cocycle (hf : IsOneLipschitz f) (hd : HasUnitSliceDeriv f w) (k : Nat) :
    (iter f k 0).testBit w =
      bitXorSum (fun j => (f (iter f j 0 % 2 ^ w)).testBit w) k := by
  have hpos := two_pow_pos w
  have h2w := two_pow_succ_eq w
  induction k with
  | zero => simp [iter, bitXorSum]
  | succ k ih =>
    simp only [iter, bitXorSum]
    have hlt := Nat.mod_lt (iter f k 0) hpos
    have hx_decomp := mod_two_pow_succ_decomp (iter f k 0) w
    have hfx : f (iter f k 0) % 2 ^ (w + 1) =
        f (iter f k 0 % 2 ^ w + if (iter f k 0).testBit w then 2 ^ w else 0) % 2 ^ (w + 1) := by
      apply hf (w + 1)
      have hlt_sum : iter f k 0 % 2 ^ w + (if (iter f k 0).testBit w then 2 ^ w else 0) < 2 ^ (w + 1) := by
        cases (iter f k 0).testBit w <;> simp <;> omega
      rw [hx_decomp, Nat.mod_eq_of_lt hlt_sum]
    have hbit_eq : (f (iter f k 0)).testBit w =
        (f (iter f k 0 % 2 ^ w + if (iter f k 0).testBit w then 2 ^ w else 0)).testBit w :=
      testBit_eq_of_mod_succ_eq hfx
    rw [hbit_eq]
    cases hb : (iter f k 0).testBit w
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      have hsum : bitXorSum (fun j => (f (iter f j 0 % 2 ^ w)).testBit w) k = false :=
        ih.symm.trans hb
      rw [hsum]; simp
    · simp only [↓reduceIte]
      have hstep := hd (iter f k 0 % 2 ^ w) hlt
      have hbit2 : (f (iter f k 0 % 2 ^ w + 2 ^ w)).testBit w =
          !(f (iter f k 0 % 2 ^ w)).testBit w := by
        rw [testBit_eq_of_mod_succ_eq hstep, testBit_add_two_pow_self]
      rw [hbit2]
      have hsum : bitXorSum (fun j => (f (iter f j 0 % 2 ^ w)).testBit w) k = true :=
        ih.symm.trans hb
      rw [hsum]
      cases (f (iter f k 0 % 2 ^ w)).testBit w <;> decide

theorem orbit_period_bit_eq_holonomy (hf : IsOneLipschitz f)
    (hsc : IsSingleCycle f w) (hd : HasUnitSliceDeriv f w) :
    (iter f (2 ^ w) 0).testBit w = holonomy f w := by
  rw [orbit_bit_cocycle hf hd (2 ^ w)]
  exact bitXorSum_perm (2 ^ w) (fun j => iter f j 0 % 2 ^ w) (fun r => (f r).testBit w)
    (fun _ _ => Nat.mod_lt _ (two_pow_pos w)) hsc.distinct

theorem singleCycle_pred_and_deriv (hf : IsOneLipschitz f) (hsc : IsSingleCycle f (w + 1)) :
    IsSingleCycle f w ∧ HasUnitSliceDeriv f w := by
  have hpos := two_pow_pos w
  have h2w := two_pow_succ_eq w
  have hd : HasUnitSliceDeriv f w := by
    intro r hr
    have hbij := singleCycle_bijective_mod hf hsc
    have hlow : f (r + 2 ^ w) % 2 ^ w = f r % 2 ^ w := by apply hf w; simp
    have h1 := mod_two_pow_succ_decomp (f (r + 2 ^ w)) w
    have h2 := mod_two_pow_succ_add_two_pow (f r) w
    have hne : f (r + 2 ^ w) % 2 ^ (w + 1) ≠ f r % 2 ^ (w + 1) := fun heq => by
      have := hbij (r + 2 ^ w) r (by omega) (by omega) heq
      omega
    have h3 := mod_two_pow_succ_decomp (f r) w
    rw [h1, h2, hlow]
    cases hb1 : (f (r + 2 ^ w)).testBit w <;> cases hb2 : (f r).testBit w <;> simp_all
  refine ⟨?_, hd⟩
  have hno : ∀ k, 0 < k → k < 2 ^ w → iter f k 0 % 2 ^ w ≠ 0 := by
    intro k hk0 hkw heq
    have hdecomp := mod_two_pow_succ_decomp (iter f k 0) w
    rw [heq, Nat.zero_add] at hdecomp
    cases hb : (iter f k 0).testBit w
    · rw [hb] at hdecomp
      simp only [Bool.false_eq_true, ↓reduceIte] at hdecomp
      exact ((singleCycle_iff_no_early_return hf (w + 1)).mp hsc).2 k hk0 (by omega) hdecomp
    · rw [hb] at hdecomp
      simp only [↓reduceIte] at hdecomp
      have h2k : iter f (k + k) 0 % 2 ^ (w + 1) = 0 := by
        rw [iter_add]
        rw [iter_oneLip hf (w + 1) k (iter f k 0) (0 + 2 ^ w) (by
          rw [hdecomp, Nat.zero_add, Nat.mod_eq_of_lt (by omega)])]
        rw [iter_add_two_pow hf hd k 0]
        have hlt2w : 2 ^ w % 2 ^ (w + 1) = 2 ^ w := Nat.mod_eq_of_lt (by omega)
        rw [Nat.add_mod, hdecomp, hlt2w, ← h2w, Nat.mod_self]
      exact ((singleCycle_iff_no_early_return hf (w + 1)).mp hsc).2 (k + k) (by omega) (by omega) h2k
  rw [singleCycle_iff_no_early_return hf w]
  refine ⟨?_, hno⟩
  have hbij_w : ∀ x y, x < 2 ^ w → y < 2 ^ w → f x % 2 ^ w = f y % 2 ^ w → x = y := by
    intro x y hx hy hxy
    have hfx := mod_two_pow_succ_decomp (f x) w
    have hfy := mod_two_pow_succ_decomp (f y) w
    have hfx2 := mod_two_pow_succ_add_two_pow (f x) w
    have hstep := hd x hx
    have hbij1 := singleCycle_bijective_mod hf hsc
    by_cases hb : (f x).testBit w = (f y).testBit w
    · exact hbij1 x y (by omega) (by omega) (by rw [hfx, hfy, hxy, hb])
    · have heq : f (x + 2 ^ w) % 2 ^ (w + 1) = f y % 2 ^ (w + 1) := by
        rw [hstep, hfx2, hfy, hxy]
        cases h1 : (f x).testBit w <;> cases h2 : (f y).testBit w <;> simp_all
      have := hbij1 (x + 2 ^ w) y (by omega) (by omega) heq
      omega
  have hdist : ∀ i j, i < 2 ^ w → j < 2 ^ w →
      iter f i 0 % 2 ^ w = iter f j 0 % 2 ^ w → i = j := by
    suffices ∀ m i j, i + j ≤ m → i < 2 ^ w → j < 2 ^ w →
        iter f i 0 % 2 ^ w = iter f j 0 % 2 ^ w → i = j by
      intro i j hi hj hij; exact this (i + j) i j (Nat.le_refl _) hi hj hij
    intro m
    induction m with
    | zero => intro i j hm _ _ _; omega
    | succ m ih =>
      intro i j hm hi hj hij
      cases i with
      | zero =>
        cases j with
        | zero => rfl
        | succ j' =>
          simp only [iter, Nat.zero_mod] at hij
          exact absurd hij.symm (hno (j' + 1) (by omega) hj)
      | succ i' =>
        cases j with
        | zero =>
          simp only [iter, Nat.zero_mod] at hij
          exact absurd hij (hno (i' + 1) (by omega) hi)
        | succ j' =>
          simp only [iter] at hij
          have hprev : iter f i' 0 % 2 ^ w = iter f j' 0 % 2 ^ w := by
            apply hbij_w _ _ (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos)
            have h1 := hf w (iter f i' 0 % 2 ^ w) (iter f i' 0) (Nat.mod_mod _ _)
            have h2 := hf w (iter f j' 0 % 2 ^ w) (iter f j' 0) (Nat.mod_mod _ _)
            rw [h1, h2, hij]
          have := ih i' j' (by omega) (by omega) (by omega) hprev
          omega
  obtain ⟨j, hj, hjeq⟩ := fin_inj_surj (2 ^ w) (fun k => iter f k 0 % 2 ^ w)
    (fun _ _ => Nat.mod_lt _ hpos) hdist (iter f (2 ^ w) 0 % 2 ^ w) (Nat.mod_lt _ hpos)
  cases j with
  | zero => simpa [iter] using hjeq.symm
  | succ j' =>
    have hstep_eq : iter f (2 ^ w) 0 = f (iter f (2 ^ w - 1) 0) := by
      have hpow : 2 ^ w = (2 ^ w - 1) + 1 := by omega
      exact congrArg (fun m => iter f m 0) hpow
    have hstep : iter f (2 ^ w - 1) 0 % 2 ^ w = iter f j' 0 % 2 ^ w := by
      apply hbij_w _ _ (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos)
      have h1 := hf w (iter f (2 ^ w - 1) 0 % 2 ^ w) (iter f (2 ^ w - 1) 0) (Nat.mod_mod _ _)
      have h2 := hf w (iter f j' 0 % 2 ^ w) (iter f j' 0) (Nat.mod_mod _ _)
      rw [h1, h2, ← hstep_eq]
      exact hjeq.symm
    have := hdist (2 ^ w - 1) j' (by omega) (by omega) hstep
    omega

/-- **THEOREM 1 (Layer 1 — Exact Bit-Slice Doubling Criterion):**
For any 1-Lipschitz T-function `f` that is single-cycle mod `2^w`,
`f` lifts to single-cycle mod `2^(w+1)` if and only if it has unit bit-slice derivative
at `w` and odd bit-slice holonomy at `w`. -/
theorem singleCycle_succ_iff (hf : IsOneLipschitz f) (hsc : IsSingleCycle f w) :
    IsSingleCycle f (w + 1) ↔ HasUnitSliceDeriv f w ∧ holonomy f w = true := by
  have hpos := two_pow_pos w
  have h2w := two_pow_succ_eq w
  constructor
  · intro hsc1
    have ⟨_, hd⟩ := singleCycle_pred_and_deriv hf hsc1
    refine ⟨hd, ?_⟩
    have hbit := orbit_period_bit_eq_holonomy hf hsc hd
    have hdecomp := mod_two_pow_succ_decomp (iter f (2 ^ w) 0) w
    rw [hsc.period, Nat.zero_add, hbit] at hdecomp
    have hno := ((singleCycle_iff_no_early_return hf (w + 1)).mp hsc1).2
    have hne := hno (2 ^ w) hpos (by omega)
    cases hhol : holonomy f w
    · rw [hhol] at hdecomp; simp at hdecomp; exact absurd hdecomp hne
    · rfl
  · rintro ⟨hd, hhol⟩
    rw [singleCycle_iff_no_early_return hf (w + 1)]
    have hbit := orbit_period_bit_eq_holonomy hf hsc hd
    have hmid : iter f (2 ^ w) 0 % 2 ^ (w + 1) = 2 ^ w := by
      rw [mod_two_pow_succ_decomp, hsc.period, hbit, hhol]; simp
    constructor
    · have hiter2 : iter f (2 ^ (w + 1)) 0 = iter f (2 ^ w) (iter f (2 ^ w) 0) := by
        rw [h2w, iter_add]
      rw [hiter2]
      rw [iter_oneLip hf (w + 1) (2 ^ w) (iter f (2 ^ w) 0) (0 + 2 ^ w) (by
        rw [hmid, Nat.zero_add, Nat.mod_eq_of_lt (by omega)])]
      rw [iter_add_two_pow hf hd (2 ^ w) 0]
      have hlt2w : 2 ^ w % 2 ^ (w + 1) = 2 ^ w := Nat.mod_eq_of_lt (by omega)
      rw [Nat.add_mod, hmid, hlt2w, ← h2w, Nat.mod_self]
    · intro k hk0 hkw heq
      by_cases hkeq : k = 2 ^ w
      · rw [hkeq, hmid] at heq; omega
      · have hmodw : iter f k 0 % 2 ^ w = 0 := by
          have hdvd : 2 ^ w ∣ 2 ^ (w + 1) := Nat.pow_dvd_pow 2 (Nat.le_succ w)
          rw [← Nat.mod_mod_of_dvd _ hdvd, heq, Nat.zero_mod]
        by_cases hlt : k < 2 ^ w
        · exact ((singleCycle_iff_no_early_return hf w).mp hsc).2 k hk0 hlt hmodw
        · have hk' : 0 < k - 2 ^ w ∧ k - 2 ^ w < 2 ^ w := by omega
          have hshift : iter f k 0 % 2 ^ w = iter f (k - 2 ^ w) 0 % 2 ^ w := by
            have hkadd : iter f k 0 = iter f (k - 2 ^ w) (iter f (2 ^ w) 0) := by
              have hk_eq : k = (k - 2 ^ w) + 2 ^ w := by omega
              exact (congrArg (fun m => iter f m 0) hk_eq).trans (iter_add f (k - 2 ^ w) (2 ^ w) 0)
            rw [hkadd]
            exact iter_oneLip hf w (k - 2 ^ w) _ 0 hsc.period
          rw [hshift] at hmodw
          exact ((singleCycle_iff_no_early_return hf w).mp hsc).2 (k - 2 ^ w) hk'.1 hk'.2 hmodw

theorem singleCycle_of_ge (hf : IsOneLipschitz f) {w1 w2 : Nat}
    (hle : w1 ≤ w2) (hsc : IsSingleCycle f w2) : IsSingleCycle f w1 := by
  induction hle with
  | refl => exact hsc
  | step _ ih => exact ih (singleCycle_pred_and_deriv hf hsc).1

/-! ## Section 5: Layer 2 — Universal Curvature-Holonomy Transport Law -/

theorem intSum_add (g1 g2 : Nat → Int) (n : Nat) :
    intSum (fun i => g1 i + g2 i) n = intSum g1 n + intSum g2 n := by
  induction n with
  | zero => simp [intSum]
  | succ n ih => simp only [intSum, ih]; omega

theorem intSum_sub (g1 g2 : Nat → Int) (n : Nat) :
    intSum (fun i => g1 i - g2 i) n = intSum g1 n - intSum g2 n := by
  induction n with
  | zero => simp [intSum]
  | succ n ih => simp only [intSum, ih]; omega

theorem intSum_const_mul (c : Int) (g : Nat → Int) (n : Nat) :
    intSum (fun i => c * g i) n = c * intSum g n := by
  induction n with
  | zero => simp [intSum]
  | succ n ih => simp only [intSum, ih]; rw [Int.mul_add]

theorem intSum_split (g : Nat → Int) (a b : Nat) :
    intSum g (a + b) = intSum g a + intSum (fun i => g (a + i)) b := by
  induction b with
  | zero => simp [intSum]
  | succ b ih =>
    rw [Nat.add_succ]
    simp only [intSum, ih]
    omega

theorem intSum_double (g : Nat → Int) (n : Nat) :
    intSum g (n + n) = intSum (fun i => g i + g (i + n)) n := by
  rw [intSum_split, intSum_add]
  congr 1
  apply intSum_congr
  intro i _
  rw [Nat.add_comm]

theorem intSum_mod_congr {n : Nat} {m : Int} {g1 g2 : Nat → Int}
    (h : ∀ i < n, g1 i % m = g2 i % m) :
    intSum g1 n % m = intSum g2 n % m := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [intSum]
    rw [Int.add_emod, ih (fun i hi => h i (by omega)), h n (Nat.lt_succ_self n), ← Int.add_emod]

private theorem bool_xor_int_mod2 (b1 b2 : Bool) :
    ((if b1 then (1 : Int) else 0) + (if b2 then (1 : Int) else 0) % 2) % 2 =
      if xor b1 b2 then 1 else 0 := by
  cases b1 <;> cases b2 <;> decide

theorem intSum_bool_mod2 (g : Nat → Bool) (n : Nat) :
    intSum (fun i => if g i then (1 : Int) else 0) n % 2 =
      if bitXorSum g n then 1 else 0 := by
  induction n with
  | zero => simp [intSum, bitXorSum]
  | succ n ih =>
    simp only [intSum, bitXorSum]
    rw [Int.add_emod, ih]
    exact bool_xor_int_mod2 (bitXorSum g n) (g n)

theorem int_mul_emod_mul_pos {c : Int} (hc : 0 < c) (a b : Int) (hb : 0 < b) :
    (c * a) % (c * b) = c * (a % b) := by
  have h1 : b * (a / b) + a % b = a := by
    have := Int.emod_def a b
    omega
  have hlt1 := Int.emod_nonneg a (by omega : b ≠ 0)
  have hlt2 := Int.emod_lt_of_pos a hb
  have hsplit : c * a = (c * b) * (a / b) + c * (a % b) := by
    have : c * a = c * (b * (a / b) + a % b) := by rw [h1]
    rw [this, Int.mul_add, ← Int.mul_assoc]
  have hnn : 0 ≤ c * (a % b) := Int.mul_nonneg (by omega) hlt1
  have hub : c * (a % b) < c * b := Int.mul_lt_mul_of_pos_left hlt2 hc
  calc (c * a) % (c * b)
      = ((c * b) * (a / b) + c * (a % b)) % (c * b) := congrArg (· % (c * b)) hsplit
    _ = (c * (a % b)) % (c * b) := Int.mul_add_emod_self_left _ _ _
    _ = c * (a % b) := Int.emod_eq_of_lt hnn hub

theorem natCast_two_pow (w : Nat) : ((2 ^ w : Nat) : Int) = (2 : Int) ^ w := by
  induction w with
  | zero => rfl
  | succ w ih =>
    rw [Nat.pow_succ, Int.pow_succ, Int.natCast_mul, ih]
    rfl

/-- Exact Sum-Holonomy Equivalence: when `f` is single-cycle mod `2^w`, the integer defect sum
`∑_{r < 2^w} (f(r) - r)` mod `2^(w+1)` equals `2^w` iff `holonomy f w = true` (else `0`). -/
theorem defectSum_mod_eq_holonomy (hf : IsOneLipschitz f) (hsc : IsSingleCycle f w) :
    defectSum f w % (2 ^ (w + 1) : Int) = if holonomy f w then (2 ^ w : Int) else 0 := by
  unfold defectSum
  have hmod : intSum (fun r => (f r : Int) - (r : Int)) (2 ^ w) % (2 ^ (w + 1) : Int) =
      intSum (fun r => ((f r % 2 ^ w : Nat) : Int) +
        (2 ^ w : Int) * (if (f r).testBit w then 1 else 0) - (r : Int)) (2 ^ w) % (2 ^ (w + 1) : Int) := by
    apply intSum_mod_congr
    intro r _
    have hdecomp := mod_two_pow_succ_decomp (f r) w
    have hcast_mod : ((f r % 2 ^ (w + 1) : Nat) : Int) = (f r : Int) % (2 ^ (w + 1) : Int) := by
      rw [Int.natCast_emod, natCast_two_pow]
    have hsub : ((f r : Int) - (r : Int)) % (2 ^ (w + 1) : Int) =
        (((f r % 2 ^ (w + 1) : Nat) : Int) - (r : Int)) % (2 ^ (w + 1) : Int) := by
      have hmod2 : ((f r % 2 ^ (w + 1) : Nat) : Int) % (2 ^ (w + 1) : Int) =
          (f r : Int) % (2 ^ (w + 1) : Int) := by
        rw [hcast_mod, Int.emod_emod]
      rw [Int.sub_emod, ← hmod2, ← Int.sub_emod]
    rw [hsub, hdecomp]
    congr 1
    cases (f r).testBit w
    · simp
    · simp [Int.natCast_add]
  rw [hmod]
  have hrew : (fun r => ((f r % 2 ^ w : Nat) : Int) +
      (2 ^ w : Int) * (if (f r).testBit w then 1 else 0) - (r : Int)) =
      (fun r => (((f r % 2 ^ w : Nat) : Int) - (r : Int)) +
        (2 ^ w : Int) * (if (f r).testBit w then 1 else 0)) := by
    funext r; omega
  rw [hrew, intSum_add, intSum_sub, intSum_const_mul]
  have hperm : intSum (fun r => ((f r % 2 ^ w : Nat) : Int)) (2 ^ w) =
      intSum (fun r => (r : Int)) (2 ^ w) :=
    intSum_perm (2 ^ w) (fun r => f r % 2 ^ w) (fun r => (r : Int))
      (fun _ _ => Nat.mod_lt _ (two_pow_pos w)) (singleCycle_bijective_mod hf hsc)
  rw [hperm, Int.sub_self, Int.zero_add]
  have h2w : (2 ^ (w + 1) : Int) = (2 ^ w : Int) * 2 := by
    rw [Int.pow_succ]
  have hpos_i : (0 : Int) < 2 ^ w := by
    rw [← natCast_two_pow]; exact Int.natCast_pos.mpr (two_pow_pos w)
  rw [h2w, int_mul_emod_mul_pos hpos_i _ 2 (by decide), intSum_bool_mod2]
  unfold holonomy
  cases bitXorSum (fun r => (f r).testBit w) (2 ^ w) <;> simp

/-- **EXACT ALGEBRAIC CURVATURE TRANSPORT IDENTITY:**
For EVERY `f : Nat → Nat` and EVERY `w : Nat`:
`defectSum f (w + 1) = 2 * defectSum f w + curvatureSum f w`. -/
theorem defectSum_succ_eq (f : Nat → Nat) (w : Nat) :
    defectSum f (w + 1) = 2 * defectSum f w + curvatureSum f w := by
  unfold defectSum curvatureSum
  rw [two_pow_succ_eq w, intSum_double]
  have hrew : (fun r => ((f r : Int) - (r : Int)) + ((f (r + 2 ^ w) : Int) - ((r + 2 ^ w : Nat) : Int))) =
      (fun r => 2 * ((f r : Int) - (r : Int)) + ((f (r + 2 ^ w) : Int) - (f r : Int) - (2 ^ w : Int))) := by
    funext r
    have hcast : ((r + 2 ^ w : Nat) : Int) = (r : Int) + (2 ^ w : Int) := by
      rw [Int.natCast_add, natCast_two_pow]
    rw [hcast]
    omega
  rw [hrew, intSum_add, intSum_const_mul]

/-- **THEOREM 2 (Layer 2 — Curvature-Holonomy Transport Law):**
If `f` is 1-Lipschitz and single-cycle mod `2^(w+1)`, then its holonomy at `w + 1` is `true`
if and only if its curvature sum at `w` vanishes mod `2^(w+2)`. -/
theorem holonomy_succ_iff_curvatureSum_zero (hf : IsOneLipschitz f)
    (hsc1 : IsSingleCycle f (w + 1)) :
    holonomy f (w + 1) = true ↔ curvatureSum f w % (2 ^ (w + 2) : Int) = 0 := by
  have ⟨hsc0, _⟩ := singleCycle_pred_and_deriv hf hsc1
  have hhol0 : holonomy f w = true := ((singleCycle_succ_iff hf hsc0).mp hsc1).2
  have hdef1 := defectSum_mod_eq_holonomy hf hsc1
  have hdef0 := defectSum_mod_eq_holonomy hf hsc0
  rw [hhol0] at hdef0
  simp only [↓reduceIte] at hdef0
  have htrans := defectSum_succ_eq f w
  have hpos1 : (0 : Int) < 2 ^ (w + 1) := by
    rw [← natCast_two_pow]; exact Int.natCast_pos.mpr (two_pow_pos (w + 1))
  have hpow2 : (2 ^ (w + 2) : Int) = 2 * (2 ^ (w + 1) : Int) := by
    rw [Int.pow_succ, Int.mul_comm]
  have h2def0 : (2 * defectSum f w) % (2 ^ (w + 2) : Int) = (2 ^ (w + 1) : Int) := by
    rw [hpow2, int_mul_emod_mul_pos (by decide : (0 : Int) < 2) _ _ hpos1, hdef0]
    rw [Int.pow_succ, Int.mul_comm]
  have hdef1' : ((2 ^ (w + 1) : Int) + curvatureSum f w % (2 ^ (w + 2) : Int)) % (2 ^ (w + 2) : Int) =
      if holonomy f (w + 1) then (2 ^ (w + 1) : Int) else 0 := by
    have h := hdef1
    rw [htrans, Int.add_emod] at h
    exact h2def0 ▸ h
  have hmod_lt := Int.emod_nonneg (curvatureSum f w) (by omega : (2 ^ (w + 2) : Int) ≠ 0)
  have hmod_ub := Int.emod_lt_of_pos (curvatureSum f w) (by omega : (0 : Int) < 2 ^ (w + 2))
  cases hhol1 : holonomy f (w + 1)
  · simp only [hhol1, Bool.false_eq_true, ↓reduceIte] at hdef1'
    constructor
    · intro h; exact absurd h (by decide)
    · intro hcurv
      rw [hcurv, Int.add_zero, Int.emod_eq_of_lt (by omega) (by omega)] at hdef1'
      omega
  · simp only [hhol1, ↓reduceIte] at hdef1'
    constructor
    · intro _
      by_cases hzero : curvatureSum f w % (2 ^ (w + 2) : Int) = 0
      · exact hzero
      · by_cases hlt : curvatureSum f w % (2 ^ (w + 2) : Int) < (2 ^ (w + 1) : Int)
        · rw [Int.emod_eq_of_lt (by omega) (by omega)] at hdef1'; omega
        · have heq : ((2 ^ (w + 1) : Int) + curvatureSum f w % (2 ^ (w + 2) : Int)) % (2 ^ (w + 2) : Int) =
              curvatureSum f w % (2 ^ (w + 2) : Int) - (2 ^ (w + 1) : Int) := by
            have hsub : (2 ^ (w + 1) : Int) + curvatureSum f w % (2 ^ (w + 2) : Int) =
                (curvatureSum f w % (2 ^ (w + 2) : Int) - (2 ^ (w + 1) : Int)) + (2 ^ (w + 2) : Int) := by omega
            rw [hsub, Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]
          rw [heq] at hdef1'
          omega
    · intro _; rfl

/-! ## Section 6: Layer 3 — Reusable Finite-to-Infinite Lifting Engines -/

/-- **ENGINE 1 (Master Finite-to-Infinite Lifting Theorem):**
For ANY base threshold `w0 : Nat` (e.g. `w0 = 3`, i.e. finite check at `w = 4`),
a single finite single-cycle check `IsSingleCycle f (w0 + 1)`, together with
unit bit-slice derivative and vanishing curvature sum for all `w ≥ w0`,
lifts to full `2^w`-cycle ergodicity for ALL `w ≥ 1`. -/
theorem lift_singleCycle_from_curvatureSum {f : Nat → Nat} (w0 : Nat)
    (hf : IsOneLipschitz f)
    (hbase : IsSingleCycle f (w0 + 1))
    (hderiv : ∀ w, w0 ≤ w → HasUnitSliceDeriv f (w + 1))
    (hcurv : ∀ w, w0 ≤ w → curvatureSum f w % (2 ^ (w + 2) : Int) = 0) :
    ∀ w, 1 ≤ w → IsSingleCycle f w := by
  have hup : ∀ k, IsSingleCycle f (w0 + 1 + k) := by
    intro k
    induction k with
    | zero => exact hbase
    | succ k ih =>
      have hsc_step : IsSingleCycle f (w0 + k + 1) := by
        have : w0 + 1 + k = w0 + k + 1 := by omega
        exact this ▸ ih
      have hhol : holonomy f (w0 + k + 1) = true :=
        (holonomy_succ_iff_curvatureSum_zero hf hsc_step).mpr (hcurv (w0 + k) (by omega))
      have hd : HasUnitSliceDeriv f (w0 + k + 1) := hderiv (w0 + k) (by omega)
      have hnext : IsSingleCycle f (w0 + k + 2) :=
        (singleCycle_succ_iff hf hsc_step).mpr ⟨hd, hhol⟩
      have : w0 + k + 2 = w0 + 1 + (k + 1) := by omega
      exact this ▸ hnext
  intro w hw
  by_cases hle : w ≤ w0 + 1
  · exact singleCycle_of_ge hf hle hbase
  · have hk := hup (w - (w0 + 1))
    have : w0 + 1 + (w - (w0 + 1)) = w := by omega
    exact this ▸ hk

/-- Convenience `w ≤ 4` Specialization (`w0 = 3`): finite check at `w = 4` (mod 16) lifts to `∀ w ≥ 1`. -/
theorem lift_singleCycle_from_w4 {f : Nat → Nat}
    (hf : IsOneLipschitz f)
    (hbase : IsSingleCycle f 4)
    (hderiv : ∀ w, 3 ≤ w → HasUnitSliceDeriv f (w + 1))
    (hcurv : ∀ w, 3 ≤ w → curvatureSum f w % (2 ^ (w + 2) : Int) = 0) :
    ∀ w, 1 ≤ w → IsSingleCycle f w :=
  lift_singleCycle_from_curvatureSum 3 hf hbase hderiv hcurv

theorem int_emod_two_mul_of_emod_zero {a m : Int} (hm : 0 < m) (h : a % m = 0) :
    a % (2 * m) = 0 ∨ a % (2 * m) = m := by
  have h1 : a = m * (a / m) := by
    have := Int.emod_def a m
    omega
  have hq : (a / m) % 2 = 0 ∨ (a / m) % 2 = 1 := by
    have hnn := Int.emod_nonneg (a / m) (by decide : (2 : Int) ≠ 0)
    have hlt := Int.emod_lt_of_pos (a / m) (by decide : (0 : Int) < 2)
    omega
  have hmul : a % (2 * m) = m * ((a / m) % 2) := by
    rw [Int.mul_comm 2 m]
    calc a % (m * 2)
        = (m * (a / m)) % (m * 2) := congrArg (· % (m * 2)) h1
      _ = m * ((a / m) % 2) := int_mul_emod_mul_pos hm (a / m) 2 (by decide)
  rcases hq with h0 | h1'
  · left; rw [hmul, h0, Int.mul_zero]
  · right; rw [hmul, h1', Int.mul_one]

theorem curvatureTerm_mod_eq_bit (hd : HasUnitSliceDeriv f w) {r : Nat} (hr : r < 2 ^ w) :
    ((f (r + 2 ^ w) : Int) - (f r : Int) - (2 ^ w : Int)) % (2 ^ (w + 2) : Int) =
      (2 ^ (w + 1) : Int) * (if curvatureBit f w r then 1 else 0) := by
  have hstep := hd r hr
  have hdiv : ((f (r + 2 ^ w) : Int) - (f r : Int) - (2 ^ w : Int)) % (2 ^ (w + 1) : Int) = 0 := by
    have hcast1 : ((f (r + 2 ^ w) % 2 ^ (w + 1) : Nat) : Int) = (f (r + 2 ^ w) : Int) % (2 ^ (w + 1) : Int) := by
      rw [Int.natCast_emod, natCast_two_pow]
    have hcast2 : (((f r + 2 ^ w) % 2 ^ (w + 1) : Nat) : Int) = ((f r : Int) + (2 ^ w : Int)) % (2 ^ (w + 1) : Int) := by
      rw [Int.natCast_emod, Int.natCast_add, natCast_two_pow, natCast_two_pow]
    have heq_mod : (f (r + 2 ^ w) : Int) % (2 ^ (w + 1) : Int) =
        ((f r : Int) + (2 ^ w : Int)) % (2 ^ (w + 1) : Int) := by
      rw [← hcast1, ← hcast2, hstep]
    have hrew : (f (r + 2 ^ w) : Int) - (f r : Int) - (2 ^ w : Int) =
        (f (r + 2 ^ w) : Int) - ((f r : Int) + (2 ^ w : Int)) := by omega
    rw [hrew, Int.sub_emod, heq_mod, Int.sub_self, Int.zero_emod]
  have hpos1 : (0 : Int) < 2 ^ (w + 1) := by
    rw [← natCast_two_pow]; exact Int.natCast_pos.mpr (two_pow_pos (w + 1))
  have hpow2 : (2 ^ (w + 2) : Int) = 2 * (2 ^ (w + 1) : Int) := by
    rw [Int.pow_succ, Int.mul_comm]
  have hcases := int_emod_two_mul_of_emod_zero hpos1 hdiv
  rw [← hpow2] at hcases
  unfold curvatureBit
  rcases hcases with h0 | h1
  · rw [h0]
    have hne : ((0 : Int) == (2 ^ (w + 1) : Int)) = false := by
      cases h : ((0 : Int) == (2 ^ (w + 1) : Int))
      · rfl
      · have := beq_iff_eq.mp h; omega
    rw [hne]; simp
  · rw [h1]
    simp

/-- Exact Reduction of Curvature Sum mod `2^(w+2)` to Boolean XOR Sum of `curvatureBit`. -/
theorem curvatureSum_zero_iff_bitXorSum (hd : HasUnitSliceDeriv f w) :
    curvatureSum f w % (2 ^ (w + 2) : Int) = 0 ↔
      bitXorSum (curvatureBit f w) (2 ^ w) = false := by
  unfold curvatureSum
  have hmod : intSum (fun r => (f (r + 2 ^ w) : Int) - (f r : Int) - (2 ^ w : Int)) (2 ^ w) % (2 ^ (w + 2) : Int) =
      intSum (fun r => (2 ^ (w + 1) : Int) * (if curvatureBit f w r then 1 else 0)) (2 ^ w) % (2 ^ (w + 2) : Int) := by
    apply intSum_mod_congr
    intro r hr
    rw [curvatureTerm_mod_eq_bit hd hr]
    have hpos1 : (0 : Int) < 2 ^ (w + 1) := by
      rw [← natCast_two_pow]; exact Int.natCast_pos.mpr (two_pow_pos (w + 1))
    have hpow2 : (2 ^ (w + 2) : Int) = 2 * (2 ^ (w + 1) : Int) := by
      rw [Int.pow_succ, Int.mul_comm]
    cases curvatureBit f w r
    · simp
    · simp only [↓reduceIte, Int.mul_one]
      exact (Int.emod_eq_of_lt (by omega) (by omega)).symm
  rw [hmod, intSum_const_mul]
  have hpos1 : (0 : Int) < 2 ^ (w + 1) := by
    rw [← natCast_two_pow]; exact Int.natCast_pos.mpr (two_pow_pos (w + 1))
  have hpow2 : (2 ^ (w + 2) : Int) = (2 ^ (w + 1) : Int) * 2 := by
    rw [Int.pow_succ]
  rw [hpow2, int_mul_emod_mul_pos hpos1 _ 2 (by decide), intSum_bool_mod2]
  cases bitXorSum (curvatureBit f w) (2 ^ w) <;> simp <;> omega

/-! ### Boolean XOR-Sum Linearity & Fixed-Point-Free Involution Annihilator -/

theorem bitXorSum_xor (p q : Nat → Bool) (n : Nat) :
    bitXorSum (fun r => xor (p r) (q r)) n = xor (bitXorSum p n) (bitXorSum q n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [bitXorSum, ih]
    cases bitXorSum p n <;> cases bitXorSum q n <;> cases p n <;> cases q n <;> decide

theorem bitXorSum_const_false (n : Nat) :
    bitXorSum (fun _ => false) n = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [bitXorSum, ih]

def countTrue (s : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => countTrue s n + if s n then 1 else 0

theorem countTrue_zero_all_false {s : Nat → Bool} {n : Nat}
    (h : countTrue s n = 0) : ∀ i < n, s i = false := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    simp only [countTrue] at h
    intro i hi
    by_cases hin : i = n
    · rw [hin]
      cases hsn : s n
      · rfl
      · rw [hsn] at h; simp at h
    · apply ih _ i (by omega)
      cases hsn : s n <;> simp [hsn] at h <;> omega

theorem exists_true_of_countTrue_pos {s : Nat → Bool} {n : Nat}
    (h : 0 < countTrue s n) : ∃ k < n, s k = true := by
  induction n with
  | zero => simp [countTrue] at h
  | succ n ih =>
    simp only [countTrue] at h
    cases hsn : s n
    · rw [hsn] at h; simp at h
      obtain ⟨k, hk, hsk⟩ := ih h
      exact ⟨k, by omega, hsk⟩
    · exact ⟨n, Nat.lt_succ_self n, hsn⟩

theorem countTrue_congr {s1 s2 : Nat → Bool} {n : Nat}
    (h : ∀ i < n, s1 i = s2 i) : countTrue s1 n = countTrue s2 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [countTrue]
    rw [ih (fun i hi => h i (by omega)), h n (Nat.lt_succ_self n)]

theorem countTrue_clear_one {s : Nat → Bool} {n k : Nat}
    (hk : k < n) (hsk : s k = true) :
    countTrue (fun i => if i = k then false else s i) n + 1 = countTrue s n := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [countTrue]
    by_cases hkn : k = n
    · rw [hkn] at hsk ⊢
      simp only [↓reduceIte, hsk, Bool.false_eq_true]
      have hcongr : countTrue (fun i => if i = n then false else s i) n = countTrue s n := by
        apply countTrue_congr
        intro i hi
        have : i ≠ n := by omega
        simp [this]
      rw [hcongr]
    · have hlt : k < n := by omega
      have hne : n ≠ k := by omega
      simp only [hne, ↓reduceIte]
      have := ih hlt
      omega

/-- **ENGINE 2 (General Fixed-Point-Free Involution Annihilator):**
If `τ` is ANY fixed-point-free involution on `{0..n-1}` preserving `p`,
then `bitXorSum p n = false`. -/
theorem bitXorSum_eq_false_of_involution {n : Nat} {p : Nat → Bool} (τ : Nat → Nat)
    (hbound : ∀ i < n, τ i < n)
    (hinv : ∀ i < n, τ (τ i) = i)
    (hne : ∀ i < n, τ i ≠ i)
    (hpres : ∀ i < n, p (τ i) = p i) :
    bitXorSum p n = false := by
  suffices ∀ (m : Nat) (s : Nat → Bool),
      countTrue s n ≤ m →
      (∀ i < n, s i = true → s (τ i) = true) →
      bitXorSum (fun i => s i && p i) n = false by
    have h := this (countTrue (fun _ => true) n) (fun _ => true) (Nat.le_refl _) (fun _ _ _ => rfl)
    have hcongr : bitXorSum (fun i => true && p i) n = bitXorSum p n := by
      apply bitXorSum_congr; intro i _; simp
    exact hcongr ▸ h
  intro m
  induction m with
  | zero =>
    intro s hle _
    have hz : countTrue s n = 0 := by omega
    have hall := countTrue_zero_all_false hz
    have hcongr : bitXorSum (fun i => s i && p i) n = bitXorSum (fun _ => false) n := by
      apply bitXorSum_congr
      intro i hi
      rw [hall i hi]; rfl
    rw [hcongr, bitXorSum_const_false]
  | succ m ih =>
    intro s hle hs
    by_cases hpos : countTrue s n = 0
    · have hall := countTrue_zero_all_false hpos
      have hcongr : bitXorSum (fun i => s i && p i) n = bitXorSum (fun _ => false) n := by
        apply bitXorSum_congr
        intro i hi
        rw [hall i hi]; rfl
      rw [hcongr, bitXorSum_const_false]
    · obtain ⟨k, hk, hsk⟩ := exists_true_of_countTrue_pos (s := s) (n := n) (by omega)
      let j := τ k
      have hj : j < n := hbound k hk
      have hne_kj : j ≠ k := hne k hk
      have hsj : s j = true := hs k hk hsk
      have hp_eq : p j = p k := hpres k hk
      let s1 : Nat → Bool := fun i => if i = k then false else s i
      let s2 : Nat → Bool := fun i => if i = j then false else s1 i
      have hc1 : countTrue s1 n + 1 = countTrue s n := countTrue_clear_one hk hsk
      have hs1j : s1 j = true := by dsimp [s1]; simp [hne_kj, hsj]
      have hc2 : countTrue s2 n + 1 = countTrue s1 n := countTrue_clear_one hj hs1j
      have hs2_closed : ∀ i < n, s2 i = true → s2 (τ i) = true := by
        intro i hi hs2i
        dsimp [s2, s1] at hs2i ⊢
        have hij : i ≠ j := by intro h; subst h; simp at hs2i
        have hik : i ≠ k := by intro h; subst h; simp [hij] at hs2i
        have hsi : s i = true := by simpa [hij, hik] using hs2i
        have hti_ne_j : τ i ≠ j := by
          intro h
          have : i = k := by
            have := congrArg τ h
            rw [hinv i hi, hinv k hk] at this
            exact this
          exact hik this
        have hti_ne_k : τ i ≠ k := by
          intro h
          have : i = j := by
            have := congrArg τ h
            rw [hinv i hi] at this
            exact this
          exact hij this
        simp [hti_ne_j, hti_ne_k, hs i hi hsi]
      have hsub := ih s2 (by omega) hs2_closed
      have hupd1 : bitXorSum (fun i => s1 i && p i) n =
          xor (xor (bitXorSum (fun i => s i && p i) n) (s k && p k)) false := by
        have h1 : (fun i => s1 i && p i) = (fun i => if i = k then false else (s i && p i)) := by
          funext i; dsimp [s1]; split <;> simp
        rw [h1]
        exact bitXorSum_update (fun i => s i && p i) n k hk false
      have hupd2 : bitXorSum (fun i => s2 i && p i) n =
          xor (xor (bitXorSum (fun i => s1 i && p i) n) (s1 j && p j)) false := by
        have h2 : (fun i => s2 i && p i) = (fun i => if i = j then false else (s1 i && p i)) := by
          funext i; dsimp [s2]; split <;> simp
        rw [h2]
        exact bitXorSum_update (fun i => s1 i && p i) n j hj false
      rw [hupd2, hupd1, hsk, hs1j, hp_eq] at hsub
      generalize bitXorSum (fun i => s i && p i) n = b at hsub ⊢
      generalize p k = pk at hsub
      cases b <;> cases pk <;> simp_all

theorem curvatureSum_zero_of_involution {f : Nat → Nat} {w : Nat}
    (hd : HasUnitSliceDeriv f w) (τ : Nat → Nat)
    (hbound : ∀ i < 2 ^ w, τ i < 2 ^ w)
    (hinv : ∀ i < 2 ^ w, τ (τ i) = i)
    (hne : ∀ i < 2 ^ w, τ i ≠ i)
    (hpres : ∀ i < 2 ^ w, curvatureBit f w (τ i) = curvatureBit f w i) :
    curvatureSum f w % (2 ^ (w + 2) : Int) = 0 :=
  (curvatureSum_zero_iff_bitXorSum hd).mpr
    (bitXorSum_eq_false_of_involution τ hbound hinv hne hpres)

/-! ### Bit-Flip Involution Annihilator (`τ r = r ^^^ 2^j`) -/

theorem testBit_eq_false_of_lt_two_pow {x w i : Nat} (hx : x < 2 ^ w) (hi : w ≤ i) :
    x.testBit i = false := by
  rw [testBit_eq_div_mod]
  have hle : 2 ^ w ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hi
  have hdiv : x / 2 ^ i = 0 := Nat.div_eq_of_lt (by omega)
  rw [hdiv]; rfl

theorem lt_two_pow_of_testBit_false {x w : Nat} (h : ∀ i, w ≤ i → x.testBit i = false) :
    x < 2 ^ w := by
  have hmod : x % 2 ^ w = x := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow]
    by_cases hi : i < w
    · simp [hi]
    · simp [hi, h i (by omega)]
  rw [← hmod]
  exact Nat.mod_lt x (two_pow_pos w)

theorem xor_lt_two_pow {a b w : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    (a ^^^ b) < 2 ^ w := by
  apply lt_two_pow_of_testBit_false
  intro i hi
  rw [Nat.testBit_xor, testBit_eq_false_of_lt_two_pow ha hi, testBit_eq_false_of_lt_two_pow hb hi]
  rfl

/-- **ENGINE 2A (Bit-Flip Curvature Involution):**
If a Boolean predicate `p` on `{0..2^w-1}` is independent of ANY bit position `j < w`,
then its XOR-sum over `{0..2^w-1}` vanishes. -/
theorem bitXorSum_eq_false_of_bitflip {w j : Nat} (hj : j < w) {p : Nat → Bool}
    (hindep : ∀ r < 2 ^ w, p (r ^^^ 2 ^ j) = p r) :
    bitXorSum p (2 ^ w) = false := by
  have h2j_lt : 2 ^ j < 2 ^ w := Nat.pow_lt_pow_right (by decide) hj
  apply bitXorSum_eq_false_of_involution (fun r => r ^^^ 2 ^ j)
  · intro r hr; exact xor_lt_two_pow hr h2j_lt
  · intro r _; rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  · intro r _ heq
    have hbit := congrArg (fun x => x.testBit j) heq
    rw [Nat.testBit_xor, Nat.testBit_two_pow] at hbit
    simp at hbit
  · exact hindep

/-! ### Additive 2-Lipschitz Bit-Slice Derivative & Curvature Bit Formula -/

theorem hasUnitSliceDeriv_add_twoLip {g : Nat → Nat} {w : Nat}
    (hg : ∀ r < 2 ^ w, g (r + 2 ^ w) % 2 ^ (w + 1) = g r % 2 ^ (w + 1)) :
    HasUnitSliceDeriv (fun x => x + g x) w := by
  intro r hr
  dsimp only
  have hstep := hg r hr
  have hrew : (r + 2 ^ w) + g (r + 2 ^ w) = (r + g (r + 2 ^ w)) + 2 ^ w := by omega
  rw [hrew, Nat.add_mod, Nat.add_mod r (g (r + 2 ^ w)), hstep, ← Nat.add_mod r (g r), ← Nat.add_mod]

theorem curvatureBit_add_twoLip {g : Nat → Nat} {w r : Nat}
    (hg : g (r + 2 ^ w) % 2 ^ (w + 1) = g r % 2 ^ (w + 1)) :
    curvatureBit (fun x => x + g x) w r =
      xor ((g (r + 2 ^ w)).testBit (w + 1)) ((g r).testBit (w + 1)) := by
  unfold curvatureBit
  have hdiff : ((r + 2 ^ w + g (r + 2 ^ w) : Nat) : Int) - ((r + g r : Nat) : Int) - (2 ^ w : Int) =
      (g (r + 2 ^ w) : Int) - (g r : Int) := by
    rw [Int.natCast_add, Int.natCast_add, Int.natCast_add, natCast_two_pow]
    omega
  rw [hdiff]
  have h1 := mod_two_pow_succ_decomp (g (r + 2 ^ w)) (w + 1)
  have h2 := mod_two_pow_succ_decomp (g r) (w + 1)
  have hcast1 : ((g (r + 2 ^ w) % 2 ^ (w + 2) : Nat) : Int) =
      (g (r + 2 ^ w) : Int) % (2 ^ (w + 2) : Int) := by
    rw [Int.natCast_emod, natCast_two_pow]
  have hcast2 : ((g r % 2 ^ (w + 2) : Nat) : Int) =
      (g r : Int) % (2 ^ (w + 2) : Int) := by
    rw [Int.natCast_emod, natCast_two_pow]
  have hmod_diff : ((g (r + 2 ^ w) : Int) - (g r : Int)) % (2 ^ (w + 2) : Int) =
      (((g (r + 2 ^ w) % 2 ^ (w + 2) : Nat) : Int) - ((g r % 2 ^ (w + 2) : Nat) : Int)) % (2 ^ (w + 2) : Int) := by
    have hm1 : ((g (r + 2 ^ w) % 2 ^ (w + 2) : Nat) : Int) % (2 ^ (w + 2) : Int) =
        (g (r + 2 ^ w) : Int) % (2 ^ (w + 2) : Int) := by
      rw [hcast1, Int.emod_emod]
    have hm2 : ((g r % 2 ^ (w + 2) : Nat) : Int) % (2 ^ (w + 2) : Int) =
        (g r : Int) % (2 ^ (w + 2) : Int) := by
      rw [hcast2, Int.emod_emod]
    rw [Int.sub_emod, ← hm1, ← hm2, ← Int.sub_emod]
  rw [hmod_diff, h1, h2, hg]
  have hpos1 : (0 : Int) < 2 ^ (w + 1) := by
    rw [← natCast_two_pow]; exact Int.natCast_pos.mpr (two_pow_pos (w + 1))
  have hpow2 : (2 ^ (w + 2) : Int) = (2 ^ (w + 1) : Int) + (2 ^ (w + 1) : Int) := by
    rw [Int.pow_succ]; omega
  cases hb1 : (g (r + 2 ^ w)).testBit (w + 1) <;> cases hb2 : (g r).testBit (w + 1)
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Int.sub_self, Int.zero_emod, Bool.xor_false]
    cases h : ((0 : Int) == (2 ^ (w + 1) : Int))
    · rfl
    · have := beq_iff_eq.mp h; omega
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Int.natCast_add, natCast_two_pow, Bool.false_xor]
    have hsub : ((g r % 2 ^ (w + 1) : Nat) : Int) - (((g r % 2 ^ (w + 1) : Nat) : Int) + (2 ^ (w + 1) : Int)) =
        (2 ^ (w + 1) : Int) + (-1) * (2 ^ (w + 2) : Int) := by omega
    rw [hsub, Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by omega) (by omega)]
    simp
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Int.natCast_add, natCast_two_pow, Bool.true_xor]
    have hsub : (((g r % 2 ^ (w + 1) : Nat) : Int) + (2 ^ (w + 1) : Int)) - ((g r % 2 ^ (w + 1) : Nat) : Int) =
        (2 ^ (w + 1) : Int) := by omega
    rw [hsub, Int.emod_eq_of_lt (by omega) (by omega)]
    simp
  · simp only [↓reduceIte, Int.sub_self, Int.zero_emod, Bool.xor_self]
    cases h : ((0 : Int) == (2 ^ (w + 1) : Int))
    · rfl
    · have := beq_iff_eq.mp h; omega

/-! ### Engine 3: Universal 2-Lipschitz Even-Parity XOR Symmetry Action -/

theorem twoLip_is_oneLip {h : Nat → Nat} (hh : IsTwoLipschitz h) : IsOneLipschitz h := by
  intro w x y hxy
  have h1 := hh w x y hxy
  have hd : 2 ^ w ∣ 2 ^ (w + 1) := Nat.pow_dvd_pow 2 (Nat.le_succ w)
  rw [← Nat.mod_mod_of_dvd (h x) hd, ← Nat.mod_mod_of_dvd (h y) hd, h1]

theorem fourLip_is_twoLip {h : Nat → Nat} (hh : IsFourLipschitz h) : IsTwoLipschitz h := by
  intro w x y hxy
  have h1 := hh w x y hxy
  have hd : 2 ^ (w + 1) ∣ 2 ^ (w + 2) := Nat.pow_dvd_pow 2 (Nat.le_succ (w + 1))
  rw [← Nat.mod_mod_of_dvd (h x) hd, ← Nat.mod_mod_of_dvd (h y) hd, h1]

theorem mod_two_pow_xor (a b w : Nat) :
    (a ^^^ b) % 2 ^ w = (a % 2 ^ w) ^^^ (b % 2 ^ w) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_xor,
      Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hi : i < w <;> simp [hi]

theorem mod_two_pow_and (a b w : Nat) :
    (a &&& b) % 2 ^ w = (a % 2 ^ w) &&& (b % 2 ^ w) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_and, Nat.testBit_and,
      Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hi : i < w <;> simp [hi]

theorem mod_two_pow_or (a b w : Nat) :
    (a ||| b) % 2 ^ w = (a % 2 ^ w) ||| (b % 2 ^ w) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_or,
      Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hi : i < w <;> simp [hi]

theorem oneLip_xor {g h : Nat → Nat} (hg : IsOneLipschitz g) (hh : IsOneLipschitz h) :
    IsOneLipschitz (fun x => g x ^^^ h x) := by
  intro w x y hxy
  rw [mod_two_pow_xor, mod_two_pow_xor, hg w x y hxy, hh w x y hxy]

theorem add_two_pow_xor_mod (a b w : Nat) :
    ((a + 2 ^ w) ^^^ b) % 2 ^ (w + 1) = ((a ^^^ b) + 2 ^ w) % 2 ^ (w + 1) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hi : i < w + 1
  · simp only [hi, decide_true, Bool.true_and]
    by_cases heq : i = w
    · subst heq
      rw [Nat.testBit_xor, testBit_add_two_pow_self, testBit_add_two_pow_self, Nat.testBit_xor]
      cases a.testBit i <;> cases b.testBit i <;> decide
    · have hlt : i < w := by omega
      have hmod1 : (a + 2 ^ w) % 2 ^ w = a % 2 ^ w := Nat.add_mod_right a (2 ^ w)
      have hmod2 : ((a ^^^ b) + 2 ^ w) % 2 ^ w = (a ^^^ b) % 2 ^ w := Nat.add_mod_right _ (2 ^ w)
      have hb1 : (a + 2 ^ w).testBit i = a.testBit i := by
        have h := congrArg (fun z => z.testBit i) hmod1
        rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow] at h
        simp only [hlt, decide_true, Bool.true_and] at h
        exact h
      have hb2 : ((a ^^^ b) + 2 ^ w).testBit i = (a ^^^ b).testBit i := by
        have h := congrArg (fun z => z.testBit i) hmod2
        rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow] at h
        simp only [hlt, decide_true, Bool.true_and] at h
        exact h
      rw [Nat.testBit_xor, hb1, hb2, Nat.testBit_xor]
  · simp [hi]

theorem hasUnitSliceDeriv_xor_twoLip_iff {g h : Nat → Nat} (hh : IsTwoLipschitz h) (w : Nat) :
    HasUnitSliceDeriv (fun x => g x ^^^ h x) w ↔ HasUnitSliceDeriv g w := by
  constructor
  · intro hd r hr
    have hstep := hd r hr
    have hh_eq : h (r + 2 ^ w) % 2 ^ (w + 1) = h r % 2 ^ (w + 1) :=
      hh w (r + 2 ^ w) r (Nat.add_mod_right r (2 ^ w))
    rw [mod_two_pow_xor, hh_eq, ← mod_two_pow_xor, ← add_two_pow_xor_mod] at hstep
    rw [mod_two_pow_xor, mod_two_pow_xor] at hstep
    have hcancel := congrArg (fun z => z ^^^ (h r % 2 ^ (w + 1))) hstep
    simpa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] using hcancel
  · intro hd r hr
    have hstep := hd r hr
    have hh_eq : h (r + 2 ^ w) % 2 ^ (w + 1) = h r % 2 ^ (w + 1) :=
      hh w (r + 2 ^ w) r (Nat.add_mod_right r (2 ^ w))
    rw [mod_two_pow_xor, hh_eq, hstep, ← mod_two_pow_xor, add_two_pow_xor_mod]

theorem holonomy_xor (g h : Nat → Nat) (w : Nat) :
    holonomy (fun x => g x ^^^ h x) w =
      xor (holonomy g w) (bitXorSum (fun r => (h r).testBit w) (2 ^ w)) := by
  unfold holonomy
  have hcongr : bitXorSum (fun r => (g r ^^^ h r).testBit w) (2 ^ w) =
      bitXorSum (fun r => xor ((g r).testBit w) ((h r).testBit w)) (2 ^ w) := by
    apply bitXorSum_congr
    intro r _
    exact Nat.testBit_xor (g r) (h r) w
  rw [hcongr, bitXorSum_xor]

theorem singleCycle_congr_mod {f1 f2 : Nat → Nat} {w : Nat}
    (hf2 : IsOneLipschitz f2)
    (heq : ∀ x, f1 x % 2 ^ w = f2 x % 2 ^ w) :
    IsSingleCycle f1 w ↔ IsSingleCycle f2 w := by
  have hiter : ∀ k x, iter f1 k x % 2 ^ w = iter f2 k x % 2 ^ w := by
    intro k x
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [iter]
      rw [heq, hf2 w _ _ ih]
  constructor <;> intro hsc
  · exact ⟨by rw [← hiter]; exact hsc.period,
      fun i j hi hj h => hsc.distinct i j hi hj (by rw [hiter, hiter]; exact h)⟩
  · exact ⟨by rw [hiter]; exact hsc.period,
      fun i j hi hj h => hsc.distinct i j hi hj (by rw [← hiter, ← hiter]; exact h)⟩

/-- **THEOREM 3 (Engine 3 — Universal 2-Lipschitz Even-Parity XOR Symmetry):**
XORing ANY 1-Lipschitz T-function `g` with ANY even 2-Lipschitz operator `h` whose bit-`w`
XOR-sum vanishes for all `w ≥ 1` preserves single-cycle ergodicity at EVERY width `w ≥ 1`. -/
theorem singleCycle_xor_symmetry_iff {g h : Nat → Nat}
    (hg : IsOneLipschitz g) (hh : IsTwoLipschitz h)
    (heven : ∀ x, (h x).testBit 0 = false)
    (hpar : ∀ w, 1 ≤ w → bitXorSum (fun r => (h r).testBit w) (2 ^ w) = false) :
    ∀ w, 1 ≤ w → (IsSingleCycle (fun x => g x ^^^ h x) w ↔ IsSingleCycle g w) := by
  have hgh : IsOneLipschitz (fun x => g x ^^^ h x) := oneLip_xor hg (twoLip_is_oneLip hh)
  intro w hw
  induction w with
  | zero => omega
  | succ w ih =>
    cases w with
    | zero =>
      -- w = 1 (mod 2): h x is even, so (g x ^^^ h x) % 2 = g x % 2
      apply singleCycle_congr_mod hg
      intro x
      rw [mod_two_pow_xor]
      have hx0 : h x % 2 ^ 1 = 0 := by
        have hdec := mod_two_pow_succ_decomp (h x) 0
        rw [heven x] at hdec
        simpa [Nat.mod_one] using hdec
      rw [hx0, Nat.xor_zero]
    | succ w' =>
      have hw1 : 1 ≤ w' + 1 := by omega
      have ih_w := ih hw1
      constructor
      · intro hsc1
        have hsc0_gh := (singleCycle_pred_and_deriv hgh hsc1).1
        have hsc0_g := ih_w.mp hsc0_gh
        have ⟨hd_gh, hhol_gh⟩ := (singleCycle_succ_iff hgh hsc0_gh).mp hsc1
        have hd_g := (hasUnitSliceDeriv_xor_twoLip_iff hh (w' + 1)).mp hd_gh
        rw [holonomy_xor, hpar (w' + 1) hw1, Bool.xor_false] at hhol_gh
        exact (singleCycle_succ_iff hg hsc0_g).mpr ⟨hd_g, hhol_gh⟩
      · intro hsc1
        have hsc0_g := (singleCycle_pred_and_deriv hg hsc1).1
        have hsc0_gh := ih_w.mpr hsc0_g
        have ⟨hd_g, hhol_g⟩ := (singleCycle_succ_iff hg hsc0_g).mp hsc1
        have hd_gh := (hasUnitSliceDeriv_xor_twoLip_iff hh (w' + 1)).mpr hd_g
        have hhol_gh : holonomy (fun x => g x ^^^ h x) (w' + 1) = true := by
          rw [holonomy_xor, hpar (w' + 1) hw1, Bool.xor_false]; exact hhol_g
        exact (singleCycle_succ_iff hgh hsc0_gh).mpr ⟨hd_gh, hhol_gh⟩

/-! ### Carry-Propagation Mask `carryMask(x) = x ^^^ (x + 1)` Instantiation -/

theorem testBit_two_pow_sub_one (w i : Nat) :
    (2 ^ w - 1).testBit i = decide (i < w) := by
  induction w generalizing i with
  | zero => simp
  | succ w ih =>
    have hpow : 2 ^ (w + 1) - 1 = (2 ^ w - 1) + 2 ^ w := by
      have := two_pow_pos w; have := two_pow_succ_eq w; omega
    rw [hpow]
    by_cases hi : i < w
    · have hmod : ((2 ^ w - 1) + 2 ^ w) % 2 ^ w = (2 ^ w - 1) % 2 ^ w := Nat.add_mod_right _ _
      have hb := congrArg (fun z => z.testBit i) hmod
      rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow] at hb
      simp only [hi, decide_true, Bool.true_and] at hb
      rw [hb, ih i]
      have hi1 : i < w + 1 := by omega
      simp [hi, hi1]
    · by_cases heq : i = w
      · subst heq
        rw [testBit_add_two_pow_self, ih i]
        simp
      · have hgt : w + 1 ≤ i := by omega
        have hlt : (2 ^ w - 1) + 2 ^ w < 2 ^ (w + 1) := by
          have := two_pow_pos w; have := two_pow_succ_eq w; omega
        rw [testBit_eq_false_of_lt_two_pow hlt hgt]
        have : ¬ (i < w + 1) := by omega
        simp [this]

theorem testBit_add_two_pow_of_lt {x w : Nat} (hx : x < 2 ^ w) (i : Nat) :
    (x + 2 ^ w).testBit i = xor (x.testBit i) (decide (i = w)) := by
  by_cases hi : i < w
  · have hmod : (x + 2 ^ w) % 2 ^ w = x % 2 ^ w := Nat.add_mod_right x (2 ^ w)
    have hb := congrArg (fun z => z.testBit i) hmod
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow] at hb
    simp only [hi, decide_true, Bool.true_and] at hb
    have hne : i ≠ w := by omega
    rw [hb]; simp [hne]
  · by_cases heq : i = w
    · subst heq
      rw [testBit_add_two_pow_self, testBit_eq_false_of_lt_two_pow hx (Nat.le_refl i)]
      simp
    · have hgt : w + 1 ≤ i := by omega
      have h2w := two_pow_succ_eq w
      rw [testBit_eq_false_of_lt_two_pow (by omega : x + 2 ^ w < 2 ^ (w + 1)) hgt,
          testBit_eq_false_of_lt_two_pow hx (by omega : w ≤ i)]
      have hne : i ≠ w := by omega
      simp [hne]

theorem carryMask_all_ones (w : Nat) : carryMask (2 ^ w - 1) = 2 ^ (w + 1) - 1 := by
  unfold carryMask
  have h1 : 2 ^ w - 1 + 1 = 2 ^ w := by have := two_pow_pos w; omega
  rw [h1]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, testBit_two_pow_sub_one, Nat.testBit_two_pow, testBit_two_pow_sub_one]
  by_cases hlt : i < w
  · have hne : w ≠ i := by omega
    have hlt1 : i < w + 1 := by omega
    simp [hlt, hne, hlt1]
  · by_cases heq : i = w
    · subst heq; simp
    · have hne : w ≠ i := by omega
      have hnlt : ¬ (i < w + 1) := by omega
      simp [hlt, hne, hnlt]

theorem carryMask_add_two_pow_lt {r w : Nat} (hr : r + 1 < 2 ^ w) :
    carryMask (r + 2 ^ w) = carryMask r := by
  unfold carryMask
  apply Nat.eq_of_testBit_eq
  intro i
  have hrew : r + 2 ^ w + 1 = (r + 1) + 2 ^ w := by omega
  rw [hrew, Nat.testBit_xor, Nat.testBit_xor,
      testBit_add_two_pow_of_lt (by omega : r < 2 ^ w) i,
      testBit_add_two_pow_of_lt hr i]
  cases r.testBit i <;> cases (r + 1).testBit i <;> cases decide (i = w) <;> decide

theorem carryMask_mod_two_pow_add (x w : Nat) :
    carryMask x % 2 ^ (w + 1) = carryMask (x % 2 ^ w) % 2 ^ (w + 1) := by
  have hpos := two_pow_pos w
  have hdiv : x = (x % 2 ^ w) + 2 ^ w * (x / 2 ^ w) := by
    have := Nat.div_add_mod x (2 ^ w); omega
  -- Prove by induction on q = x / 2^w that carryMask (r + 2^w * q) % 2^(w+1) = carryMask r % 2^(w+1)
  suffices ∀ q r, r < 2 ^ w → carryMask (r + 2 ^ w * q) % 2 ^ (w + 1) = carryMask r % 2 ^ (w + 1) by
    calc carryMask x % 2 ^ (w + 1)
        = carryMask (x % 2 ^ w + 2 ^ w * (x / 2 ^ w)) % 2 ^ (w + 1) :=
          congrArg (fun z => carryMask z % 2 ^ (w + 1)) hdiv
      _ = carryMask (x % 2 ^ w) % 2 ^ (w + 1) := this (x / 2 ^ w) (x % 2 ^ w) (Nat.mod_lt x hpos)
  intro q r hr
  by_cases hlast : r + 1 < 2 ^ w
  · -- By induction on q, carryMask (r + 2^w * q) = carryMask r identically!
    suffices carryMask (r + 2 ^ w * q) = carryMask r by rw [this]
  -- r + 2^w * q and r + 1 + 2^w * q share identical bits ≥ w.
    apply Nat.eq_of_testBit_eq
    intro i
    unfold carryMask
    have hrew : r + 2 ^ w * q + 1 = (r + 1) + 2 ^ w * q := by omega
    rw [hrew, Nat.testBit_xor, Nat.testBit_xor]
    by_cases hi : i < w
    · have hm1 : (r + 2 ^ w * q) % 2 ^ w = r % 2 ^ w := by rw [Nat.add_mul_mod_self_left]
      have hm2 : (r + 1 + 2 ^ w * q) % 2 ^ w = (r + 1) % 2 ^ w := by rw [Nat.add_mul_mod_self_left]
      have hb1 := congrArg (fun z => z.testBit i) hm1
      have hb2 := congrArg (fun z => z.testBit i) hm2
      simp only [Nat.testBit_mod_two_pow, hi, decide_true, Bool.true_and] at hb1 hb2
      rw [hb1, hb2]
    · have hge : w ≤ i := by omega
      -- Since r < 2^w and r+1 < 2^w, both (r + 2^w * q) / 2^i and (r+1 + 2^w * q) / 2^i equal (2^w * q) / 2^i!
      have hd1 : (r + 2 ^ w * q) / 2 ^ i = (2 ^ w * q) / 2 ^ i := by
        have hpow_split : 2 ^ i = 2 ^ w * 2 ^ (i - w) := by
          rw [← Nat.pow_add]; congr 1; omega
        rw [hpow_split, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
        rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt (by omega : r < 2 ^ w), Nat.zero_add]
        rw [Nat.mul_div_cancel_left _ hpos]
      have hd2 : (r + 1 + 2 ^ w * q) / 2 ^ i = (2 ^ w * q) / 2 ^ i := by
        have hpow_split : 2 ^ i = 2 ^ w * 2 ^ (i - w) := by
          rw [← Nat.pow_add]; congr 1; omega
        rw [hpow_split, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
        rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hlast, Nat.zero_add]
        rw [Nat.mul_div_cancel_left _ hpos]
      rw [testBit_eq_div_mod, testBit_eq_div_mod, hd1, hd2, Bool.xor_self]
      rw [testBit_eq_false_of_lt_two_pow (by omega : r < 2 ^ w) hge,
          testBit_eq_false_of_lt_two_pow hlast hge, Bool.xor_self]
  · -- r = 2^w - 1: r + 2^w * q = 2^w * (q + 1) - 1, so ALL bits 0..w are 1 in carryMask!
    have hr_eq : r = 2 ^ w - 1 := by omega
    subst hr_eq
    rw [carryMask_all_ones w]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hi : i < w + 1
    · simp only [hi, decide_true, Bool.true_and]
      rw [testBit_two_pow_sub_one (w + 1) i]
      simp only [hi, decide_true]
      unfold carryMask
      have hsucc : (2 ^ w - 1 + 2 ^ w * q) + 1 = 2 ^ w * (q + 1) := by
        rw [Nat.mul_succ]; omega
      rw [hsucc, Nat.testBit_xor]
      by_cases hiw : i < w
      · have hm1 : (2 ^ w - 1 + 2 ^ w * q) % 2 ^ w = (2 ^ w - 1) % 2 ^ w :=
          Nat.add_mul_mod_self_left _ _ _
        have hm2 : (2 ^ w * (q + 1)) % 2 ^ w = 0 := Nat.mul_mod_right _ _
        have hb1 := congrArg (fun z => z.testBit i) hm1
        have hb2 := congrArg (fun z => z.testBit i) hm2
        simp only [Nat.testBit_mod_two_pow, hiw, decide_true, Bool.true_and] at hb1 hb2
        rw [hb1, hb2, testBit_two_pow_sub_one w i]
        simp [hiw]
      · have heq : i = w := by omega
        rw [heq]
        rw [testBit_eq_div_mod, testBit_eq_div_mod]
        have hd1 : (2 ^ w - 1 + 2 ^ w * q) / 2 ^ w = q := by
          rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt (by omega : 2 ^ w - 1 < 2 ^ w), Nat.zero_add]
        have hd2 : (2 ^ w * (q + 1)) / 2 ^ w = q + 1 := Nat.mul_div_cancel_left _ hpos
        rw [hd1, hd2, Nat.add_mod]
        have hlt : q % 2 < 2 := Nat.mod_lt q (by decide)
        cases hq : q % 2 with
        | zero => decide
        | succ k =>
          have hk : k = 0 := by omega
          subst hk; decide
    · simp [hi]

/-- Every 4-Lipschitz function automatically has even bit-`w` parity for all `w ≥ 1`
(via bit-flip involution at bit `w - 1`). -/
theorem fourLip_even_parity {h : Nat → Nat} (hh : IsFourLipschitz h) (w : Nat) (hw : 1 ≤ w) :
    bitXorSum (fun r => (h r).testBit w) (2 ^ w) = false := by
  apply bitXorSum_eq_false_of_bitflip (j := w - 1) (by omega)
  intro r _
  have hmod_low : (r ^^^ 2 ^ (w - 1)) % 2 ^ (w - 1) = r % 2 ^ (w - 1) := by
    rw [mod_two_pow_xor, Nat.mod_self, Nat.xor_zero]
  have hmod_hi := hh (w - 1) (r ^^^ 2 ^ (w - 1)) r hmod_low
  have hpow_eq : w - 1 + 2 = w + 1 := by omega
  rw [hpow_eq] at hmod_hi
  exact testBit_eq_of_mod_succ_eq hmod_hi

theorem scaled_carryMask_fourLip (k : Nat) :
    IsFourLipschitz (fun x => 2 * k * carryMask x) := by
  intro w x y hxy
  dsimp only
  have hc : carryMask x % 2 ^ (w + 1) = carryMask y % 2 ^ (w + 1) := by
    rw [carryMask_mod_two_pow_add x w, carryMask_mod_two_pow_add y w, hxy]
  have hpow2 : 2 ^ (w + 2) = 2 * 2 ^ (w + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [Nat.mul_assoc 2 k, Nat.mul_assoc 2 k, hpow2]
  rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left]
  congr 1
  rw [Nat.mul_mod, hc, ← Nat.mul_mod]

theorem scaled_carryMask_even_parity (k w : Nat) (hw : 1 ≤ w) :
    bitXorSum (fun r => (2 * k * carryMask r).testBit w) (2 ^ w) = false :=
  fourLip_even_parity (scaled_carryMask_fourLip k) w hw

/-- **COROLLARY (Universal Carry-Mask XOR Symmetry):**
For EVERY 1-Lipschitz T-function `g` and EVERY `k : Nat`, XORing with the global
carry-propagation mask `2 * k * (x ^^^ (x + 1))` preserves single-cycle ergodicity
at EVERY width `w ≥ 1` simultaneously! -/
theorem singleCycle_xor_carryMask_iff {g : Nat → Nat} (hg : IsOneLipschitz g) (k : Nat) :
    ∀ w, 1 ≤ w →
      (IsSingleCycle (fun x => g x ^^^ (2 * k * carryMask x)) w ↔ IsSingleCycle g w) := by
  apply singleCycle_xor_symmetry_iff hg (fourLip_is_twoLip (scaled_carryMask_fourLip k))
  · intro x
    rw [testBit_eq_div_mod]
    simp [Nat.mul_assoc]
  · intro w hw
    exact scaled_carryMask_even_parity k w hw

/-! ## Section 7: Certified Finite Orbit Checker & Bit-Run Primitives -/

def checkOrbitAux (f : Nat → Nat) (mod : Nat) : Nat → Nat → Bool
  | 0, x => x % mod == 0
  | steps + 1, x =>
    let nx := f x % mod
    if steps = 0 then nx == 0
    else (nx != 0) && checkOrbitAux f mod steps nx

def checkSingleCycle (f : Nat → Nat) (w : Nat) : Bool :=
  checkOrbitAux f (2 ^ w) (2 ^ w) 0

theorem checkOrbitAux_iff (hf : IsOneLipschitz f) (w : Nat) :
    ∀ (steps : Nat) (x : Nat),
      checkOrbitAux f (2 ^ w) steps x = true ↔
        (iter f steps x % 2 ^ w = 0 ∧
         ∀ j, 0 < j → j < steps → iter f j x % 2 ^ w ≠ 0) := by
  intro steps
  induction steps with
  | zero =>
    intro x
    simp [checkOrbitAux, iter]
  | succ s ih =>
    intro x
    cases s with
    | zero =>
      simp only [checkOrbitAux, ↓reduceIte, beq_iff_eq, iter]
      constructor
      · intro h; exact ⟨h, fun j hj1 hj2 => by omega⟩
      · intro h; exact h.1
    | succ s' =>
      change ((f x % 2 ^ w != 0) && checkOrbitAux f (2 ^ w) (s' + 1) (f x % 2 ^ w)) = true ↔ _
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
      rw [ih (f x % 2 ^ w)]
      have hiter_shift : ∀ k, iter f k (f x % 2 ^ w) % 2 ^ w = iter f (k + 1) x % 2 ^ w := by
        intro k
        have h1 := iter_oneLip hf w k (f x % 2 ^ w) (f x) (Nat.mod_mod _ _)
        rw [h1]
        have h2 : iter f k (f x) = iter f (k + 1) x := by
          have : k + 1 = k + 1 := rfl
          rw [iter_add]; rfl
        rw [h2]
      rw [hiter_shift (s' + 1)]
      constructor
      · rintro ⟨hfx, hper, hno⟩
        refine ⟨hper, fun j hj1 hj2 => ?_⟩
        cases j with
        | zero => omega
        | succ j' =>
          cases j' with
          | zero => simpa [iter] using hfx
          | succ j'' =>
            have hstep := hno (j'' + 1) (by omega) (by omega)
            rw [hiter_shift (j'' + 1)] at hstep
            exact hstep
      · rintro ⟨hper, hno⟩
        refine ⟨?_, hper, fun j hj1 hj2 => ?_⟩
        · exact hno 1 (by omega) (by omega)
        · rw [hiter_shift j]
          exact hno (j + 1) (by omega) (by omega)

/-- **SOUND & COMPLETE FINITE BASE CHECKER:**
For any 1-Lipschitz `f` and any width `w`, `checkSingleCycle f w = true ↔ IsSingleCycle f w`. -/
theorem checkSingleCycle_iff (hf : IsOneLipschitz f) (w : Nat) :
    checkSingleCycle f w = true ↔ IsSingleCycle f w := by
  unfold checkSingleCycle
  rw [checkOrbitAux_iff hf w (2 ^ w) 0, singleCycle_iff_no_early_return hf w]

/-! ### Bit-Shift and `d`-Run Bitwise Conjunction Primitives -/

theorem testBit_shiftLeft_eq (x s i : Nat) :
    (x <<< s).testBit i = (decide (s ≤ i) && x.testBit (i - s)) := by
  rw [Nat.shiftLeft_eq]
  rw [testBit_eq_div_mod]
  by_cases h : s ≤ i
  · simp only [h, decide_true, Bool.true_and]
    have hpow : 2 ^ i = 2 ^ s * 2 ^ (i - s) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [hpow, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ (two_pow_pos s)]
    exact (testBit_eq_div_mod x (i - s)).symm
  · simp only [h, decide_false, Bool.false_and]
    have hpow : 2 ^ i ∣ 2 ^ s := Nat.pow_dvd_pow 2 (by omega)
    have hmul : 2 ^ s = 2 ^ i * 2 ^ (s - i) := by
      rw [← Nat.pow_add]; congr 1; omega
    have heven : 2 ∣ 2 ^ (s - i) := by
      have hsub : s - i = (s - i - 1) + 1 := by omega
      rw [hsub, Nat.pow_succ]
      exact Nat.dvd_mul_left 2 _
    have hmul2 : x * 2 ^ s = (x * 2 ^ (s - i)) * 2 ^ i := by
      rw [hmul, Nat.mul_comm (2 ^ i), ← Nat.mul_assoc]
    rw [hmul2, Nat.mul_div_cancel _ (two_pow_pos i)]
    have h2 : 2 ∣ x * 2 ^ (s - i) := Nat.dvd_trans heven (Nat.dvd_mul_left _ _)
    rw [Nat.mod_eq_zero_of_dvd h2]; rfl

theorem testBit_two_mul (x i : Nat) :
    (2 * x).testBit i = (decide (1 ≤ i) && x.testBit (i - 1)) := by
  have h : 2 * x = x <<< 1 := by rw [Nat.shiftLeft_eq]; omega
  rw [h, testBit_shiftLeft_eq]

theorem testBit_runD_succ (d x i : Nat) :
    (runD (d + 2) x).testBit i =
      ((runD (d + 1) x).testBit i && (decide (d + 1 ≤ i) && x.testBit (i - (d + 1)))) := by
  simp only [runD, Nat.testBit_and, testBit_shiftLeft_eq]

theorem testBit_runD_true_iff {d : Nat} (hd : 1 ≤ d) (x i : Nat) :
    (runD d x).testBit i = true ↔
      (d - 1 ≤ i ∧ ∀ s, s < d → x.testBit (i - s) = true) := by
  induction d with
  | zero => omega
  | succ d ih =>
    cases d with
    | zero =>
      simp only [runD, Nat.sub_self, Nat.zero_le, true_and]
      constructor
      · intro hx s hs
        have : s = 0 := by omega
        subst this; simpa using hx
      · intro h; simpa using h 0 (by omega)
    | succ d' =>
      rw [testBit_runD_succ, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      rw [ih (by omega)]
      constructor
      · rintro ⟨⟨hge, hall⟩, hle, hbit⟩
        refine ⟨by omega, fun s hs => ?_⟩
        by_cases hlt : s < d' + 1
        · exact hall s hlt
        · have heq : s = d' + 1 := by omega
          rw [heq]; exact hbit
      · rintro ⟨hle, hall⟩
        refine ⟨⟨by omega, fun s hs => hall s (by omega)⟩, by omega, hall (d' + 1) (by omega)⟩

theorem testBit_runD_lt_false {d x i : Nat} (hd : 1 ≤ d) (hi : i < d - 1) :
    (runD d x).testBit i = false := by
  cases h : (runD d x).testBit i
  · rfl
  · have := (testBit_runD_true_iff hd x i).mp h
    omega

theorem testBit_runD_eq_of_mod_eq {d w x y i : Nat} (hd : 1 ≤ d)
    (hxy : x % 2 ^ w = y % 2 ^ w) (hi : i < w) :
    (runD d x).testBit i = (runD d y).testBit i := by
  have hbit_eq : ∀ j < w, x.testBit j = y.testBit j := by
    intro j hj
    have h := congrArg (fun z => z.testBit j) hxy
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow] at h
    simp only [hj, decide_true, Bool.true_and] at h
    exact h
  cases hx : (runD d x).testBit i
  · cases hy : (runD d y).testBit i
    · rfl
    · have ⟨hge, hall⟩ := (testBit_runD_true_iff hd y i).mp hy
      have hx' : (runD d x).testBit i = true :=
        (testBit_runD_true_iff hd x i).mpr ⟨hge, fun s hs => by rw [hbit_eq (i - s) (by omega)]; exact hall s hs⟩
      rw [hx] at hx'; exact absurd hx' (by decide)
  · symm
    have ⟨hge, hall⟩ := (testBit_runD_true_iff hd x i).mp hx
    exact (testBit_runD_true_iff hd y i).mpr ⟨hge, fun s hs => by rw [← hbit_eq (i - s) (by omega)]; exact hall s hs⟩

theorem two_mul_runD_twoLip (d : Nat) (hd : 1 ≤ d) :
    IsTwoLipschitz (fun x => 2 * runD d x) := by
  intro w x y hxy
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hi : i < w + 1
  · simp only [hi, decide_true, Bool.true_and]
    rw [testBit_two_mul, testBit_two_mul]
    by_cases hi1 : 1 ≤ i
    · simp only [hi1, decide_true, Bool.true_and]
      exact testBit_runD_eq_of_mod_eq hd hxy (by omega)
    · simp [hi1]
  · simp [hi]

theorem runD_testBit_of_lt {d w r : Nat} (hd : 1 ≤ d) (hr : r < 2 ^ w) :
    (runD d r).testBit w = false := by
  cases h : (runD d r).testBit w
  · rfl
  · have ⟨_, hall⟩ := (testBit_runD_true_iff hd r w).mp h
    have h0 := hall 0 (by omega)
    simp only [Nat.sub_zero] at h0
    rw [testBit_eq_false_of_lt_two_pow hr (Nat.le_refl w)] at h0
    exact absurd h0 (by decide)

theorem runD_add_two_pow_testBit {d w r : Nat} (hd : 1 ≤ d) (hr : r < 2 ^ w) :
    (runD d (r + 2 ^ w)).testBit w = true ↔
      (d - 1 ≤ w ∧ ∀ s, 1 ≤ s → s < d → r.testBit (w - s) = true) := by
  rw [testBit_runD_true_iff hd (r + 2 ^ w) w]
  constructor
  · rintro ⟨hge, hall⟩
    refine ⟨hge, fun s hs1 hsd => ?_⟩
    have hb := hall s hsd
    rw [testBit_add_two_pow_of_lt hr (w - s)] at hb
    have hne : w - s ≠ w := by omega
    simpa [hne] using hb
  · rintro ⟨hge, hall⟩
    refine ⟨hge, fun s hsd => ?_⟩
    rw [testBit_add_two_pow_of_lt hr (w - s)]
    cases s with
    | zero =>
      simp only [Nat.sub_zero, decide_true, testBit_eq_false_of_lt_two_pow hr (Nat.le_refl w)]
      rfl
    | succ s' =>
      have hne : w - (s' + 1) ≠ w := by omega
      simp only [hne, decide_false, Bool.xor_false]
      exact hall (s' + 1) (by omega) hsd

/-! ## Section 8: Novel Theorem Family A — 4-Parameter Hybrid ARX-Square-Run-CarryMask T-Functions -/

def hybridBitCond (a b C : Nat) : Bool :=
  C.testBit 0 && (!a.testBit 1 || C.testBit 1) && (a.testBit 0 || C.testBit 2) && (!b.testBit 0 || C.testBit 3)

theorem hybridCore_oneLip (a b C : Nat) :
    IsOneLipschitz (fun x => (((a * x * x) ^^^ (2 * runD 2 x) ^^^ (2 * b * runD 3 x)) ||| C)) := by
  intro w x y hxy
  dsimp only
  rw [mod_two_pow_or, mod_two_pow_or]
  congr 1
  rw [mod_two_pow_xor, mod_two_pow_xor, mod_two_pow_xor, mod_two_pow_xor]
  have hsq : (a * x * x) % 2 ^ w = (a * y * y) % 2 ^ w := by
    rw [Nat.mul_mod (a * x), Nat.mul_mod a x, hxy, ← Nat.mul_mod a y, ← Nat.mul_mod (a * y)]
  have hr2 : (2 * runD 2 x) % 2 ^ w = (2 * runD 2 y) % 2 ^ w :=
    twoLip_is_oneLip (two_mul_runD_twoLip 2 (by omega)) w x y hxy
  have hr3 : (2 * b * runD 3 x) % 2 ^ w = (2 * b * runD 3 y) % 2 ^ w := by
    have h1 := twoLip_is_oneLip (two_mul_runD_twoLip 3 (by omega)) w x y hxy
    have hrew1 : 2 * b * runD 3 x = b * (2 * runD 3 x) := by
      rw [Nat.mul_comm 2 b, Nat.mul_assoc]
    have hrew2 : 2 * b * runD 3 y = b * (2 * runD 3 y) := by
      rw [Nat.mul_comm 2 b, Nat.mul_assoc]
    rw [hrew1, hrew2, Nat.mul_mod, h1, ← Nat.mul_mod]
  rw [hsq, hr2, hr3]

theorem hybridBase_oneLip (a b C : Nat) : IsOneLipschitz (hybridBase a b C) := by
  intro w x y hxy
  unfold hybridBase
  rw [Nat.add_mod, hxy, hybridCore_oneLip a b C w x y hxy, ← Nat.add_mod]

theorem hybridH_oneLip (a b C k : Nat) : IsOneLipschitz (hybridH a b C k) :=
  oneLip_xor (hybridBase_oneLip a b C) (twoLip_is_oneLip (fourLip_is_twoLip (scaled_carryMask_fourLip k)))

theorem sq_add_two_pow_mod {a w r : Nat} (hw : 2 ≤ w) :
    (a * (r + 2 ^ w) * (r + 2 ^ w)) % 2 ^ (w + 2) =
      (a * r * r + 2 ^ (w + 1) * (a * r)) % 2 ^ (w + 2) := by
  have hexp : a * (r + 2 ^ w) * (r + 2 ^ w) =
      (a * r * r + 2 ^ (w + 1) * (a * r)) + 2 ^ (w + 2) * (2 ^ (w - 2) * a) := by
    have h2w : 2 ^ w * 2 ^ w = 2 ^ (w + 2) * 2 ^ (w - 2) := by
      rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
    have h2w1 : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
    calc a * (r + 2 ^ w) * (r + 2 ^ w)
        = (a * r + a * 2 ^ w) * (r + 2 ^ w) := by rw [Nat.mul_add a r (2 ^ w)]
      _ = (a * r + a * 2 ^ w) * r + (a * r + a * 2 ^ w) * 2 ^ w := by rw [Nat.mul_add]
      _ = (a * r * r + a * 2 ^ w * r) + (a * r * 2 ^ w + a * 2 ^ w * 2 ^ w) := by
          rw [Nat.add_mul, Nat.add_mul]
      _ = (a * r * r + (2 * 2 ^ w) * (a * r)) + (2 ^ w * 2 ^ w) * a := by
          have t1 : a * 2 ^ w * r = 2 ^ w * (a * r) := by
            rw [Nat.mul_comm a (2 ^ w), Nat.mul_assoc]
          have t2 : a * r * 2 ^ w = 2 ^ w * (a * r) := Nat.mul_comm _ _
          have t3 : a * 2 ^ w * 2 ^ w = (2 ^ w * 2 ^ w) * a := by
            rw [Nat.mul_assoc, Nat.mul_comm a]
          rw [t1, t2, t3]
          have t4 : 2 ^ w * (a * r) + 2 ^ w * (a * r) = 2 * 2 ^ w * (a * r) := by
            rw [Nat.mul_assoc 2, Nat.two_mul]
          omega
      _ = (a * r * r + 2 ^ (w + 1) * (a * r)) + 2 ^ (w + 2) * (2 ^ (w - 2) * a) := by
          rw [← h2w1, h2w, Nat.mul_assoc (2 ^ (w + 2))]
  rw [hexp, Nat.add_mul_mod_self_left]

theorem testBit_add_two_pow_mul (x c k : Nat) :
    (x + 2 ^ k * c).testBit k = xor (x.testBit k) (c.testBit 0) := by
  rw [testBit_eq_div_mod, testBit_eq_div_mod, testBit_eq_div_mod]
  rw [Nat.add_mul_div_left _ _ (two_pow_pos k), Nat.pow_zero, Nat.div_one]
  rw [Nat.add_mod]
  have h1 : (x / 2 ^ k) % 2 < 2 := Nat.mod_lt _ (by decide)
  have h2 : c % 2 < 2 := Nat.mod_lt _ (by decide)
  cases hx : (x / 2 ^ k) % 2 with
  | zero =>
    cases hc : c % 2 with
    | zero => decide
    | succ c' =>
      have hc0 : c' = 0 := by omega
      rw [hc0]; decide
  | succ x' =>
    have hx0 : x' = 0 := by omega
    rw [hx0]
    cases hc : c % 2 with
    | zero => decide
    | succ c' =>
      have hc0 : c' = 0 := by omega
      rw [hc0]; decide

theorem testBit_mul_zero (a r : Nat) :
    (a * r).testBit 0 = (a.testBit 0 && r.testBit 0) := by
  rw [testBit_eq_div_mod, testBit_eq_div_mod, testBit_eq_div_mod]
  rw [Nat.pow_zero, Nat.div_one, Nat.div_one, Nat.div_one, Nat.mul_mod]
  have ha : a % 2 < 2 := Nat.mod_lt _ (by decide)
  have hr : r % 2 < 2 := Nat.mod_lt _ (by decide)
  cases h1 : a % 2 with
  | zero => simp
  | succ a' =>
    have ha0 : a' = 0 := by omega
    rw [ha0]
    cases h2 : r % 2 with
    | zero => decide
    | succ r' =>
      have hr0 : r' = 0 := by omega
      rw [hr0]; decide

theorem sq_add_two_pow_testBit {a w r : Nat} (hw : 2 ≤ w) :
    (a * (r + 2 ^ w) * (r + 2 ^ w)).testBit (w + 1) =
      xor ((a * r * r).testBit (w + 1)) (a.testBit 0 && r.testBit 0) := by
  rw [testBit_eq_of_mod_succ_eq (sq_add_two_pow_mod hw), testBit_add_two_pow_mul, testBit_mul_zero]

theorem sq_add_two_pow_mod_succ {a w r : Nat} (hw : 2 ≤ w) :
    (a * (r + 2 ^ w) * (r + 2 ^ w)) % 2 ^ (w + 1) = (a * r * r) % 2 ^ (w + 1) := by
  have h1 := sq_add_two_pow_mod (a := a) (r := r) hw
  have hd : 2 ^ (w + 1) ∣ 2 ^ (w + 2) := Nat.pow_dvd_pow 2 (Nat.le_succ (w + 1))
  calc (a * (r + 2 ^ w) * (r + 2 ^ w)) % 2 ^ (w + 1)
      = ((a * (r + 2 ^ w) * (r + 2 ^ w)) % 2 ^ (w + 2)) % 2 ^ (w + 1) := (Nat.mod_mod_of_dvd _ hd).symm
    _ = ((a * r * r + 2 ^ (w + 1) * (a * r)) % 2 ^ (w + 2)) % 2 ^ (w + 1) := congrArg (· % 2 ^ (w + 1)) h1
    _ = (a * r * r + 2 ^ (w + 1) * (a * r)) % 2 ^ (w + 1) := Nat.mod_mod_of_dvd _ hd
    _ = (a * r * r) % 2 ^ (w + 1) := Nat.add_mul_mod_self_left _ _ _

theorem two_mul_b_runD3_add_two_pow_testBit {b w r : Nat} (hw : 2 ≤ w) (hr : r < 2 ^ w) :
    (2 * b * runD 3 (r + 2 ^ w)).testBit (w + 1) =
      xor ((2 * b * runD 3 r).testBit (w + 1)) (b.testBit 0 && r.testBit (w - 1) && r.testBit (w - 2)) := by
  have hlow : runD 3 (r + 2 ^ w) % 2 ^ w = runD 3 r % 2 ^ w := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hi : i < w
    · simp only [hi, decide_true, Bool.true_and]
      exact testBit_runD_eq_of_mod_eq (by omega) (Nat.add_mod_right r (2 ^ w)) hi
    · simp [hi]
  have hbit0 : (runD 3 r).testBit w = false := runD_testBit_of_lt (by omega) hr
  have hbit1 : (runD 3 (r + 2 ^ w)).testBit w = (r.testBit (w - 1) && r.testBit (w - 2)) := by
    cases h : (runD 3 (r + 2 ^ w)).testBit w
    · cases h1 : r.testBit (w - 1) <;> cases h2 : r.testBit (w - 2)
      · rfl
      · rfl
      · rfl
      · exfalso
        have ht : (runD 3 (r + 2 ^ w)).testBit w = true := by
          rw [runD_add_two_pow_testBit (by omega) hr]
          refine ⟨by omega, fun s hs1 hs3 => ?_⟩
          have : s = 1 ∨ s = 2 := by omega
          rcases this with rfl | rfl <;> assumption
        rw [h] at ht; exact absurd ht (by decide)
    · have ⟨_, hall⟩ := (runD_add_two_pow_testBit (by omega) hr).mp h
      rw [hall 1 (by omega) (by omega), hall 2 (by omega) (by omega)]; rfl
  have hmod1 : runD 3 (r + 2 ^ w) % 2 ^ (w + 1) =
      (runD 3 r + 2 ^ w * (if r.testBit (w - 1) && r.testBit (w - 2) then 1 else 0)) % 2 ^ (w + 1) := by
    rw [mod_two_pow_succ_decomp (runD 3 (r + 2 ^ w)) w, hlow, hbit1]
    have hdec := mod_two_pow_succ_decomp (runD 3 r) w
    rw [hbit0] at hdec
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hdec
    rw [Nat.add_mod, hdec]
    have hlt := Nat.mod_lt (runD 3 r) (two_pow_pos w)
    have h2w := two_pow_succ_eq w
    cases r.testBit (w - 1) && r.testBit (w - 2)
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.mul_zero, Nat.zero_mod, Nat.add_zero]
      exact (Nat.mod_eq_of_lt (by omega : runD 3 r % 2 ^ w < 2 ^ (w + 1))).symm
    · simp only [↓reduceIte, Nat.mul_one]
      have hlt2 : 2 ^ w % 2 ^ (w + 1) = 2 ^ w := Nat.mod_eq_of_lt (by omega)
      rw [hlt2]
      exact (Nat.mod_eq_of_lt (by omega : runD 3 r % 2 ^ w + 2 ^ w < 2 ^ (w + 1))).symm
  have hmul_mod : (2 * b * runD 3 (r + 2 ^ w)) % 2 ^ (w + 2) =
      (2 * b * runD 3 r + 2 ^ (w + 1) * (b * if r.testBit (w - 1) && r.testBit (w - 2) then 1 else 0)) % 2 ^ (w + 2) := by
    have hpow2 : 2 ^ (w + 2) = 2 * 2 ^ (w + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [Nat.mul_assoc 2 b, hpow2, Nat.mul_mod_mul_left]
    have hrhs : 2 * b * runD 3 r + 2 ^ (w + 1) * (b * if r.testBit (w - 1) && r.testBit (w - 2) then 1 else 0) =
        2 * (b * (runD 3 r + 2 ^ w * (if r.testBit (w - 1) && r.testBit (w - 2) then 1 else 0))) := by
      have hpow1 : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [Nat.mul_add b, Nat.mul_add 2, Nat.mul_assoc 2 b, hpow1]
      congr 1
      let t := if r.testBit (w - 1) && r.testBit (w - 2) then 1 else 0
      change 2 * 2 ^ w * (b * t) = 2 * (b * (2 ^ w * t))
      calc 2 * 2 ^ w * (b * t) = 2 * (2 ^ w * (b * t)) := Nat.mul_assoc 2 (2 ^ w) (b * t)
        _ = 2 * (b * (2 ^ w * t)) := by rw [Nat.mul_left_comm (2 ^ w) b t]
    rw [hrhs, Nat.mul_mod_mul_left]
    congr 1
    rw [Nat.mul_mod b (runD 3 (r + 2 ^ w)), hmod1, ← Nat.mul_mod]
  rw [testBit_eq_of_mod_succ_eq hmul_mod, testBit_add_two_pow_mul, testBit_mul_zero]
  cases b.testBit 0 <;> cases r.testBit (w - 1) <;> cases r.testBit (w - 2) <;> simp

theorem two_mul_runD2_add_two_pow_testBit {w r : Nat} (hw : 1 ≤ w) (hr : r < 2 ^ w) :
    (2 * runD 2 (r + 2 ^ w)).testBit (w + 1) =
      xor ((2 * runD 2 r).testBit (w + 1)) (r.testBit (w - 1)) := by
  rw [testBit_two_mul, testBit_two_mul]
  simp only [Nat.le_add_left, decide_true, Bool.true_and, Nat.add_sub_cancel]
  rw [runD_testBit_of_lt (by omega) hr, Bool.false_xor]
  cases h : (runD 2 (r + 2 ^ w)).testBit w
  · cases h1 : r.testBit (w - 1)
    · rfl
    · exfalso
      have ht : (runD 2 (r + 2 ^ w)).testBit w = true := by
        rw [runD_add_two_pow_testBit (by omega) hr]
        refine ⟨by omega, fun s hs1 hs2 => ?_⟩
        have : s = 1 := by omega
        subst this; exact h1
      rw [h] at ht; exact absurd ht (by decide)
  · have ⟨_, hall⟩ := (runD_add_two_pow_testBit (by omega) hr).mp h
    exact (hall 1 (by omega) (by omega)).symm

theorem hybridCore_twoLip_ge2 (a b C : Nat) {w r : Nat} (hw : 2 ≤ w) :
    (((a * (r + 2 ^ w) * (r + 2 ^ w)) ^^^ (2 * runD 2 (r + 2 ^ w)) ^^^ (2 * b * runD 3 (r + 2 ^ w))) ||| C) % 2 ^ (w + 1) =
    (((a * r * r) ^^^ (2 * runD 2 r) ^^^ (2 * b * runD 3 r)) ||| C) % 2 ^ (w + 1) := by
  rw [mod_two_pow_or, mod_two_pow_or]
  congr 1
  rw [mod_two_pow_xor, mod_two_pow_xor, mod_two_pow_xor, mod_two_pow_xor]
  rw [sq_add_two_pow_mod_succ hw]
  have hr2 := two_mul_runD_twoLip 2 (by omega) w (r + 2 ^ w) r (Nat.add_mod_right r (2 ^ w))
  have hr3 : (2 * b * runD 3 (r + 2 ^ w)) % 2 ^ (w + 1) = (2 * b * runD 3 r) % 2 ^ (w + 1) := by
    have h1 := two_mul_runD_twoLip 3 (by omega) w (r + 2 ^ w) r (Nat.add_mod_right r (2 ^ w))
    have hrew1 : 2 * b * runD 3 (r + 2 ^ w) = b * (2 * runD 3 (r + 2 ^ w)) := by
      rw [Nat.mul_comm 2 b, Nat.mul_assoc]
    have hrew2 : 2 * b * runD 3 r = b * (2 * runD 3 r) := by
      rw [Nat.mul_comm 2 b, Nat.mul_assoc]
    rw [hrew1, hrew2, Nat.mul_mod, h1, ← Nat.mul_mod]
  rw [hr2, hr3]

private theorem xor6_cancel (u1 u2 u3 d1 d2 d3 : Bool) :
    xor (xor (xor (xor u1 d1) (xor u2 d2)) (xor u3 d3)) (xor (xor u1 u2) u3) =
      xor (xor d1 d2) d3 := by
  cases u1 <;> cases u2 <;> cases u3 <;> cases d1 <;> cases d2 <;> cases d3 <;> decide

/-- **CURVATURE ANNIHILATION FOR `hybridBase` AT ALL `w ≥ 3`:**
Using multi-term `F_2`-linear decomposition + bit-flip involutions at bits `w-1` and `0`. -/
theorem hybridBase_curvature_zero (a b C : Nat) {w : Nat} (hw : 3 ≤ w) :
    curvatureSum (hybridBase a b C) w % (2 ^ (w + 2) : Int) = 0 := by
  have hd : HasUnitSliceDeriv (hybridBase a b C) w :=
    hasUnitSliceDeriv_add_twoLip (fun r _ => hybridCore_twoLip_ge2 a b C (by omega))
  rw [curvatureSum_zero_iff_bitXorSum hd]
  by_cases hC : C.testBit (w + 1) = true
  · have hcongr : bitXorSum (curvatureBit (hybridBase a b C) w) (2 ^ w) =
        bitXorSum (fun _ => false) (2 ^ w) := by
      apply bitXorSum_congr
      intro r hr
      unfold hybridBase
      rw [curvatureBit_add_twoLip (hybridCore_twoLip_ge2 a b C (by omega))]
      rw [Nat.testBit_or, Nat.testBit_or, hC]
      simp
    rw [hcongr, bitXorSum_const_false]
  · have hCf : C.testBit (w + 1) = false := by
      cases h : C.testBit (w + 1)
      · rfl
      · exact absurd h hC
    have hcongr : bitXorSum (curvatureBit (hybridBase a b C) w) (2 ^ w) =
        bitXorSum (fun r => xor (xor (a.testBit 0 && r.testBit 0) (r.testBit (w - 1)))
          (b.testBit 0 && r.testBit (w - 1) && r.testBit (w - 2))) (2 ^ w) := by
      apply bitXorSum_congr
      intro r hr
      unfold hybridBase
      rw [curvatureBit_add_twoLip (hybridCore_twoLip_ge2 a b C (by omega))]
      rw [Nat.testBit_or, Nat.testBit_or, hCf, Bool.or_false, Bool.or_false]
      rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor]
      rw [sq_add_two_pow_testBit (by omega),
          two_mul_runD2_add_two_pow_testBit (by omega) hr,
          two_mul_b_runD3_add_two_pow_testBit (by omega) hr]
      exact xor6_cancel _ _ _ _ _ _
    rw [hcongr, bitXorSum_xor, bitXorSum_xor]
    have ht1 : bitXorSum (fun r => a.testBit 0 && r.testBit 0) (2 ^ w) = false := by
      apply bitXorSum_eq_false_of_bitflip (j := w - 1) (by omega)
      intro r _
      rw [Nat.testBit_xor, Nat.testBit_two_pow]
      have hne : w - 1 ≠ 0 := by omega
      simp [hne]
    have ht2 : bitXorSum (fun r => r.testBit (w - 1)) (2 ^ w) = false := by
      apply bitXorSum_eq_false_of_bitflip (j := 0) (by omega)
      intro r _
      rw [Nat.testBit_xor, Nat.testBit_two_pow]
      have hne : 0 ≠ w - 1 := by omega
      simp [hne]
    have ht3 : bitXorSum (fun r => b.testBit 0 && r.testBit (w - 1) && r.testBit (w - 2)) (2 ^ w) = false := by
      apply bitXorSum_eq_false_of_bitflip (j := 0) (by omega)
      intro r _
      rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_two_pow, Nat.testBit_two_pow]
      have hne1 : 0 ≠ w - 1 := by omega
      have hne2 : 0 ≠ w - 2 := by omega
      simp [hne1, hne2]
    rw [ht1, ht2, ht3]; rfl

/-- **THEOREM A1 (Sharp `w ≤ 4` Lifting for the 4-Parameter Hybrid Family `hybridH`):**
For ALL `a b C k : Nat`, `hybridH a b C k` is single-cycle mod `2^w` for ALL `w ≥ 1`
if and only if it is single-cycle at the single finite width `w = 4` (mod 16). -/
theorem hybridH_singleCycle_iff_w4 (a b C k : Nat) :
    (∀ w, 1 ≤ w → IsSingleCycle (hybridH a b C k) w) ↔ IsSingleCycle (hybridH a b C k) 4 := by
  constructor
  · intro hall; exact hall 4 (by omega)
  · intro h4 w hw
    unfold hybridH at h4 ⊢
    rw [singleCycle_xor_carryMask_iff (hybridBase_oneLip a b C) k w hw]
    have h4_base : IsSingleCycle (hybridBase a b C) 4 :=
      (singleCycle_xor_carryMask_iff (hybridBase_oneLip a b C) k 4 (by omega)).mp h4
    exact lift_singleCycle_from_w4 (hybridBase_oneLip a b C) h4_base
      (fun w' hw' => hasUnitSliceDeriv_add_twoLip (fun r _ => hybridCore_twoLip_ge2 a b C (by omega)))
      (fun w' hw' => hybridBase_curvature_zero a b C hw') w hw

/-! ### Complete 4-Bit Arithmetic Characterization of `hybridH a b C k` -/

theorem hybridBase_mod16_reduce (a b C x : Nat) :
    hybridBase a b C x % 2 ^ 4 = hybridBase (a % 16) (b % 2) (C % 16) x % 2 ^ 4 := by
  unfold hybridBase
  have h16 : (2 ^ 4 : Nat) = 16 := rfl
  rw [h16]
  rw [Nat.add_mod, Nat.add_mod x]
  congr 1; congr 1
  rw [← h16, mod_two_pow_or, mod_two_pow_or]
  have hCmod : C % 2 ^ 4 = (C % 16) % 2 ^ 4 := by rw [h16, Nat.mod_mod]
  rw [← hCmod]
  congr 1
  rw [mod_two_pow_xor, mod_two_pow_xor, mod_two_pow_xor, mod_two_pow_xor]
  congr 1
  · congr 1
    rw [h16, Nat.mul_mod (a * x), Nat.mul_mod a x, Nat.mul_mod ((a % 16) * x), Nat.mul_mod (a % 16) x, Nat.mod_mod]
  · have h8dvd : 8 ∣ 2 * runD 3 x := by
      have hmod8 : (2 * runD 3 x) % 2 ^ 3 = 0 := by
        apply Nat.eq_of_testBit_eq
        intro i
        rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
        by_cases hi : i < 3
        · simp only [hi, decide_true, Bool.true_and, testBit_two_mul]
          by_cases hi1 : 1 ≤ i
          · simp only [hi1, decide_true, Bool.true_and]
            exact testBit_runD_lt_false (d := 3) (by omega) (by omega)
          · simp [hi1]
        · simp [hi]
      exact Nat.dvd_of_mod_eq_zero hmod8
    obtain ⟨m, hm⟩ := h8dvd
    have hrew1 : 2 * b * runD 3 x = 8 * (b * m) := by
      calc 2 * b * runD 3 x = b * (2 * runD 3 x) := by rw [Nat.mul_comm 2 b, Nat.mul_assoc]
        _ = b * (8 * m) := by rw [hm]
        _ = 8 * (b * m) := Nat.mul_left_comm b 8 m
    have hrew2 : 2 * (b % 2) * runD 3 x = 8 * ((b % 2) * m) := by
      calc 2 * (b % 2) * runD 3 x = (b % 2) * (2 * runD 3 x) := by rw [Nat.mul_comm 2 (b % 2), Nat.mul_assoc]
        _ = (b % 2) * (8 * m) := by rw [hm]
        _ = 8 * ((b % 2) * m) := Nat.mul_left_comm (b % 2) 8 m
    rw [h16, hrew1, hrew2]
    have h16_eq : (16 : Nat) = 8 * 2 := rfl
    rw [h16_eq, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left]
    congr 1
    rw [Nat.mul_mod b m 2, Nat.mul_mod (b % 2) m 2, Nat.mod_mod]

def verifyAll512 : Bool :=
  (List.range 16).all fun a =>
    (List.range 2).all fun b =>
      (List.range 16).all fun C =>
        checkSingleCycle (hybridBase a b C) 4 == hybridBitCond a b C

theorem verifyAll512_eq_true : verifyAll512 = true := by decide

theorem checkSingleCycle_hybridBase_eq_bitCond (a b C : Nat)
    (ha : a < 16) (hb : b < 2) (hC : C < 16) :
    checkSingleCycle (hybridBase a b C) 4 = hybridBitCond a b C := by
  have h := verifyAll512_eq_true
  unfold verifyAll512 at h
  rw [List.all_eq_true] at h
  have h1 := h a (List.mem_range.mpr ha)
  rw [List.all_eq_true] at h1
  have h2 := h1 b (List.mem_range.mpr hb)
  rw [List.all_eq_true] at h2
  have h3 := h2 C (List.mem_range.mpr hC)
  exact beq_iff_eq.mp h3

theorem hybridBitCond_mod (a b C : Nat) :
    hybridBitCond (a % 16) (b % 2) (C % 16) = hybridBitCond a b C := by
  unfold hybridBitCond
  have ha0 : (a % 16).testBit 0 = a.testBit 0 := by
    have := Nat.testBit_mod_two_pow a 4 0; simp
  have ha1 : (a % 16).testBit 1 = a.testBit 1 := by
    have := Nat.testBit_mod_two_pow a 4 1; simpa using this
  have hb0 : (b % 2).testBit 0 = b.testBit 0 := by
    have := Nat.testBit_mod_two_pow b 1 0; simp
  have hC0 : (C % 16).testBit 0 = C.testBit 0 := by
    have := Nat.testBit_mod_two_pow C 4 0; simp
  have hC1 : (C % 16).testBit 1 = C.testBit 1 := by
    have := Nat.testBit_mod_two_pow C 4 1; simpa using this
  have hC2 : (C % 16).testBit 2 = C.testBit 2 := by
    have := Nat.testBit_mod_two_pow C 4 2; simpa using this
  have hC3 : (C % 16).testBit 3 = C.testBit 3 := by
    have := Nat.testBit_mod_two_pow C 4 3; simpa using this
  rw [ha0, ha1, hb0, hC0, hC1, hC2, hC3]

/-- **THEOREM A2 (Complete 4-Bit Arithmetic Characterization of `hybridH`):**
For ALL `a b C k : Nat`, `hybridH a b C k` is single-cycle mod `2^w` for ALL `w ≥ 1`
if and only if `C_0 = 1`, `a_1 = 1 → C_1 = 1`, `a_0 = 0 → C_2 = 1`, and `b_0 = 1 → C_3 = 1`
(completely independent of `k` and of all higher bits `≥ 4` of `C`!). -/
theorem hybridH_singleCycle_iff_bits (a b C k : Nat) :
    (∀ w, 1 ≤ w → IsSingleCycle (hybridH a b C k) w) ↔
      (C.testBit 0 = true ∧
       (a.testBit 1 = true → C.testBit 1 = true) ∧
       (a.testBit 0 = false → C.testBit 2 = true) ∧
       (b.testBit 0 = true → C.testBit 3 = true)) := by
  rw [hybridH_singleCycle_iff_w4]
  unfold hybridH
  rw [singleCycle_xor_carryMask_iff (hybridBase_oneLip a b C) k 4 (by omega)]
  rw [singleCycle_congr_mod (hybridBase_oneLip (a % 16) (b % 2) (C % 16))
        (hybridBase_mod16_reduce a b C)]
  rw [← checkSingleCycle_iff (hybridBase_oneLip (a % 16) (b % 2) (C % 16)) 4]
  rw [checkSingleCycle_hybridBase_eq_bitCond (a % 16) (b % 2) (C % 16)
        (Nat.mod_lt a (by decide)) (Nat.mod_lt b (by decide)) (Nat.mod_lt C (by decide))]
  rw [hybridBitCond_mod]
  unfold hybridBitCond
  cases C.testBit 0 <;> cases a.testBit 1 <;> cases C.testBit 1 <;>
    cases a.testBit 0 <;> cases C.testBit 2 <;> cases b.testBit 0 <;> cases C.testBit 3 <;>
    simp

/-! ## Section 9: Novel Theorem Family B — Arbitrary-Order `d`-Run Family & No-Universal-Width Theorem -/

theorem runT_core_twoLip (d C : Nat) (hd : 1 ≤ d) :
    IsTwoLipschitz (fun x => (2 * runD d x) ||| C) := by
  intro w x y hxy
  dsimp only
  rw [mod_two_pow_or, mod_two_pow_or, two_mul_runD_twoLip d hd w x y hxy]

theorem runT_oneLip (d C : Nat) (hd : 1 ≤ d) : IsOneLipschitz (runT d C) := by
  intro w x y hxy
  unfold runT
  rw [Nat.add_mod, hxy, twoLip_is_oneLip (runT_core_twoLip d C hd) w x y hxy, ← Nat.add_mod]

theorem runT_hasUnitSliceDeriv (d C w : Nat) (hd : 1 ≤ d) :
    HasUnitSliceDeriv (runT d C) w :=
  hasUnitSliceDeriv_add_twoLip (fun r _ => runT_core_twoLip d C hd w (r + 2 ^ w) r (Nat.add_mod_right r (2 ^ w)))

theorem add_const_oneLip (C : Nat) : IsOneLipschitz (fun x => x + C) := by
  intro w x y hxy; dsimp only; rw [Nat.add_mod, hxy, ← Nat.add_mod]

theorem add_const_singleCycle_iff (C : Nat) :
    ∀ w, 1 ≤ w → (IsSingleCycle (fun x => x + C) w ↔ C.testBit 0 = true) := by
  have h1 : IsSingleCycle (fun x => x + C) 1 ↔ C.testBit 0 = true := by
    rw [singleCycle_iff_no_early_return (add_const_oneLip C) 1]
    rw [testBit_eq_div_mod, Nat.pow_zero, Nat.div_one]
    have hlt : C % 2 < 2 := Nat.mod_lt C (by decide)
    constructor
    · rintro ⟨_, hno⟩
      have hne := hno 1 (by omega) (by decide)
      simp only [iter, Nat.pow_one, Nat.zero_add] at hne
      have : C % 2 = 1 := by omega
      rw [this]; rfl
    · intro hodd
      have hC1 : C % 2 = 1 := beq_iff_eq.mp hodd
      refine ⟨?_, fun k hk1 hk2 => ?_⟩
      · simp only [iter, Nat.pow_one, Nat.zero_add]
        rw [Nat.add_mod, hC1]
      · have hk : k = 1 := by omega
        subst hk
        simp only [iter, Nat.pow_one, Nat.zero_add, hC1]
        decide
  intro w hw
  constructor
  · intro hsc
    exact h1.mp (singleCycle_of_ge (add_const_oneLip C) hw hsc)
  · intro hodd
    apply lift_singleCycle_from_curvatureSum 0 (add_const_oneLip C) (h1.mpr hodd)
    · intro w' _
      exact hasUnitSliceDeriv_add_twoLip (fun _ _ => rfl)
    · intro w' _
      unfold curvatureSum
      have hcongr : intSum (fun r => (((r + 2 ^ w' + C : Nat) : Int) - ((r + C : Nat) : Int) - (2 ^ w' : Int))) (2 ^ w') =
          intSum (fun _ => (0 : Int)) (2 ^ w') := by
        apply intSum_congr
        intro r _
        rw [Int.natCast_add, Int.natCast_add, Int.natCast_add, natCast_two_pow]
        omega
      rw [hcongr]
      have hz : ∀ n, intSum (fun _ => (0 : Int)) n = 0 := by
        intro n; induction n with | zero => rfl | succ n ih => simp [intSum, ih]
      rw [hz]; rfl
    · exact hw

theorem two_mul_runD_mod_eq_zero {d w x : Nat} (hd : 1 ≤ d) (hw : w ≤ d) :
    (2 * runD d x) % 2 ^ w = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
  by_cases hi : i < w
  · simp only [hi, decide_true, Bool.true_and, testBit_two_mul]
    by_cases hi1 : 1 ≤ i
    · simp only [hi1, decide_true, Bool.true_and]
      exact testBit_runD_lt_false hd (by omega)
    · simp [hi1]
  · simp [hi]

theorem runT_singleCycle_le {d C w : Nat} (hd : 1 ≤ d) (hw1 : 1 ≤ w) (hwd : w ≤ d) :
    IsSingleCycle (runT d C) w ↔ C.testBit 0 = true := by
  have hmod : ∀ x, runT d C x % 2 ^ w = (x + C) % 2 ^ w := by
    intro x
    unfold runT
    rw [Nat.add_mod, mod_two_pow_or, two_mul_runD_mod_eq_zero hd hwd, Nat.zero_or, ← Nat.add_mod]
  rw [singleCycle_congr_mod (add_const_oneLip C) hmod]
  exact add_const_singleCycle_iff C w hw1

theorem intSum_const (c : Int) (n : Nat) : intSum (fun _ => c) n = (n : Int) * c := by
  induction n with
  | zero => simp [intSum]
  | succ n ih =>
    simp only [intSum, ih, Int.natCast_succ]
    rw [Int.add_mul, Int.one_mul]

theorem runD_testBit_top_iff {d r : Nat} (hd : 1 ≤ d) (hr : r < 2 ^ d) :
    (runD d r).testBit (d - 1) = true ↔ r = 2 ^ d - 1 := by
  rw [testBit_runD_true_iff hd r (d - 1)]
  constructor
  · rintro ⟨_, hall⟩
    apply Nat.eq_of_testBit_eq
    intro i
    rw [testBit_two_pow_sub_one d i]
    by_cases hi : i < d
    · simp only [hi, decide_true]
      have h := hall (d - 1 - i) (by omega)
      have heq : d - 1 - (d - 1 - i) = i := by omega
      rw [heq] at h
      exact h
    · simp only [hi, decide_false]
      exact testBit_eq_false_of_lt_two_pow hr (by omega)
  · intro heq
    subst heq
    refine ⟨Nat.le_refl _, fun s hs => ?_⟩
    rw [testBit_two_pow_sub_one]
    have hlt : d - 1 - s < d := by omega
    simp [hlt]

theorem runT_holonomy_at_d {d C : Nat} (hd : 2 ≤ d) (hC0 : C.testBit 0 = true) :
    holonomy (runT d C) d = C.testBit d := by
  have hsc_d : IsSingleCycle (runT d C) d :=
    (runT_singleCycle_le (by omega) (by omega) (Nat.le_refl d)).mpr hC0
  have hdef := defectSum_mod_eq_holonomy (runT_oneLip d C (by omega)) hsc_d
  have hpos_d : (0 : Int) < 2 ^ d := by
    rw [← natCast_two_pow]; exact Int.natCast_pos.mpr (two_pow_pos d)
  have hpow_succ : (2 ^ (d + 1) : Int) = (2 ^ d : Int) + (2 ^ d : Int) := by
    rw [Int.pow_succ]; omega
  -- Compute defectSum (runT d C) d % 2^(d+1) explicitly!
  have hterm_lt : ∀ r < 2 ^ d - 1,
      (((runT d C r : Int) - (r : Int)) % (2 ^ (d + 1) : Int)) = ((C % 2 ^ (d + 1) : Nat) : Int) := by
    intro r hr
    unfold runT
    have hdiff : ((r + ((2 * runD d r) ||| C) : Nat) : Int) - (r : Int) =
        (((2 * runD d r) ||| C : Nat) : Int) := by
      rw [Int.natCast_add]; omega
    rw [hdiff, ← natCast_two_pow, ← Int.natCast_emod]
    congr 1
    rw [mod_two_pow_or]
    have hzero : (2 * runD d r) % 2 ^ (d + 1) = 0 := by
      rw [mod_two_pow_succ_decomp, two_mul_runD_mod_eq_zero (by omega) (Nat.le_refl d)]
      rw [testBit_two_mul]
      have h1 : 1 ≤ d := by omega
      simp only [h1, decide_true, Bool.true_and]
      have hbf : (runD d r).testBit (d - 1) = false := by
        cases h : (runD d r).testBit (d - 1)
        · rfl
        · have heq := (runD_testBit_top_iff (by omega) (by omega)).mp h
          omega
      rw [hbf]; simp
    rw [hzero, Nat.zero_or]
  have hterm_last :
      (((runT d C (2 ^ d - 1) : Int) - ((2 ^ d - 1 : Nat) : Int)) % (2 ^ (d + 1) : Int)) =
        (((C % 2 ^ (d + 1) : Nat) : Int) + (if C.testBit d then 0 else (2 ^ d : Int))) % (2 ^ (d + 1) : Int) := by
    unfold runT
    have hdiff : (((2 ^ d - 1) + ((2 * runD d (2 ^ d - 1)) ||| C) : Nat) : Int) - ((2 ^ d - 1 : Nat) : Int) =
        (((2 * runD d (2 ^ d - 1)) ||| C : Nat) : Int) := by
      rw [Int.natCast_add]; omega
    rw [hdiff, ← natCast_two_pow, ← Int.natCast_emod]
    have hval : ((2 * runD d (2 ^ d - 1)) ||| C) % 2 ^ (d + 1) =
        C % 2 ^ (d + 1) + if C.testBit d then 0 else 2 ^ d := by
      have hmod2r : (2 * runD d (2 ^ d - 1)) % 2 ^ (d + 1) = 2 ^ d := by
        rw [mod_two_pow_succ_decomp, two_mul_runD_mod_eq_zero (by omega) (Nat.le_refl d)]
        rw [testBit_two_mul]
        have h1 : 1 ≤ d := by omega
        simp only [h1, decide_true, Bool.true_and]
        have hbt : (runD d (2 ^ d - 1)).testBit (d - 1) = true :=
          (runD_testBit_top_iff (by omega) (by have := two_pow_pos d; omega)).mpr rfl
        rw [hbt]; simp
      rw [mod_two_pow_or, hmod2r]
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_or, Nat.testBit_two_pow, Nat.testBit_mod_two_pow]
      cases hCd : C.testBit d
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hC_lt : C % 2 ^ (d + 1) < 2 ^ d := by
          rw [mod_two_pow_succ_decomp, hCd]; simp; exact Nat.mod_lt C (two_pow_pos d)
        rw [testBit_add_two_pow_of_lt hC_lt i, Nat.testBit_mod_two_pow]
        by_cases hi : i < d + 1
        · by_cases heq : i = d
          · subst heq; simp [hCd]
          · have hne1 : d ≠ i := by omega
            have hne2 : i ≠ d := by omega
            simp [hi, hne1, hne2]
        · have hne1 : d ≠ i := by omega
          have hne2 : i ≠ d := by omega
          simp [hi, hne1, hne2]
      · simp only [↓reduceIte, Nat.add_zero, Nat.testBit_mod_two_pow]
        by_cases heq : d = i
        · subst heq; simp [hCd]
        · simp [heq]
    rw [hval]
    have hlt_rhs : C % 2 ^ (d + 1) + (if C.testBit d then 0 else 2 ^ d) < 2 ^ (d + 1) := by
      have hdec := mod_two_pow_succ_decomp C d
      have hltC := Nat.mod_lt C (two_pow_pos d)
      have h2d := two_pow_succ_eq d
      cases hCd : C.testBit d
      · rw [hCd] at hdec; simp at hdec ⊢; omega
      · rw [hCd] at hdec; simp at hdec ⊢; omega
    have hcast : ((C % 2 ^ (d + 1) + if C.testBit d then 0 else 2 ^ d : Nat) : Int) =
        ((C % 2 ^ (d + 1) : Nat) : Int) + (if C.testBit d then 0 else (2 ^ d : Int)) := by
      cases C.testBit d <;> simp [Int.natCast_add]
    rw [hcast, natCast_two_pow, Int.emod_eq_of_lt]
    · cases C.testBit d <;> simp <;> omega
    · rw [← hcast, ← natCast_two_pow]; exact Int.ofNat_lt.mpr hlt_rhs
  have hsum_eval : defectSum (runT d C) d % (2 ^ (d + 1) : Int) =
      ((2 ^ d : Int) * ((C % 2 ^ (d + 1) : Nat) : Int) + (if C.testBit d then 0 else (2 ^ d : Int))) % (2 ^ (d + 1) : Int) := by
    unfold defectSum
    have hpow_split : 2 ^ d = (2 ^ d - 1) + 1 := by have := two_pow_pos d; omega
    calc intSum (fun r => (runT d C r : Int) - (r : Int)) (2 ^ d) % (2 ^ (d + 1) : Int)
        = intSum (fun r => (runT d C r : Int) - (r : Int)) ((2 ^ d - 1) + 1) % (2 ^ (d + 1) : Int) := by
            rw [← hpow_split]
      _ = (intSum (fun r => (runT d C r : Int) - (r : Int)) (2 ^ d - 1) +
            ((runT d C (2 ^ d - 1) : Int) - ((2 ^ d - 1 : Nat) : Int))) % (2 ^ (d + 1) : Int) := rfl
      _ = (intSum (fun r => (runT d C r : Int) - (r : Int)) (2 ^ d - 1) % (2 ^ (d + 1) : Int) +
            ((runT d C (2 ^ d - 1) : Int) - ((2 ^ d - 1 : Nat) : Int)) % (2 ^ (d + 1) : Int)) % (2 ^ (d + 1) : Int) :=
            Int.add_emod _ _ _
      _ = (intSum (fun _ => ((C % 2 ^ (d + 1) : Nat) : Int)) (2 ^ d - 1) % (2 ^ (d + 1) : Int) +
            (((C % 2 ^ (d + 1) : Nat) : Int) + (if C.testBit d then 0 else (2 ^ d : Int))) % (2 ^ (d + 1) : Int)) % (2 ^ (d + 1) : Int) := by
            rw [hterm_last]
            congr 1; congr 1
            apply intSum_mod_congr
            intro r hr
            rw [hterm_lt r hr]
            have hlt := Nat.mod_lt C (two_pow_pos (d + 1))
            rw [← natCast_two_pow, ← Int.natCast_emod, Nat.mod_eq_of_lt hlt]
      _ = (intSum (fun _ => ((C % 2 ^ (d + 1) : Nat) : Int)) (2 ^ d - 1) +
            (((C % 2 ^ (d + 1) : Nat) : Int) + (if C.testBit d then 0 else (2 ^ d : Int)))) % (2 ^ (d + 1) : Int) :=
            (Int.add_emod _ _ _).symm
      _ = ((2 ^ d : Int) * ((C % 2 ^ (d + 1) : Nat) : Int) + (if C.testBit d then 0 else (2 ^ d : Int))) % (2 ^ (d + 1) : Int) := by
            rw [intSum_const]
            have hcast_d : (((2 ^ d - 1 : Nat) : Int) + 1) = (2 ^ d : Int) := by
              rw [← natCast_two_pow]; have := two_pow_pos d; omega
            have hrew : ((2 ^ d - 1 : Nat) : Int) * ((C % 2 ^ (d + 1) : Nat) : Int) +
                (((C % 2 ^ (d + 1) : Nat) : Int) + (if C.testBit d then 0 else (2 ^ d : Int))) =
                (((2 ^ d - 1 : Nat) : Int) + 1) * ((C % 2 ^ (d + 1) : Nat) : Int) +
                (if C.testBit d then 0 else (2 ^ d : Int)) := by
              rw [Int.add_mul, Int.one_mul]; omega
            rw [hrew, hcast_d]
  have h2dC : ((2 ^ d : Int) * ((C % 2 ^ (d + 1) : Nat) : Int)) % (2 ^ (d + 1) : Int) = (2 ^ d : Int) := by
    have hpow2 : (2 ^ (d + 1) : Int) = (2 ^ d : Int) * 2 := by rw [Int.pow_succ]
    rw [hpow2, int_mul_emod_mul_pos hpos_d _ 2 (by decide)]
    have hodd : ((C % 2 ^ (d + 1) : Nat) : Int) % 2 = 1 := by
      have hdvd : 2 ∣ 2 ^ (d + 1) := by
        rw [Nat.pow_succ]; exact Nat.dvd_mul_left 2 _
      have hmod2 : (C % 2 ^ (d + 1)) % 2 = C % 2 := Nat.mod_mod_of_dvd C hdvd
      have hC1 : C % 2 = 1 := by
        rw [testBit_eq_div_mod, Nat.pow_zero, Nat.div_one] at hC0
        exact beq_iff_eq.mp hC0
      have hcast2 : ((C % 2 ^ (d + 1) : Nat) : Int) % (2 : Int) = (((C % 2 ^ (d + 1)) % 2 : Nat) : Int) := by
        exact (Int.natCast_emod (C % 2 ^ (d + 1)) 2).symm
      rw [hcast2, hmod2, hC1]; rfl
    rw [hodd, Int.mul_one]
  rw [hsum_eval, Int.add_emod, h2dC] at hdef
  cases hCd : C.testBit d <;> rw [hCd] at hdef
  · simp only [Bool.false_eq_true, ↓reduceIte] at hdef
    have hmod_2d : (2 ^ d : Int) % (2 ^ (d + 1) : Int) = (2 ^ d : Int) :=
      Int.emod_eq_of_lt (by omega) (by omega)
    have hmod0 : ((2 ^ d : Int) + (2 ^ d : Int) % (2 ^ (d + 1) : Int)) % (2 ^ (d + 1) : Int) = 0 := by
      rw [hmod_2d, ← hpow_succ, Int.emod_self]
    rw [hmod0] at hdef
    cases hhol : holonomy (runT d C) d
    · rfl
    · rw [hhol] at hdef; simp at hdef; omega
  · simp only [↓reduceIte, Int.zero_emod, Int.add_zero] at hdef
    rw [Int.emod_eq_of_lt (by omega) (by omega)] at hdef
    cases hhol : holonomy (runT d C) d
    · rw [hhol] at hdef; simp at hdef; omega
    · rfl

theorem runT_curvature_zero {d C w : Nat} (hd : 2 ≤ d) (hw : d ≤ w) :
    curvatureSum (runT d C) w % (2 ^ (w + 2) : Int) = 0 := by
  have hderiv := runT_hasUnitSliceDeriv d C w (by omega)
  rw [curvatureSum_zero_iff_bitXorSum hderiv]
  by_cases hC : C.testBit (w + 1) = true
  · have hcongr : bitXorSum (curvatureBit (runT d C) w) (2 ^ w) =
        bitXorSum (fun _ => false) (2 ^ w) := by
      apply bitXorSum_congr
      intro r _
      unfold runT
      rw [curvatureBit_add_twoLip (runT_core_twoLip d C (by omega) w (r + 2 ^ w) r (Nat.add_mod_right r (2 ^ w)))]
      rw [Nat.testBit_or, Nat.testBit_or, hC]; simp
    rw [hcongr, bitXorSum_const_false]
  · have hCf : C.testBit (w + 1) = false := by
      cases h : C.testBit (w + 1)
      · rfl
      · exact absurd h hC
    have hcongr : bitXorSum (curvatureBit (runT d C) w) (2 ^ w) =
        bitXorSum (fun r => (runD d (r + 2 ^ w)).testBit w) (2 ^ w) := by
      apply bitXorSum_congr
      intro r hr
      unfold runT
      rw [curvatureBit_add_twoLip (runT_core_twoLip d C (by omega) w (r + 2 ^ w) r (Nat.add_mod_right r (2 ^ w)))]
      rw [Nat.testBit_or, Nat.testBit_or, hCf, Bool.or_false, Bool.or_false]
      rw [testBit_two_mul, testBit_two_mul]
      simp only [Nat.le_add_left, decide_true, Bool.true_and, Nat.add_sub_cancel]
      rw [runD_testBit_of_lt (by omega) hr, Bool.xor_false]
    rw [hcongr]
    -- Bit-flip involution at bit 0: since w ≥ d, all indices w - s (1 ≤ s < d) satisfy w - s ≥ 1 > 0!
    apply bitXorSum_eq_false_of_bitflip (j := 0) (by omega)
    intro r hr
    have hr' : (r ^^^ 1) < 2 ^ w := xor_lt_two_pow hr (by have : 2 ^ 0 < 2 ^ w := Nat.pow_lt_pow_right (by decide) (by omega); exact this)
    have hpow0 : 2 ^ 0 = 1 := rfl
    rw [hpow0]
    cases h1 : (runD d (r + 2 ^ w)).testBit w
    · cases h2 : (runD d ((r ^^^ 1) + 2 ^ w)).testBit w
      · rfl
      · exfalso
        have ⟨hge, hall⟩ := (runD_add_two_pow_testBit (by omega) hr').mp h2
        have ht : (runD d (r + 2 ^ w)).testBit w = true := by
          rw [runD_add_two_pow_testBit (by omega) hr]
          refine ⟨hge, fun s hs1 hsd => ?_⟩
          have hb := hall s hs1 hsd
          rw [Nat.testBit_xor] at hb
          have hbit1 : (1 : Nat).testBit (w - s) = false := by
            have h0 : (1 : Nat) = 2 ^ 0 := rfl
            rw [h0, Nat.testBit_two_pow]
            have hne : 0 ≠ w - s := by omega
            simp [hne]
          simpa [hbit1] using hb
        rw [h1] at ht; exact absurd ht (by decide)
    · have ⟨hge, hall⟩ := (runD_add_two_pow_testBit (by omega) hr).mp h1
      have h2 : (runD d ((r ^^^ 1) + 2 ^ w)).testBit w = true := by
        rw [runD_add_two_pow_testBit (by omega) hr']
        refine ⟨hge, fun s hs1 hsd => ?_⟩
        rw [Nat.testBit_xor]
        have hbit1 : (1 : Nat).testBit (w - s) = false := by
          have h0 : (1 : Nat) = 2 ^ 0 := rfl
          rw [h0, Nat.testBit_two_pow]
          have hne : 0 ≠ w - s := by omega
          simp [hne]
        rw [hbit1, Bool.xor_false]
        exact hall s hs1 hsd
      exact h2

/-- **THEOREM B1 (Complete Infinite Classification of the Arbitrary-Order `d`-Run Family `runT`):**
For EVERY `d ≥ 2` and EVERY `C : Nat`, `runT d C` is single-cycle mod `2^w` for ALL `w ≥ 1`
if and only if `C` is odd AND bit `d` of `C` is `1`. -/
theorem runT_singleCycle_iff {d : Nat} (hd : 2 ≤ d) (C : Nat) :
    (∀ w, 1 ≤ w → IsSingleCycle (runT d C) w) ↔ (C.testBit 0 = true ∧ C.testBit d = true) := by
  constructor
  · intro hall
    have hC0 : C.testBit 0 = true :=
      (runT_singleCycle_le (by omega) (by omega) (by omega)).mp (hall 1 (by omega))
    have hsc_d : IsSingleCycle (runT d C) d := hall d (by omega)
    have hsc_d1 : IsSingleCycle (runT d C) (d + 1) := hall (d + 1) (by omega)
    have hhol := ((singleCycle_succ_iff (runT_oneLip d C (by omega)) hsc_d).mp hsc_d1).2
    rw [runT_holonomy_at_d hd hC0] at hhol
    exact ⟨hC0, hhol⟩
  · rintro ⟨hC0, hCd⟩
    have hsc_d : IsSingleCycle (runT d C) d :=
      (runT_singleCycle_le (by omega) (by omega) (Nat.le_refl d)).mpr hC0
    have hhol : holonomy (runT d C) d = true := by
      rw [runT_holonomy_at_d hd hC0]; exact hCd
    have hsc_d1 : IsSingleCycle (runT d C) (d + 1) :=
      (singleCycle_succ_iff (runT_oneLip d C (by omega)) hsc_d).mpr
        ⟨runT_hasUnitSliceDeriv d C d (by omega), hhol⟩
    exact lift_singleCycle_from_curvatureSum d (runT_oneLip d C (by omega)) hsc_d1
      (fun w _ => runT_hasUnitSliceDeriv d C (w + 1) (by omega))
      (fun w hw => runT_curvature_zero hd hw)

/-- **THEOREM B2 (Sharp Threshold Failure at Exact Width `d + 1`):**
For EVERY `d ≥ 2`, `runT d 1` is single-cycle for EVERY width `1 ≤ w ≤ d`,
yet FAILS single-cycle ergodicity at width `d + 1`. -/
theorem runT_sharp_threshold {d : Nat} (hd : 2 ≤ d) :
    (∀ w, 1 ≤ w → w ≤ d → IsSingleCycle (runT d 1) w) ∧ ¬ IsSingleCycle (runT d 1) (d + 1) := by
  have h10 : (1 : Nat).testBit 0 = true := by decide
  have h1d : (1 : Nat).testBit d = false := by
    have h0 : (1 : Nat) = 2 ^ 0 := rfl
    rw [h0, Nat.testBit_two_pow]
    have hne : 0 ≠ d := by omega
    simp [hne]
  constructor
  · intro w hw1 hwd
    exact (runT_singleCycle_le (by omega) hw1 hwd).mpr h10
  · intro hsc_d1
    have hsc_d : IsSingleCycle (runT d 1) d :=
      (runT_singleCycle_le (by omega) (by omega) (Nat.le_refl d)).mpr h10
    have hhol := ((singleCycle_succ_iff (runT_oneLip d 1 (by omega)) hsc_d).mp hsc_d1).2
    rw [runT_holonomy_at_d hd h10, h1d] at hhol
    exact absurd hhol (by decide)

/-- **THEOREM B3 (No-Universal-Finite-Threshold Theorem for 1-Lipschitz T-Functions):**
In stark contrast to integer polynomials (Larin's mod-8 theorem), NO finite width `W ≥ 1`
suffices universally for 1-Lipschitz bitwise T-functions: for EVERY `W ≥ 1`, there exists
an explicit 1-Lipschitz T-function that is single-cycle for all `1 ≤ w ≤ W` yet fails at `W + 1`. -/
theorem no_universal_finite_threshold :
    ∀ W, 1 ≤ W → ∃ f : Nat → Nat, IsOneLipschitz f ∧
      (∀ w, 1 ≤ w → w ≤ W → IsSingleCycle f w) ∧ ¬ IsSingleCycle f (W + 1) := by
  intro W hW
  by_cases hW1 : W = 1
  · subst hW1
    refine ⟨fun x => 3 * x + 1, ?_, ?_, ?_⟩
    · intro w x y hxy; dsimp only; rw [Nat.add_mod, Nat.mul_mod, hxy, ← Nat.mul_mod, ← Nat.add_mod]
    · intro w hw1 hw2
      have hw : w = 1 := by omega
      subst hw
      have hlip : IsOneLipschitz (fun x => 3 * x + 1) := by
        intro w x y hxy; dsimp only; rw [Nat.add_mod, Nat.mul_mod, hxy, ← Nat.mul_mod, ← Nat.add_mod]
      exact (checkSingleCycle_iff hlip 1).mp (by decide)
    · intro hsc2
      have hlip : IsOneLipschitz (fun x => 3 * x + 1) := by
        intro w x y hxy; dsimp only; rw [Nat.add_mod, Nat.mul_mod, hxy, ← Nat.mul_mod, ← Nat.add_mod]
      have hchk := (checkSingleCycle_iff hlip 2).mpr hsc2
      exact absurd hchk (by decide)
  · have hge2 : 2 ≤ W := by omega
    exact ⟨runT W 1, runT_oneLip W 1 (by omega),
      (runT_sharp_threshold hge2).1, (runT_sharp_threshold hge2).2⟩

/-! ## Section 10: Surprising Corollaries, Sharpness Counterexamples, & Non-Vacuity Witnesses -/

/-- **COROLLARY A3 (Bit-2 Obstruction Mutual Annihilation):**
At `C = 1`:
  (1) Klimov-Shamir `x ↦ x + ((x * x) ||| 1)` FAILS at `w = 3` (mod 8);
  (2) Pure 2-run `x ↦ x + ((2 * runD 2 x) ||| 1)` FAILS at `w = 3` (mod 8);
  (3) Yet their XOR hybrid `x ↦ x + (((x * x) ^^^ (2 * runD 2 x)) ||| 1)` is single-cycle `∀ w ≥ 1`! -/
theorem defect_annihilation_hybrid :
    ¬ IsSingleCycle (fun x => x + ((x * x) ||| 1)) 3 ∧
    ¬ IsSingleCycle (runT 2 1) 3 ∧
    (∀ w, 1 ≤ w → IsSingleCycle (hybridH 1 0 1 0) w) := by
  refine ⟨?_, (runT_sharp_threshold (by omega)).2, ?_⟩
  · intro hsc
    have hlip : IsOneLipschitz (fun x => x + ((x * x) ||| 1)) := by
      intro w x y hxy; dsimp only
      rw [Nat.add_mod, hxy, mod_two_pow_or, Nat.mul_mod, hxy, ← Nat.mul_mod, ← mod_two_pow_or, ← Nat.add_mod]
    exact absurd ((checkSingleCycle_iff hlip 3).mpr hsc) (by decide)
  · exact (hybridH_singleCycle_iff_bits 1 0 1 0).mpr (by decide)

/-- **SHARPNESS WITNESS A4 (`w ≤ 4` is tight for `hybridH`):**
`hybridH 1 1 1 1` passes mod 2, mod 4, AND mod 8 (`w = 1, 2, 3`), yet FAILS at `w = 4` (mod 16). -/
theorem hybridH_w3_pass_w4_fail :
    (∀ w, 1 ≤ w → w ≤ 3 → IsSingleCycle (hybridH 1 1 1 1) w) ∧
    ¬ IsSingleCycle (hybridH 1 1 1 1) 4 := by
  have hlip := hybridH_oneLip 1 1 1 1
  have h3 : IsSingleCycle (hybridH 1 1 1 1) 3 := (checkSingleCycle_iff hlip 3).mp (by decide)
  refine ⟨fun w _ hw3 => singleCycle_of_ge hlip hw3 h3, ?_⟩
  intro h4
  have hbits := (hybridH_singleCycle_iff_bits 1 1 1 1).mp ((hybridH_singleCycle_iff_w4 1 1 1 1).mpr h4)
  have hC3 : (1 : Nat).testBit 3 = true := hbits.2.2.2 (by decide)
  exact absurd hC3 (by decide)

/-- **KERNEL-CHECKED NON-VACUITY WITNESS 1 (Engine Hypotheses Jointly Inhabited on Non-Trivial Hybrid):**
Concrete witness `hybridH 1 1 9 3` (all 4 nonlinear/bitwise/carry-mask layers active!) is
1-Lipschitz, single-cycle for ALL `w ≥ 1`, transitive on every `2^w`, and exact period `2^w`. -/
theorem nonvacuity_hybridH_1_1_9_3 :
    IsOneLipschitz (hybridH 1 1 9 3) ∧
    (∀ w, 1 ≤ w → IsSingleCycle (hybridH 1 1 9 3) w) ∧
    (∀ w, 1 ≤ w → ∀ x y, ∃ k < 2 ^ w, iter (hybridH 1 1 9 3) k x % 2 ^ w = y % 2 ^ w) := by
  have hlip := hybridH_oneLip 1 1 9 3
  have hall : ∀ w, 1 ≤ w → IsSingleCycle (hybridH 1 1 9 3) w :=
    (hybridH_singleCycle_iff_bits 1 1 9 3).mpr (by decide)
  exact ⟨hlip, hall, fun w hw => singleCycle_transitive hlip (hall w hw)⟩

/-- **KERNEL-CHECKED NON-VACUITY WITNESS 2 (Engine `lift_singleCycle_from_w4` Hypothesis Bundle):**
Direct constructive witness that the full hypothesis tuple of `lift_singleCycle_from_w4` is inhabited. -/
theorem nonvacuity_engine_w4_bundle :
    ∃ f : Nat → Nat,
      IsOneLipschitz f ∧
      IsSingleCycle f 4 ∧
      (∀ w, 3 ≤ w → HasUnitSliceDeriv f (w + 1)) ∧
      (∀ w, 3 ≤ w → curvatureSum f w % (2 ^ (w + 2) : Int) = 0) :=
  ⟨hybridBase 1 1 9,
   hybridBase_oneLip 1 1 9,
   (checkSingleCycle_iff (hybridBase_oneLip 1 1 9) 4).mp (by decide),
   fun _ hw => hasUnitSliceDeriv_add_twoLip (fun _ _ => hybridCore_twoLip_ge2 1 1 9 (by omega)),
   fun _ hw => hybridBase_curvature_zero 1 1 9 hw⟩

/-- **KERNEL-CHECKED NON-VACUITY WITNESS 3 (High-Order `d = 5` Run Family with `C = 33`):** -/
theorem nonvacuity_runT_5_33 :
    (∀ w, 1 ≤ w → IsSingleCycle (runT 5 33) w) ∧ ¬ IsSingleCycle (runT 5 1) 6 :=
  ⟨(runT_singleCycle_iff (by omega) 33).mpr (by decide), (runT_sharp_threshold (by omega)).2⟩


/-! ## Section 11: Axiom Audit (`#print axioms`) -/

end SiliconTFunc
