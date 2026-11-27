/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BsdaMixedBitwisePermPolys.Defs

/-!
# Theorems (`BsdaMixedBitwisePermPolys`)

Task 17 (dynsil-17): Mixed Bitwise-Arithmetic Permutation-Polynomial Engine Mod 2^w
  Standalone Lean 4.36.0 — Zero Mathlib, Zero Lake, Zero `sorry`, Standard Axioms Only.
-/


namespace MixedPermEngine
/-- Output bit `i` of `f` when input bit `i` is `0` (with lower bits `x : BitVec i`). -/
def val0 (f : ∀ w : Nat, BitVec w → BitVec w) (i : Nat) (x : BitVec i) : Bool :=
  (f (i + 1) (BitVec.cons false x)).msb

theorem setWidth_cons_eq {w : Nat} (b : Bool) (x : BitVec w) :
    (BitVec.cons b x).setWidth w = x := by
  ext i hi
  simp

theorem cons_msb_setWidth {w : Nat} (x : BitVec (w + 1)) :
    BitVec.cons x.msb (x.setWidth w) = x := by
  ext i hi
  rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem]
  rw [BitVec.getLsbD_cons]
  by_cases h : i = w
  · subst h; simp [BitVec.msb_eq_getLsbD_last]
  · have hlt : i < w := by omega
    simp [h, hlt]

theorem bitVec_eq_iff_msb_and_setWidth {w : Nat} (x y : BitVec (w + 1)) :
    x = y ↔ x.msb = y.msb ∧ x.setWidth w = y.setWidth w := by
  constructor
  · intro h; subst h; exact ⟨rfl, rfl⟩
  · rintro ⟨hm, ht⟩
    rw [← cons_msb_setWidth x, ← cons_msb_setWidth y, hm, ht]

/-- Inductive step of bit-slice lifting: for a coherent family `f`,
    `f (w + 1)` is bijective iff `f w` is bijective and every fiber flips its MSB. -/
theorem bijective_succ_iff {f : ∀ w, BitVec w → BitVec w} (hf : Coherent f) (w : Nat) :
    Bijective (f (w + 1)) ↔
      Bijective (f w) ∧ ∀ x : BitVec w, bitDeriv f w x = true := by
  constructor
  · intro ⟨hinj, hsurj⟩
    have hbij_w : Bijective (f w) := by
      constructor
      · intro a b hab
        have ht0 : (f (w + 1) (BitVec.cons false a)).setWidth w = f w a := by
          rw [hf w, setWidth_cons_eq]
        have ht1 : (f (w + 1) (BitVec.cons true a)).setWidth w = f w a := by
          rw [hf w, setWidth_cons_eq]
        have htb : (f (w + 1) (BitVec.cons false b)).setWidth w = f w a := by
          rw [hf w, setWidth_cons_eq, hab]
        have hne_msb : (f (w + 1) (BitVec.cons false a)).msb ≠ (f (w + 1) (BitVec.cons true a)).msb := by
          intro hmeq
          have heq : f (w + 1) (BitVec.cons false a) = f (w + 1) (BitVec.cons true a) :=
            (bitVec_eq_iff_msb_and_setWidth _ _).2 ⟨hmeq, by rw [ht0, ht1]⟩
          have hcons := hinj _ _ heq
          have hfalse_true : false = true := by
            have := congrArg BitVec.msb hcons
            simp [BitVec.msb_cons] at this
          exact Bool.false_ne_true hfalse_true
        by_cases h0 : (f (w + 1) (BitVec.cons false b)).msb = (f (w + 1) (BitVec.cons false a)).msb
        · have heq : f (w + 1) (BitVec.cons false b) = f (w + 1) (BitVec.cons false a) :=
            (bitVec_eq_iff_msb_and_setWidth _ _).2 ⟨h0, by rw [htb, ht0]⟩
          have hcons := hinj _ _ heq
          have := congrArg (BitVec.setWidth w) hcons
          simpa [setWidth_cons_eq] using this.symm
        · have h1 : (f (w + 1) (BitVec.cons false b)).msb = (f (w + 1) (BitVec.cons true a)).msb := by
            cases hm : (f (w + 1) (BitVec.cons false b)).msb <;>
            cases hm0 : (f (w + 1) (BitVec.cons false a)).msb <;>
            cases hm1 : (f (w + 1) (BitVec.cons true a)).msb <;> simp_all
          have heq : f (w + 1) (BitVec.cons false b) = f (w + 1) (BitVec.cons true a) :=
            (bitVec_eq_iff_msb_and_setWidth _ _).2 ⟨h1, by rw [htb, ht1]⟩
          have hcons := hinj _ _ heq
          have := congrArg (BitVec.setWidth w) hcons
          simpa [setWidth_cons_eq] using this.symm
      · intro y
        obtain ⟨x, hx⟩ := hsurj (BitVec.cons false y)
        refine ⟨x.setWidth w, ?_⟩
        rw [← hf w x, hx, setWidth_cons_eq]
    refine ⟨hbij_w, ?_⟩
    intro x
    unfold bitDeriv
    have hne : f (w + 1) (BitVec.cons true x) ≠ f (w + 1) (BitVec.cons false x) := by
      intro heq
      have hcons := hinj _ _ heq
      have := congrArg BitVec.msb hcons
      simp [BitVec.msb_cons] at this
    have ht : (f (w + 1) (BitVec.cons true x)).setWidth w =
              (f (w + 1) (BitVec.cons false x)).setWidth w := by
      rw [hf w, hf w, setWidth_cons_eq, setWidth_cons_eq]
    cases hm1 : (f (w + 1) (BitVec.cons true x)).msb <;>
    cases hm0 : (f (w + 1) (BitVec.cons false x)).msb
    · exfalso; exact hne ((bitVec_eq_iff_msb_and_setWidth _ _).2 ⟨hm1.trans hm0.symm, ht⟩)
    · rfl
    · rfl
    · exfalso; exact hne ((bitVec_eq_iff_msb_and_setWidth _ _).2 ⟨hm1.trans hm0.symm, ht⟩)
  · rintro ⟨⟨hinj_w, hsurj_w⟩, hderiv⟩
    constructor
    · intro x y hxy
      have ht : f w (x.setWidth w) = f w (y.setWidth w) := by
        rw [← hf w x, ← hf w y, hxy]
      have hxt : x.setWidth w = y.setWidth w := hinj_w _ _ ht
      have hmsb : x.msb = y.msb := by
        have hd := hderiv (x.setWidth w)
        unfold bitDeriv at hd
        have hx' : f (w + 1) x = f (w + 1) (BitVec.cons x.msb (x.setWidth w)) := by
          rw [cons_msb_setWidth]
        have hy' : f (w + 1) y = f (w + 1) (BitVec.cons y.msb (x.setWidth w)) := by
          rw [hxt, cons_msb_setWidth]
        cases hxm : x.msb <;> cases hym : y.msb
        · rfl
        · rw [hxm] at hx'; rw [hym] at hy'
          have hmeq : (f (w + 1) (BitVec.cons false (x.setWidth w))).msb =
                      (f (w + 1) (BitVec.cons true (x.setWidth w))).msb := by
            rw [← hx', ← hy', hxy]
          rw [hmeq] at hd; simp at hd
        · rw [hxm] at hx'; rw [hym] at hy'
          have hmeq : (f (w + 1) (BitVec.cons true (x.setWidth w))).msb =
                      (f (w + 1) (BitVec.cons false (x.setWidth w))).msb := by
            rw [← hx', ← hy', hxy]
          rw [hmeq] at hd; simp at hd
        · rfl
      exact (bitVec_eq_iff_msb_and_setWidth x y).2 ⟨hmsb, hxt⟩
    · intro y
      obtain ⟨x0, hx0⟩ := hsurj_w (y.setWidth w)
      have hd := hderiv x0
      unfold bitDeriv at hd
      by_cases hcase : (f (w + 1) (BitVec.cons false x0)).msb = y.msb
      · refine ⟨BitVec.cons false x0, ?_⟩
        exact (bitVec_eq_iff_msb_and_setWidth _ _).2 ⟨hcase, by rw [hf w, setWidth_cons_eq, hx0]⟩
      · refine ⟨BitVec.cons true x0, ?_⟩
        have htrue : (f (w + 1) (BitVec.cons true x0)).msb = y.msb := by
          cases h1 : (f (w + 1) (BitVec.cons true x0)).msb <;>
          cases h0 : (f (w + 1) (BitVec.cons false x0)).msb <;>
          cases hy : y.msb <;> simp_all
        exact (bitVec_eq_iff_msb_and_setWidth _ _).2 ⟨htrue, by rw [hf w, setWidth_cons_eq, hx0]⟩

/-- Universal Bit-Slice Lifting Theorem: a coherent family `f` is bijective at width `w`
    iff every bit-slice derivative `bitDeriv f i x` is `true` for all `i < w`. -/
theorem bijective_iff_forall_bitDeriv {f : ∀ w, BitVec w → BitVec w} (hf : Coherent f) (w : Nat) :
    Bijective (f w) ↔ ∀ (i : Nat), i < w → ∀ x : BitVec i, bitDeriv f i x = true := by
  induction w with
  | zero =>
    constructor
    · intro _ i hi; omega
    · intro _
      constructor
      · intro x y _; exact Subsingleton.elim x y
      · intro y; exact ⟨0#0, Subsingleton.elim _ _⟩
  | succ w ih =>
    rw [bijective_succ_iff hf w, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi x
      by_cases hlt : i < w
      · exact h1 i hlt x
      · have heq : i = w := by omega
        subst heq; exact h2 x
    · intro hall
      exact ⟨fun i hi x => hall i (by omega) x, fun x => hall w (by omega) x⟩

/-- Bijectivity for all `w ≥ 2` is equivalent to every bit-slice derivative being `true`
    for all `i : Nat` (and equivalent to bijectivity for all `w : Nat`). -/
theorem bijective_all_ge_two_iff {f : ∀ w, BitVec w → BitVec w} (hf : Coherent f) :
    (∀ w, 2 ≤ w → Bijective (f w)) ↔
      ∀ (i : Nat) (x : BitVec i), bitDeriv f i x = true := by
  constructor
  · intro hall i x
    have hbij := hall (max 2 (i + 1)) (Nat.le_max_left _ _)
    exact (bijective_iff_forall_bitDeriv hf _).1 hbij i (by omega) x
  · intro hall w _
    exact (bijective_iff_forall_bitDeriv hf w).2 (fun i _ x => hall i x)

theorem testBit_eq_false_of_natSigBits_le (m i : Nat) (hi : natSigBits m ≤ i) :
    m.testBit i = false := by
  unfold natSigBits at hi
  by_cases hm : m = 0
  · subst hm; simp
  · simp only [hm, ↓reduceIte] at hi
    have h1 : m < 2 ^ (Nat.log2 m + 1) := Nat.lt_log2_self
    have hlt : m < 2 ^ i := Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) hi)
    exact Nat.testBit_lt_two_pow hlt

theorem intBit_stable (c : Int) (i : Nat) (hi : intSigBits c ≤ i) :
    intBit c i = decide (c < 0) := by
  cases c with
  | ofNat n =>
    simp only [intBit, intSigBits] at hi ⊢
    have hnot : ¬ (Int.ofNat n < 0) := Int.not_lt.2 (Int.natCast_nonneg n)
    simp only [hnot, decide_false]
    exact testBit_eq_false_of_natSigBits_le n i hi
  | negSucc n =>
    simp only [intBit, intSigBits] at hi ⊢
    have hlt : Int.negSucc n < 0 := Int.negSucc_lt_zero n
    simp only [hlt, decide_true]
    rw [testBit_eq_false_of_natSigBits_le n i hi]
    rfl

theorem getLsbD_ofInt_eq_intBit (w : Nat) (c : Int) (i : Nat) (hi : i < w) :
    (BitVec.ofInt w c).getLsbD i = intBit c i := by
  cases c with
  | ofNat n =>
    have hc : BitVec.ofInt w (Int.ofNat n) = BitVec.ofNat w n := rfl
    rw [hc, BitVec.getLsbD_ofNat]
    simp [hi, intBit]
  | negSucc n =>
    have hofInt : BitVec.ofInt w (Int.negSucc n) = ~~~(BitVec.ofNat w n) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofInt, BitVec.toNat_not, BitVec.toNat_ofNat]
      have hp : 0 < 2 ^ w := Nat.two_pow_pos w
      have hmod : n % 2 ^ w < 2 ^ w := Nat.mod_lt n hp
      have hneg : Int.negSucc n = -(n : Int) - 1 := by
        rw [Int.negSucc_eq]; omega
      rw [hneg]
      have hdiv : (n : Int) = (2 ^ w : Nat) * ((n / 2 ^ w : Nat) : Int) + ((n % 2 ^ w : Nat) : Int) := by
        have := Nat.div_add_mod n (2 ^ w)
        omega
      have hrewrite : -(n : Int) - 1 =
          (2 ^ w : Nat) * (-((n / 2 ^ w : Nat) : Int) - 1) + ((2 ^ w - 1 - n % 2 ^ w : Nat) : Int) := by
        rw [Int.mul_sub, Int.mul_neg, Int.mul_one]
        omega
      have h1 : (-(n : Int) - 1) % (2 ^ w : Nat) = ((2 ^ w - 1 - n % 2 ^ w : Nat) : Int) := by
        rw [hrewrite, Int.mul_add_emod_self_left]
        exact Int.emod_eq_of_lt (by omega) (by omega)
      rw [h1]
      omega
    rw [hofInt, BitVec.getLsbD_not, BitVec.getLsbD_ofNat]
    simp [hi, intBit]

theorem msb_ofInt_eq_intBit (i : Nat) (c : Int) :
    (BitVec.ofInt (i + 1) c).msb = intBit c i := by
  rw [BitVec.msb_eq_getLsbD_last]
  exact getLsbD_ofInt_eq_intBit (i + 1) c i (by omega)

-- Coherence closure for all 10 operators + composition
theorem coherent_id : Coherent (fun _ x => x) := fun _ _ => rfl

theorem coherent_const (c : Int) : Coherent (fun w _ => BitVec.ofInt w c) := by
  intro w _
  ext i hi
  rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem]
  simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  rw [getLsbD_ofInt_eq_intBit (w + 1) c i (by omega), getLsbD_ofInt_eq_intBit w c i hi]

theorem coherent_not {f} (hf : Coherent f) : Coherent (fun w x => ~~~(f w x)) := by
  intro w x; ext i hi
  rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem]
  have h1 : (f (w + 1) x).getLsbD i = (f w (x.setWidth w)).getLsbD i := by
    rw [← hf w x]; simp [hi]
  simp [hi, h1]

theorem coherent_shl (k : Nat) {f} (hf : Coherent f) : Coherent (fun w x => (f w x) <<< k) := by
  intro w x; ext i hi
  rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem]
  have hi1 : i < w + 1 := by omega
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft, hi, hi1, decide_true, Bool.true_and]
  by_cases hki : i < k
  · simp [hki]
  · have hsub : i - k < w := by omega
    have h1 : (f (w + 1) x).getLsbD (i - k) = ((f (w + 1) x).setWidth w).getLsbD (i - k) := by
      simp [hsub]
    rw [h1, hf w x]

theorem coherent_xor {f g} (hf : Coherent f) (hg : Coherent g) :
    Coherent (fun w x => f w x ^^^ g w x) := by
  intro w x; ext i hi
  rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem]
  have h1 : (f (w + 1) x).getLsbD i = (f w (x.setWidth w)).getLsbD i := by
    rw [← hf w x]; simp [hi]
  have h2 : (g (w + 1) x).getLsbD i = (g w (x.setWidth w)).getLsbD i := by
    rw [← hg w x]; simp [hi]
  simp [hi, h1, h2]

theorem coherent_and {f g} (hf : Coherent f) (hg : Coherent g) :
    Coherent (fun w x => f w x &&& g w x) := by
  intro w x; ext i hi
  rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem]
  have h1 : (f (w + 1) x).getLsbD i = (f w (x.setWidth w)).getLsbD i := by
    rw [← hf w x]; simp [hi]
  have h2 : (g (w + 1) x).getLsbD i = (g w (x.setWidth w)).getLsbD i := by
    rw [← hg w x]; simp [hi]
  simp [hi, h1, h2]

theorem coherent_or {f g} (hf : Coherent f) (hg : Coherent g) :
    Coherent (fun w x => f w x ||| g w x) := by
  intro w x; ext i hi
  rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem]
  have h1 : (f (w + 1) x).getLsbD i = (f w (x.setWidth w)).getLsbD i := by
    rw [← hf w x]; simp [hi]
  have h2 : (g (w + 1) x).getLsbD i = (g w (x.setWidth w)).getLsbD i := by
    rw [← hg w x]; simp [hi]
  simp [hi, h1, h2]

-- Helper: MSB decomposition on `BitVec (i + 1)`
theorem toNat_eq_msb_add_setWidth {i : Nat} (a : BitVec (i + 1)) :
    a.toNat = (a.setWidth i).toNat + (if a.msb then 2 ^ i else 0) := by
  have h1 : a.toNat % 2 ^ i = (a.setWidth i).toNat := by
    simp [BitVec.toNat_setWidth]
  have hlt : a.toNat < 2 ^ (i + 1) := a.isLt
  have hpow : 2 ^ (i + 1) = 2 ^ i * 2 := by rw [Nat.pow_succ]
  have hdiv : a.toNat / 2 ^ i < 2 := by
    have hlt2 : a.toNat < 2 ^ i * 2 := by rw [← hpow]; exact hlt
    exact Nat.div_lt_of_lt_mul hlt2
  have h2 : a.toNat / 2 ^ i = if a.msb then 1 else 0 := by
    have hmsb : a.msb = a.toNat.testBit i := by
      rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_eq_getElem (by omega)]
      simp [BitVec.getElem_eq_testBit_toNat]
    rw [hmsb, Nat.testBit_eq_decide_div_mod_eq, Nat.mod_eq_of_lt hdiv]
    cases hq : a.toNat / 2 ^ i with
    | zero => simp
    | succ k =>
      have hk0 : k = 0 := by omega
      subst hk0; simp
  have hdm := Nat.div_add_mod a.toNat (2 ^ i)
  rw [h1, h2] at hdm
  cases h : a.msb <;> simp [h] at hdm ⊢ <;> omega

theorem setWidth_sub_eq {w : Nat} (a b : BitVec (w + 1)) :
    (a - b).setWidth w = a.setWidth w - b.setWidth w := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub]
  have hdvd : 2 ^ w ∣ 2 ^ (w + 1) := ⟨2, by rw [Nat.pow_succ]⟩
  rw [Nat.mod_mod_of_dvd _ hdvd]
  have ha := toNat_eq_msb_add_setWidth a
  have hb := toNat_eq_msb_add_setWidth b
  have hta := (a.setWidth w).isLt
  have htb := (b.setWidth w).isLt
  have hpow : 2 ^ (w + 1) = 2 ^ w + 2 ^ w := by rw [Nat.pow_succ]; omega
  have hmod : ∀ n m : Nat, (n + 2 ^ w * m) % 2 ^ w = n % 2 ^ w :=
    fun n m => Nat.add_mul_mod_self_left n (2 ^ w) m
  have ha_mod : a.toNat % 2 ^ w = (a.setWidth w).toNat := by simp [BitVec.toNat_setWidth]
  have hb_mod : b.toNat % 2 ^ w = (b.setWidth w).toNat := by simp [BitVec.toNat_setWidth]
  rw [ha_mod, hb_mod]
  cases ham : a.msb <;> cases hbm : b.msb <;>
  simp only [ham, hbm, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at ha hb
  · have heq : 2 ^ (w + 1) - b.toNat + a.toNat = (2 ^ w - (b.setWidth w).toNat + (a.setWidth w).toNat) + 2 ^ w * 1 := by omega
    rw [heq, hmod]
  · have heq : 2 ^ (w + 1) - b.toNat + a.toNat = (2 ^ w - (b.setWidth w).toNat + (a.setWidth w).toNat) := by omega
    rw [heq]
  · have heq : 2 ^ (w + 1) - b.toNat + a.toNat = (2 ^ w - (b.setWidth w).toNat + (a.setWidth w).toNat) + 2 ^ w * 2 := by omega
    rw [heq, hmod]
  · have heq : 2 ^ (w + 1) - b.toNat + a.toNat = (2 ^ w - (b.setWidth w).toNat + (a.setWidth w).toNat) + 2 ^ w * 1 := by omega
    rw [heq, hmod]

theorem coherent_add {f g} (hf : Coherent f) (hg : Coherent g) :
    Coherent (fun w x => f w x + g w x) := by
  intro w x
  rw [BitVec.setWidth_add _ _ (by omega), hf w x, hg w x]

theorem coherent_sub {f g} (hf : Coherent f) (hg : Coherent g) :
    Coherent (fun w x => f w x - g w x) := by
  intro w x
  rw [setWidth_sub_eq, hf w x, hg w x]

theorem coherent_mul {f g} (hf : Coherent f) (hg : Coherent g) :
    Coherent (fun w x => f w x * g w x) := by
  intro w x
  rw [BitVec.setWidth_mul _ _ (by omega), hf w x, hg w x]

theorem coherent_comp {f g} (hf : Coherent f) (hg : Coherent g) :
    Coherent (fun w x => f w (g w x)) := by
  intro w x
  rw [hf w, hg w]

private theorem mod_of_range {x m : Nat} (h : x < 2 * m) :
    x % m = if m ≤ x then x - m else x := by
  by_cases hc : m ≤ x
  · simp only [hc, ↓reduceIte]
    rw [Nat.mod_eq_sub_mod hc, Nat.mod_eq_of_lt (by omega)]
  · simp only [hc, ↓reduceIte]
    exact Nat.mod_eq_of_lt (by omega)

theorem msb_add_eq {i : Nat} (a b : BitVec (i + 1)) :
    (a + b).msb =
      (a.msb ^^ b.msb ^^ decide (2 ^ i ≤ (a.setWidth i).toNat + (b.setWidth i).toNat)) := by
  have ha := toNat_eq_msb_add_setWidth a
  have hb := toNat_eq_msb_add_setWidth b
  have hab := toNat_eq_msb_add_setWidth (a + b)
  have hta := (a.setWidth i).isLt
  have htb := (b.setWidth i).isLt
  have hpow : 2 ^ (i + 1) = 2 ^ i + 2 ^ i := by rw [Nat.pow_succ]; omega
  have hmod : (a + b).toNat = (a.toNat + b.toNat) % 2 ^ (i + 1) := BitVec.toNat_add a b
  have htr : ((a + b).setWidth i).toNat = ((a.setWidth i).toNat + (b.setWidth i).toNat) % 2 ^ i := by
    rw [BitVec.setWidth_add _ _ (by omega), BitVec.toNat_add]
  have hmod1 : (a.toNat + b.toNat) % 2 ^ (i + 1) =
      if 2 ^ (i + 1) ≤ a.toNat + b.toNat then a.toNat + b.toNat - 2 ^ (i + 1) else a.toNat + b.toNat :=
    mod_of_range (by have := a.isLt; have := b.isLt; omega)
  have hmod2 : ((a.setWidth i).toNat + (b.setWidth i).toNat) % 2 ^ i =
      if 2 ^ i ≤ (a.setWidth i).toNat + (b.setWidth i).toNat
      then (a.setWidth i).toNat + (b.setWidth i).toNat - 2 ^ i
      else (a.setWidth i).toNat + (b.setWidth i).toNat :=
    mod_of_range (by omega)
  rw [hmod, hmod1, htr, hmod2] at hab
  cases ham : a.msb <;> cases hbm : b.msb <;> cases habm : (a + b).msb <;>
  simp only [ham, hbm, habm, Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
             Bool.xor_false, Bool.xor_true, Bool.false_xor, Bool.true_xor] at ha hb hab ⊢
  all_goals
    by_cases hc : 2 ^ i ≤ (a.setWidth i).toNat + (b.setWidth i).toNat <;>
    simp only [hc, ↓reduceIte, decide_true, decide_false] at hab ⊢
    all_goals
      first | rfl | (split at hab <;> omega)

theorem msb_sub_eq {i : Nat} (a b : BitVec (i + 1)) :
    (a - b).msb =
      (a.msb ^^ b.msb ^^ decide ((a.setWidth i).toNat < (b.setWidth i).toNat)) := by
  have ha := toNat_eq_msb_add_setWidth a
  have hb := toNat_eq_msb_add_setWidth b
  have hab := toNat_eq_msb_add_setWidth (a - b)
  have hta := (a.setWidth i).isLt
  have htb := (b.setWidth i).isLt
  have hpow : 2 ^ (i + 1) = 2 ^ i + 2 ^ i := by rw [Nat.pow_succ]; omega
  have hmod : (a - b).toNat = (2 ^ (i + 1) - b.toNat + a.toNat) % 2 ^ (i + 1) := BitVec.toNat_sub a b
  have htr : ((a - b).setWidth i).toNat = (2 ^ i - (b.setWidth i).toNat + (a.setWidth i).toNat) % 2 ^ i := by
    rw [setWidth_sub_eq, BitVec.toNat_sub]
  have hmod1 : (2 ^ (i + 1) - b.toNat + a.toNat) % 2 ^ (i + 1) =
      if 2 ^ (i + 1) ≤ 2 ^ (i + 1) - b.toNat + a.toNat
      then 2 ^ (i + 1) - b.toNat + a.toNat - 2 ^ (i + 1)
      else 2 ^ (i + 1) - b.toNat + a.toNat :=
    mod_of_range (by have := a.isLt; have := b.isLt; omega)
  have hmod2 : (2 ^ i - (b.setWidth i).toNat + (a.setWidth i).toNat) % 2 ^ i =
      if 2 ^ i ≤ 2 ^ i - (b.setWidth i).toNat + (a.setWidth i).toNat
      then 2 ^ i - (b.setWidth i).toNat + (a.setWidth i).toNat - 2 ^ i
      else 2 ^ i - (b.setWidth i).toNat + (a.setWidth i).toNat :=
    mod_of_range (by omega)
  rw [hmod, hmod1, htr, hmod2] at hab
  cases ham : a.msb <;> cases hbm : b.msb <;> cases habm : (a - b).msb <;>
  simp only [ham, hbm, habm, Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
             Bool.xor_false, Bool.xor_true, Bool.false_xor, Bool.true_xor] at ha hb hab ⊢
  all_goals
    by_cases hc : (a.setWidth i).toNat < (b.setWidth i).toNat <;>
    simp only [hc, decide_true, decide_false]
    all_goals
      first | rfl | (split at hab <;> split at hab <;> omega)

theorem coherent_setWidth_le {f} (hf : Coherent f) {w k : Nat} (hk : k ≤ w) (x : BitVec w) :
    (f w x).setWidth k = f k (x.setWidth k) := by
  induction w with
  | zero =>
    have : k = 0 := by omega
    subst this; simp
  | succ w ih =>
    by_cases heq : k = w + 1
    · subst heq; simp
    · have hle : k ≤ w := by omega
      have h1 : (f (w + 1) x).setWidth k = ((f (w + 1) x).setWidth w).setWidth k := by
        ext j hj
        rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem]
        simp [hj, Nat.lt_of_lt_of_le hj hle]
      have h2 : x.setWidth k = (x.setWidth w).setWidth k := by
        ext j hj
        rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem]
        simp [hj, Nat.lt_of_lt_of_le hj hle]
      rw [h1, hf w x, ih hle, ← h2]

theorem coherent_getLsbD_zero {f} (hf : Coherent f) {w : Nat} (hw : 1 ≤ w) (x : BitVec w) :
    (f w x).getLsbD 0 = bit0Val f (x.getLsbD 0) := by
  have htr := coherent_setWidth_le hf hw x
  have h0 : (f w x).getLsbD 0 = ((f w x).setWidth 1).getLsbD 0 := by
    simp
  rw [h0, htr]
  unfold bit0Val
  have hx1 : x.setWidth 1 = BitVec.cons (x.getLsbD 0) (0#0) := by
    ext j hj
    have hj0 : j = 0 := by omega
    subst hj0
    rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem]
    rw [BitVec.getLsbD_cons]
    simp
  rw [hx1, BitVec.msb_eq_getLsbD_last]

/-- Exact product MSB flip rule for `i ≥ 1` (i.e. width `i + 2`). -/
theorem msb_mul_flip {i : Nat} (a0 a1 b0 b1 : BitVec (i + 2))
    (ha : a0.setWidth (i + 1) = a1.setWidth (i + 1))
    (hb : b0.setWidth (i + 1) = b1.setWidth (i + 1)) :
    ((a1 * b1).msb != (a0 * b0).msb) =
      ((a0.getLsbD 0 && (b1.msb != b0.msb)) ^^ (b0.getLsbD 0 && (a1.msb != a0.msb))) := by
  let p := 2 ^ (i + 1)
  have hp_pos : 0 < p := Nat.two_pow_pos (i + 1)
  have hp2 : 2 ^ (i + 2) = 2 * p := by show 2 ^ (i + 2) = 2 * 2 ^ (i + 1); rw [Nat.pow_succ]; omega
  have hp_even : p % 2 = 0 := by show 2 ^ (i + 1) % 2 = 0; rw [Nat.pow_succ]; omega
  have ha0 : a0.toNat = (a0.setWidth (i + 1)).toNat + (if a0.msb then p else 0) :=
    toNat_eq_msb_add_setWidth a0
  have ha1 : a1.toNat = (a0.setWidth (i + 1)).toNat + (if a1.msb then p else 0) := by
    rw [ha]; exact toNat_eq_msb_add_setWidth a1
  have hb0 : b0.toNat = (b0.setWidth (i + 1)).toNat + (if b0.msb then p else 0) :=
    toNat_eq_msb_add_setWidth b0
  have hb1 : b1.toNat = (b0.setWidth (i + 1)).toNat + (if b1.msb then p else 0) := by
    rw [hb]; exact toNat_eq_msb_add_setWidth b1
  let ta := (a0.setWidth (i + 1)).toNat
  let tb := (b0.setWidth (i + 1)).toNat
  have ha0_lsb : a0.getLsbD 0 = decide (ta % 2 = 1) := by
    have h0 : a0.getLsbD 0 = (a0.setWidth (i + 1)).getLsbD 0 := by simp
    rw [h0, BitVec.getLsbD_eq_getElem]
    change ta.testBit 0 = decide (ta % 2 = 1)
    rw [Nat.testBit_zero]; simp
  have hb0_lsb : b0.getLsbD 0 = decide (tb % 2 = 1) := by
    have h0 : b0.getLsbD 0 = (b0.setWidth (i + 1)).getLsbD 0 := by simp
    rw [h0, BitVec.getLsbD_eq_getElem]
    change tb.testBit 0 = decide (tb % 2 = 1)
    rw [Nat.testBit_zero]; simp
  have msb_eq_div : ∀ (z : BitVec (i + 2)), z.msb = decide (p ≤ z.toNat) := by
    intro z
    have hz : z.toNat = (z.setWidth (i + 1)).toNat + (if z.msb then p else 0) :=
      toNat_eq_msb_add_setWidth z
    have hzt : (z.setWidth (i + 1)).toNat < p := (z.setWidth (i + 1)).isLt
    cases hzm : z.msb
    · simp only [hzm, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hz
      have hnot : ¬ (p ≤ z.toNat) := by omega
      simp [hnot]
    · simp only [hzm, ↓reduceIte] at hz
      have hle : p ≤ z.toNat := by omega
      simp [hle]
  rw [msb_eq_div (a1 * b1), msb_eq_div (a0 * b0), ha0_lsb, hb0_lsb]
  rw [BitVec.toNat_mul, BitVec.toNat_mul, hp2]
  have hge_iff : ∀ n : Nat, decide (p ≤ n % (2 * p)) = decide ((n / p) % 2 = 1) := by
    intro n
    have hdivmod : n % (2 * p) = (n / p % 2) * p + n % p := by
      have h1 := Nat.div_add_mod n p
      have h2 := Nat.div_add_mod (n / p) 2
      have h3 : n = (2 * p) * (n / p / 2) + ((n / p % 2) * p + n % p) := by
        have hstep1 : p * (n / p) = p * (2 * (n / p / 2) + n / p % 2) :=
          congrArg (p * ·) h2.symm
        have hstep2 : p * (2 * (n / p / 2) + n / p % 2) =
            (2 * p) * (n / p / 2) + (n / p % 2) * p := by
          rw [Nat.mul_add]
          have hc1 : p * (2 * (n / p / 2)) = (2 * p) * (n / p / 2) := by
            rw [← Nat.mul_assoc, Nat.mul_comm p 2]
          have hc2 : p * (n / p % 2) = (n / p % 2) * p := Nat.mul_comm _ _
          omega
        omega
      have hlt : (n / p % 2) * p + n % p < 2 * p := by
        have hq : n / p % 2 ≤ 1 := by omega
        have hr : n % p < p := Nat.mod_lt _ hp_pos
        have hm : (n / p % 2) * p ≤ 1 * p := Nat.mul_le_mul_right p hq
        omega
      calc n % (2 * p)
          = ((2 * p) * (n / p / 2) + ((n / p % 2) * p + n % p)) % (2 * p) :=
              congrArg (· % (2 * p)) h3
        _ = ((n / p % 2) * p + n % p) % (2 * p) := Nat.mul_add_mod _ _ _
        _ = (n / p % 2) * p + n % p := Nat.mod_eq_of_lt hlt
    rw [hdivmod]
    have hlt : n % p < p := Nat.mod_lt _ hp_pos
    rcases (show n / p % 2 = 0 ∨ n / p % 2 = 1 by omega) with h | h <;> simp [h] <;> omega
  rw [hge_iff, hge_iff]
  have hdiv_add : ∀ (q r : Nat), ((q * p + r) / p) % 2 = (q + r / p) % 2 := by
    intro q r
    rw [Nat.mul_comm q p, Nat.mul_add_div hp_pos]
  have h1 : (ta + p) * tb = tb * p + ta * tb := by
    rw [Nat.add_mul, Nat.mul_comm p tb, Nat.add_comm]
  have h2 : ta * (tb + p) = ta * p + ta * tb := by
    rw [Nat.mul_add, Nat.add_comm]
  have h3 : (ta + p) * (tb + p) = (ta + tb + p) * p + ta * tb := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
    have hptb : p * tb = tb * p := Nat.mul_comm _ _
    have htap : ta * p + tb * p + p * p = (ta + tb + p) * p := by
      simp only [Nat.add_mul]
    omega
  have hparity : ∀ (q : Nat),
      (decide ((q + ta * tb / p) % 2 = 1) != decide ((ta * tb / p) % 2 = 1)) =
        decide (q % 2 = 1) := by
    intro q
    rcases (show q % 2 = 0 ∨ q % 2 = 1 by omega) with hq | hq <;>
    rcases (show (ta * tb / p) % 2 = 0 ∨ (ta * tb / p) % 2 = 1 by omega) with hr | hr
    · have : (q + ta * tb / p) % 2 = 0 := by omega
      simp [hq, hr, this]
    · have : (q + ta * tb / p) % 2 = 1 := by omega
      simp [hq, hr, this]
    · have : (q + ta * tb / p) % 2 = 1 := by omega
      simp [hq, hr, this]
    · have : (q + ta * tb / p) % 2 = 0 := by omega
      simp [hq, hr, this]
  have hparity_sym : ∀ (q : Nat),
      (decide ((ta * tb / p) % 2 = 1) != decide ((q + ta * tb / p) % 2 = 1)) =
        decide (q % 2 = 1) := by
    intro q
    have hcomm : ∀ x y : Bool, (x != y) = (y != x) := by intro x y; cases x <;> cases y <;> rfl
    rw [hcomm, hparity]
  have hxor_mod : decide ((ta + tb + p) % 2 = 1) = (decide (ta % 2 = 1) ^^ decide (tb % 2 = 1)) := by
    rcases (show ta % 2 = 0 ∨ ta % 2 = 1 by omega) with hta | hta <;>
    rcases (show tb % 2 = 0 ∨ tb % 2 = 1 by omega) with htb | htb
    · have : (ta + tb + p) % 2 = 0 := by omega
      simp [hta, htb, this]
    · have : (ta + tb + p) % 2 = 1 := by omega
      simp [hta, htb, this]
    · have : (ta + tb + p) % 2 = 1 := by omega
      simp [hta, htb, this]
    · have : (ta + tb + p) % 2 = 0 := by omega
      simp [hta, htb, this]
  have hsub_mod : ∀ (u v : Nat),
      (decide ((u + ta * tb / p) % 2 = 1) != decide ((v + ta * tb / p) % 2 = 1)) =
        (decide (u % 2 = 1) ^^ decide (v % 2 = 1)) := by
    intro u v
    rcases (show u % 2 = 0 ∨ u % 2 = 1 by omega) with hu | hu <;>
    rcases (show v % 2 = 0 ∨ v % 2 = 1 by omega) with hv | hv <;>
    rcases (show (ta * tb / p) % 2 = 0 ∨ (ta * tb / p) % 2 = 1 by omega) with hr | hr
    all_goals
      have h1' : (u + ta * tb / p) % 2 = (u % 2 + (ta * tb / p) % 2) % 2 := by omega
      have h2' : (v + ta * tb / p) % 2 = (v % 2 + (ta * tb / p) % 2) % 2 := by omega
      rw [h1', h2']
      simp [hu, hv, hr]
  cases ha0m : a0.msb <;> cases ha1m : a1.msb <;>
  cases hb0m : b0.msb <;> cases hb1m : b1.msb <;>
  simp only [ha0m, ha1m, hb0m, hb1m, Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
             Bool.bne_true, Bool.bne_false, Bool.not_false, Bool.not_true,
             Bool.and_false, Bool.and_true, Bool.false_xor] at ha0 ha1 hb0 hb1 ⊢
  all_goals
    rw [ha0, ha1, hb0, hb1]
  all_goals
    try simp only [bne_self_eq_false]
  all_goals
    try (rw [h1, hdiv_add]; exact hparity tb)
    try (rw [h1, hdiv_add]; exact hparity_sym tb)
    try (rw [h2, hdiv_add]; exact hparity ta)
    try (rw [h2, hdiv_add]; exact hparity_sym ta)
    try (rw [h3, hdiv_add]; rw [hparity, hxor_mod])
    try (rw [h3, hdiv_add]; rw [hparity_sym, hxor_mod])
    try (rw [h1, h2, hdiv_add, hdiv_add, hsub_mod]; exact Bool.xor_comm _ _)
    try (rw [h1, h2, hdiv_add, hdiv_add, hsub_mod])
    try (rw [h1, h3, hdiv_add, hdiv_add, hsub_mod]; rw [hxor_mod]; cases decide (ta % 2 = 1) <;> cases decide (tb % 2 = 1) <;> rfl)
    try (rw [h2, h3, hdiv_add, hdiv_add, hsub_mod]; rw [hxor_mod]; cases decide (ta % 2 = 1) <;> cases decide (tb % 2 = 1) <;> rfl)

-- Now state all 11 bit-slice differential calculus rules cleanly!

theorem bitDeriv_id (i : Nat) (x : BitVec i) :
    bitDeriv (fun _ y => y) i x = true := by
  simp [bitDeriv, BitVec.msb_cons]

theorem bitDeriv_const (c : Int) (i : Nat) (x : BitVec i) :
    bitDeriv (fun w _ => BitVec.ofInt w c) i x = false := by
  simp [bitDeriv]

theorem bitDeriv_not {f} (i : Nat) (x : BitVec i) :
    bitDeriv (fun w y => ~~~(f w y)) i x = bitDeriv f i x := by
  simp only [bitDeriv, BitVec.msb_not]
  cases (f (i + 1) (BitVec.cons true x)).msb <;>
  cases (f (i + 1) (BitVec.cons false x)).msb <;> rfl

theorem bitDeriv_shl {f} (hf : Coherent f) {k : Nat} (hk : 1 ≤ k) (i : Nat) (x : BitVec i) :
    bitDeriv (fun w y => (f w y) <<< k) i x = false := by
  unfold bitDeriv
  suffices h : ((f (i + 1) (BitVec.cons true x)) <<< k).msb =
               ((f (i + 1) (BitVec.cons false x)) <<< k).msb by
    rw [h]; simp
  rw [BitVec.msb_eq_getLsbD_last, BitVec.msb_eq_getLsbD_last]
  simp only [BitVec.getLsbD_shiftLeft, Nat.add_sub_cancel]
  by_cases hik : i < k
  · simp [hik]
  · have hlt : i - k < i := by omega
    have h1 : (f (i + 1) (BitVec.cons true x)).getLsbD (i - k) =
              ((f (i + 1) (BitVec.cons true x)).setWidth i).getLsbD (i - k) := by
      simp [hlt]
    have h2 : (f (i + 1) (BitVec.cons false x)).getLsbD (i - k) =
              ((f (i + 1) (BitVec.cons false x)).setWidth i).getLsbD (i - k) := by
      simp [hlt]
    rw [h1, h2, hf i, hf i, setWidth_cons_eq, setWidth_cons_eq]

theorem bitDeriv_xor {f g} (i : Nat) (x : BitVec i) :
    bitDeriv (fun w y => f w y ^^^ g w y) i x = (bitDeriv f i x ^^ bitDeriv g i x) := by
  simp only [bitDeriv, BitVec.msb_xor]
  cases (f (i + 1) (BitVec.cons true x)).msb <;>
  cases (f (i + 1) (BitVec.cons false x)).msb <;>
  cases (g (i + 1) (BitVec.cons true x)).msb <;>
  cases (g (i + 1) (BitVec.cons false x)).msb <;> rfl

theorem bitDeriv_add {f g} (hf : Coherent f) (hg : Coherent g) (i : Nat) (x : BitVec i) :
    bitDeriv (fun w y => f w y + g w y) i x = (bitDeriv f i x ^^ bitDeriv g i x) := by
  unfold bitDeriv
  rw [msb_add_eq, msb_add_eq]
  rw [hf i, hf i, hg i, hg i, setWidth_cons_eq, setWidth_cons_eq]
  cases (f (i + 1) (BitVec.cons true x)).msb <;>
  cases (f (i + 1) (BitVec.cons false x)).msb <;>
  cases (g (i + 1) (BitVec.cons true x)).msb <;>
  cases (g (i + 1) (BitVec.cons false x)).msb <;>
  cases decide (2 ^ i ≤ (f i x).toNat + (g i x).toNat) <;> rfl

theorem bitDeriv_sub {f g} (hf : Coherent f) (hg : Coherent g) (i : Nat) (x : BitVec i) :
    bitDeriv (fun w y => f w y - g w y) i x = (bitDeriv f i x ^^ bitDeriv g i x) := by
  unfold bitDeriv
  rw [msb_sub_eq, msb_sub_eq]
  rw [hf i, hf i, hg i, hg i, setWidth_cons_eq, setWidth_cons_eq]
  cases (f (i + 1) (BitVec.cons true x)).msb <;>
  cases (f (i + 1) (BitVec.cons false x)).msb <;>
  cases (g (i + 1) (BitVec.cons true x)).msb <;>
  cases (g (i + 1) (BitVec.cons false x)).msb <;>
  cases decide ((f i x).toNat < (g i x).toNat) <;> rfl

theorem bitDeriv_and {f g} (i : Nat) (x : BitVec i) :
    bitDeriv (fun w y => f w y &&& g w y) i x =
      ((val0 f i x && bitDeriv g i x) ^^
       (val0 g i x && bitDeriv f i x) ^^
       (bitDeriv f i x && bitDeriv g i x)) := by
  simp only [bitDeriv, val0, BitVec.msb_and]
  cases (f (i + 1) (BitVec.cons true x)).msb <;>
  cases (f (i + 1) (BitVec.cons false x)).msb <;>
  cases (g (i + 1) (BitVec.cons true x)).msb <;>
  cases (g (i + 1) (BitVec.cons false x)).msb <;> rfl

theorem bitDeriv_or {f g} (i : Nat) (x : BitVec i) :
    bitDeriv (fun w y => f w y ||| g w y) i x =
      ((!val0 f i x && bitDeriv g i x) ^^
       (!val0 g i x && bitDeriv f i x) ^^
       (bitDeriv f i x && bitDeriv g i x)) := by
  simp only [bitDeriv, val0, BitVec.msb_or]
  cases (f (i + 1) (BitVec.cons true x)).msb <;>
  cases (f (i + 1) (BitVec.cons false x)).msb <;>
  cases (g (i + 1) (BitVec.cons true x)).msb <;>
  cases (g (i + 1) (BitVec.cons false x)).msb <;> rfl

theorem bitDeriv_mul_succ {f g} (hf : Coherent f) (hg : Coherent g) (i : Nat) (x : BitVec (i + 1)) :
    bitDeriv (fun w y => f w y * g w y) (i + 1) x =
      ((bit0Val f (x.getLsbD 0) && bitDeriv g (i + 1) x) ^^
       (bit0Val g (x.getLsbD 0) && bitDeriv f (i + 1) x)) := by
  unfold bitDeriv
  have ha : (f (i + 2) (BitVec.cons false x)).setWidth (i + 1) =
            (f (i + 2) (BitVec.cons true x)).setWidth (i + 1) := by
    rw [hf (i + 1), hf (i + 1), setWidth_cons_eq, setWidth_cons_eq]
  have hb : (g (i + 2) (BitVec.cons false x)).setWidth (i + 1) =
            (g (i + 2) (BitVec.cons true x)).setWidth (i + 1) := by
    rw [hg (i + 1), hg (i + 1), setWidth_cons_eq, setWidth_cons_eq]
  rw [msb_mul_flip _ _ _ _ ha hb]
  have hcons0 : (BitVec.cons false x).getLsbD 0 = x.getLsbD 0 := by
    rw [BitVec.getLsbD_cons]
    simp
  have hflsb : (f (i + 2) (BitVec.cons false x)).getLsbD 0 = bit0Val f (x.getLsbD 0) := by
    rw [coherent_getLsbD_zero hf (by omega), hcons0]
  have hglsb : (g (i + 2) (BitVec.cons false x)).getLsbD 0 = bit0Val g (x.getLsbD 0) := by
    rw [coherent_getLsbD_zero hg (by omega), hcons0]
  rw [hflsb, hglsb]

theorem bitDeriv_comp {f g} (hg : Coherent g) (i : Nat) (x : BitVec i) :
    bitDeriv (fun w y => f w (g w y)) i x = (bitDeriv f i (g i x) && bitDeriv g i x) := by
  simp only [bitDeriv]
  have ht0 : (g (i + 1) (BitVec.cons false x)).setWidth i = g i x := by
    rw [hg i, setWidth_cons_eq]
  have ht1 : (g (i + 1) (BitVec.cons true x)).setWidth i = g i x := by
    rw [hg i, setWidth_cons_eq]
  have hg0 : g (i + 1) (BitVec.cons false x) =
      BitVec.cons (g (i + 1) (BitVec.cons false x)).msb (g i x) := by
    rw [← ht0, cons_msb_setWidth]
  have hg1 : g (i + 1) (BitVec.cons true x) =
      BitVec.cons (g (i + 1) (BitVec.cons true x)).msb (g i x) := by
    rw [← ht1, cons_msb_setWidth]
  rw [hg1, hg0]
  cases (g (i + 1) (BitVec.cons true x)).msb <;>
  cases (g (i + 1) (BitVec.cons false x)).msb <;>
  simp [BitVec.msb_cons]
  · cases (f (i + 1) (BitVec.cons true (g i x))).msb <;>
    cases (f (i + 1) (BitVec.cons false (g i x))).msb <;> rfl

/-- Run `SliceAuto` on `x : BitVec i` (for `i ≥ 1`) from LSB (`x_0`) to MSB (`x_{i-1}`). -/
def SliceAuto.run (A : SliceAuto) : ∀ {i : Nat}, 1 ≤ i → BitVec i → SState
  | 0, h, _ => absurd h (by omega)
  | 1, _, x => A.init1 x.msb
  | i + 2, _, x => A.step (i + 1) (A.run (by omega) (x.setWidth (i + 1))) x.msb

theorem SliceAuto.run_one (A : SliceAuto) (b : Bool) :
    A.run (i := 1) (by omega) (BitVec.cons b (0#0)) = A.init1 b := by
  simp [SliceAuto.run, BitVec.msb_cons]

theorem SliceAuto.run_succ (A : SliceAuto) {i : Nat} (hi : 1 ≤ i) (b : Bool) (x : BitVec i) :
    A.run (i := i + 1) (by omega) (BitVec.cons b x) = A.step i (A.run hi x) b := by
  cases i with
  | zero => omega
  | succ k =>
    simp only [SliceAuto.run, BitVec.msb_cons, setWidth_cons_eq]

/-- Semantic validity & finite-state cardinality witness (separate `Prop`, outside data). -/
structure SliceAutoValid (A : SliceAuto) (card : Nat) : Prop where
  hL          : 1 ≤ A.L
  step_stable : ∀ i, A.L ≤ i → ∀ q b, A.step i q b = A.step A.L q b
  out_stable  : ∀ i, A.L ≤ i → ∀ q, A.out i q = A.out A.L q
  finite_wit  : ∃ (wf : SState → Prop) (encode : SState → Nat),
    (∀ b, wf (A.init1 b)) ∧
    (∀ i q b, wf q → wf (A.step i q b)) ∧
    (∀ q, wf q → encode q < card) ∧
    (∀ q1 q2, wf q1 → wf q2 → encode q1 = encode q2 → q1 = q2)

theorem mem_addUniq {q x : SState} {l : List SState} :
    x ∈ addUniq q l ↔ x = q ∨ x ∈ l := by
  unfold addUniq
  by_cases h : q ∈ l
  · simp only [h, ↓reduceIte]
    constructor
    · intro hx; exact Or.inr hx
    · rintro (rfl | hx); exact h; exact hx
  · simp [h]

theorem mem_unionUniq {xs acc : List SState} {x : SState} :
    x ∈ unionUniq xs acc ↔ x ∈ xs ∨ x ∈ acc := by
  induction xs generalizing acc with
  | nil => simp [unionUniq]
  | cons q qs ih =>
    simp only [unionUniq, List.foldl_cons] at *
    rw [ih, mem_addUniq]
    simp only [List.mem_cons]
    constructor
    · rintro (h | rfl | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr h
    · rintro ((rfl | h) | h)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

theorem nodup_addUniq {q : SState} {l : List SState} (hl : l.Nodup) :
    (addUniq q l).Nodup := by
  unfold addUniq
  by_cases h : q ∈ l
  · simp [h, hl]
  · simp [h, List.nodup_cons, hl]

theorem nodup_unionUniq {xs acc : List SState} (hacc : acc.Nodup) :
    (unionUniq xs acc).Nodup := by
  induction xs generalizing acc with
  | nil => exact hacc
  | cons q qs ih =>
    simp only [unionUniq, List.foldl_cons]
    exact ih (nodup_addUniq hacc)

theorem length_addUniq_ge (q : SState) (l : List SState) :
    l.length ≤ (addUniq q l).length := by
  unfold addUniq
  by_cases h : q ∈ l <;> simp [h]

theorem length_unionUniq_ge (xs acc : List SState) :
    acc.length ≤ (unionUniq xs acc).length := by
  induction xs generalizing acc with
  | nil => exact Nat.le_refl _
  | cons q qs ih =>
    simp only [unionUniq, List.foldl_cons]
    exact Nat.le_trans (length_addUniq_ge q acc) (ih (addUniq q acc))

theorem length_unionUniq_gt {xs acc : List SState} {q0 : SState}
    (hq_in : q0 ∈ xs) (hq_not : q0 ∉ acc) :
    acc.length + 1 ≤ (unionUniq xs acc).length := by
  induction xs generalizing acc with
  | nil => cases hq_in
  | cons q qs ih =>
    simp only [unionUniq, List.foldl_cons]
    by_cases hmem : q ∈ acc
    · simp only [addUniq, hmem, ↓reduceIte]
      have hne : q0 ≠ q := fun heq => hq_not (heq ▸ hmem)
      rcases List.mem_cons.1 hq_in with rfl | htail
      · exact absurd rfl hne
      · exact ih htail hq_not
    · have hlen : (addUniq q acc).length = acc.length + 1 := by
        simp [addUniq, hmem]
      have hge : (addUniq q acc).length ≤ (unionUniq qs (addUniq q acc)).length :=
        length_unionUniq_ge qs (addUniq q acc)
      change acc.length + 1 ≤ (unionUniq qs (addUniq q acc)).length
      omega

-- Elementary finite pigeonhole for `List Nat` with `Nodup` and `< card`
private theorem nodup_filter {α : Type _} (p : α → Bool) :
    ∀ {l : List α}, l.Nodup → (l.filter p).Nodup
  | [], _ => List.nodup_nil
  | a :: t, hnd => by
    rw [List.nodup_cons] at hnd
    simp only [List.filter_cons]
    cases hp : p a
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact nodup_filter p hnd.2
    · simp only [↓reduceIte, List.nodup_cons]
      refine ⟨fun hmem => hnd.1 (List.mem_filter.1 hmem).1, nodup_filter p hnd.2⟩

private theorem filter_ne_length_add_one {l : List Nat} (hnd : l.Nodup) (k : Nat) :
    l.length ≤ (l.filter (fun x => decide (x ≠ k))).length + 1 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    rcases hnd with ⟨ha_not, ht_nd⟩
    by_cases hak : a = k
    · subst hak
      have hfilt : t.filter (fun x => decide (x ≠ a)) = t := by
        apply List.filter_eq_self.2
        intro x hx
        simp only [decide_eq_true_eq]
        intro hxa
        exact ha_not (hxa ▸ hx)
      have hdec : decide (a ≠ a) = false := by simp
      simp only [List.filter_cons, hdec, Bool.false_eq_true, ↓reduceIte, hfilt, List.length_cons]
      exact Nat.le_refl _
    · have hne : decide (a ≠ k) = true := by simp [hak]
      simp only [List.filter_cons, hne, ↓reduceIte, List.length_cons]
      have := ih ht_nd
      omega

private theorem nodup_nat_length_le :
    ∀ (card : Nat) (l : List Nat), l.Nodup → (∀ n ∈ l, n < card) → l.length ≤ card
  | 0, l, _, hlt => by
    cases l with
    | nil => simp
    | cons a _ =>
      have := hlt a List.mem_cons_self
      omega
  | card + 1, l, hnd, hlt => by
    have hnd' : (l.filter (fun x => decide (x ≠ card))).Nodup := nodup_filter _ hnd
    have hlt' : ∀ n ∈ l.filter (fun x => decide (x ≠ card)), n < card := by
      intro n hn
      have hmem := List.mem_filter.1 hn
      have hlt1 := hlt n hmem.1
      have hne : n ≠ card := by simpa using hmem.2
      omega
    have ih := nodup_nat_length_le card _ hnd' hlt'
    have hstep := filter_ne_length_add_one hnd card
    omega

theorem nodup_length_le_of_encode {l : List SState} {wf : SState → Prop}
    {encode : SState → Nat} {card : Nat}
    (hnd : l.Nodup) (hwf : ∀ q ∈ l, wf q)
    (hlt : ∀ q, wf q → encode q < card)
    (hinj : ∀ q1 q2, wf q1 → wf q2 → encode q1 = encode q2 → q1 = q2) :
    l.length ≤ card := by
  have hnd_map : (l.map encode).Nodup := by
    clear hlt card
    induction l with
    | nil => simp
    | cons a t ih =>
      rw [List.nodup_cons] at hnd
      simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih hnd.2 (fun q hq => hwf q (List.mem_cons_of_mem _ hq))⟩
      intro hmem
      rcases List.mem_map.1 hmem with ⟨b, hb_in, hbeq⟩
      have heq : b = a :=
        hinj b a (hwf b (List.mem_cons_of_mem _ hb_in)) (hwf a List.mem_cons_self) hbeq
      exact hnd.1 (heq ▸ hb_in)
  have hlt_map : ∀ n ∈ l.map encode, n < card := by
    intro n hn
    rcases List.mem_map.1 hn with ⟨q, hq, rfl⟩
    exact hlt q (hwf q hq)
  have hlen := nodup_nat_length_le card (l.map encode) hnd_map hlt_map
  simpa using hlen

theorem mem_stepList {stepFn : SState → Bool → SState} {l : List SState} {q' : SState} :
    q' ∈ stepList stepFn l ↔ ∃ q ∈ l, ∃ b : Bool, stepFn q b = q' := by
  unfold stepList
  rw [mem_unionUniq]
  simp only [List.not_mem_nil, or_false, List.mem_flatMap, List.mem_cons]
  constructor
  · rintro ⟨q, hq, h | h⟩
    · exact ⟨q, hq, false, h.symm⟩
    · exact ⟨q, hq, true, h.symm⟩
  · rintro ⟨q, hq, b, rfl⟩
    cases b
    · exact ⟨q, hq, Or.inl rfl⟩
    · exact ⟨q, hq, Or.inr rfl⟩

theorem nodup_stepList (stepFn : SState → Bool → SState) (l : List SState) :
    (stepList stepFn l).Nodup :=
  nodup_unionUniq List.nodup_nil

theorem nodup_layerList (A : SliceAuto) (i : Nat) : (layerList A i).Nodup := by
  cases i with
  | zero => exact List.nodup_nil
  | succ k =>
    cases k with
    | zero => exact nodup_unionUniq List.nodup_nil
    | succ m => exact nodup_stepList _ _

/-- Exact soundness & completeness of `layerList`:
    `q ∈ layerList A i` iff `q` is reached by some `x : BitVec i`. -/
theorem mem_layerList_iff (A : SliceAuto) :
    ∀ {i : Nat} (hi : 1 ≤ i) (q : SState),
      q ∈ layerList A i ↔ ∃ x : BitVec i, A.run hi x = q
  | 0, hi, _ => absurd hi (by omega)
  | 1, _, q => by
    simp only [layerList]
    rw [mem_unionUniq]
    simp only [List.not_mem_nil, or_false, List.mem_cons]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨BitVec.cons false (0#0), A.run_one false⟩
      · exact ⟨BitVec.cons true (0#0), A.run_one true⟩
    · rintro ⟨x, rfl⟩
      cases h : x.msb
      · exact Or.inl (by simp [SliceAuto.run, h])
      · exact Or.inr (by simp [SliceAuto.run, h])
  | i + 2, _, q => by
    simp only [layerList]
    rw [mem_stepList]
    constructor
    · rintro ⟨q0, hq0, b, rfl⟩
      rcases (mem_layerList_iff A (i := i + 1) (by omega) q0).1 hq0 with ⟨x0, hx0⟩
      refine ⟨BitVec.cons b x0, ?_⟩
      rw [A.run_succ (by omega) b x0, hx0]
    · rintro ⟨x, rfl⟩
      refine ⟨A.run (by omega) (x.setWidth (i + 1)), ?_, x.msb, rfl⟩
      exact (mem_layerList_iff A (i := i + 1) (by omega) _).2 ⟨x.setWidth (i + 1), rfl⟩

theorem nodup_cumList (A : SliceAuto) (d : Nat) : (cumList A d).Nodup := by
  induction d with
  | zero => exact nodup_layerList A A.L
  | succ d ih => exact nodup_unionUniq ih

theorem subset_cumList_succ (A : SliceAuto) (d : Nat) {q : SState} (hq : q ∈ cumList A d) :
    q ∈ cumList A (d + 1) := by
  simp only [cumList]
  exact mem_unionUniq.2 (Or.inr hq)

theorem subset_cumList_zero (A : SliceAuto) (d : Nat) {q : SState} (hq : q ∈ layerList A A.L) :
    q ∈ cumList A d := by
  induction d with
  | zero => exact hq
  | succ d ih => exact subset_cumList_succ A d ih

/-- Every state in `cumList A d` is genuinely reachable at some depth `i ∈ [A.L, A.L + d]`. -/
theorem mem_cumList_reached {A : SliceAuto} {card : Nat} (hv : SliceAutoValid A card) :
    ∀ (d : Nat) (q : SState), q ∈ cumList A d →
      ∃ (i : Nat) (hi : 1 ≤ i), A.L ≤ i ∧ i ≤ A.L + d ∧ ∃ x : BitVec i, A.run hi x = q
  | 0, q, hq => by
    rcases (mem_layerList_iff A hv.hL q).1 hq with ⟨x, hx⟩
    exact ⟨A.L, hv.hL, Nat.le_refl _, Nat.le_refl _, x, hx⟩
  | d + 1, q, hq => by
    simp only [cumList] at hq
    rcases mem_unionUniq.1 hq with hstep | hold
    · rcases mem_stepList.1 hstep with ⟨q0, hq0, b, rfl⟩
      rcases mem_cumList_reached hv d q0 hq0 with ⟨i, hi, hLi, hid, x0, hx0⟩
      refine ⟨i + 1, by omega, by omega, by omega, BitVec.cons b x0, ?_⟩
      rw [A.run_succ hi b x0, hx0, hv.step_stable i hLi]
    · rcases mem_cumList_reached hv d q hold with ⟨i, hi, hLi, hid, x0, hx0⟩
      exact ⟨i, hi, hLi, by omega, x0, hx0⟩

theorem isClosedAt_iff (A : SliceAuto) (d : Nat) :
    isClosedAt A d = true ↔ ∀ q ∈ stepList (A.step A.L) (cumList A d), q ∈ cumList A d := by
  unfold isClosedAt
  simp only [List.all_eq_true, decide_eq_true_eq]

/-- If `cumList A D` is closed, EVERY state reachable at ANY depth `i ≥ A.L` lies in `cumList A D`. -/
theorem run_mem_cumList_of_closed {A : SliceAuto} {card : Nat} (hv : SliceAutoValid A card)
    {D : Nat} (hclosed : isClosedAt A D = true) :
    ∀ (i : Nat) (hi : 1 ≤ i), A.L ≤ i → ∀ (x : BitVec i), A.run hi x ∈ cumList A D
  | 0, hi, _, _ => absurd hi (by omega)
  | 1, hi, hLi, x => by
    have hL1 : A.L = 1 := by have := hv.hL; omega
    have hmem : A.run hi x ∈ layerList A 1 := (mem_layerList_iff A hi _).2 ⟨x, rfl⟩
    have hmemL : A.run hi x ∈ layerList A A.L := by rw [hL1]; exact hmem
    exact subset_cumList_zero A D hmemL
  | i + 2, hi, hLi, x => by
    by_cases heq : A.L = i + 2
    · have hmem : A.run hi x ∈ layerList A A.L := by
        rw [heq]; exact (mem_layerList_iff A hi _).2 ⟨x, rfl⟩
      exact subset_cumList_zero A D hmem
    · have hLprev : A.L ≤ i + 1 := by omega
      have hprev : A.run (by omega) (x.setWidth (i + 1)) ∈ cumList A D :=
        run_mem_cumList_of_closed hv hclosed (i + 1) (by omega) hLprev (x.setWidth (i + 1))
      have hrun : A.run hi x = A.step (i + 1) (A.run (by omega) (x.setWidth (i + 1))) x.msb := rfl
      rw [hrun, hv.step_stable (i + 1) hLprev]
      have hstep : A.step A.L (A.run (by omega) (x.setWidth (i + 1))) x.msb ∈
          stepList (A.step A.L) (cumList A D) :=
        mem_stepList.2 ⟨_, hprev, x.msb, rfl⟩
      exact (isClosedAt_iff A D).1 hclosed _ hstep

private theorem wf_run {A : SliceAuto} {wf : SState → Prop}
    (hinit : ∀ b, wf (A.init1 b)) (hstep : ∀ i q b, wf q → wf (A.step i q b)) :
    ∀ {i : Nat} (hi : 1 ≤ i) (x : BitVec i), wf (A.run hi x)
  | 0, hi, _ => absurd hi (by omega)
  | 1, _, x => hinit x.msb
  | i + 2, _, x => hstep (i + 1) _ x.msb (wf_run hinit hstep (by omega) (x.setWidth (i + 1)))

private theorem cumList_length_le {A : SliceAuto} {card : Nat}
    (hv : SliceAutoValid A card) (d : Nat) : (cumList A d).length ≤ card := by
  rcases hv.finite_wit with ⟨wf, encode, hinit, hstep, hlt, hinj⟩
  have hwf : ∀ q ∈ cumList A d, wf q := by
    intro q hq
    rcases mem_cumList_reached hv d q hq with ⟨i, hi, _, _, x, rfl⟩
    exact wf_run hinit hstep hi x
  exact nodup_length_le_of_encode (nodup_cumList A d) hwf hlt hinj

private theorem exists_not_of_all_eq_false {α : Type _} {p : α → Bool} :
    ∀ {l : List α}, l.all p = false → ∃ x ∈ l, p x = false
  | [], h => by simp at h
  | a :: t, h => by
    simp only [List.all_cons, Bool.and_eq_false_iff] at h
    rcases h with ha | ht
    · exact ⟨a, List.mem_cons_self, ha⟩
    · rcases exists_not_of_all_eq_false ht with ⟨x, hx, hpx⟩
      exact ⟨x, List.mem_cons_of_mem _ hx, hpx⟩

private theorem isClosedAt_findStabDepthAux {A : SliceAuto} {card : Nat} (hv : SliceAutoValid A card) :
    ∀ (fuel d : Nat), (cumList A d).length + fuel > card →
      isClosedAt A (findStabDepthAux A d fuel) = true
  | 0, d, hgt => by
    exfalso
    have hle := cumList_length_le hv d
    omega
  | fuel + 1, d, hgt => by
    simp only [findStabDepthAux]
    cases hc : isClosedAt A d
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rcases exists_not_of_all_eq_false hc with ⟨q0, hq0_in, hq0_f⟩
      have hq0_not : q0 ∉ cumList A d := by simpa using hq0_f
      have hgrow : (cumList A d).length + 1 ≤ (cumList A (d + 1)).length :=
        length_unionUniq_gt hq0_in hq0_not
      exact isClosedAt_findStabDepthAux hv fuel (d + 1) (by omega)
    · simp [hc]

/-- Completeness Theorem: for EVERY valid finite-state `SliceAuto`, `stabDepth A card`
    is GUARANTEED to be a closed BFS stabilization horizon! -/
theorem isClosedAt_stabDepth {A : SliceAuto} {card : Nat} (hv : SliceAutoValid A card) :
    isClosedAt A (stabDepth A card) = true := by
  have hnonempty : 1 ≤ (cumList A 0).length := by
    have hmem : A.run hv.hL (0#A.L) ∈ cumList A 0 :=
      (mem_layerList_iff A hv.hL _).2 ⟨0#A.L, rfl⟩
    cases h : cumList A 0 with
    | nil => simp [h] at hmem
    | cons _ _ => simp
  exact isClosedAt_findStabDepthAux hv card 0 (by omega)

theorem checkPreLayers_iff (A : SliceAuto) (target : Bool) :
    ∀ (k : Nat), checkPreLayers A target k = true ↔
      ∀ (i : Nat), 1 ≤ i → i < k → ∀ q ∈ layerList A i, A.out i q = target
  | 0 => by
    simp only [checkPreLayers, true_iff]
    intro i hi hlt; omega
  | 1 => by
    simp only [checkPreLayers, true_iff]
    intro i hi hlt; omega
  | k + 2 => by
    simp only [checkPreLayers, Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
    rw [checkPreLayers_iff A target (k + 1)]
    constructor
    · rintro ⟨h1, h2⟩ i hi hilt q hq
      by_cases hlt : i < k + 1
      · exact h1 i hi hlt q hq
      · have heq : i = k + 1 := by omega
        subst heq; exact h2 q hq
    · intro hall
      exact ⟨fun i hi hlt q hq => hall i hi (by omega) q hq,
             fun q hq => hall (k + 1) (by omega) (by omega) q hq⟩

/-- Master Three-Way Equivalence for `SliceAuto` (Finite → ∞ Lifting Bridge):
    (1) Infinite property `∀ i ≥ 1, ∀ x : BitVec i, A.out i (A.run x) = target`
    (2) Bounded-horizon property `∀ 1 ≤ i ≤ A.L + stabDepth A card, ∀ x, A.out i (A.run x) = target`
    (3) Decidable Boolean check `checkAutoConst A card target = true`. -/
theorem checkAutoConst_iff {A : SliceAuto} {card : Nat} (hv : SliceAutoValid A card) (target : Bool) :
    (∀ (i : Nat) (hi : 1 ≤ i) (x : BitVec i), A.out i (A.run hi x) = target) ↔
      checkAutoConst A card target = true := by
  have hclosed := isClosedAt_stabDepth hv
  unfold checkAutoConst
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
  rw [checkPreLayers_iff]
  constructor
  · intro hall
    refine ⟨?_, ?_⟩
    · intro i hi _ q hq
      rcases (mem_layerList_iff A hi q).1 hq with ⟨x, rfl⟩
      exact hall i hi x
    · intro q hq
      rcases mem_cumList_reached hv (stabDepth A card) q hq with ⟨i, hi, hLi, _, x, rfl⟩
      rw [← hv.out_stable i hLi]
      exact hall i hi x
  · rintro ⟨hpre, hcum⟩ i hi x
    by_cases hlt : i < A.L
    · exact hpre i hi hlt (A.run hi x) ((mem_layerList_iff A hi _).2 ⟨x, rfl⟩)
    · have hge : A.L ≤ i := by omega
      have hmem : A.run hi x ∈ cumList A (stabDepth A card) :=
        run_mem_cumList_of_closed hv hclosed i hi hge x
      rw [hv.out_stable i hge]
      exact hcum _ hmem

theorem sliceAuto_all_iff_bounded {A : SliceAuto} {card : Nat} (hv : SliceAutoValid A card) (target : Bool) :
    (∀ (i : Nat) (hi : 1 ≤ i) (x : BitVec i), A.out i (A.run hi x) = target) ↔
      (∀ (i : Nat) (hi : 1 ≤ i), i ≤ A.L + stabDepth A card →
        ∀ x : BitVec i, A.out i (A.run hi x) = target) := by
  constructor
  · intro hall i hi _ x; exact hall i hi x
  · intro hbdd
    apply (checkAutoConst_iff hv target).2
    unfold checkAutoConst
    simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
    rw [checkPreLayers_iff]
    refine ⟨?_, ?_⟩
    · intro i hi hilt q hq
      rcases (mem_layerList_iff A hi q).1 hq with ⟨x, rfl⟩
      exact hbdd i hi (by omega) x
    · intro q hq
      rcases mem_cumList_reached hv (stabDepth A card) q hq with ⟨i, hi, hLi, hid, x, rfl⟩
      rw [← hv.out_stable i hLi]
      exact hbdd i hi hid x

theorem MixedExpr.coherent (e : MixedExpr) : Coherent (fun w => e.eval w) := by
  induction e with
  | var => exact coherent_id
  | const c => exact coherent_const c
  | not _ ih => exact coherent_not ih
  | shl k _ ih => exact coherent_shl k ih
  | add _ _ iha ihb => exact coherent_add iha ihb
  | sub _ _ iha ihb => exact coherent_sub iha ihb
  | xor _ _ iha ihb => exact coherent_xor iha ihb
  | and _ _ iha ihb => exact coherent_and iha ihb
  | or _ _ iha ihb => exact coherent_or iha ihb
  | mul _ _ iha ihb => exact coherent_mul iha ihb

-- Encoding helpers for `SState` cardinality witnesses
private def encodeBools : List Bool → Nat
  | []     => 0
  | b :: t => (if b then 1 else 0) + 2 * encodeBools t

private theorem encodeBools_lt : ∀ (bs : List Bool), encodeBools bs < 2 ^ bs.length
  | [] => by simp [encodeBools]
  | b :: t => by
    have ih := encodeBools_lt t
    simp only [encodeBools, List.length_cons, Nat.pow_succ]
    cases b <;> simp <;> omega

private theorem encodeBools_inj :
    ∀ {bs1 bs2 : List Bool}, bs1.length = bs2.length → encodeBools bs1 = encodeBools bs2 → bs1 = bs2
  | [], [], _, _ => rfl
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen
  | b1 :: t1, b2 :: t2, hlen, heq => by
    simp only [encodeBools] at heq
    have hb : b1 = b2 := by cases b1 <;> cases b2 <;> simp at heq ⊢ <;> omega
    subst hb
    have ht : encodeBools t1 = encodeBools t2 := by cases b1 <;> simp at heq <;> omega
    have hlt : t1.length = t2.length := by simpa using hlen
    rw [encodeBools_inj hlt ht]

private theorem pair_encode_lt {a b ca cb : Nat} (ha : a < ca) (hb : b < cb) :
    a * cb + b < ca * cb := by
  have h1 : (a + 1) * cb ≤ ca * cb := Nat.mul_le_mul_right cb ha
  rw [Nat.add_mul, Nat.one_mul] at h1
  omega

private theorem pair_encode_inj {a1 b1 a2 b2 cb : Nat}
    (hb1 : b1 < cb) (hb2 : b2 < cb) (heq : a1 * cb + b1 = a2 * cb + b2) :
    a1 = a2 ∧ b1 = b2 := by
  have hcb : 0 < cb := by omega
  have hdiv1 : (a1 * cb + b1) / cb = a1 := by
    rw [Nat.mul_comm, Nat.mul_add_div hcb, Nat.div_eq_of_lt hb1, Nat.add_zero]
  have hdiv2 : (a2 * cb + b2) / cb = a2 := by
    rw [Nat.mul_comm, Nat.mul_add_div hcb, Nat.div_eq_of_lt hb2, Nat.add_zero]
  have ha : a1 = a2 := by rw [← hdiv1, heq, hdiv2]
  subst ha
  exact ⟨rfl, by omega⟩

def FullAuto.run (M : FullAuto) : ∀ (i : Nat), BitVec i → SState
  | 0, _     => M.init
  | i + 1, x => M.step i (M.run i (x.setWidth i)) x.msb

theorem FullAuto.run_cons (M : FullAuto) {i : Nat} (b : Bool) (x : BitVec i) :
    M.run (i + 1) (BitVec.cons b x) = M.step i (M.run i x) b := by
  simp [FullAuto.run, BitVec.msb_cons]

/-- Semantic soundness predicate for `FullAuto` (outside data). -/
structure FullAutoSound (e : MixedExpr) (M : FullAuto) : Prop where
  out_eq      : ∀ (i : Nat) (x : BitVec i) (b : Bool),
                  M.out i (M.run i x) b = (e.eval (i + 1) (BitVec.cons b x)).msb
  step_stable : ∀ i, M.sigBits ≤ i → ∀ q b, M.step i q b = M.step M.sigBits q b
  out_stable  : ∀ i, M.sigBits ≤ i → ∀ q b, M.out i q b = M.out M.sigBits q b
  finite_wit  : ∃ (wf : SState → Prop) (encode : SState → Nat),
    wf M.init ∧
    (∀ i q b, wf q → wf (M.step i q b)) ∧
    (∀ q, wf q → encode q < M.card) ∧
    (∀ q1 q2, wf q1 → wf q2 → encode q1 = encode q2 → q1 = q2)

-- Soundness proofs for every `FullAuto` combinator
private theorem fullVar_sound : FullAutoSound .var fullVar where
  out_eq _ _ _ := by simp [fullVar, MixedExpr.eval, BitVec.msb_cons]
  step_stable _ _ _ _ := rfl
  out_stable _ _ _ _ := rfl
  finite_wit := ⟨fun q => q = .unit, fun _ => 0, rfl, fun _ _ _ _ => rfl,
    fun _ _ => Nat.zero_lt_one, fun _ _ h1 h2 _ => h1.trans h2.symm⟩

private theorem fullConst_sound (c : Int) : FullAutoSound (.const c) (fullConst c) where
  out_eq i _ _ := by simp [fullConst, MixedExpr.eval, msb_ofInt_eq_intBit]
  step_stable _ _ _ _ := rfl
  out_stable i hi _ _ := by
    simp only [fullConst]
    rw [intBit_stable c i hi, intBit_stable c (intSigBits c) (Nat.le_refl _)]
  finite_wit := ⟨fun q => q = .unit, fun _ => 0, rfl, fun _ _ _ _ => rfl,
    fun _ _ => Nat.zero_lt_one, fun _ _ h1 h2 _ => h1.trans h2.symm⟩

private theorem fullNot_sound {e M} (h : FullAutoSound e M) : FullAutoSound (.not e) (fullNot M) where
  out_eq i x b := by
    have hrun : ∀ (n : Nat) (y : BitVec n), (fullNot M).run n y = M.run n y := by
      intro n
      induction n with
      | zero => intro _; rfl
      | succ k ih =>
        intro y
        have hstep : (fullNot M).run (k + 1) y = M.step k ((fullNot M).run k (y.setWidth k)) y.msb := rfl
        rw [hstep, ih (y.setWidth k)]
        rfl
    have h1 : (fullNot M).out i ((fullNot M).run i x) b = !(M.out i (M.run i x) b) := by
      rw [hrun i x]; rfl
    rw [h1, h.out_eq i x b]
    simp [MixedExpr.eval, BitVec.msb_not]
  step_stable := h.step_stable
  out_stable i hi q b := by simp only [fullNot, h.out_stable i hi q b]
  finite_wit := h.finite_wit

-- Shift-register buffer invariant helper
private def shlBuf (e : MixedExpr) (k i : Nat) (x : BitVec i) : List Bool :=
  (List.range k).map (fun j => if i + j < k then false else (e.eval i x).getLsbD (i + j - k))

private theorem shlBuf_zero (e : MixedExpr) (k : Nat) (x : BitVec 0) :
    shlBuf e k 0 x = List.replicate k false := by
  apply List.ext_getElem
  · simp [shlBuf]
  · intro j hj1 _
    have hjk : j < k := by simpa [shlBuf] using hj1
    simp [shlBuf]

private theorem shlBuf_step (e : MixedExpr) {k : Nat} (hk : 1 ≤ k) (i : Nat) (x : BitVec i) (b : Bool) :
    (shlBuf e k i x).tail ++ [(e.eval (i + 1) (BitVec.cons b x)).msb] =
      shlBuf e k (i + 1) (BitVec.cons b x) := by
  apply List.ext_getElem
  · simp only [shlBuf, List.length_append, List.length_tail, List.length_map,
               List.length_range, List.length_singleton]
    omega
  · intro j hj1 hj2
    have hjk : j < k := by simpa [shlBuf] using hj2
    have htail_len : (shlBuf e k i x).tail.length = k - 1 := by
      simp [shlBuf]
    by_cases hlast : j < k - 1
    · rw [List.getElem_append_left (by omega)]
      rw [List.getElem_tail]
      simp only [shlBuf, List.getElem_map, List.getElem_range]
      have hidx : i + (j + 1) = (i + 1) + j := by omega
      rw [hidx]
      by_cases hlt : i + 1 + j < k
      · simp [hlt]
      · simp only [hlt, ↓reduceIte]
        have hlti : i + 1 + j - k < i := by omega
        have hcoh := e.coherent i (BitVec.cons b x)
        rw [setWidth_cons_eq] at hcoh
        have hlsb : (e.eval (i + 1) (BitVec.cons b x)).getLsbD (i + 1 + j - k) =
            ((e.eval (i + 1) (BitVec.cons b x)).setWidth i).getLsbD (i + 1 + j - k) := by
          simp [hlti]
        rw [hlsb, hcoh]
    · have hjeq : j = k - 1 := by omega
      subst hjeq
      rw [List.getElem_append_right (by omega)]
      simp only [htail_len, Nat.sub_self, List.getElem_singleton]
      simp only [shlBuf, List.getElem_map, List.getElem_range]
      have hnotlt : ¬ (i + 1 + (k - 1) < k) := by omega
      have hsub : i + 1 + (k - 1) - k = i := by omega
      simp only [hnotlt, ↓reduceIte, hsub, BitVec.msb_eq_getLsbD_last, Nat.add_sub_cancel]

private theorem fullShl_sound (k : Nat) {e M} (h : FullAutoSound e M) :
    FullAutoSound (.shl k e) (fullShl k M) := by
  unfold fullShl
  by_cases hk0 : k = 0
  · subst hk0
    simp only [↓reduceIte]
    refine ⟨?_, h.step_stable, h.out_stable, h.finite_wit⟩
    intro i x b
    simpa [MixedExpr.eval] using h.out_eq i x b
  · simp only [hk0, ↓reduceIte]
    have hk : 1 ≤ k := by omega
    have hrun : ∀ (i : Nat) (x : BitVec i),
        (fullShl k M).run i x = .pair (M.run i x) (.buf (shlBuf e k i x)) := by
      intro i
      induction i with
      | zero =>
        intro x
        simp only [FullAuto.run, fullShl, hk0, ↓reduceIte]
        rw [shlBuf_zero]
      | succ i ih =>
        intro x
        have hcons := cons_msb_setWidth x
        have hstep : (fullShl k M).run (i + 1) x =
            (fullShl k M).step i ((fullShl k M).run i (x.setWidth i)) x.msb := rfl
        rw [hstep, ih (x.setWidth i)]
        simp only [fullShl, hk0, ↓reduceIte]
        rw [h.out_eq i (x.setWidth i) x.msb, shlBuf_step e hk i (x.setWidth i) x.msb, hcons]
        rfl
    constructor
    · intro i x b
      have hr := hrun i x
      simp only [fullShl, hk0, ↓reduceIte] at hr
      rw [hr]
      dsimp only
      have hhead : (shlBuf e k i x).headD false =
          if i < k then false else (e.eval i x).getLsbD (i - k) := by
        have hne : (shlBuf e k i x).length = k := by simp [shlBuf]
        cases hlist : shlBuf e k i x with
        | nil => rw [hlist] at hne; simp at hne; omega
        | cons hd tl =>
          have h0 : hd = (shlBuf e k i x)[0]'(by omega) := by simp [hlist]
          simp only [List.headD_cons, h0, shlBuf, List.getElem_map, List.getElem_range, Nat.add_zero]
      rw [hhead]
      simp only [MixedExpr.eval, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft,
                 Nat.add_sub_cancel, Nat.lt_succ_self, decide_true, Bool.true_and]
      by_cases hik : i < k
      · simp [hik]
      · simp only [hik, ↓reduceIte, decide_false, Bool.not_false, Bool.true_and]
        have hlt : i - k < i := by omega
        have hcoh := e.coherent i (BitVec.cons b x)
        rw [setWidth_cons_eq] at hcoh
        have hlsb : (e.eval (i + 1) (BitVec.cons b x)).getLsbD (i - k) =
            ((e.eval (i + 1) (BitVec.cons b x)).setWidth i).getLsbD (i - k) := by
          simp [hlt]
        rw [hlsb, hcoh]
    · intro i hi q b
      cases q with
      | pair qm qbuf =>
        cases qbuf with
        | buf bs => simp [h.step_stable i hi, h.out_stable i hi]
        | _ => rfl
      | _ => rfl
    · intro _ _ _ _; rfl
    · rcases h.finite_wit with ⟨wfM, encM, hinitM, hstepM, hltM, hinjM⟩
      refine ⟨fun q => ∃ qm bs, q = .pair qm (.buf bs) ∧ wfM qm ∧ bs.length = k,
              fun q => match q with | .pair qm (.buf bs) => encM qm * 2 ^ k + encodeBools bs | _ => 0,
              ?_, ?_, ?_, ?_⟩
      · exact ⟨M.init, List.replicate k false, rfl, hinitM, by simp⟩
      · rintro i _ b ⟨qm, bs, rfl, hwf, hlen⟩
        refine ⟨M.step i qm b, bs.tail ++ [M.out i qm b], rfl, hstepM i qm b hwf, ?_⟩
        simp only [List.length_append, List.length_tail, List.length_singleton, hlen]
        omega
      · rintro _ ⟨qm, bs, rfl, hwf, hlen⟩
        have hb := encodeBools_lt bs
        rw [hlen] at hb
        exact pair_encode_lt (hltM qm hwf) hb
      · rintro _ _ ⟨qm1, bs1, rfl, hwf1, hlen1⟩ ⟨qm2, bs2, rfl, hwf2, hlen2⟩ heq
        have hb1 := encodeBools_lt bs1; rw [hlen1] at hb1
        have hb2 := encodeBools_lt bs2; rw [hlen2] at hb2
        rcases pair_encode_inj hb1 hb2 heq with ⟨he1, he2⟩
        rw [hinjM qm1 qm2 hwf1 hwf2 he1, encodeBools_inj (hlen1.trans hlen2.symm) he2]

private theorem fullBitwise_run (op : Bool → Bool → Bool) (Ma Mb : FullAuto) :
    ∀ (i : Nat) (x : BitVec i), (fullBitwise op Ma Mb).run i x = .pair (Ma.run i x) (Mb.run i x)
  | 0, _ => rfl
  | i + 1, x => by
    have hstep : (fullBitwise op Ma Mb).run (i + 1) x =
        (fullBitwise op Ma Mb).step i ((fullBitwise op Ma Mb).run i (x.setWidth i)) x.msb := rfl
    rw [hstep, fullBitwise_run op Ma Mb i (x.setWidth i)]
    rfl

private theorem fullBitwise_valid (op : Bool → Bool → Bool) {ea eb Ma Mb}
    (ha : FullAutoSound ea Ma) (hb : FullAutoSound eb Mb) :
    (∀ i, max Ma.sigBits Mb.sigBits ≤ i → ∀ q b,
      (fullBitwise op Ma Mb).step i q b = (fullBitwise op Ma Mb).step (max Ma.sigBits Mb.sigBits) q b) ∧
    (∀ i, max Ma.sigBits Mb.sigBits ≤ i → ∀ q b,
      (fullBitwise op Ma Mb).out i q b = (fullBitwise op Ma Mb).out (max Ma.sigBits Mb.sigBits) q b) ∧
    (∃ (wf : SState → Prop) (encode : SState → Nat),
      wf (fullBitwise op Ma Mb).init ∧
      (∀ i q b, wf q → wf ((fullBitwise op Ma Mb).step i q b)) ∧
      (∀ q, wf q → encode q < (fullBitwise op Ma Mb).card) ∧
      (∀ q1 q2, wf q1 → wf q2 → encode q1 = encode q2 → q1 = q2)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi q b
    have hia : Ma.sigBits ≤ i := Nat.le_trans (Nat.le_max_left _ _) hi
    have hib : Mb.sigBits ≤ i := Nat.le_trans (Nat.le_max_right _ _) hi
    cases q with
    | pair qa qb =>
      simp only [fullBitwise]
      rw [ha.step_stable i hia, ha.step_stable (max Ma.sigBits Mb.sigBits) (Nat.le_max_left _ _),
          hb.step_stable i hib, hb.step_stable (max Ma.sigBits Mb.sigBits) (Nat.le_max_right _ _)]
    | _ => rfl
  · intro i hi q b
    have hia : Ma.sigBits ≤ i := Nat.le_trans (Nat.le_max_left _ _) hi
    have hib : Mb.sigBits ≤ i := Nat.le_trans (Nat.le_max_right _ _) hi
    cases q with
    | pair qa qb =>
      simp only [fullBitwise]
      rw [ha.out_stable i hia, ha.out_stable (max Ma.sigBits Mb.sigBits) (Nat.le_max_left _ _),
          hb.out_stable i hib, hb.out_stable (max Ma.sigBits Mb.sigBits) (Nat.le_max_right _ _)]
    | _ => rfl
  · rcases ha.finite_wit with ⟨wfa, enca, hia, hsa, hlta, hinja⟩
    rcases hb.finite_wit with ⟨wfb, encb, hib, hsb, hltb, hinjb⟩
    refine ⟨fun q => ∃ qa qb, q = .pair qa qb ∧ wfa qa ∧ wfb qb,
            fun q => match q with | .pair qa qb => enca qa * Mb.card + encb qb | _ => 0,
            ⟨Ma.init, Mb.init, rfl, hia, hib⟩, ?_, ?_, ?_⟩
    · rintro i _ b ⟨qa, qb, rfl, hqa, hqb⟩
      exact ⟨Ma.step i qa b, Mb.step i qb b, rfl, hsa i qa b hqa, hsb i qb b hqb⟩
    · rintro _ ⟨qa, qb, rfl, hqa, hqb⟩
      exact pair_encode_lt (hlta qa hqa) (hltb qb hqb)
    · rintro _ _ ⟨qa1, qb1, rfl, hqa1, hqb1⟩ ⟨qa2, qb2, rfl, hqa2, hqb2⟩ heq
      rcases pair_encode_inj (hltb qb1 hqb1) (hltb qb2 hqb2) heq with ⟨he1, he2⟩
      rw [hinja qa1 qa2 hqa1 hqa2 he1, hinjb qb1 qb2 hqb1 hqb2 he2]

private theorem fullAdd_sound {ea eb Ma Mb}
    (ha : FullAutoSound ea Ma) (hb : FullAutoSound eb Mb) :
    FullAutoSound (.add ea eb) (fullAdd Ma Mb) := by
  have hrun : ∀ (i : Nat) (x : BitVec i),
      (fullAdd Ma Mb).run i x =
        .carry (Ma.run i x) (Mb.run i x) (decide (2 ^ i ≤ (ea.eval i x).toNat + (eb.eval i x).toNat)) := by
    intro i
    induction i with
    | zero =>
      intro x
      have ha0 : (ea.eval 0 x).toNat = 0 := by have := (ea.eval 0 x).isLt; omega
      have hb0 : (eb.eval 0 x).toNat = 0 := by have := (eb.eval 0 x).isLt; omega
      simp [FullAuto.run, fullAdd, ha0, hb0]
    | succ i ih =>
      intro x
      have hstep : (fullAdd Ma Mb).run (i + 1) x =
          (fullAdd Ma Mb).step i ((fullAdd Ma Mb).run i (x.setWidth i)) x.msb := rfl
      rw [hstep, ih (x.setWidth i)]
      simp only [fullAdd]
      have hcons := cons_msb_setWidth x
      have hva : Ma.out i (Ma.run i (x.setWidth i)) x.msb = (ea.eval (i + 1) x).msb := by
        rw [ha.out_eq, hcons]
      have hvb : Mb.out i (Mb.run i (x.setWidth i)) x.msb = (eb.eval (i + 1) x).msb := by
        rw [hb.out_eq, hcons]
      rw [hva, hvb]
      have hna := toNat_eq_msb_add_setWidth (ea.eval (i + 1) x)
      have hnb := toNat_eq_msb_add_setWidth (eb.eval (i + 1) x)
      have hca : (ea.eval (i + 1) x).setWidth i = ea.eval i (x.setWidth i) := ea.coherent i x
      have hcb : (eb.eval (i + 1) x).setWidth i = eb.eval i (x.setWidth i) := eb.coherent i x
      rw [hca] at hna
      rw [hcb] at hnb
      have hta := (ea.eval i (x.setWidth i)).isLt
      have htb := (eb.eval i (x.setWidth i)).isLt
      have hpow : 2 ^ (i + 1) = 2 ^ i + 2 ^ i := by rw [Nat.pow_succ]; omega
      congr 1
      cases hma : (ea.eval (i + 1) x).msb <;> cases hmb : (eb.eval (i + 1) x).msb <;>
      simp only [hma, hmb, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hna hnb <;>
      by_cases hc : 2 ^ i ≤ (ea.eval i (x.setWidth i)).toNat + (eb.eval i (x.setWidth i)).toNat <;>
      simp only [hc, decide_true, decide_false, Bool.and_true, Bool.and_false,
                 Bool.or_true, Bool.or_false]
      all_goals
        first
        | (symm; exact decide_eq_true (by omega))
        | (symm; exact decide_eq_false (by omega))
  constructor
  · intro i x b
    rw [hrun i x]
    simp only [fullAdd, MixedExpr.eval]
    rw [ha.out_eq, hb.out_eq, msb_add_eq]
    have hca : (ea.eval (i + 1) (BitVec.cons b x)).setWidth i = ea.eval i x := by
      have := ea.coherent i (BitVec.cons b x); rwa [setWidth_cons_eq] at this
    have hcb : (eb.eval (i + 1) (BitVec.cons b x)).setWidth i = eb.eval i x := by
      have := eb.coherent i (BitVec.cons b x); rwa [setWidth_cons_eq] at this
    rw [hca, hcb]
  · intro i hi q b
    have hia : Ma.sigBits ≤ i := Nat.le_trans (Nat.le_max_left _ _) hi
    have hib : Mb.sigBits ≤ i := Nat.le_trans (Nat.le_max_right _ _) hi
    cases q with
    | carry qa qb c =>
      simp only [fullAdd]
      rw [ha.step_stable i hia, ha.step_stable (max Ma.sigBits Mb.sigBits) (Nat.le_max_left _ _),
          hb.step_stable i hib, hb.step_stable (max Ma.sigBits Mb.sigBits) (Nat.le_max_right _ _),
          ha.out_stable i hia, ha.out_stable (max Ma.sigBits Mb.sigBits) (Nat.le_max_left _ _),
          hb.out_stable i hib, hb.out_stable (max Ma.sigBits Mb.sigBits) (Nat.le_max_right _ _)]
    | _ => rfl
  · intro i hi q b
    have hia : Ma.sigBits ≤ i := Nat.le_trans (Nat.le_max_left _ _) hi
    have hib : Mb.sigBits ≤ i := Nat.le_trans (Nat.le_max_right _ _) hi
    cases q with
    | carry qa qb c =>
      simp only [fullAdd]
      rw [ha.out_stable i hia, ha.out_stable (max Ma.sigBits Mb.sigBits) (Nat.le_max_left _ _),
          hb.out_stable i hib, hb.out_stable (max Ma.sigBits Mb.sigBits) (Nat.le_max_right _ _)]
    | _ => rfl
  · rcases ha.finite_wit with ⟨wfa, enca, hia, hsa, hlta, hinja⟩
    rcases hb.finite_wit with ⟨wfb, encb, hib, hsb, hltb, hinjb⟩
    refine ⟨fun q => ∃ qa qb c, q = .carry qa qb c ∧ wfa qa ∧ wfb qb,
            fun q => match q with
              | .carry qa qb c => (if c then 1 else 0) + 2 * (enca qa * Mb.card + encb qb)
              | _ => 0,
            ⟨Ma.init, Mb.init, false, rfl, hia, hib⟩, ?_, ?_, ?_⟩
    · rintro i _ b ⟨qa, qb, c, rfl, hqa, hqb⟩
      exact ⟨Ma.step i qa b, Mb.step i qb b, _, rfl, hsa i qa b hqa, hsb i qb b hqb⟩
    · rintro _ ⟨qa, qb, c, rfl, hqa, hqb⟩
      have hp := pair_encode_lt (hlta qa hqa) (hltb qb hqb)
      simp only [fullAdd]
      cases c <;> simp <;> omega
    · rintro _ _ ⟨qa1, qb1, c1, rfl, hqa1, hqb1⟩ ⟨qa2, qb2, c2, rfl, hqa2, hqb2⟩ heq
      have hc : c1 = c2 := by cases c1 <;> cases c2 <;> simp at heq ⊢ <;> omega
      subst hc
      have hp : enca qa1 * Mb.card + encb qb1 = enca qa2 * Mb.card + encb qb2 := by
        cases c1 <;> simp at heq <;> omega
      rcases pair_encode_inj (hltb qb1 hqb1) (hltb qb2 hqb2) hp with ⟨he1, he2⟩
      rw [hinja qa1 qa2 hqa1 hqa2 he1, hinjb qb1 qb2 hqb1 hqb2 he2]

private theorem fullSub_sound {ea eb Ma Mb}
    (ha : FullAutoSound ea Ma) (hb : FullAutoSound eb Mb) :
    FullAutoSound (.sub ea eb) (fullSub Ma Mb) := by
  have hrun : ∀ (i : Nat) (x : BitVec i),
      (fullSub Ma Mb).run i x =
        .carry (Ma.run i x) (Mb.run i x) (decide ((ea.eval i x).toNat < (eb.eval i x).toNat)) := by
    intro i
    induction i with
    | zero =>
      intro x
      have ha0 : (ea.eval 0 x).toNat = 0 := by have := (ea.eval 0 x).isLt; omega
      have hb0 : (eb.eval 0 x).toNat = 0 := by have := (eb.eval 0 x).isLt; omega
      simp [FullAuto.run, fullSub, ha0, hb0]
    | succ i ih =>
      intro x
      have hstep : (fullSub Ma Mb).run (i + 1) x =
          (fullSub Ma Mb).step i ((fullSub Ma Mb).run i (x.setWidth i)) x.msb := rfl
      rw [hstep, ih (x.setWidth i)]
      simp only [fullSub]
      have hcons := cons_msb_setWidth x
      have hva : Ma.out i (Ma.run i (x.setWidth i)) x.msb = (ea.eval (i + 1) x).msb := by
        rw [ha.out_eq, hcons]
      have hvb : Mb.out i (Mb.run i (x.setWidth i)) x.msb = (eb.eval (i + 1) x).msb := by
        rw [hb.out_eq, hcons]
      rw [hva, hvb]
      have hna := toNat_eq_msb_add_setWidth (ea.eval (i + 1) x)
      have hnb := toNat_eq_msb_add_setWidth (eb.eval (i + 1) x)
      have hca : (ea.eval (i + 1) x).setWidth i = ea.eval i (x.setWidth i) := ea.coherent i x
      have hcb : (eb.eval (i + 1) x).setWidth i = eb.eval i (x.setWidth i) := eb.coherent i x
      rw [hca] at hna
      rw [hcb] at hnb
      have hta := (ea.eval i (x.setWidth i)).isLt
      have htb := (eb.eval i (x.setWidth i)).isLt
      congr 1
      cases hma : (ea.eval (i + 1) x).msb <;> cases hmb : (eb.eval (i + 1) x).msb <;>
      simp only [hma, hmb, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hna hnb <;>
      by_cases hc : (ea.eval i (x.setWidth i)).toNat < (eb.eval i (x.setWidth i)).toNat <;>
      simp only [hc, decide_true, decide_false, Bool.not_true, Bool.not_false,
                 Bool.and_true, Bool.and_false, Bool.or_true, Bool.or_false]
      all_goals
        first
        | (symm; exact decide_eq_true (by omega))
        | (symm; exact decide_eq_false (by omega))
  constructor
  · intro i x b
    rw [hrun i x]
    simp only [fullSub, MixedExpr.eval]
    rw [ha.out_eq, hb.out_eq, msb_sub_eq]
    have hca : (ea.eval (i + 1) (BitVec.cons b x)).setWidth i = ea.eval i x := by
      have := ea.coherent i (BitVec.cons b x); rwa [setWidth_cons_eq] at this
    have hcb : (eb.eval (i + 1) (BitVec.cons b x)).setWidth i = eb.eval i x := by
      have := eb.coherent i (BitVec.cons b x); rwa [setWidth_cons_eq] at this
    rw [hca, hcb]
  · intro i hi q b
    have hia : Ma.sigBits ≤ i := Nat.le_trans (Nat.le_max_left _ _) hi
    have hib : Mb.sigBits ≤ i := Nat.le_trans (Nat.le_max_right _ _) hi
    cases q with
    | carry qa qb c =>
      simp only [fullSub]
      rw [ha.step_stable i hia, ha.step_stable (max Ma.sigBits Mb.sigBits) (Nat.le_max_left _ _),
          hb.step_stable i hib, hb.step_stable (max Ma.sigBits Mb.sigBits) (Nat.le_max_right _ _),
          ha.out_stable i hia, ha.out_stable (max Ma.sigBits Mb.sigBits) (Nat.le_max_left _ _),
          hb.out_stable i hib, hb.out_stable (max Ma.sigBits Mb.sigBits) (Nat.le_max_right _ _)]
    | _ => rfl
  · intro i hi q b
    have hia : Ma.sigBits ≤ i := Nat.le_trans (Nat.le_max_left _ _) hi
    have hib : Mb.sigBits ≤ i := Nat.le_trans (Nat.le_max_right _ _) hi
    cases q with
    | carry qa qb c =>
      simp only [fullSub]
      rw [ha.out_stable i hia, ha.out_stable (max Ma.sigBits Mb.sigBits) (Nat.le_max_left _ _),
          hb.out_stable i hib, hb.out_stable (max Ma.sigBits Mb.sigBits) (Nat.le_max_right _ _)]
    | _ => rfl
  · rcases ha.finite_wit with ⟨wfa, enca, hia, hsa, hlta, hinja⟩
    rcases hb.finite_wit with ⟨wfb, encb, hib, hsb, hltb, hinjb⟩
    refine ⟨fun q => ∃ qa qb c, q = .carry qa qb c ∧ wfa qa ∧ wfb qb,
            fun q => match q with
              | .carry qa qb c => (if c then 1 else 0) + 2 * (enca qa * Mb.card + encb qb)
              | _ => 0,
            ⟨Ma.init, Mb.init, false, rfl, hia, hib⟩, ?_, ?_, ?_⟩
    · rintro i _ b ⟨qa, qb, c, rfl, hqa, hqb⟩
      exact ⟨Ma.step i qa b, Mb.step i qb b, _, rfl, hsa i qa b hqa, hsb i qb b hqb⟩
    · rintro _ ⟨qa, qb, c, rfl, hqa, hqb⟩
      have hp := pair_encode_lt (hlta qa hqa) (hltb qb hqb)
      simp only [fullSub]
      cases c <;> simp <;> omega
    · rintro _ _ ⟨qa1, qb1, c1, rfl, hqa1, hqb1⟩ ⟨qa2, qb2, c2, rfl, hqa2, hqb2⟩ heq
      have hc : c1 = c2 := by cases c1 <;> cases c2 <;> simp at heq ⊢ <;> omega
      subst hc
      have hp : enca qa1 * Mb.card + encb qb1 = enca qa2 * Mb.card + encb qb2 := by
        cases c1 <;> simp at heq <;> omega
      rcases pair_encode_inj (hltb qb1 hqb1) (hltb qb2 hqb2) hp with ⟨he1, he2⟩
      rw [hinja qa1 qa2 hqa1 hqa2 he1, hinjb qb1 qb2 hqb1 hqb2 he2]

theorem compileFull_sound : ∀ (e : MixedExpr) (M : FullAuto), compileFull e = some M → FullAutoSound e M
  | .var, M, h => by
    simp only [compileFull, Option.some.injEq] at h; subst h; exact fullVar_sound
  | .const c, M, h => by
    simp only [compileFull, Option.some.injEq] at h; subst h; exact fullConst_sound c
  | .not e, M, h => by
    simp only [compileFull] at h
    cases he : compileFull e with
    | none => simp [he] at h
    | some Me =>
      simp only [he, Option.map_some, Option.some.injEq] at h; subst h
      exact fullNot_sound (compileFull_sound e Me he)
  | .shl k e, M, h => by
    simp only [compileFull] at h
    cases he : compileFull e with
    | none => simp [he] at h
    | some Me =>
      simp only [he, Option.map_some, Option.some.injEq] at h; subst h
      exact fullShl_sound k (compileFull_sound e Me he)
  | .xor a b, M, h => by
    simp only [compileFull, bind, Option.bind] at h
    cases ha : compileFull a <;> cases hb : compileFull b <;> simp [ha, hb] at h
    subst h
    have hsa := compileFull_sound a _ ha; have hsb := compileFull_sound b _ hb
    rcases fullBitwise_valid xor hsa hsb with ⟨hst, ho, hfin⟩
    exact ⟨fun i x v => by rw [fullBitwise_run]; simp [fullBitwise, hsa.out_eq, hsb.out_eq, MixedExpr.eval, BitVec.msb_xor],
           hst, ho, hfin⟩
  | .and a b, M, h => by
    simp only [compileFull, bind, Option.bind] at h
    cases ha : compileFull a <;> cases hb : compileFull b <;> simp [ha, hb] at h
    subst h
    have hsa := compileFull_sound a _ ha; have hsb := compileFull_sound b _ hb
    rcases fullBitwise_valid and hsa hsb with ⟨hst, ho, hfin⟩
    exact ⟨fun i x v => by rw [fullBitwise_run]; simp [fullBitwise, hsa.out_eq, hsb.out_eq, MixedExpr.eval, BitVec.msb_and],
           hst, ho, hfin⟩
  | .or a b, M, h => by
    simp only [compileFull, bind, Option.bind] at h
    cases ha : compileFull a <;> cases hb : compileFull b <;> simp [ha, hb] at h
    subst h
    have hsa := compileFull_sound a _ ha; have hsb := compileFull_sound b _ hb
    rcases fullBitwise_valid or hsa hsb with ⟨hst, ho, hfin⟩
    exact ⟨fun i x v => by rw [fullBitwise_run]; simp [fullBitwise, hsa.out_eq, hsb.out_eq, MixedExpr.eval, BitVec.msb_or],
           hst, ho, hfin⟩
  | .add a b, M, h => by
    simp only [compileFull, bind, Option.bind] at h
    cases ha : compileFull a <;> cases hb : compileFull b <;> simp [ha, hb] at h
    subst h
    exact fullAdd_sound (compileFull_sound a _ ha) (compileFull_sound b _ hb)
  | .sub a b, M, h => by
    simp only [compileFull, bind, Option.bind] at h
    cases ha : compileFull a <;> cases hb : compileFull b <;> simp [ha, hb] at h
    subst h
    exact fullSub_sound (compileFull_sound a _ ha) (compileFull_sound b _ hb)
  | .mul _ _, _, h => by simp [compileFull] at h

/-- Semantic soundness predicate for `DerivAuto` (outside data). -/
structure DerivAutoSound (e : MixedExpr) (D : DerivAuto) : Prop where
  valid    : SliceAutoValid D.auto D.card
  bit0_eq  : ∀ b : Bool, D.bit0 b = bit0Val (fun w => e.eval w) b
  deriv_eq : ∀ (i : Nat) (hi : 1 ≤ i) (x : BitVec i),
               D.auto.out i (D.auto.run hi x) = bitDeriv (fun w => e.eval w) i x

-- Soundness proofs for `DerivAuto` combinators
private theorem sliceAutoValid_unit (dval : Bool) :
    SliceAutoValid { init1 := fun _ => .unit, step := fun _ _ _ => .unit, out := fun _ _ => dval, L := 1 } 1 where
  hL := Nat.le_refl 1
  step_stable _ _ _ _ := rfl
  out_stable _ _ _ := rfl
  finite_wit := ⟨fun q => q = .unit, fun _ => 0, fun _ => rfl, fun _ _ _ _ => rfl,
    fun _ _ => Nat.zero_lt_one, fun _ _ h1 h2 _ => h1.trans h2.symm⟩

private theorem fullToDeriv_run (M : FullAuto) :
    ∀ {i : Nat} (hi : 1 ≤ i) (x : BitVec i), (fullToDeriv M).auto.run hi x = M.run i x
  | 0, hi, _ => absurd hi (by omega)
  | 1, _, x => by
    simp only [SliceAuto.run, fullToDeriv, FullAuto.run]
  | i + 2, _, x => by
    have hstep : (fullToDeriv M).auto.run (i := i + 2) (by omega) x =
        M.step (i + 1) ((fullToDeriv M).auto.run (by omega) (x.setWidth (i + 1))) x.msb := rfl
    rw [hstep, fullToDeriv_run M (by omega) (x.setWidth (i + 1))]
    rfl

private theorem fullToDeriv_sound {e M} (h : FullAutoSound e M) :
    DerivAutoSound e (fullToDeriv M) := by
  constructor
  · constructor
    · exact Nat.le_max_left 1 M.sigBits
    · intro i hi q b
      have h1 : M.sigBits ≤ i := Nat.le_trans (Nat.le_max_right 1 M.sigBits) hi
      have h2 : M.sigBits ≤ max 1 M.sigBits := Nat.le_max_right 1 M.sigBits
      simp only [fullToDeriv]
      rw [h.step_stable i h1, h.step_stable (max 1 M.sigBits) h2]
    · intro i hi q
      have h1 : M.sigBits ≤ i := Nat.le_trans (Nat.le_max_right 1 M.sigBits) hi
      have h2 : M.sigBits ≤ max 1 M.sigBits := Nat.le_max_right 1 M.sigBits
      simp only [fullToDeriv]
      rw [h.out_stable i h1, h.out_stable (max 1 M.sigBits) h2,
          h.out_stable i h1, h.out_stable (max 1 M.sigBits) h2]
    · rcases h.finite_wit with ⟨wf, enc, hinit, hstep, hlt, hinj⟩
      exact ⟨wf, enc, fun b => hstep 0 M.init b hinit, hstep, hlt, hinj⟩
  · intro b
    simpa [fullToDeriv, bit0Val, FullAuto.run] using h.out_eq 0 (0#0) b
  · intro i hi x
    rw [fullToDeriv_run M hi x]
    simp only [fullToDeriv, bitDeriv]
    rw [h.out_eq i x true, h.out_eq i x false]

private theorem derivXorPair_run (Da Db : DerivAuto) :
    ∀ {i : Nat} (hi : 1 ≤ i) (x : BitVec i),
      (derivXorPair Da Db).auto.run hi x = .pair (Da.auto.run hi x) (Db.auto.run hi x)
  | 0, hi, _ => absurd hi (by omega)
  | 1, _, _ => rfl
  | i + 2, _, x => by
    have hstep : (derivXorPair Da Db).auto.run (i := i + 2) (by omega) x =
        (derivXorPair Da Db).auto.step (i + 1) ((derivXorPair Da Db).auto.run (by omega) (x.setWidth (i + 1))) x.msb := rfl
    rw [hstep, derivXorPair_run Da Db (by omega) (x.setWidth (i + 1))]
    rfl

private theorem derivXorPair_valid {Da Db}
    (hva : SliceAutoValid Da.auto Da.card) (hvb : SliceAutoValid Db.auto Db.card) :
    SliceAutoValid (derivXorPair Da Db).auto (derivXorPair Da Db).card where
  hL := Nat.le_trans hva.hL (Nat.le_max_left _ _)
  step_stable i hi q b := by
    have hia : Da.auto.L ≤ i := Nat.le_trans (Nat.le_max_left _ _) hi
    have hib : Db.auto.L ≤ i := Nat.le_trans (Nat.le_max_right _ _) hi
    cases q with
    | pair qa qb =>
      simp only [derivXorPair]
      rw [hva.step_stable i hia, hva.step_stable _ (Nat.le_max_left _ _),
          hvb.step_stable i hib, hvb.step_stable _ (Nat.le_max_right _ _)]
    | _ => rfl
  out_stable i hi q := by
    have hia : Da.auto.L ≤ i := Nat.le_trans (Nat.le_max_left _ _) hi
    have hib : Db.auto.L ≤ i := Nat.le_trans (Nat.le_max_right _ _) hi
    cases q with
    | pair qa qb =>
      simp only [derivXorPair]
      rw [hva.out_stable i hia, hva.out_stable _ (Nat.le_max_left _ _),
          hvb.out_stable i hib, hvb.out_stable _ (Nat.le_max_right _ _)]
    | _ => rfl
  finite_wit := by
    rcases hva.finite_wit with ⟨wfa, enca, hia, hsa, hlta, hinja⟩
    rcases hvb.finite_wit with ⟨wfb, encb, hib, hsb, hltb, hinjb⟩
    refine ⟨fun q => ∃ qa qb, q = .pair qa qb ∧ wfa qa ∧ wfb qb,
            fun q => match q with | .pair qa qb => enca qa * Db.card + encb qb | _ => 0,
            fun b => ⟨Da.auto.init1 b, Db.auto.init1 b, rfl, hia b, hib b⟩, ?_, ?_, ?_⟩
    · rintro i _ b ⟨qa, qb, rfl, hqa, hqb⟩
      exact ⟨Da.auto.step i qa b, Db.auto.step i qb b, rfl, hsa i qa b hqa, hsb i qb b hqb⟩
    · rintro _ ⟨qa, qb, rfl, hqa, hqb⟩
      exact pair_encode_lt (hlta qa hqa) (hltb qb hqb)
    · rintro _ _ ⟨qa1, qb1, rfl, hqa1, hqb1⟩ ⟨qa2, qb2, rfl, hqa2, hqb2⟩ heq
      rcases pair_encode_inj (hltb qb1 hqb1) (hltb qb2 hqb2) heq with ⟨he1, he2⟩
      rw [hinja qa1 qa2 hqa1 hqa2 he1, hinjb qb1 qb2 hqb1 hqb2 he2]

private theorem derivMul_run (Da Db : DerivAuto) :
    ∀ {i : Nat} (hi : 1 ≤ i) (x : BitVec i),
      (derivMul Da Db).auto.run hi x = .carry (Da.auto.run hi x) (Db.auto.run hi x) (x.getLsbD 0)
  | 0, hi, _ => absurd hi (by omega)
  | 1, _, x => by
    simp only [SliceAuto.run, derivMul, BitVec.msb_eq_getLsbD_last]
  | i + 2, _, x => by
    have hstep : (derivMul Da Db).auto.run (i := i + 2) (by omega) x =
        (derivMul Da Db).auto.step (i + 1) ((derivMul Da Db).auto.run (by omega) (x.setWidth (i + 1))) x.msb := rfl
    rw [hstep, derivMul_run Da Db (by omega) (x.setWidth (i + 1))]
    have h0 : (x.setWidth (i + 1)).getLsbD 0 = x.getLsbD 0 := by simp
    change SState.carry (Da.auto.run (by omega) x) (Db.auto.run (by omega) x) ((x.setWidth (i + 1)).getLsbD 0) =
           SState.carry (Da.auto.run (by omega) x) (Db.auto.run (by omega) x) (x.getLsbD 0)
    rw [h0]

private theorem derivMul_sound {ea eb Da Db}
    (ha : DerivAutoSound ea Da) (hb : DerivAutoSound eb Db) :
    DerivAutoSound (.mul ea eb) (derivMul Da Db) := by
  constructor
  · constructor
    · exact Nat.le_trans ha.valid.hL (Nat.le_max_left _ _)
    · intro i hi q b
      have hia : Da.auto.L ≤ i := Nat.le_trans (Nat.le_max_left _ _) hi
      have hib : Db.auto.L ≤ i := Nat.le_trans (Nat.le_max_right _ _) hi
      cases q with
      | carry qa qb x0 =>
        simp only [derivMul]
        rw [ha.valid.step_stable i hia, ha.valid.step_stable _ (Nat.le_max_left _ _),
            hb.valid.step_stable i hib, hb.valid.step_stable _ (Nat.le_max_right _ _)]
      | _ => rfl
    · intro i hi q
      have hia : Da.auto.L ≤ i := Nat.le_trans (Nat.le_max_left _ _) hi
      have hib : Db.auto.L ≤ i := Nat.le_trans (Nat.le_max_right _ _) hi
      cases q with
      | carry qa qb x0 =>
        simp only [derivMul]
        rw [ha.valid.out_stable i hia, ha.valid.out_stable _ (Nat.le_max_left _ _),
            hb.valid.out_stable i hib, hb.valid.out_stable _ (Nat.le_max_right _ _)]
      | _ => rfl
    · rcases ha.valid.finite_wit with ⟨wfa, enca, hia, hsa, hlta, hinja⟩
      rcases hb.valid.finite_wit with ⟨wfb, encb, hib, hsb, hltb, hinjb⟩
      refine ⟨fun q => ∃ qa qb x0, q = .carry qa qb x0 ∧ wfa qa ∧ wfb qb,
              fun q => match q with
                | .carry qa qb x0 => (if x0 then 1 else 0) + 2 * (enca qa * Db.card + encb qb)
                | _ => 0,
              fun b => ⟨Da.auto.init1 b, Db.auto.init1 b, b, rfl, hia b, hib b⟩, ?_, ?_, ?_⟩
      · rintro i _ b ⟨qa, qb, x0, rfl, hqa, hqb⟩
        exact ⟨Da.auto.step i qa b, Db.auto.step i qb b, x0, rfl, hsa i qa b hqa, hsb i qb b hqb⟩
      · rintro _ ⟨qa, qb, x0, rfl, hqa, hqb⟩
        have hp := pair_encode_lt (hlta qa hqa) (hltb qb hqb)
        simp only [derivMul]
        cases x0 <;> simp <;> omega
      · rintro _ _ ⟨qa1, qb1, x1, rfl, hqa1, hqb1⟩ ⟨qa2, qb2, x2, rfl, hqa2, hqb2⟩ heq
        have hx : x1 = x2 := by cases x1 <;> cases x2 <;> simp at heq ⊢ <;> omega
        subst hx
        have hp : enca qa1 * Db.card + encb qb1 = enca qa2 * Db.card + encb qb2 := by
          cases x1 <;> simp at heq <;> omega
        rcases pair_encode_inj (hltb qb1 hqb1) (hltb qb2 hqb2) hp with ⟨he1, he2⟩
        rw [hinja qa1 qa2 hqa1 hqa2 he1, hinjb qb1 qb2 hqb1 hqb2 he2]
  · intro b
    simp only [derivMul, ha.bit0_eq, hb.bit0_eq, bit0Val, MixedExpr.eval]
    have hmul1 : ∀ u v : BitVec 1, (u * v).msb = (u.msb && v.msb) := by
      intro u v
      have hu : u = BitVec.cons u.msb (0#0) := by
        have := cons_msb_setWidth u; simpa [Subsingleton.elim (u.setWidth 0) (0#0)] using this.symm
      have hv : v = BitVec.cons v.msb (0#0) := by
        have := cons_msb_setWidth v; simpa [Subsingleton.elim (v.setWidth 0) (0#0)] using this.symm
      rw [hu, hv]
      cases u.msb <;> cases v.msb <;> decide
    exact (hmul1 _ _).symm
  · intro i hi x
    cases i with
    | zero => omega
    | succ k =>
      rw [derivMul_run Da Db hi x]
      simp only [derivMul]
      rw [ha.bit0_eq, hb.bit0_eq, ha.deriv_eq (k + 1) hi x, hb.deriv_eq (k + 1) hi x]
      exact (bitDeriv_mul_succ ea.coherent eb.coherent k x).symm

private theorem derivGateLeft_run (isOr : Bool) (Ma : FullAuto) (Db : DerivAuto) :
    ∀ {i : Nat} (hi : 1 ≤ i) (x : BitVec i),
      (derivGateLeft isOr Ma Db).auto.run hi x = .pair (Ma.run i x) (Db.auto.run hi x)
  | 0, hi, _ => absurd hi (by omega)
  | 1, _, x => by simp [SliceAuto.run, derivGateLeft, FullAuto.run]
  | i + 2, _, x => by
    have hstep : (derivGateLeft isOr Ma Db).auto.run (i := i + 2) (by omega) x =
        (derivGateLeft isOr Ma Db).auto.step (i + 1) ((derivGateLeft isOr Ma Db).auto.run (by omega) (x.setWidth (i + 1))) x.msb := rfl
    rw [hstep, derivGateLeft_run isOr Ma Db (by omega) (x.setWidth (i + 1))]
    rfl

private theorem derivGateRight_run (isOr : Bool) (Da : DerivAuto) (Mb : FullAuto) :
    ∀ {i : Nat} (hi : 1 ≤ i) (x : BitVec i),
      (derivGateRight isOr Da Mb).auto.run hi x = .pair (Da.auto.run hi x) (Mb.run i x)
  | 0, hi, _ => absurd hi (by omega)
  | 1, _, x => by simp [SliceAuto.run, derivGateRight, FullAuto.run]
  | i + 2, _, x => by
    have hstep : (derivGateRight isOr Da Mb).auto.run (i := i + 2) (by omega) x =
        (derivGateRight isOr Da Mb).auto.step (i + 1) ((derivGateRight isOr Da Mb).auto.run (by omega) (x.setWidth (i + 1))) x.msb := rfl
    rw [hstep, derivGateRight_run isOr Da Mb (by omega) (x.setWidth (i + 1))]
    rfl

private theorem derivGateLeft_sound (isOr : Bool) {ea eb Ma Db}
    (hfa : FullAutoSound ea Ma) (hzero : ∀ (i : Nat), 1 ≤ i → ∀ x : BitVec i, bitDeriv (fun w => ea.eval w) i x = false)
    (hdb : DerivAutoSound eb Db) :
    DerivAutoSound (if isOr then .or ea eb else .and ea eb) (derivGateLeft isOr Ma Db) := by
  constructor
  · constructor
    · exact Nat.le_trans (Nat.le_max_left 1 Ma.sigBits) (Nat.le_max_left _ _)
    · intro i hi q b
      have hia : Ma.sigBits ≤ i := Nat.le_trans (Nat.le_trans (Nat.le_max_right 1 Ma.sigBits) (Nat.le_max_left _ _)) hi
      have hia' : Ma.sigBits ≤ max (max 1 Ma.sigBits) Db.auto.L :=
        Nat.le_trans (Nat.le_max_right 1 Ma.sigBits) (Nat.le_max_left _ _)
      have hib : Db.auto.L ≤ i := Nat.le_trans (Nat.le_max_right _ _) hi
      cases q with
      | pair qa qb =>
        simp only [derivGateLeft]
        rw [hfa.step_stable i hia, hfa.step_stable _ hia',
            hdb.valid.step_stable i hib, hdb.valid.step_stable _ (Nat.le_max_right _ _)]
      | _ => rfl
    · intro i hi q
      have hia : Ma.sigBits ≤ i := Nat.le_trans (Nat.le_trans (Nat.le_max_right 1 Ma.sigBits) (Nat.le_max_left _ _)) hi
      have hia' : Ma.sigBits ≤ max (max 1 Ma.sigBits) Db.auto.L :=
        Nat.le_trans (Nat.le_max_right 1 Ma.sigBits) (Nat.le_max_left _ _)
      have hib : Db.auto.L ≤ i := Nat.le_trans (Nat.le_max_right _ _) hi
      cases q with
      | pair qa qb =>
        simp only [derivGateLeft]
        rw [hfa.out_stable i hia, hfa.out_stable _ hia',
            hdb.valid.out_stable i hib, hdb.valid.out_stable _ (Nat.le_max_right _ _)]
      | _ => rfl
    · rcases hfa.finite_wit with ⟨wfa, enca, hia, hsa, hlta, hinja⟩
      rcases hdb.valid.finite_wit with ⟨wfb, encb, hib, hsb, hltb, hinjb⟩
      refine ⟨fun q => ∃ qa qb, q = .pair qa qb ∧ wfa qa ∧ wfb qb,
              fun q => match q with | .pair qa qb => enca qa * Db.card + encb qb | _ => 0,
              fun b => ⟨Ma.step 0 Ma.init b, Db.auto.init1 b, rfl, hsa 0 Ma.init b hia, hib b⟩, ?_, ?_, ?_⟩
      · rintro i _ b ⟨qa, qb, rfl, hqa, hqb⟩
        exact ⟨Ma.step i qa b, Db.auto.step i qb b, rfl, hsa i qa b hqa, hsb i qb b hqb⟩
      · rintro _ ⟨qa, qb, rfl, hqa, hqb⟩
        exact pair_encode_lt (hlta qa hqa) (hltb qb hqb)
      · rintro _ _ ⟨qa1, qb1, rfl, hqa1, hqb1⟩ ⟨qa2, qb2, rfl, hqa2, hqb2⟩ heq
        rcases pair_encode_inj (hltb qb1 hqb1) (hltb qb2 hqb2) heq with ⟨he1, he2⟩
        rw [hinja qa1 qa2 hqa1 hqa2 he1, hinjb qb1 qb2 hqb1 hqb2 he2]
  · intro b
    have h0 : Ma.out 0 Ma.init b = (ea.eval 1 (BitVec.cons b 0#0)).msb := hfa.out_eq 0 (0#0) b
    cases isOr <;> simp [derivGateLeft, h0, hdb.bit0_eq, bit0Val, MixedExpr.eval,
                         BitVec.msb_and, BitVec.msb_or]
  · intro i hi x
    rw [derivGateLeft_run isOr Ma Db hi x]
    have hza := hzero i hi x
    cases isOr
    · simp only [derivGateLeft, ↓reduceIte, Bool.false_eq_true]
      rw [hfa.out_eq i x false, hdb.deriv_eq i hi x]
      change (val0 (fun w => ea.eval w) i x && bitDeriv (fun w => eb.eval w) i x) =
             bitDeriv (fun w y => ea.eval w y &&& eb.eval w y) i x
      rw [bitDeriv_and, hza]
      simp
    · simp only [derivGateLeft, ↓reduceIte]
      rw [hfa.out_eq i x false, hdb.deriv_eq i hi x]
      change (!val0 (fun w => ea.eval w) i x && bitDeriv (fun w => eb.eval w) i x) =
             bitDeriv (fun w y => ea.eval w y ||| eb.eval w y) i x
      rw [bitDeriv_or, hza]
      simp

private theorem derivGateRight_sound (isOr : Bool) {ea eb Da Mb}
    (hda : DerivAutoSound ea Da)
    (hfb : FullAutoSound eb Mb) (hzero : ∀ (i : Nat), 1 ≤ i → ∀ x : BitVec i, bitDeriv (fun w => eb.eval w) i x = false) :
    DerivAutoSound (if isOr then .or ea eb else .and ea eb) (derivGateRight isOr Da Mb) := by
  constructor
  · constructor
    · exact Nat.le_trans hda.valid.hL (Nat.le_max_left _ _)
    · intro i hi q b
      have hia : Da.auto.L ≤ i := Nat.le_trans (Nat.le_max_left _ _) hi
      have hib : Mb.sigBits ≤ i := Nat.le_trans (Nat.le_trans (Nat.le_max_right 1 Mb.sigBits) (Nat.le_max_right _ _)) hi
      have hib' : Mb.sigBits ≤ max Da.auto.L (max 1 Mb.sigBits) :=
        Nat.le_trans (Nat.le_max_right 1 Mb.sigBits) (Nat.le_max_right _ _)
      cases q with
      | pair qa qb =>
        simp only [derivGateRight]
        rw [hda.valid.step_stable i hia, hda.valid.step_stable _ (Nat.le_max_left _ _),
            hfb.step_stable i hib, hfb.step_stable _ hib']
      | _ => rfl
    · intro i hi q
      have hia : Da.auto.L ≤ i := Nat.le_trans (Nat.le_max_left _ _) hi
      have hib : Mb.sigBits ≤ i := Nat.le_trans (Nat.le_trans (Nat.le_max_right 1 Mb.sigBits) (Nat.le_max_right _ _)) hi
      have hib' : Mb.sigBits ≤ max Da.auto.L (max 1 Mb.sigBits) :=
        Nat.le_trans (Nat.le_max_right 1 Mb.sigBits) (Nat.le_max_right _ _)
      cases q with
      | pair qa qb =>
        simp only [derivGateRight]
        rw [hda.valid.out_stable i hia, hda.valid.out_stable _ (Nat.le_max_left _ _),
            hfb.out_stable i hib, hfb.out_stable _ hib']
      | _ => rfl
    · rcases hda.valid.finite_wit with ⟨wfa, enca, hia, hsa, hlta, hinja⟩
      rcases hfb.finite_wit with ⟨wfb, encb, hib, hsb, hltb, hinjb⟩
      refine ⟨fun q => ∃ qa qb, q = .pair qa qb ∧ wfa qa ∧ wfb qb,
              fun q => match q with | .pair qa qb => enca qa * Mb.card + encb qb | _ => 0,
              fun b => ⟨Da.auto.init1 b, Mb.step 0 Mb.init b, rfl, hia b, hsb 0 Mb.init b hib⟩, ?_, ?_, ?_⟩
      · rintro i _ b ⟨qa, qb, rfl, hqa, hqb⟩
        exact ⟨Da.auto.step i qa b, Mb.step i qb b, rfl, hsa i qa b hqa, hsb i qb b hqb⟩
      · rintro _ ⟨qa, qb, rfl, hqa, hqb⟩
        exact pair_encode_lt (hlta qa hqa) (hltb qb hqb)
      · rintro _ _ ⟨qa1, qb1, rfl, hqa1, hqb1⟩ ⟨qa2, qb2, rfl, hqa2, hqb2⟩ heq
        rcases pair_encode_inj (hltb qb1 hqb1) (hltb qb2 hqb2) heq with ⟨he1, he2⟩
        rw [hinja qa1 qa2 hqa1 hqa2 he1, hinjb qb1 qb2 hqb1 hqb2 he2]
  · intro b
    have h0 : Mb.out 0 Mb.init b = (eb.eval 1 (BitVec.cons b 0#0)).msb := hfb.out_eq 0 (0#0) b
    cases isOr <;> simp [derivGateRight, hda.bit0_eq, h0, bit0Val, MixedExpr.eval,
                         BitVec.msb_and, BitVec.msb_or]
  · intro i hi x
    rw [derivGateRight_run isOr Da Mb hi x]
    have hzb := hzero i hi x
    cases isOr
    · simp only [derivGateRight, ↓reduceIte, Bool.false_eq_true]
      rw [hfb.out_eq i x false, hda.deriv_eq i hi x]
      change (val0 (fun w => eb.eval w) i x && bitDeriv (fun w => ea.eval w) i x) =
             bitDeriv (fun w y => ea.eval w y &&& eb.eval w y) i x
      rw [bitDeriv_and, hzb]
      simp
    · simp only [derivGateRight, ↓reduceIte]
      rw [hfb.out_eq i x false, hda.deriv_eq i hi x]
      change (!val0 (fun w => eb.eval w) i x && bitDeriv (fun w => ea.eval w) i x) =
             bitDeriv (fun w y => ea.eval w y ||| eb.eval w y) i x
      rw [bitDeriv_or, hzb]
      simp

private theorem derivZero_of_checkZeroGe1 {e D} (hs : DerivAutoSound e D) (hz : D.checkZeroGe1 = true) :
    ∀ (i : Nat), 1 ≤ i → ∀ x : BitVec i, bitDeriv (fun w => e.eval w) i x = false := by
  intro i hi x
  rw [← hs.deriv_eq i hi x]
  exact (checkAutoConst_iff hs.valid false).2 hz i hi x

/-- Master Compiler Soundness Theorem for `compileBSDA`. -/
theorem compileBSDA_sound : ∀ (e : MixedExpr) (D : DerivAuto), compileBSDA e = some D → DerivAutoSound e D
  | .var, D, h => by
    simp only [compileBSDA, Option.some.injEq] at h; subst h
    exact ⟨sliceAutoValid_unit true,
           fun b => by simp [derivConstAuto, bit0Val, MixedExpr.eval, BitVec.msb_cons],
           fun i _ x => by simpa [derivConstAuto, MixedExpr.eval] using (bitDeriv_id i x).symm⟩
  | .const c, D, h => by
    simp only [compileBSDA, Option.some.injEq] at h; subst h
    exact ⟨sliceAutoValid_unit false,
           fun _ => by simp [derivConstAuto, bit0Val, MixedExpr.eval, msb_ofInt_eq_intBit],
           fun i _ x => by simpa [derivConstAuto, MixedExpr.eval] using (bitDeriv_const c i x).symm⟩
  | .not e, D, h => by
    simp only [compileBSDA] at h
    cases he : compileBSDA e with
    | none => simp [he] at h
    | some De =>
      simp only [he, Option.map_some, Option.some.injEq] at h; subst h
      have hs := compileBSDA_sound e De he
      exact ⟨hs.valid,
             fun b => by simp [derivNot, hs.bit0_eq, bit0Val, MixedExpr.eval, BitVec.msb_not],
             fun i hi x => by simp [derivNot, hs.deriv_eq i hi x, MixedExpr.eval, bitDeriv_not]⟩
  | .shl k e, D, h => by
    simp only [compileBSDA] at h
    by_cases hk : k = 0
    · subst hk
      simp only [↓reduceIte] at h
      have hs := compileBSDA_sound e D h
      exact ⟨hs.valid,
             fun b => by simpa [MixedExpr.eval, bit0Val] using hs.bit0_eq b,
             fun i hi x => by simpa [MixedExpr.eval, bitDeriv] using hs.deriv_eq i hi x⟩
    · simp only [hk, ↓reduceIte, Option.some.injEq] at h; subst h
      have hk1 : 1 ≤ k := by omega
      exact ⟨sliceAutoValid_unit false,
             fun b => by
               simp only [derivConstAuto, bit0Val, MixedExpr.eval, BitVec.msb_eq_getLsbD_last,
                          BitVec.getLsbD_shiftLeft]
               have : 0 < k := by omega
               simp [this],
             fun i _ x => by
               change false = bitDeriv (fun w y => e.eval w y <<< k) i x
               exact (bitDeriv_shl e.coherent hk1 i x).symm⟩
  | .add a b, D, h => by
    simp only [compileBSDA, bind, Option.bind] at h
    cases ha : compileBSDA a <;> cases hb : compileBSDA b <;> simp [ha, hb] at h
    subst h
    have hsa := compileBSDA_sound a _ ha; have hsb := compileBSDA_sound b _ hb
    refine ⟨derivXorPair_valid hsa.valid hsb.valid, ?_, ?_⟩
    · intro x0
      simp only [derivXorPair, hsa.bit0_eq, hsb.bit0_eq, bit0Val, MixedExpr.eval]
      have hadd1 : ∀ u v : BitVec 1, (u + v).msb = (u.msb ^^ v.msb) := by
        intro u v
        have h := msb_add_eq (i := 0) u v
        have hu : (u.setWidth 0).toNat = 0 := by have := (u.setWidth 0).isLt; omega
        have hv : (v.setWidth 0).toNat = 0 := by have := (v.setWidth 0).isLt; omega
        simpa [hu, hv] using h
      exact (hadd1 _ _).symm
    · intro i hi x
      rw [derivXorPair_run _ _ hi x]
      simp only [derivXorPair, hsa.deriv_eq i hi x, hsb.deriv_eq i hi x]
      exact (bitDeriv_add a.coherent b.coherent i x).symm
  | .sub a b, D, h => by
    simp only [compileBSDA, bind, Option.bind] at h
    cases ha : compileBSDA a <;> cases hb : compileBSDA b <;> simp [ha, hb] at h
    subst h
    have hsa := compileBSDA_sound a _ ha; have hsb := compileBSDA_sound b _ hb
    refine ⟨derivXorPair_valid hsa.valid hsb.valid, ?_, ?_⟩
    · intro x0
      simp only [derivXorPair, hsa.bit0_eq, hsb.bit0_eq, bit0Val, MixedExpr.eval]
      have hsub1 : ∀ u v : BitVec 1, (u - v).msb = (u.msb ^^ v.msb) := by
        intro u v
        have h := msb_sub_eq (i := 0) u v
        have hu : (u.setWidth 0).toNat = 0 := by have := (u.setWidth 0).isLt; omega
        have hv : (v.setWidth 0).toNat = 0 := by have := (v.setWidth 0).isLt; omega
        simpa [hu, hv] using h
      exact (hsub1 _ _).symm
    · intro i hi x
      rw [derivXorPair_run _ _ hi x]
      simp only [derivXorPair, hsa.deriv_eq i hi x, hsb.deriv_eq i hi x]
      exact (bitDeriv_sub a.coherent b.coherent i x).symm
  | .xor a b, D, h => by
    simp only [compileBSDA, bind, Option.bind] at h
    cases ha : compileBSDA a <;> cases hb : compileBSDA b <;> simp [ha, hb] at h
    subst h
    have hsa := compileBSDA_sound a _ ha; have hsb := compileBSDA_sound b _ hb
    refine ⟨derivXorPair_valid hsa.valid hsb.valid, ?_, ?_⟩
    · intro x0
      simp [derivXorPair, hsa.bit0_eq, hsb.bit0_eq, bit0Val, MixedExpr.eval, BitVec.msb_xor]
    · intro i hi x
      rw [derivXorPair_run _ _ hi x]
      simp only [derivXorPair, hsa.deriv_eq i hi x, hsb.deriv_eq i hi x]
      exact (bitDeriv_xor i x).symm
  | .mul a b, D, h => by
    simp only [compileBSDA, bind, Option.bind] at h
    cases ha : compileBSDA a <;> cases hb : compileBSDA b <;> simp [ha, hb] at h
    subst h
    exact derivMul_sound (compileBSDA_sound a _ ha) (compileBSDA_sound b _ hb)
  | .and a b, D, h => by
    simp only [compileBSDA] at h
    cases hfa : compileFull a <;> cases hfb : compileFull b <;> simp only [hfa, hfb] at h
    · -- none, none
      cases hda : compileBSDA a <;> cases hdb : compileBSDA b <;> simp only [hda, hdb] at h
      · simp at h
      · simp at h
      · simp at h
      · rename_i da db
        cases hz : da.checkZeroGe1 && db.checkZeroGe1
        · simp [hz] at h
        · simp only [hz, ↓reduceIte, Option.some.injEq] at h; subst h
          have hsa := compileBSDA_sound a da hda; have hsb := compileBSDA_sound b db hdb
          have hza := derivZero_of_checkZeroGe1 hsa (Bool.and_eq_true_iff.1 hz).1
          have hzb := derivZero_of_checkZeroGe1 hsb (Bool.and_eq_true_iff.1 hz).2
          exact ⟨sliceAutoValid_unit false,
                 fun x0 => by simp [derivConstAuto, hsa.bit0_eq, hsb.bit0_eq, bit0Val, MixedExpr.eval, BitVec.msb_and],
                 fun i hi x => by simp [derivConstAuto, MixedExpr.eval, bitDeriv_and, hza i hi x, hzb i hi x]⟩
    · -- none, some fb
      rename_i fb
      cases hda : compileBSDA a <;> cases hdb : compileBSDA b <;> simp only [hda, hdb] at h
      · simp at h
      · simp at h
      · simp at h
      · rename_i da db
        have hsa := compileBSDA_sound a da hda; have hsb := compileBSDA_sound b db hdb
        cases hz : da.checkZeroGe1 && db.checkZeroGe1
        · simp only [hz, Bool.false_eq_true, ↓reduceIte] at h
          cases hzb : db.checkZeroGe1
          · simp [hzb] at h
          · simp only [hzb, ↓reduceIte, Option.some.injEq] at h; subst h
            exact derivGateRight_sound false hsa (compileFull_sound b fb hfb) (derivZero_of_checkZeroGe1 hsb hzb)
        · simp only [hz, ↓reduceIte, Option.some.injEq] at h; subst h
          have hza := derivZero_of_checkZeroGe1 hsa (Bool.and_eq_true_iff.1 hz).1
          have hzb := derivZero_of_checkZeroGe1 hsb (Bool.and_eq_true_iff.1 hz).2
          exact ⟨sliceAutoValid_unit false,
                 fun x0 => by simp [derivConstAuto, hsa.bit0_eq, hsb.bit0_eq, bit0Val, MixedExpr.eval, BitVec.msb_and],
                 fun i hi x => by simp [derivConstAuto, MixedExpr.eval, bitDeriv_and, hza i hi x, hzb i hi x]⟩
    · -- some fa, none
      rename_i fa
      cases hda : compileBSDA a <;> cases hdb : compileBSDA b <;> simp only [hda, hdb] at h
      · simp at h
      · simp at h
      · simp at h
      · rename_i da db
        have hsa := compileBSDA_sound a da hda; have hsb := compileBSDA_sound b db hdb
        cases hz : da.checkZeroGe1 && db.checkZeroGe1
        · simp only [hz, Bool.false_eq_true, ↓reduceIte] at h
          cases hza : da.checkZeroGe1
          · simp [hza] at h
          · simp only [hza, ↓reduceIte, Option.some.injEq] at h; subst h
            exact derivGateLeft_sound false (compileFull_sound a fa hfa) (derivZero_of_checkZeroGe1 hsa hza) hsb
        · simp only [hz, ↓reduceIte, Option.some.injEq] at h; subst h
          have hza := derivZero_of_checkZeroGe1 hsa (Bool.and_eq_true_iff.1 hz).1
          have hzb := derivZero_of_checkZeroGe1 hsb (Bool.and_eq_true_iff.1 hz).2
          exact ⟨sliceAutoValid_unit false,
                 fun x0 => by simp [derivConstAuto, hsa.bit0_eq, hsb.bit0_eq, bit0Val, MixedExpr.eval, BitVec.msb_and],
                 fun i hi x => by simp [derivConstAuto, MixedExpr.eval, bitDeriv_and, hza i hi x, hzb i hi x]⟩
    · -- some fa, some fb
      rename_i fa fb
      simp only [Option.some.injEq] at h; subst h
      have hfull : compileFull (.and a b) = some (fullBitwise and fa fb) := by
        simp [compileFull, hfa, hfb]
      exact fullToDeriv_sound (compileFull_sound (.and a b) _ hfull)
  | .or a b, D, h => by
    simp only [compileBSDA] at h
    cases hfa : compileFull a <;> cases hfb : compileFull b <;> simp only [hfa, hfb] at h
    · -- none, none
      cases hda : compileBSDA a <;> cases hdb : compileBSDA b <;> simp only [hda, hdb] at h
      · simp at h
      · simp at h
      · simp at h
      · rename_i da db
        cases hz : da.checkZeroGe1 && db.checkZeroGe1
        · simp [hz] at h
        · simp only [hz, ↓reduceIte, Option.some.injEq] at h; subst h
          have hsa := compileBSDA_sound a da hda; have hsb := compileBSDA_sound b db hdb
          have hza := derivZero_of_checkZeroGe1 hsa (Bool.and_eq_true_iff.1 hz).1
          have hzb := derivZero_of_checkZeroGe1 hsb (Bool.and_eq_true_iff.1 hz).2
          exact ⟨sliceAutoValid_unit false,
                 fun x0 => by simp [derivConstAuto, hsa.bit0_eq, hsb.bit0_eq, bit0Val, MixedExpr.eval, BitVec.msb_or],
                 fun i hi x => by simp [derivConstAuto, MixedExpr.eval, bitDeriv_or, hza i hi x, hzb i hi x]⟩
    · -- none, some fb
      rename_i fb
      cases hda : compileBSDA a <;> cases hdb : compileBSDA b <;> simp only [hda, hdb] at h
      · simp at h
      · simp at h
      · simp at h
      · rename_i da db
        have hsa := compileBSDA_sound a da hda; have hsb := compileBSDA_sound b db hdb
        cases hz : da.checkZeroGe1 && db.checkZeroGe1
        · simp only [hz, Bool.false_eq_true, ↓reduceIte] at h
          cases hzb : db.checkZeroGe1
          · simp [hzb] at h
          · simp only [hzb, ↓reduceIte, Option.some.injEq] at h; subst h
            exact derivGateRight_sound true hsa (compileFull_sound b fb hfb) (derivZero_of_checkZeroGe1 hsb hzb)
        · simp only [hz, ↓reduceIte, Option.some.injEq] at h; subst h
          have hza := derivZero_of_checkZeroGe1 hsa (Bool.and_eq_true_iff.1 hz).1
          have hzb := derivZero_of_checkZeroGe1 hsb (Bool.and_eq_true_iff.1 hz).2
          exact ⟨sliceAutoValid_unit false,
                 fun x0 => by simp [derivConstAuto, hsa.bit0_eq, hsb.bit0_eq, bit0Val, MixedExpr.eval, BitVec.msb_or],
                 fun i hi x => by simp [derivConstAuto, MixedExpr.eval, bitDeriv_or, hza i hi x, hzb i hi x]⟩
    · -- some fa, none
      rename_i fa
      cases hda : compileBSDA a <;> cases hdb : compileBSDA b <;> simp only [hda, hdb] at h
      · simp at h
      · simp at h
      · simp at h
      · rename_i da db
        have hsa := compileBSDA_sound a da hda; have hsb := compileBSDA_sound b db hdb
        cases hz : da.checkZeroGe1 && db.checkZeroGe1
        · simp only [hz, Bool.false_eq_true, ↓reduceIte] at h
          cases hza : da.checkZeroGe1
          · simp [hza] at h
          · simp only [hza, ↓reduceIte, Option.some.injEq] at h; subst h
            exact derivGateLeft_sound true (compileFull_sound a fa hfa) (derivZero_of_checkZeroGe1 hsa hza) hsb
        · simp only [hz, ↓reduceIte, Option.some.injEq] at h; subst h
          have hza := derivZero_of_checkZeroGe1 hsa (Bool.and_eq_true_iff.1 hz).1
          have hzb := derivZero_of_checkZeroGe1 hsb (Bool.and_eq_true_iff.1 hz).2
          exact ⟨sliceAutoValid_unit false,
                 fun x0 => by simp [derivConstAuto, hsa.bit0_eq, hsb.bit0_eq, bit0Val, MixedExpr.eval, BitVec.msb_or],
                 fun i hi x => by simp [derivConstAuto, MixedExpr.eval, bitDeriv_or, hza i hi x, hzb i hi x]⟩
    · -- some fa, some fb
      rename_i fa fb
      simp only [Option.some.injEq] at h; subst h
      have hfull : compileFull (.or a b) = some (fullBitwise or fa fb) := by
        simp [compileFull, hfa, hfb]
      exact fullToDeriv_sound (compileFull_sound (.or a b) _ hfull)

-- ----------------------------------------------------------------------------
-- 4C. Crown-Jewel Three-Way BSDA Engine Theorems (Exact ↔ Lifting ∀ w ≥ 2)
-- ----------------------------------------------------------------------------

/-- **Engine Theorem 1 (Exact Necessary & Sufficient BSDA Decision Theorem):**
    For any `MixedExpr` compiling to `D`, `e` is bijective on `BitVec w` for ALL `w ≥ 2`
    IF AND ONLY IF the pure-data finite-state checker `D.checkBijective = true`. -/
theorem bsda_bijective_iff (e : MixedExpr) (D : DerivAuto) (h : compileBSDA e = some D) :
    (∀ w, 2 ≤ w → Bijective (e.eval w)) ↔ D.checkBijective = true := by
  have hs := compileBSDA_sound e D h
  rw [bijective_all_ge_two_iff e.coherent]
  unfold DerivAuto.checkBijective
  rw [Bool.and_eq_true, ← checkAutoConst_iff hs.valid true]
  constructor
  · intro hall
    refine ⟨?_, ?_⟩
    · have h0 := hall 0 (0#0)
      simpa [bitDeriv, bit0Val, hs.bit0_eq] using h0
    · intro i hi x
      rw [hs.deriv_eq i hi x]
      exact hall i x
  · rintro ⟨hb0, hge1⟩ i x
    cases i with
    | zero =>
      have hx : x = 0#0 := Subsingleton.elim x (0#0)
      subst hx
      simpa [bitDeriv, bit0Val, hs.bit0_eq] using hb0
    | succ k =>
      rw [← hs.deriv_eq (k + 1) (by omega) x]
      exact hge1 (k + 1) (by omega) x

/-- **Engine Theorem 2 (Exact Generalized Rivest Finite-Slice Lifting Theorem):**
    For any `MixedExpr` compiling to `D`, `e` is bijective on `BitVec w` for ALL `w ≥ 2`
    IF AND ONLY IF `e` is bijective at the single computable finite width `D.horizonW`
    (which equals `2` for all classical Rivest polynomials!). -/
theorem bsda_finite_slice_iff (e : MixedExpr) (D : DerivAuto) (h : compileBSDA e = some D) :
    (∀ w, 2 ≤ w → Bijective (e.eval w)) ↔ Bijective (e.eval D.horizonW) := by
  have hs := compileBSDA_sound e D h
  have hW : 2 ≤ D.horizonW := by unfold DerivAuto.horizonW; have := hs.valid.hL; omega
  constructor
  · intro hall; exact hall D.horizonW hW
  · intro hbijW
    rw [bijective_iff_forall_bitDeriv e.coherent D.horizonW] at hbijW
    rw [bijective_all_ge_two_iff e.coherent]
    intro i x
    cases i with
    | zero => exact hbijW 0 (by omega) x
    | succ k =>
      have hall_ge1 : ∀ (j : Nat) (hj : 1 ≤ j) (y : BitVec j),
          D.auto.out j (D.auto.run hj y) = true := by
        apply (sliceAuto_all_iff_bounded hs.valid true).2
        intro j hj hle y
        rw [hs.deriv_eq j hj y]
        exact hbijW j (by unfold DerivAuto.horizonW; omega) y
      rw [← hs.deriv_eq (k + 1) (by omega) x]
      exact hall_ge1 (k + 1) (by omega) x

/-- **1-Line Kernel Reflection Rule (Positive):** certifies `∀ w ≥ 2, Bijective (e.eval w)` by `decide`. -/
theorem bsda_decide_bijective (e : MixedExpr)
    (h : (compileBSDA e).map DerivAuto.checkBijective = some true) :
    ∀ w, 2 ≤ w → Bijective (e.eval w) := by
  cases hc : compileBSDA e with
  | none => simp [hc] at h
  | some D =>
    simp only [hc, Option.map_some, Option.some.injEq] at h
    exact (bsda_bijective_iff e D hc).2 h

/-- **1-Line Kernel Reflection Rule (Negative):** refutes `∀ w ≥ 2, Bijective (e.eval w)` by `decide`. -/
theorem bsda_decide_not_bijective (e : MixedExpr)
    (h : (compileBSDA e).map DerivAuto.checkBijective = some false) :
    ¬ (∀ w, 2 ≤ w → Bijective (e.eval w)) := by
  cases hc : compileBSDA e with
  | none => simp [hc] at h
  | some D =>
    simp only [hc, Option.map_some, Option.some.injEq] at h
    intro hall
    have ht := (bsda_bijective_iff e D hc).1 hall
    rw [h] at ht; exact Bool.noConfusion ht

theorem coherent_bvPow (d : Nat) : Coherent (fun w x => bvPow (w := w) x d) := by
  induction d with
  | zero => exact coherent_const 1
  | succ d ih => exact coherent_mul coherent_id ih

theorem bit0Val_bvPow (d : Nat) (b : Bool) :
    bit0Val (fun w x => bvPow (w := w) x d) b = if d = 0 then true else b := by
  induction d with
  | zero =>
    simp [bit0Val, bvPow]
  | succ d ih =>
    simp only [bit0Val, bvPow] at ih ⊢
    have hmul1 : ∀ u v : BitVec 1, (u * v).msb = (u.msb && v.msb) := by
      intro u v
      have hu : u = BitVec.cons u.msb (0#0) := by
        have := cons_msb_setWidth u; simpa [Subsingleton.elim (u.setWidth 0) (0#0)] using this.symm
      have hv : v = BitVec.cons v.msb (0#0) := by
        have := cons_msb_setWidth v; simpa [Subsingleton.elim (v.setWidth 0) (0#0)] using this.symm
      rw [hu, hv]; cases u.msb <;> cases v.msb <;> decide
    rw [hmul1, BitVec.msb_cons, ih]
    cases d <;> cases b <;> rfl

/-- Exact bit-slice derivative of `x^d` for all `i ≥ 1` (width `i + 1`):
    `d = 0 => false`, `d = 1 => true`, `d ≥ 2 even => false`, `d ≥ 3 odd => x_0`. -/
theorem bitDeriv_bvPow_succ (d i : Nat) (x : BitVec (i + 1)) :
    bitDeriv (fun w y => bvPow (w := w) y d) (i + 1) x =
      if d = 0 then false
      else if d = 1 then true
      else if d % 2 = 1 then x.getLsbD 0
      else false := by
  induction d with
  | zero =>
    simpa [bvPow] using bitDeriv_const 1 (i + 1) x
  | succ d ih =>
    change bitDeriv (fun w y => y * bvPow (w := w) y d) (i + 1) x = _
    rw [bitDeriv_mul_succ coherent_id (coherent_bvPow d) i x]
    rw [bitDeriv_id, ih, bit0Val_bvPow]
    have hvar0 : bit0Val (fun _ y => y) (x.getLsbD 0) = x.getLsbD 0 := by
      simp [bit0Val, BitVec.msb_cons]
    rw [hvar0]
    cases d with
    | zero => simp
    | succ d' =>
      cases d' with
      | zero => simp
      | succ d'' =>
        have hne1 : d'' + 2 ≠ 0 := by omega
        have hne2 : d'' + 2 ≠ 1 := by omega
        have hne3 : d'' + 3 ≠ 0 := by omega
        have hne4 : d'' + 3 ≠ 1 := by omega
        simp only [hne1, hne2, hne3, hne4, ↓reduceIte]
        rcases (show d'' % 2 = 0 ∨ d'' % 2 = 1 by omega) with hp | hp
        · have hp1 : (d'' + 2) % 2 = 0 := by omega
          have hp2 : (d'' + 3) % 2 = 1 := by omega
          simp [hp1, hp2]
        · have hp1 : (d'' + 2) % 2 = 1 := by omega
          have hp2 : (d'' + 3) % 2 = 0 := by omega
          simp [hp1, hp2]

theorem coherent_evalMaskedTerm (t : MaskedTerm) : Coherent (fun w => evalMaskedTerm w t) := by
  unfold evalMaskedTerm
  exact coherent_and (coherent_shl t.shift (coherent_mul (coherent_const t.coeff) (coherent_bvPow t.deg)))
    (coherent_const t.mask)

theorem coherent_evalMaskedPoly (a0 : Int) (ts : List MaskedTerm) :
    Coherent (fun w => evalMaskedPoly w a0 ts) := by
  induction ts with
  | nil => exact coherent_const a0
  | cons t ts ih =>
    simp only [evalMaskedPoly]
    cases t.op
    · exact coherent_add ih (coherent_evalMaskedTerm t)
    · exact coherent_sub ih (coherent_evalMaskedTerm t)
    · exact coherent_xor ih (coherent_evalMaskedTerm t)

theorem bitDeriv_evalMaskedTerm_zero (t : MaskedTerm) (x : BitVec 0) :
    bitDeriv (fun w => evalMaskedTerm w t) 0 x = termBit0Deriv t := by
  have hx : x = 0#0 := Subsingleton.elim x (0#0)
  subst hx
  unfold bitDeriv evalMaskedTerm termBit0Deriv
  have hmul1 : ∀ u v : BitVec 1, (u * v).msb = (u.msb && v.msb) := by
    intro u v
    have hu : u = BitVec.cons u.msb (0#0) := by
      have := cons_msb_setWidth u; simpa [Subsingleton.elim (u.setWidth 0) (0#0)] using this.symm
    have hv : v = BitVec.cons v.msb (0#0) := by
      have := cons_msb_setWidth v; simpa [Subsingleton.elim (v.setWidth 0) (0#0)] using this.symm
    rw [hu, hv]; cases u.msb <;> cases v.msb <;> decide
  by_cases hs : t.shift = 0
  · rw [hs]
    simp only [BitVec.shiftLeft_zero, BitVec.msb_and, msb_ofInt_eq_intBit, hmul1]
    have hp1 : (bvPow (BitVec.cons true (0#0)) t.deg).msb = if t.deg = 0 then true else true :=
      bit0Val_bvPow t.deg true
    have hp0 : (bvPow (BitVec.cons false (0#0)) t.deg).msb = if t.deg = 0 then true else false :=
      bit0Val_bvPow t.deg false
    rw [hp1, hp0]
    cases t.deg with
    | zero => simp
    | succ d =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, decide_true, Nat.succ_le_succ_iff, Nat.zero_le,
                 Bool.true_and, Bool.and_true, Bool.and_false, Bool.false_and]
      cases intBit t.coeff 0 <;> cases intBit t.mask 0 <;> rfl
  · have hmsb_shl : ∀ (u : BitVec 1), (u <<< t.shift).msb = false := by
      intro u
      rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft]
      have : 0 < t.shift := by omega
      simp [this]
    simp [hs, BitVec.msb_and, hmsb_shl]

theorem bitDeriv_evalMaskedTerm_succ (t : MaskedTerm) (i : Nat) (x : BitVec (i + 1)) :
    bitDeriv (fun w => evalMaskedTerm w t) (i + 1) x =
      (termLinDeriv t (i + 1) ^^ (termOddDeriv t (i + 1) && x.getLsbD 0)) := by
  unfold evalMaskedTerm
  rw [bitDeriv_and, bitDeriv_const]
  simp only [Bool.and_false, Bool.xor_false, Bool.false_xor]
  have hval_mask : val0 (fun w _ => BitVec.ofInt w t.mask) (i + 1) x = intBit t.mask (i + 1) := by
    simp [val0, msb_ofInt_eq_intBit]
  rw [hval_mask]
  by_cases hs : t.shift = 0
  · have hshl : (fun w y => (BitVec.ofInt w t.coeff * bvPow y t.deg) <<< t.shift) =
                (fun w y => BitVec.ofInt w t.coeff * bvPow y t.deg) := by
      funext w y; simp [hs]
    rw [hshl, bitDeriv_mul_succ (coherent_const t.coeff) (coherent_bvPow t.deg) i x]
    rw [bitDeriv_const, bitDeriv_bvPow_succ]
    have hc0 : bit0Val (fun w _ => BitVec.ofInt w t.coeff) (x.getLsbD 0) = intBit t.coeff 0 := by
      simp [bit0Val, msb_ofInt_eq_intBit]
    rw [hc0]
    simp only [Bool.and_false, Bool.xor_false, termLinDeriv, termOddDeriv, hs, decide_true, Bool.true_and]
    cases hd : t.deg with
    | zero => simp
    | succ d1 =>
      cases d1 with
      | zero => simp [Bool.and_comm]
      | succ d2 =>
        have hne0 : d2 + 2 ≠ 0 := by omega
        have hne1 : d2 + 2 ≠ 1 := by omega
        rcases (show d2 % 2 = 0 ∨ d2 % 2 = 1 by omega) with hp | hp
        · have hm : (d2 + 2) % 2 = 0 := by omega
          simp [hm]
        · have hm : (d2 + 2) % 2 = 1 := by omega
          have hge3 : 3 ≤ d2 + 2 := by omega
          simp only [hne0, hne1, hm, hge3, ↓reduceIte, decide_true, decide_false,
                     Bool.false_and, Bool.true_and, Bool.false_xor]
          cases intBit t.mask (i + 1) <;> cases intBit t.coeff 0 <;> cases x.getLsbD 0 <;> rfl
  · have hs1 : 1 ≤ t.shift := by omega
    rw [bitDeriv_shl (coherent_mul (coherent_const t.coeff) (coherent_bvPow t.deg)) hs1 (i + 1) x]
    simp [termLinDeriv, termOddDeriv, hs]

theorem bitDeriv_evalMaskedPoly_zero (a0 : Int) (ts : List MaskedTerm) (x : BitVec 0) :
    bitDeriv (fun w => evalMaskedPoly w a0 ts) 0 x = xorFold termBit0Deriv ts := by
  induction ts with
  | nil =>
    simpa [evalMaskedPoly, xorFold] using bitDeriv_const a0 0 x
  | cons t ts ih =>
    simp only [evalMaskedPoly, xorFold]
    cases t.op
    · simp only [applyConn]
      rw [bitDeriv_add (coherent_evalMaskedPoly a0 ts) (coherent_evalMaskedTerm t), ih, bitDeriv_evalMaskedTerm_zero]
    · simp only [applyConn]
      rw [bitDeriv_sub (coherent_evalMaskedPoly a0 ts) (coherent_evalMaskedTerm t), ih, bitDeriv_evalMaskedTerm_zero]
    · simp only [applyConn]
      rw [bitDeriv_xor, ih, bitDeriv_evalMaskedTerm_zero]

theorem bitDeriv_evalMaskedPoly_succ (a0 : Int) (ts : List MaskedTerm) (i : Nat) (x : BitVec (i + 1)) :
    bitDeriv (fun w => evalMaskedPoly w a0 ts) (i + 1) x =
      (xorFold (fun t => termLinDeriv t (i + 1)) ts ^^
       (xorFold (fun t => termOddDeriv t (i + 1)) ts && x.getLsbD 0)) := by
  induction ts with
  | nil =>
    simpa [evalMaskedPoly, xorFold] using bitDeriv_const a0 (i + 1) x
  | cons t ts ih =>
    simp only [evalMaskedPoly, xorFold]
    have hstep :
        bitDeriv (fun w y => applyConn t.op (evalMaskedPoly w a0 ts y) (evalMaskedTerm w t y)) (i + 1) x =
        (bitDeriv (fun w => evalMaskedPoly w a0 ts) (i + 1) x ^^
         bitDeriv (fun w => evalMaskedTerm w t) (i + 1) x) := by
      cases t.op
      · exact bitDeriv_add (coherent_evalMaskedPoly a0 ts) (coherent_evalMaskedTerm t) (i + 1) x
      · exact bitDeriv_sub (coherent_evalMaskedPoly a0 ts) (coherent_evalMaskedTerm t) (i + 1) x
      · exact bitDeriv_xor (i + 1) x
    rw [hstep, ih, bitDeriv_evalMaskedTerm_succ]
    cases xorFold (fun t => termLinDeriv t (i + 1)) ts <;>
    cases xorFold (fun t => termOddDeriv t (i + 1)) ts <;>
    cases termLinDeriv t (i + 1) <;>
    cases termOddDeriv t (i + 1) <;>
    cases x.getLsbD 0 <;> rfl

/-- **Infinite Theorem 1 (Generalized Bitwise-Masked Mixed-Connective Rivest Theorem):**
    For ANY constant `a0 : Int` and ANY list of masked shifted polynomial terms `ts` with
    arbitrary connectives `∈ {+, -, ^}`, `evalMaskedPoly w a0 ts` is bijective on `BitVec w`
    for ALL `w ≥ 2` IF AND ONLY IF:
    (1) bit-0 parity is `true`,
    (2) linear unshifted odd-coeff masks XOR to `true` at every bit `i ≥ 1`, AND
    (3) higher-odd-degree (`d ≥ 3`) unshifted odd-coeff masks XOR to `false` at every bit `i ≥ 1`. -/
theorem maskedPoly_bijective_iff (a0 : Int) (ts : List MaskedTerm) :
    (∀ w, 2 ≤ w → Bijective (evalMaskedPoly w a0 ts)) ↔
      (xorFold termBit0Deriv ts = true ∧
       (∀ i, 1 ≤ i → xorFold (fun t => termLinDeriv t i) ts = true) ∧
       (∀ i, 1 ≤ i → xorFold (fun t => termOddDeriv t i) ts = false)) := by
  rw [bijective_all_ge_two_iff (coherent_evalMaskedPoly a0 ts)]
  constructor
  · intro hall
    refine ⟨?_, ?_, ?_⟩
    · have h0 := hall 0 (0#0)
      rwa [bitDeriv_evalMaskedPoly_zero] at h0
    · intro i hi
      cases i with
      | zero => omega
      | succ k =>
        have h0 := hall (k + 1) (0#(k + 1))
        rw [bitDeriv_evalMaskedPoly_succ] at h0
        simpa using h0
    · intro i hi
      cases i with
      | zero => omega
      | succ k =>
        have h0 := hall (k + 1) (0#(k + 1))
        have h1 := hall (k + 1) (1#(k + 1))
        rw [bitDeriv_evalMaskedPoly_succ] at h0 h1
        have hlsb0 : (0#(k + 1)).getLsbD 0 = false := by simp
        have hlsb1 : (1#(k + 1)).getLsbD 0 = true := by simp
        rw [hlsb0] at h0; rw [hlsb1] at h1
        cases hl : xorFold (fun t => termLinDeriv t (k + 1)) ts <;>
        cases ho : xorFold (fun t => termOddDeriv t (k + 1)) ts <;> simp_all
  · rintro ⟨hb0, hlin, hodd⟩ i x
    cases i with
    | zero => rw [bitDeriv_evalMaskedPoly_zero]; exact hb0
    | succ k =>
      rw [bitDeriv_evalMaskedPoly_succ, hlin (k + 1) (by omega), hodd (k + 1) (by omega)]
      simp

/-- Sharp finite-slice horizon for masked polynomials: only masks of unshifted odd-degree
    odd-coefficient terms contribute! Equals `2` for all classical Rivest polynomials. -/
def maskedMaxSig : List MaskedTerm → Nat
  | [] => 1
  | t :: ts =>
    let rest := maskedMaxSig ts
    if t.shift = 0 ∧ t.deg % 2 = 1 ∧ intBit t.coeff 0 = true then
      max rest (intSigBits t.mask)
    else rest

def maskedHorizon (ts : List MaskedTerm) : Nat :=
  maskedMaxSig ts + 1

private theorem maskedMaxSig_ge_one : ∀ ts, 1 ≤ maskedMaxSig ts
  | [] => Nat.le_refl 1
  | t :: ts => by
    unfold maskedMaxSig
    split
    · exact Nat.le_trans (maskedMaxSig_ge_one ts) (Nat.le_max_left _ _)
    · exact maskedMaxSig_ge_one ts

private theorem maskedMaxSig_cons_le (t : MaskedTerm) (ts : List MaskedTerm) :
    maskedMaxSig ts ≤ maskedMaxSig (t :: ts) := by
  simp only [maskedMaxSig]
  split
  · exact Nat.le_max_left _ _
  · exact Nat.le_refl _

private theorem xorFold_lin_stable (ts : List MaskedTerm) :
    ∀ (i : Nat), maskedMaxSig ts ≤ i →
      xorFold (fun t => termLinDeriv t i) ts = xorFold (fun t => termLinDeriv t (maskedMaxSig ts)) ts := by
  induction ts with
  | nil => intro _ _; rfl
  | cons t ts ih =>
    intro i hi
    unfold xorFold
    have hts_le : maskedMaxSig ts ≤ maskedMaxSig (t :: ts) := maskedMaxSig_cons_le t ts
    rw [ih i (Nat.le_trans hts_le hi), ih (maskedMaxSig (t :: ts)) hts_le]
    congr 1
    unfold termLinDeriv
    by_cases hcond : t.shift = 0 ∧ t.deg = 1 ∧ intBit t.coeff 0 = true
    · rcases hcond with ⟨hs, hd, hc⟩
      have hodd : t.deg % 2 = 1 := by omega
      have hsig : intSigBits t.mask ≤ maskedMaxSig (t :: ts) := by
        simp only [maskedMaxSig, hs, hodd, hc, and_self, ↓reduceIte]
        exact Nat.le_max_right _ _
      simp only [hs, hd, hc, decide_true, Bool.true_and]
      rw [intBit_stable t.mask i (Nat.le_trans hsig hi), intBit_stable t.mask (maskedMaxSig (t :: ts)) hsig]
    · by_cases hs : t.shift = 0
      · by_cases hd : t.deg = 1
        · have hc : intBit t.coeff 0 = false := by
            cases h : intBit t.coeff 0
            · rfl
            · exact absurd ⟨hs, hd, h⟩ hcond
          simp [hs, hd, hc]
        · simp [hs, hd]
      · simp [hs]

private theorem xorFold_odd_stable (ts : List MaskedTerm) :
    ∀ (i : Nat), maskedMaxSig ts ≤ i →
      xorFold (fun t => termOddDeriv t i) ts = xorFold (fun t => termOddDeriv t (maskedMaxSig ts)) ts := by
  induction ts with
  | nil => intro _ _; rfl
  | cons t ts ih =>
    intro i hi
    unfold xorFold
    have hts_le : maskedMaxSig ts ≤ maskedMaxSig (t :: ts) := maskedMaxSig_cons_le t ts
    rw [ih i (Nat.le_trans hts_le hi), ih (maskedMaxSig (t :: ts)) hts_le]
    congr 1
    unfold termOddDeriv
    by_cases hcond : t.shift = 0 ∧ t.deg % 2 = 1 ∧ intBit t.coeff 0 = true
    · rcases hcond with ⟨hs, hodd, hc⟩
      have hsig : intSigBits t.mask ≤ maskedMaxSig (t :: ts) := by
        simp only [maskedMaxSig, hs, hodd, hc, and_self, ↓reduceIte]
        exact Nat.le_max_right _ _
      simp only [hs, hodd, hc, decide_true, Bool.true_and]
      rw [intBit_stable t.mask i (Nat.le_trans hsig hi), intBit_stable t.mask (maskedMaxSig (t :: ts)) hsig]
    · by_cases hs : t.shift = 0
      · by_cases hodd : t.deg % 2 = 1
        · have hc : intBit t.coeff 0 = false := by
            cases h : intBit t.coeff 0
            · rfl
            · exact absurd ⟨hs, hodd, h⟩ hcond
          simp [hs, hodd, hc]
        · simp [hs, hodd]
      · simp [hs]

/-- **Finite-Slice Cutoff Theorem for Masked Polynomials:**
    Bijectivity for all `w ≥ 2` is equivalent to bijectivity at the single finite width
    `maskedHorizon ts` (which equals `2` when all masks are `-1`, recovering Rivest 2001). -/
theorem maskedPoly_finite_slice_iff (a0 : Int) (ts : List MaskedTerm) :
    (∀ w, 2 ≤ w → Bijective (evalMaskedPoly w a0 ts)) ↔
      Bijective (evalMaskedPoly (maskedHorizon ts) a0 ts) := by
  have hge1 := maskedMaxSig_ge_one ts
  have hge2 : 2 ≤ maskedHorizon ts := by unfold maskedHorizon; omega
  constructor
  · intro hall; exact hall _ hge2
  · intro hbij
    rw [bijective_iff_forall_bitDeriv (coherent_evalMaskedPoly a0 ts)] at hbij
    rw [maskedPoly_bijective_iff]
    have h0 : xorFold termBit0Deriv ts = true := by
      have := hbij 0 (by omega) (0#0)
      rwa [bitDeriv_evalMaskedPoly_zero] at this
    have hle_lin : ∀ i, 1 ≤ i → i ≤ maskedMaxSig ts → xorFold (fun t => termLinDeriv t i) ts = true := by
      intro i hi hle
      cases i with
      | zero => omega
      | succ k =>
        have h := hbij (k + 1) (by unfold maskedHorizon; omega) (0#(k + 1))
        rw [bitDeriv_evalMaskedPoly_succ] at h
        simpa using h
    have hle_odd : ∀ i, 1 ≤ i → i ≤ maskedMaxSig ts → xorFold (fun t => termOddDeriv t i) ts = false := by
      intro i hi hle
      cases i with
      | zero => omega
      | succ k =>
        have h0' := hbij (k + 1) (by unfold maskedHorizon; omega) (0#(k + 1))
        have h1' := hbij (k + 1) (by unfold maskedHorizon; omega) (1#(k + 1))
        rw [bitDeriv_evalMaskedPoly_succ] at h0' h1'
        have hl0 : (0#(k + 1)).getLsbD 0 = false := by simp
        have hl1 : (1#(k + 1)).getLsbD 0 = true := by simp
        rw [hl0] at h0'; rw [hl1] at h1'
        cases hl : xorFold (fun t => termLinDeriv t (k + 1)) ts <;>
        cases ho : xorFold (fun t => termOddDeriv t (k + 1)) ts <;> simp_all
    refine ⟨h0, ?_, ?_⟩
    · intro i hi
      by_cases hle : i ≤ maskedMaxSig ts
      · exact hle_lin i hi hle
      · rw [xorFold_lin_stable ts i (by omega)]
        exact hle_lin (maskedMaxSig ts) hge1 (Nat.le_refl _)
    · intro i hi
      by_cases hle : i ≤ maskedMaxSig ts
      · exact hle_odd i hi hle
      · rw [xorFold_odd_stable ts i (by omega)]
        exact hle_odd (maskedMaxSig ts) hge1 (Nat.le_refl _)

theorem maskedMaxSig_classicalTerms (cs : List Int) (d : Nat) :
    maskedMaxSig (classicalTerms cs d) = 1 := by
  induction cs generalizing d with
  | nil => rfl
  | cons c rest ih =>
    simp only [classicalTerms, maskedMaxSig, ih (d + 1)]
    have hsig : intSigBits (-1) = 0 := by decide
    split <;> simp [hsig]

theorem rivest_classical_mod4_iff (a0 : Int) (cs : List Int) :
    (∀ w, 2 ≤ w → Bijective (evalMaskedPoly w a0 (classicalTerms cs 1))) ↔
      Bijective (evalMaskedPoly 2 a0 (classicalTerms cs 1)) := by
  have h := maskedPoly_finite_slice_iff a0 (classicalTerms cs 1)
  have hh : maskedHorizon (classicalTerms cs 1) = 2 := by
    simp [maskedHorizon, maskedMaxSig_classicalTerms]
  rwa [hh] at h

/-- **Sharpness Family 1 (∀ k ≥ 1):**
    `Q_k(x) = x + (x^3 &&& 2^k)` is bijective mod `2^w` for ALL `1 ≤ w ≤ k`,
    and FAILS to be bijective at `w = k + 1`! -/
def sharpCubicTerms (k : Nat) : List MaskedTerm :=
  [{ coeff := 1, deg := 1, shift := 0, mask := -1, op := .add },
   { coeff := 1, deg := 3, shift := 0, mask := Int.ofNat (2 ^ k), op := .add }]

private theorem intBit_neg_one (n : Nat) : intBit (-1) n = true := by
  have h : (-1 : Int) = Int.negSucc 0 := rfl
  rw [h]; simp [intBit]

private theorem intBit_one_zero : intBit 1 0 = true := by decide

theorem sharpCubic_bijective_below (k w : Nat) (hw : w ≤ k) :
    Bijective (evalMaskedPoly w 0 (sharpCubicTerms k)) := by
  rw [bijective_iff_forall_bitDeriv (coherent_evalMaskedPoly 0 (sharpCubicTerms k))]
  intro i hi x
  have hik : i < k := by omega
  cases i with
  | zero =>
    rw [bitDeriv_evalMaskedPoly_zero]
    have hb0 : intBit (Int.ofNat (2 ^ k)) 0 = false := by
      simp only [intBit, Nat.testBit_zero]
      have hdiv : 2 ^ k % 2 = 0 := by
        cases k with | zero => omega | succ m => rw [Nat.pow_succ]; omega
      simp [hdiv]
    simp only [sharpCubicTerms, xorFold, termBit0Deriv, hb0, intBit_neg_one, intBit_one_zero]
    simp
  | succ j =>
    rw [bitDeriv_evalMaskedPoly_succ]
    have hbj : intBit (Int.ofNat (2 ^ k)) (j + 1) = false := by
      simp only [intBit, Nat.testBit_two_pow]
      have hne : k ≠ j + 1 := by omega
      simp [hne]
    simp only [sharpCubicTerms, xorFold, termLinDeriv, termOddDeriv, hbj, intBit_neg_one, intBit_one_zero]
    cases x.getLsbD 0 <;> simp

theorem sharpCubic_not_bijective_at {k : Nat} (hk : 1 ≤ k) :
    ¬ Bijective (evalMaskedPoly (k + 1) 0 (sharpCubicTerms k)) := by
  rw [bijective_iff_forall_bitDeriv (coherent_evalMaskedPoly 0 (sharpCubicTerms k))]
  intro hall
  cases k with
  | zero => omega
  | succ m =>
    have h := hall (m + 1) (by omega) (1#(m + 1))
    rw [bitDeriv_evalMaskedPoly_succ] at h
    have hbk : intBit (Int.ofNat (2 ^ (m + 1))) (m + 1) = true := by
      simp [intBit]
    have hlsb : (1#(m + 1)).getLsbD 0 = true := by simp
    simp only [sharpCubicTerms, xorFold, termLinDeriv, termOddDeriv, hbk, intBit_neg_one, intBit_one_zero, hlsb] at h
    exact Bool.noConfusion h

theorem bitDeriv_and_add_const (c : Int) (i : Nat) (x : BitVec i) :
    bitDeriv (fun w y => y &&& (y + BitVec.ofInt w c)) i x =
      !(intBit c i ^^ decide (2 ^ i ≤ x.toNat + (BitVec.ofInt i c).toNat)) := by
  rw [bitDeriv_and, bitDeriv_add coherent_id (coherent_const c), bitDeriv_id, bitDeriv_const]
  have hvx : val0 (fun _ y => y) i x = false := by simp [val0, BitVec.msb_cons]
  have hvc : val0 (fun w y => y + BitVec.ofInt w c) i x =
      (intBit c i ^^ decide (2 ^ i ≤ x.toNat + (BitVec.ofInt i c).toNat)) := by
    unfold val0
    rw [msb_add_eq, BitVec.msb_cons, msb_ofInt_eq_intBit, setWidth_cons_eq]
    have htr : (BitVec.ofInt (i + 1) c).setWidth i = BitVec.ofInt i c := coherent_const c i (0#(i + 1))
    rw [htr]
    simp
  rw [hvx, hvc]
  cases intBit c i ^^ decide (2 ^ i ≤ x.toNat + (BitVec.ofInt i c).toNat) <;> rfl

/-- **Infinite Theorem 2 (Exact Carry-Coupled Congruence Theorem):**
    For ALL `c, d : Int` and ALL widths `w : Nat`:
    `F_{c,d}(x) = x + (x &&& (x + c)) + (x &&& (x + d))` is bijective on `BitVec w`
    IF AND ONLY IF `c ≡ d (mod 2^w)` (i.e., `BitVec.ofInt w c = BitVec.ofInt w d`)! -/
theorem carryPair_bijective_iff (c d : Int) (w : Nat) :
    Bijective ((carryPairExpr c d).eval w) ↔ BitVec.ofInt w c = BitVec.ofInt w d := by
  rw [bijective_iff_forall_bitDeriv (carryPairExpr c d).coherent w]
  constructor
  · intro hall
    -- Prove by strong induction on bit index `i < w` that `intBit c i = intBit d i`
    have hbits : ∀ i, i < w → intBit c i = intBit d i := by
      intro i
      induction i using Nat.strongRecOn with
      | ind i ih =>
        intro hi
        have hpref : BitVec.ofInt i c = BitVec.ofInt i d := by
          ext j hj
          rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem]
          rw [getLsbD_ofInt_eq_intBit i c j hj, getLsbD_ofInt_eq_intBit i d j hj]
          exact ih j hj (by omega)
        have hd := hall i hi (0#i)
        unfold carryPairExpr at hd
        change bitDeriv (fun u y => (y + (y &&& (y + BitVec.ofInt u c))) + (y &&& (y + BitVec.ofInt u d))) i (0#i) = true at hd
        have hc1 : Coherent (fun u y => y &&& (y + BitVec.ofInt u c)) :=
          coherent_and coherent_id (coherent_add coherent_id (coherent_const c))
        have hc2 : Coherent (fun u y => y &&& (y + BitVec.ofInt u d)) :=
          coherent_and coherent_id (coherent_add coherent_id (coherent_const d))
        rw [bitDeriv_add (coherent_add coherent_id hc1) hc2,
            bitDeriv_add coherent_id hc1, bitDeriv_id,
            bitDeriv_and_add_const, bitDeriv_and_add_const, hpref] at hd
        cases hci : intBit c i <;> cases hdi : intBit d i <;>
        cases decide (2 ^ i ≤ (0#i).toNat + (BitVec.ofInt i d).toNat)
        all_goals
          simp [hci, hdi] at hd ⊢
    ext i hi
    rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem]
    rw [getLsbD_ofInt_eq_intBit w c i hi, getLsbD_ofInt_eq_intBit w d i hi]
    exact hbits i hi
  · intro heq i hi x
    have hci : intBit c i = intBit d i := by
      have := congrArg (fun v => v.getLsbD i) heq
      rwa [getLsbD_ofInt_eq_intBit w c i hi, getLsbD_ofInt_eq_intBit w d i hi] at this
    have hpref : BitVec.ofInt i c = BitVec.ofInt i d := by
      have h1 := coherent_setWidth_le (coherent_const c) (by omega : i ≤ w) (0#w)
      have h2 := coherent_setWidth_le (coherent_const d) (by omega : i ≤ w) (0#w)
      rw [← h1, ← h2, heq]
    unfold carryPairExpr
    change bitDeriv (fun u y => (y + (y &&& (y + BitVec.ofInt u c))) + (y &&& (y + BitVec.ofInt u d))) i x = true
    have hc1 : Coherent (fun u y => y &&& (y + BitVec.ofInt u c)) :=
      coherent_and coherent_id (coherent_add coherent_id (coherent_const c))
    have hc2 : Coherent (fun u y => y &&& (y + BitVec.ofInt u d)) :=
      coherent_and coherent_id (coherent_add coherent_id (coherent_const d))
    rw [bitDeriv_add (coherent_add coherent_id hc1) hc2,
        bitDeriv_add coherent_id hc1, bitDeriv_id,
        bitDeriv_and_add_const, bitDeriv_and_add_const, hci, hpref]
    cases intBit d i ^^ decide (2 ^ i ≤ x.toNat + (BitVec.ofInt i d).toNat) <;> rfl

/-- **Sharp Carry-Coupled Horizon Explosion Corollary (∀ k ≥ 1):**
    `F_{1, 1 + 2^k}` is bijective on `BitVec w` for ALL `w ≤ k` and FAILS at `w = k + 1`! -/
theorem carryPair_sharp_family (k : Nat) :
    (∀ w, w ≤ k → Bijective ((carryPairExpr 1 (1 + Int.ofNat (2 ^ k))).eval w)) ∧
    ¬ Bijective ((carryPairExpr 1 (1 + Int.ofNat (2 ^ k))).eval (k + 1)) := by
  constructor
  · intro w hw
    rw [carryPair_bijective_iff]
    ext i hi
    rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem]
    rw [getLsbD_ofInt_eq_intBit w _ i hi, getLsbD_ofInt_eq_intBit w _ i hi]
    have h1 : (1 + Int.ofNat (2 ^ k)) = Int.ofNat (1 + 2 ^ k) := rfl
    rw [h1]
    simp only [intBit]
    have hpow : (1 + 2 ^ k).testBit i = (1 : Nat).testBit i := by
      have hik : i < k := by omega
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
      have hdvd : 2 ^ i ∣ 2 ^ k := ⟨2 ^ (k - i), by rw [← Nat.pow_add]; congr 1; omega⟩
      have hge1 : 1 ≤ k - i := by omega
      have heven : 2 ^ (k - i) % 2 = 0 := by
        cases hki : k - i with | zero => omega | succ m => rw [Nat.pow_succ]; omega
      have hdiv : (1 + 2 ^ k) / 2 ^ i = 1 / 2 ^ i + 2 ^ (k - i) := by
        have hpos : 0 < 2 ^ i := Nat.two_pow_pos i
        have hmul : 2 ^ k = 2 ^ i * 2 ^ (k - i) := by rw [← Nat.pow_add]; congr 1; omega
        rw [hmul, Nat.add_mul_div_left _ _ hpos]
      rw [hdiv]
      have : (1 / 2 ^ i + 2 ^ (k - i)) % 2 = (1 / 2 ^ i) % 2 := by omega
      rw [this]
    exact hpow.symm
  · rw [carryPair_bijective_iff]
    intro heq
    have hbit := congrArg (fun v => v.getLsbD k) heq
    rw [getLsbD_ofInt_eq_intBit (k + 1) _ k (by omega),
        getLsbD_ofInt_eq_intBit (k + 1) _ k (by omega)] at hbit
    have h1 : (1 + Int.ofNat (2 ^ k)) = Int.ofNat (1 + 2 ^ k) := rfl
    rw [h1] at hbit
    simp only [intBit] at hbit
    cases k with
    | zero => simp at hbit
    | succ m =>
      have h2le : 2 ≤ 2 ^ (m + 1) := by
        rw [Nat.pow_succ]; have := Nat.two_pow_pos m; omega
      have hl : (1 : Nat).testBit (m + 1) = false :=
        Nat.testBit_lt_two_pow (by omega)
      have hr : (1 + 2 ^ (m + 1)).testBit (m + 1) = true := by
        rw [Nat.testBit_eq_decide_div_mod_eq]
        have hpos : 0 < 2 ^ (m + 1) := Nat.two_pow_pos (m + 1)
        have hdiv : (1 + 2 ^ (m + 1)) / 2 ^ (m + 1) = 1 := by
          have := Nat.add_div_right 1 hpos
          rw [this, Nat.div_eq_of_lt (by omega), Nat.zero_add]
        simp [hdiv]
      rw [hl, hr] at hbit
      exact Bool.noConfusion hbit

/-- **Infinite Theorem 3A (Universal Zero-Linear-Term Complement-Bridge Bijection Family):**
    For ANY coherent T-function family `g` (even outside the finite-state transducer class!)
    and ANY bit-width `w`, `H_g(x) = (x &&& g(x)) + (~~~x ||| g(x))` is ALWAYS bijective! -/
theorem complementBridge_bijective {g : ∀ w, BitVec w → BitVec w} (hg : Coherent g) (w : Nat) :
    Bijective (fun x : BitVec w => (x &&& g w x) + (~~~x ||| g w x)) := by
  have hcoh : Coherent (fun u y => (y &&& g u y) + (~~~y ||| g u y)) :=
    coherent_add (coherent_and coherent_id hg) (coherent_or (coherent_not coherent_id) hg)
  rw [bijective_iff_forall_bitDeriv hcoh w]
  intro i _ x
  rw [bitDeriv_add (coherent_and coherent_id hg) (coherent_or (coherent_not coherent_id) hg)]
  rw [bitDeriv_and, bitDeriv_or, bitDeriv_not, bitDeriv_id]
  have hv0 : val0 (fun _ y => y) i x = false := by simp [val0, BitVec.msb_cons]
  have hvn : val0 (fun _ y => ~~~y) i x = true := by simp [val0, BitVec.msb_cons]
  rw [hv0, hvn]
  cases val0 g i x <;> cases bitDeriv g i x <;> rfl

/-- **Infinite Theorem 3B (Universal Add-XOR Carry Cancellation Law):**
    For ANY coherent `f, g` and ANY width `w`, `(f(x) + g(x)) ^^^ g(x)` is bijective
    IF AND ONLY IF `f(x)` is bijective! -/
theorem addXorCancel_bijective_iff {f g : ∀ w, BitVec w → BitVec w}
    (hf : Coherent f) (hg : Coherent g) (w : Nat) :
    Bijective (fun x : BitVec w => (f w x + g w x) ^^^ g w x) ↔ Bijective (f w) := by
  have hcoh : Coherent (fun u y => (f u y + g u y) ^^^ g u y) :=
    coherent_xor (coherent_add hf hg) hg
  rw [bijective_iff_forall_bitDeriv hcoh w, bijective_iff_forall_bitDeriv hf w]
  constructor <;> intro h i hi x
  · have := h i hi x
    rw [bitDeriv_xor, bitDeriv_add hf hg] at this
    cases hf' : bitDeriv f i x <;> cases hg' : bitDeriv g i x <;> simp_all
  · rw [bitDeriv_xor, bitDeriv_add hf hg, h i hi x]
    cases bitDeriv g i x <;> rfl

/-- **Infinite Theorem 3C (Generalized Klimov-Shamir Exact ↔ Criterion):**
    For ANY coherent T-function `g` (even wild nonlinear ones!) and ANY `c : Int`,
    `x + (g(x)^2 ||| c)` is bijective for ALL `w ≥ 2` IF AND ONLY IF
    `c` is odd OR `g(0)_0 = g(1)_0`! -/
theorem klimovShamir_general_iff {g : ∀ w, BitVec w → BitVec w} (hg : Coherent g) (c : Int) :
    (∀ w, 2 ≤ w → Bijective (fun x : BitVec w => x + ((g w x * g w x) ||| BitVec.ofInt w c))) ↔
      (intBit c 0 = true ∨ bit0Val g false = bit0Val g true) := by
  have hsq : Coherent (fun w y => g w y * g w y) := coherent_mul hg hg
  have hor : Coherent (fun w y => (g w y * g w y) ||| BitVec.ofInt w c) :=
    coherent_or hsq (coherent_const c)
  have hcoh : Coherent (fun w y => y + ((g w y * g w y) ||| BitVec.ofInt w c)) :=
    coherent_add coherent_id hor
  rw [bijective_all_ge_two_iff hcoh]
  have hge1 : ∀ (k : Nat) (x : BitVec (k + 1)),
      bitDeriv (fun w y => y + ((g w y * g w y) ||| BitVec.ofInt w c)) (k + 1) x = true := by
    intro k x
    rw [bitDeriv_add coherent_id hor, bitDeriv_id, bitDeriv_or, bitDeriv_const,
        bitDeriv_mul_succ hg hg k x]
    cases bit0Val g (x.getLsbD 0) <;> cases bitDeriv g (k + 1) x <;>
    cases val0 (fun w y => g w y * g w y) (k + 1) x <;>
    cases val0 (fun w _ => BitVec.ofInt w c) (k + 1) x <;> rfl
  have h0_iff : bitDeriv (fun w y => y + ((g w y * g w y) ||| BitVec.ofInt w c)) 0 (0#0) = true ↔
      (intBit c 0 = true ∨ bit0Val g false = bit0Val g true) := by
    rw [bitDeriv_add coherent_id hor, bitDeriv_id]
    unfold bitDeriv bit0Val
    have hmul1 : ∀ u : BitVec 1, (u * u).msb = u.msb := by
      intro u
      have hu : u = BitVec.cons u.msb (0#0) := by
        have := cons_msb_setWidth u; simpa [Subsingleton.elim (u.setWidth 0) (0#0)] using this.symm
      rw [hu]; cases u.msb <;> decide
    simp only [BitVec.msb_or, msb_ofInt_eq_intBit, hmul1]
    cases (g 1 (BitVec.cons true (0#0))).msb <;>
    cases (g 1 (BitVec.cons false (0#0))).msb <;>
    cases intBit c 0 <;> decide
  constructor
  · intro hall; exact h0_iff.1 (hall 0 (0#0))
  · intro hcond i x
    cases i with
    | zero =>
      have hx : x = 0#0 := Subsingleton.elim x (0#0)
      subst hx; exact h0_iff.2 hcond
    | succ k => exact hge1 k x

-- ============================================================================
-- Section 7: Kernel-Checked BSDA Engine Instantiations (Pure `decide`!),
--            Non-Vacuity Witnesses, Sharp Outside-BSDA Boundary, & Axiom Audit
-- ============================================================================

def exX  : MixedExpr := .var
def exX2 : MixedExpr := .mul .var .var
def exX3 : MixedExpr := .mul exX2 .var
def exX5 : MixedExpr := .mul exX3 exX2

/-- 1. Classical Rivest cubic: `x + 2x^2 + 2x^3` (BSDA computes exact `horizonW = 2`!). -/
def exRivest : MixedExpr :=
  .add (.add exX (.mul (.const 2) exX2)) (.mul (.const 2) exX3)

theorem exRivest_horizon : (compileBSDA exRivest).map DerivAuto.horizonW = some 2 := by decide
theorem exRivest_bijective : ∀ w, 2 ≤ w → Bijective (exRivest.eval w) :=
  bsda_decide_bijective exRivest (by decide)

/-- 2. Klimov-Shamir nonlinear T-function: `x + (x^2 | 5)` (`horizonW = 2`). -/
def exKlimovShamir : MixedExpr := .add exX (.or exX2 (.const 5))

theorem exKlimovShamir_bijective : ∀ w, 2 ≤ w → Bijective (exKlimovShamir.eval w) :=
  bsda_decide_bijective exKlimovShamir (by decide)

/-- 3. Signed/unsigned bitwise-masked Rivest quintic:
    `(x & -2) + (x^2 & 1) + (x^3 & 8) + (x^5 & 8)`. -/
def exMaskedRivest : MixedExpr :=
  .add (.add (.add (.and exX (.const (-2))) (.and exX2 (.const 1)))
             (.and exX3 (.const 8)))
       (.and exX5 (.const 8))

theorem exMaskedRivest_bijective : ∀ w, 2 ≤ w → Bijective (exMaskedRivest.eval w) :=
  bsda_decide_bijective exMaskedRivest (by decide)

/-- 4. Carry-gated nonlinear mixed quintic: `x + (((x + 1) << 1) & (x^3 + x^5))`. -/
def exCarryGatedQuintic : MixedExpr :=
  .add exX (.and (.shl 1 (.add exX (.const 1))) (.add exX3 exX5))

theorem exCarryGatedQuintic_bijective : ∀ w, 2 ≤ w → Bijective (exCarryGatedQuintic.eval w) :=
  bsda_decide_bijective exCarryGatedQuintic (by decide)

/-- 5. Zero-linear-term carry-complement bijection: `(x & (x + 1)) + (~x | (x + 1))`. -/
def exZeroLinear : MixedExpr :=
  .add (.and exX (.add exX (.const 1))) (.or (.not exX) (.add exX (.const 1)))

theorem exZeroLinear_bijective : ∀ w, 2 ≤ w → Bijective (exZeroLinear.eval w) :=
  bsda_decide_bijective exZeroLinear (by decide)

/-- 6. Full-spectrum mixed polynomial combining `+`, `-`, `*`, `^`, `&`, `|`, `<<`, carries, & deg 5:
    `((x ^ (x << 1)) + (x^2 | 5)) - ((x ^ (x + 1)) & (x^3 ^ x^5))`. -/
def exFullSpectrum : MixedExpr :=
  .sub (.add (.xor exX (.shl 1 exX)) (.or exX2 (.const 5)))
       (.and (.xor exX (.add exX (.const 1))) (.xor exX3 exX5))

theorem exFullSpectrum_bijective : ∀ w, 2 ≤ w → Bijective (exFullSpectrum.eval w) :=
  bsda_decide_bijective exFullSpectrum (by decide)

-- Kernel-checked negative / mutation tests (refuting non-bijective mixed polynomials!)
def negRivest : MixedExpr := .add (.add exX exX2) exX3
def negCarryGated : MixedExpr := .add exX (.and (.shl 1 (.add exX (.const 1))) exX3)
def negKlimovEven : MixedExpr := .add exX (.or exX2 (.const 4))
def negCarryPair17 : MixedExpr := carryPairExpr 1 17

theorem negRivest_not_bijective : ¬ (∀ w, 2 ≤ w → Bijective (negRivest.eval w)) :=
  bsda_decide_not_bijective negRivest (by decide)

theorem negCarryGated_not_bijective : ¬ (∀ w, 2 ≤ w → Bijective (negCarryGated.eval w)) :=
  bsda_decide_not_bijective negCarryGated (by decide)

theorem negKlimovEven_not_bijective : ¬ (∀ w, 2 ≤ w → Bijective (negKlimovEven.eval w)) :=
  bsda_decide_not_bijective negKlimovEven (by decide)

theorem negCarryPair17_not_bijective : ¬ (∀ w, 2 ≤ w → Bijective (negCarryPair17.eval w)) :=
  bsda_decide_not_bijective negCarryPair17 (by decide)

-- Kernel-checked non-vacuity witnesses (proving our certified bijections are genuinely non-trivial!)
example : exZeroLinear.eval 3 (0#3) = 7#3 ∧ exZeroLinear.eval 3 (2#3) = 1#3 := by decide
example : exFullSpectrum.eval 4 (0#4) = 5#4 ∧ exFullSpectrum.eval 4 (3#4) = 2#4 := by decide
example : exMaskedRivest.eval 4 (3#4) = 11#4 ∧ exMaskedRivest.eval 4 (1#4) = 1#4 := by decide

-- Sharp outside-BSDA boundary witness: `B(x) = x + (x^2 & (x ^ 1))`
-- Lies OUTSIDE the BSDA fragment (nonlinear square's bit value multiplies a nonzero derivative),
-- is bijective mod 2 and mod 4, and FIRST FAILS mod 8 (`B(2) = B(6) = 2 mod 8`)!
def boundaryExpr : MixedExpr :=
  .add exX (.and exX2 (.xor exX (.const 1)))

theorem boundaryExpr_outside_bsda : compileBSDA boundaryExpr = none := by decide

theorem boundaryExpr_bijective_mod2 : Bijective (boundaryExpr.eval 1) := by
  rw [bijective_iff_forall_bitDeriv boundaryExpr.coherent 1]
  intro i hi x
  have hi0 : i = 0 := by omega
  subst hi0
  have hx : x = 0#0 := Subsingleton.elim x (0#0)
  subst hx
  decide

theorem boundaryExpr_bijective_mod4 : Bijective (boundaryExpr.eval 2) := by
  rw [bijective_iff_forall_bitDeriv boundaryExpr.coherent 2]
  intro i hi x
  match i with
  | 0 =>
    have hx : x = 0#0 := Subsingleton.elim x (0#0)
    subst hx; decide
  | 1 =>
    have hx : x = 0#1 ∨ x = 1#1 := by
      have := x.isLt
      rcases (show x.toNat = 0 ∨ x.toNat = 1 by omega) with h | h
      · left; exact BitVec.eq_of_toNat_eq h
      · right; exact BitVec.eq_of_toNat_eq h
    rcases hx with rfl | rfl <;> decide
  | i + 2 => omega

theorem boundaryExpr_not_bijective_mod8 : ¬ Bijective (boundaryExpr.eval 3) := by
  intro ⟨hinj, _⟩
  have hcol : boundaryExpr.eval 3 (2#3) = boundaryExpr.eval 3 (6#3) := by decide
  have heq := hinj (2#3) (6#3) hcol
  exact absurd heq (by decide)

end MixedPermEngine

-- ============================================================================
-- Exhaustive Axiom Audit (Must be ⊆ {propext, Classical.choice, Quot.sound})
-- ============================================================================


