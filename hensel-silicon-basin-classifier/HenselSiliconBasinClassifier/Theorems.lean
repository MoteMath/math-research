/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HenselSiliconBasinClassifier.Defs

/-!
# Theorems (`hensel-silicon-basin-classifier`)

Full proofs of the headline infinite theorems of 2-Adic Hensel-Contraction Fixed-Point and Basin Classifier.
-/

namespace HenselSilicon

theorem iter_zero {α : Type} (f : α → α) (x : α) : iter f 0 x = x := rfl

theorem iter_succ {α : Type} (f : α → α) (n : Nat) (x : α) :
    iter f (n + 1) x = f (iter f n x) := rfl

theorem iter_succ_apply {α : Type} (f : α → α) (n : Nat) (x : α) :
    iter f (n + 1) x = iter f n (f x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iter_succ, ih, iter_succ]

theorem iter_add {α : Type} (f : α → α) (a b : Nat) (x : α) :
    iter f (a + b) x = iter f a (iter f b x) := by
  induction a with
  | zero => rw [Nat.zero_add]; rfl
  | succ a ih =>
    rw [Nat.succ_add, iter_succ, ih, iter_succ]

theorem iter_mul {α : Type} (f : α → α) (q L : Nat) (x : α) :
    iter (iter f L) q x = iter f (q * L) x := by
  induction q with
  | zero => rw [Nat.zero_mul]; rfl
  | succ q ih =>
    rw [iter_succ, ih, Nat.succ_mul, Nat.add_comm, iter_add]

theorem iter_fixed {α : Type} {f : α → α} {x : α} (h : f x = x) :
    ∀ n : Nat, iter f n x = x
  | 0 => rfl
  | n + 1 => by rw [iter_succ, iter_fixed h n, h]

theorem setWidth_eq_iff {w k : Nat} (x y : BitVec w) :
    BitVec.setWidth k x = BitVec.setWidth k y ↔
      ∀ i, i < k → x.getLsbD i = y.getLsbD i := by
  constructor
  · intro h i hi
    have hbit := congrArg (fun v => v.getLsbD i) h
    rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth] at hbit
    simp only [hi, decide_true, Bool.true_and] at hbit
    exact hbit
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth]
    simp only [hi, decide_true, Bool.true_and]
    exact h i hi

theorem setWidth_eq_of_le {w k l : Nat} (hkl : k ≤ l) {x y : BitVec w}
    (h : BitVec.setWidth l x = BitVec.setWidth l y) :
    BitVec.setWidth k x = BitVec.setWidth k y := by
  have := congrArg (BitVec.setWidth k) h
  simpa [BitVec.setWidth_setWidth_of_le _ hkl] using this

theorem setWidth_succ_of_eq_bit {w k : Nat} {x y : BitVec w}
    (hlo : BitVec.setWidth k x = BitVec.setWidth k y)
    (hbit : x.getLsbD k = y.getLsbD k) :
    BitVec.setWidth (k + 1) x = BitVec.setWidth (k + 1) y := by
  rw [setWidth_eq_iff]
  intro i hi
  by_cases hik : i < k
  · exact (setWidth_eq_iff x y).mp hlo i hik
  · have heq : i = k := by omega
    subst heq
    exact hbit

theorem setWidth_self_eq {w : Nat} (x : BitVec w) : BitVec.setWidth w x = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_setWidth]
  simp only [hi, decide_true, Bool.true_and]

theorem setWidth_ofNat_le {w k : Nat} (hk : k ≤ w) (c : Nat) :
    BitVec.setWidth k (BitVec.ofNat w c) = BitVec.ofNat k c := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat, BitVec.getLsbD_ofNat]
  have hiw : i < w := Nat.lt_of_lt_of_le hi hk
  simp only [hi, hiw, decide_true, Bool.true_and]

theorem setWidth_sub_le {w k : Nat} (hk : k ≤ w) (x y : BitVec w) :
    BitVec.setWidth k (x - y) = BitVec.setWidth k x - BitVec.setWidth k y := by
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg,
      BitVec.neg_eq_not_add, BitVec.neg_eq_not_add,
      BitVec.setWidth_add _ _ hk, BitVec.setWidth_add _ _ hk,
      BitVec.setWidth_not hk, setWidth_ofNat_le hk 1]

theorem setWidth_shiftLeft_le {w k : Nat} (hk : k ≤ w) (x : BitVec w) (s : Nat) :
    BitVec.setWidth k (x <<< s) = (BitVec.setWidth k x) <<< s := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hiw : i < w := Nat.lt_of_lt_of_le hi hk
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth]
  by_cases his : i < s
  · simp only [hi, hiw, his, decide_true, Bool.not_true, Bool.and_false, Bool.false_and]
  · have hsub : i - s < k := by omega
    simp only [hi, hiw, his, hsub, decide_true, decide_false, Bool.not_false,
      Bool.true_and, Bool.and_true]

theorem carry_zero_eq {w : Nat} (a b : BitVec w) (c : Bool) :
    BitVec.carry 0 a b c = c := by
  cases c <;> simp [BitVec.carry, Nat.mod_one]

theorem carry_congr {w k : Nat} {a₁ a₂ b₁ b₂ : BitVec w} (c : Bool)
    (ha : BitVec.setWidth k a₁ = BitVec.setWidth k a₂)
    (hb : BitVec.setWidth k b₁ = BitVec.setWidth k b₂) :
    BitVec.carry k a₁ b₁ c = BitVec.carry k a₂ b₂ c := by
  induction k with
  | zero => rw [carry_zero_eq, carry_zero_eq]
  | succ k ih =>
    have ha' := setWidth_eq_of_le (Nat.le_succ k) ha
    have hb' := setWidth_eq_of_le (Nat.le_succ k) hb
    have hba : a₁.getLsbD k = a₂.getLsbD k :=
      (setWidth_eq_iff a₁ a₂).mp ha k (Nat.lt_succ_self k)
    have hbb : b₁.getLsbD k = b₂.getLsbD k :=
      (setWidth_eq_iff b₁ b₂).mp hb k (Nat.lt_succ_self k)
    rw [BitVec.carry_succ, BitVec.carry_succ, hba, hbb, ih ha' hb']

theorem getLsbD_add_xor_diff {w k : Nat} (hk : k < w) {a₁ a₂ b₁ b₂ : BitVec w}
    (ha : BitVec.setWidth k a₁ = BitVec.setWidth k a₂)
    (hb : BitVec.setWidth k b₁ = BitVec.setWidth k b₂) :
    ((a₁ + b₁).getLsbD k ^^ (a₂ + b₂).getLsbD k) =
      ((a₁.getLsbD k ^^ a₂.getLsbD k) ^^ (b₁.getLsbD k ^^ b₂.getLsbD k)) := by
  rw [BitVec.getLsbD_add hk, BitVec.getLsbD_add hk]
  have hc := carry_congr false ha hb
  rw [hc]
  cases a₁.getLsbD k <;> cases a₂.getLsbD k <;> cases b₁.getLsbD k <;>
    cases b₂.getLsbD k <;> cases BitVec.carry k a₂ b₂ false <;> rfl

theorem getLsbD_neg_xor_diff {w k : Nat} (hk : k < w) {b₁ b₂ : BitVec w}
    (hb : BitVec.setWidth k b₁ = BitVec.setWidth k b₂) :
    ((-b₁).getLsbD k ^^ (-b₂).getLsbD k) = (b₁.getLsbD k ^^ b₂.getLsbD k) := by
  rw [BitVec.neg_eq_not_add, BitVec.neg_eq_not_add]
  have hnot : BitVec.setWidth k (~~~b₁) = BitVec.setWidth k (~~~b₂) := by
    rw [BitVec.setWidth_not (Nat.le_of_lt hk), BitVec.setWidth_not (Nat.le_of_lt hk), hb]
  rw [getLsbD_add_xor_diff hk hnot rfl, BitVec.getLsbD_not, BitVec.getLsbD_not]
  simp only [hk, decide_true, Bool.true_and, Bool.xor_self, Bool.xor_false]
  cases b₁.getLsbD k <;> cases b₂.getLsbD k <;> rfl

theorem getLsbD_sub_xor_diff {w k : Nat} (hk : k < w) {a₁ a₂ b₁ b₂ : BitVec w}
    (ha : BitVec.setWidth k a₁ = BitVec.setWidth k a₂)
    (hb : BitVec.setWidth k b₁ = BitVec.setWidth k b₂) :
    ((a₁ - b₁).getLsbD k ^^ (a₂ - b₂).getLsbD k) =
      ((a₁.getLsbD k ^^ a₂.getLsbD k) ^^ (b₁.getLsbD k ^^ b₂.getLsbD k)) := by
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg]
  have hneg : BitVec.setWidth k (-b₁) = BitVec.setWidth k (-b₂) := by
    rw [BitVec.neg_eq_not_add, BitVec.neg_eq_not_add,
        BitVec.setWidth_add _ _ (Nat.le_of_lt hk),
        BitVec.setWidth_add _ _ (Nat.le_of_lt hk),
        BitVec.setWidth_not (Nat.le_of_lt hk),
        BitVec.setWidth_not (Nat.le_of_lt hk), hb]
  rw [getLsbD_add_xor_diff hk ha hneg, getLsbD_neg_xor_diff hk hb]

/-! ### Exact 2-Adic Leibniz Product Rule for `BitVec` Multiplication (`1 ≤ k < w`) -/

theorem nat_div_two_pow_mod_two (n k : Nat) :
    ((n / 2 ^ k) % 2 == 1) = n.testBit k := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_comm, Nat.and_one_is_mod]
  cases Nat.mod_two_eq_zero_or_one (n / 2 ^ k) with
  | inl h => simp [h]
  | inr h => simp [h]

theorem nat_mod_two_pow_succ (n k : Nat) :
    n % 2 ^ (k + 1) = n % 2 ^ k + (n.testBit k).toNat * 2 ^ k := by
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
  have hq : (n % (2 ^ k * 2)) / 2 ^ k = (n / 2 ^ k) % 2 := Nat.mod_mul_right_div_self n (2 ^ k) 2
  have hrem : (n % (2 ^ k * 2)) % 2 ^ k = n % 2 ^ k :=
    Nat.mod_mod_of_dvd n ⟨2, rfl⟩
  have hdm := Nat.div_add_mod (n % (2 ^ k * 2)) (2 ^ k)
  rw [hq, hrem] at hdm
  have hbit := nat_div_two_pow_mod_two n k
  have hEq : (n / 2 ^ k) % 2 = (n.testBit k).toNat := by
    cases h : n.testBit k with
    | false =>
      rw [h] at hbit
      have hne : (n / 2 ^ k) % 2 ≠ 1 := by simpa using hbit
      have hlt := Nat.mod_lt (n / 2 ^ k) (by omega : 0 < 2)
      change (n / 2 ^ k) % 2 = 0
      omega
    | true =>
      rw [h] at hbit
      simpa using hbit
  rw [hpow, ← hdm, hEq, Nat.mul_comm, Nat.add_comm]

theorem nat_mul_bit_decomp (a b k : Nat) (hk : 1 ≤ k) :
    (a * b).testBit k =
      (((a % 2 ^ k) * (b % 2 ^ k)).testBit k ^^
       ((a.testBit 0 && b.testBit k) ^^ (b.testBit 0 && a.testBit k))) := by
  have h2k : 2 ^ (k + 1) ∣ 2 ^ k * 2 ^ k := by
    have hk1 : k + 1 ≤ k + k := by omega
    rw [← Nat.pow_add]
    exact Nat.pow_dvd_pow 2 hk1
  have hmod : (a * b) % 2 ^ (k + 1) =
      ((a % 2 ^ (k + 1)) * (b % 2 ^ (k + 1))) % 2 ^ (k + 1) := Nat.mul_mod a b (2 ^ (k + 1))
  have ha := nat_mod_two_pow_succ a k
  have hb := nat_mod_two_pow_succ b k
  let r := a % 2 ^ k
  let s := b % 2 ^ k
  let da := (a.testBit k).toNat
  let db := (b.testBit k).toNat
  have hexp : (r + da * 2 ^ k) * (s + db * 2 ^ k) =
      r * s + (r * db + s * da) * 2 ^ k + (da * db) * (2 ^ k * 2 ^ k) := by
    have h1 : (r + da * 2 ^ k) * (s + db * 2 ^ k) =
        r * s + (r * (db * 2 ^ k) + da * 2 ^ k * s) + da * 2 ^ k * (db * 2 ^ k) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.add_assoc, ← Nat.add_assoc (r * (db * 2 ^ k)),
          ← Nat.add_assoc (r * s)]
    have h2 : r * (db * 2 ^ k) + da * 2 ^ k * s = (r * db + s * da) * 2 ^ k := by
      rw [Nat.add_mul, ← Nat.mul_assoc, Nat.mul_right_comm da (2 ^ k) s, Nat.mul_comm da s]
    have h3 : da * 2 ^ k * (db * 2 ^ k) = (da * db) * (2 ^ k * 2 ^ k) := by
      rw [Nat.mul_assoc, Nat.mul_left_comm (2 ^ k) db (2 ^ k), ← Nat.mul_assoc]
    rw [h1, h2, h3]
  have hmod2 : (a * b) % 2 ^ (k + 1) =
      (r * s + (r * db + s * da) * 2 ^ k) % 2 ^ (k + 1) := by
    rw [hmod, ha, hb]
    change ((r + da * 2 ^ k) * (s + db * 2 ^ k)) % 2 ^ (k + 1) = _
    rw [hexp]
    rcases h2k with ⟨t, ht⟩
    rw [ht, ← Nat.mul_assoc, Nat.mul_comm (da * db) (2 ^ (k + 1)),
        Nat.mul_assoc (2 ^ (k + 1)), Nat.add_mul_mod_self_left]
  have htb : (a * b).testBit k = ((r * s + (r * db + s * da) * 2 ^ k)).testBit k := by
    have hlt : k < k + 1 := Nat.lt_succ_self k
    have h1 := Nat.testBit_mod_two_pow (a * b) (k + 1) k
    have h2 := Nat.testBit_mod_two_pow (r * s + (r * db + s * da) * 2 ^ k) (k + 1) k
    rw [hmod2] at h1
    simp only [hlt, decide_true, Bool.true_and] at h1 h2
    rw [← h1, h2]
  rw [htb, ← nat_div_two_pow_mod_two, Nat.add_mul_div_right _ _ (Nat.two_pow_pos k),
      ← nat_div_two_pow_mod_two]
  have hr0 : r % 2 = (a.testBit 0).toNat := by
    have h2 : 2 ∣ 2 ^ k := by simpa using Nat.pow_dvd_pow 2 hk
    have hrm : r % 2 = a % 2 := Nat.mod_mod_of_dvd a h2
    rw [hrm]
    have h0 := nat_div_two_pow_mod_two a 0
    simp only [Nat.pow_zero, Nat.div_one] at h0
    cases h : a.testBit 0 with
    | false =>
      rw [h] at h0
      have hne : a % 2 ≠ 1 := by simpa using h0
      have hlt := Nat.mod_lt a (by omega : 0 < 2)
      change a % 2 = 0; omega
    | true =>
      rw [h] at h0
      simpa using h0
  have hs0 : s % 2 = (b.testBit 0).toNat := by
    have h2 : 2 ∣ 2 ^ k := by simpa using Nat.pow_dvd_pow 2 hk
    have hsm : s % 2 = b % 2 := Nat.mod_mod_of_dvd b h2
    rw [hsm]
    have h0 := nat_div_two_pow_mod_two b 0
    simp only [Nat.pow_zero, Nat.div_one] at h0
    cases h : b.testBit 0 with
    | false =>
      rw [h] at h0
      have hne : b % 2 ≠ 1 := by simpa using h0
      have hlt := Nat.mod_lt b (by omega : 0 < 2)
      change b % 2 = 0; omega
    | true =>
      rw [h] at h0
      simpa using h0
  have hmod_add : (r * s / 2 ^ k + (r * db + s * da)) % 2 =
      ((r * s / 2 ^ k) % 2 + ((r % 2) * db + (s % 2) * da)) % 2 := by
    have hinner : (r * db + s * da) % 2 = ((r % 2) * db + (s % 2) * da) % 2 := by
      rw [Nat.add_mod, Nat.mul_mod r db, Nat.mul_mod s da,
          Nat.add_mod ((r % 2) * db), Nat.mul_mod (r % 2) db, Nat.mul_mod (s % 2) da,
          Nat.mod_mod, Nat.mod_mod]
    rw [Nat.add_mod, hinner, ← Nat.add_mod, Nat.add_mod ((r * s / 2 ^ k) % 2), Nat.mod_mod,
        ← Nat.add_mod]
  rw [hmod_add, hr0, hs0]
  change (((r * s / 2 ^ k) % 2 + ((a.testBit 0).toNat * (b.testBit k).toNat +
      (b.testBit 0).toNat * (a.testBit k).toNat)) % 2 == 1) =
    (((r * s / 2 ^ k) % 2 == 1) ^^
      ((a.testBit 0 && b.testBit k) ^^ (b.testBit 0 && a.testBit k)))
  cases Nat.mod_two_eq_zero_or_one (r * s / 2 ^ k) with
  | inl h =>
    rw [h]
    cases a.testBit 0 <;> cases b.testBit 0 <;> cases a.testBit k <;> cases b.testBit k <;> rfl
  | inr h =>
    rw [h]
    cases a.testBit 0 <;> cases b.testBit 0 <;> cases a.testBit k <;> cases b.testBit k <;> rfl

theorem getLsbD_mul_xor_diff {w k : Nat} (hk1 : 1 ≤ k) (hkw : k < w)
    {a₁ a₂ b₁ b₂ : BitVec w}
    (ha : BitVec.setWidth k a₁ = BitVec.setWidth k a₂)
    (hb : BitVec.setWidth k b₁ = BitVec.setWidth k b₂) :
    ((a₁ * b₁).getLsbD k ^^ (a₂ * b₂).getLsbD k) =
      ((a₁.getLsbD 0 && (b₁.getLsbD k ^^ b₂.getLsbD k)) ^^
       (b₁.getLsbD 0 && (a₁.getLsbD k ^^ a₂.getLsbD k))) := by
  have haMod : a₁.toNat % 2 ^ k = a₂.toNat % 2 ^ k := by
    have := congrArg BitVec.toNat ha
    simpa [BitVec.toNat_setWidth] using this
  have hbMod : b₁.toNat % 2 ^ k = b₂.toNat % 2 ^ k := by
    have := congrArg BitVec.toNat hb
    simpa [BitVec.toNat_setWidth] using this
  have ha0 : a₁.getLsbD 0 = a₂.getLsbD 0 :=
    (setWidth_eq_iff a₁ a₂).mp ha 0 hk1
  have hb0 : b₁.getLsbD 0 = b₂.getLsbD 0 :=
    (setWidth_eq_iff b₁ b₂).mp hb 0 hk1
  have hbit : ∀ (x y : BitVec w), (x * y).getLsbD k = (x.toNat * y.toNat).testBit k := by
    intro x y
    rw [BitVec.getLsbD, BitVec.toNat_mul, Nat.testBit_mod_two_pow]
    simp only [hkw, decide_true, Bool.true_and]
  rw [hbit a₁ b₁, hbit a₂ b₂,
      nat_mul_bit_decomp a₁.toNat b₁.toNat k hk1,
      nat_mul_bit_decomp a₂.toNat b₂.toNat k hk1,
      haMod, hbMod]
  have hget : ∀ (x : BitVec w) (i : Nat), x.toNat.testBit i = x.getLsbD i := fun _ _ => rfl
  rw [hget, hget, hget, hget, hget, hget, hget, hget, ← ha0, ← hb0]
  cases ((a₂.toNat % 2 ^ k) * (b₂.toNat % 2 ^ k)).testBit k <;>
    cases a₁.getLsbD 0 <;> cases b₁.getLsbD 0 <;>
    cases a₁.getLsbD k <;> cases a₂.getLsbD k <;>
    cases b₁.getLsbD k <;> cases b₂.getLsbD k <;> rfl

/-! ### Exact Carryless Multiplication (`bvClmul`) & Its Leibniz Rule -/

theorem getLsbD_bvClmulAux_succ {w : Nat} (a b : BitVec w) (i k : Nat) (hk : k < w) :
    (bvClmulAux a b (i + 1)).getLsbD k =
      ((bvClmulAux a b i).getLsbD k ^^
       (if i ≤ k then (b.getLsbD i && a.getLsbD (k - i)) else false)) := by
  simp only [bvClmulAux]
  split
  · rename_i hbi
    rw [BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft]
    by_cases hik : i ≤ k
    · have hnot : ¬(k < i) := by omega
      simp only [hk, hik, hnot, hbi, decide_true, decide_false, Bool.not_false,
        Bool.true_and, ite_true]
    · have hlt : k < i := by omega
      simp only [hk, hik, hlt, decide_true, Bool.not_true, Bool.and_false,
        Bool.false_and, ite_false]
  · rename_i hbi
    have hbf : b.getLsbD i = false := by cases h : b.getLsbD i <;> simp_all
    by_cases hik : i ≤ k
    · simp only [hik, hbf, Bool.false_and, ite_true, Bool.bne_false]
    · simp only [hik, ite_false, Bool.bne_false]

theorem getLsbD_bvClmulAux_ge {w : Nat} (a b : BitVec w) {n k : Nat}
    (hk : k < w) (hkn : k + 1 ≤ n) :
    (bvClmulAux a b n).getLsbD k = (bvClmulAux a b (k + 1)).getLsbD k := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases heq : n = k
    · subst heq; rfl
    · have hle : k + 1 ≤ n := by omega
      have hgt : ¬(n ≤ k) := by omega
      rw [getLsbD_bvClmulAux_succ a b n k hk]
      simp only [hgt, ite_false, Bool.bne_false, ih hle]

theorem getLsbD_bvClmul {w : Nat} (a b : BitVec w) {k : Nat} (hk : k < w) :
    (bvClmul a b).getLsbD k = (bvClmulAux a b (k + 1)).getLsbD k :=
  getLsbD_bvClmulAux_ge a b hk (Nat.succ_le_of_lt hk)

theorem setWidth_bvClmul {w k : Nat} (hk : k ≤ w) (a b : BitVec w) :
    BitVec.setWidth k (bvClmul a b) =
      bvClmul (BitVec.setWidth k a) (BitVec.setWidth k b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hjw : j < w := Nat.lt_of_lt_of_le hj hk
  rw [BitVec.getLsbD_setWidth]
  simp only [hj, decide_true, Bool.true_and]
  rw [getLsbD_bvClmul a b hjw, getLsbD_bvClmul _ _ hj]
  suffices ∀ n, n ≤ j + 1 →
      (bvClmulAux a b n).getLsbD j =
      (bvClmulAux (BitVec.setWidth k a) (BitVec.setWidth k b) n).getLsbD j by
    exact this (j + 1) (Nat.le_refl _)
  intro n hn
  induction n with
  | zero =>
    rw [bvClmulAux, bvClmulAux]
    simp only [BitVec.getLsbD_zero]
  | succ n ih =>
    rw [getLsbD_bvClmulAux_succ a b n j hjw,
        getLsbD_bvClmulAux_succ _ _ n j hj,
        ih (Nat.le_of_succ_le hn)]
    have hnj : n ≤ j := by omega
    have hnk : n < k := by omega
    have hsub : j - n < k := by omega
    simp only [hnj, ite_true, BitVec.getLsbD_setWidth, hnk, hsub, decide_true, Bool.true_and]

theorem getLsbD_bvClmul_xor_diff {w k : Nat} (hk1 : 1 ≤ k) (hkw : k < w)
    {a₁ a₂ b₁ b₂ : BitVec w}
    (ha : BitVec.setWidth k a₁ = BitVec.setWidth k a₂)
    (hb : BitVec.setWidth k b₁ = BitVec.setWidth k b₂) :
    ((bvClmul a₁ b₁).getLsbD k ^^ (bvClmul a₂ b₂).getLsbD k) =
      ((a₁.getLsbD 0 && (b₁.getLsbD k ^^ b₂.getLsbD k)) ^^
       (b₁.getLsbD 0 && (a₁.getLsbD k ^^ a₂.getLsbD k))) := by
  rw [getLsbD_bvClmul a₁ b₁ hkw, getLsbD_bvClmul a₂ b₂ hkw]
  rw [getLsbD_bvClmulAux_succ a₁ b₁ k k hkw, getLsbD_bvClmulAux_succ a₂ b₂ k k hkw]
  simp only [Nat.le_refl, ite_true, Nat.sub_self]
  have ha0 : a₁.getLsbD 0 = a₂.getLsbD 0 := (setWidth_eq_iff a₁ a₂).mp ha 0 hk1
  have hb0 : b₁.getLsbD 0 = b₂.getLsbD 0 := (setWidth_eq_iff b₁ b₂).mp hb 0 hk1
  have hmid : ∀ n, 1 ≤ n → n ≤ k →
      ((bvClmulAux a₁ b₁ n).getLsbD k ^^ (bvClmulAux a₂ b₂ n).getLsbD k) =
      (b₁.getLsbD 0 && (a₁.getLsbD k ^^ a₂.getLsbD k)) := by
    intro n hn1 hnk
    induction n with
    | zero => omega
    | succ n ih =>
      by_cases hn0 : n = 0
      · subst hn0
        rw [getLsbD_bvClmulAux_succ a₁ b₁ 0 k hkw,
            getLsbD_bvClmulAux_succ a₂ b₂ 0 k hkw]
        simp only [bvClmulAux, BitVec.getLsbD_zero, Nat.zero_le, ite_true, Nat.sub_zero,
          Bool.false_bne, ← hb0]
        cases b₁.getLsbD 0 <;> cases a₁.getLsbD k <;> cases a₂.getLsbD k <;> rfl
      · have hn_pos : 1 ≤ n := by omega
        have hn_lt : n < k := by omega
        have hkn_lt : k - n < k := by omega
        have hbi : b₁.getLsbD n = b₂.getLsbD n := (setWidth_eq_iff b₁ b₂).mp hb n hn_lt
        have hai : a₁.getLsbD (k - n) = a₂.getLsbD (k - n) :=
          (setWidth_eq_iff a₁ a₂).mp ha (k - n) hkn_lt
        rw [getLsbD_bvClmulAux_succ a₁ b₁ n k hkw,
            getLsbD_bvClmulAux_succ a₂ b₂ n k hkw]
        simp only [Nat.le_of_lt hn_lt, ite_true, hbi, hai]
        have hprev := ih hn_pos (Nat.le_of_lt hn_lt)
        generalize (bvClmulAux a₁ b₁ n).getLsbD k = p₁ at hprev ⊢
        generalize (bvClmulAux a₂ b₂ n).getLsbD k = p₂ at hprev ⊢
        generalize (b₂.getLsbD n && a₂.getLsbD (k - n)) = q
        rw [← hprev]
        cases p₁ <;> cases p₂ <;> cases q <;> rfl
  have hm := hmid k hk1 (Nat.le_refl k)
  rw [← ha0]
  generalize (bvClmulAux a₁ b₁ k).getLsbD k = u₁ at hm ⊢
  generalize (bvClmulAux a₂ b₂ k).getLsbD k = u₂ at hm ⊢
  generalize a₁.getLsbD 0 = a0
  generalize b₁.getLsbD 0 = b0 at hm ⊢
  generalize a₁.getLsbD k = ak1 at hm ⊢
  generalize a₂.getLsbD k = ak2 at hm ⊢
  generalize b₁.getLsbD k = bk1
  generalize b₂.getLsbD k = bk2
  cases u₁ <;> cases u₂ <;> cases a0 <;> cases b0 <;>
    cases ak1 <;> cases ak2 <;> cases bk1 <;> cases bk2 <;>
    first | rfl | cases hm

/-! ## Layer 1: Bitwise-Polynomial AST (`BPoly`) & 3-Valued Bit-Derivative Compiler -/

/-- Every `BPoly` expression is automatically a T-function (commutes with `BitVec.setWidth`). -/
theorem BPoly.eval_setWidth (e : BPoly) {w k : Nat} (hk : k ≤ w) (x : BitVec w) :
    BitVec.setWidth k (e.eval x) = e.eval (BitVec.setWidth k x) := by
  induction e with
  | var => rfl
  | const c => exact setWidth_ofNat_le hk c
  | add a b iha ihb =>
    simp only [BPoly.eval, BitVec.setWidth_add _ _ hk, iha, ihb]
  | sub a b iha ihb =>
    simp only [BPoly.eval, setWidth_sub_le hk, iha, ihb]
  | mul a b iha ihb =>
    simp only [BPoly.eval, BitVec.setWidth_mul _ _ hk, iha, ihb]
  | xor a b iha ihb =>
    simp only [BPoly.eval, BitVec.setWidth_xor, iha, ihb]
  | and a b iha ihb =>
    simp only [BPoly.eval, BitVec.setWidth_and, iha, ihb]
  | or a b iha ihb =>
    simp only [BPoly.eval, BitVec.setWidth_or, iha, ihb]
  | not a iha =>
    simp only [BPoly.eval, BitVec.setWidth_not hk, iha]
  | shl a s iha =>
    simp only [BPoly.eval, setWidth_shiftLeft_le hk, iha]
  | clmul a b iha ihb =>
    simp only [BPoly.eval, setWidth_bvClmul hk, iha, ihb]

theorem BPoly.eval_getLsbD_zero (e : BPoly) {w : Nat} (hw : 0 < w) (x : BitVec w) :
    (e.eval x).getLsbD 0 = e.evalBit0 (x.getLsbD 0) := by
  induction e with
  | var => rfl
  | const c =>
    rw [BPoly.eval, BPoly.evalBit0, BitVec.getLsbD_ofNat]
    simp only [hw, decide_true, Bool.true_and]
  | add a b iha ihb =>
    rw [BPoly.eval, BPoly.evalBit0, BitVec.getLsbD_add hw, carry_zero_eq, iha, ihb]
    simp only [Bool.bne_false]
  | sub a b iha ihb =>
    rw [BPoly.eval, BPoly.evalBit0, BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add,
        BitVec.getLsbD_add hw, carry_zero_eq, BitVec.getLsbD_add hw, carry_zero_eq,
        BitVec.getLsbD_not, BitVec.getLsbD_ofNat, iha, ihb]
    simp only [hw, decide_true, Bool.true_and, Bool.bne_false]
    have h1 : Nat.testBit 1 0 = true := rfl
    rw [h1]
    cases a.evalBit0 (x.getLsbD 0) <;> cases b.evalBit0 (x.getLsbD 0) <;> rfl
  | mul a b iha ihb =>
    simp only [BPoly.eval, BPoly.evalBit0]
    rw [BitVec.getLsbD, BitVec.toNat_mul, Nat.testBit_mod_two_pow]
    simp only [hw, decide_true, Bool.true_and]
    rw [← nat_div_two_pow_mod_two, Nat.pow_zero, Nat.div_one, Nat.mul_mod]
    have ha : ((a.eval x).toNat % 2 == 1) = a.evalBit0 (x.getLsbD 0) := by
      rw [← iha, BitVec.getLsbD, ← nat_div_two_pow_mod_two]
      simp only [Nat.pow_zero, Nat.div_one]
    have hb : ((b.eval x).toNat % 2 == 1) = b.evalBit0 (x.getLsbD 0) := by
      rw [← ihb, BitVec.getLsbD, ← nat_div_two_pow_mod_two]
      simp only [Nat.pow_zero, Nat.div_one]
    cases ha_m : (a.eval x).toNat % 2 with
    | zero =>
      have : a.evalBit0 (x.getLsbD 0) = false := by rw [← ha, ha_m]; rfl
      simp [this]
    | succ k =>
      have hk1 : k = 0 := by have := Nat.mod_lt (a.eval x).toNat (by omega : 0 < 2); omega
      subst hk1
      have ha1 : a.evalBit0 (x.getLsbD 0) = true := by rw [← ha, ha_m]; rfl
      cases hb_m : (b.eval x).toNat % 2 with
      | zero =>
        have : b.evalBit0 (x.getLsbD 0) = false := by rw [← hb, hb_m]; rfl
        simp [ha1, this]
      | succ k' =>
        have hk2 : k' = 0 := by have := Nat.mod_lt (b.eval x).toNat (by omega : 0 < 2); omega
        subst hk2
        have hb1 : b.evalBit0 (x.getLsbD 0) = true := by rw [← hb, hb_m]; rfl
        simp [ha1, hb1]
  | xor a b iha ihb => rw [BPoly.eval, BPoly.evalBit0, BitVec.getLsbD_xor, iha, ihb]
  | and a b iha ihb => rw [BPoly.eval, BPoly.evalBit0, BitVec.getLsbD_and, iha, ihb]
  | or  a b iha ihb => rw [BPoly.eval, BPoly.evalBit0, BitVec.getLsbD_or, iha, ihb]
  | not a iha =>
    rw [BPoly.eval, BPoly.evalBit0, BitVec.getLsbD_not, iha]
    simp only [hw, decide_true, Bool.true_and]
  | shl a s iha =>
    rw [BPoly.eval, BPoly.evalBit0, BitVec.getLsbD_shiftLeft]
    cases s with
    | zero => simp only [hw, Nat.not_lt_zero, decide_true, decide_false, Bool.not_false,
        Bool.true_and, Nat.sub_zero, beq_self_eq_true, ite_true, iha]
    | succ s => simp only [hw, Nat.zero_lt_succ, decide_true, Bool.not_true, Bool.and_false,
        Bool.false_and, Nat.succ_ne_zero, beq_iff_eq, ite_false]
  | clmul a b iha ihb =>
    rw [BPoly.eval, BPoly.evalBit0, getLsbD_bvClmul _ _ hw, getLsbD_bvClmulAux_succ _ _ 0 0 hw]
    simp only [bvClmulAux, BitVec.getLsbD_zero, Nat.le_refl, ite_true, Nat.sub_zero,
      Bool.false_bne, iha, ihb, Bool.and_comm]

/- Static bit-support analyzers: provably 0 (or provably 1) at all bit positions `k ≥ m`. -/


theorem BPoly.support_sound (m : Nat) (e : BPoly) {w k : Nat}
    (hmk : m ≤ k) (hkw : k < w) (x : BitVec w) :
    (e.vanishesAbove m = true → (e.eval x).getLsbD k = false) ∧
    (e.allOnesAbove m = true → (e.eval x).getLsbD k = true) := by
  induction e with
  | var => simp [BPoly.vanishesAbove, BPoly.allOnesAbove]
  | const c =>
    refine ⟨fun h => ?_, fun h => by simp [BPoly.allOnesAbove] at h⟩
    have hc : c < 2 ^ m := by simpa [BPoly.vanishesAbove] using h
    have hck : c < 2 ^ k := Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by omega) hmk)
    rw [BPoly.eval, BitVec.getLsbD_ofNat]
    simp only [hkw, decide_true, Bool.true_and]
    rw [← nat_div_two_pow_mod_two, Nat.div_eq_of_lt hck]; rfl
  | add _ _ _ _ => simp [BPoly.vanishesAbove, BPoly.allOnesAbove]
  | sub _ _ _ _ => simp [BPoly.vanishesAbove, BPoly.allOnesAbove]
  | mul _ _ _ _ => simp [BPoly.vanishesAbove, BPoly.allOnesAbove]
  | shl _ _ _ => simp [BPoly.vanishesAbove, BPoly.allOnesAbove]
  | clmul _ _ _ _ => simp [BPoly.vanishesAbove, BPoly.allOnesAbove]
  | xor a b iha ihb =>
    refine ⟨fun h => ?_, fun h => by simp [BPoly.allOnesAbove] at h⟩
    simp only [BPoly.vanishesAbove, Bool.and_eq_true] at h
    rw [BPoly.eval, BitVec.getLsbD_xor, iha.1 h.1, ihb.1 h.2]; rfl
  | and a b iha ihb =>
    constructor
    · intro h
      simp only [BPoly.vanishesAbove, Bool.or_eq_true] at h
      rw [BPoly.eval, BitVec.getLsbD_and]
      cases h with
      | inl h1 => rw [iha.1 h1]; rfl
      | inr h2 => rw [ihb.1 h2]; exact Bool.and_false _
    · intro h
      simp only [BPoly.allOnesAbove, Bool.and_eq_true] at h
      rw [BPoly.eval, BitVec.getLsbD_and, iha.2 h.1, ihb.2 h.2]; rfl
  | or a b iha ihb =>
    constructor
    · intro h
      simp only [BPoly.vanishesAbove, Bool.and_eq_true] at h
      rw [BPoly.eval, BitVec.getLsbD_or, iha.1 h.1, ihb.1 h.2]; rfl
    · intro h
      simp only [BPoly.allOnesAbove, Bool.or_eq_true] at h
      rw [BPoly.eval, BitVec.getLsbD_or]
      cases h with
      | inl h1 => rw [iha.2 h1]; rfl
      | inr h2 => rw [ihb.2 h2]; exact Bool.or_true _
  | not a iha =>
    constructor
    · intro h
      simp only [BPoly.vanishesAbove] at h
      rw [BPoly.eval, BitVec.getLsbD_not, iha.2 h]
      simp only [hkw, decide_true, Bool.not_true, Bool.and_false]
    · intro h
      simp only [BPoly.allOnesAbove] at h
      rw [BPoly.eval, BitVec.getLsbD_not, iha.1 h]
      simp only [hkw, decide_true, Bool.not_false, Bool.and_true]

theorem absBit_xor_satisfies {d₁ d₂ : AbsBit} {dx dy₁ dy₂ : Bool}
    (h1 : d₁.Satisfies dx dy₁) (h2 : d₂.Satisfies dx dy₂) :
    (AbsBit.xor d₁ d₂).Satisfies dx (dy₁ ^^ dy₂) := by
  cases d₁ <;> cases d₂ <;> cases dx <;> cases dy₁ <;> cases dy₂ <;>
    simp_all [AbsBit.xor, AbsBit.Satisfies]

theorem absBit_scale_satisfies (b : Bool) {d : AbsBit} {dx dy : Bool}
    (h : d.Satisfies dx dy) :
    (AbsBit.scale b d).Satisfies dx (b && dy) := by
  cases b
  · simp [AbsBit.scale, AbsBit.Satisfies]
  · simp [AbsBit.scale, h]

/-- Fundamental Compiler Soundness Theorem for `BPoly.absDeriv`. -/
theorem BPoly.absDeriv_sound (m : Nat) (hm : 1 ≤ m) (e : BPoly)
    {w k : Nat} (hmk : m ≤ k) (hkw : k < w)
    (x y : BitVec w) (hxy : BitVec.setWidth k x = BitVec.setWidth k y) :
    (e.absDeriv m (x.getLsbD 0)).Satisfies
      (x.getLsbD k ^^ y.getLsbD k)
      ((e.eval x).getLsbD k ^^ (e.eval y).getLsbD k) := by
  have hk1 : 1 ≤ k := Nat.le_trans hm hmk
  have hw0 : 0 < w := Nat.lt_of_lt_of_le (by omega) hkw
  induction e with
  | var => rfl
  | const c => simp [BPoly.absDeriv, BPoly.eval, AbsBit.Satisfies]
  | add a b iha ihb =>
    have ha : BitVec.setWidth k (a.eval x) = BitVec.setWidth k (a.eval y) := by
      rw [a.eval_setWidth (Nat.le_of_lt hkw), a.eval_setWidth (Nat.le_of_lt hkw), hxy]
    have hb : BitVec.setWidth k (b.eval x) = BitVec.setWidth k (b.eval y) := by
      rw [b.eval_setWidth (Nat.le_of_lt hkw), b.eval_setWidth (Nat.le_of_lt hkw), hxy]
    simp only [BPoly.eval, BPoly.absDeriv]
    rw [getLsbD_add_xor_diff hkw ha hb]
    exact absBit_xor_satisfies iha ihb
  | sub a b iha ihb =>
    have ha : BitVec.setWidth k (a.eval x) = BitVec.setWidth k (a.eval y) := by
      rw [a.eval_setWidth (Nat.le_of_lt hkw), a.eval_setWidth (Nat.le_of_lt hkw), hxy]
    have hb : BitVec.setWidth k (b.eval x) = BitVec.setWidth k (b.eval y) := by
      rw [b.eval_setWidth (Nat.le_of_lt hkw), b.eval_setWidth (Nat.le_of_lt hkw), hxy]
    simp only [BPoly.eval, BPoly.absDeriv]
    rw [getLsbD_sub_xor_diff hkw ha hb]
    exact absBit_xor_satisfies iha ihb
  | xor a b iha ihb =>
    simp only [BPoly.eval, BPoly.absDeriv, BitVec.getLsbD_xor]
    have hrearr :
        (((a.eval x).getLsbD k ^^ (b.eval x).getLsbD k) ^^
         ((a.eval y).getLsbD k ^^ (b.eval y).getLsbD k)) =
        (((a.eval x).getLsbD k ^^ (a.eval y).getLsbD k) ^^
         ((b.eval x).getLsbD k ^^ (b.eval y).getLsbD k)) := by
      cases (a.eval x).getLsbD k <;> cases (b.eval x).getLsbD k <;>
        cases (a.eval y).getLsbD k <;> cases (b.eval y).getLsbD k <;> rfl
    rw [hrearr]
    exact absBit_xor_satisfies iha ihb
  | not a iha =>
    simp only [BPoly.eval, BPoly.absDeriv, BitVec.getLsbD_not, hkw, decide_true, Bool.true_and]
    have hnot : (!(a.eval x).getLsbD k ^^ !(a.eval y).getLsbD k) =
        ((a.eval x).getLsbD k ^^ (a.eval y).getLsbD k) := by
      cases (a.eval x).getLsbD k <;> cases (a.eval y).getLsbD k <;> rfl
    rw [hnot]
    exact iha
  | shl a s iha =>
    simp only [BPoly.eval, BPoly.absDeriv]
    cases s with
    | zero =>
      simp only [beq_self_eq_true, ite_true, BitVec.getLsbD_shiftLeft, hkw,
        decide_true, Bool.true_and, Nat.not_lt_zero, decide_false, Bool.not_false, Nat.sub_zero]
      exact iha
    | succ s =>
      simp only [Nat.succ_ne_zero, beq_iff_eq, ite_false, AbsBit.Satisfies,
        BitVec.getLsbD_shiftLeft, hkw, decide_true, Bool.true_and]
      by_cases hks : k < s + 1
      · simp [hks]
      · have hsub : k - (s + 1) < k := by omega
        have ha : BitVec.setWidth k (a.eval x) = BitVec.setWidth k (a.eval y) := by
          rw [a.eval_setWidth (Nat.le_of_lt hkw), a.eval_setWidth (Nat.le_of_lt hkw), hxy]
        have hbit : (a.eval x).getLsbD (k - (s + 1)) = (a.eval y).getLsbD (k - (s + 1)) :=
          (setWidth_eq_iff _ _).mp ha (k - (s + 1)) hsub
        simp [hks, hbit]
  | mul a b iha ihb =>
    have ha : BitVec.setWidth k (a.eval x) = BitVec.setWidth k (a.eval y) := by
      rw [a.eval_setWidth (Nat.le_of_lt hkw), a.eval_setWidth (Nat.le_of_lt hkw), hxy]
    have hb : BitVec.setWidth k (b.eval x) = BitVec.setWidth k (b.eval y) := by
      rw [b.eval_setWidth (Nat.le_of_lt hkw), b.eval_setWidth (Nat.le_of_lt hkw), hxy]
    simp only [BPoly.eval, BPoly.absDeriv]
    rw [getLsbD_mul_xor_diff hk1 hkw ha hb,
        a.eval_getLsbD_zero hw0 x, b.eval_getLsbD_zero hw0 x]
    exact absBit_xor_satisfies (absBit_scale_satisfies _ ihb) (absBit_scale_satisfies _ iha)
  | clmul a b iha ihb =>
    have ha : BitVec.setWidth k (a.eval x) = BitVec.setWidth k (a.eval y) := by
      rw [a.eval_setWidth (Nat.le_of_lt hkw), a.eval_setWidth (Nat.le_of_lt hkw), hxy]
    have hb : BitVec.setWidth k (b.eval x) = BitVec.setWidth k (b.eval y) := by
      rw [b.eval_setWidth (Nat.le_of_lt hkw), b.eval_setWidth (Nat.le_of_lt hkw), hxy]
    simp only [BPoly.eval, BPoly.absDeriv]
    rw [getLsbD_bvClmul_xor_diff hk1 hkw ha hb,
        a.eval_getLsbD_zero hw0 x, b.eval_getLsbD_zero hw0 x]
    exact absBit_xor_satisfies (absBit_scale_satisfies _ ihb) (absBit_scale_satisfies _ iha)
  | and a b iha ihb =>
    simp only [BPoly.eval, BPoly.absDeriv, BitVec.getLsbD_and]
    split
    · rename_i hvan
      simp only [AbsBit.Satisfies]
      simp only [Bool.or_eq_true] at hvan
      cases hvan with
      | inl ha0 =>
        rw [(a.support_sound m hmk hkw x).1 ha0, (a.support_sound m hmk hkw y).1 ha0]; rfl
      | inr hb0 =>
        rw [(b.support_sound m hmk hkw x).1 hb0, (b.support_sound m hmk hkw y).1 hb0]
        simp only [Bool.and_false]; rfl
    · split
      · rename_i ha1
        rw [(a.support_sound m hmk hkw x).2 ha1, (a.support_sound m hmk hkw y).2 ha1]
        simpa using ihb
      · split
        · rename_i hb1
          rw [(b.support_sound m hmk hkw x).2 hb1, (b.support_sound m hmk hkw y).2 hb1]
          simpa using iha
        · cases hda : a.absDeriv m (x.getLsbD 0) <;> cases hdb : b.absDeriv m (x.getLsbD 0)
          all_goals try exact True.intro
          rw [hda] at iha; rw [hdb] at ihb
          simp only [AbsBit.Satisfies] at iha ihb ⊢
          have haeq : (a.eval x).getLsbD k = (a.eval y).getLsbD k := by
            cases h1 : (a.eval x).getLsbD k <;> cases h2 : (a.eval y).getLsbD k <;> simp_all
          have hbeq : (b.eval x).getLsbD k = (b.eval y).getLsbD k := by
            cases h1 : (b.eval x).getLsbD k <;> cases h2 : (b.eval y).getLsbD k <;> simp_all
          rw [haeq, hbeq]; exact Bool.xor_self _
  | or a b iha ihb =>
    simp only [BPoly.eval, BPoly.absDeriv, BitVec.getLsbD_or]
    split
    · rename_i hone
      simp only [AbsBit.Satisfies]
      simp only [Bool.or_eq_true] at hone
      cases hone with
      | inl ha1 =>
        rw [(a.support_sound m hmk hkw x).2 ha1, (a.support_sound m hmk hkw y).2 ha1]; rfl
      | inr hb1 =>
        rw [(b.support_sound m hmk hkw x).2 hb1, (b.support_sound m hmk hkw y).2 hb1]
        simp only [Bool.or_true]; rfl
    · split
      · rename_i ha0
        rw [(a.support_sound m hmk hkw x).1 ha0, (a.support_sound m hmk hkw y).1 ha0]
        simpa using ihb
      · split
        · rename_i hb0
          rw [(b.support_sound m hmk hkw x).1 hb0, (b.support_sound m hmk hkw y).1 hb0]
          simpa using iha
        · cases hda : a.absDeriv m (x.getLsbD 0) <;> cases hdb : b.absDeriv m (x.getLsbD 0)
          all_goals try exact True.intro
          rw [hda] at iha; rw [hdb] at ihb
          simp only [AbsBit.Satisfies] at iha ihb ⊢
          have haeq : (a.eval x).getLsbD k = (a.eval y).getLsbD k := by
            cases h1 : (a.eval x).getLsbD k <;> cases h2 : (a.eval y).getLsbD k <;> simp_all
          have hbeq : (b.eval x).getLsbD k = (b.eval y).getLsbD k := by
            cases h1 : (b.eval x).getLsbD k <;> cases h2 : (b.eval y).getLsbD k <;> simp_all
          rw [haeq, hbeq]; exact Bool.xor_self _

/-! ## Layer 2: Width-Polymorphic 2-Adic Hensel-Contraction & Basin Engine -/

theorem IsTFunc.iter_setWidth {F : ∀ w, BitVec w → BitVec w} (hF : IsTFunc F)
    {w k : Nat} (hk : k ≤ w) (t : Nat) (x : BitVec w) :
    BitVec.setWidth k (iter (F w) t x) = iter (F k) t (BitVec.setWidth k x) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [iter_succ, iter_succ, hF hk, ih]

theorem BPoly.isTFunc (e : BPoly) : IsTFunc (fun _ => e.eval) :=
  fun hk x => e.eval_setWidth hk x

theorem BPoly.isContractingOn_of_absDeriv (e : BPoly) (m : Nat) (hm : 1 ≤ m)
    (P : BitVec m → Bool)
    (hcert : ∀ r : BitVec m, P r = true → e.absDeriv m (r.getLsbD 0) = .zero) :
    IsContractingOn (fun _ => e.eval) m P := by
  intro w k hmk hkw x y hPx hxy
  have hlo : BitVec.setWidth k (e.eval x) = BitVec.setWidth k (e.eval y) := by
    rw [e.eval_setWidth (Nat.le_of_lt hkw), e.eval_setWidth (Nat.le_of_lt hkw), hxy]
  apply setWidth_succ_of_eq_bit hlo
  have hsound := e.absDeriv_sound m hm hmk hkw x y hxy
  have hbit0 : (BitVec.setWidth m x).getLsbD 0 = x.getLsbD 0 := by
    rw [BitVec.getLsbD_setWidth]
    have hm0 : 0 < m := hm
    simp only [hm0, decide_true, Bool.true_and]
  have hd : e.absDeriv m (x.getLsbD 0) = .zero := by
    rw [← hbit0]
    exact hcert (BitVec.setWidth m x) hPx
  rw [hd] at hsound
  simp only [AbsBit.Satisfies] at hsound
  cases h1 : (e.eval x).getLsbD k <;> cases h2 : (e.eval y).getLsbD k <;> simp_all

theorem BPoly.isContractingOn_of_check (e : BPoly) (m : Nat) (hm : 1 ≤ m)
    (P : BitVec m → Bool) (hchk : e.checkContractingOn m P = true) :
    IsContractingOn (fun _ => e.eval) m P := by
  apply e.isContractingOn_of_absDeriv m hm P
  intro r hPr
  have hrlt : r.toNat < 2 ^ m := r.isLt
  have hmem : r.toNat ∈ List.range (2 ^ m) := List.mem_range.mpr hrlt
  have hall := List.all_eq_true.mp hchk r.toNat hmem
  have hof : BitVec.ofNat m r.toNat = r := by
    rw [BitVec.ofNat_toNat, setWidth_self_eq]
  dsimp only at hall
  rw [hof, hPr] at hall
  simpa using hall

theorem BPoly.isContractingGlobal_of_absDeriv (e : BPoly) (m : Nat) (hm : 1 ≤ m)
    (h0 : e.absDeriv m false = .zero) (h1 : e.absDeriv m true = .zero) :
    IsContractingOn (fun _ => e.eval) m (fun _ => true) := by
  apply e.isContractingOn_of_absDeriv m hm (fun _ => true)
  intro r _
  cases r.getLsbD 0
  · exact h0
  · exact h1

/-! ### Theorem 1: Universal Fixed-Point Depth Bound (No Contraction Hypothesis!) -/

theorem bitvec_fiber_two {k : Nat} (a b z : BitVec (k + 1))
    (hab : BitVec.setWidth k b = BitVec.setWidth k a)
    (hne : b.getLsbD k ≠ a.getLsbD k)
    (hz : BitVec.setWidth k z = BitVec.setWidth k a) :
    z = a ∨ z = b := by
  by_cases hzk : z.getLsbD k = a.getLsbD k
  · left
    have hsw := setWidth_succ_of_eq_bit hz hzk
    simpa [setWidth_self_eq] using hsw
  · right
    have hzb : z.getLsbD k = b.getLsbD k := by
      cases h1 : z.getLsbD k <;> cases h2 : a.getLsbD k <;> cases h3 : b.getLsbD k <;> simp_all
    have hsw := setWidth_succ_of_eq_bit (hz.trans hab.symm) hzb
    simpa [setWidth_self_eq] using hsw

/--
  **Universal Fixed-Point Depth Law:**
  For ANY T-function `F` (no contraction hypothesis required!), every `x : BitVec w`
  that eventually reaches a fixed point `xStar` reaches `xStar` in at most `w` steps.
-/
theorem tfunc_fixedPoint_depth_le_width {F : ∀ w, BitVec w → BitVec w} (hF : IsTFunc F)
    {w : Nat} (x xStar : BitVec w)
    (hfix : F w xStar = xStar) (hreach : ∃ t, iter (F w) t x = xStar) :
    iter (F w) w x = xStar := by
  suffices ∀ k, k ≤ w → BitVec.setWidth k (iter (F w) k x) = BitVec.setWidth k xStar by
    have h := this w (Nat.le_refl w)
    simpa [setWidth_self_eq] using h
  intro k hk
  induction k with
  | zero =>
    apply BitVec.eq_of_getLsbD_eq
    intro i hi; omega
  | succ k ih =>
    have hkw : k ≤ w := Nat.le_of_succ_le hk
    have hprev := ih hkw
    let y := iter (F w) k x
    let a := BitVec.setWidth (k + 1) xStar
    let b := BitVec.setWidth (k + 1) y
    have hFa : F (k + 1) a = a := by
      change F (k + 1) (BitVec.setWidth (k + 1) xStar) = BitVec.setWidth (k + 1) xStar
      rw [← hF hk xStar, hfix]
    have hFb_eq : BitVec.setWidth (k + 1) (iter (F w) (k + 1) x) = F (k + 1) b := by
      rw [iter_succ, hF hk]
    rw [hFb_eq]
    by_cases hbit : y.getLsbD k = xStar.getLsbD k
    · have hba : b = a := setWidth_succ_of_eq_bit hprev hbit
      rw [hba, hFa]
    · have hba_lo : BitVec.setWidth k b = BitVec.setWidth k a := by
        change BitVec.setWidth k (BitVec.setWidth (k + 1) y) =
          BitVec.setWidth k (BitVec.setWidth (k + 1) xStar)
        rw [BitVec.setWidth_setWidth_of_le _ (Nat.le_succ k),
            BitVec.setWidth_setWidth_of_le _ (Nat.le_succ k)]
        exact hprev
      have hne_bit : b.getLsbD k ≠ a.getLsbD k := by
        have hlt : k < k + 1 := Nat.lt_succ_self k
        change (BitVec.setWidth (k + 1) y).getLsbD k ≠ (BitVec.setWidth (k + 1) xStar).getLsbD k
        rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth]
        simp only [hlt, decide_true, Bool.true_and]
        exact hbit
      have hFb_lo : BitVec.setWidth k (F (k + 1) b) = BitVec.setWidth k a := by
        rw [hF (Nat.le_succ k), hba_lo, ← hF (Nat.le_succ k), hFa]
      cases bitvec_fiber_two a b (F (k + 1) b) hba_lo hne_bit hFb_lo with
      | inl h1 => exact h1
      | inr hFb_fix =>
        exfalso
        rcases hreach with ⟨t, ht⟩
        have hba_ne : b ≠ a := by
          intro hEq
          exact hne_bit (congrArg (fun v => v.getLsbD k) hEq)
        by_cases htk : t ≤ k
        · have hyx : y = xStar := by
            have hdecomp : k = (k - t) + t := by omega
            change iter (F w) k x = xStar
            rw [hdecomp, iter_add, ht, iter_fixed hfix]
          exact hba_ne (congrArg (BitVec.setWidth (k + 1)) hyx)
        · have hdecomp : t = (t - k) + k := by omega
          have hiter : iter (F w) t x = iter (F w) (t - k) (iter (F w) k x) := by
            rw [← iter_add, ← hdecomp]
          have ha_eq : a = iter (F (k + 1)) (t - k) b := by
            change BitVec.setWidth (k + 1) xStar = iter (F (k + 1)) (t - k) (BitVec.setWidth (k + 1) (iter (F w) k x))
            rw [← ht, hiter, hF.iter_setWidth hk]
          rw [iter_fixed hFb_fix] at ha_eq
          exact hba_ne ha_eq.symm

/-! ### Theorem 2: Cycle-Localized 2-Adic Hensel Lifting Engine -/

theorem iter_contracts_by_count {F : ∀ w, BitVec w → BitVec w}
    (hF : IsTFunc F) {m : Nat} {P : BitVec m → Bool} (hC : IsContractingOn F m P)
    {w k : Nat} (hmk : m ≤ k) (hkw : k ≤ w)
    (r : BitVec m) (x y : BitVec w)
    (hxr : BitVec.setWidth m x = r)
    (hxy : BitVec.setWidth k x = BitVec.setWidth k y) (t : Nat) :
    BitVec.setWidth (min w (k + cycleContractionCount F m P r t)) (iter (F w) t x) =
    BitVec.setWidth (min w (k + cycleContractionCount F m P r t)) (iter (F w) t y) := by
  induction t with
  | zero =>
    have hmin : min w (k + 0) = k := by omega
    rw [cycleContractionCount, hmin]
    exact hxy
  | succ t ih =>
    let c := cycleContractionCount F m P r t
    let j := min w (k + c)
    have hle_w : j ≤ w := Nat.min_le_left w (k + c)
    have hmj : m ≤ j := by omega
    rw [cycleContractionCount]
    cases hPt : P (iter (F m) t r) with
    | false =>
      change BitVec.setWidth (min w (k + (c + 0))) (iter (F w) (t + 1) x) =
             BitVec.setWidth (min w (k + (c + 0))) (iter (F w) (t + 1) y)
      rw [Nat.add_zero, iter_succ, iter_succ, hF hle_w, hF hle_w, ih]
    | true =>
      by_cases hjw : j < w
      · have hmin_succ : min w (k + (c + 1)) = j + 1 := by omega
        change BitVec.setWidth (min w (k + (c + 1))) (iter (F w) (t + 1) x) =
               BitVec.setWidth (min w (k + (c + 1))) (iter (F w) (t + 1) y)
        rw [hmin_succ, iter_succ, iter_succ]
        have hPm : P (BitVec.setWidth m (iter (F w) t x)) = true := by
          rw [hF.iter_setWidth (Nat.le_trans hmk hkw), hxr, hPt]
        exact hC hmj hjw (iter (F w) t x) (iter (F w) t y) hPm ih
      · have hj_eq : j = w := by omega
        have hmin_eq : min w (k + (c + 1)) = w := by omega
        change BitVec.setWidth (min w (k + (c + 1))) (iter (F w) (t + 1) x) =
               BitVec.setWidth (min w (k + (c + 1))) (iter (F w) (t + 1) y)
        rw [hmin_eq, iter_succ, iter_succ]
        change BitVec.setWidth j (iter (F w) t x) = BitVec.setWidth j (iter (F w) t y) at ih
        rw [hj_eq, setWidth_self_eq, setWidth_self_eq] at ih
        rw [ih]

theorem iter_cycle_contracts_iterated {F : ∀ w, BitVec w → BitVec w}
    (hF : IsTFunc F) {m : Nat} {P : BitVec m → Bool} (hC : IsContractingOn F m P)
    {w k L : Nat} (hmk : m ≤ k) (hkw : k ≤ w)
    (r : BitVec m) (hper : iter (F m) L r = r)
    (x y : BitVec w)
    (hxr : BitVec.setWidth m x = r)
    (hxy : BitVec.setWidth k x = BitVec.setWidth k y) (q : Nat) :
    BitVec.setWidth (min w (k + q * cycleContractionCount F m P r L)) (iter (F w) (q * L) x) =
    BitVec.setWidth (min w (k + q * cycleContractionCount F m P r L)) (iter (F w) (q * L) y) := by
  let c := cycleContractionCount F m P r L
  induction q with
  | zero =>
    have hmin : min w (k + 0 * c) = k := by omega
    change BitVec.setWidth (min w (k + 0 * c)) (iter (F w) (0 * L) x) =
           BitVec.setWidth (min w (k + 0 * c)) (iter (F w) (0 * L) y)
    rw [hmin, Nat.zero_mul]; exact hxy
  | succ q ih =>
    let j := min w (k + q * c)
    have hmj : m ≤ j := by omega
    have hjw : j ≤ w := Nat.min_le_left w (k + q * c)
    have hxr_q : BitVec.setWidth m (iter (F w) (q * L) x) = r := by
      rw [hF.iter_setWidth (Nat.le_trans hmk hkw), hxr, ← iter_mul, iter_fixed hper]
    have hstep := iter_contracts_by_count hF hC hmj hjw r
      (iter (F w) (q * L) x) (iter (F w) (q * L) y) hxr_q ih L
    have hmin_eq : min w (j + c) = min w (k + (q + 1) * c) := by
      have : (q + 1) * c = q * c + c := Nat.succ_mul q c
      omega
    change BitVec.setWidth (min w (j + c)) (iter (F w) L (iter (F w) (q * L) x)) =
           BitVec.setWidth (min w (j + c)) (iter (F w) L (iter (F w) (q * L) y)) at hstep
    rw [hmin_eq, ← iter_add, ← iter_add, Nat.add_comm L (q * L), ← Nat.succ_mul] at hstep
    exact hstep

theorem henselRounds_mul_ge {w m c : Nat} (hc : 1 ≤ c) :
    w - m ≤ henselRounds w m c * c := by
  unfold henselRounds
  have hpos : 0 < c := hc
  have hmod := Nat.mod_lt (w - m + c - 1) hpos
  have hdiv := Nat.div_add_mod (w - m + c - 1) c
  rw [Nat.mul_comm] at hdiv
  omega

theorem fiber_collapse {F : ∀ w, BitVec w → BitVec w}
    (hF : IsTFunc F) {m L : Nat} {P : BitVec m → Bool} (hC : IsContractingOn F m P)
    (r : BitVec m) (hper : iter (F m) L r = r)
    (hc : 1 ≤ cycleContractionCount F m P r L)
    {w : Nat} (hmw : m ≤ w) (x y : BitVec w)
    (hx : BitVec.setWidth m x = r) (hy : BitVec.setWidth m y = r) :
    iter (F w) (henselRounds w m (cycleContractionCount F m P r L) * L) x =
    iter (F w) (henselRounds w m (cycleContractionCount F m P r L) * L) y := by
  let c := cycleContractionCount F m P r L
  have h := iter_cycle_contracts_iterated hF hC (Nat.le_refl m) hmw r hper x y hx
    (hx.trans hy.symm) (henselRounds w m c)
  have hge : w - m ≤ henselRounds w m c * c := henselRounds_mul_ge (w := w) (m := m) hc
  have hmin : min w (m + henselRounds w m c * c) = w := by omega
  change BitVec.setWidth (min w (m + henselRounds w m c * c)) (iter (F w) (henselRounds w m c * L) x) =
         BitVec.setWidth (min w (m + henselRounds w m c * c)) (iter (F w) (henselRounds w m c * L) y) at h
  rw [hmin, setWidth_self_eq, setWidth_self_eq] at h
  exact h

/-- `henselLift` projects back to `r` under `setWidth m`. -/
theorem henselLift_setWidth {F : ∀ w, BitVec w → BitVec w} (hF : IsTFunc F)
    {m L c w : Nat} (hmw : m ≤ w) (r : BitVec m) (hper : iter (F m) L r = r) :
    BitVec.setWidth m (henselLift F m L c w r) = r := by
  unfold henselLift
  rw [hF.iter_setWidth hmw, BitVec.setWidth_setWidth_of_le _ hmw, setWidth_self_eq,
      ← iter_mul, iter_fixed hper]

/-- **Existence:** `henselLift` is an exact `L`-periodic point at width `w`. -/
theorem henselLift_periodic {F : ∀ w, BitVec w → BitVec w}
    (hF : IsTFunc F) {m L : Nat} {P : BitVec m → Bool} (hC : IsContractingOn F m P)
    (r : BitVec m) (hper : iter (F m) L r = r)
    (hc : 1 ≤ cycleContractionCount F m P r L)
    {w : Nat} (hmw : m ≤ w) :
    iter (F w) L (henselLift F m L (cycleContractionCount F m P r L) w r) =
      henselLift F m L (cycleContractionCount F m P r L) w r := by
  let c := cycleContractionCount F m P r L
  let q := henselRounds w m c
  let xStar := henselLift F m L c w r
  have hxStar_m : BitVec.setWidth m xStar = r := henselLift_setWidth hF hmw r hper
  have hLx_m : BitVec.setWidth m (iter (F w) L xStar) = r := by
    rw [hF.iter_setWidth hmw, hxStar_m, hper]
  have hr0_m : BitVec.setWidth m (BitVec.setWidth w r) = r := by
    rw [BitVec.setWidth_setWidth_of_le _ hmw, setWidth_self_eq]
  have hcol1 := fiber_collapse hF hC r hper hc hmw (iter (F w) L xStar) xStar hLx_m hxStar_m
  have hcol2 := fiber_collapse hF hC r hper hc hmw xStar (BitVec.setWidth w r) hxStar_m hr0_m
  have hcomm : iter (F w) (q * L) (iter (F w) L xStar) =
      iter (F w) L (iter (F w) (q * L) xStar) := by
    rw [← iter_add, Nat.add_comm, iter_add]
  change iter (F w) (q * L) (iter (F w) L xStar) = iter (F w) (q * L) xStar at hcol1
  change iter (F w) (q * L) xStar = xStar at hcol2
  rw [hcomm, hcol2] at hcol1
  exact hcol1

/-- **Uniqueness:** Any `L`-periodic point at width `w` truncating to `r` equals `henselLift`. -/
theorem henselLift_unique {F : ∀ w, BitVec w → BitVec w}
    (hF : IsTFunc F) {m L : Nat} {P : BitVec m → Bool} (hC : IsContractingOn F m P)
    (r : BitVec m) (hper : iter (F m) L r = r)
    (hc : 1 ≤ cycleContractionCount F m P r L)
    {w : Nat} (hmw : m ≤ w) (y : BitVec w)
    (hym : BitVec.setWidth m y = r) (hyper : iter (F w) L y = y) :
    y = henselLift F m L (cycleContractionCount F m P r L) w r := by
  let c := cycleContractionCount F m P r L
  let q := henselRounds w m c
  have hr0_m : BitVec.setWidth m (BitVec.setWidth w r) = r := by
    rw [BitVec.setWidth_setWidth_of_le _ hmw, setWidth_self_eq]
  have hcol := fiber_collapse hF hC r hper hc hmw y (BitVec.setWidth w r) hym hr0_m
  have hyq : iter (F w) (q * L) y = y := by
    rw [← iter_mul, iter_fixed hyper]
  change iter (F w) (q * L) y = henselLift F m L c w r at hcol
  rw [hyq] at hcol
  exact hcol

/-- **Exact Minimal-Period Preservation:** `xStar` has exact period `d` iff `r` has exact period `d`. -/
theorem henselLift_period_iff {F : ∀ w, BitVec w → BitVec w}
    (hF : IsTFunc F) {m L : Nat} {P : BitVec m → Bool} (hC : IsContractingOn F m P)
    (r : BitVec m) (hper : iter (F m) L r = r)
    (hc : 1 ≤ cycleContractionCount F m P r L)
    {w : Nat} (hmw : m ≤ w) (d : Nat) :
    iter (F w) d (henselLift F m L (cycleContractionCount F m P r L) w r) =
      henselLift F m L (cycleContractionCount F m P r L) w r ↔
    iter (F m) d r = r := by
  let c := cycleContractionCount F m P r L
  let xStar := henselLift F m L c w r
  have hxStar_m : BitVec.setWidth m xStar = r := henselLift_setWidth hF hmw r hper
  constructor
  · intro h
    have h1 := congrArg (BitVec.setWidth m) h
    rw [hF.iter_setWidth hmw] at h1
    change iter (F m) d (BitVec.setWidth m xStar) = BitVec.setWidth m xStar at h1
    rw [hxStar_m] at h1
    exact h1
  · intro h
    have hdx_m : BitVec.setWidth m (iter (F w) d xStar) = r := by
      rw [hF.iter_setWidth hmw, hxStar_m, h]
    have hdx_per : iter (F w) L (iter (F w) d xStar) = iter (F w) d xStar := by
      rw [← iter_add, Nat.add_comm, iter_add]
      exact congrArg (iter (F w) d) (henselLift_periodic hF hC r hper hc hmw)
    exact henselLift_unique hF hC r hper hc hmw (iter (F w) d xStar) hdx_m hdx_per

/-- **Cycle-Localized Basin Convergence Depth Bound:**
    If `x` reaches `r` mod `2^m` in `d` steps, then `x` reaches `henselLift r`
    in at most `d + ⌈(w - m) / c⌉ * L` steps. -/
theorem henselLift_basin_convergence {F : ∀ w, BitVec w → BitVec w}
    (hF : IsTFunc F) {m L : Nat} {P : BitVec m → Bool} (hC : IsContractingOn F m P)
    (r : BitVec m) (hper : iter (F m) L r = r)
    (hc : 1 ≤ cycleContractionCount F m P r L)
    {w : Nat} (hmw : m ≤ w) (x : BitVec w) (d : Nat)
    (hreach : iter (F m) d (BitVec.setWidth m x) = r) :
    iter (F w) (d + henselRounds w m (cycleContractionCount F m P r L) * L) x =
      henselLift F m L (cycleContractionCount F m P r L) w r := by
  have hdx_m : BitVec.setWidth m (iter (F w) d x) = r := by
    rw [hF.iter_setWidth hmw, hreach]
  have hr0_m : BitVec.setWidth m (BitVec.setWidth w r) = r := by
    rw [BitVec.setWidth_setWidth_of_le _ hmw, setWidth_self_eq]
  rw [Nat.add_comm, iter_add]
  exact fiber_collapse hF hC r hper hc hmw (iter (F w) d x) (BitVec.setWidth w r) hdx_m hr0_m

/-- **Full-Cycle Tight Depth Bound (`d + (w - m)`):**
    When every step on the cycle of `r` is contracting (e.g., global contraction above `m`),
    entering the mod-`2^m` cycle in `d` steps guarantees entering the exact width-`w` cycle
    in at most `d + (w - m)` steps! -/
theorem fullCycle_convergence_depth {F : ∀ w, BitVec w → BitVec w}
    (hF : IsTFunc F) {m L : Nat} {P : BitVec m → Bool} (hC : IsContractingOn F m P)
    (r : BitVec m) (hper : iter (F m) L r = r)
    (hall : ∀ t, P (iter (F m) t r) = true)
    {w : Nat} (hmw : m ≤ w) (x : BitVec w) (d : Nat)
    (hreach : iter (F m) d (BitVec.setWidth m x) = r) :
    iter (F w) L (iter (F w) (d + (w - m)) x) = iter (F w) (d + (w - m)) x := by
  have hcount : ∀ t, cycleContractionCount F m P r t = t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih => simp [cycleContractionCount, hall t, ih]
  let y := iter (F w) d x
  have hym : BitVec.setWidth m y = r := by
    change BitVec.setWidth m (iter (F w) d x) = r
    rw [hF.iter_setWidth hmw, hreach]
  have hLy_m : BitVec.setWidth m (iter (F w) L y) = r := by
    rw [hF.iter_setWidth hmw, hym, hper]
  have hstep := iter_contracts_by_count hF hC (Nat.le_refl m) hmw r (iter (F w) L y) y
    hLy_m (hLy_m.trans hym.symm) (w - m)
  rw [hcount (w - m)] at hstep
  have hmin : min w (m + (w - m)) = w := by omega
  rw [hmin, setWidth_self_eq, setWidth_self_eq] at hstep
  have hcomm : iter (F w) (w - m) (iter (F w) L y) = iter (F w) L (iter (F w) (w - m) y) := by
    rw [← iter_add, Nat.add_comm, iter_add]
  rw [hcomm] at hstep
  simpa [y, ← iter_add, Nat.add_comm d (w - m)] using hstep

/-- Tight fixed-point specialization of `fullCycle_convergence_depth`:
    if `r` is a fixed point with `P r = true` and `iter (F m) d (setWidth m x) = r`,
    then `iter (F w) (d + (w - m)) x = henselLift F m 1 1 w r`. -/
theorem fixedPoint_convergence_depth {F : ∀ w, BitVec w → BitVec w}
    (hF : IsTFunc F) {m : Nat} {P : BitVec m → Bool} (hC : IsContractingOn F m P)
    (r : BitVec m) (hfix : F m r = r) (hPr : P r = true)
    {w : Nat} (hmw : m ≤ w) (x : BitVec w) (d : Nat)
    (hreach : iter (F m) d (BitVec.setWidth m x) = r) :
    iter (F w) (d + (w - m)) x = henselLift F m 1 1 w r := by
  have hper : iter (F m) 1 r = r := hfix
  have hc : cycleContractionCount F m P r 1 = 1 := by
    simp [cycleContractionCount, iter, hPr]
  have hq : henselRounds w m 1 = w - m := by
    unfold henselRounds; omega
  have h := henselLift_basin_convergence hF hC r hper (by rw [hc]; omega) hmw x d hreach
  simpa [hc, hq, Nat.mul_one] using h

/-! ### Theorem 3: Exact `bvCount` Cardinality, Bijection & Basin-Size Scaling Engine -/

theorem bvCount_congr {w : Nat} {Q₁ Q₂ : BitVec w → Bool}
    (h : ∀ x : BitVec w, Q₁ x = Q₂ x) :
    bvCount w Q₁ = bvCount w Q₂ := by
  unfold bvCount
  congr 1
  funext n
  exact h (BitVec.ofNat w n)

theorem list_countP_eq_length_filter {α : Type} (p : α → Bool) (l : List α) :
    l.countP p = (l.filter p).length :=
  List.countP_eq_length_filter

theorem nodup_le_of_inj {α β : Type} (l₁ : List α) (l₂ : List β)
    (hn : l₁.Nodup) (f : α → β)
    (hmem : ∀ a ∈ l₁, f a ∈ l₂)
    (hinj : ∀ a₁ ∈ l₁, ∀ a₂ ∈ l₁, f a₁ = f a₂ → a₁ = a₂) :
    l₁.length ≤ l₂.length := by
  induction l₁ generalizing l₂ with
  | nil => exact Nat.zero_le _
  | cons a rest ih =>
    have ha_not : a ∉ rest := (List.nodup_cons.mp hn).1
    have hn_rest : rest.Nodup := (List.nodup_cons.mp hn).2
    have hfa : f a ∈ l₂ := hmem a (List.mem_cons_self ..)
    have ⟨l₂a, l₂b, hl₂⟩ := List.append_of_mem hfa
    have hsub : ∀ x ∈ rest, f x ∈ l₂a ++ l₂b := by
      intro x hx
      have hfx : f x ∈ l₂a ++ f a :: l₂b := hl₂ ▸ hmem x (List.mem_cons_of_mem a hx)
      rw [List.mem_append, List.mem_cons] at hfx
      rw [List.mem_append]
      rcases hfx with h1 | hEq | h2
      · exact Or.inl h1
      · exfalso
        have hxa : x = a := hinj x (List.mem_cons_of_mem a hx) a (List.mem_cons_self ..) hEq
        exact ha_not (hxa ▸ hx)
      · exact Or.inr h2
    have hinj_rest : ∀ x₁ ∈ rest, ∀ x₂ ∈ rest, f x₁ = f x₂ → x₁ = x₂ :=
      fun x₁ hx₁ x₂ hx₂ => hinj x₁ (List.mem_cons_of_mem a hx₁) x₂ (List.mem_cons_of_mem a hx₂)
    have hle := ih (l₂a ++ l₂b) hn_rest hsub hinj_rest
    rw [hl₂, List.length_append, List.length_cons, List.length_cons]
    rw [List.length_append] at hle
    omega

theorem nodup_filter {α : Type} (p : α → Bool) {l : List α} (h : l.Nodup) :
    (l.filter p).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a rest ih =>
    have ⟨ha, hr⟩ := List.nodup_cons.mp h
    simp only [List.filter_cons]
    cases p a
    · exact ih hr
    · exact List.nodup_cons.mpr ⟨fun hmem => ha (List.mem_filter.mp hmem).1, ih hr⟩

/-- Bijection principle for `bvCount`: any bijection between `{x | Q₁ x}` and `{y | Q₂ y}`
    proves `bvCount w₁ Q₁ = bvCount w₂ Q₂`. -/
theorem bvCount_eq_of_bij {w₁ w₂ : Nat} {Q₁ : BitVec w₁ → Bool} {Q₂ : BitVec w₂ → Bool}
    (f : BitVec w₁ → BitVec w₂) (g : BitVec w₂ → BitVec w₁)
    (hf : ∀ x, Q₁ x = true → Q₂ (f x) = true)
    (hg : ∀ y, Q₂ y = true → Q₁ (g y) = true)
    (hgf : ∀ x, Q₁ x = true → g (f x) = x)
    (hfg : ∀ y, Q₂ y = true → f (g y) = y) :
    bvCount w₁ Q₁ = bvCount w₂ Q₂ := by
  unfold bvCount
  rw [list_countP_eq_length_filter, list_countP_eq_length_filter]
  let L₁ := (List.range (2 ^ w₁)).filter (fun n => Q₁ (BitVec.ofNat w₁ n))
  let L₂ := (List.range (2 ^ w₂)).filter (fun n => Q₂ (BitVec.ofNat w₂ n))
  have hn₁ : L₁.Nodup := nodup_filter _ List.nodup_range
  have hn₂ : L₂.Nodup := nodup_filter _ List.nodup_range
  have hof₁ : ∀ n, n < 2 ^ w₁ → (BitVec.ofNat w₁ n).toNat = n := fun n hn => by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  have hof₂ : ∀ n, n < 2 ^ w₂ → (BitVec.ofNat w₂ n).toNat = n := fun n hn => by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  have hle1 : L₁.length ≤ L₂.length := by
    apply nodup_le_of_inj L₁ L₂ hn₁ (fun n => (f (BitVec.ofNat w₁ n)).toNat)
    · intro n hn
      have ⟨hmem, hq⟩ := List.mem_filter.mp hn
      rw [List.mem_filter, List.mem_range]
      refine ⟨(f (BitVec.ofNat w₁ n)).isLt, ?_⟩
      have hre : BitVec.ofNat w₂ (f (BitVec.ofNat w₁ n)).toNat = f (BitVec.ofNat w₁ n) := by
        rw [BitVec.ofNat_toNat, setWidth_self_eq]
      rw [hre]
      exact hf _ hq
    · intro n₁ hn₁' n₂ hn₂' heq
      have ⟨hr₁, hq₁⟩ := List.mem_filter.mp hn₁'
      have ⟨hr₂, hq₂⟩ := List.mem_filter.mp hn₂'
      have hfeq : f (BitVec.ofNat w₁ n₁) = f (BitVec.ofNat w₁ n₂) := BitVec.eq_of_toNat_eq heq
      have hxeq : BitVec.ofNat w₁ n₁ = BitVec.ofNat w₁ n₂ := by
        rw [← hgf _ hq₁, ← hgf _ hq₂, hfeq]
      have := congrArg BitVec.toNat hxeq
      rw [hof₁ n₁ (List.mem_range.mp hr₁), hof₁ n₂ (List.mem_range.mp hr₂)] at this
      exact this
  have hle2 : L₂.length ≤ L₁.length := by
    apply nodup_le_of_inj L₂ L₁ hn₂ (fun n => (g (BitVec.ofNat w₂ n)).toNat)
    · intro n hn
      have ⟨hmem, hq⟩ := List.mem_filter.mp hn
      rw [List.mem_filter, List.mem_range]
      refine ⟨(g (BitVec.ofNat w₂ n)).isLt, ?_⟩
      have hre : BitVec.ofNat w₁ (g (BitVec.ofNat w₂ n)).toNat = g (BitVec.ofNat w₂ n) := by
        rw [BitVec.ofNat_toNat, setWidth_self_eq]
      rw [hre]
      exact hg _ hq
    · intro n₁ hn₁' n₂ hn₂' heq
      have ⟨hr₁, hq₁⟩ := List.mem_filter.mp hn₁'
      have ⟨hr₂, hq₂⟩ := List.mem_filter.mp hn₂'
      have hgeq : g (BitVec.ofNat w₂ n₁) = g (BitVec.ofNat w₂ n₂) := BitVec.eq_of_toNat_eq heq
      have hyeq : BitVec.ofNat w₂ n₁ = BitVec.ofNat w₂ n₂ := by
        rw [← hfg _ hq₁, ← hfg _ hq₂, hgeq]
      have := congrArg BitVec.toNat hyeq
      rw [hof₂ n₁ (List.mem_range.mp hr₁), hof₂ n₂ (List.mem_range.mp hr₂)] at this
      exact this
  exact Nat.le_antisymm hle1 hle2

theorem range_add (a b : Nat) :
    List.range (a + b) = List.range a ++ (List.range b).map (fun i => a + i) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.add_succ, List.range_succ, List.range_succ, List.map_append, List.map_singleton,
        ← List.append_assoc, ih]

theorem countP_range_mul_periodic (p : Nat → Bool) (M : Nat)
    (hper : ∀ n, p (n + M) = p n) (q : Nat) :
    (List.range (q * M)).countP p = (List.range M).countP p * q := by
  have hshift : ∀ a n, p (a * M + n) = p n := by
    intro a
    induction a with
    | zero => intro n; simp
    | succ a ih =>
      intro n
      have h1 : (a + 1) * M + n = (a * M + n) + M := by
        rw [Nat.succ_mul]; omega
      rw [h1, hper, ih]
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, range_add, List.countP_append, ih, List.countP_map]
    have hcomp : (p ∘ fun i => q * M + i) = p := by
      funext i; exact hshift q i
    rw [hcomp, Nat.mul_succ]

/-- **Exact Fiber-Scaling Law:** Pulling back any predicate `Qm` from `BitVec m`
    to `BitVec w` (`m ≤ w`) multiplies its exact count by `2^(w - m)`. -/
theorem bvCount_setWidth_pullback {m w : Nat} (hmw : m ≤ w) (Qm : BitVec m → Bool) :
    bvCount w (fun x => Qm (BitVec.setWidth m x)) = bvCount m Qm * 2 ^ (w - m) := by
  unfold bvCount
  have hpow : 2 ^ w = 2 ^ (w - m) * 2 ^ m := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hmw]
  have hfun : (fun n => Qm (BitVec.setWidth m (BitVec.ofNat w n))) =
      (fun n => Qm (BitVec.ofNat m n)) := by
    funext n
    rw [setWidth_ofNat_le hmw]
  rw [hpow, hfun]
  apply countP_range_mul_periodic (fun n => Qm (BitVec.ofNat m n)) (2 ^ m)
  intro n
  have hof : BitVec.ofNat m (n + 2 ^ m) = BitVec.ofNat m n := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat]
  rw [hof]

/-! ### Reusable Finite-to-Infinite Master Classification Theorems -/

/-- **Master Periodic-Point Count Lifting Theorem:**
    If `F` is a T-function contracting on `P` above bit `m` and every `L`-periodic point
    at width `m` hits `P` at least once per cycle (checked by `checkPeriodicContracting`),
    then for ALL `w ≥ m`, `F w` has the EXACT SAME number of `L`-periodic points as `F m`! -/
theorem periodicCount_lift {F : ∀ w, BitVec w → BitVec w}
    (hF : IsTFunc F) {m L : Nat} {P : BitVec m → Bool} (hC : IsContractingOn F m P)
    (hchk : checkPeriodicContracting F m L P = true)
    {w : Nat} (hmw : m ≤ w) :
    bvCount w (isPeriodicB F L w) = bvCount m (isPeriodicB F L m) := by
  have hall : ∀ r : BitVec m, iter (F m) L r = r → 1 ≤ cycleContractionCount F m P r L := by
    intro r hr
    have hmem : r.toNat ∈ List.range (2 ^ m) := List.mem_range.mpr r.isLt
    have h := List.all_eq_true.mp hchk r.toNat hmem
    have hof : BitVec.ofNat m r.toNat = r := by rw [BitVec.ofNat_toNat, setWidth_self_eq]
    dsimp only at h
    rw [hof, hr] at h
    simpa using h
  apply bvCount_eq_of_bij (BitVec.setWidth m)
    (fun r => henselLift F m L (cycleContractionCount F m P r L) w r)
  · intro x hx
    have hx' : iter (F w) L x = x := by simpa [isPeriodicB] using hx
    have hm' : iter (F m) L (BitVec.setWidth m x) = BitVec.setWidth m x := by
      rw [← hF.iter_setWidth hmw, hx']
    simpa [isPeriodicB] using hm'
  · intro r hr
    have hr' : iter (F m) L r = r := by simpa [isPeriodicB] using hr
    have hper := henselLift_periodic hF hC r hr' (hall r hr') hmw
    simpa [isPeriodicB] using hper
  · intro x hx
    have hx' : iter (F w) L x = x := by simpa [isPeriodicB] using hx
    have hm' : iter (F m) L (BitVec.setWidth m x) = BitVec.setWidth m x := by
      rw [← hF.iter_setWidth hmw, hx']
    exact (henselLift_unique hF hC (BitVec.setWidth m x) hm' (hall _ hm') hmw x rfl hx').symm
  · intro r hr
    have hr' : iter (F m) L r = r := by simpa [isPeriodicB] using hr
    exact henselLift_setWidth hF hmw r hr'

/-- **Master Fixed-Point Count Lifting Theorem** (`L = 1` specialization). -/
theorem fixedPointCount_lift {F : ∀ w, BitVec w → BitVec w}
    (hF : IsTFunc F) {m : Nat} {P : BitVec m → Bool} (hC : IsContractingOn F m P)
    (hchk : checkPeriodicContracting F m 1 P = true)
    {w : Nat} (hmw : m ≤ w) :
    bvCount w (isFixedPointB F w) = bvCount m (isFixedPointB F m) := by
  have h := periodicCount_lift hF hC hchk hmw
  have h1 : isFixedPointB F w = isPeriodicB F 1 w := rfl
  have h2 : isFixedPointB F m = isPeriodicB F 1 m := rfl
  rw [h1, h2]; exact h

/-- **Master Global Fixed-Point Convergence Depth Theorem (`≤ dMax + (w - m)`):**
    If every state mod `2^m` reaches a fixed point in `≤ dMax` steps and all fixed points
    mod `2^m` satisfy `P`, then for ALL `w ≥ m`, every `x : BitVec w` reaches its exact
    Hensel-lifted fixed point in at most `dMax + (w - m)` steps! -/
theorem global_fixedPoint_depth_lift {F : ∀ w, BitVec w → BitVec w}
    (hF : IsTFunc F) {m dMax : Nat} {P : BitVec m → Bool} (hC : IsContractingOn F m P)
    (hreach : checkAllReachFixed F m dMax = true)
    (hfpC : checkPeriodicContracting F m 1 P = true)
    {w : Nat} (hmw : m ≤ w) (x : BitVec w) :
    F w (iter (F w) (dMax + (w - m)) x) = iter (F w) (dMax + (w - m)) x := by
  let r0 := BitVec.setWidth m x
  let r := iter (F m) dMax r0
  have hmem0 : r0.toNat ∈ List.range (2 ^ m) := List.mem_range.mpr r0.isLt
  have h0 := List.all_eq_true.mp hreach r0.toNat hmem0
  have hof0 : BitVec.ofNat m r0.toNat = r0 := by rw [BitVec.ofNat_toNat, setWidth_self_eq]
  dsimp only at h0
  rw [hof0] at h0
  have hfix : F m r = r := by simpa [r] using h0
  have hmemr : r.toNat ∈ List.range (2 ^ m) := List.mem_range.mpr r.isLt
  have hrC := List.all_eq_true.mp hfpC r.toNat hmemr
  have hofr : BitVec.ofNat m r.toNat = r := by rw [BitVec.ofNat_toNat, setWidth_self_eq]
  dsimp only at hrC
  rw [hofr] at hrC
  have hPr : P r = true := by
    have hfix1 : iter (F m) 1 r = r := hfix
    rw [hfix1] at hrC
    simp only [beq_self_eq_true, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hrC
    cases hP : P r with
    | true => rfl
    | false =>
      simp [cycleContractionCount, iter, hP] at hrC
  have hconv := fixedPoint_convergence_depth hF hC r hfix hPr hmw x dMax rfl
  rw [hconv]
  have hc1 : cycleContractionCount F m P r 1 = 1 := by
    simp [cycleContractionCount, iter, hPr]
  have hper := henselLift_periodic hF hC r (L := 1) hfix (by rw [hc1]; omega) hmw
  simpa [hc1, iter] using hper

/-- **Master Exact Fixed-Point Basin-Size Scaling Theorem:**
    Under the finite check at width `m`, for ANY fixed point `r` of `F m` with `P r = true`,
    its lifted fixed point `xStar = henselLift F m 1 1 w r` has exact basin size
    `(bvCount m (inFixedBasinAt F m dMax r)) * 2^(w - m)` for ALL `w ≥ m`! -/
theorem fixedPoint_basinSize_lift {F : ∀ w, BitVec w → BitVec w}
    (hF : IsTFunc F) {m dMax : Nat} {P : BitVec m → Bool} (hC : IsContractingOn F m P)
    (hreach : checkAllReachFixed F m dMax = true)
    (r : BitVec m) (hfix : F m r = r) (hPr : P r = true)
    {w : Nat} (hmw : m ≤ w) :
    bvCount w (inFixedBasinAt F w (dMax + (w - m)) (henselLift F m 1 1 w r)) =
      bvCount m (inFixedBasinAt F m dMax r) * 2 ^ (w - m) := by
  have heq_pred : ∀ x : BitVec w,
      inFixedBasinAt F w (dMax + (w - m)) (henselLift F m 1 1 w r) x =
      inFixedBasinAt F m dMax r (BitVec.setWidth m x) := by
    intro x
    unfold inFixedBasinAt
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    constructor
    · intro h
      have hm := congrArg (BitVec.setWidth m) h
      rw [hF.iter_setWidth hmw, henselLift_setWidth hF hmw (L := 1) r hfix] at hm
      let r0 := BitVec.setWidth m x
      have hmem0 : r0.toNat ∈ List.range (2 ^ m) := List.mem_range.mpr r0.isLt
      have h0 := List.all_eq_true.mp hreach r0.toNat hmem0
      have hof0 : BitVec.ofNat m r0.toNat = r0 := by rw [BitVec.ofNat_toNat, setWidth_self_eq]
      dsimp only at h0
      rw [hof0] at h0
      have hfix0 : F m (iter (F m) dMax r0) = iter (F m) dMax r0 := by simpa using h0
      rw [Nat.add_comm, iter_add, iter_fixed hfix0] at hm
      exact hm
    · intro h
      exact fixedPoint_convergence_depth hF hC r hfix hPr hmw x dMax h
  rw [bvCount_congr heq_pred, bvCount_setWidth_pullback hmw]

/-! ## Layer 3: Six Sharp Infinite Theorems, Exact Sharpness Lower Bounds & Counterexamples -/

/-! ### Theorem I: Asymmetric Non-Power-of-Two Basins for `f(x) = (x & 4) | (x * x)` (`∀ w ≥ 3`) -/

theorem mapAsym_contracting :
    IsContractingOn (fun _ => mapAsym.eval) 3 (fun _ => true) :=
  mapAsym.isContractingGlobal_of_absDeriv 3 (by omega) rfl rfl

theorem mapAsym_fixedPointCount (w : Nat) (hw : 3 ≤ w) :
    bvCount w (isFixedPointB (fun _ => mapAsym.eval) w) = 4 := by
  rw [fixedPointCount_lift mapAsym.isTFunc (P := fun _ => true) mapAsym_contracting (by decide) hw]
  decide

theorem mapAsym_depth_le (w : Nat) (hw : 3 ≤ w) (x : BitVec w) :
    mapAsym.eval (iter mapAsym.eval (1 + (w - 3)) x) =
      iter mapAsym.eval (1 + (w - 3)) x :=
  global_fixedPoint_depth_lift mapAsym.isTFunc (P := fun _ => true) mapAsym_contracting
    (dMax := 1) (by decide) (by decide) hw x

theorem mapAsym_basin_0 (w : Nat) (hw : 3 ≤ w) :
    bvCount w (inFixedBasinAt (fun _ => mapAsym.eval) w (1 + (w - 3))
      (henselLift (fun _ => mapAsym.eval) 3 1 1 w 0#3)) = 1 * 2 ^ (w - 3) := by
  rw [fixedPoint_basinSize_lift mapAsym.isTFunc (P := fun _ => true) mapAsym_contracting (dMax := 1)
      (by decide) 0#3 (by decide) rfl hw]
  rfl

theorem mapAsym_basin_1 (w : Nat) (hw : 3 ≤ w) :
    bvCount w (inFixedBasinAt (fun _ => mapAsym.eval) w (1 + (w - 3))
      (henselLift (fun _ => mapAsym.eval) 3 1 1 w 1#3)) = 2 * 2 ^ (w - 3) := by
  rw [fixedPoint_basinSize_lift mapAsym.isTFunc (P := fun _ => true) mapAsym_contracting (dMax := 1)
      (by decide) 1#3 (by decide) rfl hw]
  rfl

theorem mapAsym_basin_4_nonPowerOfTwo (w : Nat) (hw : 3 ≤ w) :
    bvCount w (inFixedBasinAt (fun _ => mapAsym.eval) w (1 + (w - 3))
      (henselLift (fun _ => mapAsym.eval) 3 1 1 w 4#3)) = 3 * 2 ^ (w - 3) := by
  rw [fixedPoint_basinSize_lift mapAsym.isTFunc (P := fun _ => true) mapAsym_contracting (dMax := 1)
      (by decide) 4#3 (by decide) rfl hw]
  rfl

theorem mapAsym_basin_5 (w : Nat) (hw : 3 ≤ w) :
    bvCount w (inFixedBasinAt (fun _ => mapAsym.eval) w (1 + (w - 3))
      (henselLift (fun _ => mapAsym.eval) 3 1 1 w 5#3)) = 2 * 2 ^ (w - 3) := by
  rw [fixedPoint_basinSize_lift mapAsym.isTFunc (P := fun _ => true) mapAsym_contracting (dMax := 1)
      (by decide) 5#3 (by decide) rfl hw]
  rfl

/-- Non-vacuity witness: the lifted fixed points of `4#3` and `5#3` at `w = 8` are
    non-trivial 2-adic attractors `148#8` and `109#8`. -/
example : henselLift (fun _ => mapAsym.eval) 3 1 1 8 4#3 = 148#8 ∧
          henselLift (fun _ => mapAsym.eval) 3 1 1 8 5#3 = 109#8 ∧
          mapAsym.eval 148#8 = 148#8 ∧
          mapAsym.eval 109#8 = 109#8 := by decide

/-! ### Theorem II: 7-Fixed-Point Bitwise-Quadratic Map `f(x) = (x & 6) | (x * x)` (`∀ w ≥ 3`) -/

theorem mapSeven_contracting :
    IsContractingOn (fun _ => mapSeven.eval) 3 (fun _ => true) :=
  mapSeven.isContractingGlobal_of_absDeriv 3 (by omega) rfl rfl

theorem mapSeven_fixedPointCount (w : Nat) (hw : 3 ≤ w) :
    bvCount w (isFixedPointB (fun _ => mapSeven.eval) w) = 7 := by
  rw [fixedPointCount_lift mapSeven.isTFunc (P := fun _ => true) mapSeven_contracting (by decide) hw]
  decide

theorem mapSeven_depth_le (w : Nat) (hw : 3 ≤ w) (x : BitVec w) :
    mapSeven.eval (iter mapSeven.eval (1 + (w - 3)) x) =
      iter mapSeven.eval (1 + (w - 3)) x :=
  global_fixedPoint_depth_lift mapSeven.isTFunc (P := fun _ => true) mapSeven_contracting
    (dMax := 1) (by decide) (by decide) hw x

theorem mapSeven_basin_6 (w : Nat) (hw : 3 ≤ w) :
    bvCount w (inFixedBasinAt (fun _ => mapSeven.eval) w (1 + (w - 3))
      (henselLift (fun _ => mapSeven.eval) 3 1 1 w 6#3)) = 2 * 2 ^ (w - 3) := by
  rw [fixedPoint_basinSize_lift mapSeven.isTFunc (P := fun _ => true) mapSeven_contracting (dMax := 1)
      (by decide) 6#3 (by decide) rfl hw]
  rfl

/-! ### Theorem III: 3-Fixed-Point Map `f(x) = ((x & 4) | (x * x)) + 2` (`∀ w ≥ 3`) -/

theorem mapThree_contracting :
    IsContractingOn (fun _ => mapThree.eval) 3 (fun _ => true) :=
  mapThree.isContractingGlobal_of_absDeriv 3 (by omega) rfl rfl

theorem mapThree_fixedPointCount (w : Nat) (hw : 3 ≤ w) :
    bvCount w (isFixedPointB (fun _ => mapThree.eval) w) = 3 := by
  rw [fixedPointCount_lift mapThree.isTFunc (P := fun _ => true) mapThree_contracting (by decide) hw]
  decide

theorem mapThree_depth_le (w : Nat) (hw : 3 ≤ w) (x : BitVec w) :
    mapThree.eval (iter mapThree.eval (2 + (w - 3)) x) =
      iter mapThree.eval (2 + (w - 3)) x :=
  global_fixedPoint_depth_lift mapThree.isTFunc (P := fun _ => true) mapThree_contracting
    (dMax := 2) (by decide) (by decide) hw x

theorem mapThree_basin_6 (w : Nat) (hw : 3 ≤ w) :
    bvCount w (inFixedBasinAt (fun _ => mapThree.eval) w (2 + (w - 3))
      (henselLift (fun _ => mapThree.eval) 3 1 1 w 6#3)) = 4 * 2 ^ (w - 3) := by
  rw [fixedPoint_basinSize_lift mapThree.isTFunc (P := fun _ => true) mapThree_contracting (dMax := 2)
      (by decide) 6#3 (by decide) rfl hw]
  rfl

/-! ### Theorem IV: Parametric Infinite XOR-Carry Family `f_c(x) = x ^ (x + c)` + Exact Depth `= w` -/

theorem mapXorAdd_contracting (c : Nat) :
    IsContractingOn (fun _ => (mapXorAdd c).eval) 1 (fun _ => true) :=
  (mapXorAdd c).isContractingGlobal_of_absDeriv 1 (by omega) rfl rfl

theorem mapXorAdd_fixed_iff (c w : Nat) (x : BitVec w) :
    (mapXorAdd c).eval x = x ↔ x = -(BitVec.ofNat w c) := by
  simp only [mapXorAdd, BPoly.eval]
  constructor
  · intro h
    have h0 : x + BitVec.ofNat w c = 0#w := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have hbi := congrArg (fun v => v.getLsbD i) h
      rw [BitVec.getLsbD_xor] at hbi
      rw [BitVec.getLsbD_zero]
      cases hx : x.getLsbD i <;> cases hy : (x + BitVec.ofNat w c).getLsbD i <;> simp_all
    have hsub := congrArg (fun v => v - BitVec.ofNat w c) h0
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg, BitVec.sub_self,
        BitVec.add_zero, BitVec.sub_eq_add_neg, BitVec.zero_add] at hsub
    exact hsub
  · intro h
    subst h
    have h0 : -(BitVec.ofNat w c) + BitVec.ofNat w c = 0#w := by
      rw [BitVec.add_comm, ← BitVec.sub_eq_add_neg, BitVec.sub_self]
    rw [h0]
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    rw [BitVec.getLsbD_xor, BitVec.getLsbD_zero, Bool.xor_false]

theorem mapXorAdd_checkAllReach (c : Nat) :
    checkAllReachFixed (fun _ => (mapXorAdd c).eval) 1 1 = true := by
  have hc : c % 2 = 0 ∨ c % 2 = 1 := Nat.mod_two_eq_zero_or_one c
  have hof : BitVec.ofNat 1 c = BitVec.ofNat 1 (c % 2) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofNat]
  unfold checkAllReachFixed
  simp only [mapXorAdd, BPoly.eval, iter, hof]
  rcases hc with h0 | h1
  · rw [h0]; decide
  · rw [h1]; decide

theorem mapXorAdd_checkPer (c : Nat) :
    checkPeriodicContracting (fun _ => (mapXorAdd c).eval) 1 1 (fun _ => true) = true := by
  unfold checkPeriodicContracting
  simp only [cycleContractionCount, iter, ite_true, Nat.zero_add, Nat.le_refl, decide_true,
    Bool.or_true, List.all_eq_true, implies_true]

theorem mapXorAdd_fixedPointCount (c w : Nat) (hw : 1 ≤ w) :
    bvCount w (isFixedPointB (fun _ => (mapXorAdd c).eval) w) = 1 := by
  rw [fixedPointCount_lift (mapXorAdd c).isTFunc (mapXorAdd_contracting c)
      (mapXorAdd_checkPer c) hw]
  have hc : c % 2 = 0 ∨ c % 2 = 1 := Nat.mod_two_eq_zero_or_one c
  have hof : BitVec.ofNat 1 c = BitVec.ofNat 1 (c % 2) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofNat]
  unfold bvCount isFixedPointB
  simp only [mapXorAdd, BPoly.eval, hof]
  rcases hc with h0 | h1
  · rw [h0]; decide
  · rw [h1]; decide

theorem mapXorAdd_converges_in_w (c w : Nat) (hw : 1 ≤ w) (x : BitVec w) :
    iter (mapXorAdd c).eval w x = -(BitVec.ofNat w c) := by
  have hfix := global_fixedPoint_depth_lift (mapXorAdd c).isTFunc (mapXorAdd_contracting c)
    (dMax := 1) (mapXorAdd_checkAllReach c) (mapXorAdd_checkPer c) hw x
  have h1w : 1 + (w - 1) = w := by omega
  rw [h1w] at hfix
  exact (mapXorAdd_fixed_iff c w _).mp hfix

/-- Exact orbit formula for `f_1(x) = x ^ (x + 1)` starting at `0#w`:
    `iter f_1 k (0#w) = ofNat w (2^k - 1)` for all `k ≤ w`. -/
theorem mapXorAdd1_orbit_zero (w : Nat) :
    ∀ k, k ≤ w → iter (mapXorAdd 1).eval k 0#w = BitVec.ofNat w (2 ^ k - 1) := by
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iter_succ, ih (Nat.le_of_succ_le hk)]
    simp only [mapXorAdd, BPoly.eval]
    have hpow : (BitVec.ofNat w (2 ^ k - 1)) + BitVec.ofNat w 1 = BitVec.ofNat w (2 ^ k) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      have hpos : 1 ≤ 2 ^ k := Nat.two_pow_pos k
      have hlt1 : 2 ^ k - 1 < 2 ^ w :=
        Nat.lt_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by omega) (Nat.le_of_succ_le hk))
      have hlt2 : 1 < 2 ^ w :=
        Nat.lt_of_lt_of_le (by omega : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by omega) (by omega))
      rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2, Nat.sub_add_cancel hpos]
    rw [hpow]
    have htest_pred : ∀ m i, (2 ^ m - 1).testBit i = decide (i < m) := by
      intro m i
      rw [← nat_div_two_pow_mod_two]
      by_cases him : i < m
      · have hle : i + 1 ≤ m := him
        have hdvd : 2 ^ (i + 1) ∣ 2 ^ m := Nat.pow_dvd_pow 2 hle
        rcases hdvd with ⟨q, hq⟩
        have hqpos : 1 ≤ q := by
          have := Nat.two_pow_pos m
          cases q with
          | zero => rw [Nat.mul_zero] at hq; omega
          | succ _ => omega
        have hdiv : (2 ^ m - 1) / 2 ^ i = 2 * q - 1 := by
          have hpow1 : 2 ^ (i + 1) = 2 ^ i * 2 := Nat.pow_succ 2 i
          have heq : 2 ^ m - 1 = (2 ^ i - 1) + (2 * q - 1) * 2 ^ i := by
            have h1 : 2 ^ m = 2 ^ i * (2 * q) := by rw [hq, hpow1, Nat.mul_assoc]
            have hsub1 : (2 * q - 1) + 1 = 2 * q := by omega
            have h2 : (2 * q - 1) * 2 ^ i + 2 ^ i = 2 ^ i * (2 * q) := by
              calc (2 * q - 1) * 2 ^ i + 2 ^ i
                  = (2 * q - 1 + 1) * 2 ^ i := by rw [Nat.add_mul, Nat.one_mul]
                _ = (2 * q) * 2 ^ i := by rw [hsub1]
                _ = 2 ^ i * (2 * q) := Nat.mul_comm _ _
            have h3 : 1 ≤ 2 ^ i := Nat.two_pow_pos i
            omega
          rw [heq, Nat.add_mul_div_right _ _ (Nat.two_pow_pos i),
              Nat.div_eq_of_lt (by have := Nat.two_pow_pos i; omega), Nat.zero_add]
        rw [hdiv]
        have hodd : (2 * q - 1) % 2 = 1 := by omega
        simp [him, hodd]
      · have hge : m ≤ i := by omega
        have hlt : 2 ^ m - 1 < 2 ^ i := by
          have hle : 2 ^ m ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hge
          have hpos : 1 ≤ 2 ^ m := Nat.two_pow_pos m
          omega
        rw [Nat.div_eq_of_lt hlt]
        simp [him]
    have htest_pow : ∀ m i, (2 ^ m).testBit i = decide (i = m) := by
      intro m i
      rw [← nat_div_two_pow_mod_two]
      by_cases him : i = m
      · subst him; rw [Nat.div_self (Nat.two_pow_pos i)]; simp
      · by_cases hlt : i < m
        · have hle : i + 1 ≤ m := hlt
          rcases Nat.pow_dvd_pow 2 hle with ⟨q, hq⟩
          have hdiv : 2 ^ m / 2 ^ i = 2 * q := by
            rw [hq, Nat.pow_succ, Nat.mul_assoc, Nat.mul_div_right _ (Nat.two_pow_pos i)]
          rw [hdiv]; simp [him]
        · have hgt : 2 ^ m < 2 ^ i := Nat.pow_lt_pow_right (by omega) (by omega)
          rw [Nat.div_eq_of_lt hgt]; simp [him]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_xor, BitVec.getLsbD_ofNat, BitVec.getLsbD_ofNat, BitVec.getLsbD_ofNat]
    simp only [hi, decide_true, Bool.true_and, htest_pred, htest_pow]
    by_cases h1 : i < k
    · have h2 : i ≠ k := by omega
      have h3 : i < k + 1 := by omega
      simp [h1, h2, h3]
    · by_cases h2 : i = k
      · subst h2; simp
      · have h3 : ¬(i < k + 1) := by omega
        simp [h1, h2, h3]

/-- **Sharpness of Depth Bound `≤ w`:** For every `w ≥ 1`, `x ^ (x + 1)` takes
    EXACTLY `w` steps from `0#w` to reach its unique fixed point `-1#w`. -/
theorem mapXorAdd1_exact_depth_sharp (w : Nat) (hw : 1 ≤ w) :
    iter (mapXorAdd 1).eval (w - 1) 0#w ≠ -(BitVec.ofNat w 1) ∧
    iter (mapXorAdd 1).eval w 0#w = -(BitVec.ofNat w 1) := by
  refine ⟨?_, mapXorAdd_converges_in_w 1 w hw 0#w⟩
  rw [mapXorAdd1_orbit_zero w (w - 1) (by omega)]
  intro hEq
  have hto := congrArg BitVec.toNat hEq
  rw [BitVec.toNat_ofNat, BitVec.toNat_neg, BitVec.toNat_ofNat] at hto
  have hlt1 : 2 ^ (w - 1) - 1 < 2 ^ w := by
    have hle : 2 ^ (w - 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (by omega)
    have hpos : 1 ≤ 2 ^ (w - 1) := Nat.two_pow_pos (w - 1)
    omega
  have hlt2 : 1 < 2 ^ w := by
    have hle : 2 ^ 1 ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hw
    omega
  have hlt3 : 2 ^ w - 1 < 2 ^ w := by
    have hpos : 1 ≤ 2 ^ w := Nat.two_pow_pos w; omega
  rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2, Nat.mod_eq_of_lt hlt3] at hto
  have hw_eq : w = (w - 1) + 1 := by omega
  have hpow : 2 ^ w = 2 ^ (w - 1) * 2 := by
    have h := congrArg (fun e => 2 ^ e) hw_eq
    rw [Nat.pow_succ] at h
    exact h
  have hpos : 1 ≤ 2 ^ (w - 1) := Nat.two_pow_pos (w - 1)
  omega

/-! ### Theorem V: Carryless + Arithmetic Hybrid `clmul(x, x) ^ (x + 1) ^ x` (`∀ w ≥ 1`) -/

theorem mapClmulHybrid_contracting :
    IsContractingOn (fun _ => mapClmulHybrid.eval) 1 (fun _ => true) :=
  mapClmulHybrid.isContractingGlobal_of_absDeriv 1 (by omega) rfl rfl

theorem mapClmulHybrid_no_fixedPoints (w : Nat) (hw : 1 ≤ w) :
    bvCount w (isFixedPointB (fun _ => mapClmulHybrid.eval) w) = 0 := by
  rw [fixedPointCount_lift mapClmulHybrid.isTFunc (P := fun _ => true)
      mapClmulHybrid_contracting (by decide) hw]
  decide

theorem mapClmulHybrid_unique_twoCycle (w : Nat) (hw : 1 ≤ w) :
    bvCount w (isPeriodicB (fun _ => mapClmulHybrid.eval) 2 w) = 2 := by
  rw [periodicCount_lift mapClmulHybrid.isTFunc (P := fun _ => true)
      mapClmulHybrid_contracting (by decide) hw]
  decide

theorem mapClmulHybrid_depth_le (w : Nat) (hw : 1 ≤ w) (x : BitVec w) :
    iter mapClmulHybrid.eval 2 (iter mapClmulHybrid.eval (w - 1) x) =
      iter mapClmulHybrid.eval (w - 1) x := by
  have hper2 : iter mapClmulHybrid.eval 2 (BitVec.setWidth 1 x) = BitVec.setWidth 1 x := by
    have hlt := (BitVec.setWidth 1 x).isLt
    have h01 : BitVec.setWidth 1 x = 0#1 ∨ BitVec.setWidth 1 x = 1#1 := by
      cases hval : (BitVec.setWidth 1 x).toNat with
      | zero => left; exact BitVec.eq_of_toNat_eq hval
      | succ k =>
        have hk : k = 0 := by omega
        subst hk; right; exact BitVec.eq_of_toNat_eq hval
    rcases h01 with h0 | h1
    · rw [h0]; decide
    · rw [h1]; decide
  have h := fullCycle_convergence_depth mapClmulHybrid.isTFunc (P := fun _ => true)
    mapClmulHybrid_contracting (BitVec.setWidth 1 x) hper2 (fun _ => rfl) hw x 0 rfl
  simpa using h

/-! ### Theorem VI: Cycle-Localized Contraction (Where Global `f'(x) = 0 mod 2` Fails!) -/

theorem mapLocalEven_not_global_deriv :
    mapLocalEven.absDeriv 1 false = .zero ∧ mapLocalEven.absDeriv 1 true = .one := by
  decide

theorem mapLocalEven_contractingOn_even :
    IsContractingOn (fun _ => mapLocalEven.eval) 1 isEven1 :=
  mapLocalEven.isContractingOn_of_check 1 (by omega) isEven1 (by decide)

theorem mapLocalEven_fixedPointCount (w : Nat) (hw : 1 ≤ w) :
    bvCount w (isFixedPointB (fun _ => mapLocalEven.eval) w) = 1 := by
  rw [fixedPointCount_lift mapLocalEven.isTFunc mapLocalEven_contractingOn_even (by decide) hw]
  decide

theorem mapLocalEven_depth_le (w : Nat) (hw : 1 ≤ w) (x : BitVec w) :
    mapLocalEven.eval (iter mapLocalEven.eval w x) = iter mapLocalEven.eval w x := by
  have h := global_fixedPoint_depth_lift mapLocalEven.isTFunc mapLocalEven_contractingOn_even
    (dMax := 1) (by decide) (by decide) hw x
  have h1w : 1 + (w - 1) = w := by omega
  rwa [h1w] at h

theorem mapHalfCycle_deriv_split :
    mapHalfCycle.absDeriv 1 false = .zero ∧ mapHalfCycle.absDeriv 1 true = .one := by
  decide

theorem mapHalfCycle_contractingOn_even :
    IsContractingOn (fun _ => mapHalfCycle.eval) 1 isEven1 :=
  mapHalfCycle.isContractingOn_of_check 1 (by omega) isEven1 (by decide)

theorem mapHalfCycle_no_fixedPoints (w : Nat) (hw : 1 ≤ w) :
    bvCount w (isFixedPointB (fun _ => mapHalfCycle.eval) w) = 0 := by
  rw [fixedPointCount_lift mapHalfCycle.isTFunc mapHalfCycle_contractingOn_even (by decide) hw]
  decide

theorem mapHalfCycle_unique_twoCycle (w : Nat) (hw : 1 ≤ w) :
    bvCount w (isPeriodicB (fun _ => mapHalfCycle.eval) 2 w) = 2 := by
  rw [periodicCount_lift mapHalfCycle.isTFunc mapHalfCycle_contractingOn_even (by decide) hw]
  decide

/-- Upper bound for `x^3 + 2x + 1`: EVERY `x : BitVec w` (`w ≥ 1`) enters the unique
    2-cycle in at most `2w - 2` steps. -/
theorem mapHalfCycle_depth_le (w : Nat) (hw : 1 ≤ w) (x : BitVec w) :
    iter mapHalfCycle.eval 2 (iter mapHalfCycle.eval (2 * (w - 1)) x) =
      iter mapHalfCycle.eval (2 * (w - 1)) x := by
  let r := BitVec.setWidth 1 x
  have h01 : r = 0#1 ∨ r = 1#1 := by
    have hlt := r.isLt
    cases hval : r.toNat with
    | zero => left; exact BitVec.eq_of_toNat_eq hval
    | succ k =>
      have hk : k = 0 := by omega
      subst hk; right; exact BitVec.eq_of_toNat_eq hval
  have hper : iter mapHalfCycle.eval 2 r = r := by
    rcases h01 with h0 | h1
    · rw [h0]; decide
    · rw [h1]; decide
  have hc : cycleContractionCount (fun _ => mapHalfCycle.eval) 1 isEven1 r 2 = 1 := by
    rcases h01 with h0 | h1
    · rw [h0]; decide
    · rw [h1]; decide
  have hconv := henselLift_basin_convergence mapHalfCycle.isTFunc mapHalfCycle_contractingOn_even
    r hper (by rw [hc]; omega) hw x 0 rfl
  have hperL := henselLift_periodic mapHalfCycle.isTFunc mapHalfCycle_contractingOn_even
    r hper (by rw [hc]; omega) hw
  have hq : henselRounds w 1 1 = w - 1 := by unfold henselRounds; omega
  have hsteps : 0 + henselRounds w 1 1 * 2 = 2 * (w - 1) := by rw [hq]; omega
  rw [hc, hsteps] at hconv
  rw [hconv]
  simpa [hc] using hperL

/-! #### Exact Lower Bound (`depth = 2w - 2`) for `x^3 + 2x + 1` at `x = 3#w` (`∀ w ≥ 2`) -/

theorem mapHalfCycle_odd_preserves_v2 {w k : Nat} (hk1 : 1 ≤ k) (hkw : k < w)
    {x y : BitVec w} (hodd : x.getLsbD 0 = true) (hv : v2Exact k x y) :
    v2Exact k (mapHalfCycle.eval x) (mapHalfCycle.eval y) := by
  refine ⟨?_, ?_⟩
  · rw [mapHalfCycle.eval_setWidth (Nat.le_of_lt hkw),
        mapHalfCycle.eval_setWidth (Nat.le_of_lt hkw), hv.1]
  · have hs := mapHalfCycle.absDeriv_sound 1 (by omega) hk1 hkw x y hv.1
    rw [hodd] at hs
    have hd : mapHalfCycle.absDeriv 1 true = .one := rfl
    rw [hd] at hs
    simp only [AbsBit.Satisfies] at hs
    have hne := hv.2
    cases h1 : x.getLsbD k <;> cases h2 : y.getLsbD k <;>
      cases h3 : (mapHalfCycle.eval x).getLsbD k <;>
      cases h4 : (mapHalfCycle.eval y).getLsbD k <;> simp_all

theorem nat_cube_expand (a b : Nat) :
    (a + b) * (a + b) * (a + b) =
      a * a * a + 3 * a * a * b + 3 * a * b * b + b * b * b := by
  have hsq : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
    have h1 : a * b = b * a := Nat.mul_comm a b
    have h2 : 2 * a * b = a * b + a * b := by rw [Nat.two_mul, Nat.add_mul]
    omega
  rw [hsq, Nat.add_mul, Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_add]
  have t1 : 2 * a * b * a = 2 * (a * a * b) := by ac_rfl
  have t2 : 3 * a * a * b = a * a * b + 2 * (a * a * b) := by
    have : 3 * a * a * b = 3 * (a * a * b) := by ac_rfl
    omega
  have t3 : 2 * a * b * b = 2 * (a * b * b) := by ac_rfl
  have t4 : b * b * a = a * b * b := by ac_rfl
  have t5 : 3 * a * b * b = 2 * (a * b * b) + a * b * b := by
    have : 3 * a * b * b = 3 * (a * b * b) := by ac_rfl
    omega
  rw [t1, t3, t4]
  omega

theorem nat_halfCycle_even_bit (n k : Nat) (hk1 : 1 ≤ k) (heven : n % 2 = 0) :
    (n * n * n + 2 * n + 1).testBit (k + 1) =
      (((n % 2 ^ k) * (n % 2 ^ k) * (n % 2 ^ k) + 2 * (n % 2 ^ k) + 1).testBit (k + 1) ^^
        n.testBit k) := by
  let r := n % 2 ^ k
  let d := (n.testBit k).toNat
  let m := r + d * 2 ^ k
  have hm_eq : n % 2 ^ (k + 1) = m := nat_mod_two_pow_succ n k
  have hn_decomp : n = m + (n / 2 ^ (k + 1)) * 2 ^ (k + 1) := by
    have hdm := Nat.div_add_mod n (2 ^ (k + 1))
    rw [hm_eq, Nat.mul_comm] at hdm
    omega
  have hr_even : 2 ∣ r := by
    have h2k : 2 ∣ 2 ^ k := by simpa using Nat.pow_dvd_pow 2 hk1
    have hrm : r % 2 = n % 2 := Nat.mod_mod_of_dvd n h2k
    exact Nat.dvd_of_mod_eq_zero (hrm.trans heven)
  have hm_even : 2 ∣ m := by
    rcases hr_even with ⟨r', hr'⟩
    have h2k : 2 ∣ 2 ^ k := by simpa using Nat.pow_dvd_pow 2 hk1
    rcases h2k with ⟨p, hp⟩
    refine ⟨r' + d * p, ?_⟩
    show r + d * 2 ^ k = 2 * (r' + d * p)
    rw [hr', hp, Nat.mul_add]; ac_rfl
  -- Step 1: n^3 + 2n + 1 ≡ m^3 + 2m + 1 (mod 2^(k+2))
  have hstep1 : (n * n * n + 2 * n + 1) % 2 ^ (k + 2) =
      (m * m * m + 2 * m + 1) % 2 ^ (k + 2) := by
    let q := n / 2 ^ (k + 1)
    let M := 2 ^ (k + 1)
    have hM2 : 2 ^ (k + 2) = 2 * M := by
      show 2 ^ ((k + 1) + 1) = 2 * 2 ^ (k + 1)
      rw [Nat.pow_succ, Nat.mul_comm]
    rcases hm_even with ⟨m', hm'⟩
    have hMpow : M * M = 2 * 2 ^ (2 * k + 1) := by
      show 2 ^ (k + 1) * 2 ^ (k + 1) = 2 * 2 ^ (2 * k + 1)
      rw [← Nat.pow_add]
      have he : (k + 1) + (k + 1) = (2 * k + 1) + 1 := by omega
      rw [he, Nat.pow_succ, Nat.mul_comm]
    have hcube : (m + q * M) * (m + q * M) * (m + q * M) + 2 * (m + q * M) + 1 =
        (m * m * m + 2 * m + 1) +
        (2 * M) * (6 * m' * m' * q + 3 * m' * q * q * M + q * q * q * (2 ^ (2 * k + 1)) + q) := by
      rw [nat_cube_expand m (q * M), Nat.mul_add 2 m (q * M)]
      have p1 : 3 * m * m * (q * M) = (2 * M) * (6 * m' * m' * q) := by
        rw [hm']
        have h12 : 3 * 2 * 2 = 2 * 6 := rfl
        calc 3 * (2 * m') * (2 * m') * (q * M)
            = (3 * 2 * 2) * (m' * m' * q * M) := by ac_rfl
          _ = (2 * 6) * (m' * m' * q * M) := by rw [h12]
          _ = (2 * M) * (6 * m' * m' * q) := by ac_rfl
      have p2 : 3 * m * (q * M) * (q * M) = (2 * M) * (3 * m' * q * q * M) := by
        rw [hm']; ac_rfl
      have p3 : q * M * (q * M) * (q * M) = (2 * M) * (q * q * q * 2 ^ (2 * k + 1)) := by
        calc q * M * (q * M) * (q * M)
            = (M * M) * (M * q * q * q) := by ac_rfl
          _ = (2 * 2 ^ (2 * k + 1)) * (M * q * q * q) := by rw [hMpow]
          _ = (2 * M) * (q * q * q * 2 ^ (2 * k + 1)) := by ac_rfl
      have p4 : 2 * (q * M) = (2 * M) * q := by ac_rfl
      rw [p1, p2, p3, p4]
      rw [Nat.mul_add (2 * M), Nat.mul_add (2 * M), Nat.mul_add (2 * M)]
      omega
    have hne : n = m + q * M := hn_decomp
    rw [hne, hcube, ← hM2, Nat.add_mul_mod_self_left]
  -- Step 2: m^3 + 2m + 1 ≡ (r^3 + 2r + 1) + d * 2^(k+1) (mod 2^(k+2))
  have hstep2 : (m * m * m + 2 * m + 1) % 2 ^ (k + 2) =
      ((r * r * r + 2 * r + 1) + d * 2 ^ (k + 1)) % 2 ^ (k + 2) := by
    let K := 2 ^ k
    have hK2 : 2 ^ (k + 1) = 2 * K := by rw [Nat.pow_succ, Nat.mul_comm]
    have hK4 : 2 ^ (k + 2) = 4 * K := by
      show 2 ^ ((k + 1) + 1) = 4 * 2 ^ k
      rw [Nat.pow_succ, Nat.pow_succ]; omega
    rcases hr_even with ⟨r', hr'⟩
    have hK_even : 2 ∣ K := by simpa [K] using Nat.pow_dvd_pow 2 hk1
    rcases hK_even with ⟨K', hK'⟩
    have hK_sq : K * K = 4 * (K' * K') := by
      have h4 : 2 * 2 = 4 := rfl
      calc K * K = (2 * K') * (2 * K') := by rw [hK']
        _ = (2 * 2) * (K' * K') := by ac_rfl
        _ = 4 * (K' * K') := by rw [h4]
    have hm_cube : m * m * m + 2 * m + 1 =
        (r * r * r + 2 * r + 1 + d * 2 ^ (k + 1)) +
        (4 * K) * (3 * r' * r' * d + 3 * r' * d * d * K' + d * d * d * (K' * K')) := by
      show (r + d * K) * (r + d * K) * (r + d * K) + 2 * (r + d * K) + 1 = _
      rw [nat_cube_expand r (d * K)]
      have h2m : 2 * (r + d * K) = 2 * r + d * 2 ^ (k + 1) := by
        rw [Nat.mul_add, hK2]; ac_rfl
      have q1 : 3 * r * r * (d * K) = (4 * K) * (3 * r' * r' * d) := by
        rw [hr']
        have h4 : 2 * 2 = 4 := rfl
        calc 3 * (2 * r') * (2 * r') * (d * K)
            = (2 * 2) * (K * 3 * r' * r' * d) := by ac_rfl
          _ = 4 * (K * 3 * r' * r' * d) := by rw [h4]
          _ = (4 * K) * (3 * r' * r' * d) := by ac_rfl
      have q2 : 3 * r * (d * K) * (d * K) = (4 * K) * (3 * r' * d * d * K') := by
        have h4 : 2 * 2 = 4 := rfl
        calc 3 * r * (d * K) * (d * K)
            = 3 * (2 * r') * (d * K) * (d * (2 * K')) := by rw [hr', ← hK']
          _ = (2 * 2) * (K * 3 * r' * d * d * K') := by ac_rfl
          _ = 4 * (K * 3 * r' * d * d * K') := by rw [h4]
          _ = (4 * K) * (3 * r' * d * d * K') := by ac_rfl
      have q3 : d * K * (d * K) * (d * K) = (4 * K) * (d * d * d * (K' * K')) := by
        calc d * K * (d * K) * (d * K)
            = (K * K) * (K * d * d * d) := by ac_rfl
          _ = (4 * (K' * K')) * (K * d * d * d) := by rw [hK_sq]
          _ = (4 * K) * (d * d * d * (K' * K')) := by ac_rfl
      rw [h2m, q1, q2, q3, Nat.mul_add (4 * K), Nat.mul_add (4 * K)]
      omega
    rw [hm_cube, ← hK4, Nat.add_mul_mod_self_left]
  -- Extract bit `k + 1` from the congruence mod `2^(k+2)`
  have hmod_all : (n * n * n + 2 * n + 1) % 2 ^ (k + 2) =
      ((r * r * r + 2 * r + 1) + d * 2 ^ (k + 1)) % 2 ^ (k + 2) :=
    hstep1.trans hstep2
  have htb : (n * n * n + 2 * n + 1).testBit (k + 1) =
      ((r * r * r + 2 * r + 1) + d * 2 ^ (k + 1)).testBit (k + 1) := by
    have hlt : k + 1 < k + 2 := Nat.lt_succ_self (k + 1)
    have h1 := Nat.testBit_mod_two_pow (n * n * n + 2 * n + 1) (k + 2) (k + 1)
    have h2 := Nat.testBit_mod_two_pow ((r * r * r + 2 * r + 1) + d * 2 ^ (k + 1)) (k + 2) (k + 1)
    rw [hmod_all] at h1
    simp only [hlt, decide_true, Bool.true_and] at h1 h2
    rw [← h1, h2]
  rw [htb, ← nat_div_two_pow_mod_two,
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos (k + 1)),
      ← nat_div_two_pow_mod_two]
  change ((((r * r * r + 2 * r + 1) / 2 ^ (k + 1)) + (n.testBit k).toNat) % 2 == 1) =
    ((((r * r * r + 2 * r + 1) / 2 ^ (k + 1)) % 2 == 1) ^^ n.testBit k)
  rw [Nat.add_mod]
  cases Nat.mod_two_eq_zero_or_one ((r * r * r + 2 * r + 1) / 2 ^ (k + 1)) with
  | inl h => rw [h]; cases n.testBit k <;> rfl
  | inr h => rw [h]; cases n.testBit k <;> rfl

theorem mapHalfCycle_even_steps_v2 {w k : Nat} (hk1 : 1 ≤ k) (hkw : k + 1 < w)
    {x y : BitVec w} (heven : x.getLsbD 0 = false) (hv : v2Exact k x y) :
    v2Exact (k + 1) (mapHalfCycle.eval x) (mapHalfCycle.eval y) := by
  refine ⟨?_, ?_⟩
  · have hPx : isEven1 (BitVec.setWidth 1 x) = true := by
      unfold isEven1
      have h0 : BitVec.setWidth 1 x = 0#1 := by
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        have hi0 : i = 0 := by omega
        subst hi0
        rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_zero]
        simp [heven]
      rw [h0]; rfl
    exact mapHalfCycle_contractingOn_even hk1 (by omega) x y hPx hv.1
  · have h2m : 2 % 2 ^ w = 2 := Nat.mod_eq_of_lt (by
      have hle : 2 ^ 2 ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (by omega); omega)
    have h1m : 1 % 2 ^ w = 1 := Nat.mod_eq_of_lt (by
      have hle : 2 ^ 2 ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (by omega); omega)
    have htoNat : ∀ z : BitVec w,
        (mapHalfCycle.eval z).toNat = (z.toNat * z.toNat * z.toNat + 2 * z.toNat + 1) % 2 ^ w := by
      intro z
      simp only [mapHalfCycle, BPoly.eval, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
        h2m, h1m]
      simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
    have hbit_x : (mapHalfCycle.eval x).getLsbD (k + 1) =
        (x.toNat * x.toNat * x.toNat + 2 * x.toNat + 1).testBit (k + 1) := by
      rw [BitVec.getLsbD, htoNat x, Nat.testBit_mod_two_pow]
      simp only [hkw, decide_true, Bool.true_and]
    have hbit_y : (mapHalfCycle.eval y).getLsbD (k + 1) =
        (y.toNat * y.toNat * y.toNat + 2 * y.toNat + 1).testBit (k + 1) := by
      rw [BitVec.getLsbD, htoNat y, Nat.testBit_mod_two_pow]
      simp only [hkw, decide_true, Bool.true_and]
    have hmod_eq : x.toNat % 2 ^ k = y.toNat % 2 ^ k := by
      have := congrArg BitVec.toNat hv.1
      simpa [BitVec.toNat_setWidth] using this
    have hx_ev : x.toNat % 2 = 0 := by
      have h0 := nat_div_two_pow_mod_two x.toNat 0
      simp only [Nat.pow_zero, Nat.div_one] at h0
      have : x.toNat.testBit 0 = false := heven
      rw [this] at h0
      have hne : x.toNat % 2 ≠ 1 := by simpa using h0
      have hlt := Nat.mod_lt x.toNat (by omega : 0 < 2)
      omega
    have hy_ev : y.toNat % 2 = 0 := by
      have h2k : 2 ∣ 2 ^ k := by simpa using Nat.pow_dvd_pow 2 hk1
      have := congrArg (· % 2) hmod_eq
      rw [Nat.mod_mod_of_dvd _ h2k, Nat.mod_mod_of_dvd _ h2k] at this
      exact this.symm.trans hx_ev
    rw [hbit_x, hbit_y,
        nat_halfCycle_even_bit x.toNat k hk1 hx_ev,
        nat_halfCycle_even_bit y.toNat k hk1 hy_ev,
        hmod_eq]
    have hne : x.toNat.testBit k ≠ y.toNat.testBit k := hv.2
    generalize ((y.toNat % 2 ^ k) * (y.toNat % 2 ^ k) * (y.toNat % 2 ^ k) +
      2 * (y.toNat % 2 ^ k) + 1).testBit (k + 1) = base
    cases base <;> cases hx1 : x.toNat.testBit k <;> cases hy1 : y.toNat.testBit k <;> simp_all

/-- **Exact Super-Linear Depth Sharpness (`depth = 2w - 2` for ALL `w ≥ 2`):**
    For `f(x) = x^3 + 2x + 1`, starting at `3#w`, step `2w - 3` is NOT yet on the 2-cycle,
    while step `2w - 2` IS on the 2-cycle! Strictly exceeds `w` for all `w ≥ 3`. -/
theorem mapHalfCycle_depth_exact_sharp (w : Nat) (hw : 2 ≤ w) :
    iter mapHalfCycle.eval 2 (iter mapHalfCycle.eval (2 * w - 3) 3#w) ≠
      iter mapHalfCycle.eval (2 * w - 3) 3#w ∧
    iter mapHalfCycle.eval 2 (iter mapHalfCycle.eval (2 * w - 2) 3#w) =
      iter mapHalfCycle.eval (2 * w - 2) 3#w := by
  have h1 : 1 ≤ w := by omega
  have hupper : iter mapHalfCycle.eval 2 (iter mapHalfCycle.eval (2 * w - 2) 3#w) =
      iter mapHalfCycle.eval (2 * w - 2) 3#w := by
    have heq : 2 * w - 2 = 2 * (w - 1) := by omega
    rw [heq]
    exact mapHalfCycle_depth_le w h1 3#w
  refine ⟨?_, hupper⟩
  let p1 : BitVec w := henselLift (fun _ => mapHalfCycle.eval) 1 2 1 w 1#1
  let p0 : BitVec w := mapHalfCycle.eval p1
  have hp1_per : iter mapHalfCycle.eval 2 p1 = p1 := by
    have hc1 : cycleContractionCount (fun _ => mapHalfCycle.eval) 1 isEven1 1#1 2 = 1 := by decide
    have h := henselLift_periodic mapHalfCycle.isTFunc mapHalfCycle_contractingOn_even
      1#1 (L := 2) (by decide) (by rw [hc1]; omega) h1
    simpa [p1, hc1] using h
  have hp1_m1 : BitVec.setWidth 1 p1 = 1#1 :=
    henselLift_setWidth mapHalfCycle.isTFunc h1 1#1 (L := 2) (by decide)
  have hp0_per : iter mapHalfCycle.eval 2 p0 = p0 := by
    change iter mapHalfCycle.eval 2 (mapHalfCycle.eval p1) = mapHalfCycle.eval p1
    rw [← iter_succ_apply, iter_succ, hp1_per]
  have hp0_m1 : BitVec.setWidth 1 p0 = 0#1 := by
    change BitVec.setWidth 1 (mapHalfCycle.eval p1) = 0#1
    rw [mapHalfCycle.eval_setWidth h1, hp1_m1]; decide
  -- Identify `setWidth 2 p1 = 1#2` by uniqueness of 2-periodic points mod 2!
  have hp1_m2 : BitVec.setWidth 2 p1 = 1#2 := by
    have h2per : iter mapHalfCycle.eval 2 (BitVec.setWidth 2 p1) = BitVec.setWidth 2 p1 := by
      rw [← IsTFunc.iter_setWidth mapHalfCycle.isTFunc hw, hp1_per]
    have h2m1 : BitVec.setWidth 1 (BitVec.setWidth 2 p1) = 1#1 := by
      rw [BitVec.setWidth_setWidth_of_le _ (by omega), hp1_m1]
    have h12_per : iter mapHalfCycle.eval 2 1#2 = 1#2 := by decide
    have h12_m1 : BitVec.setWidth 1 1#2 = 1#1 := by decide
    have hu1 := henselLift_unique mapHalfCycle.isTFunc mapHalfCycle_contractingOn_even
      1#1 (L := 2) (by decide) (by decide) (w := 2) (by omega) (BitVec.setWidth 2 p1) h2m1 h2per
    have hu2 := henselLift_unique mapHalfCycle.isTFunc mapHalfCycle_contractingOn_even
      1#1 (L := 2) (by decide) (by decide) (w := 2) (by omega) 1#2 h12_m1 h12_per
    exact hu1.trans hu2.symm
  -- Base case at j = 0: `v2Exact 1 (3#w) p1` and `(3#w).getLsbD 0 = true`
  have hbase_v2 : v2Exact 1 3#w p1 := by
    refine ⟨?_, ?_⟩
    · rw [setWidth_ofNat_le h1 3, hp1_m1]; decide
    · have h3_1 : (3#w).getLsbD 1 = true := by
        rw [BitVec.getLsbD_ofNat]; simp [show 1 < w by omega]; decide
      have hp1_1 : p1.getLsbD 1 = false := by
        have hbit := congrArg (fun v => v.getLsbD 1) hp1_m2
        rw [BitVec.getLsbD_setWidth] at hbit
        simp only [show 1 < 2 by omega, decide_true, Bool.true_and] at hbit
        exact hbit.trans (by decide)
      rw [h3_1, hp1_1]; decide
  have hbase_odd : (3#w).getLsbD 0 = true := by
    rw [BitVec.getLsbD_ofNat]; simp [show 0 < w by omega]
  -- Induction on j ≤ w - 2:
  have hind : ∀ j, j ≤ w - 2 →
      v2Exact (j + 1) (iter mapHalfCycle.eval (2 * j) 3#w) p1 ∧
      (iter mapHalfCycle.eval (2 * j) 3#w).getLsbD 0 = true ∧
      v2Exact (j + 1) (iter mapHalfCycle.eval (2 * j + 1) 3#w) p0 ∧
      (iter mapHalfCycle.eval (2 * j + 1) 3#w).getLsbD 0 = false := by
    intro j hj
    induction j with
    | zero =>
      have hodd_step := mapHalfCycle_odd_preserves_v2 (by omega) (by omega) hbase_odd hbase_v2
      have h0_ev : (mapHalfCycle.eval 3#w).getLsbD 0 = false := by
        rw [mapHalfCycle.eval_getLsbD_zero (by omega), hbase_odd]; rfl
      exact ⟨hbase_v2, hbase_odd, hodd_step, h0_ev⟩
    | succ j ih =>
      have ⟨_, _, hv_odd, hev_odd⟩ := ih (by omega)
      have heven_step := mapHalfCycle_even_steps_v2 (by omega) (by omega) hev_odd hv_odd
      have h2j2 : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
      have hfp0 : mapHalfCycle.eval p0 = p1 := hp1_per
      have hv_even' : v2Exact (j + 2) (iter mapHalfCycle.eval (2 * (j + 1)) 3#w) p1 := by
        rw [h2j2, iter_succ, ← hfp0]; exact heven_step
      have hodd_next : (iter mapHalfCycle.eval (2 * (j + 1)) 3#w).getLsbD 0 = true := by
        rw [h2j2, iter_succ, mapHalfCycle.eval_getLsbD_zero (by omega), hev_odd]; rfl
      have hodd_step := mapHalfCycle_odd_preserves_v2 (by omega) (by omega) hodd_next hv_even'
      have hev_next : (iter mapHalfCycle.eval (2 * (j + 1) + 1) 3#w).getLsbD 0 = false := by
        rw [iter_succ, mapHalfCycle.eval_getLsbD_zero (by omega), hodd_next]; rfl
      exact ⟨hv_even', hodd_next, hodd_step, hev_next⟩
  have ⟨_, _, hv_last, hev_last⟩ := hind (w - 2) (Nat.le_refl _)
  have ht_eq : 2 * (w - 2) + 1 = 2 * w - 3 := by omega
  have hk_eq : (w - 2) + 1 = w - 1 := by omega
  rw [ht_eq, hk_eq] at hv_last
  rw [ht_eq] at hev_last
  intro hper_last
  -- If `y = iter f (2w-3) 3#w` were 2-periodic and even, uniqueness forces `y = p0`, contradicting `hv_last.2`!
  let y := iter mapHalfCycle.eval (2 * w - 3) 3#w
  have hym1 : BitVec.setWidth 1 y = 0#1 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_zero]
    simp [y, hev_last]
  have hy_eq : y = henselLift (fun _ => mapHalfCycle.eval) 1 2 1 w 0#1 :=
    henselLift_unique mapHalfCycle.isTFunc mapHalfCycle_contractingOn_even
      0#1 (L := 2) (by decide) (by decide) h1 y hym1 hper_last
  have hp0_eq : p0 = henselLift (fun _ => mapHalfCycle.eval) 1 2 1 w 0#1 :=
    henselLift_unique mapHalfCycle.isTFunc mapHalfCycle_contractingOn_even
      0#1 (L := 2) (by decide) (by decide) h1 p0 hp0_m1 hp0_per
  have hyeqp0 : y = p0 := hy_eq.trans hp0_eq.symm
  exact hv_last.2 (congrArg (fun v => v.getLsbD (w - 1)) hyeqp0)

/-! ### Sharpness Counterexamples (Kernel-Checked) -/

theorem counterexample_isometric_drops_fixedPoint :
    bvCount 1 (isFixedPointB (fun _ => mapMixedIso.eval) 1) = 2 ∧
    bvCount 2 (isFixedPointB (fun _ => mapMixedIso.eval) 2) = 1 := by
  decide

/-- Yet on the contracting even class, `mapMixedIso` STILL has a unique even fixed point `0#w`
    with exact basin size `2^(w - 1)` for all `w ≥ 1`! -/
theorem mapMixedIso_even_basin (w : Nat) (hw : 1 ≤ w) (x : BitVec w)
    (heven : BitVec.setWidth 1 x = 0#1) :
    iter mapMixedIso.eval (w - 1) x = 0#w := by
  have hC : IsContractingOn (fun _ => mapMixedIso.eval) 1 isEven1 :=
    mapMixedIso.isContractingOn_of_check 1 (by omega) isEven1 (by decide)
  have hconv := fixedPoint_convergence_depth mapMixedIso.isTFunc hC 0#1
    (by decide) rfl hw x 0 heven
  have hlift : henselLift (fun _ => mapMixedIso.eval) 1 1 1 w 0#1 = 0#w := by
    have h0fix : iter mapMixedIso.eval 1 (0#w) = 0#w := by
      simp [iter, mapMixedIso, BPoly.eval]
    have hc1 : cycleContractionCount (fun _ => mapMixedIso.eval) 1 isEven1 0#1 1 = 1 := by decide
    have hu := henselLift_unique mapMixedIso.isTFunc hC 0#1 (L := 1) (by decide)
      (by rw [hc1]; omega) hw 0#w
      (by apply BitVec.eq_of_getLsbD_eq; intro i hi; simp) h0fix
    simpa [hc1] using hu.symm
  simpa [hlift] using hconv

/-- Counterexample 2: For `mapAsym = (x & 4) | (x * x)`, checking at `w = 2` is below
    the contraction threshold `m = 3` and gives the wrong fixed-point count (`2 ≠ 4`). -/
theorem counterexample_below_threshold :
    bvCount 2 (isFixedPointB (fun _ => mapAsym.eval) 2) = 2 ∧
    bvCount 3 (isFixedPointB (fun _ => mapAsym.eval) 3) = 4 := by
  decide

/-- Counterexample 3: Right shift `x >>> 1` is NOT a T-function (fails `setWidth` commutation). -/
theorem counterexample_shr_not_tfunc :
    ¬ IsTFunc (fun _ x => x >>> 1) := by
  intro h
  have hbad := h (w := 2) (k := 1) (by omega) 2#2
  revert hbad
  decide

theorem counterexample_cycle_exceeds_width :
    IsContractingOn (fun _ => mapCycle4.eval) 3 (fun _ => true) ∧
    iter mapCycle4.eval 4 (iter mapCycle4.eval 3 3#3) ≠ iter mapCycle4.eval 3 3#3 ∧
    iter mapCycle4.eval 4 (iter mapCycle4.eval 4 3#3) = iter mapCycle4.eval 4 3#3 := by
  refine ⟨mapCycle4.isContractingGlobal_of_absDeriv 3 (by omega) rfl rfl, ?_, ?_⟩ <;> decide

/-! ### Kernel-Checked Negative / Mutation Certificate Tests -/

theorem negative_certs_rejected :
    mapMixedIso.checkContractingOn 1 (fun _ => true) = false ∧
    mapAsym.checkContractingOn 2 (fun _ => true) = false ∧
    mapHalfCycle.checkContractingOn 1 (fun _ => true) = false ∧
    checkAllReachFixed (fun _ => mapAsym.eval) 3 0 = false ∧
    checkAllReachFixed (fun _ => mapThree.eval) 3 1 = false ∧
    checkAllReachFixed (fun _ => mapHalfCycle.eval) 1 5 = false ∧
    checkPeriodicContracting (fun _ => mapMixedIso.eval) 1 1 isEven1 = false := by
  decide

end HenselSilicon
