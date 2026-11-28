import Defs

namespace SiliconRacksQuandles

/-! ## Section 1: Pure-Init BitVec Single-Bit & Low-Mask Lemmas -/

private theorem getLsbD_eq_testBit {w : Nat} (x : BitVec w) (i : Nat) :
    x.getLsbD i = x.toNat.testBit i :=
  (BitVec.testBit_toNat x).symm

private theorem singleBit_toNat {w : Nat} (k : Nat) (hk : k < w) :
    ((1#w : BitVec w) <<< k).toNat = 2 ^ k := by
  have h1lt : 1 % 2 ^ w = 1 := Nat.mod_eq_of_lt (by
    have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ w); omega)
  have h2lt : 2 ^ k < 2 ^ w := Nat.pow_lt_pow_right (by omega) hk
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, h1lt, Nat.shiftLeft_eq, Nat.one_mul,
    Nat.mod_eq_of_lt h2lt]

private theorem add_singleBit_eq_two_pow {w : Nat} (k : Nat) (hk : k < w) :
    ((1#w : BitVec w) <<< k) + ((1#w : BitVec w) <<< k) = (1#w <<< (k + 1)) := by
  apply BitVec.eq_of_toNat_eq
  have h1lt : 1 % 2 ^ w = 1 := Nat.mod_eq_of_lt (by
    have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ w); omega)
  rw [BitVec.toNat_add, singleBit_toNat k hk, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, h1lt,
    Nat.shiftLeft_eq, Nat.one_mul, Nat.pow_succ]
  congr 1; omega

private theorem add_multiple_preserves_low_bits {w : Nat} (s : Nat) (hs : s < w)
    (a b : BitVec w) (hb : ∃ q : Nat, b.toNat = q * 2 ^ s) :
    ∀ i, i < s → (a + b).getLsbD i = a.getLsbD i := by
  rcases hb with ⟨q, hq⟩
  intro i hi
  have hiw : i < w := by omega
  rw [getLsbD_eq_testBit, getLsbD_eq_testBit, BitVec.toNat_add]
  have hdvd : 2 ^ s ∣ 2 ^ w := Nat.pow_dvd_pow 2 (by omega)
  have hmod : (a.toNat + b.toNat) % 2 ^ w % 2 ^ s = a.toNat % 2 ^ s := by
    rw [Nat.mod_mod_of_dvd _ hdvd, hq, Nat.add_mul_mod_self_right]
  have htb := congrArg (fun n => n.testBit i) hmod
  simp only [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and] at htb
  rw [Nat.testBit_mod_two_pow]
  exact htb

private theorem sub_multiple_preserves_low_bits {w : Nat} (s : Nat) (hs : s < w)
    (a b : BitVec w) (hb : ∃ q : Nat, b.toNat = q * 2 ^ s) :
    ∀ i, i < s → (a - b).getLsbD i = a.getLsbD i := by
  intro i hi
  have hsum : (a - b) + b = a := by grind
  have h := add_multiple_preserves_low_bits s hs (a - b) b hb i hi
  rw [hsum] at h
  exact h.symm

private theorem add_two_pow_k_flips_bit {w : Nat} (k : Nat) (hk : k < w) (a : BitVec w) :
    (a + (1#w <<< k)).getLsbD k = !(a.getLsbD k) := by
  rw [getLsbD_eq_testBit, getLsbD_eq_testBit, BitVec.toNat_add, singleBit_toNat k hk,
    Nat.testBit_mod_two_pow, decide_eq_true hk, Bool.true_and]
  have hdiv : (a.toNat + 2 ^ k) / 2 ^ k = a.toNat / 2 ^ k + 1 :=
    Nat.add_div_right a.toNat (Nat.two_pow_pos k)
  rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, hdiv]
  have h1 : ∀ n : Nat, ((1 &&& n) != 0) = decide (n % 2 = 1) := by
    intro n; rw [Nat.and_comm, Nat.and_one_is_mod]
    by_cases h : n % 2 = 1 <;> simp [h] <;> omega
  rw [h1, h1]
  by_cases h : (a.toNat / 2 ^ k) % 2 = 1
  · simp [h, show (a.toNat / 2 ^ k + 1) % 2 ≠ 1 by omega]
  · simp [h, show (a.toNat / 2 ^ k + 1) % 2 = 1 by omega]

private theorem sub_two_pow_k_flips_bit {w : Nat} (k : Nat) (hk : k < w) (a : BitVec w) :
    (a - (1#w <<< k)).getLsbD k = !(a.getLsbD k) := by
  have h := add_two_pow_k_flips_bit k hk (a - (1#w <<< k))
  have hsum : (a - (1#w <<< k)) + (1#w <<< k) = a := by grind
  rw [hsum] at h
  cases hb : (a - (1#w <<< k)).getLsbD k <;> rw [hb] at h <;> simp [h]

private theorem xor_singleBit_eq {w : Nat} (k : Nat) (hk : k < w) (a : BitVec w) :
    a ^^^ (1#w <<< k) =
      if a.getLsbD k then a - (1#w <<< k) else a + (1#w <<< k) := by
  by_cases hbit : a.getLsbD k = true
  · simp only [hbit, ↓reduceIte]
    -- Show `(a ^^^ c) + c = a` when `a.getLsbD k = true`!
    have hsum : (a ^^^ (1#w <<< k)) + (1#w <<< k) = a := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_xor, singleBit_toNat k hk]
      have hdiv_odd : (a.toNat / 2 ^ k) % 2 = 1 := by
        rw [getLsbD_eq_testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_comm,
          Nat.and_one_is_mod] at hbit
        by_cases h1 : (a.toNat / 2 ^ k) % 2 = 1
        · exact h1
        · simp [show (a.toNat / 2 ^ k) % 2 = 0 by omega] at hbit
      have hge : 2 ^ k ≤ a.toNat := by
        have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
        have h1 : 1 ≤ a.toNat / 2 ^ k := by
          generalize a.toNat / 2 ^ k = q at hdiv_odd; omega
        have hmul := (Nat.le_div_iff_mul_le hpos).mp h1
        rw [Nat.one_mul] at hmul
        exact hmul
      have hxor_sub : a.toNat ^^^ 2 ^ k = a.toNat - 2 ^ k := by
        -- Show `(a.toNat - 2^k) + 2^k = a.toNat` and `(a.toNat - 2^k) ^^^ 2^k = a.toNat`
        have hadd_eq_xor : ∀ u, u.testBit k = false → u + 2 ^ k = u ^^^ 2 ^ k := by
          intro u hu
          have hdisj : (u &&& 2 ^ k) = 0 := by
            apply Nat.eq_of_testBit_eq; intro j
            rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
            by_cases hjk : k = j
            · subst hjk; simp [hu]
            · simp [hjk]
          -- Standard `u + v = (u ^^^ v) + 2 * (u &&& v)` via strong recursion on `u`:
          have hadd_and : ∀ x y : Nat, x + y = (x ^^^ y) + 2 * (x &&& y) := by
            intro x
            induction x using Nat.strongRecOn with
            | ind x ih =>
              intro y
              by_cases hx : x = 0
              · subst hx; simp
              · have hlt : x / 2 < x := Nat.div_lt_self (Nat.pos_of_ne_zero hx) (by omega)
                have ih' := ih (x / 2) hlt (y / 2)
                have hxd : (x ^^^ y) / 2 = x / 2 ^^^ y / 2 := by
                  apply Nat.eq_of_testBit_eq; intro j
                  rw [← Nat.testBit_succ, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ]
                have had : (x &&& y) / 2 = x / 2 &&& y / 2 := by
                  apply Nat.eq_of_testBit_eq; intro j
                  rw [← Nat.testBit_succ, Nat.testBit_and, Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ]
                have hbit0 : x % 2 + y % 2 = (x ^^^ y) % 2 + 2 * ((x &&& y) % 2) := by
                  have htb1 : (x ^^^ y).testBit 0 = (x.testBit 0 ^^ y.testBit 0) := Nat.testBit_xor x y 0
                  have htb2 : (x &&& y).testBit 0 = (x.testBit 0 && y.testBit 0) := Nat.testBit_and x y 0
                  simp only [Nat.testBit_zero] at htb1 htb2
                  have hx2 : x % 2 = 0 ∨ x % 2 = 1 := by omega
                  have hy2 : y % 2 = 0 ∨ y % 2 = 1 := by omega
                  rcases hx2 with hx2 | hx2 <;> rcases hy2 with hy2 | hy2 <;>
                    (rw [hx2, hy2] at htb1 htb2;
                     by_cases h1 : (x ^^^ y) % 2 = 1 <;> by_cases h2 : (x &&& y) % 2 = 1 <;>
                      (simp [h1, h2] at htb1 htb2; try omega))
                have h1 := Nat.div_add_mod x 2
                have h2 := Nat.div_add_mod y 2
                have h3 := Nat.div_add_mod (x ^^^ y) 2
                have h4 := Nat.div_add_mod (x &&& y) 2
                rw [hxd] at h3; rw [had] at h4
                omega
          have h := hadd_and u (2 ^ k)
          rw [hdisj] at h; omega
        have hsub_bit : (a.toNat - 2 ^ k).testBit k = false := by
          have hdiv : (a.toNat - 2 ^ k) / 2 ^ k = a.toNat / 2 ^ k - 1 := by
            have h1 : a.toNat = (a.toNat - 2 ^ k) + 2 ^ k := by omega
            have h2 := Nat.add_div_right (a.toNat - 2 ^ k) (Nat.two_pow_pos k)
            rw [← h1] at h2
            generalize (a.toNat - 2 ^ k) / 2 ^ k = r at h2 ⊢
            omega
          rw [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv, Nat.and_comm, Nat.and_one_is_mod]
          have hsub_even : (a.toNat / 2 ^ k - 1) % 2 = 0 := by
            generalize a.toNat / 2 ^ k = q at hdiv_odd; omega
          rw [hsub_even]; rfl
        have h1 := hadd_eq_xor (a.toNat - 2 ^ k) hsub_bit
        have h2 : (a.toNat - 2 ^ k) + 2 ^ k = a.toNat := by omega
        rw [h2] at h1
        calc a.toNat ^^^ 2 ^ k
            = ((a.toNat - 2 ^ k) ^^^ 2 ^ k) ^^^ 2 ^ k := by rw [← h1]
          _ = a.toNat - 2 ^ k := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      rw [hxor_sub, show a.toNat - 2 ^ k + 2 ^ k = a.toNat by omega, Nat.mod_eq_of_lt a.isLt]
    grind
  · have hbitf : a.getLsbD k = false := by cases h : a.getLsbD k <;> simp [h] at hbit ⊢
    simp only [hbitf, Bool.false_eq_true, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_xor, BitVec.toNat_add, singleBit_toNat k hk]
    have hdisj : (a.toNat &&& 2 ^ k) = 0 := by
      apply Nat.eq_of_testBit_eq; intro j
      rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases hjk : k = j
      · subst hjk; rw [← getLsbD_eq_testBit, hbitf]; rfl
      · simp [hjk]
    have hadd_and : ∀ x y : Nat, x + y = (x ^^^ y) + 2 * (x &&& y) := by
      intro x
      induction x using Nat.strongRecOn with
      | ind x ih =>
        intro y
        by_cases hx : x = 0
        · subst hx; simp
        · have hlt : x / 2 < x := Nat.div_lt_self (Nat.pos_of_ne_zero hx) (by omega)
          have ih' := ih (x / 2) hlt (y / 2)
          have hxd : (x ^^^ y) / 2 = x / 2 ^^^ y / 2 := by
            apply Nat.eq_of_testBit_eq; intro j
            rw [← Nat.testBit_succ, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ]
          have had : (x &&& y) / 2 = x / 2 &&& y / 2 := by
            apply Nat.eq_of_testBit_eq; intro j
            rw [← Nat.testBit_succ, Nat.testBit_and, Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ]
          have hbit0 : x % 2 + y % 2 = (x ^^^ y) % 2 + 2 * ((x &&& y) % 2) := by
            have htb1 : (x ^^^ y).testBit 0 = (x.testBit 0 ^^ y.testBit 0) := Nat.testBit_xor x y 0
            have htb2 : (x &&& y).testBit 0 = (x.testBit 0 && y.testBit 0) := Nat.testBit_and x y 0
            simp only [Nat.testBit_zero] at htb1 htb2
            have hx2 : x % 2 = 0 ∨ x % 2 = 1 := by omega
            have hy2 : y % 2 = 0 ∨ y % 2 = 1 := by omega
            rcases hx2 with hx2 | hx2 <;> rcases hy2 with hy2 | hy2 <;>
              (rw [hx2, hy2] at htb1 htb2;
               by_cases h1 : (x ^^^ y) % 2 = 1 <;> by_cases h2 : (x &&& y) % 2 = 1 <;>
                (simp [h1, h2] at htb1 htb2; try omega))
          have h1 := Nat.div_add_mod x 2
          have h2 := Nat.div_add_mod y 2
          have h3 := Nat.div_add_mod (x ^^^ y) 2
          have h4 := Nat.div_add_mod (x &&& y) 2
          rw [hxd] at h3; rw [had] at h4
          omega
    have hsum : a.toNat + 2 ^ k = a.toNat ^^^ 2 ^ k := by
      have h := hadd_and a.toNat (2 ^ k); rw [hdisj] at h; omega
    have hlt : a.toNat ^^^ 2 ^ k < 2 ^ w :=
      Nat.xor_lt_two_pow a.isLt (Nat.pow_lt_pow_right (by omega) hk)
    rw [hsum, Nat.mod_eq_of_lt hlt]

/-! ## Section 2: Universal Coset-Shift & Single-Bit Carry-XOR Framed-Link Racks -/

theorem cosetRack_laws {w : Nat} (g : BitVec w → BitVec w)
    (hadd : ∀ d a, g (d + g a) = g d)
    (hsub : ∀ d a, g (d - g a) = g d) :
    (∀ x y, cosetRack g x (cosetRackInv g x y) = y) ∧
    (∀ x y, cosetRackInv g x (cosetRack g x y) = y) ∧
    (∀ x y z, cosetRack g x (cosetRack g y z) =
      cosetRack g (cosetRack g x y) (cosetRack g x z)) ∧
    ((∀ x, cosetRack g x x = x) ↔ g 0#w = 0#w) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    unfold cosetRack cosetRackInv
    have h1 : y - g (y - x) - x = (y - x) - g (y - x) := by grind
    rw [h1, hsub]
    grind
  · intro x y
    unfold cosetRack cosetRackInv
    have h1 : y + g (y - x) - x = (y - x) + g (y - x) := by grind
    rw [h1, hadd]
    grind
  · intro x y z
    unfold cosetRack
    have h1 : z + g (z - y) - x = (z - x) + g (z - y) := by grind
    have h2 : z + g (z - x) - (y + g (y - x)) = ((z - y) + g (z - x)) - g (y - x) := by grind
    rw [h1, hadd, h2, hsub, hadd]
    grind
  · constructor
    · intro h
      have h0 := h 0#w
      unfold cosetRack at h0
      grind
    · intro h0 x
      unfold cosetRack
      have hx : x - x = 0#w := by grind
      rw [hx, h0]
      grind

theorem carryXorRack_eq {w : Nat} (k : Nat) (hk : k < w) (x y : BitVec w) :
    carryXorRack k x y =
      y + (if (y - x).getLsbD k then 0#w else (1#w <<< (k + 1))) := by
  unfold carryXorRack
  rw [xor_singleBit_eq k hk (y - x)]
  have h2 := add_singleBit_eq_two_pow k hk
  cases (y - x).getLsbD k
  · simp only [Bool.false_eq_true, ↓reduceIte]
    grind
  · simp only [↓reduceIte]
    grind

theorem carryXorRack_framed_laws {w : Nat} (k : Nat) (hk : k + 1 < w) :
    (∀ x y : BitVec w, carryXorRack k x (y - (if (y - x).getLsbD k then 0#w else (1#w <<< (k + 1)))) = y) ∧
    (∀ x y : BitVec w, carryXorRack k x y - (if (carryXorRack k x y - x).getLsbD k then 0#w else (1#w <<< (k + 1))) = y) ∧
    (∀ x y z : BitVec w, carryXorRack k x (carryXorRack k y z) =
      carryXorRack k (carryXorRack k x y) (carryXorRack k x z)) ∧
    carryXorRack k 0#w 0#w ≠ 0#w ∧
    carryXorRack k (carryXorRack k 0#w 0#w) 0#w ≠
      carryXorRack k (carryXorRack k 0#w 0#w) (carryXorRack k 0#w 0#w) := by
  let g : BitVec w → BitVec w := fun d => if d.getLsbD k then 0#w else (1#w <<< (k + 1))
  have hg_mult : ∀ a, ∃ q : Nat, (g a).toNat = q * 2 ^ (k + 1) := by
    intro a
    dsimp only [g]
    cases a.getLsbD k
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨1, by rw [singleBit_toNat (k + 1) hk, Nat.one_mul]⟩
    · simp only [↓reduceIte]
      exact ⟨0, by simp⟩
  have hadd : ∀ d a, g (d + g a) = g d := by
    intro d a
    dsimp only [g]
    rw [add_multiple_preserves_low_bits (k + 1) hk d (g a) (hg_mult a) k (by omega)]
  have hsub : ∀ d a, g (d - g a) = g d := by
    intro d a
    dsimp only [g]
    rw [sub_multiple_preserves_low_bits (k + 1) hk d (g a) (hg_mult a) k (by omega)]
  have hlaws := cosetRack_laws g hadd hsub
  have heq : ∀ x y, carryXorRack k x y = cosetRack g x y :=
    fun x y => carryXorRack_eq k (by omega) x y
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y; rw [heq]; exact hlaws.1 x y
  · intro x y; rw [heq]; exact hlaws.2.1 x y
  · intro x y z; rw [heq, heq, heq, heq, heq]; exact hlaws.2.2.1 x y z
  · rw [heq]; unfold cosetRack; dsimp only [g]
    have h0 : (0#w - 0#w : BitVec w).getLsbD k = false := by simp
    rw [h0]; simp only [Bool.false_eq_true, ↓reduceIte, BitVec.zero_add]
    intro hzero
    have htn := congrArg BitVec.toNat hzero
    rw [singleBit_toNat (k + 1) hk, BitVec.toNat_ofNat, Nat.zero_mod] at htn
    have hpos : 0 < 2 ^ (k + 1) := Nat.two_pow_pos (k + 1)
    omega
  · intro hsame
    -- Check `carryXorRack k (carryXorRack k 0 0) 0 = 2^(k+1)` vs `carryXorRack k (2^(k+1)) (2^(k+1)) = 2^(k+2)`?
    -- Actually wait: at `k + 2 = w`, `2^(k+2) = 0`, whereas `2^(k+1) ≠ 0`, so ALWAYS `2^(k+1) ≠ 2^(k+1) + 2^(k+1)`!
    rw [heq, heq, heq] at hsame
    have h00 : cosetRack g 0#w 0#w = (1#w <<< (k + 1)) := by
      unfold cosetRack; dsimp only [g]
      have h0 : (0#w - 0#w : BitVec w).getLsbD k = false := by simp
      rw [h0]; simp
    rw [h00] at hsame
    have hlhs : cosetRack g (1#w <<< (k + 1)) 0#w = (1#w <<< (k + 1)) := by
      unfold cosetRack; dsimp only [g]
      have hbit : ((0#w : BitVec w) - (1#w <<< (k + 1))).getLsbD k = false := by
        have := sub_multiple_preserves_low_bits (k + 1) hk 0#w (1#w <<< (k + 1))
          ⟨1, by rw [singleBit_toNat (k + 1) hk, Nat.one_mul]⟩ k (by omega)
        simpa using this
      rw [hbit]; simp
    have hrhs : cosetRack g (1#w <<< (k + 1)) (1#w <<< (k + 1)) =
        (1#w <<< (k + 1)) + (1#w <<< (k + 1)) := by
      unfold cosetRack; dsimp only [g]
      have h0 : ((1#w <<< (k + 1)) - (1#w <<< (k + 1)) : BitVec w).getLsbD k = false := by simp
      rw [h0]; simp
    rw [hlhs, hrhs] at hsame
    have hzero : (1#w <<< (k + 1) : BitVec w) = 0#w := by grind
    have htn := congrArg BitVec.toNat hzero
    rw [singleBit_toNat (k + 1) hk, BitVec.toNat_ofNat, Nat.zero_mod] at htn
    have hpos : 0 < 2 ^ (k + 1) := Nat.two_pow_pos (k + 1)
    omega

/-! ## Section 3: Involutive Non-Idempotent Zero-Borrow Core-XOR Framed-Link Racks -/

private theorem lowMask_toNat {w : Nat} (k : Nat) (hk : k < w) :
    (lowMask w k).toNat = 2 ^ k - 1 := by
  unfold lowMask
  have h1lt : 1 % 2 ^ w = 1 := Nat.mod_eq_of_lt (by
    have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ w); omega)
  have hpow_pos : 1 ≤ 2 ^ k := Nat.two_pow_pos k
  have hlt : 2 ^ k < 2 ^ w := Nat.pow_lt_pow_right (by omega) hk
  rw [BitVec.toNat_sub, singleBit_toNat k hk, BitVec.toNat_ofNat, h1lt]
  have h1 : 2 ^ w - 1 + 2 ^ k = (2 ^ k - 1) + 2 ^ w := by omega
  rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

private theorem lowMask_getLsbD {w : Nat} (k : Nat) (hk : k < w) (i : Nat) :
    (lowMask w k).getLsbD i = decide (i < k) := by
  rw [getLsbD_eq_testBit, lowMask_toNat k hk]
  by_cases hik : i < k
  · simp only [decide_eq_true hik]
    have hdiv : (2 ^ k - 1) / 2 ^ i = 2 ^ (k - i) - 1 := by
      have hpow : 2 ^ k = 2 ^ i * 2 ^ (k - i) := by
        rw [← Nat.pow_add, show i + (k - i) = k by omega]
      have hpos : 0 < 2 ^ i := Nat.two_pow_pos i
      have hpos2 : 1 ≤ 2 ^ (k - i) := Nat.two_pow_pos (k - i)
      have hsub : 2 ^ k - 1 = (2 ^ i - 1) + 2 ^ i * (2 ^ (k - i) - 1) := by
        rw [hpow, Nat.mul_sub_left_distrib, Nat.mul_one]
        have : 2 ^ i ≤ 2 ^ i * 2 ^ (k - i) := Nat.le_mul_of_pos_right _ hpos2
        omega
      rw [hsub, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt (by omega), Nat.zero_add]
    have hodd : (2 ^ (k - i) - 1) % 2 = 1 := by
      have h1 : k - i = (k - i - 1) + 1 := by omega
      rw [h1, Nat.pow_succ]
      have hpos := Nat.two_pow_pos (k - i - 1)
      generalize 2 ^ (k - i - 1) = q at hpos ⊢
      omega
    rw [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv, Nat.and_comm, Nat.and_one_is_mod, hodd]
    rfl
  · simp only [decide_eq_false hik]
    have hlt : 2 ^ k - 1 < 2 ^ i := by
      have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
      have hle := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : k ≤ i)
      omega
    exact Nat.testBit_lt_two_pow hlt

private theorem split_hi_lo {w : Nat} (k : Nat) (hk : k < w) (x : BitVec w) :
    (x &&& lowMask w k).toNat = x.toNat % 2 ^ k ∧
    (x &&& ~~~lowMask w k).toNat = (x.toNat / 2 ^ k) * 2 ^ k ∧
    (x ^^^ lowMask w k).toNat = (x.toNat / 2 ^ k) * 2 ^ k + (2 ^ k - 1 - x.toNat % 2 ^ k) := by
  have hlo : (x &&& lowMask w k).toNat = x.toNat % 2 ^ k := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [← getLsbD_eq_testBit, BitVec.getLsbD_and, lowMask_getLsbD k hk i, Nat.testBit_mod_two_pow,
      getLsbD_eq_testBit]
    by_cases hik : i < k <;> simp [hik]
  have hhi : (x &&& ~~~lowMask w k).toNat = (x.toNat / 2 ^ k) * 2 ^ k := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [← getLsbD_eq_testBit, BitVec.getLsbD_and, BitVec.getLsbD_not, lowMask_getLsbD k hk i,
      getLsbD_eq_testBit, Nat.mul_comm, Nat.testBit_two_pow_mul]
    by_cases hiw : i < w
    · by_cases hik : i < k
      · simp [hiw, hik, show ¬ k ≤ i by omega]
      · have hki : k ≤ i := by omega
        simp [hiw, hik, hki, Nat.testBit_div_two_pow, show (i - k) + k = i by omega]
    · have hxf : x.toNat.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) (by omega)))
      have hdivf : (x.toNat / 2 ^ k).testBit (i - k) = false := by
        rw [Nat.testBit_div_two_pow, show (i - k) + k = i by omega]; exact hxf
      simp [hiw, hxf, hdivf]
  have hxor : (x ^^^ lowMask w k).toNat = (x.toNat / 2 ^ k) * 2 ^ k + (2 ^ k - 1 - x.toNat % 2 ^ k) := by
    have hlt_lo : x.toNat % 2 ^ k < 2 ^ k := Nat.mod_lt x.toNat (Nat.two_pow_pos k)
    have hsub_lt : 2 ^ k - 1 - x.toNat % 2 ^ k < 2 ^ k := by omega
    have hsub_bit : ∀ i, i < k → (2 ^ k - 1 - x.toNat % 2 ^ k).testBit i = !(x.toNat.testBit i) := by
      intro i hi
      -- Sum `(2^k - 1 - r) + r = 2^k - 1` has no carries: prove by induction on `k`!
      have hcomp : ∀ m r, r < 2 ^ m → ∀ j, j < m → (2 ^ m - 1 - r).testBit j = !(r.testBit j) := by
        intro m
        induction m with
        | zero => intro _ _ _ hj; omega
        | succ m ihm =>
          intro r hr j hj
          have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; omega
          have hdiv : (2 ^ (m + 1) - 1 - r) / 2 = 2 ^ m - 1 - r / 2 := by omega
          have hmod : (2 ^ (m + 1) - 1 - r) % 2 = 1 - r % 2 := by omega
          cases j with
          | zero =>
            rw [Nat.testBit_zero, Nat.testBit_zero, hmod]
            by_cases h1 : r % 2 = 1 <;> simp [h1] <;> omega
          | succ j =>
            rw [Nat.testBit_succ, Nat.testBit_succ, hdiv]
            exact ihm (r / 2) (by omega) j (by omega)
      rw [hcomp k (x.toNat % 2 ^ k) hlt_lo i hi, Nat.testBit_mod_two_pow]
      simp [hi]
    apply Nat.eq_of_testBit_eq; intro i
    rw [← getLsbD_eq_testBit, BitVec.getLsbD_xor, lowMask_getLsbD k hk i, getLsbD_eq_testBit]
    by_cases hik : i < k
    · simp only [decide_eq_true hik]
      have hmod : ((x.toNat / 2 ^ k) * 2 ^ k + (2 ^ k - 1 - x.toNat % 2 ^ k)) % 2 ^ k =
          2 ^ k - 1 - x.toNat % 2 ^ k := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hsub_lt]
      have htb := congrArg (fun n => n.testBit i) hmod
      simp only [Nat.testBit_mod_two_pow, decide_eq_true hik, Bool.true_and] at htb
      rw [htb, hsub_bit i hik]
      cases x.toNat.testBit i <;> rfl
    · simp only [decide_eq_false hik, Bool.xor_false]
      have hdiv : ((x.toNat / 2 ^ k) * 2 ^ k + (2 ^ k - 1 - x.toNat % 2 ^ k)) / 2 ^ k =
          x.toNat / 2 ^ k := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hsub_lt,
          Nat.zero_add]
      have htb := congrArg (fun n => n.testBit (i - k)) hdiv
      rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, show (i - k) + k = i by omega] at htb
      exact htb.symm
  exact ⟨hlo, hhi, hxor⟩

theorem coreXorRack_eq {w : Nat} (k : Nat) (hk : k < w) (x y : BitVec w) :
    coreXorRack k x y =
      2#w * (x &&& ~~~lowMask w k) + lowMask w k - y := by
  unfold coreXorRack
  have hpair : (x ^^^ lowMask w k) + x = 2#w * (x &&& ~~~lowMask w k) + lowMask w k := by
    apply BitVec.eq_of_toNat_eq
    have ⟨_, hhi, hxor⟩ := split_hi_lo k hk x
    have hmask := lowMask_toNat k hk
    have hdm := Nat.div_add_mod x.toNat (2 ^ k)
    rw [Nat.mul_comm (2 ^ k)] at hdm
    have hlt_lo : x.toNat % 2 ^ k < 2 ^ k := Nat.mod_lt x.toNat (Nat.two_pow_pos k)
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_mul, hxor, hhi, hmask, BitVec.toNat_ofNat]
    have h2 : (2 % 2 ^ w * (x.toNat / 2 ^ k * 2 ^ k)) % 2 ^ w =
        (2 * (x.toNat / 2 ^ k * 2 ^ k)) % 2 ^ w := by
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
    rw [h2, Nat.add_mod ((2 * (x.toNat / 2 ^ k * 2 ^ k)) % 2 ^ w), Nat.mod_mod, ← Nat.add_mod]
    congr 1; omega
  have h1 : (x ^^^ lowMask w k) + (x - y) = ((x ^^^ lowMask w k) + x) - y := by grind
  rw [h1, hpair]

theorem coreXorRack_involutive_framed_laws {w : Nat} (k : Nat) (hk1 : 1 ≤ k) (hk2 : k < w) :
    (∀ x y : BitVec w, coreXorRack k x (coreXorRack k x y) = y) ∧
    (∀ x y z : BitVec w, coreXorRack k x (coreXorRack k y z) =
      coreXorRack k (coreXorRack k x y) (coreXorRack k x z)) ∧
    coreXorRack k 0#w 0#w ≠ 0#w := by
  have hhi_step : ∀ x y : BitVec w,
      (coreXorRack k x y &&& ~~~lowMask w k) =
        2#w * (x &&& ~~~lowMask w k) - (y &&& ~~~lowMask w k) := by
    intro x y
    rw [coreXorRack_eq k hk2 x y]
    -- Show `A + lowMask - y = (A - y_hi) + (lowMask - y_lo)` has high bits `A - y_hi`!
    let A : BitVec w := 2#w * (x &&& ~~~lowMask w k)
    let yh : BitVec w := y &&& ~~~lowMask w k
    let yl : BitVec w := y &&& lowMask w k
    have hy_split : y = yh + yl := by
      apply BitVec.eq_of_toNat_eq
      have ⟨hlo, hhi, _⟩ := split_hi_lo k hk2 y
      have hdm := Nat.div_add_mod y.toNat (2 ^ k)
      rw [Nat.mul_comm (2 ^ k)] at hdm
      rw [BitVec.toNat_add, hhi, hlo]
      have hsum : y.toNat / 2 ^ k * 2 ^ k + y.toNat % 2 ^ k = y.toNat := by omega
      rw [hsum, Nat.mod_eq_of_lt y.isLt]
    have hdiff_split : A + lowMask w k - y = (A - yh) + (lowMask w k - yl) := by
      rw [hy_split]; grind
    have hmult_A : ∃ q : Nat, A.toNat = q * 2 ^ k := by
      have ⟨_, hhi, _⟩ := split_hi_lo k hk2 x
      dsimp only [A]
      rw [BitVec.toNat_mul, hhi, BitVec.toNat_ofNat]
      have hdvd : 2 ^ k ∣ 2 ^ w := Nat.pow_dvd_pow 2 (by omega)
      have hmod0 : ((2 % 2 ^ w) * ((x.toNat / 2 ^ k) * 2 ^ k) % 2 ^ w) % 2 ^ k = 0 := by
        rw [Nat.mod_mod_of_dvd _ hdvd, ← Nat.mul_assoc, Nat.mul_mod_left]
      exact ⟨((2 % 2 ^ w) * ((x.toNat / 2 ^ k) * 2 ^ k) % 2 ^ w) / 2 ^ k, by
        have h := Nat.div_add_mod ((2 % 2 ^ w) * ((x.toNat / 2 ^ k) * 2 ^ k) % 2 ^ w) (2 ^ k)
        rw [Nat.mul_comm (2 ^ k)] at h
        omega⟩
    have hmult_yh : ∃ q : Nat, yh.toNat = q * 2 ^ k := by
      have ⟨_, hhi, _⟩ := split_hi_lo k hk2 y
      exact ⟨y.toNat / 2 ^ k, hhi⟩
    have hmult_sub : ∃ q : Nat, (A - yh).toNat = q * 2 ^ k := by
      rcases hmult_A with ⟨qa, hqa⟩
      rcases hmult_yh with ⟨qy, hqy⟩
      have hdvd : 2 ^ k ∣ 2 ^ w := Nat.pow_dvd_pow 2 (by omega)
      have hmod0 : (A - yh).toNat % 2 ^ k = 0 := by
        rw [BitVec.toNat_sub, Nat.mod_mod_of_dvd _ hdvd, hqa, hqy]
        rcases hdvd with ⟨c, hc⟩
        rw [hc]
        have h1 : 2 ^ k * c - qy * 2 ^ k + qa * 2 ^ k = (c - qy + qa) * 2 ^ k := by
          have hy_le : qy ≤ c := by
            have := yh.isLt; rw [hqy, hc] at this
            have : qy * 2 ^ k < c * 2 ^ k := by rw [Nat.mul_comm c]; exact this
            exact Nat.le_of_lt (Nat.lt_of_mul_lt_mul_right this)
          rw [Nat.mul_comm (2 ^ k) c, ← Nat.mul_sub_right_distrib, ← Nat.add_mul]
        rw [h1, Nat.mul_mod_left]
      exact ⟨(A - yh).toNat / 2 ^ k, by
        have h := Nat.div_add_mod (A - yh).toNat (2 ^ k)
        rw [Nat.mul_comm (2 ^ k)] at h
        omega⟩
    have hrem_lt : (lowMask w k - yl).toNat < 2 ^ k := by
      have ⟨hlo, _, _⟩ := split_hi_lo k hk2 y
      have hmask := lowMask_toNat k hk2
      have hlt_lo : y.toNat % 2 ^ k < 2 ^ k := Nat.mod_lt y.toNat (Nat.two_pow_pos k)
      have hlt_w : 2 ^ k < 2 ^ w := Nat.pow_lt_pow_right (by omega) hk2
      rw [BitVec.toNat_sub, hmask, hlo]
      have h1 : 2 ^ w - y.toNat % 2 ^ k + (2 ^ k - 1) = (2 ^ k - 1 - y.toNat % 2 ^ k) + 2 ^ w := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega
    rw [hdiff_split]
    apply BitVec.eq_of_toNat_eq
    have ⟨_, hhi_res, _⟩ := split_hi_lo k hk2 ((A - yh) + (lowMask w k - yl))
    rcases hmult_sub with ⟨qs, hqs⟩
    rw [hhi_res, BitVec.toNat_add, hqs]
    have hlt_sum : qs * 2 ^ k + (lowMask w k - yl).toNat < 2 ^ w := by
      have hlt_s := (A - yh).isLt
      rw [hqs] at hlt_s
      have hdvd : 2 ^ k ∣ 2 ^ w := Nat.pow_dvd_pow 2 (by omega)
      rcases hdvd with ⟨c, hc⟩
      have hqc : qs < c := by
        rw [hc, Nat.mul_comm (2 ^ k) c] at hlt_s
        exact Nat.lt_of_mul_lt_mul_right hlt_s
      have h1 : qs + 1 ≤ c := by omega
      have h2 : (qs + 1) * 2 ^ k ≤ c * 2 ^ k := Nat.mul_le_mul_right (2 ^ k) h1
      rw [Nat.add_mul, Nat.one_mul, ← Nat.mul_comm (2 ^ k) c, ← hc] at h2
      omega
    rw [Nat.mod_eq_of_lt hlt_sum, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos k),
      Nat.div_eq_of_lt hrem_lt, Nat.zero_add]
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    rw [coreXorRack_eq k hk2, coreXorRack_eq k hk2]
    grind
  · intro x y z
    rw [coreXorRack_eq k hk2 x (coreXorRack k y z), coreXorRack_eq k hk2 y z]
    rw [coreXorRack_eq k hk2 (coreXorRack k x y) (coreXorRack k x z), hhi_step x y,
      coreXorRack_eq k hk2 x z]
    grind
  · rw [coreXorRack_eq k hk2]
    have h0 : (0#w &&& ~~~lowMask w k) = 0#w := by simp
    rw [h0]
    have hsimp : 2#w * 0#w + lowMask w k - 0#w = lowMask w k := by grind
    rw [hsimp]
    intro hzero
    have htn := congrArg BitVec.toNat hzero
    rw [lowMask_toNat k hk2, BitVec.toNat_ofNat, Nat.zero_mod] at htn
    have h2 : 2 ≤ 2 ^ k := by
      have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hk1; omega
    omega

theorem coreXorRack_nonAlexander :
    ¬ (∃ a b d : BitVec 4, ∀ x y : BitVec 4, coreXorRack 1 x y = a * x + b * y + d) := by
  rintro ⟨a, b, d, h⟩
  have h00 := h 0#4 0#4
  have h10 := h 1#4 0#4
  have h20 := h 2#4 0#4
  have hc00 : coreXorRack 1 0#4 0#4 = 1#4 := by decide
  have hc10 : coreXorRack 1 1#4 0#4 = 1#4 := by decide
  have hc20 : coreXorRack 1 2#4 0#4 = 5#4 := by decide
  rw [hc00] at h00; rw [hc10] at h10; rw [hc20] at h20
  have hd : d = 1#4 := by grind
  have ha : a = 0#4 := by grind
  have hcontra : (5#4 : BitVec 4) = 1#4 := by grind
  exact absurd hcontra (by decide)

/-! ## Section 4: Single-Bit Conjugated Both-Sided Knot Quandles -/

theorem conjBitQuandle_eq {w : Nat} (k : Nat) (hk : k < w) (x y : BitVec w) :
    conjBitQuandle k x y =
      if x.getLsbD k = y.getLsbD k then y
      else if x.getLsbD k then y - (1#w <<< (k + 1))
      else y + (1#w <<< (k + 1)) := by
  unfold conjBitQuandle
  rw [xor_singleBit_eq k hk x]
  have h2 := add_singleBit_eq_two_pow k hk
  cases hx : x.getLsbD k
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hsum : x + (1#w <<< k) + (y - x) = y + (1#w <<< k) := by grind
    rw [hsum, xor_singleBit_eq k hk (y + (1#w <<< k)), add_two_pow_k_flips_bit k hk y]
    cases hy : y.getLsbD k <;> simp <;> grind
  · simp only [↓reduceIte]
    have hsum : x - (1#w <<< k) + (y - x) = y - (1#w <<< k) := by grind
    rw [hsum, xor_singleBit_eq k hk (y - (1#w <<< k)), sub_two_pow_k_flips_bit k hk y]
    cases hy : y.getLsbD k <;> simp <;> grind

theorem conjBitQuandle_bothSided_laws {w : Nat} (k : Nat) (hk : k + 1 < w) :
    (∀ x : BitVec w, conjBitQuandle k x x = x) ∧
    (∀ x y : BitVec w, conjBitQuandle k x (conjBitQuandleInv k x y) = y) ∧
    (∀ x y : BitVec w, conjBitQuandleInv k x (conjBitQuandle k x y) = y) ∧
    (∀ x y z : BitVec w, conjBitQuandle k x (conjBitQuandle k y z) =
      conjBitQuandle k (conjBitQuandle k x y) (conjBitQuandle k x z)) ∧
    (∀ x y z : BitVec w, conjBitQuandle k (conjBitQuandle k x y) z =
      conjBitQuandle k (conjBitQuandle k x z) (conjBitQuandle k y z)) := by
  have hk_lt : k < w := by omega
  have hmult : ∃ q : Nat, ((1#w : BitVec w) <<< (k + 1)).toNat = q * 2 ^ (k + 1) :=
    ⟨1, by rw [singleBit_toNat (k + 1) hk, Nat.one_mul]⟩
  have hbit_q : ∀ x y : BitVec w, (conjBitQuandle k x y).getLsbD k = y.getLsbD k := by
    intro x y
    rw [conjBitQuandle_eq k hk_lt x y]
    cases hx : x.getLsbD k <;> cases hy : y.getLsbD k <;> simp
    · exact hy
    · rw [add_multiple_preserves_low_bits (k + 1) hk y _ hmult k (by omega)]; exact hy
    · rw [sub_multiple_preserves_low_bits (k + 1) hk y _ hmult k (by omega)]; exact hy
    · exact hy
  have hbit_inv : ∀ x y : BitVec w, (conjBitQuandleInv k x y).getLsbD k = y.getLsbD k := by
    intro x y
    unfold conjBitQuandleInv
    cases hx : x.getLsbD k <;> cases hy : y.getLsbD k <;> simp
    · exact hy
    · rw [sub_multiple_preserves_low_bits (k + 1) hk y _ hmult k (by omega)]; exact hy
    · rw [add_multiple_preserves_low_bits (k + 1) hk y _ hmult k (by omega)]; exact hy
    · exact hy
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x; rw [conjBitQuandle_eq k hk_lt x x]; simp
  · intro x y
    rw [conjBitQuandle_eq k hk_lt x _, hbit_inv x y]
    unfold conjBitQuandleInv
    cases hx : x.getLsbD k <;> cases hy : y.getLsbD k <;> simp <;> grind
  · intro x y
    unfold conjBitQuandleInv
    rw [hbit_q x y, conjBitQuandle_eq k hk_lt x y]
    cases hx : x.getLsbD k <;> cases hy : y.getLsbD k <;> simp <;> grind
  · intro x y z
    rw [conjBitQuandle_eq k hk_lt x (conjBitQuandle k y z),
      conjBitQuandle_eq k hk_lt (conjBitQuandle k x y) (conjBitQuandle k x z),
      hbit_q y z, hbit_q x y, hbit_q x z,
      conjBitQuandle_eq k hk_lt y z, conjBitQuandle_eq k hk_lt x z]
    cases hx : x.getLsbD k <;> cases hy : y.getLsbD k <;> cases hz : z.getLsbD k <;>
      simp <;> grind
  · intro x y z
    rw [conjBitQuandle_eq k hk_lt (conjBitQuandle k x y) z,
      conjBitQuandle_eq k hk_lt (conjBitQuandle k x z) (conjBitQuandle k y z),
      hbit_q x y, hbit_q x z, hbit_q y z,
      conjBitQuandle_eq k hk_lt y z]
    simp

theorem conjBitQuandle_nonInvolutive_nonAlexander :
    (∀ {w : Nat} (k : Nat), k + 2 < w →
      conjBitQuandle k 0#w (conjBitQuandle k 0#w (1#w <<< k)) ≠ (1#w <<< k)) ∧
    conjBitQuandle 0 0#3 (conjBitQuandle 0 0#3 1#3) ≠ 1#3 ∧
    ¬ (∃ a b d : BitVec 3, ∀ x y : BitVec 3, conjBitQuandle 0 x y = a * x + b * y + d) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w k hk
    have hk_lt : k < w := by omega
    have hk1 : k + 1 < w := by omega
    have h0b : (0#w : BitVec w).getLsbD k = false := by simp
    have h1b : (1#w <<< k : BitVec w).getLsbD k = true := by
      rw [getLsbD_eq_testBit, singleBit_toNat k hk_lt, Nat.testBit_two_pow]; simp
    have hstep1 : conjBitQuandle k 0#w (1#w <<< k) = (1#w <<< k) + (1#w <<< (k + 1)) := by
      rw [conjBitQuandle_eq k hk_lt, h0b, h1b]; simp
    have hmult : ∃ q : Nat, ((1#w : BitVec w) <<< (k + 1)).toNat = q * 2 ^ (k + 1) :=
      ⟨1, by rw [singleBit_toNat (k + 1) hk1, Nat.one_mul]⟩
    have h1b' : ((1#w <<< k) + (1#w <<< (k + 1)) : BitVec w).getLsbD k = true := by
      rw [add_multiple_preserves_low_bits (k + 1) hk1 _ _ hmult k (by omega), h1b]
    rw [hstep1, conjBitQuandle_eq k hk_lt, h0b, h1b']
    simp only [Bool.false_eq_true, ↓reduceIte]
    intro heq
    have h2z : ((1#w <<< (k + 1)) + (1#w <<< (k + 1)) : BitVec w) = 0#w := by grind
    rw [add_singleBit_eq_two_pow (k + 1) hk1] at h2z
    have htn := congrArg BitVec.toNat h2z
    rw [singleBit_toNat (k + 2) hk, BitVec.toNat_ofNat, Nat.zero_mod] at htn
    have hpos : 0 < 2 ^ (k + 2) := Nat.two_pow_pos (k + 2)
    omega
  · decide
  · rintro ⟨a, b, d, h⟩
    have h00 := h 0#3 0#3
    have h01 := h 0#3 1#3
    have h02 := h 0#3 2#3
    have hc00 : conjBitQuandle 0 0#3 0#3 = 0#3 := by decide
    have hc01 : conjBitQuandle 0 0#3 1#3 = 3#3 := by decide
    have hc02 : conjBitQuandle 0 0#3 2#3 = 2#3 := by decide
    rw [hc00] at h00; rw [hc01] at h01; rw [hc02] at h02
    have hd : d = 0#3 := by grind
    have hb : b = 3#3 := by grind
    have hcontra : (2#3 : BitVec 3) = 6#3 := by grind
    exact absurd hcontra (by decide)

end SiliconRacksQuandles
