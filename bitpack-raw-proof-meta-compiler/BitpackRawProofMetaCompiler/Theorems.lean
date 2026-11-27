import BitpackRawProofMetaCompiler.Defs

namespace BitPackMC
private theorem popcountFuel_zero (f : Nat) : popcountFuel f 0 = 0 := by
  cases f <;> rfl

private theorem popcountFuel_ge : ∀ f1 f2 n, n ≤ f1 -> n ≤ f2 ->
    popcountFuel f1 n = popcountFuel f2 n := by
  intro f1
  induction f1 with
  | zero =>
    intro f2 n h1 _
    have hn : n = 0 := by omega
    subst hn; simp [popcountFuel_zero]
  | succ f1 ih =>
    intro f2 n h1 h2
    cases f2 with
    | zero =>
      have hn : n = 0 := by omega
      subst hn; simp [popcountFuel_zero]
    | succ f2 =>
      by_cases hn : n = 0
      · subst hn; rfl
      · have hne : (n == 0) = false := by simp [hn]
        simp only [popcountFuel, hne, Bool.false_eq_true, ↓reduceIte]
        rw [ih f2 (n / 2) (by omega) (by omega)]

theorem popcount_zero : popcount 0 = 0 := rfl

theorem popcount_bit (b : Bool) (n : Nat) :
    popcount (2 * n + b.toNat) = b.toNat + popcount n := by
  cases b
  · simp only [Bool.toNat_false, Nat.add_zero, Nat.zero_add]
    by_cases h : n = 0
    · subst h; rfl
    · unfold popcount
      have h1 : popcountFuel (2 * n) (2 * n) = popcountFuel ((2 * n - 1) + 1) (2 * n) :=
        popcountFuel_ge (2 * n) ((2 * n - 1) + 1) (2 * n) (Nat.le_refl _) (by omega)
      rw [h1]
      simp only [popcountFuel]
      have hne : (2 * n == 0) = false := by
        have : 2 * n ≠ 0 := by omega
        simp [this]
      rw [hne]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hmod : (2 * n) % 2 = 0 := by omega
      have hdiv : (2 * n) / 2 = n := by omega
      rw [hmod, hdiv, Nat.zero_add]
      exact popcountFuel_ge (2 * n - 1) n n (by omega) (Nat.le_refl _)
  · simp only [Bool.toNat_true]
    unfold popcount
    simp only [popcountFuel]
    have hne : ((2 * n + 1) == 0) = false := by simp
    rw [hne]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hmod : (2 * n + 1) % 2 = 1 := by omega
    have hdiv : (2 * n + 1) / 2 = n := by omega
    rw [hmod, hdiv]
    rw [popcountFuel_ge (2 * n) n n (by omega) (Nat.le_refl _)]

theorem popcount_two_mul (n : Nat) : popcount (2 * n) = popcount n := by
  have h := popcount_bit false n
  simpa using h

private theorem mod2_beq_toNat (n : Nat) : (n % 2 == 1).toNat = n % 2 := by
  have hlt : n % 2 < 2 := Nat.mod_lt n (by decide)
  by_cases h : n % 2 = 1
  · simp [h]
  · have h0 : n % 2 = 0 := by omega
    simp [h0]

private theorem nat_testBit_two_mul_add (b : Bool) (n i : Nat) :
    (2 * n + b.toNat).testBit i =
      match i with
      | 0 => b
      | j + 1 => n.testBit j := by
  cases i with
  | zero =>
    cases b <;> simp [Nat.testBit_zero]
  | succ j =>
    have hdiv : (2 * n + b.toNat) / 2 = n := by cases b <;> simp <;> omega
    rw [Nat.testBit_succ, hdiv]

theorem two_mul_add_xor (a b : Nat) (ba bb : Bool) :
    (2 * a + ba.toNat) ^^^ (2 * b + bb.toNat) =
      2 * (a ^^^ b) + (ba ^^ bb).toNat := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, nat_testBit_two_mul_add, nat_testBit_two_mul_add, nat_testBit_two_mul_add]
  cases i with
  | zero => cases ba <;> cases bb <;> rfl
  | succ j => simp [Nat.testBit_xor]

theorem two_mul_add_and (a b : Nat) (ba bb : Bool) :
    (2 * a + ba.toNat) &&& (2 * b + bb.toNat) =
      2 * (a &&& b) + (ba && bb).toNat := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, nat_testBit_two_mul_add, nat_testBit_two_mul_add, nat_testBit_two_mul_add]
  cases i with
  | zero => cases ba <;> cases bb <;> rfl
  | succ j => simp [Nat.testBit_and]

theorem two_mul_add_or (a b : Nat) (ba bb : Bool) :
    (2 * a + ba.toNat) ||| (2 * b + bb.toNat) =
      2 * (a ||| b) + (ba || bb).toNat := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, nat_testBit_two_mul_add, nat_testBit_two_mul_add, nat_testBit_two_mul_add]
  cases i with
  | zero => cases ba <;> cases bb <;> rfl
  | succ j => simp [Nat.testBit_or]

theorem popcount_gray_shift (x : Nat) :
    popcount ((2 * x) ^^^ (2 * (x / 2))) = popcount (x ^^^ (x >>> 1)) := by
  have h1 : (2 * x) ^^^ (2 * (x / 2)) = 2 * (x ^^^ (x / 2)) := by
    have h := two_mul_add_xor x (x / 2) false false
    simpa using h
  have h2 : x >>> 1 = x / 2 := by
    rw [Nat.shiftRight_eq_div_pow]
  rw [h1, h2, popcount_two_mul]

-- ============================================================================
-- Section 2: BitExpr Bytecode ISA & Bit-Sliced Carry-State Transducer
-- ============================================================================

theorem le_pow_carryWidth {k : Nat} (hk : k ≤ 16) : k ≤ 2 ^ carryWidth k := by
  unfold carryWidth
  split
  · omega
  · split
    · omega
    · split
      · omega
      · split <;> omega

private theorem add_mul_mod {a b p : Nat} (ha : a < p) : (a + p * b) % p = a := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

private theorem add_mul_div {a b p : Nat} (hp : 0 < p) (ha : a < p) : (a + p * b) / p = b := by
  rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt ha, Nat.zero_add]

private theorem add_mul_lt {a b p q : Nat} (ha : a < p) (hb : b < q) : a + p * b < p * q := by
  have h1 : p * b + p ≤ p * q := by
    have : b + 1 ≤ q := hb
    calc p * b + p = p * (b + 1) := by rw [Nat.mul_succ]
      _ ≤ p * q := Nat.mul_le_mul_left p this
  omega

private theorem div_lt_of_lt_mul {s p q : Nat} (hs : s < p * q) : s / p < q :=
  Nat.div_lt_of_lt_mul hs

theorem evalFrom_zero (e : BitExpr) (x y : Nat) : evalFrom e 0 x y = evalExpr e x y := by
  induction e with
  | varX => rfl
  | varY => rfl
  | mulK k a ih =>
    simp [evalFrom, evalExpr, ih]
  | even a ih =>
    simp [evalFrom, evalExpr, ih]
  | add a b iha ihb =>
    simp [evalFrom, evalExpr, iha, ihb]
  | xor a b iha ihb =>
    simp [evalFrom, evalExpr, iha, ihb]
  | and a b iha ihb =>
    simp [evalFrom, evalExpr, iha, ihb]
  | or a b iha ihb =>
    simp [evalFrom, evalExpr, iha, ihb]

theorem evalFrom_flush (e : BitExpr) (s : Nat) : evalFrom e s 0 0 = flushExpr e s := by
  induction e generalizing s with
  | varX => rfl
  | varY => rfl
  | mulK k a ih => simp [evalFrom, flushExpr, ih]
  | even a ih => simp [evalFrom, flushExpr, ih]
  | add a b iha ihb => simp [evalFrom, flushExpr, iha, ihb]
  | xor a b iha ihb => simp [evalFrom, flushExpr, iha, ihb]
  | and a b iha ihb => simp [evalFrom, flushExpr, iha, ihb]
  | or a b iha ihb => simp [evalFrom, flushExpr, iha, ihb]

theorem evalFrom_noVarY (e : BitExpr) (hy : e.hasVarY = false) (s x y1 y2 : Nat) :
    evalFrom e s x y1 = evalFrom e s x y2 := by
  induction e generalizing s with
  | varX => rfl
  | varY => simp [BitExpr.hasVarY] at hy
  | mulK k a ih =>
    simp [evalFrom, ih hy]
  | even a ih =>
    simp [evalFrom, ih hy]
  | add a b iha ihb =>
    simp only [BitExpr.hasVarY, Bool.or_eq_false_iff] at hy
    simp [evalFrom, iha hy.1, ihb hy.2]
  | xor a b iha ihb =>
    simp only [BitExpr.hasVarY, Bool.or_eq_false_iff] at hy
    simp [evalFrom, iha hy.1, ihb hy.2]
  | and a b iha ihb =>
    simp only [BitExpr.hasVarY, Bool.or_eq_false_iff] at hy
    simp [evalFrom, iha hy.1, ihb hy.2]
  | or a b iha ihb =>
    simp only [BitExpr.hasVarY, Bool.or_eq_false_iff] at hy
    simp [evalFrom, iha hy.1, ihb hy.2]

theorem stepExpr_lt (e : BitExpr) (hv : e.valid = true) (s : Nat)
    (hs : s < 2 ^ e.stateWidth) (bx by_ : Bool) :
    (stepExpr e s bx by_).1 < 2 ^ e.stateWidth := by
  induction e generalizing s with
  | varX => simp [stepExpr, BitExpr.stateWidth]
  | varY => simp [stepExpr, BitExpr.stateWidth]
  | mulK k a ih =>
    simp only [BitExpr.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    rcases hv with ⟨⟨_, hk16⟩, hva⟩
    simp only [BitExpr.stateWidth, Nat.pow_add] at hs ⊢
    have hp : 0 < 2 ^ carryWidth k := Nat.two_pow_pos _
    have hsa : s / 2 ^ carryWidth k < 2 ^ a.stateWidth := div_lt_of_lt_mul hs
    have hc : s % 2 ^ carryWidth k < 2 ^ carryWidth k := Nat.mod_lt _ hp
    have hkle : k ≤ 2 ^ carryWidth k := le_pow_carryWidth hk16
    have ih' := ih hva (s / 2 ^ carryWidth k) hsa
    simp only [stepExpr]
    have ht : (k * (stepExpr a (s / 2 ^ carryWidth k) bx by_).2.toNat + s % 2 ^ carryWidth k) / 2 <
        2 ^ carryWidth k := by
      have hba : (stepExpr a (s / 2 ^ carryWidth k) bx by_).2.toNat ≤ 1 := by
        cases (stepExpr a (s / 2 ^ carryWidth k) bx by_).2 <;> decide
      have : k * (stepExpr a (s / 2 ^ carryWidth k) bx by_).2.toNat ≤ k := by
        calc k * (stepExpr a (s / 2 ^ carryWidth k) bx by_).2.toNat ≤ k * 1 :=
              Nat.mul_le_mul_left k hba
          _ = k := Nat.mul_one k
      omega
    exact add_mul_lt ht ih'
  | even a ih =>
    simp only [BitExpr.valid] at hv
    simp only [BitExpr.stateWidth, Nat.pow_add, Nat.pow_one] at hs ⊢
    have hsa : s / 2 < 2 ^ a.stateWidth := div_lt_of_lt_mul hs
    have ih' := ih hv (s / 2) hsa
    simp only [stepExpr]
    exact add_mul_lt (by decide : 1 < 2) ih'
  | add a b iha ihb =>
    simp only [BitExpr.valid, Bool.and_eq_true] at hv
    simp only [BitExpr.stateWidth, Nat.pow_add, Nat.pow_one] at hs ⊢
    have h1 : s / 2 < 2 ^ a.stateWidth * 2 ^ b.stateWidth := by
      have : s < 2 * (2 ^ a.stateWidth * 2 ^ b.stateWidth) := by
        simpa [Nat.mul_assoc] using hs
      exact div_lt_of_lt_mul this
    have hsa : (s / 2) % 2 ^ a.stateWidth < 2 ^ a.stateWidth := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hsb : (s / 2) / 2 ^ a.stateWidth < 2 ^ b.stateWidth := div_lt_of_lt_mul h1
    have iha' := iha hv.1 ((s / 2) % 2 ^ a.stateWidth) hsa
    have ihb' := ihb hv.2 ((s / 2) / 2 ^ a.stateWidth) hsb
    simp only [stepExpr]
    have hba : (stepExpr a ((s / 2) % 2 ^ a.stateWidth) bx by_).2.toNat ≤ 1 := by
      cases (stepExpr a ((s / 2) % 2 ^ a.stateWidth) bx by_).2 <;> decide
    have hbb : (stepExpr b ((s / 2) / 2 ^ a.stateWidth) bx by_).2.toNat ≤ 1 := by
      cases (stepExpr b ((s / 2) / 2 ^ a.stateWidth) bx by_).2 <;> decide
    have hc : s % 2 < 2 := Nat.mod_lt _ (by decide)
    have hcarry : ((stepExpr a ((s / 2) % 2 ^ a.stateWidth) bx by_).2.toNat +
        (stepExpr b ((s / 2) / 2 ^ a.stateWidth) bx by_).2.toNat + s % 2) / 2 < 2 := by omega
    have hpair := add_mul_lt iha' ihb'
    have htot := add_mul_lt hcarry hpair
    simpa [Nat.mul_assoc] using htot
  | xor a b iha ihb =>
    simp only [BitExpr.valid, Bool.and_eq_true] at hv
    simp only [BitExpr.stateWidth, Nat.pow_add] at hs ⊢
    have hsa : s % 2 ^ a.stateWidth < 2 ^ a.stateWidth := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hsb : s / 2 ^ a.stateWidth < 2 ^ b.stateWidth := div_lt_of_lt_mul hs
    simpa [stepExpr] using add_mul_lt (iha hv.1 _ hsa) (ihb hv.2 _ hsb)
  | and a b iha ihb =>
    simp only [BitExpr.valid, Bool.and_eq_true] at hv
    simp only [BitExpr.stateWidth, Nat.pow_add] at hs ⊢
    have hsa : s % 2 ^ a.stateWidth < 2 ^ a.stateWidth := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hsb : s / 2 ^ a.stateWidth < 2 ^ b.stateWidth := div_lt_of_lt_mul hs
    simpa [stepExpr] using add_mul_lt (iha hv.1 _ hsa) (ihb hv.2 _ hsb)
  | or a b iha ihb =>
    simp only [BitExpr.valid, Bool.and_eq_true] at hv
    simp only [BitExpr.stateWidth, Nat.pow_add] at hs ⊢
    have hsa : s % 2 ^ a.stateWidth < 2 ^ a.stateWidth := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hsb : s / 2 ^ a.stateWidth < 2 ^ b.stateWidth := div_lt_of_lt_mul hs
    simpa [stepExpr] using add_mul_lt (iha hv.1 _ hsa) (ihb hv.2 _ hsb)

theorem stepExpr_spec (e : BitExpr) (hv : e.valid = true) (s x y : Nat)
    (hs : s < 2 ^ e.stateWidth) :
    let res := stepExpr e s (x % 2 == 1) (y % 2 == 1)
    evalFrom e s x y = 2 * evalFrom e res.1 (x / 2) (y / 2) + res.2.toNat := by
  induction e generalizing s with
  | varX =>
    simp only [evalFrom, stepExpr, mod2_beq_toNat]
    omega
  | varY =>
    simp only [evalFrom, stepExpr, mod2_beq_toNat]
    omega
  | mulK k a ih =>
    simp only [BitExpr.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    rcases hv with ⟨⟨_, hk16⟩, hva⟩
    simp only [BitExpr.stateWidth, Nat.pow_add] at hs
    have hp : 0 < 2 ^ carryWidth k := Nat.two_pow_pos _
    have hsa : s / 2 ^ carryWidth k < 2 ^ a.stateWidth := div_lt_of_lt_mul hs
    have hc : s % 2 ^ carryWidth k < 2 ^ carryWidth k := Nat.mod_lt _ hp
    have hkle : k ≤ 2 ^ carryWidth k := le_pow_carryWidth hk16
    have iha := ih hva (s / 2 ^ carryWidth k) hsa
    simp only [stepExpr, evalFrom]
    generalize hresA : stepExpr a (s / 2 ^ carryWidth k) (x % 2 == 1) (y % 2 == 1) = resA at iha ⊢
    generalize ht : k * resA.2.toNat + s % 2 ^ carryWidth k = t
    have ht_lt : t / 2 < 2 ^ carryWidth k := by
      have hba : resA.2.toNat ≤ 1 := by cases resA.2 <;> decide
      have : k * resA.2.toNat ≤ k := by
        calc k * resA.2.toNat ≤ k * 1 := Nat.mul_le_mul_left k hba
          _ = k := Nat.mul_one k
      omega
    have hdiv : (t / 2 + 2 ^ carryWidth k * resA.1) / 2 ^ carryWidth k = resA.1 :=
      add_mul_div hp ht_lt
    have hmod : (t / 2 + 2 ^ carryWidth k * resA.1) % 2 ^ carryWidth k = t / 2 :=
      add_mul_mod ht_lt
    rw [hdiv, hmod, iha, mod2_beq_toNat]
    have hmul : k * (2 * evalFrom a resA.1 (x / 2) (y / 2) + resA.2.toNat) =
        2 * (k * evalFrom a resA.1 (x / 2) (y / 2)) + k * resA.2.toNat := by
      rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm k 2, Nat.mul_assoc]
    omega
  | even a ih =>
    simp only [BitExpr.valid] at hv
    simp only [BitExpr.stateWidth, Nat.pow_add, Nat.pow_one] at hs
    have hsa : s / 2 < 2 ^ a.stateWidth := div_lt_of_lt_mul hs
    have iha := ih hv (s / 2) hsa
    dsimp only at iha
    simp only [stepExpr, evalFrom]
    have hmod1 : (1 + 2 * (stepExpr a (s / 2) (x % 2 == 1) (y % 2 == 1)).1) % 2 = 1 := by omega
    have hdiv1 : (1 + 2 * (stepExpr a (s / 2) (x % 2 == 1) (y % 2 == 1)).1) / 2 =
        (stepExpr a (s / 2) (x % 2 == 1) (y % 2 == 1)).1 := by omega
    simp only [hmod1, hdiv1, beq_self_eq_true, ↓reduceIte]
    rw [iha]
    by_cases hst : (s % 2 == 1) = true
    · simp [hst]
    · simp only [hst, Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, Nat.add_zero]
      have hba : (stepExpr a (s / 2) (x % 2 == 1) (y % 2 == 1)).2.toNat < 2 := by
        cases (stepExpr a (s / 2) (x % 2 == 1) (y % 2 == 1)).2 <;> decide
      have : (2 * evalFrom a (stepExpr a (s / 2) (x % 2 == 1) (y % 2 == 1)).1 (x / 2) (y / 2) +
          (stepExpr a (s / 2) (x % 2 == 1) (y % 2 == 1)).2.toNat) / 2 =
          evalFrom a (stepExpr a (s / 2) (x % 2 == 1) (y % 2 == 1)).1 (x / 2) (y / 2) := by omega
      simp [this]
  | add a b iha ihb =>
    simp only [BitExpr.valid, Bool.and_eq_true] at hv
    simp only [BitExpr.stateWidth, Nat.pow_add, Nat.pow_one] at hs
    have h1 : s / 2 < 2 ^ a.stateWidth * 2 ^ b.stateWidth := by
      have : s < 2 * (2 ^ a.stateWidth * 2 ^ b.stateWidth) := by
        simpa [Nat.mul_assoc] using hs
      exact div_lt_of_lt_mul this
    have hpA : 0 < 2 ^ a.stateWidth := Nat.two_pow_pos _
    have hsa : (s / 2) % 2 ^ a.stateWidth < 2 ^ a.stateWidth := Nat.mod_lt _ hpA
    have hsb : (s / 2) / 2 ^ a.stateWidth < 2 ^ b.stateWidth := div_lt_of_lt_mul h1
    have ha_lt := stepExpr_lt a hv.1 _ hsa (x % 2 == 1) (y % 2 == 1)
    have ha_sp := iha hv.1 _ hsa
    have hb_sp := ihb hv.2 _ hsb
    simp only [stepExpr, evalFrom]
    generalize hresA : stepExpr a ((s / 2) % 2 ^ a.stateWidth) (x % 2 == 1) (y % 2 == 1) = resA at ha_lt ha_sp ⊢
    generalize hresB : stepExpr b ((s / 2) / 2 ^ a.stateWidth) (x % 2 == 1) (y % 2 == 1) = resB at hb_sp ⊢
    generalize ht : resA.2.toNat + resB.2.toNat + s % 2 = t
    have hba : resA.2.toNat ≤ 1 := by cases resA.2 <;> decide
    have hbb : resB.2.toNat ≤ 1 := by cases resB.2 <;> decide
    have hc : s % 2 < 2 := Nat.mod_lt _ (by decide)
    have ht_lt : t / 2 < 2 := by omega
    have hmod2 : (t / 2 + 2 * (resA.1 + 2 ^ a.stateWidth * resB.1)) % 2 = t / 2 :=
      add_mul_mod ht_lt
    have hdiv2 : (t / 2 + 2 * (resA.1 + 2 ^ a.stateWidth * resB.1)) / 2 =
        resA.1 + 2 ^ a.stateWidth * resB.1 := add_mul_div (by decide) ht_lt
    rw [hmod2, hdiv2, add_mul_mod ha_lt, add_mul_div hpA ha_lt, ha_sp, hb_sp, mod2_beq_toNat]
    omega
  | xor a b iha ihb =>
    simp only [BitExpr.valid, Bool.and_eq_true] at hv
    simp only [BitExpr.stateWidth, Nat.pow_add] at hs
    have hpA : 0 < 2 ^ a.stateWidth := Nat.two_pow_pos _
    have hsa : s % 2 ^ a.stateWidth < 2 ^ a.stateWidth := Nat.mod_lt _ hpA
    have hsb : s / 2 ^ a.stateWidth < 2 ^ b.stateWidth := div_lt_of_lt_mul hs
    have ha_lt := stepExpr_lt a hv.1 _ hsa (x % 2 == 1) (y % 2 == 1)
    have ha_sp := iha hv.1 _ hsa
    have hb_sp := ihb hv.2 _ hsb
    simp only [stepExpr, evalFrom]
    rw [add_mul_mod ha_lt, add_mul_div hpA ha_lt, ha_sp, hb_sp]
    exact two_mul_add_xor _ _ _ _
  | and a b iha ihb =>
    simp only [BitExpr.valid, Bool.and_eq_true] at hv
    simp only [BitExpr.stateWidth, Nat.pow_add] at hs
    have hpA : 0 < 2 ^ a.stateWidth := Nat.two_pow_pos _
    have hsa : s % 2 ^ a.stateWidth < 2 ^ a.stateWidth := Nat.mod_lt _ hpA
    have hsb : s / 2 ^ a.stateWidth < 2 ^ b.stateWidth := div_lt_of_lt_mul hs
    have ha_lt := stepExpr_lt a hv.1 _ hsa (x % 2 == 1) (y % 2 == 1)
    have ha_sp := iha hv.1 _ hsa
    have hb_sp := ihb hv.2 _ hsb
    simp only [stepExpr, evalFrom]
    rw [add_mul_mod ha_lt, add_mul_div hpA ha_lt, ha_sp, hb_sp]
    exact two_mul_add_and _ _ _ _
  | or a b iha ihb =>
    simp only [BitExpr.valid, Bool.and_eq_true] at hv
    simp only [BitExpr.stateWidth, Nat.pow_add] at hs
    have hpA : 0 < 2 ^ a.stateWidth := Nat.two_pow_pos _
    have hsa : s % 2 ^ a.stateWidth < 2 ^ a.stateWidth := Nat.mod_lt _ hpA
    have hsb : s / 2 ^ a.stateWidth < 2 ^ b.stateWidth := div_lt_of_lt_mul hs
    have ha_lt := stepExpr_lt a hv.1 _ hsa (x % 2 == 1) (y % 2 == 1)
    have ha_sp := iha hv.1 _ hsa
    have hb_sp := ihb hv.2 _ hsb
    simp only [stepExpr, evalFrom]
    rw [add_mul_mod ha_lt, add_mul_div hpA ha_lt, ha_sp, hb_sp]
    exact two_mul_add_or _ _ _ _

-- ============================================================================
-- Section 3: Multi-Expression Product System (`sysWidth`, `stepSys`, `flushSys`)
-- ============================================================================

theorem evalSysFrom_zero (es : List BitExpr) (x y : Nat) :
    evalSysFrom es 0 x y = evalSys es x y := by
  induction es with
  | nil => rfl
  | cons e rest ih =>
    simp [evalSysFrom, evalSys, evalFrom_zero, ih]

theorem evalSysFrom_flush (es : List BitExpr) (s : Nat) :
    evalSysFrom es s 0 0 = flushSys es s := by
  induction es generalizing s with
  | nil => rfl
  | cons e rest ih =>
    simp [evalSysFrom, flushSys, evalFrom_flush, ih]

theorem evalSysFrom_noVarY (es : List BitExpr) (hy : sysNoVarY es = true) (s x y1 y2 : Nat) :
    evalSysFrom es s x y1 = evalSysFrom es s x y2 := by
  induction es generalizing s with
  | nil => rfl
  | cons e rest ih =>
    simp only [sysNoVarY, Bool.and_eq_true, Bool.not_eq_true'] at hy
    simp only [evalSysFrom]
    rw [evalFrom_noVarY e hy.1, ih hy.2]

theorem stepSys_lt (es : List BitExpr) (hv : sysValid es = true) (s : Nat)
    (hs : s < 2 ^ sysWidth es) (bx by_ : Bool) :
    (stepSys es s bx by_).1 < 2 ^ sysWidth es := by
  induction es generalizing s with
  | nil => simp [stepSys, sysWidth]
  | cons e rest ih =>
    simp only [sysValid, Bool.and_eq_true] at hv
    simp only [sysWidth, Nat.pow_add] at hs ⊢
    have hp : 0 < 2 ^ e.stateWidth := Nat.two_pow_pos _
    have hse : s % 2 ^ e.stateWidth < 2 ^ e.stateWidth := Nat.mod_lt _ hp
    have hsr : s / 2 ^ e.stateWidth < 2 ^ sysWidth rest := div_lt_of_lt_mul hs
    simpa [stepSys] using add_mul_lt (stepExpr_lt e hv.1 _ hse bx by_) (ih hv.2 _ hsr)

theorem evalSysFrom_step (es : List BitExpr) (hv : sysValid es = true) (s x y : Nat)
    (hs : s < 2 ^ sysWidth es) :
    let res := stepSys es s (x % 2 == 1) (y % 2 == 1)
    evalSysFrom es s x y =
      List.zipWith (fun v b => 2 * v + b.toNat) (evalSysFrom es res.1 (x / 2) (y / 2)) res.2 := by
  induction es generalizing s with
  | nil => rfl
  | cons e rest ih =>
    simp only [sysValid, Bool.and_eq_true] at hv
    simp only [sysWidth, Nat.pow_add] at hs
    have hp : 0 < 2 ^ e.stateWidth := Nat.two_pow_pos _
    have hse : s % 2 ^ e.stateWidth < 2 ^ e.stateWidth := Nat.mod_lt _ hp
    have hsr : s / 2 ^ e.stateWidth < 2 ^ sysWidth rest := div_lt_of_lt_mul hs
    have hlt := stepExpr_lt e hv.1 _ hse (x % 2 == 1) (y % 2 == 1)
    have hsp := stepExpr_spec e hv.1 _ x y hse
    have ihr := ih hv.2 _ hsr
    simp only [stepSys, evalSysFrom, List.zipWith_cons_cons]
    rw [add_mul_mod hlt, add_mul_div hp hlt, hsp, ihr]

private theorem weightedSum_zip_pop (ws : List Int) (vs : List Nat) (bs : List Bool)
    (hlen : vs.length = bs.length) :
    weightedSum ws ((List.zipWith (fun v b => 2 * v + b.toNat) vs bs).map popcount) =
      weightedBits ws bs + weightedSum ws (vs.map popcount) := by
  induction ws generalizing vs bs with
  | nil => simp [weightedSum, weightedBits]
  | cons c cs ih =>
    cases vs with
    | nil =>
      cases bs with
      | nil => simp [weightedSum, weightedBits]
      | cons _ _ => simp at hlen
    | cons v vs' =>
      cases bs with
      | nil => simp at hlen
      | cons b bs' =>
        simp only [List.length_cons, Nat.succ.injEq] at hlen
        simp only [List.zipWith_cons_cons, List.map_cons, weightedSum, weightedBits]
        rw [popcount_bit b v, ih vs' bs' hlen]
        cases b
        · simp; omega
        · simp [Int.mul_add]; omega

private theorem evalSysFrom_length (es : List BitExpr) (s x y : Nat) :
    (evalSysFrom es s x y).length = es.length := by
  induction es generalizing s with
  | nil => rfl
  | cons _ rest ih => simp [evalSysFrom, ih]

private theorem stepSys_bits_length (es : List BitExpr) (s : Nat) (bx by_ : Bool) :
    (stepSys es s bx by_).2.length = es.length := by
  induction es generalizing s with
  | nil => rfl
  | cons _ rest ih => simp [stepSys, ih]

theorem weightedPopFrom_step (es : List BitExpr) (ws : List Int) (hv : sysValid es = true)
    (s x y : Nat) (hs : s < 2 ^ sysWidth es) :
    let res := stepSys es s (x % 2 == 1) (y % 2 == 1)
    weightedPopFrom es ws s x y =
      weightedBits ws res.2 + weightedPopFrom es ws res.1 (x / 2) (y / 2) := by
  unfold weightedPopFrom
  rw [evalSysFrom_step es hv s x y hs]
  apply weightedSum_zip_pop
  rw [evalSysFrom_length, stepSys_bits_length]

-- ============================================================================
-- Section 4: Compact Raw-Bit Wire Codec (`ByteArray` -> `BitReader` -> `RawCert`)
-- ============================================================================

private theorem mem_alphabetOf (twoVar : Bool) (bx by_ : Bool)
    (h : twoVar = true ∨ by_ = false) :
    (bx, by_) ∈ alphabetOf twoVar := by
  cases twoVar
  · rcases h with h1 | h2
    · cases h1
    · subst h2; cases bx <;> simp [alphabetOf]
  · cases bx <;> cases by_ <;> simp [alphabetOf]

private theorem lookupPhi_spec {ss : List Nat} {ps : List Int} {s : Nat} {p : Int}
    (h : lookupPhi ss ps s = some p) :
    ∃ idx : Nat, ss[idx]? = some s ∧ ps[idx]? = some p := by
  induction ss generalizing ps with
  | nil => simp [lookupPhi] at h
  | cons s0 ss' ih =>
    cases ps with
    | nil => simp [lookupPhi] at h
    | cons p0 ps' =>
      simp only [lookupPhi] at h
      by_cases heq : (s0 == s) = true
      · simp only [heq, ↓reduceIte, Option.some.injEq] at h
        refine ⟨0, ?_, ?_⟩
        · simp [beq_iff_eq.mp heq]
        · simp [h]
      · simp only [heq, Bool.false_eq_true, ↓reduceIte] at h
        rcases ih h with ⟨idx, hs, hp⟩
        exact ⟨idx + 1, hs, hp⟩

private theorem checkPopRows_at {isEq : Bool} {es : List BitExpr} {ws : List Int}
    {twoVar : Bool} {allS : List Nat} {allP : List Int} {ss : List Nat} {ps : List Int}
    (h : checkPopRows isEq es ws twoVar allS allP ss ps = true)
    {idx : Nat} {s : Nat} {p : Int}
    (hs : ss[idx]? = some s) (hp : ps[idx]? = some p) :
    (if isEq then weightedFlush es ws s = p else p ≤ weightedFlush es ws s) ∧
    ∀ ab ∈ alphabetOf twoVar, checkPopEdge isEq es ws allS allP s p ab.1 ab.2 = true := by
  induction ss generalizing ps idx with
  | nil => simp at hs
  | cons s0 ss' ih =>
    cases ps with
    | nil => simp at hp
    | cons p0 ps' =>
      simp only [checkPopRows, Bool.and_eq_true] at h
      rcases h with ⟨⟨hTerm, hEdges⟩, hRest⟩
      cases idx with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hs hp
        subst hs; subst hp
        refine ⟨?_, ?_⟩
        · cases isEq <;> simpa using hTerm
        · intro ab hab
          exact List.all_eq_true.mp hEdges ab hab
      | succ idx' =>
        exact ih hRest hs hp

private theorem stateInList_spec {ss : List Nat} {s : Nat}
    (h : stateInList ss s = true) : s ∈ ss := by
  induction ss with
  | nil => simp [stateInList] at h
  | cons s0 ss' ih =>
    simp only [stateInList, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | hrest
    · exact List.Mem.head _
    · exact List.Mem.tail _ (ih hrest)

private theorem checkBitEqRows_mem {e0 e1 : BitExpr} {twoVar : Bool} {allS ss : List Nat}
    (h : checkBitEqRows e0 e1 twoVar allS ss = true) {s : Nat} (hmem : s ∈ ss) :
    (match flushSys [e0, e1] s with | [f0, f1] => f0 = f1 | _ => False) ∧
    ∀ ab ∈ alphabetOf twoVar,
      let res := stepSys [e0, e1] s ab.1 ab.2
      (match res.2 with | [b0, b1] => b0 = b1 | _ => False) ∧ res.1 ∈ allS := by
  induction ss with
  | nil => cases hmem
  | cons s0 ss' ih =>
    simp only [checkBitEqRows, Bool.and_eq_true] at h
    rcases h with ⟨⟨hTerm, hEdges⟩, hRest⟩
    cases hmem with
    | head =>
      refine ⟨?_, ?_⟩
      · generalize hfl : flushSys [e0, e1] s = fl at hTerm ⊢
        cases fl with
        | nil => simp at hTerm
        | cons f0 r0 =>
          cases r0 with
          | nil => simp at hTerm
          | cons f1 r1 =>
            cases r1 with
            | nil => simpa using hTerm
            | cons _ _ => simp at hTerm
      · intro ab hab
        have he := List.all_eq_true.mp hEdges ab hab
        simp only [Bool.and_eq_true] at he
        refine ⟨?_, stateInList_spec he.2⟩
        have ho := he.1
        generalize hr : (stepSys [e0, e1] s ab.1 ab.2).2 = outs at ho ⊢
        cases outs with
        | nil => simp at ho
        | cons b0 r0 =>
          cases r0 with
          | nil => simp at ho
          | cons b1 r1 =>
            cases r1 with
            | nil => simpa using ho
            | cons _ _ => simp at ho
    | tail _ hmem' => exact ih hRest hmem'

private theorem pop_induction_aux
    (isEq : Bool) (es : List BitExpr) (ws : List Int) (twoVar : Bool)
    (allS : List Nat) (allP : List Int)
    (hv : sysValid es = true)
    (hB : ∀ s ∈ allS, s < 2 ^ sysWidth es)
    (hRows : checkPopRows isEq es ws twoVar allS allP allS allP = true) :
    ∀ n x y, x + y ≤ n -> (twoVar = true ∨ y = 0) ->
      ∀ (idx : Nat) (s : Nat) (p : Int), allS[idx]? = some s -> allP[idx]? = some p ->
        if isEq then weightedPopFrom es ws s x y = p
        else p ≤ weightedPopFrom es ws s x y := by
  intro n
  induction n with
  | zero =>
    intro x y hxy _ idx s p hs hp
    have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    subst hx; subst hy
    have hrow := (checkPopRows_at hRows hs hp).1
    unfold weightedPopFrom weightedFlush at *
    rw [evalSysFrom_flush]
    exact hrow
  | succ n ih =>
    intro x y hxy htv idx s p hs hp
    by_cases h0 : x = 0 ∧ y = 0
    · rcases h0 with ⟨rfl, rfl⟩
      have hrow := (checkPopRows_at hRows hs hp).1
      unfold weightedPopFrom weightedFlush at *
      rw [evalSysFrom_flush]
      exact hrow
    · have hsum : x / 2 + y / 2 ≤ n := by omega
      have hby : twoVar = true ∨ (y % 2 == 1) = false := by
        rcases htv with h1 | h2
        · exact Or.inl h1
        · subst h2; exact Or.inr rfl
      have htv' : twoVar = true ∨ y / 2 = 0 := by
        rcases htv with h1 | h2
        · exact Or.inl h1
        · subst h2; exact Or.inr rfl
      have hmem : s ∈ allS := List.mem_of_getElem? hs
      have hs_lt : s < 2 ^ sysWidth es := hB s hmem
      have hab : (x % 2 == 1, y % 2 == 1) ∈ alphabetOf twoVar :=
        mem_alphabetOf twoVar (x % 2 == 1) (y % 2 == 1) hby
      have hedge := (checkPopRows_at hRows hs hp).2 (x % 2 == 1, y % 2 == 1) hab
      simp only [checkPopEdge] at hedge
      generalize hstep : stepSys es s (x % 2 == 1) (y % 2 == 1) = res at hedge
      generalize hlook : lookupPhi allS allP res.1 = opt at hedge
      cases opt with
      | none => simp at hedge
      | some p' =>
        rcases lookupPhi_spec hlook with ⟨idx', hs', hp'⟩
        have hrec := ih (x / 2) (y / 2) hsum htv' idx' res.1 p' hs' hp'
        have hstep_eq := weightedPopFrom_step es ws hv s x y hs_lt
        rw [hstep] at hstep_eq
        rw [hstep_eq]
        cases isEq
        · simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at hedge hrec ⊢
          omega
        · simp only [↓reduceIte, decide_eq_true_eq] at hedge hrec ⊢
          omega

private theorem bitEq_induction_aux
    (e0 e1 : BitExpr) (twoVar : Bool) (allS : List Nat)
    (hv : sysValid [e0, e1] = true)
    (hB : ∀ s ∈ allS, s < 2 ^ sysWidth [e0, e1])
    (hRows : checkBitEqRows e0 e1 twoVar allS allS = true) :
    ∀ n x y, x + y ≤ n -> (twoVar = true ∨ y = 0) ->
      ∀ s, s ∈ allS ->
        match evalSysFrom [e0, e1] s x y with
        | [v0, v1] => v0 = v1
        | _ => False := by
  intro n
  induction n with
  | zero =>
    intro x y hxy _ s hmem
    have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    subst hx; subst hy
    rw [evalSysFrom_flush]
    exact (checkBitEqRows_mem hRows hmem).1
  | succ n ih =>
    intro x y hxy htv s hmem
    by_cases h0 : x = 0 ∧ y = 0
    · rcases h0 with ⟨rfl, rfl⟩
      rw [evalSysFrom_flush]
      exact (checkBitEqRows_mem hRows hmem).1
    · have hsum : x / 2 + y / 2 ≤ n := by omega
      have hby : twoVar = true ∨ (y % 2 == 1) = false := by
        rcases htv with h1 | h2
        · exact Or.inl h1
        · subst h2; exact Or.inr rfl
      have htv' : twoVar = true ∨ y / 2 = 0 := by
        rcases htv with h1 | h2
        · exact Or.inl h1
        · subst h2; exact Or.inr rfl
      have hs_lt : s < 2 ^ sysWidth [e0, e1] := hB s hmem
      have hab := mem_alphabetOf twoVar (x % 2 == 1) (y % 2 == 1) hby
      have hrow := (checkBitEqRows_mem hRows hmem).2 (x % 2 == 1, y % 2 == 1) hab
      have hstep := evalSysFrom_step [e0, e1] hv s x y hs_lt
      generalize hres : stepSys [e0, e1] s (x % 2 == 1) (y % 2 == 1) = res at hrow hstep
      rcases hrow with ⟨hb_eq, hmem'⟩
      have hrec := ih (x / 2) (y / 2) hsum htv' res.1 hmem'
      rw [hstep]
      generalize hev : evalSysFrom [e0, e1] res.1 (x / 2) (y / 2) = vs at hrec ⊢
      generalize hbo : res.2 = bs at hb_eq ⊢
      cases vs with
      | nil => exact hrec.elim
      | cons v0 vr0 =>
        cases vr0 with
        | nil => exact hrec.elim
        | cons v1 vr1 =>
          cases vr1 with
          | cons _ _ => exact hrec.elim
          | nil =>
            cases bs with
            | nil => exact hb_eq.elim
            | cons b0 br0 =>
              cases br0 with
              | nil => exact hb_eq.elim
              | cons b1 br1 =>
                cases br1 with
                | cons _ _ => exact hb_eq.elim
                | nil =>
                  simp only [List.zipWith_cons_cons, List.zipWith_nil_left]
                  rw [hrec, hb_eq]

/-- General Soundness Meta-Theorem for `checkCert`. -/
theorem checkCert_sound (c : DecodedCert) (h : checkCert c = true) : c.goal.denote := by
  unfold checkCert at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hpre
    have hv : sysValid c.goal.exprs = true := by
      cases hsv : sysValid c.goal.exprs <;> simp [hsv] at hpre ⊢
    have hB : ∀ s ∈ c.states, s < 2 ^ sysWidth c.goal.exprs := by
      have hall : c.states.all (fun s => decide (s < 2 ^ sysWidth c.goal.exprs)) = true := by
        cases ha : c.states.all (fun s => decide (s < 2 ^ sysWidth c.goal.exprs)) <;>
          simp [hv, ha] at hpre ⊢
      intro s hmem
      exact of_decide_eq_true (List.all_eq_true.mp hall s hmem)
    have hVarY : c.goal.twoVar = true ∨ sysNoVarY c.goal.exprs = true := by
      cases htv : c.goal.twoVar <;> cases hny : sysNoVarY c.goal.exprs <;>
        simp [htv, hny] at hpre ⊢
    unfold Goal.denote
    cases hsch : c.goal.schema
    · -- popIneq
      simp only [hsch] at h ⊢
      cases hst : c.states with
      | nil => simp [hst] at h
      | cons s0 ss =>
        cases s0 with
        | succ _ => simp [hst] at h
        | zero =>
          cases hph : c.phi with
          | nil => simp [hst, hph] at h
          | cons p0 ps =>
            simp only [hst, hph, Bool.and_eq_true, decide_eq_true_eq] at h
            rcases h with ⟨hinit, hrows⟩
            intro x y
            have hmain : p0 ≤ weightedPop c.goal.exprs c.goal.weights x y := by
              unfold weightedPop
              rw [← evalSysFrom_zero]
              rcases hVarY with htv | hny
              · have := pop_induction_aux false c.goal.exprs c.goal.weights c.goal.twoVar
                  (0 :: ss) (p0 :: ps) hv (by simpa [hst] using hB) hrows
                  (x + y) x y (Nat.le_refl _) (Or.inl htv) 0 0 p0 rfl rfl
                simpa [weightedPopFrom] using this
              · have := pop_induction_aux false c.goal.exprs c.goal.weights c.goal.twoVar
                  (0 :: ss) (p0 :: ps) hv (by simpa [hst] using hB) hrows
                  x x 0 (by omega) (Or.inr rfl) 0 0 p0 rfl rfl
                simp only [Bool.false_eq_true, ↓reduceIte, weightedPopFrom] at this
                rwa [evalSysFrom_noVarY c.goal.exprs hny 0 x y 0]
            omega
    · -- popEq
      simp only [hsch] at h ⊢
      cases hst : c.states with
      | nil => simp [hst] at h
      | cons s0 ss =>
        cases s0 with
        | succ _ => simp [hst] at h
        | zero =>
          cases hph : c.phi with
          | nil => simp [hst, hph] at h
          | cons p0 ps =>
            simp only [hst, hph, Bool.and_eq_true, decide_eq_true_eq] at h
            rcases h with ⟨hinit, hrows⟩
            intro x y
            have hmain : weightedPop c.goal.exprs c.goal.weights x y = p0 := by
              unfold weightedPop
              rw [← evalSysFrom_zero]
              rcases hVarY with htv | hny
              · have := pop_induction_aux true c.goal.exprs c.goal.weights c.goal.twoVar
                  (0 :: ss) (p0 :: ps) hv (by simpa [hst] using hB) hrows
                  (x + y) x y (Nat.le_refl _) (Or.inl htv) 0 0 p0 rfl rfl
                simpa [weightedPopFrom] using this
              · have := pop_induction_aux true c.goal.exprs c.goal.weights c.goal.twoVar
                  (0 :: ss) (p0 :: ps) hv (by simpa [hst] using hB) hrows
                  x x 0 (by omega) (Or.inr rfl) 0 0 p0 rfl rfl
                simp only [↓reduceIte, weightedPopFrom] at this
                rwa [evalSysFrom_noVarY c.goal.exprs hny 0 x y 0]
            omega
    · -- bitEq
      simp only [hsch] at h ⊢
      cases hes : c.goal.exprs with
      | nil => simp [hes] at h
      | cons e0 er0 =>
        cases er0 with
        | nil => simp [hes] at h
        | cons e1 er1 =>
          cases er1 with
          | cons _ _ => simp [hes] at h
          | nil =>
            cases hst : c.states with
            | nil => simp [hes, hst] at h
            | cons s0 ss =>
              cases s0 with
              | succ _ => simp [hes, hst] at h
              | zero =>
                simp only [hes, hst] at h hv hB hVarY
                intro x y
                have h0mem : (0 : Nat) ∈ (0 :: ss) := List.Mem.head _
                rcases hVarY with htv | hny
                · have hres := bitEq_induction_aux e0 e1 c.goal.twoVar (0 :: ss) hv hB h
                    (x + y) x y (Nat.le_refl _) (Or.inl htv) 0 h0mem
                  rw [evalSysFrom_zero] at hres
                  simpa [evalSys] using hres
                · have hres := bitEq_induction_aux e0 e1 c.goal.twoVar (0 :: ss) hv hB h
                    x x 0 (by omega) (Or.inr rfl) 0 h0mem
                  rw [← evalSysFrom_noVarY [e0, e1] hny 0 x y 0, evalSysFrom_zero] at hres
                  simpa [evalSys] using hres

/-- Top-level Soundness Meta-Theorem for Raw-Bit `ByteArray` Proof-Carrying Certificates. -/
theorem soundness_verifyGoal (raw : ByteArray) (g : Goal) (h : verifyGoal raw g = true) :
    g.denote := by
  unfold verifyGoal at h
  cases hd : decodeRawCert raw with
  | none => simp [hd] at h
  | some c =>
    simp only [hd, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨hgeq, hchk⟩
    rw [← hgeq]
    exact checkCert_sound c hchk

theorem soundness_verifyRawCert (raw : ByteArray) (h : verifyRawCert raw = true) :
    ∃ c, decodeRawCert raw = some c ∧ c.goal.denote := by
  unfold verifyRawCert at h
  cases hd : decodeRawCert raw with
  | none => simp [hd] at h
  | some c =>
    simp only [hd] at h
    exact ⟨c, rfl, checkCert_sound c h⟩

-- ============================================================================
-- Section 7: Ten Concrete Infinite Theorems Discharged from Compact Raw Bytes!
-- ============================================================================

-- Synthesized raw-bit ByteArray certificates (from explore_and_verify.py):

/-- Theorem 1 (13-byte cert, Schema 0): Exact Gray-Code / 3x Convex-Hull Uncertainty Principle. -/
theorem gray_3x_uncertainty (x : Nat) :
    2 * popcount x ≤ 2 * popcount (3 * x) + popcount (x ^^^ (x >>> 1)) := by
  have h := soundness_verifyGoal certGray3x
    { schema := .popIneq, twoVar := false,
      exprs := [.varX, .mulK 3 .varX, .xor (.mulK 2 .varX) (.even .varX)],
      weights := [-2, 2, 1], offset := 0 } (by decide) x 0
  simp only [weightedPop, weightedSum, evalSys, evalExpr, List.map, Int.ofNat_eq_natCast] at h
  rw [popcount_gray_shift] at h
  omega

/-- Theorem 2 (25-byte cert, Schema 0): Non-Subadditive (3, 11) 3/4 Lower Bound (constant not proved optimal). -/
theorem pop_3x_11x_sharp (x : Nat) :
    3 * popcount x ≤ 4 * (popcount (3 * x) + popcount (11 * x)) := by
  have h := soundness_verifyGoal cert3x11x
    { schema := .popIneq, twoVar := false,
      exprs := [.varX, .mulK 3 .varX, .mulK 11 .varX],
      weights := [-3, 4, 4], offset := 0 } (by decide) x 0
  simp only [weightedPop, weightedSum, evalSys, evalExpr, List.map, Int.ofNat_eq_natCast] at h
  omega

/-- Theorem 3 (26-byte cert, Schema 0): Non-Subadditive (5, 9) 2/3 Lower Bound (constant not proved optimal). -/
theorem pop_5x_9x_lower (x : Nat) :
    2 * popcount x ≤ 3 * (popcount (5 * x) + popcount (9 * x)) := by
  have h := soundness_verifyGoal cert5x9xLower
    { schema := .popIneq, twoVar := false,
      exprs := [.varX, .mulK 5 .varX, .mulK 9 .varX],
      weights := [-2, 3, 3], offset := 0 } (by decide) x 0
  simp only [weightedPop, weightedSum, evalSys, evalExpr, List.map, Int.ofNat_eq_natCast] at h
  omega

/-- Theorem 4 (23-byte cert, Schema 0): Zero-Slack Bitwise-AND (5, 9) 3/2 Upper Bound (constant not proved optimal). -/
theorem pop_5x_and_9x_upper (x : Nat) :
    2 * popcount ((5 * x) &&& (9 * x)) ≤ 3 * popcount x := by
  have h := soundness_verifyGoal cert5xAnd9xUpper
    { schema := .popIneq, twoVar := false,
      exprs := [.varX, .and (.mulK 5 .varX) (.mulK 9 .varX)],
      weights := [3, -2], offset := 0 } (by decide) x 0
  simp only [weightedPop, weightedSum, evalSys, evalExpr, List.map, Int.ofNat_eq_natCast] at h
  omega

/-- Theorem 5 (23-byte cert, Schema 0): Bitwise-OR Separation Law (3, 11) 2/3 Lower Bound (constant not proved optimal). -/
theorem pop_3x_or_11x_sharp (x : Nat) :
    2 * popcount x ≤ 3 * popcount ((3 * x) ||| (11 * x)) := by
  have h := soundness_verifyGoal cert3xOr11x
    { schema := .popIneq, twoVar := false,
      exprs := [.varX, .or (.mulK 3 .varX) (.mulK 11 .varX)],
      weights := [-2, 3], offset := 0 } (by decide) x 0
  simp only [weightedPop, weightedSum, evalSys, evalExpr, List.map, Int.ofNat_eq_natCast] at h
  omega

/-- Theorem 6 (42-byte cert, Schema 0): 3-Body Super-Linear Synergy (3, 7, 11) 4/3 Bound (constant not proved optimal). -/
theorem pop_3x_7x_11x_synergy (x : Nat) :
    4 * popcount x ≤ 3 * (popcount (3 * x) + popcount (7 * x) + popcount (11 * x)) := by
  have h := soundness_verifyGoal cert3x7x11x
    { schema := .popIneq, twoVar := false,
      exprs := [.varX, .mulK 3 .varX, .mulK 7 .varX, .mulK 11 .varX],
      weights := [-4, 3, 3, 3], offset := 0 } (by decide) x 0
  simp only [weightedPop, weightedSum, evalSys, evalExpr, List.map, Int.ofNat_eq_natCast] at h
  omega

/-- Theorem 7 (14-byte cert, Schema 0): 2-Variable Mixed Carry-XOR 1/3 Lower Bound (constant not proved optimal). -/
theorem pop_2var_3x_plus_y_xor (x y : Nat) :
    popcount x + popcount y ≤ 3 * (popcount (3 * x + y) + popcount (x ^^^ y)) := by
  have h := soundness_verifyGoal cert2Var3xY
    { schema := .popIneq, twoVar := true,
      exprs := [.varX, .varY, .add (.mulK 3 .varX) .varY, .xor .varX .varY],
      weights := [-1, -1, 3, 3], offset := 0 } (by decide) x y
  simp only [weightedPop, weightedSum, evalSys, evalExpr, List.map, Int.ofNat_eq_natCast] at h
  omega

/-- Theorem 8 (29-byte cert, Schema 1): 2-Var Exact Carry-Cascade Popcount Conservation Law. -/
theorem pop_eq_3x_plus_y_cascade (x y : Nat) :
    popcount (3 * x + y) +
    popcount ((3 * x + y) ^^^ ((3 * x) ^^^ y)) +
    popcount ((3 * x) ^^^ (x ^^^ (2 * x))) =
    2 * popcount x + popcount y := by
  have h := soundness_verifyGoal certPopEq3xY
    { schema := .popEq, twoVar := true,
      exprs := [
        .varX, .varY,
        .add (.mulK 3 .varX) .varY,
        .xor (.add (.mulK 3 .varX) .varY) (.xor (.mulK 3 .varX) .varY),
        .xor (.mulK 3 .varX) (.xor .varX (.mulK 2 .varX))
      ],
      weights := [-2, -1, 1, 1, 1], offset := 0 } (by decide) x y
  simp only [weightedPop, weightedSum, evalSys, evalExpr, List.map, Int.ofNat_eq_natCast] at h
  omega

/-- Theorem 9 (33-byte cert, Schema 2): Nonlinear Bitwise-Carry Collapse to 8*x. -/
theorem bit_eq_3x_5x_8x (x : Nat) :
    ((3 * x) ||| (5 * x)) + ((3 * x) &&& (5 * x)) = 8 * x := by
  have h := soundness_verifyGoal certBitEq3x5x8x
    { schema := .bitEq, twoVar := false,
      exprs := [
        .add (.or (.mulK 3 .varX) (.mulK 5 .varX)) (.and (.mulK 3 .varX) (.mulK 5 .varX)),
        .mulK 8 .varX
      ],
      weights := [], offset := 0 } (by decide) x 0
  simpa [evalExpr] using h

/-- Theorem 10 (19-byte cert, Schema 2): 2-Var Coupled Carry-Collapse Identity. -/
theorem bit_eq_3x_plus_y_collapse (x y : Nat) :
    (3 * x + y) + ((3 * x) ^^^ y) = 2 * ((3 * x) ||| y) := by
  have h := soundness_verifyGoal certBitEq3xY
    { schema := .bitEq, twoVar := true,
      exprs := [
        .add (.add (.mulK 3 .varX) .varY) (.xor (.mulK 3 .varX) .varY),
        .mulK 2 (.or (.mulK 3 .varX) .varY)
      ],
      weights := [], offset := 0 } (by decide) x y
  simpa [evalExpr] using h

-- ============================================================================
-- Section 8: Kernel-Checked Non-Vacuity, Sharpness & Mutation-Rejection Proofs
-- ============================================================================

-- Non-vacuity: all 3 schemas are genuinely inhabited by raw-bit certificates!
theorem nonvacuous_schema0 : verifyRawCert cert3x11x = true := by decide
theorem nonvacuous_schema1 : verifyRawCert certPopEq3xY = true := by decide
theorem nonvacuous_schema2 : verifyRawCert certBitEq3xY = true := by decide

-- Kernel-checked exact zero-slack sharpness witnesses for Theorem 4 (`pop_5x_and_9x_upper`):
theorem sharp_5x_and_9x_exact_3 :
    2 * popcount ((5 * 3) &&& (9 * 3)) = 3 * popcount 3 := by decide
theorem sharp_5x_and_9x_exact_99 :
    2 * popcount ((5 * 99) &&& (9 * 99)) = 3 * popcount 99 := by decide
theorem sharp_5x_and_9x_beats_1 :
    ¬ (popcount ((5 * 3) &&& (9 * 3)) ≤ popcount 3) := by decide

-- Kernel-checked sharpness witnesses for Theorem 1 (`gray_3x_uncertainty`):
-- Both extremes achieve slack 1: x = 2^6 - 1 = 63 (all-ones) and x = (2^7 + 1)/3 = 43 (alternating)
theorem sharp_gray_3x_allones :
    2 * popcount (3 * 63) + popcount (63 ^^^ (63 >>> 1)) = 2 * popcount 63 + 1 := by decide
theorem sharp_gray_3x_altbits :
    2 * popcount (3 * 43) + popcount (43 ^^^ (43 >>> 1)) = 2 * popcount 43 + 1 := by decide

-- Kernel-checked sharpness witnesses for Theorem 7 (`pop_2var_3x_plus_y_xor`):
-- Exact constant slack 1 at (x, y) = (11, 31) and (43, 127); tightening 1/3 -> 2/5 fails at (11, 31)!
theorem sharp_2var_3x_y_slack1_a :
    3 * (popcount (3 * 11 + 31) + popcount (11 ^^^ 31)) = popcount 11 + popcount 31 + 1 := by decide
theorem sharp_2var_3x_y_slack1_b :
    3 * (popcount (3 * 43 + 127) + popcount (43 ^^^ 127)) = popcount 43 + popcount 127 + 1 := by decide
theorem sharp_2var_3x_y_beats_2_5 :
    ¬ (2 * (popcount 11 + popcount 31) ≤ 5 * (popcount (3 * 11 + 31) + popcount (11 ^^^ 31))) := by
  decide

-- Kernel-checked sharpness witness for Theorem 2 (`pop_3x_11x_sharp`) at x = 187 and x = 11963:
theorem sharp_3x_11x_slack10_a :
    4 * (popcount (3 * 187) + popcount (11 * 187)) = 3 * popcount 187 + 10 := by decide
theorem sharp_3x_11x_slack10_b :
    4 * (popcount (3 * 11963) + popcount (11 * 11963)) = 3 * popcount 11963 + 10 := by decide

-- Kernel-checked sharpness witness for Theorem 6 (`pop_3x_7x_11x_synergy`) at x = 111:
theorem sharp_3x_7x_11x_slack18 :
    3 * (popcount (3 * 111) + popcount (7 * 111) + popcount (11 * 111)) =
      4 * popcount 111 + 18 := by decide

-- Kernel-checked Negative / Adversarial Mutation Tests (broken certs MUST be rejected!):

theorem reject_empty : verifyRawCert (ByteArray.mk #[]) = false := by decide

-- 2. Truncated certificate rejected
theorem reject_truncated :
    verifyRawCert (ByteArray.mk #[0x0A, 0x41, 0x82, 0x2A, 0x30, 0xCC]) = false := by decide

-- 3. Canonical framing violation: valid cert + extra trailing zero byte rejected!
theorem reject_trailing_zero_byte :
    verifyRawCert (ByteArray.mk #[0x0A, 0x41, 0x82, 0x2A, 0x30, 0xCC, 0x28, 0x10,
                                  0xD8, 0x9E, 0x03, 0xC8, 0x04, 0x00]) = false := by decide

-- 4. Canonical framing violation: non-zero padding bit in last byte (bit 103) rejected!
theorem reject_nonzero_padding :
    verifyRawCert (flipBit certGray3x 103) = false := by decide

-- 5. Corrupted magic nibble (bit 0) rejected!
theorem reject_bad_magic :
    verifyRawCert (flipBit cert3x11x 0) = false := by decide

-- 6. Invalid reserved schema opcode `3` (flip bits 4 and 5 in Schema 0 cert) rejected!
theorem reject_invalid_schema_3 :
    verifyRawCert (flipBit (flipBit certGray3x 4) 5) = false := by decide

-- 7. Corrupted reachable-state bit inside cert3x11x (bit 80) rejected!
theorem reject_corrupted_state :
    verifyRawCert (flipBit cert3x11x 80) = false := by decide

-- 8. Corrupted potential Phi bit inside cert3x11x (bit 170) rejected!
theorem reject_corrupted_phi :
    verifyRawCert (flipBit cert3x11x 170) = false := by decide

-- 9. Corrupted Schema 1 (`popEq`) conservation potential bit rejected!
theorem reject_corrupted_pop_eq :
    verifyRawCert (flipBit certPopEq3xY 200) = false := by decide

-- 10. Corrupted Schema 2 (`bitEq`) state/AST bit rejected!
theorem reject_corrupted_bit_eq :
    verifyRawCert (flipBit certBitEq3xY 90) = false := by decide

-- 11. Goal-mismatch attack: valid cert for (3,11) rejected when presented for (5,9)!
theorem reject_goal_mismatch :
    verifyGoal cert3x11x
      { schema := .popIneq, twoVar := false,
        exprs := [.varX, .mulK 5 .varX, .mulK 9 .varX],
        weights := [-2, 3, 3], offset := 0 } = false := by decide

-- 12. Tightened false conjecture attack: valid cert rejected when claiming 4*pop(x) <= 5*(pop(3x)+pop(11x))
--     (4/5 = 0.80 > 3/4 = 0.75, so this claim is false.)
theorem reject_false_tightened_goal :
    verifyGoal cert3x11x
      { schema := .popIneq, twoVar := false,
        exprs := [.varX, .mulK 3 .varX, .mulK 11 .varX],
        weights := [-4, 5, 5], offset := 0 } = false := by decide

-- 13. Illegal varY smuggling attack: flipping twoVar=1 -> twoVar=0 (bit 6) on a 2-var cert is rejected!
theorem reject_varY_in_onevar_cert :
    verifyRawCert (flipBit cert2Var3xY 6) = false := by decide

-- 14. Illegal varY smuggling attack on Schema 2 (`bitEq`) 2-var cert is rejected!
theorem reject_varY_in_onevar_biteq :
    verifyRawCert (flipBit certBitEq3xY 6) = false := by decide

end BitPackMC
