import BinaryPartitionWindowAutomata.Defs

namespace BinaryPartitionAutomaton
theorem digitSum_congr {f g : Nat → Nat} {n : Nat} {ds : List Nat}
    (h : ∀ d ∈ ds, d ≤ n → (n - d) % 2 = 0 → f ((n - d) / 2) = g ((n - d) / 2)) :
    digitSum f n ds = digitSum g n ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [digitSum]
    have h1 : (if d ≤ n ∧ (n - d) % 2 = 0 then f ((n - d) / 2) else 0) =
              (if d ≤ n ∧ (n - d) % 2 = 0 then g ((n - d) / 2) else 0) := by
      split
      · next hcond => exact h d (by simp) hcond.1 hcond.2
      · rfl
    rw [h1, ih (fun x hx => h x (by simp [hx]))]

theorem digitSum_append (f : Nat → Nat) (n : Nat) (xs ys : List Nat) :
    digitSum f n (xs ++ ys) = digitSum f n xs + digitSum f n ys := by
  induction xs with
  | nil => simp [digitSum]
  | cons d ds ih => simp [digitSum, ih, Nat.add_assoc]

theorem digitSum_mod (f : Nat → Nat) (n M : Nat) (ds : List Nat) :
    digitSum f n ds % M = digitSum (fun k => f k % M) n ds % M := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [digitSum]
    split
    · rw [Nat.add_mod, ih]
      conv => rhs; rw [Nat.add_mod, Nat.mod_mod]
    · rw [Nat.add_mod, ih, ← Nat.add_mod]

/-- Fuel independence: `binPartFuel D f1 n = binPartFuel D f2 n` whenever `n ≤ f1` and `n ≤ f2`. -/
theorem binPartFuel_indep (D : List Nat) :
    ∀ n f1 f2 : Nat, n ≤ f1 → n ≤ f2 → binPartFuel D f1 n = binPartFuel D f2 n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f1 f2 hf1 hf2
    cases n with
    | zero => cases f1 <;> cases f2 <;> rfl
    | succ m =>
      cases f1 with
      | zero => omega
      | succ f1' =>
        cases f2 with
        | zero => omega
        | succ f2' =>
          simp only [binPartFuel]
          apply digitSum_congr
          intro d _ hle _
          exact ih ((m + 1 - d) / 2) (by omega) f1' f2' (by omega) (by omega)

theorem binPart_zero (D : List Nat) : binPart D 0 = 1 := rfl

theorem binPart_pos (D : List Nat) (n : Nat) (hn : n > 0) :
    binPart D n = digitSum (binPart D) n D := by
  cases n with
  | zero => omega
  | succ m =>
    unfold binPart
    simp only [binPartFuel]
    apply digitSum_congr
    intro d _ hle _
    exact binPartFuel_indep D ((m + 1 - d) / 2) m ((m + 1 - d) / 2) (by omega) (Nat.le_refl _)

theorem v2Fuel_indep : ∀ n f1 f2 : Nat, n ≤ f1 → n ≤ f2 → v2Fuel f1 n = v2Fuel f2 n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f1 f2 hf1 hf2
    cases n with
    | zero => cases f1 <;> cases f2 <;> simp [v2Fuel]
    | succ m =>
      cases f1 with
      | zero => omega
      | succ f1' =>
        cases f2 with
        | zero => omega
        | succ f2' =>
          simp only [v2Fuel]
          split
          · rw [ih ((m + 1) / 2) (by omega) f1' f2' (by omega) (by omega)]
          · rfl

theorem v2_two_mul (n : Nat) (hn : n > 0) : v2 (2 * n) = 1 + v2 n := by
  cases n with
  | zero => omega
  | succ k =>
    unfold v2
    have h1 : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    rw [h1]
    conv => lhs; unfold v2Fuel
    simp only [show (2 * k + 1) + 1 > 0 ∧ ((2 * k + 1) + 1) % 2 = 0 by omega,
               and_self, ↓reduceIte, show ((2 * k + 1) + 1) / 2 = k + 1 by omega]
    rw [v2Fuel_indep (k + 1) (2 * k + 1) (k + 1) (by omega) (Nat.le_refl _)]

theorem v2_odd (n : Nat) (h : n % 2 = 1) : v2 n = 0 := by
  cases n with
  | zero => omega
  | succ k =>
    unfold v2
    simp only [v2Fuel, show ¬ (k + 1 > 0 ∧ (k + 1) % 2 = 0) by omega, ↓reduceIte]

theorem v2_pow2 (k : Nat) : v2 (2 ^ k) = k := by
  induction k with
  | zero => exact v2_odd 1 (by decide)
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
    rw [hpow, v2_two_mul (2 ^ k) (Nat.pow_pos (by omega)), ih]
    omega

theorem v2_add_pow2 (k x : Nat) (hx0 : 0 < x) (hxl : x < 2 ^ k) :
    v2 (x + 2 ^ k) = v2 x := by
  induction k generalizing x with
  | zero => omega
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
    by_cases hpar : x % 2 = 0
    · have h1 : x + 2 ^ (k + 1) = 2 * (x / 2 + 2 ^ k) := by rw [hpow]; omega
      have h2 : x = 2 * (x / 2) := by omega
      rw [h1, v2_two_mul (x / 2 + 2 ^ k) (by omega)]
      conv => rhs; rw [h2, v2_two_mul (x / 2) (by omega)]
      rw [ih (x / 2) (by omega) (by rw [hpow] at hxl; omega)]
    · have h1 : (x + 2 ^ (k + 1)) % 2 = 1 := by rw [hpow]; omega
      rw [v2_odd (x + 2 ^ (k + 1)) h1, v2_odd x (by omega)]

theorem exists_pow2_mul_odd (m : Nat) (hm : m > 0) :
    ∃ u : Nat, u % 2 = 1 ∧ m = 2 ^ v2 m * u := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    by_cases hpar : m % 2 = 0
    · have hpos : m / 2 > 0 := by omega
      have hlt : m / 2 < m := by omega
      obtain ⟨u, hu_odd, hu_eq⟩ := ih (m / 2) hlt hpos
      refine ⟨u, hu_odd, ?_⟩
      have hm2 : m = 2 * (m / 2) := by omega
      have hv : v2 m = 1 + v2 (m / 2) := by
        conv => lhs; rw [hm2]
        exact v2_two_mul (m / 2) hpos
      rw [hv, show 1 + v2 (m / 2) = v2 (m / 2) + 1 by omega, Nat.pow_succ]
      calc m = 2 * (m / 2) := hm2
           _ = 2 * (2 ^ v2 (m / 2) * u) := congrArg (2 * ·) hu_eq
           _ = 2 ^ v2 (m / 2) * 2 * u := by
             rw [Nat.mul_comm 2 (2 ^ v2 (m / 2) * u), Nat.mul_assoc, Nat.mul_comm u 2, ← Nat.mul_assoc]
    · refine ⟨m, by omega, ?_⟩
      rw [v2_odd m (by omega)]
      simp

/-! ## Section 2: Reusable Finite-State Window-Automaton Congruence Compiler -/

theorem winVec_zero (D : List Nat) (M j : Nat) :
    winVec D M 0 j = initWin M j := by
  unfold winVec initWin
  cases j with
  | zero => simp [binPart_zero]
  | succ k => simp

theorem validDigitSetBool_sound {D : List Nat} {L : Nat} (h : validDigitSetBool D L = true) :
    ValidDigitSet D L := by
  unfold validDigitSetBool at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact h

theorem digitSum_zero_of_count_zero (f : Nat → Nat) (ds : List Nat) (h : ds.count 0 = 0) :
    digitSum f 0 ds = 0 := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [digitSum]
    have hd0 : d ≠ 0 := by
      intro heq; subst heq; simp at h
    have hds : ds.count 0 = 0 := by
      simp [hd0] at h; exact h
    simp [hd0, ih hds]

theorem digitSum_zero_of_count_one (f : Nat → Nat) (ds : List Nat) (h : ds.count 0 = 1) :
    digitSum f 0 ds = f 0 := by
  induction ds with
  | nil => simp at h
  | cons d ds ih =>
    simp only [digitSum]
    by_cases hd0 : d = 0
    · subst hd0
      have hds : ds.count 0 = 0 := by simp at h; omega
      simp [digitSum_zero_of_count_zero f ds hds]
    · have hds : ds.count 0 = 1 := by simp [hd0] at h; exact h
      simp [hd0, ih hds]

/-- At `n = 0`, `binPart D 0 = digitSum (binPart D) 0 D` whenever `D.count 0 = 1`. -/
theorem binPart_eq_digitSum (D : List Nat) (h0 : D.count 0 = 1) (n : Nat) :
    binPart D n = digitSum (binPart D) n D := by
  cases n with
  | zero =>
    rw [binPart_zero, digitSum_zero_of_count_one (binPart D) D h0, binPart_zero]
  | succ m =>
    exact binPart_pos D (m + 1) (by omega)

/-- Core Bit-Shift Window Step Lemma: `V(2n + b) = T_b(V(n))` for ALL `n`, `j < L`, `b : Bool`. -/
theorem winVec_bitStep (D : List Nat) (L M : Nat) (hD : ValidDigitSet D L)
    (b : Bool) (n j : Nat) (hj : j < L) :
    winVec D M (2 * n + if b then 1 else 0) j =
      stepWin D L M b (winVec D M n) j := by
  let bv := if b then 1 else 0
  change winVec D M (2 * n + bv) j = stepWin D L M b (winVec D M n) j
  unfold winVec stepWin
  by_cases hjn : j ≤ 2 * n + bv
  · simp only [hjn, ↓reduceIte]
    rw [binPart_eq_digitSum D hD.2 (2 * n + bv - j)]
    rw [digitSum_mod]
    congr 1
    suffices ∀ ds : List Nat, (∀ d ∈ ds, d ≤ L) →
        digitSum (fun k => binPart D k % M) (2 * n + bv - j) ds =
        stepWinSum L b (fun i => if i ≤ n then binPart D (n - i) % M else 0) j ds by
      exact this D hD.1
    intro ds hds
    induction ds with
    | nil => rfl
    | cons d ds ih =>
      simp only [digitSum, stepWinSum]
      have hdL : d ≤ L := hds d (by simp)
      have hterm :
          (if d ≤ 2 * n + bv - j ∧ (2 * n + bv - j - d) % 2 = 0
           then binPart D ((2 * n + bv - j - d) / 2) % M else 0) =
          (if bv ≤ j + d ∧ (j + d - bv) % 2 = 0 ∧ (j + d - bv) / 2 < L
           then (if (j + d - bv) / 2 ≤ n then binPart D (n - (j + d - bv) / 2) % M else 0)
           else 0) := by
        by_cases hc1 : d ≤ 2 * n + bv - j ∧ (2 * n + bv - j - d) % 2 = 0
        · simp only [hc1]
          by_cases hbv : bv ≤ j + d
          · have hev : (j + d - bv) % 2 = 0 := by omega
            have hlt : (j + d - bv) / 2 < L := by omega
            have hle : (j + d - bv) / 2 ≤ n := by omega
            have hidx : (2 * n + bv - j - d) / 2 = n - (j + d - bv) / 2 := by omega
            simp only [hbv, hev, hlt, hle, and_self, ↓reduceIte, hidx]
          · have : bv = 0 ∨ bv = 1 := by cases b <;> simp [bv]
            omega
        · simp only [hc1]
          by_cases hc2 : bv ≤ j + d ∧ (j + d - bv) % 2 = 0 ∧ (j + d - bv) / 2 < L
          · simp only [hc2]
            by_cases hle : (j + d - bv) / 2 ≤ n
            · exfalso; apply hc1; omega
            · simp [hle]
          · simp [hc2]
      change (if d ≤ 2 * n + bv - j ∧ (2 * n + bv - j - d) % 2 = 0
              then binPart D ((2 * n + bv - j - d) / 2) % M else 0) +
             digitSum (fun k => binPart D k % M) (2 * n + bv - j) ds =
             (if bv ≤ j + d ∧ (j + d - bv) % 2 = 0 ∧ (j + d - bv) / 2 < L
              then (if (j + d - bv) / 2 ≤ n then binPart D (n - (j + d - bv) / 2) % M else 0)
              else 0) +
             stepWinSum L b (fun i => if i ≤ n then binPart D (n - i) % M else 0) j ds
      rw [hterm, ih (fun x hx => hds x (by simp [hx]))]
  · simp only [hjn, ↓reduceIte]
    suffices stepWinSum L b (fun i => if i ≤ n then binPart D (n - i) % M else 0) j D = 0 by
      rw [this]; exact (Nat.zero_mod M).symm
    suffices ∀ ds : List Nat,
        stepWinSum L b (fun i => if i ≤ n then binPart D (n - i) % M else 0) j ds = 0 from this D
    intro ds
    induction ds with
    | nil => rfl
    | cons d ds ih =>
      simp only [stepWinSum, ih, Nat.add_zero]
      change (if bv ≤ j + d ∧ (j + d - bv) % 2 = 0 ∧ (j + d - bv) / 2 < L
              then (if (j + d - bv) / 2 ≤ n then binPart D (n - (j + d - bv) / 2) % M else 0)
              else 0) = 0
      by_cases hc : bv ≤ j + d ∧ (j + d - bv) % 2 = 0 ∧ (j + d - bv) / 2 < L
      · simp only [hc]
        have hgt : ¬ ((j + d - bv) / 2 ≤ n) := by omega
        simp [hgt]
      · simp [hc]

/-! ### Balanced Binary Lookup Tree & Structurally-Recursive Logarithmic Range Checker -/

theorem allBelowPow_sound (p : Nat → Bool) (limit : Nat) :
    ∀ d lo : Nat, allBelowPow p limit d lo = true →
      ∀ i, lo ≤ i → i < lo + 2 ^ d → i < limit → p i = true := by
  intro d
  induction d with
  | zero =>
    intro lo h i hlo hhi hlim
    simp only [allBelowPow] at h
    have heq : i = lo := by omega
    subst heq
    simpa [hlim] using h
  | succ d ih =>
    intro lo h i hlo hhi hlim
    simp only [allBelowPow, Bool.and_eq_true] at h
    have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; omega
    by_cases hlt : i < lo + 2 ^ d
    · exact ih lo h.1 i hlo hlt hlim
    · exact ih (lo + 2 ^ d) h.2 i (by omega) (by omega) hlim

theorem allLt_sound {d limit : Nat} {p : Nat → Bool} (h : allLt d limit p = true) :
    ∀ i, i < limit → p i = true := by
  unfold allLt at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  intro i hi
  exact allBelowPow_sound p limit d 0 h.2 i (Nat.zero_le i) (by omega) hi

namespace WindowAutomatonCert
theorem runState_zero (c : WindowAutomatonCert) : c.runState 0 = c.q0 := by
  rw [runState]

theorem runState_bitStep (c : WindowAutomatonCert) (h0 : c.trans false c.q0 = c.q0)
    (n : Nat) (b : Bool) :
    c.runState (2 * n + if b then 1 else 0) = c.trans b (c.runState n) := by
  cases n with
  | zero =>
    cases b with
    | false =>
      simp only [Nat.mul_zero, Nat.add_zero, Bool.false_eq_true, ↓reduceIte, runState_zero]
      exact h0.symm
    | true =>
      change c.runState 1 = c.trans true (c.runState 0)
      conv => lhs; unfold runState
      simp [runState_zero]
  | succ k =>
    cases b with
    | false =>
      have hpos : 2 * (k + 1) + 0 = (2 * k + 1) + 1 := by omega
      simp only [Bool.false_eq_true, ↓reduceIte, hpos]
      rw [runState]
      simp only [show ((2 * k + 1) + 1) % 2 = 0 by omega,
                 show (0 == 1) = false by rfl,
                 show ((2 * k + 1) + 1) / 2 = k + 1 by omega]
    | true =>
      have hpos : 2 * (k + 1) + 1 = (2 * k + 2) + 1 := by omega
      simp only [↓reduceIte, hpos]
      rw [runState]
      simp only [show ((2 * k + 2) + 1) % 2 = 1 by omega,
                 show (1 == 1) = true by rfl,
                 show ((2 * k + 2) + 1) / 2 = k + 1 by omega]

theorem stepWin_congr (D : List Nat) (L M : Nat) (b : Bool) {u v : Nat → Nat} (j : Nat)
    (h : ∀ i, i < L → u i = v i) :
    stepWin D L M b u j = stepWin D L M b v j := by
  unfold stepWin
  congr 1
  induction D with
  | nil => rfl
  | cons d ds ih =>
    simp only [stepWinSum]
    rw [ih]
    congr 1
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      split
      · next hc => exact h _ hc.2.2
      · rfl
    · simp only [↓reduceIte]
      split
      · next hc => exact h _ hc.2.2
      · rfl

theorem valid_facts {c : WindowAutomatonCert} (hv : c.isValid = true) :
    0 < c.L ∧ 0 < c.M ∧ 0 < c.S ∧ c.q0 < c.S ∧
    (∀ j < c.L, c.embed c.q0 j = initWin c.M j) ∧
    (∀ q < c.S, c.trans false q < c.S ∧ c.trans true q < c.S ∧
      (∀ j < c.L,
        c.embed (c.trans false q) j = stepWin c.D c.L c.M false (c.embed q) j ∧
        c.embed (c.trans true q) j = stepWin c.D c.L c.M true (c.embed q) j)) := by
  unfold isValid at hv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
  rcases hv with ⟨⟨⟨⟨⟨hL, hM⟩, hS⟩, hq0⟩, hinit⟩, hstep⟩
  refine ⟨hL, hM, hS, hq0, ?_, ?_⟩
  · intro j hj
    have := allLt_sound hinit j hj
    simpa [beq_iff_eq] using this
  · intro q hq
    have hqstep := allLt_sound hstep q hq
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hqstep
    rcases hqstep with ⟨⟨ht0, ht1⟩, hcomm⟩
    refine ⟨ht0, ht1, ?_⟩
    intro j hj
    have hjc := allLt_sound hcomm j hj
    simp only [Bool.and_eq_true, beq_iff_eq] at hjc
    exact hjc

/-- **Master Automaton Lifting Soundness Theorem (Finite Certificate → ∀ n : Nat).** -/
theorem soundness (c : WindowAutomatonCert) (hD : ValidDigitSet c.D c.L)
    (hv : c.isValid = true) :
    ∀ n : Nat, c.runState n < c.S ∧ ∀ j < c.L, winVec c.D c.M n j = c.embed (c.runState n) j := by
  have ⟨hL, hM, hS, hq0, hinit, hstep⟩ := valid_facts hv
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
      refine ⟨by simpa [runState_zero] using hq0, ?_⟩
      intro j hj
      rw [winVec_zero, runState_zero, hinit j hj]
    | succ m =>
      have hlt : (m + 1) / 2 < m + 1 := by omega
      have ⟨hqs, hqemb⟩ := ih ((m + 1) / 2) hlt
      have ⟨ht0, ht1, hcomm⟩ := hstep (c.runState ((m + 1) / 2)) hqs
      let b : Bool := ((m + 1) % 2 == 1)
      have hdecomp : m + 1 = 2 * ((m + 1) / 2) + if b then 1 else 0 := by
        cases hb : b
        · have hm : (m + 1) % 2 ≠ 1 := by simpa [b] using hb
          simp; omega
        · have hm : (m + 1) % 2 = 1 := by simpa [b] using hb
          simp; omega
      have hrun : c.runState (m + 1) = c.trans b (c.runState ((m + 1) / 2)) := by
        rw [runState]
      rw [hrun]
      refine ⟨?_, ?_⟩
      · cases b <;> assumption
      · intro j hj
        conv => lhs; rw [hdecomp]
        rw [winVec_bitStep c.D c.L c.M hD b ((m + 1) / 2) j hj]
        rw [stepWin_congr c.D c.L c.M b j hqemb]
        cases b with
        | false => exact (hcomm j hj).1.symm
        | true => exact (hcomm j hj).2.symm

theorem eval_mod_eq (c : WindowAutomatonCert) (hD : ValidDigitSet c.D c.L)
    (hv : c.isValid = true) (n : Nat) :
    binPart c.D n % c.M = c.embed (c.runState n) 0 := by
  have hL := (valid_facts hv).1
  have h := (soundness c hD hv n).2 0 hL
  simpa [winVec] using h

theorem runState_affine (c : WindowAutomatonCert) (h0 : c.trans false c.q0 = c.q0) :
    ∀ a offset n : Nat, offset < 2 ^ a →
      c.runState (2 ^ a * n + offset) = c.runBits (c.runState n) a offset := by
  intro a
  induction a with
  | zero =>
    intro offset n hoff
    have : offset = 0 := by omega
    subst this
    simp [runBits]
  | succ a ih =>
    intro offset n hoff
    let topBit : Bool := ((offset / 2 ^ a) % 2 == 1)
    let rem := offset % 2 ^ a
    have hrem : rem < 2 ^ a := Nat.mod_lt offset (Nat.pow_pos (by omega))
    have hlt2 : offset / 2 ^ a < 2 := by
      have hpow : 2 ^ (a + 1) = 2 * 2 ^ a := by rw [Nat.pow_succ]; omega
      rw [hpow] at hoff
      exact Nat.div_lt_of_lt_mul (by omega)
    have htop_val : offset / 2 ^ a = if topBit then 1 else 0 := by
      cases htb : topBit
      · have hm : (offset / 2 ^ a) % 2 ≠ 1 := by simpa [topBit] using htb
        simp only [Bool.false_eq_true, ↓reduceIte]
        generalize offset / 2 ^ a = q at hlt2 hm ⊢; omega
      · have hm : (offset / 2 ^ a) % 2 = 1 := by simpa [topBit] using htb
        simp only [↓reduceIte]
        generalize offset / 2 ^ a = q at hlt2 hm ⊢; omega
    have hsplit : 2 ^ (a + 1) * n + offset =
        2 ^ a * (2 * n + if topBit then 1 else 0) + rem := by
      have hdivmod : 2 ^ a * (offset / 2 ^ a) + rem = offset := Nat.div_add_mod offset (2 ^ a)
      rw [htop_val] at hdivmod
      have hpow : 2 ^ (a + 1) = 2 ^ a * 2 := Nat.pow_succ 2 a
      rw [hpow, Nat.mul_assoc, Nat.mul_add, ← hdivmod]
      omega
    rw [hsplit, ih rem (2 * n + if topBit then 1 else 0) hrem, runState_bitStep c h0 n topBit]
    rfl

/-! ### Three Reusable Infinite Theorem Compilers -/

/-- **Compiler 1 (Forbidden Residue):** Finite check on `q < S` lifts to `∀ n, B_D(n) % M ≠ r`. -/
theorem cert_forbids_residue (c : WindowAutomatonCert) (hD : ValidDigitSet c.D c.L)
    (hv : c.isValid = true) (res : Nat)
    (hcheck : allLt c.depthS c.S (fun q => c.embed q 0 != res) = true) :
    ∀ n : Nat, binPart c.D n % c.M ≠ res := by
  intro n
  rw [eval_mod_eq c hD hv n]
  have hqs := (soundness c hD hv n).1
  have hne := allLt_sound hcheck (c.runState n) hqs
  simpa [bne_iff_ne] using hne

/-- **Compiler 2 (Affine Self-Congruence):** Finite check on `q < S` lifts to
    `∀ n, B_D(2^a * n + offset) % M = (α * B_D(n)) % M`. -/
theorem cert_affine_self (c : WindowAutomatonCert) (hD : ValidDigitSet c.D c.L)
    (hv : c.isValid = true) (h0 : c.trans false c.q0 = c.q0)
    (a offset alpha : Nat) (hoff : offset < 2 ^ a)
    (hcheck : allLt c.depthS c.S (fun q => c.embed (c.runBits q a offset) 0 == (alpha * c.embed q 0) % c.M) = true) :
    ∀ n : Nat, binPart c.D (2 ^ a * n + offset) % c.M = (alpha * binPart c.D n) % c.M := by
  intro n
  rw [eval_mod_eq c hD hv (2 ^ a * n + offset), runState_affine c h0 a offset n hoff]
  have hqs := (soundness c hD hv n).1
  have heq := allLt_sound hcheck (c.runState n) hqs
  simp only [beq_iff_eq] at heq
  rw [heq, ← eval_mod_eq c hD hv n]
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

/-- **Compiler 3 (Coupled Offset Congruence):** Finite check on `q < S` lifts to
    `∀ n, B_D(2^a * n + c1) % M = (α * B_D(2^a * n + c2)) % M`. -/
theorem cert_coupled_affine (c : WindowAutomatonCert) (hD : ValidDigitSet c.D c.L)
    (hv : c.isValid = true) (h0 : c.trans false c.q0 = c.q0)
    (a c1 c2 alpha : Nat) (hc1 : c1 < 2 ^ a) (hc2 : c2 < 2 ^ a)
    (hcheck : allLt c.depthS c.S (fun q =>
      c.embed (c.runBits q a c1) 0 == (alpha * c.embed (c.runBits q a c2) 0) % c.M) = true) :
    ∀ n : Nat, binPart c.D (2 ^ a * n + c1) % c.M = (alpha * binPart c.D (2 ^ a * n + c2)) % c.M := by
  intro n
  rw [eval_mod_eq c hD hv (2 ^ a * n + c1), runState_affine c h0 a c1 n hc1]
  have hqs := (soundness c hD hv n).1
  have heq := allLt_sound hcheck (c.runState n) hqs
  simp only [beq_iff_eq] at heq
  rw [heq, ← runState_affine c h0 a c2 n hc2, ← eval_mod_eq c hD hv (2 ^ a * n + c2)]
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

end WindowAutomatonCert
theorem cert_b5_valid : cert_b5.isValid = true := by decide

theorem b5_forbids_three_mod4_via_dfa : ∀ n : Nat, br 5 n % 4 ≠ 3 :=
  WindowAutomatonCert.cert_forbids_residue cert_b5 (validDigitSetBool_sound (by decide)) cert_b5_valid 3 (by decide)

theorem cert_b4_valid : cert_b4.isValid = true := by decide

theorem b4_16n_mod4 : ∀ n : Nat, br 4 (16 * n) % 4 = br 4 n % 4 := by
  have h := WindowAutomatonCert.cert_affine_self cert_b4 (validDigitSetBool_sound (by decide))
    cert_b4_valid (by decide) 4 0 1 (by decide) (by decide)
  intro n
  have hr : List.range 5 = [0, 1, 2, 3, 4] := rfl
  simpa [br, hr, cert_b4] using h n

theorem b4_16n_plus_5_mod4 : ∀ n : Nat, br 4 (16 * n + 5) % 4 = (3 * br 4 n) % 4 :=
  WindowAutomatonCert.cert_affine_self cert_b4 (validDigitSetBool_sound (by decide))
    cert_b4_valid (by decide) 4 5 3 (by decide) (by decide)

theorem b4_16n_plus_15_mod4 : ∀ n : Nat, br 4 (16 * n + 15) % 4 = br 4 n % 4 := by
  have h := WindowAutomatonCert.cert_affine_self cert_b4 (validDigitSetBool_sound (by decide))
    cert_b4_valid (by decide) 4 15 1 (by decide) (by decide)
  intro n
  have hr : List.range 5 = [0, 1, 2, 3, 4] := rfl
  simpa [br, hr, cert_b4] using h n

theorem b4_coupled_8n_5_mod4 : ∀ n : Nat, br 4 (8 * n + 5) % 4 = (3 * br 4 (8 * n)) % 4 := by
  have h := WindowAutomatonCert.cert_coupled_affine cert_b4 (validDigitSetBool_sound (by decide))
    cert_b4_valid (by decide) 3 5 0 3 (by decide) (by decide) (by decide)
  intro n
  have hr : List.range 5 = [0, 1, 2, 3, 4] := rfl
  simpa [br, hr, cert_b4] using h n

theorem cert_gap023_valid : cert_gap023.isValid = true := by decide

theorem gap023_32n_plus_16_mod4 :
    ∀ n : Nat, binPart [0, 2, 3] (32 * n + 16) % 4 = (3 * binPart [0, 2, 3] n) % 4 :=
  WindowAutomatonCert.cert_affine_self cert_gap023 (validDigitSetBool_sound (by decide))
    cert_gap023_valid (by decide) 5 16 3 (by decide) (by decide)

theorem gap023_32n_plus_30_mod4 :
    ∀ n : Nat, binPart [0, 2, 3] (32 * n + 30) % 4 = binPart [0, 2, 3] n % 4 := by
  have h := WindowAutomatonCert.cert_affine_self cert_gap023 (validDigitSetBool_sound (by decide))
    cert_gap023_valid (by decide) 5 30 1 (by decide) (by decide)
  intro n; simpa [cert_gap023] using h n

theorem gap023_64n_plus_35_mod4 :
    ∀ n : Nat, binPart [0, 2, 3] (64 * n + 35) % 4 = (3 * binPart [0, 2, 3] n) % 4 :=
  WindowAutomatonCert.cert_affine_self cert_gap023 (validDigitSetBool_sound (by decide))
    cert_gap023_valid (by decide) 6 35 3 (by decide) (by decide)

/-- Hostile mutation tests: corrupting `q0`, `d1`, or `D` makes `isValid = false` (non-vacuous checker). -/
theorem mutation_rejects_bad_q0 : ({ cert_b5 with q0 := 1 }).isValid = false := by decide
theorem mutation_rejects_bad_d1 : ({ cert_b4 with d1 := cert_b4.d0 }).isValid = false := by decide
theorem mutation_rejects_bad_D : ({ cert_gap023 with D := [0, 1, 3] }).isValid = false := by decide

/-! ## Section 4: Parametric Symbolic 2-Adic Lifting (`∀ r ≥ 1, ∀ n : Nat`) -/

theorem sumShift_congr {f g : Nat → Nat} {q start cnt : Nat}
    (h : ∀ x, f x = g x) : sumShift f q start cnt = sumShift g q start cnt := by
  induction cnt with
  | zero => rfl
  | succ c ih =>
    simp only [sumShift, ih]
    split <;> simp [h]

theorem sumShift_mod (f : Nat → Nat) (q start cnt M : Nat) :
    sumShift f q start cnt % M = sumShift (fun x => f x % M) q start cnt % M := by
  induction cnt with
  | zero => rfl
  | succ c ih =>
    simp only [sumShift]
    split
    · rw [Nat.add_mod, ih]
      conv => rhs; rw [Nat.add_mod, Nat.mod_mod]
    · rw [Nat.add_mod, ih, ← Nat.add_mod]

theorem two_mul_sumShift_mod4 (f : Nat → Nat) (q start cnt : Nat) :
    (2 * sumShift f q start cnt) % 4 = (2 * sumShift (fun x => f x % 2) q start cnt) % 4 := by
  have h := sumShift_mod f q start cnt 2
  omega

theorem sumShift_zero_of_all (f : Nat → Nat) (q start cnt : Nat)
    (h : ∀ i < cnt, start + i ≤ q → f (q - (start + i)) = 0) :
    sumShift f q start cnt = 0 := by
  induction cnt with
  | zero => rfl
  | succ c ih =>
    simp only [sumShift]
    have hlast : (if start + c ≤ q then f (q - (start + c)) else 0) = 0 := by
      split
      · next hle => exact h c (by omega) hle
      · rfl
    rw [hlast, ih (fun i hi => h i (by omega))]

theorem sumShift_eq_single (f : Nat → Nat) (q start cnt i0 : Nat)
    (hi0 : i0 < cnt) (hle0 : start + i0 ≤ q)
    (hother : ∀ i < cnt, i ≠ i0 → start + i ≤ q → f (q - (start + i)) = 0) :
    sumShift f q start cnt = f (q - (start + i0)) := by
  induction cnt with
  | zero => omega
  | succ c ih =>
    simp only [sumShift]
    by_cases hci : c = i0
    · subst hci
      have hrest : sumShift f q start c = 0 :=
        sumShift_zero_of_all f q start c (fun i hi => hother i (by omega) (by omega))
      simp [hle0, hrest]
    · have hlast : (if start + c ≤ q then f (q - (start + c)) else 0) = 0 := by
        split
        · next hle => exact hother c (by omega) hci hle
        · rfl
      rw [hlast, Nat.zero_add]
      exact ih (by omega) (fun i hi hne => hother i (by omega) hne)

theorem sumShift_split (f : Nat → Nat) (q start a b : Nat) :
    sumShift f q start (a + b) = sumShift f q (start + a) b + sumShift f q start a := by
  induction b with
  | zero =>
    rw [Nat.add_zero, sumShift, Nat.zero_add]
  | succ b ih =>
    rw [show a + (b + 1) = (a + b) + 1 by omega]
    rw [sumShift, sumShift, ih, show start + (a + b) = start + a + b by omega]
    omega

/-! ### Exact Bit-Shift Unfolding of `br r n` in Terms of `sumShift` -/

theorem digitSum_range_even (f : Nat → Nat) (q : Nat) :
    ∀ k : Nat, digitSum f (2 * q) (List.range (k + 1)) = sumShift f q 0 (k / 2 + 1) := by
  intro k
  induction k with
  | zero =>
    simp [List.range_succ, digitSum, sumShift]
  | succ k ih =>
    rw [List.range_succ, digitSum_append, ih]
    simp only [digitSum, Nat.add_zero]
    by_cases hpar : (k + 1) % 2 = 0
    · have hdiv : (k + 1) / 2 = k / 2 + 1 := by omega
      rw [hdiv]
      simp only [sumShift, Nat.zero_add]
      have hterm :
          (if k + 1 ≤ 2 * q ∧ (2 * q - (k + 1)) % 2 = 0 then f ((2 * q - (k + 1)) / 2) else 0) =
          (if k / 2 + 1 ≤ q then f (q - (k / 2 + 1)) else 0) := by
        by_cases hle : k / 2 + 1 ≤ q
        · have h1 : k + 1 ≤ 2 * q := by omega
          have h2 : (2 * q - (k + 1)) % 2 = 0 := by omega
          have h3 : (2 * q - (k + 1)) / 2 = q - (k / 2 + 1) := by omega
          simp [hle, h1, h2, h3]
        · have h1 : ¬ (k + 1 ≤ 2 * q) := by omega
          simp [hle, h1]
      rw [hterm, Nat.add_comm]
    · have hdiv : (k + 1) / 2 = k / 2 := by omega
      have hnot : ¬ (k + 1 ≤ 2 * q ∧ (2 * q - (k + 1)) % 2 = 0) := by omega
      rw [hdiv]; simp [hnot]

theorem digitSum_range_odd (f : Nat → Nat) (q : Nat) :
    ∀ k : Nat, digitSum f (2 * q + 1) (List.range (k + 1)) = sumShift f q 0 ((k + 1) / 2) := by
  intro k
  induction k with
  | zero =>
    simp [List.range_succ, digitSum, sumShift]
  | succ k ih =>
    rw [List.range_succ, digitSum_append, ih]
    simp only [digitSum, Nat.add_zero]
    by_cases hpar : (k + 1) % 2 = 1
    · have hdiv : (k + 1 + 1) / 2 = (k + 1) / 2 + 1 := by omega
      rw [hdiv]
      simp only [sumShift, Nat.zero_add]
      have hterm :
          (if k + 1 ≤ 2 * q + 1 ∧ (2 * q + 1 - (k + 1)) % 2 = 0 then f ((2 * q + 1 - (k + 1)) / 2) else 0) =
          (if (k + 1) / 2 ≤ q then f (q - (k + 1) / 2) else 0) := by
        have hsub : 2 * q + 1 - (k + 1) = 2 * q - k := by omega
        rw [hsub]
        by_cases hle : (k + 1) / 2 ≤ q
        · have h1 : k + 1 ≤ 2 * q + 1 := by omega
          have h2 : (2 * q - k) % 2 = 0 := by omega
          have h3 : (2 * q - k) / 2 = q - (k + 1) / 2 := by omega
          simp [hle, h1, h2, h3]
        · have h1 : ¬ (k + 1 ≤ 2 * q + 1) := by omega
          simp [hle, h1]
      rw [hterm, Nat.add_comm]
    · have hdiv : (k + 1 + 1) / 2 = (k + 1) / 2 := by omega
      have hsub : 2 * q + 1 - (k + 1) = 2 * q - k := by omega
      rw [hdiv, hsub]
      have hnot : ¬ (k + 1 ≤ 2 * q + 1 ∧ (2 * q - k) % 2 = 0) := by omega
      simp only [hnot, ↓reduceIte, Nat.add_zero]

theorem range_succ_count_zero (r : Nat) : (List.range (r + 1)).count 0 = 1 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [List.range_succ, List.count_append, ih]
    simp

theorem br_even (r q : Nat) : br r (2 * q) = sumShift (br r) q 0 (r / 2 + 1) := by
  unfold br
  rw [binPart_eq_digitSum (List.range (r + 1)) (range_succ_count_zero r) (2 * q)]
  exact digitSum_range_even (binPart (List.range (r + 1))) q r

theorem br_odd (r q : Nat) : br r (2 * q + 1) = sumShift (br r) q 0 ((r + 1) / 2) := by
  unfold br
  rw [binPart_eq_digitSum (List.range (r + 1)) (range_succ_count_zero r) (2 * q + 1)]
  exact digitSum_range_odd (binPart (List.range (r + 1))) q r

/-! ### Helper Modular Lemmas for Theorem A -/

theorem add_one_mod_eq_one_iff (x m : Nat) (hm : m ≥ 2) :
    (x + 1) % m = 1 ↔ x % m = 0 := by
  have hlt := Nat.mod_lt x (by omega : m > 0)
  have h1m : 1 % m = 1 := Nat.mod_eq_of_lt (by omega)
  constructor
  · intro h
    rw [Nat.add_mod, h1m] at h
    by_cases he : x % m + 1 = m
    · rw [he, Nat.mod_self] at h; omega
    · rw [Nat.mod_eq_of_lt (by omega)] at h; omega
  · intro h
    rw [Nat.add_mod, h, h1m, Nat.zero_add, h1m]

theorem mod_mul_two (q m : Nat) (hm : m > 0) :
    (2 * q) % m = if 2 * (q % m) < m then 2 * (q % m) else 2 * (q % m) - m := by
  have hlt := Nat.mod_lt q hm
  have h1 : (2 * q) % m = (2 * (q % m)) % m := by
    calc (2 * q) % m = (2 % m * (q % m)) % m := Nat.mul_mod 2 q m
         _ = (2 % m * ((q % m) % m)) % m := by rw [Nat.mod_mod]
         _ = (2 * (q % m)) % m := (Nat.mul_mod 2 (q % m) m).symm
  rw [h1]
  split
  · next hlt2 => exact Nat.mod_eq_of_lt hlt2
  · next hge =>
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem mod_mul_two_add_one (q m : Nat) (hm : m ≥ 2) :
    (2 * q + 1) % m = if 2 * (q % m) + 1 < m then 2 * (q % m) + 1 else 2 * (q % m) + 1 - m := by
  have hlt := Nat.mod_lt q (by omega : m > 0)
  have h1 : (2 * q + 1) % m = (2 * (q % m) + 1) % m := by
    have h2 : (2 * q) % m = (2 * (q % m)) % m := by
      calc (2 * q) % m = (2 % m * (q % m)) % m := Nat.mul_mod 2 q m
           _ = (2 % m * ((q % m) % m)) % m := by rw [Nat.mod_mod]
           _ = (2 * (q % m)) % m := (Nat.mul_mod 2 (q % m) m).symm
    rw [Nat.add_mod, h2, ← Nat.add_mod]
  rw [h1]
  split
  · next hlt2 => exact Nat.mod_eq_of_lt hlt2
  · next hge =>
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem sub_mod_eq_one_iff (q d m : Nat) (hd : d + 1 < m) :
    (q + 1 - (d + 1)) % m = 1 ↔ q % m = d + 1 := by
  have hm : m > 0 := by omega
  have hqlt := Nat.mod_lt q hm
  by_cases hle : d + 1 ≤ q
  · have hsub : q + 1 - (d + 1) = q - d := by omega
    rw [hsub]
    have hd_add : q = (q - d) + d := by omega
    have hdm : d % m = d := Nat.mod_eq_of_lt (by omega)
    constructor
    · intro h
      have hq : q % m = ((q - d) % m + d % m) % m := by
        conv => lhs; rw [hd_add]; rw [Nat.add_mod]
      rw [h, hdm] at hq
      have hlt1 : 1 + d < m := by omega
      rw [Nat.mod_eq_of_lt hlt1] at hq
      omega
    · intro h
      have hlt2 := Nat.mod_lt (q - d) hm
      have hadd : ((q - d) % m + d) % m = d + 1 := by
        have hq : ((q - d) + d) % m = d + 1 := by rw [← hd_add]; exact h
        rw [Nat.add_mod, hdm] at hq; exact hq
      by_cases hsum : (q - d) % m + d < m
      · rw [Nat.mod_eq_of_lt hsum] at hadd; omega
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hadd; omega
  · have hz : q + 1 - (d + 1) = 0 := by omega
    have hqeq : q % m = q := Nat.mod_eq_of_lt (by omega)
    rw [hz, hqeq]; simp; omega

/-! ### Theorem A: Universal Mod-2 Periodicity (`∀ r ≥ 1, ∀ n : Nat`) -/

/-- Telescoping indicator lemma: `∑_{j=0}^{c-1} [j ≤ q] · [(q - j) % m ≤ 1] ≡ [q+1 ≡ 1] + [q+1-c ≡ 1] (mod 2)`. -/
theorem sumShift_mod2_telescope (m : Nat) (hm : m ≥ 2) (q c : Nat) :
    sumShift (fun t => if t % m ≤ 1 then 1 else 0) q 0 c % 2 =
      ((if (q + 1) % m = 1 then 1 else 0) + (if (q + 1 - c) % m = 1 then 1 else 0)) % 2 := by
  induction c with
  | zero =>
    simp only [sumShift, Nat.sub_zero]
    split <;> simp
  | succ c ih =>
    simp only [sumShift, Nat.zero_add]
    rw [Nat.add_mod, ih]
    by_cases hle : c ≤ q
    · simp only [hle, ↓reduceIte]
      have hstep :
          (if (q - c) % m ≤ 1 then 1 else 0) =
          (if (q - c) % m = 1 then 1 else 0) + (if (q - c + 1) % m = 1 then 1 else 0) := by
        have hiff := add_one_mod_eq_one_iff (q - c) m hm
        by_cases h0 : (q - c) % m = 0
        · simp [h0, hiff.mpr h0]
        · have hnot1 : (q - c + 1) % m ≠ 1 := fun hc => h0 (hiff.mp hc)
          by_cases h1 : (q - c) % m = 1
          · simp [h1, hnot1]
          · have hnotle : ¬ ((q - c) % m ≤ 1) := by omega
            simp [hnotle, h1, hnot1]
      have heq1 : q + 1 - c = q - c + 1 := by omega
      have heq2 : q + 1 - (c + 1) = q - c := by omega
      rw [hstep, heq1, heq2]
      omega
    · have hz1 : q + 1 - c = 0 := by omega
      have hz2 : q + 1 - (c + 1) = 0 := by omega
      simp [hle, hz1, hz2]

/-- **Theorem A (Universal Mod-2 Periodicity):** For every `r ≥ 1` and every `n : Nat`,
    `b_r(n)` is odd if and only if `n mod (r + 1) ∈ {0, 1}`. -/
theorem br_mod2_universal (r : Nat) (hr : r ≥ 1) :
    ∀ n : Nat, br r n % 2 = if n % (r + 1) ≤ 1 then 1 else 0 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
      simp [br, binPart_zero]
    | succ k =>
      let m := r + 1
      have hm : m ≥ 2 := by omega
      by_cases hpar : (k + 1) % 2 = 0
      · let q := (k + 1) / 2
        have h2q : k + 1 = 2 * q := by omega
        have hq_pos : q ≥ 1 := by omega
        rw [h2q, br_even, sumShift_mod]
        have hcongr : sumShift (fun x => br r x % 2) q 0 (r / 2 + 1) =
            sumShift (fun t => if t % m ≤ 1 then 1 else 0) q 0 (r / 2 + 1) := by
          suffices ∀ c, sumShift (fun x => br r x % 2) q 0 c =
              sumShift (fun t => if t % m ≤ 1 then 1 else 0) q 0 c from this (r / 2 + 1)
          intro c
          induction c with
          | zero => rfl
          | succ c ihc =>
            simp only [sumShift, Nat.zero_add, ihc]
            congr 1
            split
            · next hle => exact ih (q - c) (by omega)
            · rfl
        rw [hcongr, sumShift_mod2_telescope m hm q (r / 2 + 1), mod_mul_two q m (by omega)]
        have hq1 := add_one_mod_eq_one_iff q m hm
        have hq2 := sub_mod_eq_one_iff q (r / 2) m (by omega)
        have hqlt := Nat.mod_lt q (by omega : m > 0)
        by_cases h1 : (q + 1) % m = 1
        · have hq0 : q % m = 0 := hq1.mp h1
          have hnot2 : ¬ ((q + 1 - (r / 2 + 1)) % m = 1) := by rw [hq2, hq0]; omega
          simp only [h1, hnot2, ↓reduceIte, hq0, Nat.mul_zero, show 0 < m by omega]; rfl
        · have hq0 : q % m ≠ 0 := fun hc => h1 (hq1.mpr hc)
          by_cases h2 : (q + 1 - (r / 2 + 1)) % m = 1
          · have hqr : q % m = r / 2 + 1 := hq2.mp h2
            simp only [h1, h2, ↓reduceIte, hqr]
            have hge : ¬ (2 * (r / 2 + 1) < m) := by omega
            have hle1 : 2 * (r / 2 + 1) - m ≤ 1 := by omega
            simp [hge, hle1]
          · have hqr : q % m ≠ r / 2 + 1 := fun hc => h2 (hq2.mpr hc)
            simp only [h1, h2, ↓reduceIte]
            split
            · next hlt =>
              have : ¬ (2 * (q % m) ≤ 1) := by omega
              simp [this]
            · next hge =>
              have : ¬ (2 * (q % m) - m ≤ 1) := by omega
              simp [this]
      · -- Odd `k + 1 = 2 * q + 1`
        let q := k / 2
        have h2q1 : k + 1 = 2 * q + 1 := by omega
        rw [h2q1, br_odd, sumShift_mod]
        have hcongr : sumShift (fun x => br r x % 2) q 0 ((r + 1) / 2) =
            sumShift (fun t => if t % m ≤ 1 then 1 else 0) q 0 ((r + 1) / 2) := by
          suffices ∀ c, sumShift (fun x => br r x % 2) q 0 c =
              sumShift (fun t => if t % m ≤ 1 then 1 else 0) q 0 c from this ((r + 1) / 2)
          intro c
          induction c with
          | zero => rfl
          | succ c ihc =>
            simp only [sumShift, Nat.zero_add, ihc]
            congr 1
            split
            · next hle => exact ih (q - c) (by omega)
            · rfl
        rw [hcongr, sumShift_mod2_telescope m hm q ((r + 1) / 2), mod_mul_two_add_one q m hm]
        have hq1 := add_one_mod_eq_one_iff q m hm
        have hq2 : (q + 1 - (r + 1) / 2) % m = 1 ↔ q % m = (r + 1) / 2 := by
          have hd : (r + 1) / 2 = ((r + 1) / 2 - 1) + 1 := by omega
          conv => lhs; rw [hd]
          conv => rhs; rw [hd]
          exact sub_mod_eq_one_iff q ((r + 1) / 2 - 1) m (by omega)
        have hqlt := Nat.mod_lt q (by omega : m > 0)
        by_cases h1 : (q + 1) % m = 1
        · have hq0 : q % m = 0 := hq1.mp h1
          have hnot2 : ¬ ((q + 1 - (r + 1) / 2) % m = 1) := by rw [hq2, hq0]; omega
          simp only [h1, hnot2, ↓reduceIte, hq0, Nat.mul_zero, Nat.zero_add, show 1 < m by omega]; rfl
        · have hq0 : q % m ≠ 0 := fun hc => h1 (hq1.mpr hc)
          by_cases h2 : (q + 1 - (r + 1) / 2) % m = 1
          · have hqr : q % m = (r + 1) / 2 := hq2.mp h2
            simp only [h1, h2, ↓reduceIte, hqr]
            have hge : ¬ (2 * ((r + 1) / 2) + 1 < m) := by omega
            have hle1 : 2 * ((r + 1) / 2) + 1 - m ≤ 1 := by omega
            simp [hge, hle1]
          · have hqr : q % m ≠ (r + 1) / 2 := fun hc => h2 (hq2.mpr hc)
            simp only [h1, h2, ↓reduceIte]
            split
            · next hlt =>
              have : ¬ (2 * (q % m) + 1 ≤ 1) := by omega
              simp [this]
            · next hge =>
              have : ¬ (2 * (q % m) + 1 - m ≤ 1) := by omega
              simp [this]

/-! ### Exact Half-Shift Recurrences for Odd `r = 2 * m + 1` -/

theorem br_odd_r_eq_S (m k : Nat) : br (2 * m + 1) k = S m (k / 2) := by
  unfold S
  by_cases hpar : k % 2 = 0
  · conv => lhs; rw [show k = 2 * (k / 2) by omega]
  · conv => lhs; rw [show k = 2 * (k / 2) + 1 by omega]
    rw [br_odd, br_even]
    rw [show (2 * m + 1 + 1) / 2 = (2 * m + 1) / 2 + 1 by omega]

theorem S_zero (m : Nat) : S m 0 = 1 := by
  simp [S, br, binPart_zero]

theorem S_recurrence (m n : Nat) :
    S m n = sumShift (fun k => S m (k / 2)) n 0 (m + 1) := by
  unfold S
  rw [br_even]
  rw [show (2 * m + 1) / 2 + 1 = m + 1 by omega]
  exact sumShift_congr (fun k => br_odd_r_eq_S m k)

theorem S_mod2 (m n : Nat) :
    S m n % 2 = if n % (m + 1) = 0 then 1 else 0 := by
  unfold S
  rw [br_mod2_universal (2 * m + 1) (by omega) (2 * n)]
  have hiff : (2 * n) % (2 * m + 1 + 1) ≤ 1 ↔ n % (m + 1) = 0 := by
    have hmul : (2 * n) % (2 * (m + 1)) = 2 * (n % (m + 1)) := Nat.mul_mod_mul_left 2 n (m + 1)
    rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega, hmul]
    omega
  by_cases h : n % (m + 1) = 0
  · simp [h, hiff.mpr h]
  · have hnot : ¬ ((2 * n) % (2 * m + 1 + 1) ≤ 1) := fun hc => h (hiff.mp hc)
    simp [h, hnot]

/-- Pair-bundling identities for `sumShift (fun k => f (k / 2))` on even and odd inputs. -/
theorem sumShift_half_even_odd_cnt (f : Nat → Nat) (q k : Nat) :
    sumShift (fun x => f (x / 2)) (2 * q) 0 (2 * k + 1) =
      f q + 2 * sumShift f q 1 k := by
  induction k with
  | zero => simp [sumShift]
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega]
    rw [sumShift, sumShift, ih, sumShift]
    simp only [Nat.zero_add]
    have h1 : 2 * k + 2 ≤ 2 * q ↔ 1 + k ≤ q := by omega
    have h2 : 2 * k + 1 ≤ 2 * q ↔ 1 + k ≤ q := by omega
    by_cases hle : 1 + k ≤ q
    · have ha : (2 * q - (2 * k + 2)) / 2 = q - (1 + k) := by omega
      have hb : (2 * q - (2 * k + 1)) / 2 = q - (1 + k) := by omega
      simp only [h1.mpr hle, h2.mpr hle, hle, ↓reduceIte, ha, hb]
      omega
    · have ha : ¬ (2 * k + 2 ≤ 2 * q) := fun hc => hle (h1.mp hc)
      have hb : ¬ (2 * k + 1 ≤ 2 * q) := fun hc => hle (h2.mp hc)
      simp [hle, ha, hb]

theorem sumShift_half_odd_odd_cnt (f : Nat → Nat) (q k : Nat) :
    sumShift (fun x => f (x / 2)) (2 * q + 1) 0 (2 * k + 1) =
      (if k ≤ q then f (q - k) else 0) + 2 * sumShift f q 0 k := by
  induction k with
  | zero =>
    simp [sumShift, show (2 * q + 1) / 2 = q by omega]
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega]
    rw [sumShift, sumShift, ih, sumShift]
    simp only [Nat.zero_add]
    have h1 : 2 * k + 2 ≤ 2 * q + 1 ↔ k + 1 ≤ q := by omega
    have h2 : 2 * k + 1 ≤ 2 * q + 1 ↔ k ≤ q := by omega
    by_cases hle1 : k + 1 ≤ q
    · have hle0 : k ≤ q := by omega
      have ha : (2 * q + 1 - (2 * k + 2)) / 2 = q - (k + 1) := by omega
      have hb : (2 * q + 1 - (2 * k + 1)) / 2 = q - k := by omega
      simp only [h1.mpr hle1, h2.mpr hle0, hle1, hle0, ↓reduceIte, ha, hb]
      omega
    · have ha : ¬ (2 * k + 2 ≤ 2 * q + 1) := fun hc => hle1 (h1.mp hc)
      by_cases hle0 : k ≤ q
      · have hb : (2 * q + 1 - (2 * k + 1)) / 2 = q - k := by omega
        simp only [ha, h2.mpr hle0, hle1, hle0, ↓reduceIte, hb]
        omega
      · have hb : ¬ (2 * k + 1 ≤ 2 * q + 1) := fun hc => hle0 (h2.mp hc)
        simp [ha, hb, hle1, hle0]

theorem sumShift_half_even_even_cnt (f : Nat → Nat) (q h : Nat) (hh : h ≥ 1) :
    sumShift (fun x => f (x / 2)) (2 * q) 0 (2 * h) =
      f q + (if h ≤ q then f (q - h) else 0) + 2 * sumShift f q 1 (h - 1) := by
  cases h with
  | zero => omega
  | succ k =>
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, show k + 1 - 1 = k by omega]
    rw [sumShift, sumShift_half_even_odd_cnt f q k]
    simp only [Nat.zero_add]
    have hcond : 2 * k + 1 ≤ 2 * q ↔ k + 1 ≤ q := by omega
    by_cases hle : k + 1 ≤ q
    · have hd : (2 * q - (2 * k + 1)) / 2 = q - (k + 1) := by omega
      simp only [hcond.mpr hle, hle, ↓reduceIte, hd]
      omega
    · have hnot : ¬ (2 * k + 1 ≤ 2 * q) := fun hc => hle (hcond.mp hc)
      simp only [hnot, hle, ↓reduceIte]
      omega

theorem sumShift_half_odd_even_cnt (f : Nat → Nat) (q h : Nat) :
    sumShift (fun x => f (x / 2)) (2 * q + 1) 0 (2 * h) =
      2 * sumShift f q 0 h := by
  induction h with
  | zero => simp [sumShift]
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by omega]
    rw [sumShift, sumShift, ih, sumShift]
    simp only [Nat.zero_add]
    have h1 : 2 * k + 1 ≤ 2 * q + 1 ↔ k ≤ q := by omega
    have h2 : 2 * k ≤ 2 * q + 1 ↔ k ≤ q := by omega
    by_cases hle : k ≤ q
    · have ha : (2 * q + 1 - (2 * k + 1)) / 2 = q - k := by omega
      have hb : (2 * q + 1 - 2 * k) / 2 = q - k := by omega
      simp only [h1.mpr hle, h2.mpr hle, hle, ↓reduceIte, ha, hb]
      omega
    · have ha : ¬ (2 * k + 1 ≤ 2 * q + 1) := fun hc => hle (h1.mp hc)
      have hb : ¬ (2 * k ≤ 2 * q + 1) := fun hc => hle (h2.mp hc)
      simp [ha, hb, hle]

/-! ### Exact Partial-Sum Bridge `S m n = ∑_{i=0}^n b_m(i)` -/

theorem S_step_diff (m n : Nat) :
    S m (n + 1) + (if m + 1 ≤ n + 1 then S m ((n + 1 - (m + 1)) / 2) else 0) =
      S m n + S m ((n + 1) / 2) := by
  rw [S_recurrence m (n + 1), S_recurrence m n]
  suffices ∀ c,
      sumShift (fun k => S m (k / 2)) (n + 1) 0 c + (if c ≤ n + 1 then S m ((n + 1 - c) / 2) else 0) =
      sumShift (fun k => S m (k / 2)) n 0 c + S m ((n + 1) / 2) by
    exact this (m + 1)
  intro c
  induction c with
  | zero => simp [sumShift]
  | succ c ih =>
    simp only [sumShift, Nat.zero_add]
    by_cases hle : c + 1 ≤ n + 1
    · have hle1 : c ≤ n + 1 := by omega
      have hle2 : c ≤ n := by omega
      have hsub1 : n + 1 - (c + 1) = n - c := by omega
      simp only [hle, hle1, hle2, ↓reduceIte, hsub1] at ih ⊢
      omega
    · have hnot2 : ¬ (c ≤ n) := by omega
      by_cases hle1 : c ≤ n + 1
      · have hzero : n + 1 - c = 0 := by omega
        simp only [hle, hle1, hnot2, ↓reduceIte, hzero] at ih ⊢
        omega
      · simp only [hle, hle1, hnot2, ↓reduceIte] at ih ⊢
        omega

theorem sumShift_rebase (f : Nat → Nat) (q d c : Nat) (hd : d ≤ q) :
    sumShift f q d c = sumShift f (q - d) 0 c := by
  induction c with
  | zero => rfl
  | succ c ih =>
    simp only [sumShift, Nat.zero_add, ih]
    have h1 : d + c ≤ q ↔ c ≤ q - d := by omega
    by_cases hc : c ≤ q - d
    · simp [h1.mpr hc, hc, show q - (d + c) = q - d - c by omega]
    · simp [hc, show ¬ (d + c ≤ q) by omega]

/-- Exact identity: `b_{2m+1}(2n) = ∑_{i=0}^n b_m(i)` for all `m, n : Nat`. -/
theorem S_eq_partial_sum (m : Nat) : ∀ n : Nat, S m n = sumShift (br m) n 0 (n + 1) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp [S_zero, sumShift, br, binPart_zero]
    | succ k =>
      have hdiff := S_step_diff m k
      have hsum_step : sumShift (br m) (k + 1) 0 (k + 2) = br m (k + 1) + sumShift (br m) k 0 (k + 1) := by
        have hsplit := sumShift_split (br m) (k + 1) 0 1 (k + 1)
        rw [show 1 + (k + 1) = k + 2 by omega, Nat.zero_add] at hsplit
        rw [hsplit, sumShift_rebase (br m) (k + 1) 1 (k + 1) (by omega), show k + 1 - 1 = k by omega]
        simp only [sumShift, Nat.zero_add, Nat.add_zero, Nat.sub_zero, Nat.zero_le, ↓reduceIte]
        omega
      rw [hsum_step, ← ih k (by omega)]
      have hkey : br m (k + 1) + (if m + 1 ≤ k + 1 then S m ((k + 1 - (m + 1)) / 2) else 0) =
          S m ((k + 1) / 2) := by
        have hlt_half : (k + 1) / 2 < k + 1 := by omega
        rw [ih ((k + 1) / 2) hlt_half]
        by_cases hpar : (k + 1) % 2 = 0
        · let q := (k + 1) / 2
          have h2q : k + 1 = 2 * q := by omega
          rw [h2q, br_even]
          have hqeq : (2 * q) / 2 = q := by omega
          rw [hqeq]
          by_cases hle : m + 1 ≤ 2 * q
          · simp only [hle, ↓reduceIte]
            have hlt2 : (2 * q - (m + 1)) / 2 < k + 1 := by omega
            rw [ih ((2 * q - (m + 1)) / 2) hlt2]
            have hlen : (m / 2 + 1) + ((2 * q - (m + 1)) / 2 + 1) = q + 1 := by omega
            rw [← hlen, sumShift_split (br m) q 0 (m / 2 + 1) ((2 * q - (m + 1)) / 2 + 1), Nat.zero_add]
            rw [sumShift_rebase (br m) q (m / 2 + 1) _ (by omega)]
            rw [show q - (m / 2 + 1) = (2 * q - (m + 1)) / 2 by omega]
            omega
          · simp only [hle, ↓reduceIte, Nat.add_zero]
            have hsplit := sumShift_split (br m) q 0 (q + 1) (m / 2 + 1 - (q + 1))
            rw [show (q + 1) + (m / 2 + 1 - (q + 1)) = m / 2 + 1 by omega, Nat.zero_add] at hsplit
            rw [hsplit]
            have hz : sumShift (br m) q (q + 1) (m / 2 + 1 - (q + 1)) = 0 :=
              sumShift_zero_of_all (br m) q (q + 1) _ (fun i _ hle' => by omega)
            rw [hz, Nat.zero_add]
        · let q := k / 2
          have h2q1 : k + 1 = 2 * q + 1 := by omega
          rw [h2q1, br_odd]
          have hqeq : (2 * q + 1) / 2 = q := by omega
          rw [hqeq]
          by_cases hle : m + 1 ≤ 2 * q + 1
          · simp only [hle, ↓reduceIte]
            have hlt2 : (2 * q + 1 - (m + 1)) / 2 < k + 1 := by omega
            rw [ih ((2 * q + 1 - (m + 1)) / 2) hlt2]
            have hlen : ((m + 1) / 2) + ((2 * q + 1 - (m + 1)) / 2 + 1) = q + 1 := by omega
            rw [← hlen, sumShift_split (br m) q 0 ((m + 1) / 2) ((2 * q + 1 - (m + 1)) / 2 + 1), Nat.zero_add]
            rw [sumShift_rebase (br m) q ((m + 1) / 2) _ (by omega)]
            rw [show q - (m + 1) / 2 = (2 * q + 1 - (m + 1)) / 2 by omega]
            omega
          · simp only [hle, ↓reduceIte, Nat.add_zero]
            have hsplit := sumShift_split (br m) q 0 (q + 1) ((m + 1) / 2 - (q + 1))
            rw [show (q + 1) + ((m + 1) / 2 - (q + 1)) = (m + 1) / 2 by omega, Nat.zero_add] at hsplit
            rw [hsplit]
            have hz : sumShift (br m) q (q + 1) ((m + 1) / 2 - (q + 1)) = 0 :=
              sumShift_zero_of_all (br m) q (q + 1) _ (fun i _ hle' => by omega)
            rw [hz, Nat.zero_add]
      omega

/-! ### Theorem B: Universal Mod-4 Carry-Valuation Law (`∀ t ≥ 1, ∀ odd u, ∀ j`) -/

/-- Case `t = 1` (`r = 4k + 1`, `u = 2k + 1` odd): `S(2k, (2k+1) * j) ≡ 1 (mod 4)` for all `j`. -/
theorem S_t1_mod4 (k : Nat) : ∀ j : Nat, S (2 * k) ((2 * k + 1) * j) % 4 = 1 := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    cases j with
    | zero => simp [S_zero]
    | succ j' =>
      let u := 2 * k + 1
      by_cases hpar : (j' + 1) % 2 = 0
      · let a := (j' + 1) / 2
        have hj : (2 * k + 1) * (j' + 1) = 2 * (u * a) := by
          have ha : j' + 1 = 2 * a := by omega
          rw [ha]; dsimp [u]; rw [Nat.mul_comm (2 * k + 1) (2 * a), Nat.mul_assoc, Nat.mul_comm a]
        rw [hj, S_recurrence (2 * k) (2 * (u * a)), sumShift_half_even_odd_cnt (S (2 * k)) (u * a) k]
        rw [Nat.add_mod, two_mul_sumShift_mod4]
        have hz : sumShift (fun x => S (2 * k) x % 2) (u * a) 1 k = 0 := by
          apply sumShift_zero_of_all
          intro i hi hle
          rw [S_mod2]
          have hndiv : (u * a - (1 + i)) % u ≠ 0 := by
            have h1 : 1 + i < u := by omega
            intro hd
            have hadd : (u * a - (1 + i)) + (1 + i) = u * a := by omega
            have : (1 + i) % u = 0 := by
              have hmod := congrArg (· % u) hadd
              rw [Nat.add_mod, hd, Nat.zero_add, Nat.mod_mod, Nat.mul_mod_right] at hmod
              exact hmod
            rw [Nat.mod_eq_of_lt h1] at this; omega
          simp [u, hndiv]
        rw [hz, Nat.mul_zero, Nat.zero_mod, Nat.add_zero, Nat.mod_mod]
        exact ih a (by omega)
      · let a := j' / 2
        have hj : (2 * k + 1) * (j' + 1) = 2 * (u * a + k) + 1 := by
          have ha : j' + 1 = 2 * a + 1 := by omega
          rw [ha, Nat.mul_add, Nat.mul_one]
          dsimp [u]
          have h1 : (2 * k + 1) * (2 * a) = 2 * ((2 * k + 1) * a) := by
            rw [Nat.mul_comm (2 * k + 1) (2 * a), Nat.mul_assoc, Nat.mul_comm a]
          omega
        rw [hj, S_recurrence (2 * k), sumShift_half_odd_odd_cnt (S (2 * k)) (u * a + k) k]
        rw [Nat.add_mod, two_mul_sumShift_mod4]
        have hle : k ≤ u * a + k := by omega
        have hsub : u * a + k - k = u * a := by omega
        have hz : sumShift (fun x => S (2 * k) x % 2) (u * a + k) 0 k = 0 := by
          apply sumShift_zero_of_all
          intro i hi hle'
          rw [S_mod2]
          have hndiv : (u * a + k - i) % u ≠ 0 := by
            have h1 : u * a + k - i = u * a + (k - i) := by omega
            rw [h1, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
            omega
          simp [u, hndiv]
        rw [hz, Nat.mul_zero, Nat.zero_mod, Nat.add_zero, Nat.mod_mod]
        simp only [hle, ↓reduceIte, hsub]
        exact ih a (by omega)

/-- Case `t ≥ 2`: `S(2^(t-1)*u - 1, u * j) % 4 = phi t (j % 2^t)` for all odd `u` and all `j`. -/
theorem S_ge2_mod4 (t u : Nat) (ht : t ≥ 2) (hu : u % 2 = 1) :
    ∀ j : Nat, S (2 ^ (t - 1) * u - 1) (u * j) % 4 = phi t (j % 2 ^ t) := by
  let h := 2 ^ (t - 2) * u
  let M := 2 ^ (t - 1) * u
  have hpow1 : 2 ^ (t - 1) = 2 * 2 ^ (t - 2) := by
    conv => lhs; rw [show t - 1 = (t - 2) + 1 by omega]
    rw [Nat.pow_succ]; omega
  have hpow2 : 2 ^ t = 2 * 2 ^ (t - 1) := by
    conv => lhs; rw [show t = (t - 1) + 1 by omega]
    rw [Nat.pow_succ]; omega
  have hM : M = 2 * h := by
    dsimp [M, h]; rw [hpow1, Nat.mul_assoc]
  have hh_pos : h ≥ 1 := by
    have : 2 ^ (t - 2) ≥ 1 := Nat.pow_pos (by omega)
    dsimp [h]; exact Nat.mul_pos this (by omega)
  have hM_sub : M - 1 + 1 = M := by omega
  have hM_cnt : M - 1 + 1 = 2 * h := by omega
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    cases j with
    | zero =>
      simp [S_zero, phi]
    | succ j' =>
      by_cases hpar : (j' + 1) % 2 = 1
      · -- Case 1: `j' + 1 = 2 * a + 1` is ODD (direct counting, no IH needed!)
        let a := j' / 2
        let q := u * a + (u - 1) / 2
        have huj : u * (j' + 1) = 2 * q + 1 := by
          have ha : j' + 1 = 2 * a + 1 := by omega
          rw [ha, Nat.mul_add, Nat.mul_one]
          have h1 : u * (2 * a) = 2 * (u * a) := by
            rw [Nat.mul_comm u (2 * a), Nat.mul_assoc, Nat.mul_comm a u]
          dsimp [q]; omega
        rw [huj, S_recurrence (M - 1), hM_cnt, sumShift_half_odd_even_cnt (S (M - 1)) q h]
        rw [two_mul_sumShift_mod4]
        let r' := a % 2 ^ (t - 1)
        let c0 := a / 2 ^ (t - 1)
        have ha_eq : a = 2 ^ (t - 1) * c0 + r' := (Nat.div_add_mod a (2 ^ (t - 1))).symm
        have hr'_lt : r' < 2 ^ (t - 1) := Nat.mod_lt a (Nat.pow_pos (by omega))
        have hqj_eq : (j' + 1) % 2 ^ t = 2 * r' + 1 := by
          have h1 : j' + 1 = 2 ^ t * c0 + (2 * r' + 1) := by
            have h2 : 2 ^ t * c0 = 2 * (2 ^ (t - 1) * c0) := by rw [hpow2, Nat.mul_assoc]
            omega
          rw [h1, Nat.mul_add_mod, Nat.mod_eq_of_lt (by rw [hpow2]; omega)]
        by_cases hsmall : r' < 2 ^ (t - 2)
        · -- Unique multiple `M * c0` lies in `{q - (h - 1), ..., q}` at `i0 = u * r' + (u - 1) / 2`
          let i0 := u * r' + (u - 1) / 2
          have hi0_lt : i0 < h := by
            dsimp [i0, h]
            have : u * r' + u ≤ u * 2 ^ (t - 2) := by
              rw [show u * r' + u = u * (r' + 1) by rw [Nat.mul_add, Nat.mul_one]]
              exact Nat.mul_le_mul_left u (by omega)
            rw [Nat.mul_comm (2 ^ (t - 2)) u]
            omega
          have hi0_le : 0 + i0 ≤ q := by
            dsimp [i0, q]
            have : r' ≤ a := by omega
            have := Nat.mul_le_mul_left u this
            omega
          have hsub0 : q - (0 + i0) = M * c0 := by
            dsimp [q, i0, M]
            have : u * a = u * (2 ^ (t - 1) * c0) + u * r' := by
              rw [← Nat.mul_add, ← ha_eq]
            have hcomm : u * (2 ^ (t - 1) * c0) = 2 ^ (t - 1) * u * c0 := by
              rw [← Nat.mul_assoc, Nat.mul_comm u (2 ^ (t - 1))]
            omega
          have hsum1 : sumShift (fun x => S (M - 1) x % 2) q 0 h = 1 := by
            have heq := sumShift_eq_single (fun x => S (M - 1) x % 2) q 0 h i0 hi0_lt hi0_le (by
              intro i hi hne hle
              rw [S_mod2, hM_sub]
              have hndiv : (q - i) % M ≠ 0 := by
                intro hd
                have hk1 : q - i = M * ((q - i) / M) := by
                  have := (Nat.div_add_mod (q - i) M).symm
                  rw [hd, Nat.add_zero] at this; exact this
                have hlt_a : M * ((q - i) / M) < M * (c0 + 1) := by
                  rw [← hk1, Nat.mul_add, Nat.mul_one]; omega
                have hgt_a : M * c0 < M * ((q - i) / M + 1) := by
                  rw [Nat.mul_add, Nat.mul_one, ← hk1]; omega
                have h1 := Nat.lt_of_mul_lt_mul_left hlt_a
                have h2 := Nat.lt_of_mul_lt_mul_left hgt_a
                have hdiv_eq : (q - i) / M = c0 := by omega
                rw [hdiv_eq] at hk1
                have : q - i = q - i0 := by rw [hk1, ← hsub0]; simp
                omega
              simp [hndiv])
            rw [heq, S_mod2, hM_sub, hsub0, Nat.mul_mod_right]
            simp
          rw [hsum1, hqj_eq]
          unfold phi
          have hlt_half : 2 * r' + 1 < 2 ^ (t - 1) := by rw [hpow1]; omega
          have hv0 : v2 (2 * r' + 1) = 0 := v2_odd (2 * r' + 1) (by omega)
          simp [hlt_half, hv0]
        · -- No multiple of `M` lies in `{q - (h - 1), ..., q}`
          have hsum0 : sumShift (fun x => S (M - 1) x % 2) q 0 h = 0 := by
            apply sumShift_zero_of_all
            intro i hi hle
            rw [S_mod2, hM_sub]
            have hndiv : (q - i) % M ≠ 0 := by
              intro hd
              let x := q - i
              have hx_eq : x = M * (x / M) := by
                have := (Nat.div_add_mod x M).symm
                rw [hd, Nat.add_zero] at this; exact this
              have hlow : M * c0 + h ≤ u * a := by
                have h1 : 2 ^ (t - 1) * c0 + 2 ^ (t - 2) ≤ a := by omega
                have h2 := Nat.mul_le_mul_left u h1
                rw [Nat.mul_add] at h2
                have hc1 : u * (2 ^ (t - 1) * c0) = M * c0 := by
                  dsimp [M]; rw [← Nat.mul_assoc, Nat.mul_comm u (2 ^ (t - 1))]
                have hc2 : u * 2 ^ (t - 2) = h := by dsimp [h]; rw [Nat.mul_comm]
                omega
              have hhigh : q < M * (c0 + 1) := by
                have h1 : a + 1 ≤ 2 ^ (t - 1) * (c0 + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
                have h2 := Nat.mul_le_mul_left u h1
                rw [Nat.mul_add, Nat.mul_one] at h2
                have hc1 : u * (2 ^ (t - 1) * (c0 + 1)) = M * (c0 + 1) := by
                  dsimp [M]; rw [← Nat.mul_assoc, Nat.mul_comm u (2 ^ (t - 1))]
                dsimp [q]; omega
              have hgt : M * c0 < x := by dsimp [x, q]; omega
              have hlt : x < M * (c0 + 1) := by dsimp [x]; omega
              rw [hx_eq] at hgt hlt
              have h1 := Nat.lt_of_mul_lt_mul_left hgt
              have h2 := Nat.lt_of_mul_lt_mul_left hlt
              omega
            simp [hndiv]
          rw [hsum0, hqj_eq]
          unfold phi
          have hge_half : ¬ (2 * r' + 1 < 2 ^ (t - 1)) := by rw [hpow1]; omega
          have hne_half : 2 * r' + 1 ≠ 2 ^ (t - 1) := by rw [hpow1]; omega
          simp [hge_half, hne_half]
      · -- Case 2: `j' + 1 = 2 * a` is EVEN (`a ≥ 1`)
        let a := (j' + 1) / 2
        have ha_pos : a ≥ 1 := by omega
        have hj_eq : j' + 1 = 2 * a := by omega
        have huj : u * (j' + 1) = 2 * (u * a) := by
          rw [hj_eq, Nat.mul_comm u (2 * a), Nat.mul_assoc, Nat.mul_comm a u]
        rw [huj, S_recurrence (M - 1), hM_cnt,
            sumShift_half_even_even_cnt (S (M - 1)) (u * a) h hh_pos]
        rw [Nat.add_mod, two_mul_sumShift_mod4]
        let r' := a % 2 ^ (t - 1)
        let c0 := a / 2 ^ (t - 1)
        have ha_eq : a = 2 ^ (t - 1) * c0 + r' := (Nat.div_add_mod a (2 ^ (t - 1))).symm
        have hr'_lt : r' < 2 ^ (t - 1) := Nat.mod_lt a (Nat.pow_pos (by omega))
        have hmid : sumShift (fun x => S (M - 1) x % 2) (u * a) 1 (h - 1) =
            if 1 ≤ r' ∧ r' < 2 ^ (t - 2) then 1 else 0 := by
          by_cases hcond : 1 ≤ r' ∧ r' < 2 ^ (t - 2)
          · simp only [hcond]
            let i0 := u * r' - 1
            have hu1 : u * r' ≥ 1 := Nat.mul_pos (by omega) (by omega)
            have hi0_lt : i0 < h - 1 := by
              dsimp [i0, h]
              have : u * r' + u ≤ u * 2 ^ (t - 2) := by
                rw [show u * r' + u = u * (r' + 1) by rw [Nat.mul_add, Nat.mul_one]]
                exact Nat.mul_le_mul_left u (by omega)
              rw [Nat.mul_comm (2 ^ (t - 2)) u]
              omega
            have hi0_le : 1 + i0 ≤ u * a := by
              dsimp [i0]
              have h1 : r' ≤ a := by omega
              have h2 := Nat.mul_le_mul_left u h1
              omega
            have hsub0 : u * a - (1 + i0) = M * c0 := by
              have : u * a = M * c0 + u * r' := by
                dsimp [M]
                rw [ha_eq, Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm u (2 ^ (t - 1))]
              dsimp [i0]; omega
            have heq := sumShift_eq_single (fun x => S (M - 1) x % 2) (u * a) 1 (h - 1) i0 hi0_lt hi0_le (by
              intro i hi hne hle
              rw [S_mod2, hM_sub]
              have hndiv : (u * a - (1 + i)) % M ≠ 0 := by
                intro hd
                let x := u * a - (1 + i)
                have hx_eq : x = M * (x / M) := by
                  have := (Nat.div_add_mod x M).symm
                  rw [hd, Nat.add_zero] at this; exact this
                have hlt1 : M * (x / M) < M * (c0 + 1) := by
                  rw [← hx_eq, Nat.mul_add, Nat.mul_one]; dsimp [x]; omega
                have hgt1 : M * c0 < M * (x / M + 1) := by
                  rw [Nat.mul_add, Nat.mul_one, ← hx_eq]; dsimp [x]; omega
                have h1 := Nat.lt_of_mul_lt_mul_left hlt1
                have h2 := Nat.lt_of_mul_lt_mul_left hgt1
                have hdiv_eq : x / M = c0 := by omega
                rw [hdiv_eq] at hx_eq
                have hsame : u * a - (1 + i) = u * a - (1 + i0) := hx_eq.trans hsub0.symm
                omega
              simp [hndiv])
            rw [heq, S_mod2, hM_sub, hsub0, Nat.mul_mod_right]
            simp
          · simp only [hcond]
            apply sumShift_zero_of_all
            intro i hi hle
            rw [S_mod2, hM_sub]
            have hndiv : (u * a - (1 + i)) % M ≠ 0 := by
              intro hd
              let x := u * a - (1 + i)
              have hx_eq : x = M * (x / M) := by
                have := (Nat.div_add_mod x M).symm
                rw [hd, Nat.add_zero] at this; exact this
              by_cases hr0 : r' = 0
              · have hua : u * a = M * c0 := by
                  dsimp [M]; rw [ha_eq, hr0, Nat.add_zero, ← Nat.mul_assoc, Nat.mul_comm u (2 ^ (t - 1))]
                have hc_pos : c0 ≥ 1 := by
                  cases hc0 : c0 with
                  | zero => rw [hc0, hr0] at ha_eq; simp at ha_eq; omega
                  | succ _ => omega
                have hgt : M * (c0 - 1) < x := by
                  have : M * (c0 - 1) + M = M * c0 := by
                    conv => rhs; rw [show c0 = (c0 - 1) + 1 by omega]
                    rw [Nat.mul_add, Nat.mul_one]
                  dsimp [x]; omega
                have hlt : x < M * c0 := by dsimp [x]; omega
                rw [hx_eq] at hgt hlt
                have h1 := Nat.lt_of_mul_lt_mul_left hgt
                have h2 := Nat.lt_of_mul_lt_mul_left hlt
                omega
              · have hge : r' ≥ 2 ^ (t - 2) := by omega
                have hlow : M * c0 + h ≤ u * a := by
                  have h1 : 2 ^ (t - 1) * c0 + 2 ^ (t - 2) ≤ a := by omega
                  have h2 := Nat.mul_le_mul_left u h1
                  rw [Nat.mul_add] at h2
                  have hc1 : u * (2 ^ (t - 1) * c0) = M * c0 := by
                    dsimp [M]; rw [← Nat.mul_assoc, Nat.mul_comm u (2 ^ (t - 1))]
                  have hc2 : u * 2 ^ (t - 2) = h := by dsimp [h]; rw [Nat.mul_comm]
                  omega
                have hhigh : u * a < M * (c0 + 1) := by
                  have h1 : a < 2 ^ (t - 1) * (c0 + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
                  have h2 := Nat.mul_lt_mul_of_pos_left h1 (by omega : u > 0)
                  have hc1 : u * (2 ^ (t - 1) * (c0 + 1)) = M * (c0 + 1) := by
                    dsimp [M]; rw [← Nat.mul_assoc, Nat.mul_comm u (2 ^ (t - 1))]
                  omega
                have hgt : M * c0 < x := by dsimp [x]; omega
                have hlt : x < M * (c0 + 1) := by dsimp [x]; omega
                rw [hx_eq] at hgt hlt
                have h1 := Nat.lt_of_mul_lt_mul_left hgt
                have h2 := Nat.lt_of_mul_lt_mul_left hlt
                omega
            simp [hndiv]
        rw [hmid]
        have ih_a := ih a (by omega)
        have h_term2 :
            (if h ≤ u * a then S (M - 1) (u * a - h) else 0) % 4 =
            phi t ((a + 3 * 2 ^ (t - 2)) % 2 ^ t) := by
          by_cases hle : h ≤ u * a
          · simp only [hle, ↓reduceIte]
            have ha_ge : 2 ^ (t - 2) ≤ a := by
              have : u * 2 ^ (t - 2) ≤ u * a := by
                dsimp [h] at hle; rw [Nat.mul_comm] at hle; exact hle
              exact Nat.le_of_mul_le_mul_left this (by omega)
            have hsub_eq : u * a - h = u * (a - 2 ^ (t - 2)) := by
              dsimp [h]; rw [Nat.mul_sub_left_distrib, Nat.mul_comm (2 ^ (t - 2)) u]
            rw [hsub_eq, ih (a - 2 ^ (t - 2)) (by omega)]
            congr 1
            have hpow4 : 2 ^ t = 4 * 2 ^ (t - 2) := by rw [hpow2, hpow1]; omega
            have hadd_eq : a + 3 * 2 ^ (t - 2) = (a - 2 ^ (t - 2)) + 2 ^ t := by omega
            rw [hadd_eq, Nat.add_mod_right]
          · simp only [hle, ↓reduceIte, Nat.zero_mod]
            have ha_lt : a < 2 ^ (t - 2) := by
              cases Nat.lt_or_ge a (2 ^ (t - 2)) with
              | inl hlt => exact hlt
              | inr hge =>
                have : u * 2 ^ (t - 2) ≤ u * a := Nat.mul_le_mul_left u hge
                dsimp [h] at hle; rw [Nat.mul_comm] at this; omega
            have hpow4 : 2 ^ t = 4 * 2 ^ (t - 2) := by rw [hpow2, hpow1]; omega
            have hmod : (a + 3 * 2 ^ (t - 2)) % 2 ^ t = a + 3 * 2 ^ (t - 2) :=
              Nat.mod_eq_of_lt (by omega)
            rw [hmod]
            unfold phi
            have hp2 : 2 ^ (t - 2) ≥ 1 := Nat.pow_pos (by omega)
            have hne0 : a + 3 * 2 ^ (t - 2) ≠ 0 := by omega
            have hge1 : ¬ (a + 3 * 2 ^ (t - 2) < 2 ^ (t - 1)) := by rw [hpow1]; omega
            have hne1 : a + 3 * 2 ^ (t - 2) ≠ 2 ^ (t - 1) := by rw [hpow1]; omega
            simp only [hne0, hge1, hne1, ↓reduceIte]
        rw [Nat.add_mod (S (M - 1) (u * a)) _ 4, ih_a, h_term2]
        let qa := a % 2 ^ t
        let q := 2 ^ (t - 2)
        have hq_pos : q ≥ 1 := Nat.pow_pos (by omega)
        have h2q : 2 ^ (t - 1) = 2 * q := hpow1
        have h4q : 2 ^ t = 4 * q := by rw [hpow2, hpow1]; omega
        have hqa_lt : qa < 4 * q := by rw [← h4q]; exact Nat.mod_lt a (by omega)
        have hr'_eq : r' = qa % (2 * q) := by
          dsimp [r', qa]
          rw [h2q, h4q, Nat.mod_mod_of_dvd a ⟨2, by omega⟩]
        have hshift_mod : (a + 3 * q) % (4 * q) = (qa + 3 * q) % (4 * q) := by
          calc (a + 3 * q) % (4 * q) = (a % (4 * q) + 3 * q % (4 * q)) % (4 * q) := Nat.add_mod _ _ _
               _ = (qa % (4 * q) + 3 * q % (4 * q)) % (4 * q) := by dsimp [qa]; rw [h4q, Nat.mod_mod]
               _ = (qa + 3 * q) % (4 * q) := (Nat.add_mod _ _ _).symm
        have hj_mod : (j' + 1) % (4 * q) = (2 * qa) % (4 * q) := by
          rw [hj_eq]; dsimp [qa]
          calc (2 * a) % (4 * q) = (2 % (4 * q) * (a % (4 * q))) % (4 * q) := Nat.mul_mod 2 a (4 * q)
               _ = (2 % (4 * q) * ((a % (4 * q)) % (4 * q))) % (4 * q) := by rw [Nat.mod_mod]
               _ = (2 * (a % (4 * q))) % (4 * q) := (Nat.mul_mod 2 (a % (4 * q)) (4 * q)).symm
               _ = (2 * (a % 2 ^ t)) % (4 * q) := by rw [h4q]
        have harg1 : (a + 3 * 2 ^ (t - 2)) % 2 ^ t = (qa + 3 * q) % (4 * q) := by
          change (a + 3 * q) % 2 ^ t = _; rw [h4q]; exact hshift_mod
        have harg2 : (j' + 1) % 2 ^ t = (2 * qa) % (4 * q) := by
          rw [h4q]; exact hj_mod
        rw [harg1, harg2]
        change ((phi t qa + phi t ((qa + 3 * q) % (4 * q))) % 4 +
                (2 * if 1 ≤ r' ∧ r' < q then 1 else 0) % 4) % 4 = phi t ((2 * qa) % (4 * q))
        rw [hr'_eq]
        -- 8 disjoint cases on `qa ∈ [0, 4*q)`
        by_cases c0 : qa = 0
        · rw [c0]
          have h1 : (0 + 3 * q) % (4 * q) = 3 * q := by
            rw [Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega)
          rw [h1]; simp only [Nat.mul_zero, Nat.zero_mod]
          unfold phi; rw [h2q]
          simp [show 3 * q ≠ 0 by omega, show ¬ (3 * q < 2 * q) by omega, show 3 * q ≠ 2 * q by omega]
        · by_cases c1 : qa < q
          · have h1 : (qa + 3 * q) % (4 * q) = qa + 3 * q := Nat.mod_eq_of_lt (by omega)
            have h2 : (2 * qa) % (4 * q) = 2 * qa := Nat.mod_eq_of_lt (by omega)
            have h3 : qa % (2 * q) = qa := Nat.mod_eq_of_lt (by omega)
            rw [h1, h2, h3]
            have hcond : 1 ≤ qa ∧ qa < q := by omega
            have hv : v2 (2 * qa) = 1 + v2 qa := v2_two_mul qa (by omega)
            unfold phi; rw [h2q]
            simp only [c0, hcond, show qa < 2 * q by omega, show qa + 3 * q ≠ 0 by omega,
                       show ¬ (qa + 3 * q < 2 * q) by omega, show qa + 3 * q ≠ 2 * q by omega,
                       show 2 * qa ≠ 0 by omega, show 2 * qa < 2 * q by omega, hv, ↓reduceIte]
            by_cases hvp : v2 qa % 2 = 0
            · simp [hvp, show (1 + v2 qa) % 2 ≠ 0 by omega]
            · simp [hvp, show (1 + v2 qa) % 2 = 0 by omega]
          · by_cases c2 : qa = q
            · rw [c2]
              have h1 : (q + 3 * q) % (4 * q) = 0 := by rw [show q + 3 * q = 4 * q by omega, Nat.mod_self]
              have h2 : (2 * q) % (4 * q) = 2 * q := Nat.mod_eq_of_lt (by omega)
              have h3 : q % (2 * q) = q := Nat.mod_eq_of_lt (by omega)
              rw [h1, h2, h3]
              have hv : v2 q = t - 2 := v2_pow2 (t - 2)
              unfold phi; rw [h2q]
              simp only [show q ≠ 0 by omega, show q < 2 * q by omega, show ¬ (1 ≤ q ∧ q < q) by omega,
                         show 2 * q ≠ 0 by omega, show ¬ (2 * q < 2 * q) by omega, hv, ↓reduceIte]
              by_cases htp : t % 2 = 0
              · simp [htp, show (t - 2) % 2 = 0 by omega]
              · simp [htp, show (t - 2) % 2 ≠ 0 by omega]
            · by_cases c3 : qa < 2 * q
              · have h1 : (qa + 3 * q) % (4 * q) = qa - q := by
                  rw [show qa + 3 * q = (qa - q) + 4 * q by omega, Nat.add_mod_right,
                      Nat.mod_eq_of_lt (by omega)]
                have h2 : (2 * qa) % (4 * q) = 2 * qa := Nat.mod_eq_of_lt (by omega)
                have h3 : qa % (2 * q) = qa := Nat.mod_eq_of_lt (by omega)
                rw [h1, h2, h3]
                have hv : v2 qa = v2 (qa - q) := by
                  have hsplit : qa = (qa - q) + 2 ^ (t - 2) := by omega
                  conv => lhs; rw [hsplit]
                  exact v2_add_pow2 (t - 2) (qa - q) (by omega) (by omega)
                unfold phi; rw [h2q]
                simp only [c0, c3, show qa - q ≠ 0 by omega, show qa - q < 2 * q by omega,
                           show ¬ (1 ≤ qa ∧ qa < q) by omega, show 2 * qa ≠ 0 by omega,
                           show ¬ (2 * qa < 2 * q) by omega, show 2 * qa ≠ 2 * q by omega, hv, ↓reduceIte]
                split <;> simp
              · by_cases c4 : qa = 2 * q
                · rw [c4]
                  have h1 : (2 * q + 3 * q) % (4 * q) = q := by
                    rw [show 2 * q + 3 * q = q + 4 * q by omega, Nat.add_mod_right,
                        Nat.mod_eq_of_lt (by omega)]
                  have h2 : (2 * (2 * q)) % (4 * q) = 0 := by
                    rw [show 2 * (2 * q) = 4 * q by omega, Nat.mod_self]
                  have h3 : (2 * q) % (2 * q) = 0 := Nat.mod_self (2 * q)
                  rw [h1, h2, h3]
                  have hv : v2 q = t - 2 := v2_pow2 (t - 2)
                  unfold phi; rw [h2q]
                  simp only [show 2 * q ≠ 0 by omega, show ¬ (2 * q < 2 * q) by omega,
                             show q ≠ 0 by omega, show q < 2 * q by omega,
                             show ¬ (1 ≤ 0 ∧ 0 < q) by omega, hv, ↓reduceIte]
                  by_cases htp : t % 2 = 0
                  · simp [htp, show (t - 2) % 2 = 0 by omega]
                  · simp [htp, show (t - 2) % 2 ≠ 0 by omega]
                · by_cases c5 : qa < 3 * q
                  · let d := qa - 2 * q
                    have hd_pos : d ≥ 1 := by omega
                    have hd_lt : d < q := by omega
                    have h1 : (qa + 3 * q) % (4 * q) = d + q := by
                      rw [show qa + 3 * q = (d + q) + 4 * q by omega, Nat.add_mod_right,
                          Nat.mod_eq_of_lt (by omega)]
                    have h2 : (2 * qa) % (4 * q) = 2 * d := by
                      rw [show 2 * qa = 2 * d + 4 * q by omega, Nat.add_mod_right,
                          Nat.mod_eq_of_lt (by omega)]
                    have h3 : qa % (2 * q) = d := by
                      rw [show qa = d + 2 * q by omega, Nat.add_mod_right,
                          Nat.mod_eq_of_lt (by omega)]
                    rw [h1, h2, h3]
                    have hv1 : v2 (d + q) = v2 d := v2_add_pow2 (t - 2) d hd_pos hd_lt
                    have hv2 : v2 (2 * d) = 1 + v2 d := v2_two_mul d hd_pos
                    have hcond : 1 ≤ d ∧ d < q := ⟨hd_pos, hd_lt⟩
                    unfold phi; rw [h2q]
                    simp only [c0, c3, c4, hcond, show d + q ≠ 0 by omega, show d + q < 2 * q by omega,
                               show 2 * d ≠ 0 by omega, show 2 * d < 2 * q by omega, hv1, hv2, ↓reduceIte]
                    by_cases hvp : v2 d % 2 = 0
                    · simp [hvp, show (1 + v2 d) % 2 ≠ 0 by omega]
                    · simp [hvp, show (1 + v2 d) % 2 = 0 by omega]
                  · by_cases c6 : qa = 3 * q
                    · rw [c6]
                      have h1 : (3 * q + 3 * q) % (4 * q) = 2 * q := by
                        rw [show 3 * q + 3 * q = 2 * q + 4 * q by omega, Nat.add_mod_right,
                            Nat.mod_eq_of_lt (by omega)]
                      have h2 : (2 * (3 * q)) % (4 * q) = 2 * q := by
                        rw [show 2 * (3 * q) = 2 * q + 4 * q by omega, Nat.add_mod_right,
                            Nat.mod_eq_of_lt (by omega)]
                      have h3 : (3 * q) % (2 * q) = q := by
                        rw [show 3 * q = q + 2 * q by omega, Nat.add_mod_right,
                            Nat.mod_eq_of_lt (by omega)]
                      rw [h1, h2, h3]
                      unfold phi; rw [h2q]
                      simp only [show 3 * q ≠ 0 by omega, show ¬ (3 * q < 2 * q) by omega,
                                 show 3 * q ≠ 2 * q by omega, show 2 * q ≠ 0 by omega,
                                 show ¬ (2 * q < 2 * q) by omega, show ¬ (1 ≤ q ∧ q < q) by omega,
                                 ↓reduceIte]
                      split <;> simp
                    · have h1 : (qa + 3 * q) % (4 * q) = qa - q := by
                        rw [show qa + 3 * q = (qa - q) + 4 * q by omega, Nat.add_mod_right,
                            Nat.mod_eq_of_lt (by omega)]
                      have h2 : (2 * qa) % (4 * q) = 2 * qa - 4 * q := by
                        conv => lhs; rw [show 2 * qa = (2 * qa - 4 * q) + 4 * q by omega]
                        rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
                      have h3 : qa % (2 * q) = qa - 2 * q := by
                        conv => lhs; rw [show qa = (qa - 2 * q) + 2 * q by omega]
                        rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
                      rw [h1, h2, h3]
                      unfold phi; rw [h2q]
                      simp only [c0, c3, c4, show qa - q ≠ 0 by omega, show ¬ (qa - q < 2 * q) by omega,
                                 show qa - q ≠ 2 * q by omega, show ¬ (1 ≤ qa - 2 * q ∧ qa - 2 * q < q) by omega,
                                 show 2 * qa - 4 * q ≠ 0 by omega, show ¬ (2 * qa - 4 * q < 2 * q) by omega,
                                 show 2 * qa - 4 * q ≠ 2 * q by omega, ↓reduceIte]

/-- **Theorem B (Universal Carry-Valuation Law for All Odd `r = 2^t * u - 1`):**
    For every `t ≥ 1`, every odd `u`, and every `j : Nat`,
    `b_{2^t * u - 1}(2 * u * j) mod 4 = Φ_t(j mod 2^t)` — strictly periodic of period `2^t`,
    independent of the odd factor `u`, and governed by the parity of `v_2(j mod 2^t)`. -/
theorem br_universal_mod4_carry_law (t u : Nat) (ht : t ≥ 1) (hu : u % 2 = 1) (j : Nat) :
    br (2 ^ t * u - 1) (2 * u * j) % 4 = phi t (j % 2 ^ t) := by
  have hpow : 2 ^ t = 2 * 2 ^ (t - 1) := by
    conv => lhs; rw [show t = (t - 1) + 1 by omega]
    rw [Nat.pow_succ]; omega
  have hr_eq : 2 ^ t * u - 1 = 2 * (2 ^ (t - 1) * u - 1) + 1 := by
    have hp : 2 ^ (t - 1) ≥ 1 := Nat.pow_pos (by omega)
    have hpos : 2 ^ (t - 1) * u ≥ 1 := Nat.mul_pos hp (by omega)
    rw [hpow, Nat.mul_assoc]; omega
  rw [hr_eq, Nat.mul_assoc 2 u j]
  change S (2 ^ (t - 1) * u - 1) (u * j) % 4 = phi t (j % 2 ^ t)
  by_cases ht1 : t = 1
  · subst ht1
    let k := (u - 1) / 2
    have hu_eq : u = 2 * k + 1 := by omega
    have hm_eq : 2 ^ (1 - 1) * u - 1 = 2 * k := by simp [hu_eq]
    rw [hm_eq, hu_eq, S_t1_mod4 k j]
    unfold phi
    have hlt : j % 2 < 2 := Nat.mod_lt j (by omega)
    by_cases h0 : j % 2 = 0
    · simp [h0]
    · have h1 : j % 2 = 1 := by omega
      simp [h1]
  · exact S_ge2_mod4 t u (by omega) hu j

/-! ### Theorem C: Complete `v_2(r + 1)` Parity Dichotomy (`∀ r ≥ 1`) -/

/-- Exact identity for even `r = 2k`: `b_{2k}(2k+1) + b_{2k}(4k+2) + 1 = S(2k, 2k+1)`. -/
theorem br_even_sum_identity (k : Nat) :
    br (2 * k) (2 * k + 1) + br (2 * k) (4 * k + 2) + 1 = S (2 * k) (2 * k + 1) := by
  rw [S_eq_partial_sum (2 * k) (2 * k + 1)]
  rw [show 4 * k + 2 = 2 * (2 * k + 1) by omega]
  rw [br_odd (2 * k) k, br_even (2 * k) (2 * k + 1)]
  rw [show (2 * k + 1) / 2 = k by omega, show (2 * k) / 2 + 1 = k + 1 by omega]
  have h1 := sumShift_split (br (2 * k)) (2 * k + 1) 0 (k + 1) (k + 1)
  rw [show (k + 1) + (k + 1) = 2 * k + 2 by omega, Nat.zero_add] at h1
  rw [h1]
  have h2 := sumShift_split (br (2 * k)) (2 * k + 1) (k + 1) k 1
  rw [h2]
  have hzero : sumShift (br (2 * k)) (2 * k + 1) (k + 1 + k) 1 = 1 := by
    simp [sumShift, show k + 1 + k = 2 * k + 1 by omega, br, binPart_zero]
  have hmid : sumShift (br (2 * k)) (2 * k + 1) (k + 1) k = sumShift (br (2 * k)) k 0 k := by
    rw [sumShift_rebase (br (2 * k)) (2 * k + 1) (k + 1) k (by omega)]
    rw [show 2 * k + 1 - (k + 1) = k by omega]
  rw [hzero, hmid]
  omega

/-- Constructive sharpness witness for every `r` with even `v_2(r + 1) ≥ 2`: `b_r(r + 1) ≡ 3 (mod 4)`. -/
theorem br_witness_even_v2_ge2 (r : Nat) (hge : v2 (r + 1) ≥ 2) (heven : v2 (r + 1) % 2 = 0) :
    br r (r + 1) % 4 = 3 := by
  obtain ⟨u, hu_odd, hr1⟩ := exists_pow2_mul_odd (r + 1) (by omega)
  let t := v2 (r + 1)
  have ht_ge : t ≥ 2 := hge
  have ht_ev : t % 2 = 0 := heven
  have hr1' : r + 1 = 2 ^ t * u := hr1
  have hr : r = 2 ^ t * u - 1 := by omega
  have hpow : 2 ^ t = 2 * 2 ^ (t - 1) := by
    conv => lhs; rw [show t = (t - 1) + 1 by omega]
    rw [Nat.pow_succ]; omega
  have hn : r + 1 = 2 * u * 2 ^ (t - 1) := by
    rw [hr1', hpow, Nat.mul_assoc, Nat.mul_comm (2 ^ (t - 1)) u, ← Nat.mul_assoc]
  rw [hn, hr, br_universal_mod4_carry_law t u (by omega) hu_odd (2 ^ (t - 1))]
  have hlt : 2 ^ (t - 1) < 2 ^ t := by
    rw [hpow]; have := Nat.pow_pos (a := 2) (n := t - 1) (by omega); omega
  rw [Nat.mod_eq_of_lt hlt]
  unfold phi
  simp [ht_ev]

/-- Constructive sharpness witness for every even `r = 2k ≥ 2` (`v_2(r + 1) = 0`):
    either `b_r(r + 1) ≡ 3 (mod 4)` or `b_r(2(r + 1)) ≡ 3 (mod 4)`. -/
theorem br_witness_even_r (k : Nat) (hk : k ≥ 1) :
    br (2 * k) (2 * k + 1) % 4 = 3 ∨ br (2 * k) (4 * k + 2) % 4 = 3 := by
  have hsum := br_even_sum_identity k
  have hS1 : S (2 * k) (2 * k + 1) % 4 = 1 := by
    simpa [Nat.mul_one] using S_t1_mod4 k 1
  have hodd : br (2 * k) (2 * k + 1) % 2 = 1 := by
    rw [br_mod2_universal (2 * k) (by omega) (2 * k + 1), Nat.mod_self]
    simp
  omega

/-- **Theorem C (Complete 2-Adic Valuation Parity Dichotomy, `∀ r ≥ 1`):**
    The `r`-restricted binary partition function `b_r(n)` avoids residue `3 (mod 4)` for ALL
    `n ∈ ℕ` if and only if the 2-adic valuation `v_2(r + 1)` is ODD. -/
theorem br_forbids_three_mod4_iff (r : Nat) (hr : r ≥ 1) :
    (∀ n : Nat, br r n % 4 ≠ 3) ↔ v2 (r + 1) % 2 = 1 := by
  constructor
  · intro hforbid
    by_cases hodd : v2 (r + 1) % 2 = 1
    · exact hodd
    · exfalso
      have heven : v2 (r + 1) % 2 = 0 := by omega
      by_cases hv0 : v2 (r + 1) = 0
      · have hr_even : r % 2 = 0 := by
          by_cases hre : r % 2 = 0
          · exact hre
          · have hpos : (r + 1) / 2 > 0 := by omega
            have h1 : r + 1 = 2 * ((r + 1) / 2) := by omega
            have hv1 : v2 (r + 1) = 1 + v2 ((r + 1) / 2) := by
              conv => lhs; rw [h1]
              exact v2_two_mul _ hpos
            omega
        let k := r / 2
        have hk : k ≥ 1 := by omega
        have hr_eq : r = 2 * k := by omega
        rw [hr_eq] at hforbid
        rcases br_witness_even_r k hk with h1 | h2
        · exact hforbid (2 * k + 1) h1
        · exact hforbid (4 * k + 2) h2
      · exact hforbid (r + 1) (br_witness_even_v2_ge2 r (by omega) heven)
  · intro hv_odd n
    obtain ⟨u, hu_odd, hr1⟩ := exists_pow2_mul_odd (r + 1) (by omega)
    let t := v2 (r + 1)
    have ht_odd : t % 2 = 1 := hv_odd
    have ht_pos : t ≥ 1 := by omega
    have hr1' : r + 1 = 2 ^ t * u := hr1
    have hpow : 2 ^ t = 2 * 2 ^ (t - 1) := by
      conv => lhs; rw [show t = (t - 1) + 1 by omega]
      rw [Nat.pow_succ]; omega
    have hr_eq : r = 2 ^ t * u - 1 := by omega
    have hM_pos : 2 ^ (t - 1) * u ≥ 1 := Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)
    have hr_odd : r = 2 * (2 ^ (t - 1) * u - 1) + 1 := by
      rw [hr_eq, hpow, Nat.mul_assoc]; omega
    rw [hr_odd, br_odd_r_eq_S]
    by_cases hdiv : (n / 2) % (2 ^ (t - 1) * u) = 0
    · let c := (n / 2) / (2 ^ (t - 1) * u)
      have hn2 : n / 2 = u * (2 ^ (t - 1) * c) := by
        have h1 : n / 2 = 2 ^ (t - 1) * u * c := by
          have := (Nat.div_add_mod (n / 2) (2 ^ (t - 1) * u)).symm
          rw [hdiv, Nat.add_zero] at this; exact this
        rw [h1, Nat.mul_comm (2 ^ (t - 1)) u, Nat.mul_assoc]
      have hval : S (2 ^ (t - 1) * u - 1) (n / 2) % 4 = phi t ((2 ^ (t - 1) * c) % 2 ^ t) := by
        have hlaw := br_universal_mod4_carry_law t u ht_pos hu_odd (2 ^ (t - 1) * c)
        rw [← hr_eq, hr_odd, Nat.mul_assoc 2 u _, ← hn2] at hlaw
        exact hlaw
      rw [hval]
      have hmod_cases : (2 ^ (t - 1) * c) % 2 ^ t = 0 ∨ (2 ^ (t - 1) * c) % 2 ^ t = 2 ^ (t - 1) := by
        rw [hpow, Nat.mul_comm 2 (2 ^ (t - 1)), Nat.mul_mod_mul_left]
        have : c % 2 = 0 ∨ c % 2 = 1 := by omega
        rcases this with hc0 | hc1
        · left; simp [hc0]
        · right; simp [hc1]
      rcases hmod_cases with hm0 | hmh
      · rw [hm0]; unfold phi; simp
      · rw [hmh]; unfold phi
        simp [show t % 2 ≠ 0 by omega]
    · have hev : S (2 ^ (t - 1) * u - 1) (n / 2) % 2 = 0 := by
        rw [S_mod2, show 2 ^ (t - 1) * u - 1 + 1 = 2 ^ (t - 1) * u by omega]
        simp [hdiv]
      omega

/-! ## Section 5: Non-Vacuity Witnesses, Sharpness Counterexamples, and Axiom Verification -/

/-- Non-vacuity witnesses: concrete `r` satisfying `v2(r+1) % 2 = 1` (odd 2-adic valuation). -/
example : v2 (5 + 1) % 2 = 1 := by decide
example : v2 (7 + 1) % 2 = 1 := by decide
example : v2 (23 + 1) % 2 = 1 := by decide
example : v2 (31 + 1) % 2 = 1 := by decide

/-- Non-vacuity of `WindowAutomatonCert`: verified concrete certificate inhabits all hypotheses. -/
example : Nonempty { c : WindowAutomatonCert // ValidDigitSet c.D c.L ∧ c.isValid = true } :=
  ⟨⟨cert_b4, validDigitSetBool_sound (by decide), cert_b4_valid⟩⟩

/-- Boundary sharpness counterexamples in `r` (even `v_2(r+1)` hits `3 mod 4`). -/
theorem sharpness_r3_even_v2 : br 3 4 % 4 = 3 := by decide
theorem sharpness_r11_even_v2 : br 11 12 % 4 = 3 := by decide
theorem sharpness_r2_even_r : br 2 6 % 4 = 3 := by decide
theorem sharpness_r4_even_r : br 4 5 % 4 = 3 := by decide

/-- Modulus sharpness counterexamples (congruences hold mod 4, FAIL mod 8!). -/
theorem sharpness_b5_fails_mod8 : br 5 6 % 8 ≠ 1 := by decide
theorem sharpness_b4_16n5_fails_mod8 : br 4 (16 * 0 + 5) % 8 ≠ (7 * br 4 0) % 8 := by decide
theorem sharpness_gap023_32n16_fails_mod8 :
    binPart [0, 2, 3] (32 * 0 + 16) % 8 ≠ (7 * binPart [0, 2, 3] 0) % 8 := by decide

/-- Offset sharpness counterexamples (shifting the offset breaks the mod-4 congruence!). -/
theorem sharpness_b4_offset10_fails : br 4 (16 * 0 + 10) % 4 ≠ (3 * br 4 0) % 4 := by decide
theorem sharpness_gap023_offset17_fails :
    binPart [0, 2, 3] (32 * 0 + 17) % 4 ≠ (3 * binPart [0, 2, 3] 0) % 4 := by decide

end BinaryPartitionAutomaton
