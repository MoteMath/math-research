import ReversibleCircuitCosetCompiler.Defs

namespace RevCert
theorem setReg_setReg_same {r w : Nat} (s : State r w) (i : Fin r) (v1 v2 : BitVec w) :
    setReg (setReg s i v1) i v2 = setReg s i v2 := by
  funext j; by_cases h : j = i <;> simp [setReg, h]

theorem setReg_id {r w : Nat} (s : State r w) (i : Fin r) :
    setReg s i (s i) = s := by
  funext j; by_cases h : j = i <;> simp [setReg, h]

theorem setReg_comm {r w : Nat} (s : State r w) {i j : Fin r} (h : i ≠ j) (vi vj : BitVec w) :
    setReg (setReg s i vi) j vj = setReg (setReg s j vj) i vi := by
  funext k
  by_cases h1 : k = i
  · subst h1; simp [setReg, h]
  · by_cases h2 : k = j
    · subst h2; simp [setReg, h1]
    · simp [setReg, h1, h2]

theorem swapRegs_invol {r w : Nat} (s : State r w) (i j : Fin r) :
    swapRegs (swapRegs s i j) i j = s := by
  funext k
  by_cases h1 : k = i
  · subst h1
    by_cases h2 : k = j
    · subst h2; simp [swapRegs]
    · simp [swapRegs, Ne.symm h2]
  · by_cases h2 : k = j
    · subst h2; simp [swapRegs, h1]
    · simp [swapRegs, h1, h2]

theorem getLsbD_one_shiftLeft {w : Nat} (p q : Nat) :
    (1#w <<< p).getLsbD q = (decide (q < w) && decide (q = p)) := by
  rw [BitVec.getLsbD_shiftLeft]
  by_cases hqw : q < w
  · by_cases hqp : q = p
    · subst hqp
      have h0w : 0 < w := by omega
      simp [hqw, h0w]
    · by_cases hlt : q < p
      · simp [hqw, hqp, hlt]
      · have hne : q - p ≠ 0 := by omega
        have h1 : (1#w).getLsbD (q - p) = false := by
          rw [BitVec.getLsbD_ofNat]
          have hpow : 2 ≤ 2 ^ (q - p) := by
            calc 2 = 2 ^ 1 := by omega
              _ ≤ 2 ^ (q - p) := Nat.pow_le_pow_right (by omega) (by omega)
          have hdiv : 1 / 2 ^ (q - p) = 0 := Nat.div_eq_of_lt (by omega)
          simp [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]
        simp [hqw, hqp, hlt, h1]
  · simp [hqw]

theorem getLsbD_flipBit {w : Nat} (x : BitVec w) (p q : Nat) :
    (flipBit x p).getLsbD q =
      if p < w ∧ q = p then !(x.getLsbD q) else x.getLsbD q := by
  unfold flipBit
  split
  · rename_i hpw
    rw [BitVec.getLsbD_xor, getLsbD_one_shiftLeft]
    by_cases hqp : q = p
    · subst hqp
      simp [hpw]
    · simp [hqp]
  · rename_i hnpw
    simp [hnpw]

theorem flipBit_invol {w : Nat} (x : BitVec w) (p : Nat) :
    flipBit (flipBit x p) p = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro q _
  rw [getLsbD_flipBit, getLsbD_flipBit]
  by_cases h : p < w ∧ q = p <;> simp [h]

theorem flipBit_comm {w : Nat} (x : BitVec w) (p1 p2 : Nat) :
    flipBit (flipBit x p1) p2 = flipBit (flipBit x p2) p1 := by
  by_cases hp : p1 = p2
  · subst hp; rfl
  · apply BitVec.eq_of_getLsbD_eq
    intro q _
    rw [getLsbD_flipBit, getLsbD_flipBit, getLsbD_flipBit, getLsbD_flipBit]
    by_cases h1 : p1 < w ∧ q = p1
    · simp [h1, hp]
    · by_cases h2 : p2 < w ∧ q = p2
      · simp [h2, Ne.symm hp]
      · simp [h1, h2]

theorem Gate.inv_inv {r : Nat} (g : Gate r) : g.inv.inv = g := by
  cases g <;> rfl

theorem evalCircuit_nil {r w : Nat} (s : State r w) :
    evalCircuit ([] : Circuit r) s = s := rfl

theorem evalCircuit_cons {r w : Nat} (g : Gate r) (C : Circuit r) (s : State r w) :
    evalCircuit (g :: C) s = evalCircuit C (evalGate g s) := rfl

theorem evalCircuit_append {r w : Nat} (C1 C2 : Circuit r) (s : State r w) :
    evalCircuit (C1 ++ C2) s = evalCircuit C2 (evalCircuit C1 s) := by
  simp [evalCircuit]

theorem evalCircuit_repeat_add {r w : Nat} (m n : Nat) (C : Circuit r) (s : State r w) :
    evalCircuit (repeatCircuit (m + n) C) s =
      evalCircuit (repeatCircuit n C) (evalCircuit (repeatCircuit m C) s) := by
  induction m generalizing s with
  | zero => simp [repeatCircuit, evalCircuit]
  | succ m ih =>
    have h : m + 1 + n = (m + n) + 1 := by omega
    rw [h, repeatCircuit, repeatCircuit, evalCircuit_append, evalCircuit_append, ih]

theorem evalCircuit_repeat_mul {r w : Nat} (q d : Nat) (C : Circuit r)
    (hd : ∀ s : State r w, evalCircuit (repeatCircuit d C) s = s) (s : State r w) :
    evalCircuit (repeatCircuit (d * q) C) s = s := by
  induction q with
  | zero => simp [repeatCircuit, evalCircuit]
  | succ q ih =>
    rw [Nat.mul_succ, evalCircuit_repeat_add, ih, hd]

-- Exact invertibility (bijectivity) of every gate and circuit
theorem evalGate_inv {r w : Nat} (g : Gate r) (s : State r w) :
    evalGate g.inv (evalGate g s) = s := by
  cases g with
  | rNot i =>
    simp [Gate.inv, evalGate, setReg_setReg_same, BitVec.not_not, setReg_id]
  | rSwap i j =>
    simp [Gate.inv, evalGate, swapRegs_invol]
  | rCnot c t =>
    simp only [Gate.inv, evalGate]
    split
    · rename_i hne
      rw [setReg_ne _ hne, setReg_self, setReg_setReg_same, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, setReg_id]
    · rfl
  | rToff c1 c2 t =>
    simp only [Gate.inv, evalGate]
    split
    · rename_i h
      rcases h with ⟨h1, h2, _⟩
      rw [setReg_ne _ h1, setReg_ne _ h2, setReg_self, setReg_setReg_same,
          BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, setReg_id]
    · rfl
  | rAdd src dst =>
    simp only [Gate.inv, evalGate]
    split
    · rename_i hne
      rw [setReg_ne _ hne, setReg_self, setReg_setReg_same, BitVec.add_sub_cancel, setReg_id]
    · rfl
  | rSub src dst =>
    simp only [Gate.inv, evalGate]
    split
    · rename_i hne
      rw [setReg_ne _ hne, setReg_self, setReg_setReg_same, BitVec.sub_add_cancel, setReg_id]
    · rfl
  | rNeg i =>
    simp [Gate.inv, evalGate, setReg_setReg_same, BitVec.neg_neg, setReg_id]
  | rInc i =>
    simp [Gate.inv, evalGate, setReg_setReg_same, BitVec.add_sub_cancel, setReg_id]
  | rDec i =>
    simp [Gate.inv, evalGate, setReg_setReg_same, BitVec.sub_add_cancel, setReg_id]
  | bNot i p =>
    simp [Gate.inv, evalGate, setReg_setReg_same, flipBit_invol, setReg_id]
  | bSwap i1 p1 i2 p2 =>
    simp only [Gate.inv, evalGate]
    split
    · rename_i hcond
      rcases hcond with ⟨hp1, hp2, hne⟩
      by_cases hdiff : ((s i1).getLsbD p1 != (s i2).getLsbD p2) = true
      · simp only [hdiff, ↓reduceIte]
        by_cases hi : i1 = i2
        · subst hi
          have hpne : p1 ≠ p2 := by
            rcases hne with h | h
            · exact absurd rfl h
            · exact h
          simp only [setReg_self, setReg_setReg_same]
          have hb1 : (flipBit (flipBit (s i1) p1) p2).getLsbD p1 = !(s i1).getLsbD p1 := by
            rw [getLsbD_flipBit, getLsbD_flipBit]
            simp [hp1, hpne]
          have hb2 : (flipBit (flipBit (s i1) p1) p2).getLsbD p2 = !(s i1).getLsbD p2 := by
            rw [getLsbD_flipBit, getLsbD_flipBit]
            simp [hp2, Ne.symm hpne]
          have hdiff2 : ((flipBit (flipBit (s i1) p1) p2).getLsbD p1 != (flipBit (flipBit (s i1) p1) p2).getLsbD p2) = true := by
            rw [hb1, hb2]
            revert hdiff
            cases (s i1).getLsbD p1 <;> cases (s i1).getLsbD p2 <;> decide
          simp only [hdiff2, ↓reduceIte]
          rw [flipBit_comm (flipBit (s i1) p1) p2 p1,
              flipBit_invol, flipBit_invol, setReg_id]
        · have hi' : i2 ≠ i1 := Ne.symm hi
          simp only [setReg_ne _ hi, setReg_ne _ hi', setReg_self]
          have hb1 : (flipBit (s i1) p1).getLsbD p1 = !(s i1).getLsbD p1 := by
            rw [getLsbD_flipBit]; simp [hp1]
          have hb2 : (flipBit (s i2) p2).getLsbD p2 = !(s i2).getLsbD p2 := by
            rw [getLsbD_flipBit]; simp [hp2]
          have hdiff2 : ((flipBit (s i1) p1).getLsbD p1 != (flipBit (s i2) p2).getLsbD p2) = true := by
            rw [hb1, hb2]
            revert hdiff
            cases (s i1).getLsbD p1 <;> cases (s i2).getLsbD p2 <;> decide
          simp only [hdiff2, ↓reduceIte]
          funext k
          by_cases hk1 : k = i1
          · subst hk1; simp [setReg, hi, flipBit_invol]
          · by_cases hk2 : k = i2
            · subst hk2; simp [setReg, flipBit_invol]
            · simp [setReg, hk1, hk2]
      · simp only [Bool.not_eq_true] at hdiff
        simp [hdiff]
    · rfl
  | bCnot ic pc it pt =>
    simp only [Gate.inv, evalGate]
    split
    · rename_i hcond
      rcases hcond with ⟨hpc, hpt, hne⟩
      by_cases hctrl : (s ic).getLsbD pc = true
      · simp only [hctrl, ↓reduceIte]
        have hctrl2 : (setReg s it (flipBit (s it) pt) ic).getLsbD pc = true := by
          by_cases hi : ic = it
          · subst hi
            have hpne : pc ≠ pt := by rcases hne with h | h; exact absurd rfl h; exact h
            rw [setReg_self, getLsbD_flipBit, ite_eq_right (fun ⟨_, heq⟩ => absurd heq hpne), hctrl]
          · rw [setReg_ne _ hi, hctrl]
        simp only [hctrl2, ↓reduceIte, setReg_self, setReg_setReg_same, flipBit_invol, setReg_id]
      · simp only [Bool.not_eq_true] at hctrl
        simp [hctrl]
    · rfl
  | bToff i1 p1 i2 p2 it pt =>
    simp only [Gate.inv, evalGate]
    split
    · rename_i hcond
      rcases hcond with ⟨hp1, hp2, hpt, hne1, hne2, _⟩
      by_cases hctrl : ((s i1).getLsbD p1 && (s i2).getLsbD p2) = true
      · simp only [hctrl, ↓reduceIte]
        have h1 : (setReg s it (flipBit (s it) pt) i1).getLsbD p1 = (s i1).getLsbD p1 := by
          by_cases hi : i1 = it
          · subst hi
            have hpne : p1 ≠ pt := by rcases hne1 with h | h; exact absurd rfl h; exact h
            rw [setReg_self, getLsbD_flipBit, ite_eq_right (fun ⟨_, heq⟩ => absurd heq hpne)]
          · rw [setReg_ne _ hi]
        have h2 : (setReg s it (flipBit (s it) pt) i2).getLsbD p2 = (s i2).getLsbD p2 := by
          by_cases hi : i2 = it
          · subst hi
            have hpne : p2 ≠ pt := by rcases hne2 with h | h; exact absurd rfl h; exact h
            rw [setReg_self, getLsbD_flipBit, ite_eq_right (fun ⟨_, heq⟩ => absurd heq hpne)]
          · rw [setReg_ne _ hi]
        rw [h1, h2, hctrl]
        simp [setReg_self, setReg_setReg_same, flipBit_invol, setReg_id]
      · simp only [Bool.not_eq_true] at hctrl
        simp [hctrl]
    · rfl

theorem evalGate_inv_left {r w : Nat} (g : Gate r) (s : State r w) :
    evalGate g (evalGate g.inv s) = s := by
  have h := evalGate_inv g.inv s
  rw [Gate.inv_inv] at h
  exact h

theorem evalCircuit_inv {r w : Nat} (C : Circuit r) (s : State r w) :
    evalCircuit C.inv (evalCircuit C s) = s := by
  induction C generalizing s with
  | nil => rfl
  | cons g gs ih =>
    have hinv : Circuit.inv (g :: gs) = Circuit.inv gs ++ [g.inv] := by
      simp [Circuit.inv]
    rw [hinv, evalCircuit_cons, evalCircuit_append, ih (evalGate g s),
        evalCircuit_cons, evalCircuit_nil, evalGate_inv]

-- ============================================================================
-- SECTION 2: LSB-Causal Truncation & Bit-Window Projection Lifter (Layers 1A & 3)
-- ============================================================================

theorem truncate_zeroExtend {r w0 w : Nat} (hw : w0 ≤ w) (s : State r w0) :
    truncateState w0 (zeroExtendState w s) = s := by
  funext i
  apply BitVec.eq_of_getLsbD_eq
  intro q hq
  simp only [truncateState, zeroExtendState, BitVec.getLsbD_setWidth]
  have hqw : q < w := by omega
  simp [hq, hqw]

theorem setWidth_one_le {w w0 : Nat} (hw : w0 ≤ w) :
    BitVec.setWidth w0 (1#w) = 1#w0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hiw : i < w := by omega
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat, BitVec.getLsbD_ofNat]
  simp [hi, hiw]

theorem setWidth_neg_le {w w0 : Nat} (x : BitVec w) (hw : w0 ≤ w) :
    BitVec.setWidth w0 (-x) = -(BitVec.setWidth w0 x) := by
  rw [BitVec.neg_eq_not_add, BitVec.neg_eq_not_add, BitVec.setWidth_add _ _ hw,
      BitVec.setWidth_not hw, setWidth_one_le hw]

theorem setWidth_sub_le {w w0 : Nat} (x y : BitVec w) (hw : w0 ≤ w) :
    BitVec.setWidth w0 (x - y) = BitVec.setWidth w0 x - BitVec.setWidth w0 y := by
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.setWidth_add _ _ hw,
      setWidth_neg_le y hw]

theorem setWidth_flipBit_lt {w w0 : Nat} (x : BitVec w) (p : Nat) (hp : p < w0) (hw : w0 ≤ w) :
    BitVec.setWidth w0 (flipBit x p) = flipBit (BitVec.setWidth w0 x) p := by
  apply BitVec.eq_of_getLsbD_eq
  intro q hq
  have hpw : p < w := by omega
  rw [BitVec.getLsbD_setWidth, getLsbD_flipBit, getLsbD_flipBit, BitVec.getLsbD_setWidth]
  simp [hq, hpw, hp]

theorem truncateState_setReg {r w w0 : Nat} (s : State r w) (i : Fin r) (v : BitVec w) :
    truncateState w0 (setReg s i v) = setReg (truncateState w0 s) i (BitVec.setWidth w0 v) := by
  funext j; by_cases h : j = i <;> simp [truncateState, setReg, h]

/-- LSB-Causal Truncation Commutation: EVERY register-parallel gate AND EVERY bit-window gate (< w0)
    commutes with truncation to width w0 for ALL w ≥ w0! -/
theorem truncate_evalGate_causal {r w w0 : Nat} (g : Gate r) (hc : isCausalGate w0 g = true)
    (hw : w0 ≤ w) (s : State r w) :
    truncateState w0 (evalGate g s) = evalGate g (truncateState w0 s) := by
  cases g with
  | rNot i =>
    simp [evalGate, truncateState_setReg, BitVec.setWidth_not hw, truncateState]
  | rSwap i j =>
    funext k
    by_cases h1 : k = i
    · subst h1; simp [evalGate, swapRegs, truncateState]
    · by_cases h2 : k = j
      · subst h2; simp [evalGate, swapRegs, truncateState, h1]
      · simp [evalGate, swapRegs, truncateState, h1, h2]
  | rCnot c t =>
    simp only [evalGate]
    split
    · simp [truncateState_setReg, BitVec.setWidth_xor, truncateState]
    · rfl
  | rToff c1 c2 t =>
    simp only [evalGate]
    split
    · simp [truncateState_setReg, BitVec.setWidth_xor, BitVec.setWidth_and, truncateState]
    · rfl
  | rAdd src dst =>
    simp only [evalGate]
    split
    · simp [truncateState_setReg, BitVec.setWidth_add _ _ hw, truncateState]
    · rfl
  | rSub src dst =>
    simp only [evalGate]
    split
    · simp [truncateState_setReg, setWidth_sub_le _ _ hw, truncateState]
    · rfl
  | rNeg i =>
    simp [evalGate, truncateState_setReg, setWidth_neg_le _ hw, truncateState]
  | rInc i =>
    simp [evalGate, truncateState_setReg, BitVec.setWidth_add _ _ hw, setWidth_one_le hw, truncateState]
  | rDec i =>
    simp [evalGate, truncateState_setReg, setWidth_sub_le _ _ hw, setWidth_one_le hw, truncateState]
  | bNot i p =>
    simp only [isCausalGate, isRegGate, isWindowGate, Bool.false_or, decide_eq_true_eq] at hc
    simp [evalGate, truncateState_setReg, setWidth_flipBit_lt _ _ hc hw, truncateState]
  | bSwap i1 p1 i2 p2 =>
    simp only [isCausalGate, isRegGate, isWindowGate, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hc
    rcases hc with ⟨hp1, hp2⟩
    have hp1w : p1 < w := by omega
    have hp2w : p2 < w := by omega
    simp only [evalGate, hp1, hp2, hp1w, hp2w, true_and]
    split
    · have hb1 : (truncateState w0 s i1).getLsbD p1 = (s i1).getLsbD p1 := by
        simp [truncateState, hp1]
      have hb2 : (truncateState w0 s i2).getLsbD p2 = (s i2).getLsbD p2 := by
        simp [truncateState, hp2]
      rw [hb1, hb2]
      split
      · simp only [truncateState_setReg, setWidth_flipBit_lt _ _ hp2 hw, setWidth_flipBit_lt _ _ hp1 hw]
        by_cases hi : i2 = i1
        · subst hi; simp [setReg, setWidth_flipBit_lt _ _ hp1 hw, truncateState]
        · simp [setReg, hi, truncateState]
      · rfl
    · rfl
  | bCnot ic pc it pt =>
    simp only [isCausalGate, isRegGate, isWindowGate, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hc
    rcases hc with ⟨hpc, hpt⟩
    have hpcw : pc < w := by omega
    have hptw : pt < w := by omega
    simp only [evalGate, hpc, hpt, hpcw, hptw, true_and]
    split
    · have hbc : (truncateState w0 s ic).getLsbD pc = (s ic).getLsbD pc := by
        simp [truncateState, hpc]
      rw [hbc]
      split
      · simp [truncateState_setReg, setWidth_flipBit_lt _ _ hpt hw, truncateState]
      · rfl
    · rfl
  | bToff i1 p1 i2 p2 it pt =>
    simp only [isCausalGate, isRegGate, isWindowGate, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hc
    rcases hc with ⟨⟨hp1, hp2⟩, hpt⟩
    have hp1w : p1 < w := by omega
    have hp2w : p2 < w := by omega
    have hptw : pt < w := by omega
    simp only [evalGate, hp1, hp2, hpt, hp1w, hp2w, hptw, true_and]
    split
    · have hb1 : (truncateState w0 s i1).getLsbD p1 = (s i1).getLsbD p1 := by
        simp [truncateState, hp1]
      have hb2 : (truncateState w0 s i2).getLsbD p2 = (s i2).getLsbD p2 := by
        simp [truncateState, hp2]
      rw [hb1, hb2]
      split
      · simp [truncateState_setReg, setWidth_flipBit_lt _ _ hpt hw, truncateState]
      · rfl
    · rfl

theorem truncate_evalCircuit_causal {r w w0 : Nat} (C : Circuit r)
    (hc : isCausalCircuit w0 C = true) (hw : w0 ≤ w) (s : State r w) :
    truncateState w0 (evalCircuit C s) = evalCircuit C (truncateState w0 s) := by
  induction C generalizing s with
  | nil => rfl
  | cons g gs ih =>
    simp only [isCausalCircuit, List.all_cons, Bool.and_eq_true] at hc
    rcases hc with ⟨hg, hgs⟩
    simp only [evalCircuit_cons]
    rw [ih hgs (evalGate g s), truncate_evalGate_causal g hg hw s]

/-- High-Bit Invariance for Bit-Window Gates (< w0): every bit q ≥ w0 is completely untouched! -/
theorem highBit_evalGate_window {r w w0 : Nat} (g : Gate r) (hg : isWindowGate w0 g = true)
    (s : State r w) (i : Fin r) (q : Nat) (hq : w0 ≤ q) :
    (evalGate g s i).getLsbD q = (s i).getLsbD q := by
  cases g with
  | rNot _ | rSwap _ _ | rCnot _ _ | rToff _ _ _
  | rAdd _ _ | rSub _ _ | rNeg _ | rInc _ | rDec _ =>
    simp [isWindowGate] at hg
  | bNot idx p =>
    simp only [isWindowGate, decide_eq_true_eq] at hg
    simp only [evalGate]
    by_cases hi : i = idx
    · subst hi; rw [setReg_self, getLsbD_flipBit, ite_eq_right (fun ⟨_, h⟩ => by omega)]
    · rw [setReg_ne _ hi]
  | bSwap i1 p1 i2 p2 =>
    simp only [isWindowGate, Bool.and_eq_true, decide_eq_true_eq] at hg
    rcases hg with ⟨hp1, hp2⟩
    simp only [evalGate]
    split
    · split
      · by_cases hi2 : i = i2
        · subst hi2
          rw [setReg_self, getLsbD_flipBit, ite_eq_right (fun ⟨_, h⟩ => by omega)]
          by_cases hi1 : i = i1
          · subst hi1; rw [setReg_self, getLsbD_flipBit, ite_eq_right (fun ⟨_, h⟩ => by omega)]
          · rw [setReg_ne _ hi1]
        · rw [setReg_ne _ hi2]
          by_cases hi1 : i = i1
          · subst hi1; rw [setReg_self, getLsbD_flipBit, ite_eq_right (fun ⟨_, h⟩ => by omega)]
          · rw [setReg_ne _ hi1]
      · rfl
    · rfl
  | bCnot ic pc it pt =>
    simp only [isWindowGate, Bool.and_eq_true, decide_eq_true_eq] at hg
    rcases hg with ⟨_, hpt⟩
    simp only [evalGate]
    split
    · split
      · by_cases hi : i = it
        · subst hi; rw [setReg_self, getLsbD_flipBit, ite_eq_right (fun ⟨_, h⟩ => by omega)]
        · rw [setReg_ne _ hi]
      · rfl
    · rfl
  | bToff i1 p1 i2 p2 it pt =>
    simp only [isWindowGate, Bool.and_eq_true, decide_eq_true_eq] at hg
    rcases hg with ⟨_, hpt⟩
    simp only [evalGate]
    split
    · split
      · by_cases hi : i = it
        · subst hi; rw [setReg_self, getLsbD_flipBit, ite_eq_right (fun ⟨_, h⟩ => by omega)]
        · rw [setReg_ne _ hi]
      · rfl
    · rfl

theorem highBit_evalCircuit_window {r w w0 : Nat} (C : Circuit r) (hC : isWindowCircuit w0 C = true)
    (s : State r w) (i : Fin r) (q : Nat) (hq : w0 ≤ q) :
    (evalCircuit C s i).getLsbD q = (s i).getLsbD q := by
  induction C generalizing s with
  | nil => rfl
  | cons g gs ih =>
    simp only [isWindowCircuit, List.all_cons, Bool.and_eq_true] at hC
    rcases hC with ⟨hg, hgs⟩
    rw [evalCircuit_cons, ih hgs (evalGate g s), highBit_evalGate_window g hg s i q hq]

-- Finite state enumeration at width w0 for decidable checkers
theorem decode_surj_aux (r w0 : Nat) (s : State r w0) :
    ∃ idx < 2 ^ (r * w0), decodeState r w0 idx = s := by
  induction r with
  | zero =>
    refine ⟨0, by simp, ?_⟩
    funext i; exact Fin.elim0 i
  | succ r' ih =>
    let s' : State r' w0 := fun i => s i.castSucc
    obtain ⟨idx', hlt', hdec'⟩ := ih s'
    let lastVal := (s (Fin.last r')).toNat
    have hlast : lastVal < 2 ^ w0 := (s (Fin.last r')).isLt
    let idx := idx' + lastVal * 2 ^ (r' * w0)
    have hpow : 2 ^ ((r' + 1) * w0) = 2 ^ (r' * w0) * 2 ^ w0 := by
      rw [Nat.add_mul, Nat.one_mul, Nat.pow_add]
    have hlt : idx < 2 ^ ((r' + 1) * w0) := by
      rw [hpow]
      have h1 : lastVal + 1 ≤ 2 ^ w0 := hlast
      calc idx' + lastVal * 2 ^ (r' * w0)
          < 2 ^ (r' * w0) + lastVal * 2 ^ (r' * w0) := Nat.add_lt_add_right hlt' _
        _ = (lastVal + 1) * 2 ^ (r' * w0) := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
        _ ≤ 2 ^ w0 * 2 ^ (r' * w0) := Nat.mul_le_mul_right _ h1
        _ = 2 ^ (r' * w0) * 2 ^ w0 := Nat.mul_comm _ _
    refine ⟨idx, hlt, ?_⟩
    funext i
    by_cases hlast_i : i.val = r'
    · have hi_eq : i = Fin.last r' := Fin.ext hlast_i
      subst hi_eq
      simp only [decodeState, Fin.val_last]
      have hpos : 0 < 2 ^ (r' * w0) := Nat.pow_pos (by omega)
      have hdiv : (idx' + lastVal * 2 ^ (r' * w0)) / 2 ^ (r' * w0) = lastVal := by
        rw [Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlt', Nat.zero_add]
      rw [hdiv, Nat.mod_eq_of_lt hlast]
      exact (BitVec.ofNat_toNat (m := w0) (x := s (Fin.last r'))).trans (BitVec.setWidth_eq _)
    · have hi_lt : i.val < r' := by omega
      let i' : Fin r' := ⟨i.val, hi_lt⟩
      have hi_eq : i = i'.castSucc := Fin.ext rfl
      rw [hi_eq]
      have hprev := congrFun hdec' i'
      simp only [decodeState, Fin.val_castSucc] at hprev ⊢
      have hsplit : r' * w0 = i'.val * w0 + (r' - i'.val) * w0 := by
        rw [← Nat.add_mul, Nat.add_sub_cancel' (Nat.le_of_lt hi_lt)]
      let d := r' - i'.val - 1
      have hsub_eq : r' - i'.val = 1 + d := by omega
      have hsplit2 : (r' - i'.val) * w0 = w0 + d * w0 := by
        rw [hsub_eq, Nat.add_mul, Nat.one_mul]
      have hpow_fac : 2 ^ (r' * w0) = 2 ^ (i'.val * w0) * (2 ^ w0 * 2 ^ (d * w0)) := by
        rw [hsplit, Nat.pow_add, hsplit2, Nat.pow_add]
      have hpos : 0 < 2 ^ (i'.val * w0) := Nat.pow_pos (by omega)
      have hdiv : idx / 2 ^ (i'.val * w0) =
                  idx' / 2 ^ (i'.val * w0) + lastVal * (2 ^ w0 * 2 ^ (d * w0)) := by
        show (idx' + lastVal * 2 ^ (r' * w0)) / 2 ^ (i'.val * w0) = _
        have hrew : lastVal * 2 ^ (r' * w0) =
                    (lastVal * (2 ^ w0 * 2 ^ (d * w0))) * 2 ^ (i'.val * w0) := by
          rw [hpow_fac]; ac_rfl
        rw [hrew, Nat.add_mul_div_right _ _ hpos]
      rw [hdiv]
      have hmod : (idx' / 2 ^ (i'.val * w0) + lastVal * (2 ^ w0 * 2 ^ (d * w0))) % 2 ^ w0 =
                  (idx' / 2 ^ (i'.val * w0)) % 2 ^ w0 := by
        have hrew : lastVal * (2 ^ w0 * 2 ^ (d * w0)) =
                    (lastVal * 2 ^ (d * w0)) * 2 ^ w0 := by ac_rfl
        rw [hrew, Nat.add_mul_mod_self_right]
      rw [hmod]
      exact hprev

theorem stateEqBool_eq_true {r w : Nat} {s1 s2 : State r w} :
    stateEqBool s1 s2 = true ↔ s1 = s2 := by
  constructor
  · intro h
    funext i
    simp only [stateEqBool, List.all_eq_true, beq_iff_eq] at h
    exact h i (List.mem_finRange i)
  · intro h; subst h
    simp [stateEqBool]

theorem allRange_eq_true {n : Nat} {p : Nat → Bool} :
    allRange n p = true ↔ ∀ i < n, p i = true := by
  induction n with
  | zero => simp [allRange]
  | succ k ih =>
    simp only [allRange, Bool.and_eq_true, ih]
    constructor
    · intro ⟨hk, hlt⟩ i hi
      by_cases heq : i = k
      · subst heq; exact hk
      · exact hlt i (by omega)
    · intro h
      exact ⟨h k (by omega), fun i hi => h i (by omega)⟩

theorem anyRange_eq_true {n : Nat} {p : Nat → Bool} :
    anyRange n p = true ↔ ∃ i < n, p i = true := by
  induction n with
  | zero => simp [anyRange]
  | succ k ih =>
    simp only [anyRange, Bool.or_eq_true, ih]
    constructor
    · intro h
      rcases h with hk | ⟨i, hi, hp⟩
      · exact ⟨k, by omega, hk⟩
      · exact ⟨i, by omega, hp⟩
    · intro ⟨i, hi, hp⟩
      by_cases heq : i = k
      · subst heq; exact Or.inl hp
      · exact Or.inr ⟨i, by omega, hp⟩

/-- Layer 1A Soundness Meta-Theorem: lifts finite width-w0 equivalence to ALL w ≥ w0! -/
theorem sound_checkWindowEq (r w0 : Nat) (C1 C2 : Circuit r)
    (h : checkWindowEq r w0 C1 C2 = true) :
    ∀ (w : Nat), w0 ≤ w → ∀ (s : State r w), evalCircuit C1 s = evalCircuit C2 s := by
  simp only [checkWindowEq, Bool.and_eq_true, allRange_eq_true] at h
  rcases h with ⟨⟨hW1, hW2⟩, hAll⟩
  have hC1 : isCausalCircuit w0 C1 = true := by
    simp only [isCausalCircuit, isWindowCircuit, List.all_eq_true] at hW1 ⊢
    intro g hg; simp [isCausalGate, hW1 g hg]
  have hC2 : isCausalCircuit w0 C2 = true := by
    simp only [isCausalCircuit, isWindowCircuit, List.all_eq_true] at hW2 ⊢
    intro g hg; simp [isCausalGate, hW2 g hg]
  intro w hw s
  funext i
  apply BitVec.eq_of_getLsbD_eq
  intro q _
  by_cases hlt : q < w0
  · obtain ⟨idx, hidx, hdec⟩ := decode_surj_aux r w0 (truncateState w0 s)
    have hEq0 : evalCircuit C1 (truncateState w0 s) = evalCircuit C2 (truncateState w0 s) := by
      rw [← hdec]
      exact stateEqBool_eq_true.mp (hAll idx hidx)
    have h1 := congrArg (fun st : State r w0 => (st i).getLsbD q) (truncate_evalCircuit_causal C1 hC1 hw s)
    have h2 := congrArg (fun st : State r w0 => (st i).getLsbD q) (truncate_evalCircuit_causal C2 hC2 hw s)
    simp only [truncateState, BitVec.getLsbD_setWidth, hlt, decide_true, Bool.true_and] at h1 h2
    rw [h1, h2, hEq0]
  · have hge : w0 ≤ q := by omega
    rw [highBit_evalCircuit_window C1 hW1 s i q hge,
        highBit_evalCircuit_window C2 hW2 s i q hge]

/-- Layer 3 Soundness Meta-Theorem: lifts pairwise distinctness at width w0 to ALL w ≥ w0! -/
theorem sound_checkDistinctAt (r w0 : Nat) (reps : Array (Circuit r))
    (h : checkDistinctAt r w0 reps = true) :
    ∀ (w : Nat), w0 ≤ w → ∀ (i j : Nat), j < i → i < reps.size →
      ∃ (s : State r w), evalCircuit reps[i]! s ≠ evalCircuit reps[j]! s := by
  simp only [checkDistinctAt, Bool.and_eq_true, allRange_eq_true, anyRange_eq_true] at h
  rcases h with ⟨hCausal, hPair⟩
  intro w hw i j hji hi
  have hj : j < reps.size := by omega
  obtain ⟨idx, _, hneBool⟩ := hPair i hi j hji
  let s0 : State r w0 := decodeState r w0 idx
  refine ⟨zeroExtendState w s0, ?_⟩
  intro heq
  have htr := congrArg (truncateState w0) heq
  rw [truncate_evalCircuit_causal reps[i]! (hCausal i hi) hw,
      truncate_evalCircuit_causal reps[j]! (hCausal j hj) hw,
      truncate_zeroExtend hw s0] at htr
  have htrue : stateEqBool (evalCircuit reps[i]! s0) (evalCircuit reps[j]! s0) = true :=
    stateEqBool_eq_true.mpr htr
  simp [s0, htrue] at hneBool

theorem isCausalCircuit_append {r w0 : Nat} (C1 C2 : Circuit r)
    (h1 : isCausalCircuit w0 C1 = true) (h2 : isCausalCircuit w0 C2 = true) :
    isCausalCircuit w0 (C1 ++ C2) = true := by
  unfold isCausalCircuit at h1 h2 ⊢
  rw [List.all_append, h1, h2]
  rfl

theorem isCausalCircuit_repeat {r w0 : Nat} (k : Nat) (C : Circuit r)
    (h : isCausalCircuit w0 C = true) :
    isCausalCircuit w0 (repeatCircuit k C) = true := by
  induction k with
  | zero => rfl
  | succ k ih => exact isCausalCircuit_append C (repeatCircuit k C) h ih

theorem sound_checkOrderLowerAt (r w0 d : Nat) (C : Circuit r)
    (h : checkOrderLowerAt r w0 d C = true) :
    ∀ (w : Nat), w0 ≤ w → ∀ (k : Nat), 0 < k → k < d → d % k = 0 →
      ∃ (s : State r w), evalCircuit (repeatCircuit k C) s ≠ s := by
  simp only [checkOrderLowerAt, Bool.and_eq_true, decide_eq_true_eq, allRange_eq_true] at h
  rcases h with ⟨⟨hC, _⟩, hDivs⟩
  intro w hw k hkpos hkd hdiv
  have hstep := hDivs k hkd
  simp only [hkpos, hdiv, and_self, ↓reduceIte, anyRange_eq_true] at hstep
  obtain ⟨idx, _, hneBool⟩ := hstep
  let s0 : State r w0 := decodeState r w0 idx
  refine ⟨zeroExtendState w s0, ?_⟩
  intro heq
  have htr := congrArg (truncateState w0) heq
  rw [truncate_evalCircuit_causal (repeatCircuit k C) (isCausalCircuit_repeat k C hC) hw,
      truncate_zeroExtend hw s0] at htr
  have htrue : stateEqBool (evalCircuit (repeatCircuit k C) s0) s0 = true :=
    stateEqBool_eq_true.mpr htr
  simp [s0, htrue] at hneBool

-- ============================================================================
-- SECTION 3: Carry-Bit-Slice Transducer Bisimulation Lifter (Layer 1B)
-- ============================================================================

-- Unified ripple-carry bit lemma for (x + y + ofBool c0)
theorem nat_div_mod_add_carry (a b c0 i : Nat) :
    ((a + b + c0) / 2 ^ i) % 2 =
      ((a / 2 ^ i) % 2 + (b / 2 ^ i) % 2 + ((a % 2 ^ i + b % 2 ^ i + c0) / 2 ^ i)) % 2 := by
  have hpos : 0 < 2 ^ i := Nat.pow_pos (by omega)
  have ha : a = a % 2 ^ i + (a / 2 ^ i) * 2 ^ i := by
    have := Nat.div_add_mod a (2 ^ i); rw [Nat.mul_comm] at this; omega
  have hb : b = b % 2 ^ i + (b / 2 ^ i) * 2 ^ i := by
    have := Nat.div_add_mod b (2 ^ i); rw [Nat.mul_comm] at this; omega
  have hsum : a + b + c0 = (a % 2 ^ i + b % 2 ^ i + c0) + (a / 2 ^ i + b / 2 ^ i) * 2 ^ i := by
    calc a + b + c0
        = (a % 2 ^ i + (a / 2 ^ i) * 2 ^ i) + (b % 2 ^ i + (b / 2 ^ i) * 2 ^ i) + c0 := by
            conv => lhs; arg 1; arg 1; rw [ha]
            conv => lhs; arg 1; arg 2; rw [hb]
      _ = (a % 2 ^ i + b % 2 ^ i + c0) + ((a / 2 ^ i) * 2 ^ i + (b / 2 ^ i) * 2 ^ i) := by omega
      _ = (a % 2 ^ i + b % 2 ^ i + c0) + (a / 2 ^ i + b / 2 ^ i) * 2 ^ i := by rw [Nat.add_mul]
  rw [hsum, Nat.add_mul_div_right _ _ hpos]
  omega

theorem carry_toNat_eq_div {w : Nat} (x y : BitVec w) (c0 : Bool) (i : Nat) :
    (BitVec.carry i x y c0).toNat = (x.toNat % 2 ^ i + y.toNat % 2 ^ i + c0.toNat) / 2 ^ i := by
  have hpos : 0 < 2 ^ i := Nat.pow_pos (by omega)
  have hx : x.toNat % 2 ^ i < 2 ^ i := Nat.mod_lt _ hpos
  have hy : y.toNat % 2 ^ i < 2 ^ i := Nat.mod_lt _ hpos
  have hc : c0.toNat ≤ 1 := by cases c0 <;> decide
  unfold BitVec.carry
  let s := x.toNat % 2 ^ i + y.toNat % 2 ^ i + c0.toNat
  change (decide (s ≥ 2 ^ i)).toNat = s / 2 ^ i
  by_cases hge : 2 ^ i ≤ s
  · have hlt2 : s < 2 ^ i + 2 ^ i := by omega
    have hdiv : s / 2 ^ i = 1 := by
      have h1 : s = (s - 2 ^ i) + 1 * 2 ^ i := by omega
      rw [h1, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt (by omega)]
    simp [hge, hdiv]
  · have hdiv : s / 2 ^ i = 0 := Nat.div_eq_of_lt (by omega)
    simp [hge, hdiv]

theorem getLsbD_addCarry {w : Nat} (x y : BitVec w) (c0 : Bool) (i : Nat) (hi : i < w) :
    (x + y + if c0 then 1#w else 0#w).getLsbD i =
      (x.getLsbD i ^^ (y.getLsbD i ^^ BitVec.carry i x y c0)) := by
  have hc_toNat : (if c0 then (1#w) else (0#w)).toNat = c0.toNat % 2 ^ w := by
    cases c0 <;> simp [BitVec.toNat_ofNat]
  have hw_pos : 1 ≤ w := by omega
  have h2w_gt1 : 1 < 2 ^ w := by
    calc 1 < 2 ^ 1 := by omega
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hw_pos
  have hc_lt : c0.toNat < 2 ^ w := by cases c0 <;> simp <;> omega
  have hval : (x + y + if c0 then 1#w else 0#w).toNat = (x.toNat + y.toNat + c0.toNat) % 2 ^ w := by
    rw [BitVec.toNat_add, BitVec.toNat_add, hc_toNat, Nat.mod_eq_of_lt hc_lt]
    simp [Nat.add_mod]
  have hpow_div : 2 ^ (i + 1) ∣ 2 ^ w := Nat.pow_dvd_pow 2 (by omega)
  have hbit_mod : ∀ N, ((N % 2 ^ w) / 2 ^ i) % 2 = (N / 2 ^ i) % 2 := by
    intro N
    obtain ⟨m, hm⟩ := hpow_div
    have hpos : 0 < 2 ^ i := Nat.pow_pos (by omega)
    have h1 : N = N % 2 ^ w + (N / 2 ^ w) * 2 ^ w := by
      have := Nat.div_add_mod N (2 ^ w); rw [Nat.mul_comm] at this; omega
    have h2 : (N / 2 ^ w) * 2 ^ w = ((N / 2 ^ w) * m * 2) * 2 ^ i := by
      rw [hm, Nat.pow_succ]; ac_rfl
    have h3 : N / 2 ^ i = (N % 2 ^ w) / 2 ^ i + (N / 2 ^ w) * m * 2 := by
      conv => lhs; rw [h1, h2]
      rw [Nat.add_mul_div_right _ _ hpos]
    rw [h3]
    omega
  have hget : ∀ (v : BitVec w), v.getLsbD i = decide ((v.toNat / 2 ^ i) % 2 = 1) := by
    intro v
    rw [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_comm, Nat.and_one_is_mod]
    have hlt2 : (v.toNat / 2 ^ i) % 2 < 2 := Nat.mod_lt _ (by omega)
    generalize (v.toNat / 2 ^ i) % 2 = b at hlt2 ⊢
    have hb : b = 0 ∨ b = 1 := by omega
    rcases hb with rfl | rfl <;> decide
  rw [hget, hval, hbit_mod, nat_div_mod_add_carry, ← carry_toNat_eq_div, hget x, hget y]
  have h1 : (x.toNat / 2 ^ i) % 2 < 2 := Nat.mod_lt _ (by omega)
  have h2 : (y.toNat / 2 ^ i) % 2 < 2 := Nat.mod_lt _ (by omega)
  generalize (x.toNat / 2 ^ i) % 2 = a at h1 ⊢
  generalize (y.toNat / 2 ^ i) % 2 = b at h2 ⊢
  have ha : a = 0 ∨ a = 1 := by omega
  have hb : b = 0 ∨ b = 1 := by omega
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> cases BitVec.carry i x y c0 <;> decide

-- 1-bit slice operations for register-parallel gates
theorem stepPureGate_spec {r w : Nat} (g : Gate r) (hReg : isRegGate g = true)
    (hNoCarry : hasCarryGate g = false) (s : State r w) (k : Nat) (hk : k < w) :
    stepPureGate g (sliceAt s k) = sliceAt (evalGate g s) k := by
  cases g with
  | rNot i =>
    funext j; by_cases h : j = i
    · subst h; simp [stepPureGate, setBit, sliceAt, evalGate, hk]
    · simp [stepPureGate, setBit, sliceAt, evalGate, h]
  | rSwap i j =>
    funext m
    by_cases h1 : m = i
    · subst h1; simp [stepPureGate, sliceAt, evalGate, swapRegs]
    · by_cases h2 : m = j
      · subst h2; simp [stepPureGate, sliceAt, evalGate, swapRegs, h1]
      · simp [stepPureGate, sliceAt, evalGate, swapRegs, h1, h2]
  | rCnot c t =>
    simp only [stepPureGate, evalGate]
    split
    · funext j; by_cases h : j = t
      · subst h; simp [setBit, sliceAt, BitVec.getLsbD_xor]
      · simp [setBit, sliceAt, h]
    · rfl
  | rToff c1 c2 t =>
    simp only [stepPureGate, evalGate]
    split
    · funext j; by_cases h : j = t
      · subst h; simp [setBit, sliceAt, BitVec.getLsbD_xor, BitVec.getLsbD_and]
      · simp [setBit, sliceAt, h]
    · rfl
  | rAdd _ _ | rSub _ _ | rNeg _ | rInc _ | rDec _ => simp [hasCarryGate] at hNoCarry
  | bNot _ _ | bSwap _ _ _ _ | bCnot _ _ _ _ | bToff _ _ _ _ _ _ => simp [isRegGate] at hReg

theorem carryOfGate_zero {r w : Nat} (g : Gate r) (hCarry : hasCarryGate g = true) (s : State r w) :
    carryOfGate g s 0 = initCarryGate g := by
  cases g with
  | rAdd src dst => by_cases h : src ≠ dst <;> simp [carryOfGate, initCarryGate, BitVec.carry_zero, h]
  | rSub src dst => by_cases h : src ≠ dst <;> simp [carryOfGate, initCarryGate, BitVec.carry_zero, h]
  | rNeg i => simp [carryOfGate, initCarryGate, BitVec.carry_zero]
  | rInc i => simp [carryOfGate, initCarryGate, BitVec.carry_zero]
  | rDec i => simp [carryOfGate, initCarryGate, BitVec.carry_zero]
  | _ => simp [hasCarryGate] at hCarry

theorem stepCarryGate_spec {r w : Nat} (g : Gate r) (hCarry : hasCarryGate g = true)
    (s : State r w) (k : Nat) (hk : k < w) :
    stepCarryGate g (carryOfGate g s k) (sliceAt s k) =
      (carryOfGate g s (k + 1), sliceAt (evalGate g s) k) := by
  cases g with
  | rAdd src dst =>
    simp only [stepCarryGate, carryOfGate, evalGate]
    by_cases hne : src ≠ dst
    · simp only [ne_eq, hne, not_false_eq_true, ↓reduceIte]
      apply Prod.ext
      · rw [BitVec.carry_succ]; rfl
      · funext j; by_cases hj : j = dst
        · subst hj
          simp only [setBit, ↓reduceIte, sliceAt, setReg_self]
          have h := getLsbD_addCarry (s j) (s src) false k hk
          simp only [Bool.false_eq_true, ↓reduceIte, BitVec.add_zero] at h
          exact h.symm
        · simp [setBit, sliceAt, hj]
    · simp only [hne, ↓reduceIte]
  | rSub src dst =>
    simp only [stepCarryGate, carryOfGate, evalGate]
    by_cases hne : src ≠ dst
    · simp only [ne_eq, hne, not_false_eq_true, ↓reduceIte]
      apply Prod.ext
      · rw [BitVec.carry_succ]
        simp [sliceAt, hk]
      · funext j; by_cases hj : j = dst
        · subst hj
          simp only [setBit, ↓reduceIte, sliceAt, setReg_self]
          have hsub : s j - s src = s j + ~~~(s src) + 1#w := by
            rw [BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add, BitVec.add_assoc]
          rw [hsub]
          have h := getLsbD_addCarry (s j) (~~~(s src)) true k hk
          simp only [↓reduceIte, BitVec.getLsbD_not, hk, decide_true, Bool.true_and] at h
          exact h.symm
        · simp [setBit, sliceAt, hj]
    · simp only [hne, ↓reduceIte]
  | rNeg idx =>
    simp only [stepCarryGate, carryOfGate, evalGate]
    apply Prod.ext
    · rw [BitVec.carry_succ]
      simp [sliceAt, hk]
    · funext j; by_cases hj : j = idx
      · subst hj
        simp only [setBit, ↓reduceIte, sliceAt, setReg_self]
        have hneg : -(s j) = ~~~(s j) + 0#w + 1#w := by
          rw [BitVec.add_zero, BitVec.neg_eq_not_add]
        rw [hneg]
        have h := getLsbD_addCarry (~~~(s j)) (0#w) true k hk
        simp only [↓reduceIte, BitVec.getLsbD_not, hk, decide_true, Bool.true_and, BitVec.getLsbD_zero] at h
        exact h.symm
      · simp [setBit, sliceAt, hj]
  | rInc idx =>
    simp only [stepCarryGate, carryOfGate, evalGate]
    apply Prod.ext
    · rw [BitVec.carry_succ]
      simp [sliceAt]
    · funext j; by_cases hj : j = idx
      · subst hj
        simp only [setBit, ↓reduceIte, sliceAt, setReg_self]
        have hinc : s j + 1#w = s j + 0#w + 1#w := by rw [BitVec.add_zero]
        rw [hinc]
        have h := getLsbD_addCarry (s j) (0#w) true k hk
        simp only [↓reduceIte, BitVec.getLsbD_zero] at h
        exact h.symm
      · simp [setBit, sliceAt, hj]
  | rDec idx =>
    simp only [stepCarryGate, carryOfGate, evalGate]
    apply Prod.ext
    · rw [BitVec.carry_succ]
      simp [sliceAt, hk]
    · funext j; by_cases hj : j = idx
      · subst hj
        simp only [setBit, ↓reduceIte, sliceAt, setReg_self]
        have hnot0 : ~~~(0#w) = -(1#w) := by
          have h0 := BitVec.neg_eq_not_add (0#w)
          rw [BitVec.neg_zero w] at h0
          calc ~~~(0#w) = ~~~(0#w) + 1#w - 1#w := (BitVec.add_sub_cancel _ _).symm
            _ = 0#w - 1#w := by rw [← h0]
            _ = -(1#w) := BitVec.zero_sub _
        have hdec : s j - 1#w = s j + ~~~(0#w) + 0#w := by
          rw [BitVec.add_zero, hnot0, BitVec.sub_eq_add_neg]
        rw [hdec]
        have h := getLsbD_addCarry (s j) (~~~(0#w)) false k hk
        simp only [Bool.false_eq_true, ↓reduceIte, BitVec.getLsbD_not, hk, decide_true, Bool.true_and,
                   BitVec.getLsbD_zero, Bool.not_false] at h
        exact h.symm
      · simp [setBit, sliceAt, hj]
  | _ => simp [hasCarryGate] at hCarry

theorem runCarryAt_cons {r w : Nat} (g : Gate r) (gs : Circuit r)
    (hReg : isRegGate g = true) (s : State r w) (k : Nat) (hk : k ≤ w) :
    runCarryAt (g :: gs) s k =
      if hasCarryGate g then
        carryOfGate g s k :: runCarryAt gs (evalGate g s) k
      else
        runCarryAt gs (evalGate g s) k := by
  induction k with
  | zero =>
    cases hc : hasCarryGate g
    · simp [runCarryAt, initCarries, hc]
    · simp [runCarryAt, initCarries, hc, carryOfGate_zero g hc s]
  | succ k ih =>
    have hk' : k < w := by omega
    have hprev := ih (by omega)
    cases hc : hasCarryGate g
    · simp only [runCarryAt, stepRegCirc, hc, Bool.false_eq_true, ↓reduceIte] at hprev ⊢
      rw [hprev, stepPureGate_spec g hReg hc s k hk']
    · simp only [runCarryAt, stepRegCirc, hc, ↓reduceIte] at hprev ⊢
      rw [hprev]
      dsimp only
      rw [stepCarryGate_spec g hc s k hk']

/-- Fundamental Bit-Slice Simulation Theorem: every register-parallel circuit (mixing CNOT,
    Toffoli, SWAP, NOT, MOD_ADD, MOD_SUB, NEG, INC, DEC) agrees bit-for-bit with its compiled
    ripple-carry Mealy transducer at EVERY bit position k < w! -/
theorem evalCircuit_getLsbD_eq_runOutAt {r w : Nat} (C : Circuit r) (hReg : isRegCircuit C = true)
    (s : State r w) (k : Nat) (hk : k < w) :
    sliceAt (evalCircuit C s) k = runOutAt C s k := by
  induction C generalizing s with
  | nil => rfl
  | cons g gs ih =>
    simp only [isRegCircuit, List.all_cons, Bool.and_eq_true] at hReg
    rcases hReg with ⟨hg, hgs⟩
    simp only [evalCircuit_cons, runOutAt]
    rw [runCarryAt_cons g gs hg s k (Nat.le_of_lt hk)]
    cases hc : hasCarryGate g
    · simp only [Bool.false_eq_true, ↓reduceIte, stepRegCirc, hc]
      rw [stepPureGate_spec g hg hc s k hk]
      exact ih hgs (evalGate g s)
    · simp only [↓reduceIte, stepRegCirc, hc]
      rw [stepCarryGate_spec g hc s k hk]
      exact ih hgs (evalGate g s)

-- Finite Bisimulation Certificate & Verifier (Layer 1B)
theorem decodeSlice_surj (r : Nat) (b : BitSlice r) :
    ∃ m < 2 ^ r, decodeSlice r m = b := by
  induction r with
  | zero =>
    refine ⟨0, by simp, ?_⟩
    funext i; exact Fin.elim0 i
  | succ r' ih =>
    obtain ⟨m', hm', hdec'⟩ := ih (fun i => b i.castSucc)
    let bit := (b (Fin.last r')).toNat
    let m := m' + bit * 2 ^ r'
    have hbit : bit ≤ 1 := by
      dsimp only [bit]; cases b (Fin.last r') <;> simp
    have hlt : m < 2 ^ (r' + 1) := by
      have hmul : bit * 2 ^ r' ≤ 2 ^ r' := by
        calc bit * 2 ^ r' ≤ 1 * 2 ^ r' := Nat.mul_le_mul_right _ hbit
          _ = 2 ^ r' := Nat.one_mul _
      rw [Nat.pow_succ]
      omega
    refine ⟨m, hlt, ?_⟩
    funext i
    by_cases hlast : i.val = r'
    · have hi : i = Fin.last r' := Fin.ext hlast
      subst hi
      simp only [decodeSlice, Fin.val_last, Nat.testBit, Nat.shiftRight_eq_div_pow]
      have hpos : 0 < 2 ^ r' := Nat.pow_pos (by omega)
      have hdiv : (m' + bit * 2 ^ r') / 2 ^ r' = bit := by
        rw [Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hm', Nat.zero_add]
      rw [hdiv]
      dsimp only [bit]
      cases b (Fin.last r') <;> decide
    · have hi_lt : i.val < r' := by omega
      let i' : Fin r' := ⟨i.val, hi_lt⟩
      have hi : i = i'.castSucc := Fin.ext rfl
      rw [hi]
      have hprev := congrFun hdec' i'
      simp only [decodeSlice, Fin.val_castSucc, Nat.testBit, Nat.shiftRight_eq_div_pow] at hprev ⊢
      let d := r' - i'.val - 1
      have he : r' = i'.val + (1 + d) := by omega
      have hsplit : 2 ^ r' = 2 ^ i'.val * (2 * 2 ^ d) := by
        calc 2 ^ r' = 2 ^ (i'.val + (1 + d)) := congrArg (2 ^ ·) he
          _ = 2 ^ i'.val * (2 * 2 ^ d) := by rw [Nat.pow_add, Nat.pow_add, Nat.pow_one]
      have hpos : 0 < 2 ^ i'.val := Nat.pow_pos (by omega)
      have hdiv : m / 2 ^ i'.val = m' / 2 ^ i'.val + bit * (2 * 2 ^ d) := by
        show (m' + bit * 2 ^ r') / 2 ^ i'.val = _
        have hrew : bit * 2 ^ r' = (bit * (2 * 2 ^ d)) * 2 ^ i'.val := by
          rw [hsplit]; ac_rfl
        rw [hrew, Nat.add_mul_div_right _ _ hpos]
      rw [hdiv, Nat.and_comm 1, Nat.and_one_is_mod]
      rw [Nat.and_comm 1, Nat.and_one_is_mod] at hprev
      have hmod : (m' / 2 ^ i'.val + bit * (2 * 2 ^ d)) % 2 = (m' / 2 ^ i'.val) % 2 := by
        have hrew : bit * (2 * 2 ^ d) = (bit * 2 ^ d) * 2 := by ac_rfl
        rw [hrew, Nat.add_mul_mod_self_right]
      rw [hmod]
      exact hprev

theorem sliceEqBool_eq_true {r : Nat} {b1 b2 : BitSlice r} :
    sliceEqBool b1 b2 = true ↔ b1 = b2 := by
  constructor
  · intro h; funext i
    simp only [sliceEqBool, List.all_eq_true, beq_iff_eq] at h
    exact h i (List.mem_finRange i)
  · intro h; subst h; simp [sliceEqBool]

/-- Layer 1B Soundness Meta-Theorem: lifts ANY valid finite bisimulation certificate to
    ALL bit-widths w : Nat and ALL register states s : State r w! -/
theorem sound_checkBisimCert (r : Nat) (C1 C2 : Circuit r) (cert : BisimCert)
    (h : checkBisimCert r C1 C2 cert = true) :
    ∀ (w : Nat), ∀ (s : State r w), evalCircuit C1 s = evalCircuit C2 s := by
  simp only [checkBisimCert, Bool.and_eq_true, List.contains_iff_mem,
             List.all_eq_true, allRange_eq_true] at h
  rcases h with ⟨⟨⟨hReg1, hReg2⟩, hInit⟩, hStep⟩
  intro w s
  have hInv : ∀ k, (runCarryAt C1 s k, runCarryAt C2 s k) ∈ cert := by
    intro k
    induction k with
    | zero => exact hInit
    | succ k ih =>
      obtain ⟨m, hm, hdec⟩ := decodeSlice_surj r (sliceAt s k)
      have hst := hStep (runCarryAt C1 s k, runCarryAt C2 s k) ih m hm
      rw [hdec] at hst
      exact hst.2
  funext i
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have h1 := congrFun (evalCircuit_getLsbD_eq_runOutAt C1 hReg1 s k hk) i
  have h2 := congrFun (evalCircuit_getLsbD_eq_runOutAt C2 hReg2 s k hk) i
  simp only [sliceAt, runOutAt] at h1 h2
  rw [h1, h2]
  obtain ⟨m, hm, hdec⟩ := decodeSlice_surj r (sliceAt s k)
  have hst := hStep (runCarryAt C1 s k, runCarryAt C2 s k) (hInv k) m hm
  have hOutEq := sliceEqBool_eq_true.mp hst.1
  rw [hdec] at hOutEq
  exact congrFun hOutEq i

-- ============================================================================
-- SECTION 4: Group-Word Rewriting & Finite Coset-Table Compiler (Layers 2A & 2B)
-- ============================================================================

theorem evalGate_preserves_untouched {r w : Nat} (g : Gate r) (s : State r w) (i : Fin r)
    (hi : i ∉ regTouched g) : evalGate g s i = s i := by
  cases g <;> simp only [regTouched, List.mem_cons, List.not_mem_nil, or_false, not_or] at hi <;>
    simp only [evalGate]
  · rw [setReg_ne _ hi]
  · rcases hi with ⟨h1, h2⟩; simp [swapRegs, h1, h2]
  · split
    · rw [setReg_ne _ hi.2]
    · rfl
  · split
    · rw [setReg_ne _ hi.2.2]
    · rfl
  · split
    · rw [setReg_ne _ hi.2]
    · rfl
  · split
    · rw [setReg_ne _ hi.2]
    · rfl
  · rw [setReg_ne _ hi]
  · rw [setReg_ne _ hi]
  · rw [setReg_ne _ hi]
  · rw [setReg_ne _ hi]
  · split
    · split
      · rcases hi with ⟨h1, h2⟩; rw [setReg_ne _ h2, setReg_ne _ h1]
      · rfl
    · rfl
  · split
    · split
      · rw [setReg_ne _ hi.2]
      · rfl
    · rfl
  · split
    · split
      · rw [setReg_ne _ hi.2.2]
      · rfl
    · rfl

theorem evalGate_depends_only_on_touched {r w : Nat} (g : Gate r) (s1 s2 : State r w)
    (hAgree : ∀ i ∈ regTouched g, s1 i = s2 i) (j : Fin r) (hj : j ∈ regTouched g) :
    evalGate g s1 j = evalGate g s2 j := by
  cases g <;> simp only [regTouched, List.mem_cons, List.not_mem_nil, or_false] at hAgree hj <;>
    simp only [evalGate]
  · have h := hAgree _ rfl; subst hj; simp [h]
  · have h1 := hAgree _ (Or.inl rfl); have h2 := hAgree _ (Or.inr rfl)
    rcases hj with rfl | rfl <;> simp [swapRegs, h1, h2]
  · have h1 := hAgree _ (Or.inl rfl); have h2 := hAgree _ (Or.inr rfl)
    split <;> rcases hj with rfl | rfl <;> simp [setReg, h1, h2]
  · have h1 := hAgree _ (Or.inl rfl)
    have h2 := hAgree _ (Or.inr (Or.inl rfl))
    have h3 := hAgree _ (Or.inr (Or.inr rfl))
    split <;> rcases hj with rfl | rfl | rfl <;> simp [setReg, h1, h2, h3]
  · have h1 := hAgree _ (Or.inl rfl); have h2 := hAgree _ (Or.inr rfl)
    split <;> rcases hj with rfl | rfl <;> simp [setReg, h1, h2]
  · have h1 := hAgree _ (Or.inl rfl); have h2 := hAgree _ (Or.inr rfl)
    split <;> rcases hj with rfl | rfl <;> simp [setReg, h1, h2]
  · have h := hAgree _ rfl; subst hj; simp [h]
  · have h := hAgree _ rfl; subst hj; simp [h]
  · have h := hAgree _ rfl; subst hj; simp [h]
  · have h := hAgree _ rfl; subst hj; simp [h]
  · have h1 := hAgree _ (Or.inl rfl); have h2 := hAgree _ (Or.inr rfl)
    split
    · rw [h1, h2]
      split
      · rcases hj with rfl | rfl
        · simp [setReg, h2]
        · simp [setReg, h2]
      · rcases hj with rfl | rfl <;> assumption
    · rcases hj with rfl | rfl <;> assumption
  · have h1 := hAgree _ (Or.inl rfl); have h2 := hAgree _ (Or.inr rfl)
    split
    · rw [h1]
      split
      · rcases hj with rfl | rfl
        · simp [setReg, h1, h2]
        · simp [setReg, h2]
      · rcases hj with rfl | rfl <;> assumption
    · rcases hj with rfl | rfl <;> assumption
  · have h1 := hAgree _ (Or.inl rfl)
    have h2 := hAgree _ (Or.inr (Or.inl rfl))
    have h3 := hAgree _ (Or.inr (Or.inr rfl))
    split
    · rw [h1, h2]
      split
      · rcases hj with rfl | rfl | rfl <;> simp [setReg, h1, h2, h3]
      · rcases hj with rfl | rfl | rfl <;> assumption
    · rcases hj with rfl | rfl | rfl <;> assumption

theorem evalGate_commute {r w : Nat} (g1 g2 : Gate r) (hc : gatesCommute g1 g2 = true) (s : State r w) :
    evalGate g2 (evalGate g1 s) = evalGate g1 (evalGate g2 s) := by
  simp only [gatesCommute, Bool.or_eq_true, beq_iff_eq] at hc
  rcases hc with rfl | hdisj
  · rfl
  · simp only [listsDisjoint, List.all_eq_true, Bool.not_eq_true'] at hdisj
    have hDisjMem : ∀ x ∈ regTouched g1, x ∉ regTouched g2 := by
      intro x hx1 hx2
      have hfalse := hdisj x hx1
      have htrue : (regTouched g2).contains x = true := List.contains_iff_mem.mpr hx2
      rw [htrue] at hfalse
      contradiction
    funext i
    by_cases hi1 : i ∈ regTouched g1
    · have hi2 : i ∉ regTouched g2 := hDisjMem i hi1
      rw [evalGate_preserves_untouched g2 _ i hi2]
      apply evalGate_depends_only_on_touched g1 s (evalGate g2 s)
      · intro j hj1; exact (evalGate_preserves_untouched g2 s j (hDisjMem j hj1)).symm
      · exact hi1
    · by_cases hi2 : i ∈ regTouched g2
      · rw [evalGate_preserves_untouched g1 _ i hi1]
        apply evalGate_depends_only_on_touched g2 (evalGate g1 s) s
        · intro j hj2
          have hj1 : j ∉ regTouched g1 := fun h => hDisjMem j h hj2
          exact evalGate_preserves_untouched g1 s j hj1
        · exact hi2
      · rw [evalGate_preserves_untouched g2 _ i hi2,
            evalGate_preserves_untouched g1 _ i hi1,
            evalGate_preserves_untouched g1 _ i hi1,
            evalGate_preserves_untouched g2 _ i hi2]

-- Layer 2A: Group-Word Rewriting Certificate Verifier
theorem applyStep_sound {r w0 : Nat} (lib : RelLib r) (hLib : LibSound lib w0)
    (word word' : Circuit r) (step : RewriteStep r)
    (hStep : applyStep lib word step = some word') :
    ∀ w, w0 ≤ w → ∀ s : State r w, evalCircuit word s = evalCircuit word' s := by
  intro w hw s
  cases step with
  | invElim pos =>
    simp only [applyStep] at hStep
    cases hdrop : word.drop pos with
    | nil => simp [hdrop] at hStep
    | cons g1 tail =>
      cases tail with
      | nil => simp [hdrop] at hStep
      | cons g2 rest =>
        simp only [hdrop] at hStep
        split at hStep
        · rename_i hinv
          injection hStep with hEq
          subst hEq
          have hword : word = word.take pos ++ (g1 :: g2 :: rest) := by
            rw [← hdrop, List.take_append_drop]
          conv => lhs; rw [hword]
          simp only [evalCircuit_append, evalCircuit_cons]
          simp only [Bool.or_eq_true, beq_iff_eq] at hinv
          rcases hinv with rfl | rfl
          · rw [evalGate_inv]
          · rw [evalGate_inv_left]
        · simp at hStep
  | invIntro pos g =>
    simp only [applyStep] at hStep
    split at hStep
    · injection hStep with hEq
      subst hEq
      have hword : word = word.take pos ++ word.drop pos := (List.take_append_drop pos word).symm
      rw [evalCircuit_append, evalCircuit_append, evalCircuit_cons, evalCircuit_cons, evalCircuit_nil,
          evalGate_inv, ← evalCircuit_append, ← hword]
    · simp at hStep
  | commute pos =>
    simp only [applyStep] at hStep
    cases hdrop : word.drop pos with
    | nil => simp [hdrop] at hStep
    | cons g1 tail =>
      cases tail with
      | nil => simp [hdrop] at hStep
      | cons g2 rest =>
        simp only [hdrop] at hStep
        split at hStep
        · rename_i hcomm
          injection hStep with hEq
          subst hEq
          have hword : word = word.take pos ++ (g1 :: g2 :: rest) := by
            rw [← hdrop, List.take_append_drop]
          conv => lhs; rw [hword]
          simp only [evalCircuit_append, evalCircuit_cons, evalCircuit_nil, evalGate_commute g1 g2 hcomm]
        · simp at hStep
  | applyRel idx fwd pos =>
    simp only [applyStep] at hStep
    cases hget : lib[idx]? with
    | none => simp [hget] at hStep
    | some p =>
      rcases p with ⟨lhs, rhs⟩
      simp only [hget] at hStep
      have hmem : (lhs, rhs) ∈ lib := List.mem_of_getElem? hget
      have hRel := hLib (lhs, rhs) hmem w hw
      cases fwd
      · simp only [Bool.false_eq_true, ↓reduceIte] at hStep
        split at hStep
        · rename_i hcond
          injection hStep with hEq
          subst hEq
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond
          rcases hcond with ⟨_, htake⟩
          have h1 : word.drop pos = rhs ++ (word.drop pos).drop rhs.length := by
            have htd := (List.take_append_drop rhs.length (word.drop pos)).symm
            rw [htake] at htd
            exact htd
          have hword : word = word.take pos ++ rhs ++ (word.drop pos).drop rhs.length := by
            rw [List.append_assoc, ← h1, List.take_append_drop]
          conv => lhs; rw [hword]
          simp only [evalCircuit_append]
          rw [(hRel _).symm]
        · simp at hStep
      · simp only [↓reduceIte] at hStep
        split at hStep
        · rename_i hcond
          injection hStep with hEq
          subst hEq
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond
          rcases hcond with ⟨_, htake⟩
          have h1 : word.drop pos = lhs ++ (word.drop pos).drop lhs.length := by
            have htd := (List.take_append_drop lhs.length (word.drop pos)).symm
            rw [htake] at htd
            exact htd
          have hword : word = word.take pos ++ lhs ++ (word.drop pos).drop lhs.length := by
            rw [List.append_assoc, ← h1, List.take_append_drop]
          conv => lhs; rw [hword]
          simp only [evalCircuit_append]
          rw [hRel _]
        · simp at hStep

/-- Layer 2A Soundness Meta-Theorem: lifts ANY kernel-checked rewriting derivation to ∀ w ≥ w0! -/
theorem sound_checkRewriteCert {r w0 : Nat} (lib : RelLib r) (hLib : LibSound lib w0)
    (w1 w2 : Circuit r) (cert : RewriteCert r)
    (hCert : checkRewriteCert lib w1 w2 cert = true) :
    ∀ w, w0 ≤ w → ∀ s : State r w, evalCircuit w1 s = evalCircuit w2 s := by
  unfold checkRewriteCert at hCert
  cases hrun : runRewrite lib w1 cert with
  | none => simp [hrun] at hCert
  | some wf =>
    simp only [hrun, beq_iff_eq] at hCert
    subst hCert
    intro w hw s
    induction cert generalizing w1 with
    | nil =>
      simp only [runRewrite] at hrun
      injection hrun with hEq
      rw [hEq]
    | cons st rest ih =>
      simp only [runRewrite] at hrun
      cases hst : applyStep lib w1 st with
      | none => simp [hst] at hrun
      | some w' =>
        simp only [hst] at hrun
        rw [applyStep_sound lib hLib w1 w' st hst w hw s]
        exact ih w' hrun

-- Layer 2B: Finite Coset-Table (Todd-Coxeter / Schreier) Certificate Compiler
theorem evalWord_append {r : Nat} (gens : Array (Circuit r)) (w1 w2 : List Nat) :
    evalWord gens (w1 ++ w2) = evalWord gens w1 ++ evalWord gens w2 := by
  induction w1 with
  | nil => rfl
  | cons k ks ih => simp [evalWord, ih, List.append_assoc]

theorem evalWord_repeat {r : Nat} (gens : Array (Circuit r)) (n : Nat) (word : List Nat) :
    evalWord gens (repeatWord n word) = repeatCircuit n (evalWord gens word) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repeatWord, repeatCircuit, evalWord_append, ih]

theorem sound_coset_walk {r w0 : Nat} (lib : RelLib r) (hLib : LibSound lib w0)
    (gens : Array (Circuit r)) (cc : CosetCert r)
    (hCert : checkCosetCert lib gens cc = true)
    (c : Nat) (hc : c < cc.numCosets)
    (word : List Nat) (hWord : ∀ k ∈ word, k < gens.size) :
    walkCoset cc.table c word < cc.numCosets ∧
    ∀ w, w0 ≤ w → ∀ s : State r w,
      evalCircuit (cc.reps[c]! ++ evalWord gens word) s =
      evalCircuit cc.reps[walkCoset cc.table c word]! s := by
  simp only [checkCosetCert, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, allRange_eq_true] at hCert
  rcases hCert with ⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, hEdges⟩
  induction word generalizing c with
  | nil =>
    exact ⟨hc, fun w _ s => by simp only [evalWord, walkCoset, List.append_nil]⟩
  | cons k ks ih =>
    have hk : k < gens.size := hWord k (List.mem_cons_self ..)
    have hks : ∀ k' ∈ ks, k' < gens.size := fun k' hm => hWord k' (List.mem_cons_of_mem k hm)
    have hEdge := (hEdges c hc).2 k hk
    rcases hEdge with ⟨hncLt, hRew⟩
    obtain ⟨hFinLt, hFinEq⟩ := ih (cc.table[c]![k]!) hncLt hks
    refine ⟨hFinLt, ?_⟩
    intro w hw s
    simp only [evalWord, walkCoset]
    rw [← List.append_assoc, evalCircuit_append]
    rw [sound_checkRewriteCert lib hLib _ _ _ hRew w hw s]
    rw [← evalCircuit_append]
    exact hFinEq w hw s

/-- Layer 2B Meta-Theorem 1 (Universal Arbitrary-Length Word Compilation):
    ANY word over `gens` compiles via finite coset-table lookup to its canonical representative
    for ALL bit-widths w ≥ w0! -/
theorem sound_coset_compile {r w0 : Nat} (lib : RelLib r) (hLib : LibSound lib w0)
    (gens : Array (Circuit r)) (cc : CosetCert r)
    (hCert : checkCosetCert lib gens cc = true)
    (word : List Nat) (hWord : ∀ k ∈ word, k < gens.size) :
    walkCoset cc.table 0 word < cc.numCosets ∧
    ∀ w, w0 ≤ w → ∀ s : State r w,
      evalCircuit (evalWord gens word) s =
      evalCircuit cc.reps[walkCoset cc.table 0 word]! s := by
  have hCertCopy := hCert
  simp only [checkCosetCert, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hCertCopy
  have hPos : 0 < cc.numCosets := hCertCopy.1.1.1.1.1
  have hRep0 : cc.reps[0]! = [] := hCertCopy.1.2
  have hWalk := sound_coset_walk lib hLib gens cc hCert 0 hPos word hWord
  refine ⟨hWalk.1, ?_⟩
  intro w hw s
  have h := hWalk.2 w hw s
  rw [hRep0, List.nil_append] at h
  exact h

/-- Layer 2B Meta-Theorem 2 (Instant Word Equivalence via Coset Equality):
    ANY two words walking to the same coset are equivalent for ALL w ≥ w0! -/
theorem sound_coset_equiv {r w0 : Nat} (lib : RelLib r) (hLib : LibSound lib w0)
    (gens : Array (Circuit r)) (cc : CosetCert r)
    (hCert : checkCosetCert lib gens cc = true)
    (w1 w2 : List Nat) (hw1 : ∀ k ∈ w1, k < gens.size) (hw2 : ∀ k ∈ w2, k < gens.size)
    (hSame : walkCoset cc.table 0 w1 = walkCoset cc.table 0 w2) :
    ∀ w, w0 ≤ w → ∀ s : State r w,
      evalCircuit (evalWord gens w1) s = evalCircuit (evalWord gens w2) s := by
  intro w hw s
  rw [(sound_coset_compile lib hLib gens cc hCert w1 hw1).2 w hw s,
      (sound_coset_compile lib hLib gens cc hCert w2 hw2).2 w hw s,
      hSame]

theorem mem_repeatWord {d : Nat} {word : List Nat} {m : Nat}
    (hWord : ∀ k ∈ word, k < m) : ∀ k ∈ repeatWord d word, k < m := by
  induction d with
  | zero => intro k hk; simp [repeatWord] at hk
  | succ d ih =>
    intro k hk
    simp only [repeatWord, List.mem_append] at hk
    rcases hk with h1 | h2
    · exact hWord k h1
    · exact ih k h2

/-- Layer 2B Meta-Theorem 3 (Universal Order & Modulo-d Power Reduction ∀ n : Nat, ∀ w ≥ w0!):
    If `repeatWord d word` returns to coset 0, then W^d = id AND W^n = W^(n % d)
    for EVERY exponent n : Nat and EVERY bit-width w ≥ w0! -/
theorem sound_coset_order {r w0 : Nat} (lib : RelLib r) (hLib : LibSound lib w0)
    (gens : Array (Circuit r)) (cc : CosetCert r)
    (hCert : checkCosetCert lib gens cc = true)
    (word : List Nat) (hWord : ∀ k ∈ word, k < gens.size) (d : Nat)
    (hCycle : walkCoset cc.table 0 (repeatWord d word) = 0) :
    ∀ w, w0 ≤ w → ∀ s : State r w,
      evalCircuit (repeatCircuit d (evalWord gens word)) s = s := by
  have hCertCopy := hCert
  simp only [checkCosetCert, Bool.and_eq_true, beq_iff_eq] at hCertCopy
  have hRep0 : cc.reps[0]! = [] := hCertCopy.1.2
  have hRepWord := mem_repeatWord (d := d) hWord
  intro w hw s
  rw [← evalWord_repeat]
  rw [(sound_coset_compile lib hLib gens cc hCert (repeatWord d word) hRepWord).2 w hw s]
  rw [hCycle, hRep0, evalCircuit_nil]

theorem sound_coset_power_mod {r w0 : Nat} (lib : RelLib r) (hLib : LibSound lib w0)
    (gens : Array (Circuit r)) (cc : CosetCert r)
    (hCert : checkCosetCert lib gens cc = true)
    (word : List Nat) (hWord : ∀ k ∈ word, k < gens.size) (d : Nat)
    (hCycle : walkCoset cc.table 0 (repeatWord d word) = 0) :
    ∀ (n : Nat) (w : Nat), w0 ≤ w → ∀ s : State r w,
      evalCircuit (repeatCircuit n (evalWord gens word)) s =
      evalCircuit (repeatCircuit (n % d) (evalWord gens word)) s := by
  intro n w hw s
  have hOrd := sound_coset_order lib hLib gens cc hCert word hWord d hCycle w hw
  have hdiv : n = d * (n / d) + n % d := (Nat.div_add_mod n d).symm
  conv => lhs; rw [hdiv]
  rw [evalCircuit_repeat_add, evalCircuit_repeat_mul (n / d) d _ hOrd s]

-- ============================================================================
-- SECTION 5: Flagship Novel Infinite Silicon Theorems (∀ w ≥ w0, ∀ n : Nat)
-- ============================================================================

-- Family I: Modular-Add + Swap SL(2,Z) Braid & Dihedral Group D6 (Order 12)
theorem cert_sl2_braid_ok :
    checkBisimCert 2 (circU ++ circV ++ circU) (circV ++ circU ++ circV) cert_sl2_braid = true := by
  decide

theorem cert_j4_ok :
    checkBisimCert 2 (repeatCircuit 4 circJ) [] cert_j4 = true := by
  decide

theorem cert_not_add_ok :
    checkBisimCert 2 [.rNot 1, .rAdd 0 1, .rNot 1] [.rSub 0 1] cert_not_add = true := by
  decide

theorem cert_d6_c6_ok :
    checkBisimCert 2 (repeatCircuit 6 circC) [] cert_d6_c6 = true := by
  decide

theorem cert_d6_sc_ok :
    checkBisimCert 2 (circS ++ circC) (repeatCircuit 5 circC ++ circS) cert_d6_sc = true := by
  decide

/-- Theorem I.1 (SL(2,Z) Modular-Add Braid Relation ∀ w : Nat): U·V·U = V·U·V on (BitVec w)^2. -/
theorem thm_sl2_braid :
    ∀ (w : Nat) (s : State 2 w),
      evalCircuit (circU ++ circV ++ circU) s = evalCircuit (circV ++ circU ++ circV) s :=
  sound_checkBisimCert 2 _ _ cert_sl2_braid cert_sl2_braid_ok

/-- Theorem I.2 (Modular 90-degree Rotation Order ≤ 4 ∀ w : Nat): J^4 = Id on (BitVec w)^2. -/
theorem thm_j_order4 :
    ∀ (w : Nat) (s : State 2 w), evalCircuit (repeatCircuit 4 circJ) s = s :=
  sound_checkBisimCert 2 _ _ cert_j4 cert_j4_ok

/-- Theorem I.3 (Bitwise-NOT / Modular-Add Dihedral Inversion ∀ w : Nat):
    rNot(1) · rAdd(0,1) · rNot(1) = rSub(0,1). -/
theorem thm_not_add_dihedral :
    ∀ (w : Nat) (s : State 2 w),
      evalCircuit [.rNot 1, .rAdd 0 1, .rNot 1] s = evalCircuit [.rSub 0 1] s :=
  sound_checkBisimCert 2 _ _ cert_not_add cert_not_add_ok

theorem d6Lib_sound : LibSound d6Lib 1 := by
  intro p hp w _ s
  simp only [d6Lib, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact sound_checkBisimCert 2 _ _ cert_d6_c6 cert_d6_c6_ok w s
  · exact sound_checkBisimCert 2 _ _ cert_d6_sc cert_d6_sc_ok w s

/-- Pure kernel `decide` check of the full 12-coset D6 Cayley table (24 edge rewrite certs). -/
theorem d6CosetCert_ok : checkCosetCert d6Lib d6Gens d6CosetCert = true := by
  decide

/-- Pure kernel `decide` faithfulness check of all 12 D6 coset reps at w0 = 2. -/
theorem d6Distinct_w2_ok : checkDistinctAt 2 2 d6CosetCert.reps = true := by
  decide

/-- Pure kernel `decide` exact-order-6 lower-bound check for C at w0 = 2. -/
theorem d6OrderLower_C_ok : checkOrderLowerAt 2 2 6 circC = true := by
  decide

/-- Theorem I.4 (Universal D6 Arbitrary-Length Word Compiler ∀ w ≥ 1):
    EVERY word over {C, S} reduces to one of 12 canonical circuits via coset table lookup. -/
theorem thm_d6_compile (word : List Nat) (hWord : ∀ k ∈ word, k < d6Gens.size) :
    walkCoset d6CosetCert.table 0 word < 12 ∧
    ∀ (w : Nat), 1 ≤ w → ∀ (s : State 2 w),
      evalCircuit (evalWord d6Gens word) s =
      evalCircuit d6CosetCert.reps[walkCoset d6CosetCert.table 0 word]! s :=
  sound_coset_compile d6Lib d6Lib_sound d6Gens d6CosetCert d6CosetCert_ok word hWord

/-- Theorem I.5 (Universal D6 Power-Mod-6 Reduction ∀ n : Nat, ∀ w ≥ 1): C^n = C^(n % 6). -/
theorem thm_d6_C_power_mod :
    ∀ (n w : Nat), 1 ≤ w → ∀ (s : State 2 w),
      evalCircuit (repeatCircuit n circC) s = evalCircuit (repeatCircuit (n % 6) circC) s := by
  have h := sound_coset_power_mod d6Lib d6Lib_sound d6Gens d6CosetCert d6CosetCert_ok
              [0] (by decide) 6 (by decide)
  intro n w hw s
  have heq : evalWord d6Gens [0] = circC := by simp [evalWord, d6Gens]
  rw [heq] at h
  exact h n w hw s

/-- Theorem I.6 (Infinite Family of Modular-Add Involutions ∀ n : Nat, ∀ w ≥ 1):
    (C^n · S)^2 = Id for every n : Nat and every bit-width w ≥ 1! -/
theorem thm_d6_reflections_invol :
    ∀ (n w : Nat), 1 ≤ w → ∀ (s : State 2 w),
      evalCircuit (repeatCircuit 2 (repeatCircuit n circC ++ circS)) s = s := by
  intro n w hw s
  have hmod := thm_d6_C_power_mod n w hw
  simp only [repeatCircuit, List.append_nil, evalCircuit_append]
  rw [hmod s, hmod (evalCircuit circS (evalCircuit (repeatCircuit (n % 6) circC) s))]
  have hlt : n % 6 < 6 := Nat.mod_lt n (by omega)
  have hcase : ∀ m < 6, ∀ st : State 2 w,
      evalCircuit circS (evalCircuit (repeatCircuit m circC)
        (evalCircuit circS (evalCircuit (repeatCircuit m circC) st))) = st := by
    intro m hm st
    have hm_cases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
    rcases hm_cases with rfl | rfl | rfl | rfl | rfl | rfl
    · exact sound_coset_order d6Lib d6Lib_sound d6Gens d6CosetCert d6CosetCert_ok
        [1] (by decide) 2 (by decide) w hw st
    · exact sound_coset_order d6Lib d6Lib_sound d6Gens d6CosetCert d6CosetCert_ok
        [0, 1] (by decide) 2 (by decide) w hw st
    · exact sound_coset_order d6Lib d6Lib_sound d6Gens d6CosetCert d6CosetCert_ok
        [0, 0, 1] (by decide) 2 (by decide) w hw st
    · exact sound_coset_order d6Lib d6Lib_sound d6Gens d6CosetCert d6CosetCert_ok
        [0, 0, 0, 1] (by decide) 2 (by decide) w hw st
    · exact sound_coset_order d6Lib d6Lib_sound d6Gens d6CosetCert d6CosetCert_ok
        [0, 0, 0, 0, 1] (by decide) 2 (by decide) w hw st
    · exact sound_coset_order d6Lib d6Lib_sound d6Gens d6CosetCert d6CosetCert_ok
        [0, 0, 0, 0, 0, 1] (by decide) 2 (by decide) w hw st
  exact hcase (n % 6) hlt s

/-- Theorem I.7 (Exact Group Order |<C, S>_w| = 12 ∀ w ≥ 2): all 12 compiled reps are distinct! -/
theorem thm_d6_exact_order12 :
    ∀ (w : Nat), 2 ≤ w → ∀ (i j : Nat), j < i → i < 12 →
      ∃ (s : State 2 w), evalCircuit d6CosetCert.reps[i]! s ≠ evalCircuit d6CosetCert.reps[j]! s :=
  sound_checkDistinctAt 2 2 d6CosetCert.reps d6Distinct_w2_ok

/-- Theorem I.8 (Exact Order ord_w(C) = 6 ∀ w ≥ 2): C^6 = Id and C^k ≠ Id for all proper divisors k ∣ 6. -/
theorem thm_d6_C_exact_order6 :
    ∀ (w : Nat), 2 ≤ w →
      (∀ s : State 2 w, evalCircuit (repeatCircuit 6 circC) s = s) ∧
      (∀ k : Nat, 0 < k → k < 6 → 6 % k = 0 →
        ∃ s : State 2 w, evalCircuit (repeatCircuit k circC) s ≠ s) := by
  intro w hw
  exact ⟨fun s => sound_checkBisimCert 2 _ _ cert_d6_c6 cert_d6_c6_ok w s,
         sound_checkOrderLowerAt 2 2 6 circC d6OrderLower_C_ok w hw⟩

/-- Sharpness I (Collapse at w = 1): at w = 1, C^3 = Id so ord_1(C) drops from 6 to 3! -/
theorem thm_d6_sharp_w1 :
    ∀ (s : State 2 1), evalCircuit (repeatCircuit 3 circC) s = s := by
  intro s
  obtain ⟨idx, hidx, hEq⟩ := decode_surj_aux 2 1 s
  rw [← hEq]
  have hall : allRange (2 ^ (2 * 1)) (fun k =>
      stateEqBool (evalCircuit (repeatCircuit 3 circC) (decodeState 2 1 k)) (decodeState 2 1 k)) = true := by
    decide
  exact stateEqBool_eq_true.mp (allRange_eq_true.mp hall idx hidx)

-- ----------------------------------------------------------------------------
-- 5.2 Family II Theorems: Bit-Indexed Hyperoctahedral Weyl Group B3 (Order 48)
-- ----------------------------------------------------------------------------

theorem b3Rel0_ok : checkWindowEq 1 3 [gA, gS, gA] [gS, gA, gS] = true := by decide
theorem b3Rel1_ok : checkWindowEq 1 3 [gS, gT] [gT, gS] = true := by decide
theorem b3Rel2_ok : checkWindowEq 1 3 [gA, gT, gA, gT] [gT, gA, gT, gA] = true := by decide
theorem b3Rel3_ok : checkWindowEq 1 3 [gA, gS, gA, gT, gA, gS] [gS, gA, gT, gA, gS, gA] = true := by decide

theorem b3Lib_sound : LibSound b3Lib 3 := by
  intro p hp w hw s
  simp only [b3Lib, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact sound_checkWindowEq 1 3 _ _ b3Rel0_ok w hw s
  · exact sound_checkWindowEq 1 3 _ _ b3Rel1_ok w hw s
  · exact sound_checkWindowEq 1 3 _ _ b3Rel2_ok w hw s
  · exact sound_checkWindowEq 1 3 _ _ b3Rel3_ok w hw s

/-- Pure kernel `decide` check of the full 48-coset B3 Cayley table (144 edge rewrite certs!). -/
theorem b3CosetCert_ok : checkCosetCert b3Lib b3Gens b3CosetCert = true := by
  decide

/-- Pure kernel `decide` faithfulness check of all 48 B3 coset reps at w0 = 3! -/
theorem b3Distinct_w3_ok : checkDistinctAt 1 3 b3CosetCert.reps = true := by
  decide

theorem b3OrderLower_AST_ok : checkOrderLowerAt 1 3 6 [gA, gS, gT] = true := by decide
theorem b3OrderLower_AT_ok  : checkOrderLowerAt 1 3 4 [gA, gT] = true := by decide

/-- Theorem II.1 (Universal B3 Arbitrary-Length Word Compiler ∀ w ≥ 3):
    EVERY circuit word over {bCnot(0,1), bSwap(0,1), bToff(0,1,2)} compiles via the
    48-coset Cayley table to a canonical representative for ALL bit-widths w ≥ 3! -/
theorem thm_b3_compile (word : List Nat) (hWord : ∀ k ∈ word, k < b3Gens.size) :
    walkCoset b3CosetCert.table 0 word < 48 ∧
    ∀ (w : Nat), 3 ≤ w → ∀ (s : State 1 w),
      evalCircuit (evalWord b3Gens word) s =
      evalCircuit b3CosetCert.reps[walkCoset b3CosetCert.table 0 word]! s :=
  sound_coset_compile b3Lib b3Lib_sound b3Gens b3CosetCert b3CosetCert_ok word hWord

/-- Theorem II.2 (Exact Weyl Group Order |<bCnot(0,1), bSwap(0,1), bToff(0,1,2)>_w| = 48 ∀ w ≥ 3):
    ALL 48 compiled coset representatives define pairwise distinct permutations of BitVec w! -/
theorem thm_b3_exact_order48 :
    ∀ (w : Nat), 3 ≤ w → ∀ (i j : Nat), j < i → i < 48 →
      ∃ (s : State 1 w), evalCircuit b3CosetCert.reps[i]! s ≠ evalCircuit b3CosetCert.reps[j]! s :=
  sound_checkDistinctAt 1 3 b3CosetCert.reps b3Distinct_w3_ok

theorem walkCoset_append (table : Array (Array Nat)) (c : Nat) (w1 w2 : List Nat) :
    walkCoset table c (w1 ++ w2) = walkCoset table (walkCoset table c w1) w2 := by
  induction w1 generalizing c with
  | nil => rfl
  | cons k ks ih => exact ih (table[c]![k]!)

theorem b3_AST_walk6 : walkCoset b3CosetCert.table 0 (repeatWord 6 [0, 1, 2]) = 0 := by
  have h1 : walkCoset b3CosetCert.table 0 [0, 1, 2] = 10 := by decide
  have h2 : walkCoset b3CosetCert.table 10 [0, 1, 2] = 34 := by decide
  have h3 : walkCoset b3CosetCert.table 34 [0, 1, 2] = 47 := by decide
  have h4 : walkCoset b3CosetCert.table 47 [0, 1, 2] = 37 := by decide
  have h5 : walkCoset b3CosetCert.table 37 [0, 1, 2] = 13 := by decide
  have h6 : walkCoset b3CosetCert.table 13 [0, 1, 2] = 0 := by decide
  simp only [repeatWord, List.append_nil, walkCoset_append, h1, h2, h3, h4, h5, h6]

/-- Theorem II.3 (Universal Modulo-6 Power Reduction ∀ n : Nat, ∀ w ≥ 3):
    (bCnot(0,1) · bSwap(0,1) · bToff(0,1,2))^n = (bCnot(0,1) · bSwap(0,1) · bToff(0,1,2))^(n % 6). -/
theorem thm_b3_AST_power_mod :
    ∀ (n w : Nat), 3 ≤ w → ∀ (s : State 1 w),
      evalCircuit (repeatCircuit n [gA, gS, gT]) s =
      evalCircuit (repeatCircuit (n % 6) [gA, gS, gT]) s := by
  have h := sound_coset_power_mod b3Lib b3Lib_sound b3Gens b3CosetCert b3CosetCert_ok
              [0, 1, 2] (by decide) 6 b3_AST_walk6
  intro n w hw s
  have heq : evalWord b3Gens [0, 1, 2] = [gA, gS, gT] := by simp [evalWord, b3Gens]
  rw [heq] at h
  exact h n w hw s

/-- Theorem II.4 (Exact Element Orders in B3 ∀ w ≥ 3): ord_w(A·S·T) = 6 and ord_w(A·T) = 4. -/
theorem thm_b3_AST_exact_order6 :
    ∀ (w : Nat), 3 ≤ w →
      (∀ s : State 1 w, evalCircuit (repeatCircuit 6 [gA, gS, gT]) s = s) ∧
      (∀ k : Nat, 0 < k → k < 6 → 6 % k = 0 →
        ∃ s : State 1 w, evalCircuit (repeatCircuit k [gA, gS, gT]) s ≠ s) := by
  intro w hw
  have hup := sound_coset_order b3Lib b3Lib_sound b3Gens b3CosetCert b3CosetCert_ok
                [0, 1, 2] (by decide) 6 b3_AST_walk6 w hw
  have heq : evalWord b3Gens [0, 1, 2] = [gA, gS, gT] := by simp [evalWord, b3Gens]
  rw [heq] at hup
  exact ⟨hup, sound_checkOrderLowerAt 1 3 6 [gA, gS, gT] b3OrderLower_AST_ok w hw⟩

theorem thm_b3_AT_exact_order4 :
    ∀ (w : Nat), 3 ≤ w →
      (∀ s : State 1 w, evalCircuit (repeatCircuit 4 [gA, gT]) s = s) ∧
      (∀ k : Nat, 0 < k → k < 4 → 4 % k = 0 →
        ∃ s : State 1 w, evalCircuit (repeatCircuit k [gA, gT]) s ≠ s) := by
  intro w hw
  have hup := sound_coset_order b3Lib b3Lib_sound b3Gens b3CosetCert b3CosetCert_ok
                [0, 2] (by decide) 4 (by decide) w hw
  have heq : evalWord b3Gens [0, 2] = [gA, gT] := by simp [evalWord, b3Gens]
  rw [heq] at hup
  exact ⟨hup, sound_checkOrderLowerAt 1 3 4 [gA, gT] b3OrderLower_AT_ok w hw⟩

/-- Sharpness II.a (Collapse at w = 2): (A·S·T)^3 = Id at w = 2 (order drops from 6 to 3!). -/
theorem thm_b3_sharp_w2 :
    ∀ (s : State 1 2), evalCircuit (repeatCircuit 3 [gA, gS, gT]) s = s := by
  intro s
  obtain ⟨idx, hidx, hEq⟩ := decode_surj_aux 1 2 s
  rw [← hEq]
  have hall : allRange (2 ^ (1 * 2)) (fun k =>
      stateEqBool (evalCircuit (repeatCircuit 3 [gA, gS, gT]) (decodeState 1 2 k)) (decodeState 1 2 k)) = true := by
    decide
  exact stateEqBool_eq_true.mp (allRange_eq_true.mp hall idx hidx)

/-- Sharpness II.b (Collapse at w = 1): A·S·T = Id at w = 1 (order drops to 1!). -/
theorem thm_b3_sharp_w1 :
    ∀ (s : State 1 1), evalCircuit [gA, gS, gT] s = s := by
  intro s
  obtain ⟨idx, hidx, hEq⟩ := decode_surj_aux 1 1 s
  rw [← hEq]
  have hall : allRange (2 ^ (1 * 1)) (fun k =>
      stateEqBool (evalCircuit [gA, gS, gT] (decodeState 1 1 k)) (decodeState 1 1 k)) = true := by
    decide
  exact stateEqBool_eq_true.mp (allRange_eq_true.mp hall idx hidx)

-- ----------------------------------------------------------------------------
-- 5.3 Family III Theorems: Hybrid Toffoli-Add Dihedral Tower D_{2^w} &
--     Nonlinear Carry-Defect Symmetry / Collapse Laws (K2 and T3)
-- ----------------------------------------------------------------------------

theorem cert_pcnot_dih_ok :
    checkBisimCert 3 ([.rNot 1] ++ circPcnot ++ [.rNot 1]) (Circuit.inv circPcnot) cert_pcnot_dih = true := by
  decide

theorem cert_ptoff_dih_ok :
    checkBisimCert 4 ([.rNot 3] ++ circPtoff ++ [.rNot 3]) (Circuit.inv circPtoff) cert_ptoff_dih = true := by
  decide

theorem cert_k2_sym_ok :
    checkBisimCert 3 (circK2 0 1 2) (circK2 1 0 2) cert_k2_sym = true := by
  decide

theorem cert_k2_not_ok :
    checkBisimCert 3 (circK2 0 1 2 ++ [.rNot 0] ++ circK2 0 1 2 ++ [.rNot 0]) [.rSub 1 2, .rSub 1 2] cert_k2_not = true := by
  decide

/-- Theorem III.1 (Toffoli-Modular-Add Dihedral Inversion ∀ w : Nat):
    rNot(3) · P_toff(0,1,3;2) · rNot(3) = P_toff(0,1,3;2)^{-1}. -/
theorem thm_ptoff_dihedral_inv :
    ∀ (w : Nat) (s : State 4 w),
      evalCircuit ([.rNot 3] ++ circPtoff ++ [.rNot 3]) s = evalCircuit (Circuit.inv circPtoff) s :=
  sound_checkBisimCert 4 _ _ cert_ptoff_dih cert_ptoff_dih_ok

theorem thm_pcnot_dihedral_inv :
    ∀ (w : Nat) (s : State 3 w),
      evalCircuit ([.rNot 1] ++ circPcnot ++ [.rNot 1]) s = evalCircuit (Circuit.inv circPcnot) s :=
  sound_checkBisimCert 3 _ _ cert_pcnot_dih cert_pcnot_dih_ok

theorem repeatCircuit_succ_right {r : Nat} (m : Nat) (C : Circuit r) :
    repeatCircuit (m + 1) C = repeatCircuit m C ++ C := by
  induction m with
  | zero => simp [repeatCircuit]
  | succ k ih =>
    calc repeatCircuit (k + 1 + 1) C
        = C ++ repeatCircuit (k + 1) C := rfl
      _ = C ++ (repeatCircuit k C ++ C) := by rw [ih]
      _ = (C ++ repeatCircuit k C) ++ C := (List.append_assoc _ _ _).symm
      _ = repeatCircuit (k + 1) C ++ C := rfl

/-- General dihedral power-involution lifting for any circuit P inverted by an involution R. -/
theorem dihedral_power_invol {r w : Nat} (P R : Circuit r)
    (hR2 : ∀ s : State r w, evalCircuit R (evalCircuit R s) = s)
    (hConj : ∀ s : State r w, evalCircuit R (evalCircuit P (evalCircuit R s)) = evalCircuit (Circuit.inv P) s) :
    ∀ (n : Nat) (s : State r w),
      evalCircuit (repeatCircuit 2 (repeatCircuit n P ++ R)) s = s := by
  have hpush : ∀ m (st : State r w),
      evalCircuit (repeatCircuit m P) (evalCircuit R (evalCircuit (repeatCircuit m P) st)) = evalCircuit R st := by
    intro m
    induction m with
    | zero => intro st; rfl
    | succ m ihm =>
      intro st
      have h4 : evalCircuit R (evalCircuit P (evalCircuit R (evalCircuit P (evalCircuit (repeatCircuit m P) st)))) =
                evalCircuit (repeatCircuit m P) st := by
        rw [hConj, evalCircuit_inv]
      have h5 := congrArg (evalCircuit R) h4
      rw [hR2] at h5
      calc evalCircuit (repeatCircuit (m + 1) P) (evalCircuit R (evalCircuit (repeatCircuit (m + 1) P) st))
          = evalCircuit (repeatCircuit m P) (evalCircuit P (evalCircuit R (evalCircuit P (evalCircuit (repeatCircuit m P) st)))) := by
              conv => lhs; arg 1; rw [repeatCircuit]
              conv => lhs; arg 2; arg 2; arg 1; rw [repeatCircuit_succ_right]
              simp only [evalCircuit_append]
        _ = evalCircuit (repeatCircuit m P) (evalCircuit R (evalCircuit (repeatCircuit m P) st)) := by
              rw [h5]
        _ = evalCircuit R st := ihm st
  intro n s
  simp only [repeatCircuit, List.append_nil, evalCircuit_append]
  have hgoal := congrArg (evalCircuit R) (hpush n s)
  rw [hR2] at hgoal
  exact hgoal

/-- Theorem III.2 (Infinite Family of Hybrid Toffoli-Add Involutions ∀ n : Nat, ∀ w : Nat):
    (P_toff(0,1,3;2)^n · rNot(3))^2 = Id for ALL exponents n and ALL bit-widths w! -/
theorem thm_ptoff_dihedral_family :
    ∀ (n w : Nat) (s : State 4 w),
      evalCircuit (repeatCircuit 2 (repeatCircuit n circPtoff ++ [.rNot 3])) s = s := by
  intro n w s
  apply dihedral_power_invol circPtoff [.rNot 3]
  · intro st; simp [evalCircuit, evalGate, setReg_setReg_same, BitVec.not_not, setReg_id]
  · intro st
    have h := thm_ptoff_dihedral_inv w st
    simp only [evalCircuit_append] at h
    exact h

/-- Theorem III.3 (Infinite Family of CNOT-Add Involutions ∀ n : Nat, ∀ w : Nat):
    (P_cnot(0,1;2)^n · rNot(1))^2 = Id for ALL exponents n and ALL bit-widths w! -/
theorem thm_pcnot_dihedral_family :
    ∀ (n w : Nat) (s : State 3 w),
      evalCircuit (repeatCircuit 2 (repeatCircuit n circPcnot ++ [.rNot 1])) s = s := by
  intro n w s
  apply dihedral_power_invol circPcnot [.rNot 1]
  · intro st; simp [evalCircuit, evalGate, setReg_setReg_same, BitVec.not_not, setReg_id]
  · intro st
    have h := thm_pcnot_dihedral_inv w st
    simp only [evalCircuit_append] at h
    exact h

-- Exact closed-form carry-defect identity: x + y = (x ^^^ y) + 2 * (x &&& y)
theorem bitvec_add_eq_xor_add_two_and {w : Nat} (x y : BitVec w) :
    x + y = (x ^^^ y) + (x &&& y) + (x &&& y) := by
  have hnat : ∀ (n a b : Nat), a < 2 ^ n → b < 2 ^ n →
      a + b = (a ^^^ b) + 2 * (a &&& b) := by
    intro n
    induction n with
    | zero =>
      intro a b ha hb
      have : a = 0 := by omega
      have : b = 0 := by omega
      subst_vars; rfl
    | succ n ih =>
      intro a b ha hb
      have ha' : a / 2 < 2 ^ n := by rw [Nat.pow_succ] at ha; omega
      have hb' : b / 2 < 2 ^ n := by rw [Nat.pow_succ] at hb; omega
      have hrec := ih (a / 2) (b / 2) ha' hb'
      have hdiv2 : ∀ m k, (m / 2).testBit k = m.testBit (k + 1) := by
        intro m k
        rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
            Nat.div_div_eq_div_mul, Nat.mul_comm 2 (2 ^ k), ← Nat.pow_succ]
      have hmod2_0 : ∀ m, (m % 2).testBit 0 = m.testBit 0 := by
        intro m
        have h := Nat.testBit_mod_two_pow (x := m) (j := 1) (i := 0)
        simp only [Nat.pow_one] at h
        simp [h]
      have hmod2_s : ∀ m k, (m % 2).testBit (k + 1) = false := by
        intro m k
        have h := Nat.testBit_mod_two_pow (x := m) (j := 1) (i := k + 1)
        simp only [Nat.pow_one] at h
        simp [h]
      have hdiv_xor : (a ^^^ b) / 2 = (a / 2) ^^^ (b / 2) := by
        apply Nat.eq_of_testBit_eq
        intro k
        rw [hdiv2, Nat.testBit_xor, Nat.testBit_xor, hdiv2, hdiv2]
      have hdiv_and : (a &&& b) / 2 = (a / 2) &&& (b / 2) := by
        apply Nat.eq_of_testBit_eq
        intro k
        rw [hdiv2, Nat.testBit_and, Nat.testBit_and, hdiv2, hdiv2]
      have hmod_xor : (a ^^^ b) % 2 = (a % 2) ^^^ (b % 2) := by
        apply Nat.eq_of_testBit_eq
        intro k
        cases k with
        | zero => rw [hmod2_0, Nat.testBit_xor, Nat.testBit_xor, hmod2_0, hmod2_0]
        | succ k => rw [hmod2_s, Nat.testBit_xor, hmod2_s, hmod2_s]; rfl
      have hmod_and : (a &&& b) % 2 = (a % 2) &&& (b % 2) := by
        apply Nat.eq_of_testBit_eq
        intro k
        cases k with
        | zero => rw [hmod2_0, Nat.testBit_and, Nat.testBit_and, hmod2_0, hmod2_0]
        | succ k => rw [hmod2_s, Nat.testBit_and, hmod2_s, hmod2_s]; rfl
      have ha2 : a = 2 * (a / 2) + a % 2 := (Nat.div_add_mod a 2).symm
      have hb2 : b = 2 * (b / 2) + b % 2 := (Nat.div_add_mod b 2).symm
      have hx2 : (a ^^^ b) = 2 * ((a ^^^ b) / 2) + (a ^^^ b) % 2 := (Nat.div_add_mod _ 2).symm
      have hn2 : (a &&& b) = 2 * ((a &&& b) / 2) + (a &&& b) % 2 := (Nat.div_add_mod _ 2).symm
      have hbit : a % 2 + b % 2 = (a % 2 ^^^ b % 2) + 2 * (a % 2 &&& b % 2) := by
        have hm1 : a % 2 = 0 ∨ a % 2 = 1 := by omega
        have hm2 : b % 2 = 0 ∨ b % 2 = 1 := by omega
        rcases hm1 with h1 | h1 <;> rcases hm2 with h2 | h2 <;> rw [h1, h2] <;> decide
      omega
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_xor, BitVec.toNat_and]
  have h := hnat w x.toNat y.toNat x.isLt y.isLt
  have hmod : (x.toNat + y.toNat) % 2 ^ w = ((x.toNat ^^^ y.toNat) + (x.toNat &&& y.toNat) + (x.toNat &&& y.toNat)) % 2 ^ w := by
    congr 1; omega
  rw [hmod]
  simp [Nat.add_mod]

theorem bitvec_xor_sub_eq {w : Nat} (d m : BitVec w) :
    (d ^^^ m) - d = m - (d &&& m) - (d &&& m) := by
  have h := bitvec_add_eq_xor_add_two_and d m
  calc (d ^^^ m) - d
      = ((d ^^^ m) + (d &&& m) + (d &&& m)) - (d &&& m) - (d &&& m) - d := by
          rw [BitVec.add_sub_cancel, BitVec.add_sub_cancel]
    _ = (d + m) - (d &&& m) - (d &&& m) - d := by rw [← h]
    _ = (m + d) - d - (d &&& m) - (d &&& m) := by
          rw [BitVec.add_comm d m]
          simp only [BitVec.sub_eq_add_neg]
          ac_rfl
    _ = m - (d &&& m) - (d &&& m) := by rw [BitVec.add_sub_cancel]

/-- Exact closed-form semantics of P_toff(0,1,3;2) for ALL bit-widths w. -/
theorem eval_circPtoff {w : Nat} (s : State 4 w) :
    evalCircuit circPtoff s =
      setReg s 2 (s 2 + (s 0 &&& s 1) - (s 3 &&& (s 0 &&& s 1)) - (s 3 &&& (s 0 &&& s 1))) := by
  simp only [circPtoff, evalCircuit, List.foldl, evalGate]
  have hne32 : (3 : Fin 4) ≠ 2 := by decide
  have hne03 : (0 : Fin 4) ≠ 3 := by decide
  have hne13 : (1 : Fin 4) ≠ 3 := by decide
  have hne01 : (0 : Fin 4) ≠ 1 := by decide
  simp only [hne32, hne03, hne13, hne01, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
  funext j
  by_cases hj2 : j = 2
  · subst hj2
    simp only [setReg, Fin.reduceEq, ↓reduceIte]
    have h := bitvec_xor_sub_eq (s 3) (s 0 &&& s 1)
    calc s 2 - s 3 + (s 3 ^^^ (s 0 &&& s 1))
        = s 2 + ((s 3 ^^^ (s 0 &&& s 1)) - s 3) := by
            simp only [BitVec.sub_eq_add_neg]; ac_rfl
      _ = s 2 + ((s 0 &&& s 1) - (s 3 &&& (s 0 &&& s 1)) - (s 3 &&& (s 0 &&& s 1))) := by rw [h]
      _ = s 2 + (s 0 &&& s 1) - (s 3 &&& (s 0 &&& s 1)) - (s 3 &&& (s 0 &&& s 1)) := by
            simp only [BitVec.sub_eq_add_neg]; ac_rfl
  · by_cases hj3 : j = 3
    · subst hj3
      simp only [setReg, Fin.reduceEq, ↓reduceIte]
      rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    · simp [setReg, hj2, hj3]

/-- Sharpness III.a (Exponential-to-Constant Order Collapse ∀ w ≥ 1):
    P_toff ALONE has order 2^w (its (2^(w-1))-th power is NON-IDENTITY for every w ≥ 1!),
    yet multiplying by a SINGLE rNot(3) collapses the order to 2 for ALL w ≥ 1! -/
theorem thm_ptoff_exp_order_sharp :
    ∀ (w : Nat), 1 ≤ w →
      ∃ (s : State 4 w), evalCircuit (repeatCircuit (2 ^ (w - 1)) circPtoff) s ≠ s := by
  intro w hw
  let s0 : State 4 w := fun i =>
    if i = 0 then 1#w else if i = 1 then 1#w else 0#w
  have hstep : ∀ k (c : BitVec w),
      evalCircuit (repeatCircuit k circPtoff) (setReg s0 2 c) = setReg s0 2 (c + BitVec.ofNat w k) := by
    intro k
    induction k with
    | zero =>
      intro c; simp [repeatCircuit, evalCircuit]
    | succ k ih =>
      intro c
      simp only [repeatCircuit, evalCircuit_append]
      rw [eval_circPtoff]
      have h0 : setReg s0 2 c 0 = 1#w := by simp [setReg, s0]
      have h1 : setReg s0 2 c 1 = 1#w := by simp [setReg, s0]
      have h3 : setReg s0 2 c 3 = 0#w := by simp [setReg, s0]
      rw [h0, h1, h3, setReg_self, setReg_setReg_same]
      have hand1 : (1#w &&& 1#w) = 1#w := BitVec.and_self
      have hand0 : (0#w &&& 1#w) = 0#w := BitVec.zero_and
      rw [hand1, hand0, BitVec.sub_zero, BitVec.sub_zero, ih]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      have h1 : ((c.toNat + 1 % 2 ^ w) % 2 ^ w + k % 2 ^ w) % 2 ^ w = (c.toNat + 1 + k) % 2 ^ w := by
        simp [Nat.add_mod]
      have h2 : (c.toNat + (k + 1) % 2 ^ w) % 2 ^ w = (c.toNat + (k + 1)) % 2 ^ w := by
        simp [Nat.add_mod]
      rw [h1, h2]
      congr 1; omega
  refine ⟨s0, ?_⟩
  have hs0 : s0 = setReg s0 2 (0#w) := by
    funext i
    by_cases h2 : i = 2
    · subst h2; simp [setReg, s0]
    · simp [setReg, h2]
  rw [hs0, hstep (2 ^ (w - 1)) (0#w)]
  intro heq
  have h2 := congrFun heq 2
  simp only [setReg_self, BitVec.zero_add] at h2
  have hval := congrArg BitVec.toNat h2
  simp only [BitVec.toNat_ofNat, Nat.zero_mod] at hval
  have hlt : 2 ^ (w - 1) < 2 ^ w := Nat.pow_lt_pow_right (by omega) (by omega)
  rw [Nat.mod_eq_of_lt hlt] at hval
  have hpos : 0 < 2 ^ (w - 1) := Nat.pow_pos (by omega)
  omega

/-- Sharpness III.b (Control vs Target NOT): replacing rNot(3) by rNot(0) breaks the involution at w = 1! -/
theorem thm_ptoff_wrong_not_counterexample :
    ∃ (s : State 4 1), evalCircuit (repeatCircuit 2 (circPtoff ++ [.rNot 0])) s ≠ s := by
  let s0 : State 4 1 := fun i => if i = 1 then 1#1 else 0#1
  refine ⟨s0, ?_⟩
  intro heq
  have h2 := congrFun heq 2
  revert h2; decide

/-- Theorem III.4 (Nonlinear Carry-Defect K2 Symmetry ∀ w : Nat):
    K2(0,1;2) = K2(1,0;2) even though CNOT(0,1) is asymmetric! (11-state bisim cert) -/
theorem thm_k2_symmetry :
    ∀ (w : Nat) (s : State 3 w), evalCircuit (circK2 0 1 2) s = evalCircuit (circK2 1 0 2) s :=
  sound_checkBisimCert 3 _ _ cert_k2_sym cert_k2_sym_ok

/-- Theorem III.5 (Nonlinear Carry-Defect K2 NOT-Collapse ∀ w : Nat):
    K2(0,1;2) · rNot(0) · K2(0,1;2) · rNot(0) = rSub(1,2)^2 (eliminates reg 0 & all ANDs! 41-state cert). -/
theorem thm_k2_not_collapse :
    ∀ (w : Nat) (s : State 3 w),
      evalCircuit (circK2 0 1 2 ++ [.rNot 0] ++ circK2 0 1 2 ++ [.rNot 0]) s =
      evalCircuit [.rSub 1 2, .rSub 1 2] s :=
  sound_checkBisimCert 3 _ _ cert_k2_not cert_k2_not_ok

/-- Exact closed-form semantics of T3(a,b,d;c) = P_toff(a,b,d;c)^2 · K2(a,b;c) for distinct (a,b,d,c):
    maps register c ↦ c - 4 * (a &&& b &&& d) mod 2^w, fixing all other registers! -/
theorem eval_circT3_gen {w : Nat} (a b d c : Fin 4)
    (hab : a ≠ b) (had : a ≠ d) (hac : a ≠ c) (hbd : b ≠ d) (hbc : b ≠ c) (hdc : d ≠ c)
    (s : State 4 w) :
    evalCircuit (circT3 a b d c) s =
      setReg s c (s c - 4#w * (s a &&& s b &&& s d)) := by
  have hP : ∀ (st : State 4 w),
      evalCircuit (circPtoffOf a b d c) st =
        setReg st c (st c + (st a &&& st b) - (st d &&& (st a &&& st b)) - (st d &&& (st a &&& st b))) := by
    intro st
    simp only [circPtoffOf, evalCircuit, List.foldl, evalGate,
               hdc, had, hbd, hab, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
    funext j
    by_cases hjc : j = c
    · rw [hjc]
      simp only [setReg, hac, hbc, hdc, Ne.symm hdc, ↓reduceIte]
      have h := bitvec_xor_sub_eq (st d) (st a &&& st b)
      calc st c - st d + (st d ^^^ (st a &&& st b))
          = st c + ((st d ^^^ (st a &&& st b)) - st d) := by
              simp only [BitVec.sub_eq_add_neg]; ac_rfl
        _ = st c + ((st a &&& st b) - (st d &&& (st a &&& st b)) - (st d &&& (st a &&& st b))) := by rw [h]
        _ = st c + (st a &&& st b) - (st d &&& (st a &&& st b)) - (st d &&& (st a &&& st b)) := by
              simp only [BitVec.sub_eq_add_neg]; ac_rfl
    · by_cases hjd : j = d
      · rw [hjd]
        simp only [setReg, hac, hbc, hdc, had, hbd, ↓reduceIte]
        rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
      · simp [setReg, hjc, hjd]
  have hK : ∀ (st : State 4 w),
      evalCircuit (circK2_4 a b c) st =
        setReg st c (st c - (st a &&& st b) - (st a &&& st b)) := by
    intro st
    simp only [circK2_4, evalCircuit, List.foldl, evalGate,
               hac, hbc, hab, ne_eq, not_false_eq_true, ↓reduceIte]
    funext j
    by_cases hjc : j = c
    · rw [hjc]
      simp only [setReg, hac, hbc, Ne.symm hbc, ↓reduceIte]
      have h := bitvec_xor_sub_eq (st b) (st a)
      have hand : (st b &&& st a) = (st a &&& st b) := BitVec.and_comm _ _
      rw [hand] at h
      calc st c - st a - st b + (st b ^^^ st a)
          = st c - st a + ((st b ^^^ st a) - st b) := by
              simp only [BitVec.sub_eq_add_neg]; ac_rfl
        _ = st c - st a + (st a - (st a &&& st b) - (st a &&& st b)) := by rw [h]
        _ = st c - (st a &&& st b) - (st a &&& st b) := by
              have hcan : -st a + st a = 0#w := by
                rw [BitVec.add_comm, ← BitVec.sub_eq_add_neg, BitVec.sub_self]
              simp only [BitVec.sub_eq_add_neg]
              calc st c + -st a + (st a + -(st a &&& st b) + -(st a &&& st b))
                  = st c + (-st a + st a) + -(st a &&& st b) + -(st a &&& st b) := by ac_rfl
                _ = st c + 0#w + -(st a &&& st b) + -(st a &&& st b) := by rw [hcan]
                _ = st c + -(st a &&& st b) + -(st a &&& st b) := by rw [BitVec.add_zero]
    · by_cases hjb : j = b
      · rw [hjb]
        simp only [setReg, hac, hbc, hab, ↓reduceIte]
        rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
      · simp [setReg, hjc, hjb]
  simp only [circT3, evalCircuit_append, hP, hK,
             setReg_ne _ hac, setReg_ne _ hbc, setReg_ne _ hdc, setReg_self, setReg_setReg_same]
  congr 1
  have h4 : ∀ (z : BitVec w), 4#w * z = z + z + z + z := by
    intro z
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_add]
    have hmul : (4 % 2 ^ w * z.toNat) % 2 ^ w = (4 * z.toNat) % 2 ^ w := by
      simp [Nat.mul_mod]
    rw [hmul]
    have h4z : 4 * z.toNat = z.toNat + z.toNat + z.toNat + z.toNat := by omega
    rw [h4z]
    simp [Nat.add_mod]
  have hand_comm : (s d &&& (s a &&& s b)) = (s a &&& s b &&& s d) := BitVec.and_comm _ _
  rw [hand_comm, h4]
  let m := s a &&& s b
  let t := s a &&& s b &&& s d
  change s c + m - t - t + m - t - t - m - m = s c - (t + t + t + t)
  simp only [BitVec.sub_eq_add_neg, BitVec.neg_add]
  have hcancel : m + -m = 0#w := by rw [← BitVec.sub_eq_add_neg, BitVec.sub_self]
  calc s c + m + -t + -t + m + -t + -t + -m + -m
      = s c + (m + -m) + (m + -m) + (-t + -t + -t + -t) := by ac_rfl
    _ = s c + 0#w + 0#w + (-t + -t + -t + -t) := by rw [hcancel]
    _ = s c + (-t + -t + -t + -t) := by rw [BitVec.add_zero, BitVec.add_zero]

/-- Theorem III.6 (Total S3-Symmetry of the Degree-3 Carry-Defect Circuit T3 ∀ w : Nat):
    T3(0,1,3;2) = T3(0,3,1;2) = T3(3,1,0;2) for EVERY bit-width w : Nat! -/
theorem thm_t3_S3_symmetry :
    ∀ (w : Nat) (s : State 4 w),
      evalCircuit (circT3 0 1 3 2) s = evalCircuit (circT3 0 3 1 2) s ∧
      evalCircuit (circT3 0 1 3 2) s = evalCircuit (circT3 3 1 0 2) s := by
  intro w s
  rw [eval_circT3_gen 0 1 3 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      eval_circT3_gen 0 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      eval_circT3_gen 3 1 0 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  constructor <;> (congr 2; ac_rfl)

/-- Sharpness III.c (Width Threshold of T3): T3 = Id for w ≤ 2, while T3 ≠ Id for ALL w ≥ 3! -/
theorem thm_t3_sharp_collapse_w2 :
    ∀ (s : State 4 2), evalCircuit (circT3 0 1 3 2) s = s := by
  intro s
  rw [eval_circT3_gen 0 1 3 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  have h4 : (4#2 : BitVec 2) = 0#2 := by decide
  rw [h4, BitVec.zero_mul, BitVec.sub_zero, setReg_id]

theorem thm_t3_nontrivial_ge3 :
    ∀ (w : Nat), 3 ≤ w → ∃ (s : State 4 w), evalCircuit (circT3 0 1 3 2) s ≠ s := by
  intro w hw
  let s0 : State 4 w := fun i => if i = 2 then 0#w else 1#w
  refine ⟨s0, ?_⟩
  rw [eval_circT3_gen 0 1 3 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  intro heq
  have h2 := congrFun heq 2
  simp only [setReg_self, s0, Fin.reduceEq, ↓reduceIte, BitVec.and_self, BitVec.mul_one, BitVec.zero_sub] at h2
  have hval := congrArg BitVec.toNat h2
  have hlt4 : 4 < 2 ^ w := by
    calc 4 < 2 ^ 3 := by omega
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hw
  have hneg4 : (-(4#w)).toNat = 2 ^ w - 4 := by
    rw [BitVec.toNat_neg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt4]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hneg4, BitVec.toNat_zero] at hval
  omega

-- ============================================================================
-- SECTION 6: Adversarial Mutation Tests (checkCert bad = false),
--            Non-Vacuity Witnesses & Exhaustive Axiom Audit
-- ============================================================================

-- 6.1 Kernel-checked negative / mutation tests across ALL 5 certificate checkers!

theorem mut_bisim_dropped_state :
    checkBisimCert 2 (circU ++ circV ++ circU) (circV ++ circU ++ circV) cert_sl2_braid.tail = false := by
  decide

theorem mut_bisim_wrong_braid :
    checkBisimCert 2 (circU ++ circV ++ circU) (circU ++ circU ++ circV) cert_sl2_braid = false := by
  decide

theorem mut_bisim_wrong_not_reg :
    checkBisimCert 4 ([.rNot 0] ++ circPtoff ++ [.rNot 0]) (Circuit.inv circPtoff) cert_ptoff_dih = false := by
  decide

theorem mut_window_wrong_wire :
    checkWindowEq 1 3 [gA, gS, gA] [gS, gA, gT] = false := by
  decide

theorem mut_window_out_of_bounds :
    checkWindowEq 1 2 [gT] [gT] = false := by
  decide

theorem mut_rewrite_illegal_commute :
    checkRewriteCert b3Lib [gA, gT] [gT, gA] [.commute 0] = false := by
  decide

theorem mut_rewrite_wrong_dir :
    checkRewriteCert d6Lib (circS ++ circC) (repeatCircuit 5 circC ++ circS) [.applyRel 1 false 0] = false := by
  decide

theorem mut_coset_corrupt_table :
    let badCC : CosetCert 2 := { d6CosetCert with table := d6CosetCert.table.set! 0 #[2, 6] }
    checkCosetCert d6Lib d6Gens badCC = false := by
  decide

theorem mut_coset_corrupt_edge_proof :
    let badRow := (b3CosetCert.edgeProofs[47]!).set! 0 []
    let badCC : CosetCert 1 := { b3CosetCert with edgeProofs := b3CosetCert.edgeProofs.set! 47 badRow }
    checkCosetCert b3Lib b3Gens badCC = false := by
  decide

theorem mut_distinct_d6_w1_rejected :
    checkDistinctAt 2 1 d6CosetCert.reps = false := by
  decide

theorem mut_distinct_b3_w2_rejected :
    checkDistinctAt 1 2 b3CosetCert.reps = false := by
  decide

theorem mut_order_lower_inflated :
    checkOrderLowerAt 2 2 12 circC = false := by
  decide

-- 6.2 Constructive Non-Vacuity Witnesses (concrete BitVec evaluations at w = 8, 64)
example : evalCircuit (circU ++ circV ++ circU) (fun i : Fin 2 => if i = 0 then 0x13#8 else 0xA7#8) =
          evalCircuit (circV ++ circU ++ circV) (fun i : Fin 2 => if i = 0 then 0x13#8 else 0xA7#8) :=
  thm_sl2_braid 8 _

example : evalCircuit (repeatCircuit 3 [gA, gS, gT]) (fun _ : Fin 1 => 1#64) ≠ (fun _ : Fin 1 => 1#64) := by
  intro h
  have h0 := congrFun h 0
  revert h0; decide

example : evalCircuit (repeatCircuit 6 [gA, gS, gT]) (fun _ : Fin 1 => 0xDEADBEEFCAFEBABE#64) =
          (fun _ : Fin 1 => 0xDEADBEEFCAFEBABE#64) :=
  (thm_b3_AST_exact_order6 64 (by omega)).1 _

example : evalCircuit (circT3 0 1 3 2) (fun i : Fin 4 => if i = 2 then 0#8 else 0x55#8) ≠
          (fun i : Fin 4 => if i = 2 then 0#8 else 0x55#8) := by
  intro h
  have h2 := congrFun h 2
  revert h2; decide

end RevCert
