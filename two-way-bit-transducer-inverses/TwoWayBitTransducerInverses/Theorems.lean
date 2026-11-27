/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TwoWayBitTransducerInverses.Defs

/-!
# Theorems (`two-way-bit-transducer-inverses`)

Full proofs of the headline infinite theorems of Two-Way Bit-Transducer Tile-Witness Inversion and Coxeter-6 Phase Transition.
-/

namespace BidirectionalTransducer

theorem ofBits_getLsbD (xs : List Bool) (i : Nat) (hi : i < xs.length) :
    (ofBits xs).getLsbD i = xs[i] := by
  induction xs generalizing i with
  | nil => cases hi
  | cons b bs ih =>
      have hpow : (2 * (ofBits bs).toNat + b.toNat) % 2 ^ (bs.length + 1)
          = 2 * (ofBits bs).toNat + b.toNat := by
        apply Nat.mod_eq_of_lt
        have hlt : (ofBits bs).toNat < 2 ^ bs.length := (ofBits bs).isLt
        have hblt : b.toNat ≤ 1 := by cases b <;> decide
        have : 2 ^ (bs.length + 1) = 2 * 2 ^ bs.length := by
          rw [Nat.pow_succ, Nat.mul_comm]
        omega
      have htoNat : (ofBits (b :: bs)).toNat = 2 * (ofBits bs).toNat + b.toNat := by
        change (BitVec.ofNat (bs.length + 1) (2 * (ofBits bs).toNat + b.toNat)).toNat = _
        rw [BitVec.toNat_ofNat]
        exact hpow
      cases i with
      | zero =>
          simp only [List.getElem_cons_zero]
          change (ofBits (b :: bs)).toNat.testBit 0 = b
          rw [htoNat, Nat.testBit_zero]
          cases b <;> simp [Nat.add_mod]
      | succ j =>
          have hj : j < bs.length := Nat.lt_of_succ_lt_succ hi
          simp only [List.getElem_cons_succ]
          change (ofBits (b :: bs)).toNat.testBit (j + 1) = bs[j]
          rw [htoNat, Nat.testBit_succ]
          have hdiv : (2 * (ofBits bs).toNat + b.toNat) / 2 = (ofBits bs).toNat := by
            cases b <;> simp <;> omega
          rw [hdiv]
          exact ih j hj

theorem ofBits_toBits {w : Nat} (x : BitVec w) :
    (ofBits (toBits x)).cast (toBits_length x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_cast]
  have hi' : i < (toBits x).length := by rw [toBits_length]; exact hi
  rw [ofBits_getLsbD (toBits x) i hi']
  simp only [toBits, List.getElem_ofFn]

theorem toBits_ofBits (xs : List Bool) : toBits (ofBits xs) = xs := by
  apply List.ext_getElem
  · exact toBits_length (ofBits xs)
  · intro i h1 h2
    simp only [toBits, List.getElem_ofFn]
    exact ofBits_getLsbD xs i h2

theorem toBits_liftBV (f : List Bool → List Bool) (hf : ∀ xs, (f xs).length = xs.length)
    {w : Nat} (x : BitVec w) :
    toBits (liftBV f hf x) = f (toBits x) := by
  apply List.ext_getElem
  · rw [toBits_length, hf, toBits_length]
  · intro i h1 h2
    simp only [liftBV, toBits, List.getElem_ofFn]
    exact ofBits_getLsbD (f (toBits x)) i h2

theorem liftBV_comp (f g : List Bool → List Bool)
    (hf : ∀ xs, (f xs).length = xs.length)
    (hg : ∀ xs, (g xs).length = xs.length)
    {w : Nat} (x : BitVec w) :
    liftBV f hf (liftBV g hg x) =
      liftBV (fun xs => f (g xs)) (fun xs => by rw [hf, hg]) x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hlen1 : i < (toBits (liftBV f hf (liftBV g hg x))).length := by rw [toBits_length]; exact hi
  have h1 : (toBits (liftBV f hf (liftBV g hg x)))[i]'hlen1
      = (toBits (liftBV (fun xs => f (g xs)) (fun xs => by rw [hf, hg]) x))[i]'(by rw [toBits_length]; exact hi) := by
    simp only [toBits_liftBV]
  simp only [toBits, List.getElem_ofFn] at h1
  exact h1

theorem liftBV_eq_id_of_list (f : List Bool → List Bool)
    (hf : ∀ xs, (f xs).length = xs.length)
    (hid : ∀ xs, f xs = xs) {w : Nat} (x : BitVec w) :
    liftBV f hf x = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h := toBits_liftBV f hf x
  rw [hid] at h
  have hget := congrArg (fun l => l.getD i false) h
  simpa [toBits, List.getD_eq_getElem?_getD, hi] using hget

theorem tileStep_nil_eq {Q : Type} {cL cM : List Q} {b o : Bool}
    (h : TileStep ([] : List (Sweep Q)) cL cM b o) : b = o := by
  cases cL <;> cases cM <;> simp [TileStep] at h
  exact h

theorem tileChain_nil_sws {Q : Type} {cL cR : List Q} {xs ys : List Bool}
    (h : TileChain ([] : List (Sweep Q)) cL cR xs ys) :
    ys = xs := by
  induction h with
  | nil _ _ => rfl
  | cons hStep _ ih =>
      have hb := tileStep_nil_eq hStep
      rw [hb, ih]

/-- Peeling off a leading forward sweep from a multi-sweep tile chain. -/
theorem tileChain_peel_fwd {Q : Type} {m : Mealy Q} {sws : List (Sweep Q)}
    {cL cR : List Q} {xs ys : List Bool}
    (h : TileChain (⟨.fwd, m⟩ :: sws) cL cR xs ys) :
    ∃ qL cL' qR cR',
      cL = qL :: cL' ∧
      cR = qR :: cR' ∧
      (runFwd m qL xs).2 = qR ∧
      TileChain sws cL' cR' (runFwd m qL xs).1 ys := by
  induction h with
  | nil c hlen =>
      cases c with
      | nil => simp at hlen
      | cons q cs =>
          refine ⟨q, cs, q, cs, rfl, rfl, rfl, ?_⟩
          exact TileChain.nil cs (Nat.succ.inj hlen)
  | @cons cL cM cR b o xs ys hStep hRest ih =>
      rcases ih with ⟨qM, cM', qR, cR', hcM, hcR, hEnd, hChain'⟩
      subst hcM
      cases cL with
      | nil => simp [TileStep] at hStep
      | cons qL cL' =>
          simp only [TileStep] at hStep
          rcases hStep with ⟨hDelta, hStep'⟩
          refine ⟨qL, cL', qR, cR', rfl, hcR, ?_, ?_⟩
          · simp only [runFwd, hDelta, hEnd]
          · simp only [runFwd, hDelta]
            exact TileChain.cons hStep' hChain'

/-- Peeling off a leading backward sweep from a multi-sweep tile chain. -/
theorem tileChain_peel_bwd {Q : Type} {m : Mealy Q} {sws : List (Sweep Q)}
    {cL cR : List Q} {xs ys : List Bool}
    (h : TileChain (⟨.bwd, m⟩ :: sws) cL cR xs ys) :
    ∃ qL cL' qR cR',
      cL = qL :: cL' ∧
      cR = qR :: cR' ∧
      (runBwd m qR xs).2 = qL ∧
      TileChain sws cL' cR' (runBwd m qR xs).1 ys := by
  induction h with
  | nil c hlen =>
      cases c with
      | nil => simp at hlen
      | cons q cs =>
          refine ⟨q, cs, q, cs, rfl, rfl, rfl, ?_⟩
          exact TileChain.nil cs (Nat.succ.inj hlen)
  | @cons cL cM cR b o xs ys hStep hRest ih =>
      rcases ih with ⟨qM, cM', qR, cR', hcM, hcR, hEnd, hChain'⟩
      subst hcM
      cases cL with
      | nil => simp [TileStep] at hStep
      | cons qL cL' =>
          simp only [TileStep] at hStep
          rcases hStep with ⟨hDelta, hStep'⟩
          refine ⟨qL, cL', qR, cR', rfl, hcR, ?_, ?_⟩
          · simp only [runBwd, hEnd, hDelta]
          · simp only [runBwd, hEnd]
            exact TileChain.cons hStep' hChain'

/--
**Lemma 1 (Stratified Global Trajectory Uniqueness):**
Any valid bidirectional tile chain matching the LSB and MSB boundary conditions
MUST produce the exact global multi-sweep output `runSweeps sws xs`.
-/
theorem tileChain_eq_runSweeps {Q : Type} (sws : List (Sweep Q))
    {cL cR : List Q} {xs ys : List Bool}
    (hChain : TileChain sws cL cR xs ys)
    (hL : LeftBoundary sws cL)
    (hR : RightBoundary sws cR) :
    ys = runSweeps sws xs := by
  induction sws generalizing cL cR xs ys with
  | nil => exact tileChain_nil_sws hChain
  | cons sw sws ih =>
      cases sw with
      | mk dir m =>
        cases dir with
        | fwd =>
            rcases tileChain_peel_fwd hChain with ⟨qL, cL', qR, cR', hcL, hcR, _, hChain'⟩
            subst hcL; subst hcR
            simp only [LeftBoundary] at hL
            simp only [RightBoundary] at hR
            rcases hL with ⟨hqL, hL'⟩
            subst hqL
            simp only [runSweeps, runSweep]
            exact ih hChain' hL' hR
        | bwd =>
            rcases tileChain_peel_bwd hChain with ⟨qL, cL', qR, cR', hcL, hcR, _, hChain'⟩
            subst hcL; subst hcR
            simp only [LeftBoundary] at hL
            simp only [RightBoundary] at hR
            rcases hR with ⟨hqR, hR'⟩
            subst hqR
            simp only [runSweeps, runSweep]
            exact ih hChain' hL hR'

/-- Coupled 2-sweep trajectory uniqueness: `B` starts in state `beta sEnd`. -/
theorem tileChain_eq_runCoupledTwoWay {Q : Type} (F B : Mealy Q) (beta : Q → Q)
    {cL cR : List Q} {xs ys : List Bool}
    (hChain : TileChain [⟨.fwd, F⟩, ⟨.bwd, B⟩] cL cR xs ys)
    (hL : ∃ qB, cL = [F.q0, qB])
    (hR : ∃ sEnd, cR = [sEnd, beta sEnd]) :
    ys = runCoupledTwoWay F beta B xs := by
  rcases tileChain_peel_fwd hChain with ⟨qFL, cL', qFR, cR', hcL, hcR, hFEnd, hChain1⟩
  rcases hL with ⟨qBL, hL'⟩
  rw [hL'] at hcL
  injection hcL with hqFL hcL'
  subst hqFL; subst hcL'
  rcases hR with ⟨sEnd, hR'⟩
  rw [hR'] at hcR
  injection hcR with hqFR hcR'
  subst hqFR; subst hcR'
  rcases tileChain_peel_bwd hChain1 with ⟨qBL', cL'', qBR', cR'', hcL1, hcR1, _, hChain2⟩
  injection hcL1 with hqBL hcL''
  injection hcR1 with hqBR hcR''
  subst hqBL; subst hcL''; subst hqBR; subst hcR''
  have hys := tileChain_nil_sws hChain2
  simp only [runCoupledTwoWay, hFEnd]
  exact hys

/-- Backward witness extraction along any bit-list `xs`. -/
theorem build_tileChain_from_witness {Q M : Type}
    (sws : List (Sweep Q))
    (P : Bool → Bool → Prop)
    (next : M → Bool → M)
    (W : M → List Q → Prop)
    (hLen : ∀ m c, W m c → c.length = sws.length)
    (hStep : ∀ m b cR, W (next m b) cR → ∃ cL o, W m cL ∧ TileStep sws cL cR b o ∧ P b o)
    (m : M) (xs : List Bool) (cR : List Q)
    (hW : W (runDFA next m xs) cR) :
    ∃ cL ys, W m cL ∧ TileChain sws cL cR xs ys ∧ BitRel P xs ys := by
  induction xs generalizing m cR with
  | nil =>
      refine ⟨cR, [], hW, TileChain.nil cR (hLen m cR hW), BitRel.nil⟩
  | cons b bs ih =>
      simp only [runDFA] at hW
      rcases ih (next m b) cR hW with ⟨cM, ys', hWM, hChain', hProp'⟩
      rcases hStep m b cM hWM with ⟨cL, o, hWL, hTile, hP⟩
      exact ⟨cL, o :: ys', hWL, TileChain.cons hTile hChain', BitRel.cons hP hProp'⟩

theorem eq_of_bitRel_eq {xs ys : List Bool} (h : BitRel Eq xs ys) : ys = xs := by
  induction h with
  | nil => rfl
  | cons hab _ ih => rw [hab, ih]

/--
**Master Mechanism Theorem (`tileWitness_sound` — Bidirectional Tile-Witness Lifter):**
If a crossing-witness automaton `(M, m0, next, W)` satisfies the three finite/local
conditions (Init-Soundness, Backward-Witnessed Good-Tile Step, and Final Boundary Coverage),
then the multi-sweep transducer satisfies `P` at EVERY bit for ALL widths `w` and ALL inputs.
-/
theorem tileWitness_sound {Q M : Type}
    (sws : List (Sweep Q))
    (P : Bool → Bool → Prop)
    (m0 : M) (next : M → Bool → M)
    (W : M → List Q → Prop)
    (hLen : ∀ m c, W m c → c.length = sws.length)
    (hInit : ∀ c, W m0 c → LeftBoundary sws c)
    (hStep : ∀ m b cR, W (next m b) cR → ∃ cL o, W m cL ∧ TileStep sws cL cR b o ∧ P b o)
    (hFinal : ∀ m, ∃ cR, W m cR ∧ RightBoundary sws cR)
    (xs : List Bool) :
    BitRel P xs (runSweeps sws xs) := by
  rcases hFinal (runDFA next m0 xs) with ⟨cR, hWR, hRB⟩
  rcases build_tileChain_from_witness sws P next W hLen hStep m0 xs cR hWR with
    ⟨cL, ys, hWL, hChain, hForall⟩
  have hLB := hInit cL hWL
  have hEq := tileChain_eq_runSweeps sws hChain hLB hRB
  rw [← hEq]
  exact hForall

/-- Identity-law specialization of `tileWitness_sound` (on `List Bool` and lifted to `BitVec w`). -/
theorem tileWitness_sound_id {Q M : Type}
    (sws : List (Sweep Q))
    (m0 : M) (next : M → Bool → M)
    (W : M → List Q → Prop)
    (hLen : ∀ m c, W m c → c.length = sws.length)
    (hInit : ∀ c, W m0 c → LeftBoundary sws c)
    (hStep : ∀ m b cR, W (next m b) cR → ∃ cL, W m cL ∧ TileStep sws cL cR b b)
    (hFinal : ∀ m, ∃ cR, W m cR ∧ RightBoundary sws cR)
    (xs : List Bool) :
    runSweeps sws xs = xs := by
  have h := tileWitness_sound sws Eq m0 next W hLen hInit
    (fun m b cR hW => by
      rcases hStep m b cR hW with ⟨cL, hWL, hTile⟩
      exact ⟨cL, b, hWL, hTile, rfl⟩)
    hFinal xs
  exact eq_of_bitRel_eq h

theorem tileWitness_sound_id_bv {Q M : Type}
    (sws : List (Sweep Q))
    (m0 : M) (next : M → Bool → M)
    (W : M → List Q → Prop)
    (hLen : ∀ m c, W m c → c.length = sws.length)
    (hInit : ∀ c, W m0 c → LeftBoundary sws c)
    (hStep : ∀ m b cR, W (next m b) cR → ∃ cL, W m cL ∧ TileStep sws cL cR b b)
    (hFinal : ∀ m, ∃ cR, W m cR ∧ RightBoundary sws cR)
    {w : Nat} (x : BitVec w) :
    sweepsBV sws x = x :=
  liftBV_eq_id_of_list (runSweeps sws) (runSweeps_length sws)
    (tileWitness_sound_id sws m0 next W hLen hInit hStep hFinal) x

/-- Coupled 2-sweep specialization of `tileWitness_sound` (`B` initialized with `beta sEnd`). -/
theorem tileWitness_sound_coupled_id {Q M : Type}
    (F B : Mealy Q) (beta : Q → Q)
    (m0 : M) (next : M → Bool → M)
    (W : M → List Q → Prop)
    (hLen : ∀ m c, W m c → c.length = 2)
    (hInit : ∀ c, W m0 c → ∃ qB, c = [F.q0, qB])
    (hStep : ∀ m b cR, W (next m b) cR →
        ∃ cL, W m cL ∧ TileStep [⟨.fwd, F⟩, ⟨.bwd, B⟩] cL cR b b)
    (hFinal : ∀ m, ∃ sEnd, W m [sEnd, beta sEnd])
    (xs : List Bool) :
    runCoupledTwoWay F beta B xs = xs := by
  rcases hFinal (runDFA next m0 xs) with ⟨sEnd, hWR⟩
  rcases build_tileChain_from_witness [⟨.fwd, F⟩, ⟨.bwd, B⟩] Eq next W hLen
    (fun m b cR hW => by
      rcases hStep m b cR hW with ⟨cL, hWL, hTile⟩
      exact ⟨cL, b, hWL, hTile, rfl⟩)
    m0 xs [sEnd, beta sEnd] hWR with ⟨cL, ys, hWL, hChain, hForall⟩
  have hEq := tileChain_eq_runCoupledTwoWay F B beta hChain (hInit cL hWL) ⟨sEnd, rfl⟩
  rw [← hEq]
  exact eq_of_bitRel_eq hForall

/-! ## Section 3: Computable Finite-Certificate Checker (`checkCert` + `decide`) -/

theorem tileStepBool_sound {Q : Type} [DecidableEq Q]
    (sws : List (Sweep Q)) (cL cR : List Q) (b o : Bool)
    (h : tileStepBool sws cL cR b o = true) :
    TileStep sws cL cR b o := by
  induction sws generalizing cL cR b with
  | nil =>
      cases cL <;> cases cR <;> simp [tileStepBool] at h
      exact h
  | cons sw sws ih =>
      cases sw with
      | mk dir m =>
        cases cL with
        | nil => cases dir <;> simp [tileStepBool] at h
        | cons qL cL' =>
          cases cR with
          | nil => cases dir <;> simp [tileStepBool] at h
          | cons qR cR' =>
            cases dir with
            | fwd =>
                simp only [tileStepBool, Bool.and_eq_true, decide_eq_true_eq] at h
                exact ⟨h.1, ih cL' cR' (m.out qL b) h.2⟩
            | bwd =>
                simp only [tileStepBool, Bool.and_eq_true, decide_eq_true_eq] at h
                exact ⟨h.1, ih cL' cR' (m.out qR b) h.2⟩

theorem leftBoundaryBool_sound {Q : Type} [DecidableEq Q]
    (sws : List (Sweep Q)) (c : List Q) (h : leftBoundaryBool sws c = true) :
    LeftBoundary sws c := by
  induction sws generalizing c with
  | nil =>
      cases c <;> simp [leftBoundaryBool] at h
      trivial
  | cons sw sws ih =>
      cases sw with
      | mk dir m =>
        cases c with
        | nil => cases dir <;> simp [leftBoundaryBool] at h
        | cons q qs =>
          cases dir with
          | fwd =>
              simp only [leftBoundaryBool, Bool.and_eq_true, decide_eq_true_eq] at h
              exact ⟨h.1, ih qs h.2⟩
          | bwd =>
              simp only [leftBoundaryBool] at h
              exact ih qs h

theorem rightBoundaryBool_sound {Q : Type} [DecidableEq Q]
    (sws : List (Sweep Q)) (c : List Q) (h : rightBoundaryBool sws c = true) :
    RightBoundary sws c := by
  induction sws generalizing c with
  | nil =>
      cases c <;> simp [rightBoundaryBool] at h
      trivial
  | cons sw sws ih =>
      cases sw with
      | mk dir m =>
        cases c with
        | nil => cases dir <;> simp [rightBoundaryBool] at h
        | cons q qs =>
          cases dir with
          | fwd =>
              simp only [rightBoundaryBool] at h
              exact ih qs h
          | bwd =>
              simp only [rightBoundaryBool, Bool.and_eq_true, decide_eq_true_eq] at h
              exact ⟨h.1, ih qs h.2⟩

/--
**Automated Finite-Certificate Lifting Theorem (`checkCert_sound`):**
If `checkCert cert = true` (discharged by `decide`), then `runSweeps cert.sws xs = xs`
for EVERY bit-list `xs`, and `sweepsBV cert.sws x = x` for EVERY width `w` and `x : BitVec w`.
-/
theorem checkCert_sound {Q : Type} [DecidableEq Q] (cert : FiniteTileCert Q)
    (hCheck : checkCert cert = true) (xs : List Bool) :
    runSweeps cert.sws xs = xs := by
  simp only [checkCert, Bool.and_eq_true] at hCheck
  rcases hCheck with ⟨⟨⟨hLenB, hInitB⟩, hStepB⟩, hFinalB⟩
  apply tileWitness_sound_id cert.sws cert.m0 cert.next (fun m c => c ∈ cert.witness m)
  · intro m c hc
    have h1 := List.all_eq_true.mp hLenB m (List.mem_finRange m)
    exact of_decide_eq_true (List.all_eq_true.mp h1 c hc)
  · intro c hc
    exact leftBoundaryBool_sound cert.sws c (List.all_eq_true.mp hInitB c hc)
  · intro m b cR hcR
    have h1 := List.all_eq_true.mp hStepB m (List.mem_finRange m)
    have hb : b ∈ [false, true] := by cases b <;> simp
    have h2 := List.all_eq_true.mp h1 b hb
    have h3 := List.all_eq_true.mp h2 cR hcR
    rcases List.any_eq_true.mp h3 with ⟨cL, hcL, hTileB⟩
    exact ⟨cL, hcL, tileStepBool_sound cert.sws cL cR b b hTileB⟩
  · intro m
    have h1 := List.all_eq_true.mp hFinalB m (List.mem_finRange m)
    rcases List.any_eq_true.mp h1 with ⟨cR, hcR, hRB⟩
    exact ⟨cR, hcR, rightBoundaryBool_sound cert.sws cR hRB⟩

theorem checkCert_sound_bv {Q : Type} [DecidableEq Q] (cert : FiniteTileCert Q)
    (hCheck : checkCert cert = true) {w : Nat} (x : BitVec w) :
    sweepsBV cert.sws x = x :=
  liftBV_eq_id_of_list (runSweeps cert.sws) (runSweeps_length cert.sws)
    (checkCert_sound cert hCheck) x

/-! ## Section 4: The 2-State Nonlinear Skip-Flip Full-Cycle Collapse Laws -/

theorem certSkipFlip2Period3_valid : checkCert certSkipFlip2Period3 = true := by
  decide

/-- Helper relating `sweepsBV` of a repeated two-way pair to iterated `twoWayBV`. -/
theorem sweepsBV_twoWay_three {Q : Type} (F B : Mealy Q) {w : Nat} (x : BitVec w) :
    sweepsBV [⟨.fwd, F⟩, ⟨.bwd, B⟩, ⟨.fwd, F⟩, ⟨.bwd, B⟩, ⟨.fwd, F⟩, ⟨.bwd, B⟩] x =
      twoWayBV F B (twoWayBV F B (twoWayBV F B x)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hlen : i < (toBits (sweepsBV [⟨.fwd, F⟩, ⟨.bwd, B⟩, ⟨.fwd, F⟩, ⟨.bwd, B⟩, ⟨.fwd, F⟩, ⟨.bwd, B⟩] x)).length := by
    rw [toBits_length]; exact hi
  have hEq : toBits (sweepsBV [⟨.fwd, F⟩, ⟨.bwd, B⟩, ⟨.fwd, F⟩, ⟨.bwd, B⟩, ⟨.fwd, F⟩, ⟨.bwd, B⟩] x) =
      toBits (twoWayBV F B (twoWayBV F B (twoWayBV F B x))) := by
    simp only [sweepsBV, twoWayBV, fwdBV, bwdBV, toBits_liftBV, runSweeps, runSweep]
  have hget := congrArg (fun l => l.getD i false) hEq
  simpa [toBits, List.getD_eq_getElem?_getD, hi] using hget

theorem iter_succ_right {α : Type} (f : α → α) (n : Nat) (x : α) :
    iter f (n + 1) x = f (iter f n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ k ih => exact ih (f x)

theorem iter_add {α : Type} (f : α → α) (a b : Nat) (x : α) :
    iter f (a + b) x = iter f b (iter f a x) := by
  induction a generalizing x with
  | zero => simp [iter]
  | succ k ih =>
      have h : k + 1 + b = (k + b) + 1 := by omega
      rw [h]
      exact ih (f x)

theorem sweepsBV_twoWay_six {Q : Type} (F B : Mealy Q) {w : Nat} (x : BitVec w) :
    sweepsBV [⟨.fwd, F⟩, ⟨.bwd, B⟩, ⟨.fwd, F⟩, ⟨.bwd, B⟩, ⟨.fwd, F⟩, ⟨.bwd, B⟩,
              ⟨.fwd, F⟩, ⟨.bwd, B⟩, ⟨.fwd, F⟩, ⟨.bwd, B⟩, ⟨.fwd, F⟩, ⟨.bwd, B⟩] x =
      iter (twoWayBV F B) 6 x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hEq : toBits (sweepsBV [⟨.fwd, F⟩, ⟨.bwd, B⟩, ⟨.fwd, F⟩, ⟨.bwd, B⟩, ⟨.fwd, F⟩, ⟨.bwd, B⟩,
              ⟨.fwd, F⟩, ⟨.bwd, B⟩, ⟨.fwd, F⟩, ⟨.bwd, B⟩, ⟨.fwd, F⟩, ⟨.bwd, B⟩] x) =
      toBits (iter (twoWayBV F B) 6 x) := by
    simp only [iter, sweepsBV, twoWayBV, fwdBV, bwdBV, toBits_liftBV, runSweeps, runSweep]
  have hget := congrArg (fun l => l.getD i false) hEq
  simpa [toBits, List.getD_eq_getElem?_getD, hi] using hget

/--
**Theorem A (`skipFlip2_period3_bv`):**
For EVERY bit-width `w : Nat` and EVERY `x : BitVec w`,
`(B_2 ∘ F_2)^3(x) = x`, certified via our 3-state, 6-witness crossing automaton.
-/
theorem skipFlip2_period3_bv {w : Nat} (x : BitVec w) :
    iter skipFlip2TwoWay 3 x = x := by
  have h := checkCert_sound_bv certSkipFlip2Period3 certSkipFlip2Period3_valid x
  simpa [certSkipFlip2Period3, skipFlip2TwoWay, iter, sweepsBV_twoWay_three] using h

theorem certSkipFlip2ShiftedPeriod6_valid : checkCert certSkipFlip2ShiftedPeriod6 = true := by
  decide

/--
**Theorem D (`skipFlip2_shifted_period6_bv`):**
Shifting `B_2`'s initial state to skip mode (`q0 = true`) lifts the period from 3 to 6:
`(B_2^{(q0=true)} ∘ F_2)^6(x) = x` for ALL `w : Nat` and ALL `x : BitVec w`.
-/
theorem skipFlip2_shifted_period6_bv {w : Nat} (x : BitVec w) :
    iter skipFlip2Shifted 6 x = x := by
  have h := checkCert_sound_bv certSkipFlip2ShiftedPeriod6 certSkipFlip2ShiftedPeriod6_valid x
  have hs := sweepsBV_twoWay_six (skipFlip2 false) (skipFlip2 true) x
  change iter (twoWayBV (skipFlip2 false) (skipFlip2 true)) 6 x = x
  rw [← hs]
  exact h

/-! ### Section 4B: Proof that `F_2` Individually Has Exact Full-Cycle Order `2^w` -/

theorem list_snoc_decomp {α : Type} :
    ∀ {n : Nat} (xs : List α), xs.length = n + 1 →
      ∃ pref b, xs = pref ++ [b] ∧ pref.length = n
  | 0, [b], _ => ⟨[], b, rfl, rfl⟩
  | n + 1, a :: xs, h => by
      have hlen : xs.length = n + 1 := Nat.succ.inj h
      rcases list_snoc_decomp xs hlen with ⟨pref, b, heq, hp⟩
      exact ⟨a :: pref, b, by simp [heq], by simp [hp]⟩

theorem runFwd_append {Q : Type} (m : Mealy Q) (q : Q) (xs ys : List Bool) :
    runFwd m q (xs ++ ys) =
      let (os1, q1) := runFwd m q xs
      let (os2, q2) := runFwd m q1 ys
      (os1 ++ os2, q2) := by
  induction xs generalizing q with
  | nil => simp [runFwd]
  | cons b bs ih =>
      simp only [List.cons_append, runFwd]
      rw [ih (m.delta q b)]

theorem sf2FlipParity_add (a b : Nat) (xs : List Bool) :
    sf2FlipParity (a + b) xs =
      xor (sf2FlipParity a xs) (sf2FlipParity b (iter skipFlip2Fwd a xs)) := by
  induction a generalizing xs with
  | zero => simp [sf2FlipParity, iter]
  | succ k ih =>
      have h1 : k + 1 + b = (k + b) + 1 := by omega
      rw [h1]
      simp only [sf2FlipParity, iter]
      rw [ih (skipFlip2Fwd xs), Bool.xor_assoc]

/-- Action of `n` iterations of `skipFlip2Fwd` on `xs ++ [b]`. -/
theorem skipFlip2Fwd_iter_snoc (n : Nat) (xs : List Bool) (b : Bool) :
    iter skipFlip2Fwd n (xs ++ [b]) =
      iter skipFlip2Fwd n xs ++ [xor b (sf2FlipParity n xs)] := by
  induction n generalizing xs b with
  | zero => simp [iter, sf2FlipParity]
  | succ k ih =>
      simp only [iter, sf2FlipParity]
      have hStep : skipFlip2Fwd (xs ++ [b]) = skipFlip2Fwd xs ++ [xor b (!(sf2End xs))] := by
        simp only [skipFlip2Fwd, sf2End, runFwd_append, runFwd]
        cases (runFwd (skipFlip2 false) false xs).2 <;> cases b <;> rfl
      rw [hStep, ih (skipFlip2Fwd xs) (xor b (!(sf2End xs)))]
      rw [Bool.xor_assoc]

/-- Key algebraic pairing identity: `xor (!(δ(q, b))) (!(δ(q, !b))) = !q` for `skipFlip2`. -/
theorem sf2_pair_xor (q b : Bool) :
    xor (!((skipFlip2 false).delta q b)) (!((skipFlip2 false).delta q (!b))) = !q := by
  cases q <;> cases b <;> rfl

theorem sf2End_snoc (xs : List Bool) (b : Bool) :
    sf2End (xs ++ [b]) = (skipFlip2 false).delta (sf2End xs) b := by
  simp only [sf2End, runFwd_append, runFwd]

theorem sf2FlipParity_pair_snoc (n : Nat) (xs : List Bool) (b : Bool) :
    xor (sf2FlipParity n (xs ++ [b])) (sf2FlipParity n (xs ++ [!b])) = sf2FlipParity n xs := by
  induction n generalizing xs b with
  | zero => rfl
  | succ k ih =>
      simp only [sf2FlipParity]
      have hStep1 : skipFlip2Fwd (xs ++ [b]) = skipFlip2Fwd xs ++ [xor b (!(sf2End xs))] := by
        have := skipFlip2Fwd_iter_snoc 1 xs b
        simpa [iter, sf2FlipParity] using this
      have hStep2 : skipFlip2Fwd (xs ++ [!b]) = skipFlip2Fwd xs ++ [xor (!b) (!(sf2End xs))] := by
        have := skipFlip2Fwd_iter_snoc 1 xs (!b)
        simpa [iter, sf2FlipParity] using this
      have hComp : xor (!b) (!(sf2End xs)) = !(xor b (!(sf2End xs))) := by
        cases b <;> cases sf2End xs <;> rfl
      rw [hStep1, hStep2, hComp, sf2End_snoc, sf2End_snoc]
      have hPair := sf2_pair_xor (sf2End xs) b
      have hIH := ih (skipFlip2Fwd xs) (xor b (!(sf2End xs)))
      have hComm : ∀ u v y z : Bool, xor (xor u v) (xor y z) = xor (xor u y) (xor v z) := by
        intro u v y z; cases u <;> cases v <;> cases y <;> cases z <;> rfl
      rw [hComm, hPair, hIH]

/-- Simultaneous induction proving period `2^w` AND odd MSB-flip parity for ALL `w : Nat`. -/
theorem skipFlip2Fwd_full_cycle_aux (w : Nat) :
    ∀ xs : List Bool, xs.length = w →
      iter skipFlip2Fwd (2 ^ w) xs = xs ∧ sf2FlipParity (2 ^ w) xs = true := by
  induction w with
  | zero =>
      intro xs hlen
      cases xs with
      | nil => exact ⟨rfl, rfl⟩
      | cons _ _ => simp at hlen
  | succ k ih =>
      intro xs hlen
      rcases list_snoc_decomp xs hlen with ⟨pref, b, hDrop, hPrefLen⟩
      rw [hDrop]
      rcases ih pref hPrefLen with ⟨hPer, hPar⟩
      have hHalf : iter skipFlip2Fwd (2 ^ k) (pref ++ [b]) = pref ++ [!b] := by
        rw [skipFlip2Fwd_iter_snoc, hPer, hPar]
        cases b <;> rfl
      have hHalfNeg : iter skipFlip2Fwd (2 ^ k) (pref ++ [!b]) = pref ++ [b] := by
        rw [skipFlip2Fwd_iter_snoc, hPer, hPar]
        cases b <;> rfl
      have hPow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
        rw [Nat.pow_succ]; omega
      constructor
      · rw [hPow, iter_add, hHalf, hHalfNeg]
      · rw [hPow, sf2FlipParity_add, hHalf, sf2FlipParity_pair_snoc, hPar]

/--
**Theorem B (`skipFlip2_fwd_period_pow2` & `skipFlip2_fwd_half_ne`):**
For EVERY bit-width `w ≥ 1` and EVERY `x : BitVec w`, the forward skip-flip
transducer `F_2` has exact minimal order `2^w` (a single full `2^w`-cycle):
`(F_2)^{2^w}(x) = x` and `(F_2)^{2^{w-1}}(x) ≠ x` (specifically, it flips the MSB).
-/
theorem skipFlip2_fwd_period_pow2 {w : Nat} (x : BitVec w) :
    iter (fwdBV (skipFlip2 false)) (2 ^ w) x = x := by
  have hIter : ∀ n (y : BitVec w),
      toBits (iter (fwdBV (skipFlip2 false)) n y) = iter skipFlip2Fwd n (toBits y) := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ k ih =>
        intro y
        simp only [iter]
        rw [ih, fwdBV, toBits_liftBV]
        rfl
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hEq : toBits (iter (fwdBV (skipFlip2 false)) (2 ^ w) x) = toBits x := by
    rw [hIter, (skipFlip2Fwd_full_cycle_aux w (toBits x) (toBits_length x)).1]
  have hget := congrArg (fun l => l.getD i false) hEq
  simpa [toBits, List.getD_eq_getElem?_getD, hi] using hget

theorem skipFlip2_fwd_half_ne {w : Nat} (x : BitVec (w + 1)) :
    iter (fwdBV (skipFlip2 false)) (2 ^ w) x ≠ x := by
  have hIter : ∀ n (y : BitVec (w + 1)),
      toBits (iter (fwdBV (skipFlip2 false)) n y) = iter skipFlip2Fwd n (toBits y) := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ k ih =>
        intro y
        simp only [iter]
        rw [ih, fwdBV, toBits_liftBV]
        rfl
  intro hEq
  have hBits := congrArg toBits hEq
  rw [hIter] at hBits
  rcases list_snoc_decomp (toBits x) (toBits_length x) with ⟨pref, b, hDrop, hPrefLen⟩
  rcases skipFlip2Fwd_full_cycle_aux w pref hPrefLen with ⟨hPer, hPar⟩
  rw [hDrop, skipFlip2Fwd_iter_snoc, hPer, hPar] at hBits
  have hLast := congrArg (fun l => l.getD w false) hBits
  simp only [List.getD_eq_getElem?_getD] at hLast
  have hidx : (pref ++ [xor b true])[w]? = some (xor b true) := by
    rw [List.getElem?_append_right (by omega), hPrefLen]; simp
  have hidx2 : (pref ++ [b])[w]? = some b := by
    rw [List.getElem?_append_right (by omega), hPrefLen]; simp
  rw [hidx, hidx2] at hLast
  cases b <;> simp at hLast

/-! ### Section 4C: Sharpness (Exact Order 3) and Genuine Two-Way Non-Separability -/

theorem toBits_zero (w : Nat) : toBits (0 : BitVec w) = List.replicate w false := by
  apply List.ext_getElem
  · simp [toBits]
  · intro i h1 h2
    simp only [toBits, List.getElem_ofFn, List.getElem_replicate]
    simp [BitVec.getLsbD]

theorem skipFlip2Fwd_replicate_false (n : Nat) :
    runFwd (skipFlip2 false) false (List.replicate n false) = (List.replicate n true, false) := by
  induction n with
  | zero => rfl
  | succ k ih =>
      simp only [List.replicate_succ, runFwd]
      change (true :: (runFwd (skipFlip2 false) false (List.replicate k false)).1,
              (runFwd (skipFlip2 false) false (List.replicate k false)).2) = _
      rw [ih]

theorem runBwd_sf2_replicate_true (n : Nat) :
    runBwd (skipFlip2 false) false (List.replicate n true) =
      match n with
      | 0 => ([], false)
      | k + 1 =>
          let (os, q) := runBwd (skipFlip2 false) false (List.replicate k true)
          (q :: os, !q) := by
  cases n with
  | zero => rfl
  | succ k =>
      simp only [List.replicate_succ, runBwd]
      cases (runBwd (skipFlip2 false) false (List.replicate k true)).2 <;>
        simp [skipFlip2]

theorem runBwd_sf2_replicate_true_state (n : Nat) :
    (runBwd (skipFlip2 false) false (List.replicate n true)).2 = (n % 2 == 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [runBwd_sf2_replicate_true]
      simp only [ih]
      cases h : k % 2 with
      | zero => simp [Nat.add_mod, h]
      | succ r =>
          have hr : r = 0 := by omega
          subst hr
          simp [Nat.add_mod, h]

theorem runBwd_sf2_replicate_true_second_msb (k : Nat) :
    (runBwd (skipFlip2 false) false (List.replicate (k + 2) true)).1.getD k false = true := by
  induction k with
  | zero => rfl
  | succ j ih =>
      have hstep := runBwd_sf2_replicate_true (j + 3)
      simp only [hstep, List.getD_cons_succ]
      exact ih

/--
**Theorem A2 (`skipFlip2_zero_not_fixed`):**
For EVERY `w ≥ 2`, `T_2(0) ≠ 0`. Combined with `T_2^3 = id` (prime order 3),
the exact minimal order of `T_2` on `BitVec w` is **3** for all `w ≥ 2`.
-/
theorem skipFlip2_zero_not_fixed (k : Nat) :
    skipFlip2TwoWay (0 : BitVec (k + 2)) ≠ (0 : BitVec (k + 2)) := by
  intro hEq
  have hBits := congrArg toBits hEq
  have hZero := toBits_zero (k + 2)
  simp only [skipFlip2TwoWay, twoWayBV, fwdBV, bwdBV, toBits_liftBV, hZero] at hBits
  change (runBwd (skipFlip2 false) false (runFwd (skipFlip2 false) false (List.replicate (k + 2) false)).1).1 = _ at hBits
  rw [skipFlip2Fwd_replicate_false] at hBits
  have hGet := congrArg (fun l => l.getD k false) hBits
  rw [runBwd_sf2_replicate_true_second_msb k] at hGet
  have hRHS : (List.replicate (k + 2) false).getD k false = false := by
    rw [List.getD_eq_getElem?_getD]
    have hlt : k < (List.replicate (k + 2) false).length := by simp
    rw [List.getElem?_eq_getElem hlt]; simp
  rw [hRHS] at hGet
  cases hGet

/--
**Theorem C1 (`skipFlip2_msb_influences_lsb`):**
For EVERY `w ≥ 2`, flipping the MSB (`0` vs `2^{w-1}`) flips bit 0 (LSB) of `T_2(x)`.
-/
theorem skipFlip2_msb_influences_lsb (k : Nat) :
    let w := k + 2
    let x0 : BitVec w := 0
    let x1 : BitVec w := BitVec.ofNat w (2 ^ (k + 1))
    (skipFlip2TwoWay x0).getLsbD 0 ≠ (skipFlip2TwoWay x1).getLsbD 0 := by
  intro w x0 x1
  have h0 : toBits x0 = List.replicate (k + 2) false := toBits_zero w
  have h1 : toBits x1 = List.replicate (k + 1) false ++ [true] := by
    apply List.ext_getElem
    · simp [toBits, x1, w]
    · intro i h1' h2'
      have hiw : i < w := by rw [toBits_length] at h1'; exact h1'
      simp only [toBits, List.getElem_ofFn, x1, BitVec.getLsbD, BitVec.toNat_ofNat]
      have hmod : 2 ^ (k + 1) % 2 ^ w = 2 ^ (k + 1) :=
        Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))
      rw [hmod, Nat.testBit_two_pow]
      by_cases hi : i < k + 1
      · rw [List.getElem_append_left (by simp; omega), List.getElem_replicate]
        have hne : k + 1 ≠ i := by omega
        simp [hne]
      · have heq : i = k + 1 := by omega
        subst heq
        rw [List.getElem_append_right (by simp)]
        simp
  have hFwd0 : (runFwd (skipFlip2 false) false (toBits x0)).1 = List.replicate (k + 2) true := by
    rw [h0, skipFlip2Fwd_replicate_false]
  have hFwd1 : (runFwd (skipFlip2 false) false (toBits x1)).1 = List.replicate (k + 1) true ++ [false] := by
    rw [h1, runFwd_append, skipFlip2Fwd_replicate_false]
    rfl
  have hBwd0 : (runBwd (skipFlip2 false) false (List.replicate (k + 2) true)).1.getD 0 false
      = ((k + 1) % 2 == 1) := by
    rw [runBwd_sf2_replicate_true]
    simp only [List.getD_cons_zero]
    exact runBwd_sf2_replicate_true_state (k + 1)
  have hBwd1_aux : ∀ m, (runBwd (skipFlip2 false) false (List.replicate m true ++ [false])) =
      let (os, q) := runBwd (skipFlip2 false) false (List.replicate m true)
      (os ++ [true], q) := by
    intro m
    induction m with
    | zero => rfl
    | succ j ih =>
        simp only [List.replicate_succ, List.cons_append, runBwd, ih]
  have hBwd1 : (runBwd (skipFlip2 false) false (List.replicate (k + 1) true ++ [false])).1.getD 0 false
      = (k % 2 == 1) := by
    rw [hBwd1_aux]
    simp only []
    have hstep := runBwd_sf2_replicate_true (k + 1)
    rw [hstep]
    simp only [List.cons_append, List.getD_cons_zero]
    exact runBwd_sf2_replicate_true_state k
  have hGet0 : ∀ (y : BitVec w), y.getLsbD 0 = (toBits y).getD 0 false := by
    intro y
    rw [List.getD_eq_getElem?_getD]
    have hlt : 0 < (toBits y).length := by rw [toBits_length]; omega
    rw [List.getElem?_eq_getElem hlt]
    simp only [Option.getD_some, toBits, List.getElem_ofFn]
  rw [hGet0, hGet0]
  have hT0 : toBits (skipFlip2TwoWay x0) = (runBwd (skipFlip2 false) false (List.replicate (k + 2) true)).1 := by
    simp only [skipFlip2TwoWay, twoWayBV, fwdBV, bwdBV, toBits_liftBV]
    change (runBwd (skipFlip2 false) false (runFwd (skipFlip2 false) false (toBits x0)).1).1 = _
    rw [hFwd0]
  have hT1 : toBits (skipFlip2TwoWay x1) = (runBwd (skipFlip2 false) false (List.replicate (k + 1) true ++ [false])).1 := by
    simp only [skipFlip2TwoWay, twoWayBV, fwdBV, bwdBV, toBits_liftBV]
    change (runBwd (skipFlip2 false) false (runFwd (skipFlip2 false) false (toBits x1)).1).1 = _
    rw [hFwd1]
  rw [hT0, hT1, hBwd0, hBwd1]
  cases h : k % 2 with
  | zero => simp [Nat.add_mod, h]
  | succ r =>
      have hr : r = 0 := by omega
      subst hr
      simp [Nat.add_mod, h]

theorem runFwd_sf2_replicate_true_last (n : Nat) :
    (runFwd (skipFlip2 false) false (List.replicate (n + 1) true)).1.getD n false = (n % 2 == 1) := by
  have hState : ∀ m q,
      (runFwd (skipFlip2 false) q (List.replicate (m + 1) true)).1.getD m false =
      if q then (m % 2 == 0) else (m % 2 == 1) := by
    intro m
    induction m with
    | zero => intro q; cases q <;> rfl
    | succ j ih =>
        intro q
        have hstep : (runFwd (skipFlip2 false) q (List.replicate (j + 2) true)).1 =
            (true != !q) :: (runFwd (skipFlip2 false) (!q && true) (List.replicate (j + 1) true)).1 := rfl
        rw [hstep, List.getD_cons_succ, ih (!q && true)]
        cases q with
        | false =>
            cases h : j % 2 with
            | zero => simp [Nat.add_mod, h]
            | succ r =>
                have hr : r = 0 := by omega
                subst hr
                simp [Nat.add_mod, h]
        | true =>
            cases h : j % 2 with
            | zero => simp [Nat.add_mod, h]
            | succ r =>
                have hr : r = 0 := by omega
                subst hr
                simp [Nat.add_mod, h]
  simpa using hState n false

theorem runBwd_sf2_last_bit (xs : List Bool) (b : Bool) :
    (runBwd (skipFlip2 false) false (xs ++ [b])).1.getD xs.length false = !b := by
  induction xs with
  | nil => cases b <;> rfl
  | cons a as ih =>
      simp only [List.cons_append, List.length_cons, runBwd, List.getD_cons_succ]
      exact ih

/--
**Theorem C2 (`skipFlip2_lsb_influences_msb`):**
For EVERY `w ≥ 2`, flipping bit 0 (LSB) (`allOnes` vs `allOnes ^^^ 1`) flips bit `w-1` (MSB) of `T_2(x)`.
Together with `skipFlip2_msb_influences_lsb`, `T_2` is provably strictly two-way.
-/
theorem skipFlip2_lsb_influences_msb (k : Nat) :
    let w := k + 2
    let xAll : BitVec w := BitVec.allOnes w
    let xFlp : BitVec w := BitVec.allOnes w ^^^ 1#w
    (skipFlip2TwoWay xAll).getLsbD (k + 1) ≠ (skipFlip2TwoWay xFlp).getLsbD (k + 1) := by
  intro w xAll xFlp
  have hAll : toBits xAll = List.replicate (k + 2) true := by
    apply List.ext_getElem
    · simp [toBits, xAll, w]
    · intro i h1 h2
      have hi : i < w := by rw [toBits_length] at h1; exact h1
      simp only [toBits, List.getElem_ofFn, List.getElem_replicate, xAll, BitVec.getLsbD_allOnes]
      exact decide_eq_true hi
  have hFlp : toBits xFlp = false :: List.replicate (k + 1) true := by
    apply List.ext_getElem
    · simp [toBits, xFlp, w]
    · intro i h1 h2
      have hi : i < w := by rw [toBits_length] at h1; exact h1
      cases i with
      | zero => simp [toBits, xFlp, w]
      | succ j =>
          simp only [toBits, List.getElem_ofFn, List.getElem_cons_succ, List.getElem_replicate,
            xFlp, BitVec.getLsbD_xor, BitVec.getLsbD_allOnes]
          have h1mod : (1#w).toNat = 1 := by
            simp only [BitVec.toNat_ofNat]
            exact Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
          have hbit : (1#w).getLsbD (j + 1) = false := by
            change (1#w).toNat.testBit (j + 1) = false
            rw [h1mod, Nat.testBit_succ]
            simp
          rw [hbit, decide_eq_true hi]
          rfl
  have hGetMsb : ∀ (y : BitVec w), y.getLsbD (k + 1) = (toBits y).getD (k + 1) false := by
    intro y
    rw [List.getD_eq_getElem?_getD]
    have hlt : k + 1 < (toBits y).length := by rw [toBits_length]; omega
    rw [List.getElem?_eq_getElem hlt]
    simp only [Option.getD_some, toBits, List.getElem_ofFn]
  rw [hGetMsb, hGetMsb]
  have hTAll : toBits (skipFlip2TwoWay xAll) =
      (runBwd (skipFlip2 false) false (runFwd (skipFlip2 false) false (List.replicate (k + 2) true)).1).1 := by
    simp only [skipFlip2TwoWay, twoWayBV, fwdBV, bwdBV, toBits_liftBV, hAll]
    rfl
  have hTFlp : toBits (skipFlip2TwoWay xFlp) =
      (runBwd (skipFlip2 false) false (runFwd (skipFlip2 false) false (false :: List.replicate (k + 1) true)).1).1 := by
    simp only [skipFlip2TwoWay, twoWayBV, fwdBV, bwdBV, toBits_liftBV, hFlp]
    rfl
  rw [hTAll, hTFlp]
  have hBwdMsb : ∀ (ys : List Bool), ys.length = k + 2 →
      (runBwd (skipFlip2 false) false ys).1.getD (k + 1) false = !(ys.getD (k + 1) false) := by
    intro ys hlen
    rcases list_snoc_decomp ys hlen with ⟨pref, b, hDrop, hDL⟩
    rw [hDrop, ← hDL, runBwd_sf2_last_bit]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hDL]
    simp
  rw [hBwdMsb _ (by rw [runFwd_length]; simp), hBwdMsb _ (by rw [runFwd_length]; simp)]
  rw [runFwd_sf2_replicate_true_last (k + 1)]
  have hFwdFlp : (runFwd (skipFlip2 false) false (false :: List.replicate (k + 1) true)).1.getD (k + 1) false
      = (k % 2 == 1) := by
    simp only [runFwd, skipFlip2, Bool.not_false, Bool.true_and, Bool.false_bne, List.getD_cons_succ]
    exact runFwd_sf2_replicate_true_last k
  rw [hFwdFlp]
  cases h : k % 2 with
  | zero => simp [Nat.add_mod, h]
  | succ r =>
      have hr : r = 0 := by omega
      subst hr
      simp [Nat.add_mod, h]

/-! ## Section 5: Infinite Parametric Family (`∀ m ≥ 2`, `k = m + 1` States) — Run-Triggered Coxeter-6 Collapse -/

/-- Exact factorization `B_m ∘ F_m = R_m ∘ S_m` for ALL `m` and ALL bit-lists. -/
theorem runSkipFlip_fwd_eq_not_S (m q : Nat) (xs : List Bool) :
    runFwd (runSkipFlip m) q xs =
      ((runFwd (runTriggerS m) q xs).1.map (!·), (runFwd (runTriggerS m) q xs).2) := by
  induction xs generalizing q with
  | nil => rfl
  | cons b bs ih =>
      simp only [runFwd, List.map_cons]
      have hDel : (runSkipFlip m).delta q b = (runTriggerS m).delta q b := rfl
      have hOut : (runSkipFlip m).out q b = !((runTriggerS m).out q b) := by
        simp only [runSkipFlip, runTriggerS]; split <;> cases b <;> rfl
      rw [hDel, hOut, ih]

theorem runSkipFlip_bwd_not_eq_R (m q : Nat) (xs : List Bool) :
    runBwd (runSkipFlip m) q (xs.map (!·)) = runBwd (runTriggerR m) q xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
      simp only [List.map_cons, runBwd, ih]
      have hOut : ∀ s : Nat, (runSkipFlip m).out s (!b) = (runTriggerR m).out s b := by
        intro s; simp only [runSkipFlip, runTriggerR]; split <;> cases b <;> rfl
      have hDel : ∀ s : Nat, (runSkipFlip m).delta s (!b) = (runTriggerR m).delta s b := by
        intro s; simp only [runSkipFlip, runTriggerR]; split <;> cases b <;> rfl
      rw [hOut, hDel]

theorem runSkipFlip_twoWay_eq_runTrigger (m : Nat) {w : Nat} (x : BitVec w) :
    twoWayBV (runSkipFlip m) (runSkipFlip m) x = runTriggerTwoWay m x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hEq : toBits (twoWayBV (runSkipFlip m) (runSkipFlip m) x) =
      toBits (runTriggerTwoWay m x) := by
    simp only [twoWayBV, runTriggerTwoWay, fwdBV, bwdBV, toBits_liftBV]
    change (runBwd (runSkipFlip m) 0 (runFwd (runSkipFlip m) 0 (toBits x)).1).1 =
           (runBwd (runTriggerR m) 0 (runFwd (runTriggerS m) 0 (toBits x)).1).1
    rw [runSkipFlip_fwd_eq_not_S, runSkipFlip_bwd_not_eq_R]
  have hget := congrArg (fun l => l.getD i false) hEq
  simpa [toBits, List.getD_eq_getElem?_getD, hi] using hget

/-- `S_m` is an involution (`S_m ∘ S_m = id`) for ALL `m` and ALL widths `w`. -/
theorem runTriggerS_invol_list (m q : Nat) (xs : List Bool) :
    runFwd (runTriggerS m) q (runFwd (runTriggerS m) q xs).1 =
      (xs, (runFwd (runTriggerS m) q xs).2) := by
  induction xs generalizing q with
  | nil => rfl
  | cons b bs ih =>
      simp only [runFwd]
      have hOut : (runTriggerS m).out q ((runTriggerS m).out q b) = b := by
        simp only [runTriggerS]; split <;> cases b <;> rfl
      have hDel : (runTriggerS m).delta q ((runTriggerS m).out q b) = (runTriggerS m).delta q b := by
        simp only [runTriggerS]; split <;> cases b <;> rfl
      rw [hOut, hDel, ih]

/-- `R_m` is an involution (`R_m ∘ R_m = id`) for ALL `m` and ALL widths `w`. -/
theorem runTriggerR_invol_list (m q : Nat) (xs : List Bool) :
    runBwd (runTriggerR m) q (runBwd (runTriggerR m) q xs).1 =
      (xs, (runBwd (runTriggerR m) q xs).2) := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
      simp only [runBwd, ih]
      have hOut : ∀ s, (runTriggerR m).out s ((runTriggerR m).out s b) = b := by
        intro s; simp only [runTriggerR]; split <;> cases b <;> rfl
      have hDel : ∀ s, (runTriggerR m).delta s ((runTriggerR m).out s b) = (runTriggerR m).delta s b := by
        intro s; simp only [runTriggerR]; split <;> cases b <;> rfl
      rw [hOut, hDel]

/-- Two-way bijectivity of `T_m = R_m ∘ S_m` with reverse-order inverse `S_m ∘ R_m`. -/
theorem runTriggerTwoWay_left_inv (m : Nat) {w : Nat} (x : BitVec w) :
    fwdBV (runTriggerS m) (bwdBV (runTriggerR m) (runTriggerTwoWay m x)) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hEq : toBits (fwdBV (runTriggerS m) (bwdBV (runTriggerR m) (runTriggerTwoWay m x))) = toBits x := by
    simp only [runTriggerTwoWay, twoWayBV, fwdBV, bwdBV, toBits_liftBV]
    change (runFwd (runTriggerS m) 0
      (runBwd (runTriggerR m) 0
        (runBwd (runTriggerR m) 0
          (runFwd (runTriggerS m) 0 (toBits x)).1).1).1).1 = toBits x
    rw [runTriggerR_invol_list, runTriggerS_invol_list]
  have hget := congrArg (fun l => l.getD i false) hEq
  simpa [toBits, List.getD_eq_getElem?_getD, hi] using hget

/-! ### Section 5B: Symbolic `(2m + 1)`-State Witness Automaton Proving `T_m^6 = id` (`∀ m ≥ 2, ∀ w`) -/

/-- Single `(S_m, R_m)` pair transition helper for `TileStep`. -/
theorem tileStep_SR_pair (m sL tL sR tR : Nat) (b outNext : Bool)
    (sws : List (Sweep Nat)) (cL cR : List Nat)
    (hS : (runTriggerS m).delta sL b = sR)
    (hR : (runTriggerR m).delta tR ((runTriggerS m).out sL b) = tL)
    (hRest : TileStep sws cL cR ((runTriggerR m).out tR ((runTriggerS m).out sL b)) outNext) :
    TileStep (⟨.fwd, runTriggerS m⟩ :: ⟨.bwd, runTriggerR m⟩ :: sws)
      (sL :: tL :: cL) (sR :: tR :: cR) b outNext :=
  ⟨hS, hR, hRest⟩

/-- Helper: 6-fold uniform pair step (same `(sL, tL, sR, tR)` in all 6 slots with fixed bit `b`). -/
theorem tileStep_sync6 (m sL tL sR tR : Nat) (b : Bool)
    (hS : (runTriggerS m).delta sL b = sR)
    (hR : (runTriggerR m).delta tR ((runTriggerS m).out sL b) = tL)
    (hB : (runTriggerR m).out tR ((runTriggerS m).out sL b) = b) :
    TileStep (runTriggerSweeps6 m) (cSync sL tL) (cSync sR tR) b b := by
  unfold runTriggerSweeps6 cSync mkCross
  refine ⟨hS, hR, ?_⟩; rw [hB]
  refine ⟨hS, hR, ?_⟩; rw [hB]
  refine ⟨hS, hR, ?_⟩; rw [hB]
  refine ⟨hS, hR, ?_⟩; rw [hB]
  refine ⟨hS, hR, ?_⟩; rw [hB]
  refine ⟨hS, hR, ?_⟩; rw [hB]; rfl

/-- Helper: period-2 alternating pair step (repeats 3 times across the 6 slots). -/
theorem tileStep_alt2_6 (m sL0 tL0 sR0 tR0 sL1 tL1 sR1 tR1 : Nat) (b b1 : Bool)
    (hS0 : (runTriggerS m).delta sL0 b = sR0)
    (hR0 : (runTriggerR m).delta tR0 ((runTriggerS m).out sL0 b) = tL0)
    (hB0 : (runTriggerR m).out tR0 ((runTriggerS m).out sL0 b) = b1)
    (hS1 : (runTriggerS m).delta sL1 b1 = sR1)
    (hR1 : (runTriggerR m).delta tR1 ((runTriggerS m).out sL1 b1) = tL1)
    (hB1 : (runTriggerR m).out tR1 ((runTriggerS m).out sL1 b1) = b) :
    TileStep (runTriggerSweeps6 m)
      (mkCross sL0 sL1 sL0 sL1 sL0 sL1 tL0 tL1 tL0 tL1 tL0 tL1)
      (mkCross sR0 sR1 sR0 sR1 sR0 sR1 tR0 tR1 tR0 tR1 tR0 tR1) b b := by
  unfold runTriggerSweeps6 mkCross
  refine ⟨hS0, hR0, ?_⟩; rw [hB0]
  refine ⟨hS1, hR1, ?_⟩; rw [hB1]
  refine ⟨hS0, hR0, ?_⟩; rw [hB0]
  refine ⟨hS1, hR1, ?_⟩; rw [hB1]
  refine ⟨hS0, hR0, ?_⟩; rw [hB0]
  refine ⟨hS1, hR1, ?_⟩; rw [hB1]; rfl

/-- Helper: period-3 cyclic pair step (repeats twice across the 6 slots). -/
theorem tileStep_cyc3_6 (m sL0 tL0 sR0 tR0 sL1 tL1 sR1 tR1 sL2 tL2 sR2 tR2 : Nat)
    (b b1 b2 : Bool)
    (hS0 : (runTriggerS m).delta sL0 b = sR0)
    (hR0 : (runTriggerR m).delta tR0 ((runTriggerS m).out sL0 b) = tL0)
    (hB0 : (runTriggerR m).out tR0 ((runTriggerS m).out sL0 b) = b1)
    (hS1 : (runTriggerS m).delta sL1 b1 = sR1)
    (hR1 : (runTriggerR m).delta tR1 ((runTriggerS m).out sL1 b1) = tL1)
    (hB1 : (runTriggerR m).out tR1 ((runTriggerS m).out sL1 b1) = b2)
    (hS2 : (runTriggerS m).delta sL2 b2 = sR2)
    (hR2 : (runTriggerR m).delta tR2 ((runTriggerS m).out sL2 b2) = tL2)
    (hB2 : (runTriggerR m).out tR2 ((runTriggerS m).out sL2 b2) = b) :
    TileStep (runTriggerSweeps6 m)
      (mkCross sL0 sL1 sL2 sL0 sL1 sL2 tL0 tL1 tL2 tL0 tL1 tL2)
      (mkCross sR0 sR1 sR2 sR0 sR1 sR2 tR0 tR1 tR2 tR0 tR1 tR2) b b := by
  unfold runTriggerSweeps6 mkCross
  refine ⟨hS0, hR0, ?_⟩; rw [hB0]
  refine ⟨hS1, hR1, ?_⟩; rw [hB1]
  refine ⟨hS2, hR2, ?_⟩; rw [hB2]
  refine ⟨hS0, hR0, ?_⟩; rw [hB0]
  refine ⟨hS1, hR1, ?_⟩; rw [hB1]
  refine ⟨hS2, hR2, ?_⟩; rw [hB2]; rfl

theorem symW_len (m : Nat) (mac : SymMacro m) (c : List Nat) (h : SymW m mac c) :
    c.length = (runTriggerSweeps6 m).length := by
  cases mac with
  | start => rcases h with ⟨b, _, rfl⟩; rfl
  | afterZero r hr =>
      rcases h with ⟨b, _, rfl⟩ | h2
      · rfl
      · split at h2 <;> subst h2 <;> rfl
  | inOnes r h1 h2 =>
      simp only [SymW] at h
      split at h
      · rcases h with ⟨b, _, rfl⟩ | rfl <;> rfl
      · rcases h with rfl | rfl | rfl | ⟨a, _, _, rfl | rfl⟩ <;> rfl

theorem symW_init (m : Nat) (c : List Nat) (h : SymW m .start c) :
    LeftBoundary (runTriggerSweeps6 m) c := by
  rcases h with ⟨b, _, rfl⟩
  simp [runTriggerSweeps6, cSync, mkCross, LeftBoundary, runTriggerS]

theorem symW_final (m : Nat) (hm : 2 ≤ m) (mac : SymMacro m) :
    ∃ cR, SymW m mac cR ∧ RightBoundary (runTriggerSweeps6 m) cR := by
  cases mac with
  | start =>
      exact ⟨cSync 0 0, ⟨0, by omega, rfl⟩, by simp [runTriggerSweeps6, cSync, mkCross, RightBoundary, runTriggerR]⟩
  | afterZero r hr =>
      exact ⟨cSync 0 0, Or.inl ⟨0, by omega, rfl⟩, by simp [runTriggerSweeps6, cSync, mkCross, RightBoundary, runTriggerR]⟩
  | inOnes r h1 h2 =>
      by_cases hr : r < m
      · refine ⟨cSync r 0, ?_, by simp [runTriggerSweeps6, cSync, mkCross, RightBoundary, runTriggerR]⟩
        simp only [SymW, hr, ite_true]
        exact Or.inl ⟨0, by omega, rfl⟩
      · refine ⟨cSync m 0, ?_, by simp [runTriggerSweeps6, cSync, mkCross, RightBoundary, runTriggerR]⟩
        simp [SymW, hr]

/-- Core symbolic tile-verification lemma covering ALL `m ≥ 2` simultaneously! -/
theorem symW_step (m : Nat) (hm : 2 ≤ m) (mac : SymMacro m) (b : Bool) (cR : List Nat)
    (hR : SymW m (symNext m hm mac b) cR) :
    ∃ cL, SymW m mac cL ∧ TileStep (runTriggerSweeps6 m) cL cR b b := by
  have hm0 : 0 < m := by omega
  have hStep_sync_0 : ∀ s t, s < m → t < m →
      TileStep (runTriggerSweeps6 m) (cSync s (t + 1)) (cSync 0 t) false false := by
    intro s t hs ht
    exact tileStep_sync6 m s (t + 1) 0 t false
      (by simp [runTriggerS, hs]) (by simp [runTriggerS, runTriggerR, hs, ht])
      (by simp [runTriggerS, runTriggerR, hs, ht])
  have hStep_altL_0_from_sync : ∀ s, s < m → s + 1 < m →
      TileStep (runTriggerSweeps6 m) (cSync s 0) (cAltL 0 (s + 1) m) false false := by
    intro s hs hs1
    exact tileStep_alt2_6 m s 0 0 m s 0 (s + 1) m false true
      (by simp [runTriggerS, hs]) (by simp [runTriggerS, runTriggerR, hs])
      (by simp [runTriggerS, runTriggerR, hs])
      (by simp [runTriggerS, hs]) (by simp [runTriggerS, runTriggerR, hs])
      (by simp [runTriggerS, runTriggerR, hs])
  have hStep_cyc0_from_sync :
      TileStep (runTriggerSweeps6 m) (cSync (m - 1) 0) (cCyc0 m) false false := by
    have hm1 : m - 1 < m := by omega
    have hmEq : m - 1 + 1 = m := by omega
    exact tileStep_cyc3_6 m (m - 1) 0 0 m (m - 1) 0 m 0 (m - 1) 0 m m false true true
      (by simp [runTriggerS, hm1]) (by simp [runTriggerS, runTriggerR, hm1])
      (by simp [runTriggerS, runTriggerR, hm1])
      (by simp [runTriggerS, hm1, hmEq]) (by simp [runTriggerS, runTriggerR, hm1, hm0])
      (by simp [runTriggerS, runTriggerR, hm1, hm0])
      (by simp [runTriggerS, hm1, hmEq]) (by simp [runTriggerS, runTriggerR, hm1])
      (by simp [runTriggerS, runTriggerR, hm1])
  have hStep_sync_0_from_altL : ∀ s1 s2, s1 < m → s2 < m →
      TileStep (runTriggerSweeps6 m) (cAltL s1 s2 m) (cSync 0 (m - 1)) false false := by
    intro s1 s2 hs1 hs2
    have hm1 : m - 1 < m := by omega
    have hmEq : m - 1 + 1 = m := by omega
    exact tileStep_alt2_6 m s1 m 0 (m - 1) s2 m 0 (m - 1) false false
      (by simp [runTriggerS, hs1]) (by simp [runTriggerS, runTriggerR, hs1, hm1, hmEq])
      (by simp [runTriggerS, runTriggerR, hs1, hm1])
      (by simp [runTriggerS, hs2]) (by simp [runTriggerS, runTriggerR, hs2, hm1, hmEq])
      (by simp [runTriggerS, runTriggerR, hs2, hm1])
  have hStep_sync_0_from_cyc0 :
      TileStep (runTriggerSweeps6 m) (cCyc0 m) (cSync 0 (m - 1)) false false := by
    have hm1 : m - 1 < m := by omega
    have hmEq : m - 1 + 1 = m := by omega
    exact tileStep_cyc3_6 m 0 m 0 (m - 1) m 0 0 (m - 1) m m 0 (m - 1) false false true
      (by simp [runTriggerS, hm0]) (by simp [runTriggerS, runTriggerR, hm0, hm1, hmEq])
      (by simp [runTriggerS, runTriggerR, hm0, hm1])
      (by simp [runTriggerS]) (by simp [runTriggerS, runTriggerR, hm1])
      (by simp [runTriggerS, runTriggerR, hm1])
      (by simp [runTriggerS]) (by simp [runTriggerS, runTriggerR, hm1, hmEq])
      (by simp [runTriggerS, runTriggerR, hm1])
  have hStep_one_sync : ∀ s t, s < m → t < m →
      TileStep (runTriggerSweeps6 m) (cSync s 0) (cSync (s + 1) t) true true := by
    intro s t hs ht
    exact tileStep_sync6 m s 0 (s + 1) t true
      (by simp [runTriggerS, hs]) (by simp [runTriggerS, runTriggerR, hs, ht])
      (by simp [runTriggerS, runTriggerR, hs, ht])
  have hStep_one_altL : ∀ s, s < m →
      TileStep (runTriggerSweeps6 m) (cSync s 0) (cAltL (s + 1) 0 m) true true := by
    intro s hs
    exact tileStep_alt2_6 m s 0 (s + 1) m s 0 0 m true false
      (by simp [runTriggerS, hs]) (by simp [runTriggerS, runTriggerR, hs])
      (by simp [runTriggerS, runTriggerR, hs])
      (by simp [runTriggerS, hs]) (by simp [runTriggerS, runTriggerR, hs])
      (by simp [runTriggerS, runTriggerR, hs])
  cases mac with
  | start =>
      cases b with
      | false =>
          simp only [symNext, SymW] at hR
          rcases hR with ⟨t, ht, rfl⟩ | h2
          · exact ⟨cSync 0 (t + 1), ⟨t + 1, by omega, rfl⟩, hStep_sync_0 0 t hm0 ht⟩
          · have h1m : 0 + 1 < m := by omega
            simp only [h1m, ite_true] at h2; subst h2
            exact ⟨cSync 0 0, ⟨0, by omega, rfl⟩, hStep_altL_0_from_sync 0 hm0 h1m⟩
      | true =>
          have h1m : 1 < m := by omega
          simp only [symNext, SymW, h1m, ite_true] at hR
          rcases hR with ⟨t, ht, rfl⟩ | rfl
          · exact ⟨cSync 0 0, ⟨0, by omega, rfl⟩, hStep_one_sync 0 t hm0 ht⟩
          · exact ⟨cSync 0 0, ⟨0, by omega, rfl⟩, hStep_one_altL 0 hm0⟩
  | afterZero r hr =>
      cases b with
      | false =>
          simp only [symNext, SymW] at hR
          rcases hR with ⟨t, ht, rfl⟩ | h2
          · by_cases ht1 : t + 1 < m
            · exact ⟨cSync 0 (t + 1), Or.inl ⟨t + 1, ht1, rfl⟩, hStep_sync_0 0 t hm0 ht⟩
            · have htEq : t = m - 1 := by omega
              subst htEq
              by_cases hr1 : r + 1 < m
              · refine ⟨cAltL 0 (r + 1) m, Or.inr (by simp [hr1]), ?_⟩
                exact hStep_sync_0_from_altL 0 (r + 1) hm0 hr1
              · refine ⟨cCyc0 m, Or.inr (by simp [hr1]), hStep_sync_0_from_cyc0⟩
          · have h1m : 0 + 1 < m := by omega
            simp only [h1m, ite_true] at h2; subst h2
            exact ⟨cSync 0 0, Or.inl ⟨0, hm0, rfl⟩, hStep_altL_0_from_sync 0 hm0 h1m⟩
      | true =>
          have h1m : 1 < m := by omega
          simp only [symNext, SymW, h1m, ite_true] at hR
          rcases hR with ⟨t, ht, rfl⟩ | rfl
          · exact ⟨cSync 0 0, Or.inl ⟨0, hm0, rfl⟩, hStep_one_sync 0 t hm0 ht⟩
          · exact ⟨cSync 0 0, Or.inl ⟨0, hm0, rfl⟩, hStep_one_altL 0 hm0⟩
  | inOnes r h1 h2 =>
      by_cases hr : r < m
      · cases b with
        | false =>
            simp only [symNext, hr, dite_true, Bool.false_eq_true, ite_false, SymW] at hR
            rcases hR with ⟨t, ht, rfl⟩ | hAlt
            · by_cases ht1 : t + 1 < m
              · refine ⟨cSync r (t + 1), ?_, hStep_sync_0 r t hr ht⟩
                simp only [SymW, hr, ite_true]; exact Or.inl ⟨t + 1, ht1, rfl⟩
              · have htEq : t = m - 1 := by omega
                subst htEq
                refine ⟨cAltL r 0 m, by simp [SymW, hr], hStep_sync_0_from_altL r 0 hr hm0⟩
            · by_cases hr1 : r + 1 < m
              · simp only [hr1, ite_true] at hAlt; subst hAlt
                refine ⟨cSync r 0, ?_, hStep_altL_0_from_sync r hr hr1⟩
                simp only [SymW, hr, ite_true]; exact Or.inl ⟨0, hm0, rfl⟩
              · simp only [hr1, ite_false] at hAlt; subst hAlt
                have hrEq : r = m - 1 := by omega
                subst hrEq
                refine ⟨cSync (m - 1) 0, ?_, hStep_cyc0_from_sync⟩
                simp only [SymW, hr, ite_true]; exact Or.inl ⟨0, hm0, rfl⟩
        | true =>
            simp only [symNext, hr, dite_true, ite_true] at hR
            by_cases hr1 : r + 1 < m
            · simp only [SymW, hr1, ite_true] at hR
              rcases hR with ⟨t, ht, rfl⟩ | rfl
              · refine ⟨cSync r 0, ?_, hStep_one_sync r t hr ht⟩
                simp only [SymW, hr, ite_true]; exact Or.inl ⟨0, hm0, rfl⟩
              · refine ⟨cSync r 0, ?_, hStep_one_altL r hr⟩
                simp only [SymW, hr, ite_true]; exact Or.inl ⟨0, hm0, rfl⟩
            · simp only [SymW, hr1, ite_false] at hR
              have hrEq : r + 1 = m := by omega
              refine ⟨cSync r 0, ?_, ?_⟩
              · simp only [SymW, hr, ite_true]; exact Or.inl ⟨0, hm0, rfl⟩
              · rcases hR with rfl | rfl | rfl | ⟨a, ha1, ham, rfl | rfl⟩
                · exact tileStep_sync6 m r 0 m 0 true
                    (by simp [runTriggerS, hr, hrEq]) (by simp [runTriggerS, runTriggerR, hr, hm0])
                    (by simp [runTriggerS, runTriggerR, hr, hm0])
                · exact tileStep_cyc3_6 m r 0 m m r 0 0 m r 0 m 0 true false true
                    (by simp [runTriggerS, hr, hrEq]) (by simp [runTriggerS, runTriggerR, hr])
                    (by simp [runTriggerS, runTriggerR, hr])
                    (by simp [runTriggerS, hr]) (by simp [runTriggerS, runTriggerR, hr])
                    (by simp [runTriggerS, runTriggerR, hr])
                    (by simp [runTriggerS, hr, hrEq]) (by simp [runTriggerS, runTriggerR, hr, hm0])
                    (by simp [runTriggerS, runTriggerR, hr, hm0])
                · exact tileStep_cyc3_6 m r 0 m 0 r 0 m m r 0 0 m true true false
                    (by simp [runTriggerS, hr, hrEq]) (by simp [runTriggerS, runTriggerR, hr, hm0])
                    (by simp [runTriggerS, runTriggerR, hr, hm0])
                    (by simp [runTriggerS, hr, hrEq]) (by simp [runTriggerS, runTriggerR, hr])
                    (by simp [runTriggerS, runTriggerR, hr])
                    (by simp [runTriggerS, hr]) (by simp [runTriggerS, runTriggerR, hr])
                    (by simp [runTriggerS, runTriggerR, hr])
                · exact tileStep_alt2_6 m r 0 m 0 r 0 m a true true
                    (by simp [runTriggerS, hr, hrEq]) (by simp [runTriggerS, runTriggerR, hr, hm0])
                    (by simp [runTriggerS, runTriggerR, hr, hm0])
                    (by simp [runTriggerS, hr, hrEq]) (by simp [runTriggerS, runTriggerR, hr, ham])
                    (by simp [runTriggerS, runTriggerR, hr, ham])
                · exact tileStep_alt2_6 m r 0 m a r 0 m 0 true true
                    (by simp [runTriggerS, hr, hrEq]) (by simp [runTriggerS, runTriggerR, hr, ham])
                    (by simp [runTriggerS, runTriggerR, hr, ham])
                    (by simp [runTriggerS, hr, hrEq]) (by simp [runTriggerS, runTriggerR, hr, hm0])
                    (by simp [runTriggerS, runTriggerR, hr, hm0])
      · -- `r = m`: transition to `.start` on BOTH `b = false` and `b = true`!
        simp only [symNext, hr, dite_false, SymW] at hR
        rcases hR with ⟨t, ht, rfl⟩
        cases b with
        | false =>
            by_cases htm : t = m
            · subst t
              refine ⟨cSync m 0, by simp [SymW, hr], ?_⟩
              exact tileStep_sync6 m m 0 0 m false
                (by simp [runTriggerS]) (by simp [runTriggerS, runTriggerR])
                (by simp [runTriggerS, runTriggerR])
            · by_cases ht1 : t + 1 < m
              · refine ⟨cAltR m 0 (t + 1), ?_, ?_⟩
                · simp only [SymW, hr, ite_false]
                  exact Or.inr (Or.inr (Or.inr ⟨t + 1, by omega, ht1, Or.inl rfl⟩))
                · exact tileStep_alt2_6 m m 0 0 t m (t + 1) 0 t false true
                    (by simp [runTriggerS]) (by simp [runTriggerS, runTriggerR, (show t < m by omega)])
                    (by simp [runTriggerS, runTriggerR, (show t < m by omega)])
                    (by simp [runTriggerS]) (by simp [runTriggerS, runTriggerR, (show t < m by omega)])
                    (by simp [runTriggerS, runTriggerR, (show t < m by omega)])
              · have htEq : t = m - 1 := by omega
                subst htEq
                have hm1 : m - 1 < m := by omega
                have hmEq : m - 1 + 1 = m := by omega
                refine ⟨cCyc2 m, by simp [SymW, hr], ?_⟩
                exact tileStep_cyc3_6 m m 0 0 (m - 1) m m 0 (m - 1) 0 m 0 (m - 1) false true false
                  (by simp [runTriggerS]) (by simp [runTriggerS, runTriggerR, hm1])
                  (by simp [runTriggerS, runTriggerR, hm1])
                  (by simp [runTriggerS]) (by simp [runTriggerS, runTriggerR, hm1, hmEq])
                  (by simp [runTriggerS, runTriggerR, hm1])
                  (by simp [runTriggerS, hm0]) (by simp [runTriggerS, runTriggerR, hm0, hm1, hmEq])
                  (by simp [runTriggerS, runTriggerR, hm0, hm1])
        | true =>
            by_cases htm : t = m
            · subst t
              refine ⟨cSync m 0, by simp [SymW, hr], ?_⟩
              exact tileStep_sync6 m m 0 0 m true
                (by simp [runTriggerS]) (by simp [runTriggerS, runTriggerR])
                (by simp [runTriggerS, runTriggerR])
            · by_cases ht1 : t + 1 < m
              · refine ⟨cAltR m (t + 1) 0, ?_, ?_⟩
                · simp only [SymW, hr, ite_false]
                  exact Or.inr (Or.inr (Or.inr ⟨t + 1, by omega, ht1, Or.inr rfl⟩))
                · exact tileStep_alt2_6 m m (t + 1) 0 t m 0 0 t true false
                    (by simp [runTriggerS]) (by simp [runTriggerS, runTriggerR, (show t < m by omega)])
                    (by simp [runTriggerS, runTriggerR, (show t < m by omega)])
                    (by simp [runTriggerS]) (by simp [runTriggerS, runTriggerR, (show t < m by omega)])
                    (by simp [runTriggerS, runTriggerR, (show t < m by omega)])
              · have htEq : t = m - 1 := by omega
                subst htEq
                have hm1 : m - 1 < m := by omega
                have hmEq : m - 1 + 1 = m := by omega
                refine ⟨cCyc1 m, by simp [SymW, hr], ?_⟩
                exact tileStep_cyc3_6 m m m 0 (m - 1) 0 m 0 (m - 1) m 0 0 (m - 1) true false false
                  (by simp [runTriggerS]) (by simp [runTriggerS, runTriggerR, hm1, hmEq])
                  (by simp [runTriggerS, runTriggerR, hm1])
                  (by simp [runTriggerS, hm0]) (by simp [runTriggerS, runTriggerR, hm0, hm1, hmEq])
                  (by simp [runTriggerS, runTriggerR, hm0, hm1])
                  (by simp [runTriggerS]) (by simp [runTriggerS, runTriggerR, hm1])
                  (by simp [runTriggerS, runTriggerR, hm1])

/--
**Theorem E1 (`runTrigger_period6_all_m_bv` — Infinite Parametric Coxeter-6 Theorem):**
For EVERY threshold `m ≥ 2` (`k = m + 1 ≥ 3` states), EVERY bit-width `w : Nat`,
and EVERY `x : BitVec w`, the 12-sweep composition satisfies:
`(B_{m+1} ∘ F_{m+1})^6(x) = (R_m ∘ S_m)^6(x) = x`,
proved simultaneously for all `m ≥ 2` and all `w` via our Bidirectional Tile-Witness Engine!
-/
theorem runTrigger_period6_all_m_bv (m : Nat) (hm : 2 ≤ m) {w : Nat} (x : BitVec w) :
    iter (runTriggerTwoWay m) 6 x = x := by
  have h := tileWitness_sound_id_bv (runTriggerSweeps6 m) .start (symNext m hm) (SymW m)
    (symW_len m) (symW_init m) (symW_step m hm) (symW_final m hm) x
  have hs := sweepsBV_twoWay_six (runTriggerS m) (runTriggerR m) x
  change iter (twoWayBV (runTriggerS m) (runTriggerR m)) 6 x = x
  rw [← hs]
  exact h

theorem runSkipFlip_period6_all_m_bv (m : Nat) (hm : 2 ≤ m) {w : Nat} (x : BitVec w) :
    iter (twoWayBV (runSkipFlip m) (runSkipFlip m)) 6 x = x := by
  have hEq : ∀ y : BitVec w, twoWayBV (runSkipFlip m) (runSkipFlip m) y = runTriggerTwoWay m y :=
    runSkipFlip_twoWay_eq_runTrigger m
  have hIter : ∀ n (y : BitVec w),
      iter (twoWayBV (runSkipFlip m) (runSkipFlip m)) n y = iter (runTriggerTwoWay m) n y := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ k ih => intro y; simp only [iter, hEq, ih]
  rw [hIter]
  exact runTrigger_period6_all_m_bv m hm x

/-! ### Section 5C: Exact 3-Regime Phase Transition (`w ≤ m`, `m + 1 ≤ w < 2m`, `w ≥ 2m`) -/

theorem countBit_true_add_false (xs : List Bool) :
    countBit true xs + countBit false xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [countBit] <;> omega

theorem runTriggerS_id_of_count_lt (m q : Nat) (xs : List Bool)
    (h : q + countBit true xs < m) :
    (runFwd (runTriggerS m) q xs).1 = xs := by
  induction xs generalizing q with
  | nil => rfl
  | cons b bs ih =>
      have hq : q < m := by omega
      simp only [runFwd, runTriggerS, hq, ite_true]
      cases b with
      | false =>
          simp only [Bool.false_eq_true, ite_false]
          simp only [countBit] at h
          exact congrArg (false :: ·) (ih 0 (by omega))
      | true =>
          simp only [ite_true]
          simp only [countBit, beq_self_eq_true, ite_true] at h
          exact congrArg (true :: ·) (ih (q + 1) (by omega))

theorem runTriggerR_out_lt {m s : Nat} (b : Bool) (h : s < m) : (runTriggerR m).out s b = b := by
  simp [runTriggerR, h]

theorem runTriggerR_delta_false_lt {m s : Nat} (h : s < m) : (runTriggerR m).delta s false = s + 1 := by
  simp [runTriggerR, h]

theorem runTriggerR_delta_true_lt {m s : Nat} (h : s < m) : (runTriggerR m).delta s true = 0 := by
  simp [runTriggerR, h]

theorem runTriggerR_out_ge {m s : Nat} (b : Bool) (h : ¬ s < m) : (runTriggerR m).out s b = !b := by
  simp [runTriggerR, h]

theorem runTriggerR_delta_ge {m s : Nat} (b : Bool) (h : ¬ s < m) : (runTriggerR m).delta s b = 0 := by
  simp [runTriggerR, h]

theorem runTriggerR_id_of_count_lt (m q : Nat) (xs : List Bool)
    (h : q + countBit false xs < m) :
    (runBwd (runTriggerR m) q xs).1 = xs ∧ (runBwd (runTriggerR m) q xs).2 ≤ q + countBit false xs := by
  induction xs with
  | nil => exact ⟨rfl, by simp [runBwd, countBit]⟩
  | cons b bs ih =>
      simp only [countBit] at h
      have hsub : q + countBit false bs < m := by cases b <;> simp at h <;> omega
      rcases ih hsub with ⟨ihOut, ihSt⟩
      have hq : (runBwd (runTriggerR m) q bs).2 < m := by omega
      simp only [runBwd, ihOut]
      rw [runTriggerR_out_lt b hq]
      cases b with
      | false =>
          rw [runTriggerR_delta_false_lt hq]
          exact ⟨rfl, by simp [countBit]; omega⟩
      | true =>
          rw [runTriggerR_delta_true_lt hq]
          exact ⟨rfl, Nat.zero_le _⟩

theorem runTriggerS_id_of_len_le (m q : Nat) (xs : List Bool)
    (h : q + xs.length ≤ m) :
    (runFwd (runTriggerS m) q xs).1 = xs := by
  induction xs generalizing q with
  | nil => rfl
  | cons b bs ih =>
      simp only [List.length_cons] at h
      have hq : q < m := by omega
      simp only [runFwd]
      have hO : (runTriggerS m).out q b = b := by simp [runTriggerS, hq]
      rw [hO]
      cases b with
      | false =>
          have hD : (runTriggerS m).delta q false = 0 := by simp [runTriggerS, hq]
          rw [hD]
          exact congrArg (false :: ·) (ih 0 (by omega))
      | true =>
          have hD : (runTriggerS m).delta q true = q + 1 := by simp [runTriggerS, hq]
          rw [hD]
          exact congrArg (true :: ·) (ih (q + 1) (by omega))

theorem runTriggerR_id_of_len_le (m q : Nat) (xs : List Bool)
    (h : q + xs.length ≤ m) :
    (runBwd (runTriggerR m) q xs).1 = xs ∧ (runBwd (runTriggerR m) q xs).2 ≤ q + xs.length := by
  induction xs with
  | nil => exact ⟨rfl, by simp [runBwd]⟩
  | cons b bs ih =>
      simp only [List.length_cons] at h
      rcases ih (by omega) with ⟨ihOut, ihSt⟩
      have hq : (runBwd (runTriggerR m) q bs).2 < m := by omega
      simp only [runBwd, ihOut]
      rw [runTriggerR_out_lt b hq]
      cases b with
      | false =>
          rw [runTriggerR_delta_false_lt hq]; exact ⟨rfl, by simp; omega⟩
      | true =>
          rw [runTriggerR_delta_true_lt hq]; exact ⟨rfl, Nat.zero_le _⟩

/-- If `S_m` modifies any bit, its output already contains at least `m` `true`s (the trigger run). -/
theorem runTriggerS_changed_has_m_ones (m q : Nat) (xs : List Bool) (hq : q ≤ m) :
    (runFwd (runTriggerS m) q xs).1 = xs ∨ m ≤ q + countBit true (runFwd (runTriggerS m) q xs).1 := by
  induction xs generalizing q with
  | nil => exact Or.inl rfl
  | cons b bs ih =>
      by_cases hlt : q < m
      · simp only [runFwd]
        have hO : (runTriggerS m).out q b = b := by simp [runTriggerS, hlt]
        rw [hO]
        cases b with
        | false =>
            have hD : (runTriggerS m).delta q false = 0 := by simp [runTriggerS, hlt]
            rw [hD]
            rcases ih 0 (Nat.zero_le m) with hEq | hCnt
            · exact Or.inl (congrArg (false :: ·) hEq)
            · right; simp [countBit]; omega
        | true =>
            have hD : (runTriggerS m).delta q true = q + 1 := by simp [runTriggerS, hlt]
            rw [hD]
            rcases ih (q + 1) (by omega) with hEq | hCnt
            · exact Or.inl (congrArg (true :: ·) hEq)
            · right; simp [countBit]; omega
      · right; omega

/-- If `R_m` modifies any bit, its output already contains at least `m` `false`s (the trigger run). -/
theorem runTriggerR_changed_has_m_zeros (m : Nat) (xs : List Bool) :
    (runBwd (runTriggerR m) 0 xs).1 = xs ∨ m ≤ countBit false (runBwd (runTriggerR m) 0 xs).1 := by
  have hAux : ∀ ys,
      ((runBwd (runTriggerR m) 0 ys).1 = ys ∧ (runBwd (runTriggerR m) 0 ys).2 ≤ countBit false ys) ∨
      m ≤ countBit false (runBwd (runTriggerR m) 0 ys).1 := by
    intro ys
    induction ys with
    | nil => left; exact ⟨rfl, by simp [runBwd, countBit]⟩
    | cons b bs ih =>
        rcases ih with ⟨ihEq, ihSt⟩ | ihM
        · by_cases hlt : (runBwd (runTriggerR m) 0 bs).2 < m
          · left
            simp only [runBwd, ihEq]
            rw [runTriggerR_out_lt b hlt]
            cases b with
            | false =>
                rw [runTriggerR_delta_false_lt hlt]; exact ⟨rfl, by simp [countBit]; omega⟩
            | true =>
                rw [runTriggerR_delta_true_lt hlt]; exact ⟨rfl, Nat.zero_le _⟩
          · right
            have hge : m ≤ (runBwd (runTriggerR m) 0 bs).2 := by omega
            simp only [runBwd, ihEq, countBit]
            omega
        · right
          simp only [runBwd, countBit]
          omega
  rcases hAux xs with ⟨hEq, _⟩ | hM
  · exact Or.inl hEq
  · exact Or.inr hM

/--
**Theorem E2 — Phase Transition Regime I (`runTrigger_regime1_id`):**
For EVERY `m ≥ 1`, `w ≤ m`, and `x : BitVec w`, `T_m(x) = x` (order 1).
-/
theorem runTrigger_regime1_id (m : Nat) {w : Nat} (hw : w ≤ m) (x : BitVec w) :
    runTriggerTwoWay m x = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hEq : toBits (runTriggerTwoWay m x) = toBits x := by
    simp only [runTriggerTwoWay, twoWayBV, fwdBV, bwdBV, toBits_liftBV]
    change (runBwd (runTriggerR m) 0 (runFwd (runTriggerS m) 0 (toBits x)).1).1 = toBits x
    have hlen : (toBits x).length ≤ m := by rw [toBits_length]; exact hw
    rw [runTriggerS_id_of_len_le m 0 (toBits x) (by omega)]
    exact (runTriggerR_id_of_len_le m 0 (toBits x) (by omega)).1
  have hget := congrArg (fun l => l.getD i false) hEq
  simpa [toBits, List.getD_eq_getElem?_getD, hi] using hget

/--
**Theorem E3 — Phase Transition Regime II (`runTrigger_regime2_invol`):**
For EVERY `m ≥ 1`, `w < 2 * m`, and `x : BitVec w`, `T_m^2(x) = x` (involution regime!).
-/
theorem runTrigger_regime2_invol_list (m : Nat) (xs : List Bool) (hw : xs.length < 2 * m) :
    let T := fun ys => (runBwd (runTriggerR m) 0 (runFwd (runTriggerS m) 0 ys).1).1
    T (T xs) = xs := by
  intro T
  have hSum := countBit_true_add_false xs
  by_cases h1 : countBit true xs < m
  · have hS1 : (runFwd (runTriggerS m) 0 xs).1 = xs :=
      runTriggerS_id_of_count_lt m 0 xs (by omega)
    have hT1 : T xs = (runBwd (runTriggerR m) 0 xs).1 := by simp [T, hS1]
    rcases runTriggerR_changed_has_m_zeros m xs with hReq | hRge
    · rw [hT1, hReq, hT1, hReq]
    · have hLenR : (runBwd (runTriggerR m) 0 xs).1.length = xs.length :=
        runBwd_length (runTriggerR m) 0 xs
      have hSumR := countBit_true_add_false (runBwd (runTriggerR m) 0 xs).1
      have hCnt1R : countBit true (runBwd (runTriggerR m) 0 xs).1 < m := by omega
      have hS2 : (runFwd (runTriggerS m) 0 (runBwd (runTriggerR m) 0 xs).1).1 =
          (runBwd (runTriggerR m) 0 xs).1 :=
        runTriggerS_id_of_count_lt m 0 _ (by omega)
      simp only [hT1, T, hS2]
      have hInv := runTriggerR_invol_list m 0 xs
      exact congrArg Prod.fst hInv
  · have h0 : countBit false xs < m := by omega
    have hR0 : (runBwd (runTriggerR m) 0 xs).1 = xs :=
      (runTriggerR_id_of_count_lt m 0 xs (by omega)).1
    rcases runTriggerS_changed_has_m_ones m 0 xs (Nat.zero_le m) with hSeq | hSge
    · simp only [T, hSeq, hR0]
    · have hLenS : (runFwd (runTriggerS m) 0 xs).1.length = xs.length :=
        runFwd_length (runTriggerS m) 0 xs
      have hSumS := countBit_true_add_false (runFwd (runTriggerS m) 0 xs).1
      have hCnt0S : countBit false (runFwd (runTriggerS m) 0 xs).1 < m := by omega
      have hR1 : (runBwd (runTriggerR m) 0 (runFwd (runTriggerS m) 0 xs).1).1 =
          (runFwd (runTriggerS m) 0 xs).1 :=
        (runTriggerR_id_of_count_lt m 0 _ (by omega)).1
      simp only [T, hR1]
      have hInv := runTriggerS_invol_list m 0 xs
      have hS2 : (runFwd (runTriggerS m) 0 (runFwd (runTriggerS m) 0 xs).1).1 = xs :=
        congrArg Prod.fst hInv
      rw [hS2, hR0]

theorem runTrigger_regime2_invol (m : Nat) {w : Nat} (hw : w < 2 * m) (x : BitVec w) :
    iter (runTriggerTwoWay m) 2 x = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hEq : toBits (iter (runTriggerTwoWay m) 2 x) = toBits x := by
    simp only [iter, runTriggerTwoWay, twoWayBV, fwdBV, bwdBV, toBits_liftBV]
    exact runTrigger_regime2_invol_list m (toBits x) (by rw [toBits_length]; exact hw)
  have hget := congrArg (fun l => l.getD i false) hEq
  simpa [toBits, List.getD_eq_getElem?_getD, hi] using hget

/-! ### Section 5D: Sharp Exact-Order Witnesses (`∀ m ≥ 2`: 2-cycle `∀ w ≥ m+1`, 3-cycle `∀ w ≥ 2m`) -/

theorem runBwd_append {Q : Type} (m : Mealy Q) (q : Q) (xs ys : List Bool) :
    runBwd m q (xs ++ ys) =
      let (os2, q2) := runBwd m q ys
      let (os1, q1) := runBwd m q2 xs
      (os1 ++ os2, q1) := by
  induction xs with
  | nil => simp [runBwd]
  | cons b bs ih =>
      simp only [List.cons_append, runBwd, ih]

theorem runBwd_R_replicate_false (m q n : Nat) (h : q + n ≤ m) :
    runBwd (runTriggerR m) q (List.replicate n false) = (List.replicate n false, q + n) := by
  induction n with
  | zero => simp [runBwd]
  | succ k ih =>
      simp only [List.replicate_succ, runBwd]
      rw [ih (by omega)]
      have hlt : q + k < m := by omega
      simp [runTriggerR, hlt]
      omega

theorem runFwd_S_replicate_true (m q n : Nat) (h : q + n ≤ m) :
    runFwd (runTriggerS m) q (List.replicate n true) = (List.replicate n true, q + n) := by
  induction n generalizing q with
  | zero => simp [runFwd]
  | succ k ih =>
      simp only [List.replicate_succ, runFwd]
      have hlt : q < m := by omega
      have hO : (runTriggerS m).out q true = true := by simp [runTriggerS, hlt]
      have hD : (runTriggerS m).delta q true = q + 1 := by simp [runTriggerS, hlt]
      rw [hO, hD, ih (q + 1) (by omega)]
      have hadd : q + 1 + k = q + (k + 1) := by omega
      rw [hadd]

theorem runFwd_S_replicate_false (m q n : Nat) (hq : q < m) :
    runFwd (runTriggerS m) q (List.replicate n false) = (List.replicate n false, if n = 0 then q else 0) := by
  induction n generalizing q with
  | zero => simp [runFwd]
  | succ k ih =>
      simp only [List.replicate_succ, runFwd]
      have hO : (runTriggerS m).out q false = false := by simp [runTriggerS, hq]
      have hD : (runTriggerS m).delta q false = 0 := by simp [runTriggerS, hq]
      rw [hO, hD, ih 0 (by omega)]
      cases k <;> rfl

theorem runBwd_R_replicate_true (m q n : Nat) (hq : q < m) :
    runBwd (runTriggerR m) q (List.replicate n true) = (List.replicate n true, if n = 0 then q else 0) := by
  induction n with
  | zero => simp [runBwd]
  | succ k ih =>
      simp only [List.replicate_succ, runBwd, ih]
      cases k with
      | zero => simp [runTriggerR, hq]
      | succ j => simp [runTriggerR, (show 0 < m by omega)]

theorem list_replicate_add {α : Type} (a b : Nat) (v : α) :
    List.replicate (a + b) v = List.replicate a v ++ List.replicate b v := by
  induction a with
  | zero => simp
  | succ k ih => rw [Nat.succ_add, List.replicate_succ, List.replicate_succ, ih, List.cons_append]

/-- Exact 2-cycle witness at `x = 0` for ALL `m ≥ 1` and ALL `w ≥ m + 1`: `T_m(0) ≠ 0`. -/
theorem runTrigger_zero_not_fixed (m d : Nat) (hm : 1 ≤ m) :
    runTriggerTwoWay m (0 : BitVec (d + m + 1)) ≠ (0 : BitVec (d + m + 1)) := by
  intro hEq
  have hBits := congrArg toBits hEq
  have hZero := toBits_zero (d + m + 1)
  simp only [runTriggerTwoWay, twoWayBV, fwdBV, bwdBV, toBits_liftBV, hZero] at hBits
  change (runBwd (runTriggerR m) 0 (runFwd (runTriggerS m) 0 (List.replicate (d + m + 1) false)).1).1 = _ at hBits
  rw [(runFwd_S_replicate_false m 0 (d + m + 1) (by omega))] at hBits
  have hSplit : List.replicate (d + m + 1) false =
      List.replicate d false ++ (false :: List.replicate m false) := by
    rw [show d + m + 1 = d + (m + 1) by omega, list_replicate_add, List.replicate_succ]
  rw [hSplit, runBwd_append] at hBits
  simp only [runBwd] at hBits
  rw [runBwd_R_replicate_false m 0 m (by omega), Nat.zero_add] at hBits
  have hStep : (runTriggerR m).out m false = true := by simp [runTriggerR]
  rw [hStep] at hBits
  have hGet := congrArg (fun l => l.getD d false) hBits
  have hLenL : (runBwd (runTriggerR m) ((runTriggerR m).delta m false) (List.replicate d false)).1.length = d := by
    rw [runBwd_length, List.length_replicate]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD] at hGet
  rw [List.getElem?_append_right (by rw [hLenL]; exact Nat.le_refl d), hLenL] at hGet
  have hR : (List.replicate d false ++ false :: List.replicate m false)[d]? = some false := by
    rw [List.getElem?_append_right (by simp), List.length_replicate]; simp
  rw [hR] at hGet
  simp at hGet

/-- For `m ≥ 2`, `S_m` fixes any bit-list with no adjacent `true`s. -/
theorem runFwd_S_of_noAdjTrue (m : Nat) (hm : 2 ≤ m) :
    ∀ (prev : Bool) (xs : List Bool), noAdjTrue prev xs →
      (runFwd (runTriggerS m) (if prev then 1 else 0) xs).1 = xs := by
  intro prev xs h
  induction xs generalizing prev with
  | nil => rfl
  | cons b bs ih =>
      rcases h with ⟨hNo, hRest⟩
      cases prev with
      | false =>
          have h0 : 0 < m := by omega
          simp only [Bool.false_eq_true, ite_false, runFwd]
          change (runTriggerS m).out 0 b :: (runFwd (runTriggerS m) ((runTriggerS m).delta 0 b) bs).1 = b :: bs
          cases b with
          | false =>
              have hO : (runTriggerS m).out 0 false = false := by simp [runTriggerS, h0]
              have hD : (runTriggerS m).delta 0 false = 0 := by simp [runTriggerS, h0]
              rw [hO, hD]; exact congrArg (false :: ·) (ih false hRest)
          | true =>
              have hO : (runTriggerS m).out 0 true = true := by simp [runTriggerS, h0]
              have hD : (runTriggerS m).delta 0 true = 1 := by simp [runTriggerS, h0]
              rw [hO, hD]; exact congrArg (true :: ·) (ih true hRest)
      | true =>
          have hb : b = false := hNo rfl
          subst hb
          have h1 : 1 < m := by omega
          simp only [ite_true, runFwd]
          change (runTriggerS m).out 1 false :: (runFwd (runTriggerS m) ((runTriggerS m).delta 1 false) bs).1 = false :: bs
          have hO : (runTriggerS m).out 1 false = false := by simp [runTriggerS, h1]
          have hD : (runTriggerS m).delta 1 false = 0 := by simp [runTriggerS, h1]
          rw [hO, hD]; exact congrArg (false :: ·) (ih false hRest)

/-- `R_m(0^n)` never has adjacent `true`s (since every `true` output resets state to `0 < m`). -/
theorem runBwd_R_zeros_noAdjTrue (m : Nat) (hm : 2 ≤ m) (n : Nat) :
    noAdjTrue false (runBwd (runTriggerR m) 0 (List.replicate n false)).1 ∧
    ((runBwd (runTriggerR m) 0 (List.replicate n false)).1.head? = some true →
      (runBwd (runTriggerR m) 0 (List.replicate n false)).2 = 0) := by
  induction n with
  | zero => exact ⟨trivial, by simp [runBwd]⟩
  | succ k ih =>
      rcases ih with ⟨ihNo, ihHead⟩
      simp only [List.replicate_succ, runBwd]
      generalize hp_eq : runBwd (runTriggerR m) 0 (List.replicate k false) = p at ihNo ihHead ⊢
      by_cases hlt : p.2 < m
      · rw [runTriggerR_out_lt false hlt, runTriggerR_delta_false_lt hlt]
        simp only [List.head?_cons]
        refine ⟨⟨(fun h => by cases h), ?_⟩, (fun h => by cases h)⟩
        cases hp : p.1 with
        | nil => trivial
        | cons b bs =>
            rw [hp] at ihNo
            exact ⟨(fun h => by cases h), ihNo.2⟩
      · rw [runTriggerR_out_ge false hlt, runTriggerR_delta_ge false hlt]
        simp only [Bool.not_false, List.head?_cons]
        refine ⟨⟨(fun h => by cases h), ?_⟩, (fun _ => trivial)⟩
        cases hp : p.1 with
        | nil => trivial
        | cons b bs =>
            rw [hp] at ihNo ihHead
            refine ⟨?_, ihNo.2⟩
            intro _
            cases b with
            | false => rfl
            | true =>
                have h0 : p.2 = 0 := ihHead rfl
                omega

/-- Exact order-2 orbit at `x = 0` for ALL `m ≥ 2` and ALL `w : Nat`: `T_m^2(0) = 0`. -/
theorem runTrigger_zero_order2 (m : Nat) (hm : 2 ≤ m) {w : Nat} :
    iter (runTriggerTwoWay m) 2 (0 : BitVec w) = (0 : BitVec w) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hZero := toBits_zero w
  have hEq : toBits (iter (runTriggerTwoWay m) 2 (0 : BitVec w)) = toBits (0 : BitVec w) := by
    simp only [iter, runTriggerTwoWay, twoWayBV, fwdBV, bwdBV, toBits_liftBV, hZero]
    change (runBwd (runTriggerR m) 0
      (runFwd (runTriggerS m) 0
        (runBwd (runTriggerR m) 0
          (runFwd (runTriggerS m) 0 (List.replicate w false)).1).1).1).1 = List.replicate w false
    rw [(runFwd_S_replicate_false m 0 w (by omega))]
    have hFix := runFwd_S_of_noAdjTrue m hm false _ (runBwd_R_zeros_noAdjTrue m hm w).1
    simp only [Bool.false_eq_true, ite_false] at hFix
    rw [hFix]
    exact congrArg Prod.fst (runTriggerR_invol_list m 0 (List.replicate w false))
  have hget := congrArg (fun l => l.getD i false) hEq
  simpa [toBits, List.getD_eq_getElem?_getD, hi] using hget

theorem altPadRev_length (n : Nat) : (altPadRev n).length = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [altPadRev, ih]

/-- For `m ≥ 2`, `S_m` from state `0` fixes `altPadRev d` and exits in state `0`. -/
theorem runFwd_S_altPadRev (m : Nat) (hm : 2 ≤ m) :
    ∀ d, runFwd (runTriggerS m) 0 (altPadRev d) = (altPadRev d, 0) := by
  intro d
  induction d using Nat.strongRecOn with
  | ind n ih =>
      match n with
      | 0 => rfl
      | 1 => simp [altPadRev, runFwd, runTriggerS, (show 0 < m by omega)]
      | k + 2 =>
          by_cases hpar : (k + 1) % 2 == 1
          · have hnext : (k % 2 == 1) = false := by
              simp only [beq_iff_eq] at hpar
              simp only [beq_eq_false_iff_ne, ne_eq]; omega
            simp only [altPadRev, hpar, hnext, runFwd]
            have hO0 : (runTriggerS m).out 0 true = true := by simp [runTriggerS, (show 0 < m by omega)]
            have hD0 : (runTriggerS m).delta 0 true = 1 := by simp [runTriggerS, (show 0 < m by omega)]
            have hO1 : (runTriggerS m).out 1 false = false := by simp [runTriggerS, (show 1 < m by omega)]
            have hD1 : (runTriggerS m).delta 1 false = 0 := by simp [runTriggerS, (show 1 < m by omega)]
            rw [hO0, hD0, hO1, hD1, ih k (by omega)]
          · have hparF : ((k + 1) % 2 == 1) = false := Bool.eq_false_iff.mpr hpar
            have hStep : altPadRev (k + 2) = false :: altPadRev (k + 1) := by
              simp [altPadRev, hparF]
            rw [hStep]
            simp only [runFwd]
            have hO0 : (runTriggerS m).out 0 false = false := by simp [runTriggerS, (show 0 < m by omega)]
            have hD0 : (runTriggerS m).delta 0 false = 0 := by simp [runTriggerS, (show 0 < m by omega)]
            rw [hO0, hD0, ih (k + 1) (by omega)]

/-- For `m ≥ 2`, `R_m` from state `0` fixes `altPadRev d` (backward pass). -/
theorem runBwd_R_altPadRev (m : Nat) (hm : 2 ≤ m) :
    ∀ d, (runBwd (runTriggerR m) 0 (altPadRev d)).1 = altPadRev d ∧
         (runBwd (runTriggerR m) 0 (altPadRev d)).2 ≤ (if d % 2 == 1 then 1 else 0) := by
  intro d
  induction d with
  | zero => exact ⟨rfl, by simp [altPadRev, runBwd]⟩
  | succ k ih =>
      rcases ih with ⟨ihOut, ihSt⟩
      have hlt : (runBwd (runTriggerR m) 0 (altPadRev k)).2 < m := by
        cases hpar : (k % 2 == 1) <;> rw [hpar] at ihSt <;> simp at ihSt <;> omega
      simp only [altPadRev, runBwd]
      rw [runTriggerR_out_lt (k % 2 == 1) hlt, ihOut]
      cases hk : k % 2 with
      | zero =>
          have h0 : (k % 2 == 1) = false := by simp [hk]
          have h1 : ((k + 1) % 2 == 1) = true := by simp [Nat.add_mod, hk]
          rw [h0] at ihSt
          simp only [Bool.false_eq_true, ite_false] at ihSt
          have hbeq : (0 == 1) = false := rfl
          rw [hbeq, runTriggerR_delta_false_lt hlt, h1]
          exact ⟨rfl, by simp; omega⟩
      | succ r =>
          have hr : r = 0 := by omega
          subst hr
          have h0 : ((k + 1) % 2 == 1) = false := by simp [Nat.add_mod, hk]
          have hbeq : (0 + 1 == 1) = true := rfl
          rw [hbeq, runTriggerR_delta_true_lt hlt, h0]
          exact ⟨rfl, by simp⟩

/--
**Theorem E4 — Exact 3-Cycle Witness (`runTrigger_witness_order3_bv`):**
For EVERY `m ≥ 2` and EVERY `w = d + 2m ≥ 2m`, the explicit alternating-padded word
`x_0 = altPadRev d ++ 1^m ++ 0^m` lies on an exact 3-cycle of `T_m = R_m ∘ S_m`:
`T_m(x_0) ≠ x_0`, `T_m^2(x_0) ≠ x_0`, and `T_m^3(x_0) = x_0`.
-/
theorem runTrigger_witness_order3_list (m d : Nat) (hm : 2 ≤ m) :
    let T := fun ys => (runBwd (runTriggerR m) 0 (runFwd (runTriggerS m) 0 ys).1).1
    let x0 := altPadRev d ++ List.replicate m true ++ List.replicate m false
    T x0 ≠ x0 ∧ T (T x0) ≠ x0 ∧ T (T (T x0)) = x0 := by
  intro T x0
  let x1 := altPadRev d ++ List.replicate (m + 1) true ++ List.replicate (m - 1) false
  let x2 := altPadRev d ++ List.replicate (m - 1) true ++ List.replicate (m + 1) false
  have hS_x0 : (runFwd (runTriggerS m) 0 x0).1 = x1 := by
    simp only [x0, x1, List.append_assoc, runFwd_append, runFwd_S_altPadRev m hm d]
    rw [runFwd_S_replicate_true m 0 m (by omega), Nat.zero_add]
    have hmSplit : List.replicate m false = false :: List.replicate (m - 1) false := by
      cases m with | zero => omega | succ j => simp [List.replicate_succ]
    rw [hmSplit]
    simp only [runFwd]
    have hO : (runTriggerS m).out m false = true := by simp [runTriggerS]
    have hD : (runTriggerS m).delta m false = 0 := by simp [runTriggerS]
    rw [hO, hD, runFwd_S_replicate_false m 0 (m - 1) (by omega)]
    have h1Split : List.replicate (m + 1) true = List.replicate m true ++ [true] := by
      rw [list_replicate_add]; rfl
    simp [h1Split, List.append_assoc]
  have hR_x1 : (runBwd (runTriggerR m) 0 x1).1 = x1 := by
    simp only [x1, List.append_assoc, runBwd_append]
    rw [runBwd_R_replicate_false m 0 (m - 1) (by omega), Nat.zero_add]
    rw [runBwd_R_replicate_true m (m - 1) (m + 1) (by omega)]
    simp only [Nat.succ_ne_zero, ite_false]
    rw [(runBwd_R_altPadRev m hm d).1]
  have hT_x0 : T x0 = x1 := by simp only [T, hS_x0, hR_x1]
  have hS_x1 : (runFwd (runTriggerS m) 0 x1).1 = x0 := by
    rw [← hS_x0]
    exact congrArg Prod.fst (runTriggerS_invol_list m 0 x0)
  have hR_x0 : (runBwd (runTriggerR m) 0 x0).1 = x2 := by
    simp only [x0, x2, List.append_assoc, runBwd_append]
    rw [runBwd_R_replicate_false m 0 m (by omega), Nat.zero_add]
    have hm1 : List.replicate m true = List.replicate (m - 1) true ++ [true] := by
      rw [show m = (m - 1) + 1 by omega, list_replicate_add]; rfl
    rw [hm1, runBwd_append]
    simp only [runBwd]
    have hO : (runTriggerR m).out m true = false := by simp [runTriggerR]
    have hD : (runTriggerR m).delta m true = 0 := by simp [runTriggerR]
    rw [hO, hD, runBwd_R_replicate_true m 0 (m - 1) (by omega)]
    have hne : m - 1 ≠ 0 := by omega
    simp only [hne, ite_false]
    rw [(runBwd_R_altPadRev m hm d).1]
    have h0Split : List.replicate (m + 1) false = false :: List.replicate m false := by
      rw [List.replicate_succ]
    simp [h0Split, List.append_assoc]
  have hT_x1 : T x1 = x2 := by simp only [T, hS_x1, hR_x0]
  have hS_x2 : (runFwd (runTriggerS m) 0 x2).1 = x2 := by
    simp only [x2, List.append_assoc, runFwd_append, runFwd_S_altPadRev m hm d]
    rw [runFwd_S_replicate_true m 0 (m - 1) (by omega), Nat.zero_add]
    rw [runFwd_S_replicate_false m (m - 1) (m + 1) (by omega)]
  have hR_x2 : (runBwd (runTriggerR m) 0 x2).1 = x0 := by
    rw [← hR_x0]
    exact congrArg Prod.fst (runTriggerR_invol_list m 0 x0)
  have hT_x2 : T x2 = x0 := by simp only [T, hS_x2, hR_x2]
  refine ⟨?_, ?_, ?_⟩
  · rw [hT_x0]
    intro hEq
    have hGet := congrArg (fun l => l.getD (d + m) false) hEq
    have h1 : x1.getD (d + m) false = true := by
      simp only [x1, List.getD_eq_getElem?_getD, List.append_assoc]
      rw [List.getElem?_append_right (by rw [altPadRev_length]; omega), altPadRev_length]
      have hidx : d + m - d = m := by omega
      rw [hidx, List.getElem?_append_left (by simp)]
      simp
    have h0 : x0.getD (d + m) false = false := by
      simp only [x0, List.getD_eq_getElem?_getD, List.append_assoc]
      rw [List.getElem?_append_right (by rw [altPadRev_length]; omega), altPadRev_length]
      have hidx : d + m - d = m := by omega
      rw [hidx, List.getElem?_append_right (by simp)]
      simp [show 0 < m by omega]
    rw [h1, h0] at hGet; cases hGet
  · rw [hT_x0, hT_x1]
    intro hEq
    have hGet := congrArg (fun l => l.getD (d + (m - 1)) false) hEq
    have h2 : x2.getD (d + (m - 1)) false = false := by
      simp only [x2, List.getD_eq_getElem?_getD, List.append_assoc]
      rw [List.getElem?_append_right (by rw [altPadRev_length]; omega), altPadRev_length]
      have hidx : d + (m - 1) - d = m - 1 := by omega
      rw [hidx, List.getElem?_append_right (by simp)]
      simp
    have h0 : x0.getD (d + (m - 1)) false = true := by
      simp only [x0, List.getD_eq_getElem?_getD, List.append_assoc]
      rw [List.getElem?_append_right (by rw [altPadRev_length]; omega), altPadRev_length]
      have hidx : d + (m - 1) - d = m - 1 := by omega
      rw [hidx, List.getElem?_append_left (by simp; omega)]
      simp [show m - 1 < m by omega]
    rw [h2, h0] at hGet; cases hGet
  · rw [hT_x0, hT_x1, hT_x2]

theorem runTrigger_witness_order3_bv (m d : Nat) (hm : 2 ≤ m) :
    ∃ x : BitVec (d + 2 * m),
      runTriggerTwoWay m x ≠ x ∧
      iter (runTriggerTwoWay m) 2 x ≠ x ∧
      iter (runTriggerTwoWay m) 3 x = x := by
  let xs := altPadRev d ++ List.replicate m true ++ List.replicate m false
  have hLen : xs.length = d + 2 * m := by
    simp only [xs, List.length_append, altPadRev_length, List.length_replicate]; omega
  let x : BitVec (d + 2 * m) := (ofBits xs).cast hLen
  have hx : toBits x = xs := by
    apply List.ext_getElem
    · rw [toBits_length, hLen]
    · intro i h1 h2
      simp only [x, toBits, List.getElem_ofFn, BitVec.getLsbD_cast]
      exact ofBits_getLsbD xs i h2
  have hT1 : toBits (runTriggerTwoWay m x) =
      (runBwd (runTriggerR m) 0 (runFwd (runTriggerS m) 0 xs).1).1 := by
    simp only [runTriggerTwoWay, twoWayBV, fwdBV, bwdBV, toBits_liftBV, hx]; rfl
  have hT2 : toBits (iter (runTriggerTwoWay m) 2 x) =
      (runBwd (runTriggerR m) 0 (runFwd (runTriggerS m) 0
        (runBwd (runTriggerR m) 0 (runFwd (runTriggerS m) 0 xs).1).1).1).1 := by
    simp only [iter, runTriggerTwoWay, twoWayBV, fwdBV, bwdBV, toBits_liftBV, hx]; rfl
  have hT3 : toBits (iter (runTriggerTwoWay m) 3 x) =
      (runBwd (runTriggerR m) 0 (runFwd (runTriggerS m) 0
        (runBwd (runTriggerR m) 0 (runFwd (runTriggerS m) 0
          (runBwd (runTriggerR m) 0 (runFwd (runTriggerS m) 0 xs).1).1).1).1).1).1 := by
    simp only [iter, runTriggerTwoWay, twoWayBV, fwdBV, bwdBV, toBits_liftBV, hx]; rfl
  rcases runTrigger_witness_order3_list m d hm with ⟨hne1, hne2, heq3⟩
  refine ⟨x, ?_, ?_, ?_⟩
  · intro h; exact hne1 (by have := congrArg toBits h; rw [hT1, hx] at this; exact this)
  · intro h; exact hne2 (by have := congrArg toBits h; rw [hT2, hx] at this; exact this)
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hEq : toBits (iter (runTriggerTwoWay m) 3 x) = toBits x := by rw [hT3, hx]; exact heq3
    have hget := congrArg (fun l => l.getD i false) hEq
    simpa [toBits, List.getD_eq_getElem?_getD, hi] using hget

/-! ## Section 6: Coupled-Boundary Engine Demo, Mutation/Sharpness Tests & Non-Vacuity -/

/--
**Theorem F1 (`coupled_parityDelay_exact_inv`):**
Using our coupled-boundary mode `tileWitness_sound_coupled_id`, `B_gd` initialized with
the final carry state `sEnd` of `F_pd` (`beta = id`) recovers `x` identically for ALL `w`!
-/
theorem coupled_parityDelay_exact_inv (xs : List Bool) :
    runCoupledTwoWay parityDelayF id grayDiffB xs = xs := by
  apply tileWitness_sound_coupled_id parityDelayF grayDiffB id false xor
    (fun p c => c = [p, p])
  · intro p c rfl; rfl
  · intro c rfl; exact ⟨false, rfl⟩
  · intro p b cR rfl
    refine ⟨[p, p], rfl, ?_⟩
    cases p <;> cases b <;> simp [TileStep, parityDelayF, grayDiffB]
  · intro p; exact ⟨p, rfl⟩

/-! ### Section 6B: Kernel-Checked Negative / Mutation Certificate Tests & Sharpness Counterexamples -/

theorem badCertPeriod2_rejected : checkCert badCertPeriod2 = false := by decide

theorem badCertDroppedWitness_rejected : checkCert badCertDroppedWitness = false := by decide

/-- Sharpness 1: Uncoupled `parityDelayF` is NOT injective (loses MSB at width 2). -/
theorem uncoupled_parityDelay_not_injective :
    (runFwd parityDelayF false [false, false]).1 = (runFwd parityDelayF false [false, true]).1 ∧
    ([false, false] : List Bool) ≠ [false, true] := by
  decide

theorem sharpness_perturbed_breaks_period3_and_6 :
    let T := twoWayBV skipFlip2Perturbed (skipFlip2 false)
    let x : BitVec 3 := 3#3
    iter T 3 x ≠ x ∧ iter T 6 x ≠ x := by
  decide

/-- Sharpness 3: Coupling `skipFlip2` (`t_w = sEnd`) destroys bijectivity even at `w = 2`! -/
theorem sharpness_coupled_skipFlip2_not_injective :
    runCoupledTwoWay (skipFlip2 false) id (skipFlip2 false) [false, true] =
    runCoupledTwoWay (skipFlip2 false) id (skipFlip2 false) [true, true] ∧
    ([false, true] : List Bool) ≠ [true, true] := by
  decide

theorem sharpness_variantA3_breaks_period3_and_6 :
    let T := twoWayBV skipFlipVariantA3 skipFlipVariantA3
    let x : BitVec 3 := 0#3
    iter T 3 x ≠ x ∧ iter T 6 x ≠ x := by
  decide

/-- Non-vacuity witnesses: concrete kernel-checked evaluations on `BitVec 4` and `BitVec 7`. -/
theorem nonvacuity_witness_skipFlip2_w4 :
    skipFlip2TwoWay (0#4) = 5#4 ∧
    skipFlip2TwoWay (5#4) = 15#4 ∧
    skipFlip2TwoWay (15#4) = 0#4 := by
  decide

theorem nonvacuity_witness_runTrigger_m2_w4 :
    runTriggerTwoWay 2 (3#4) = 7#4 ∧
    runTriggerTwoWay 2 (7#4) = 1#4 ∧
    runTriggerTwoWay 2 (1#4) = 3#4 := by
  decide

theorem nonvacuity_witness_runTrigger_m2_w7_exact6 :
    let T := runTriggerTwoWay 2
    let x : BitVec 7 := 1#7
    T x ≠ x ∧ iter T 2 x ≠ x ∧ iter T 3 x ≠ x ∧ iter T 6 x = x := by
  refine ⟨by decide, by decide, by decide, runTrigger_period6_all_m_bv 2 (by decide) 1#7⟩

end BidirectionalTransducer
