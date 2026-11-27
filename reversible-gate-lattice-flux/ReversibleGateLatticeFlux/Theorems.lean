/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ReversibleGateLatticeFlux.Defs

/-!
# Theorems (`reversible-gate-lattice-flux`)

Full proofs of the headline infinite theorems of Reversible Toffoli and Fredkin Gate-Lattice Conservation Engine.
-/

namespace GateLatticeEngine

theorem checkTree_sound (f : Nat → Bool) (d base : Nat)
    (h : checkTree f d base = true) :
    ∀ m : Nat, base ≤ m → m < base + 2 ^ d → f m = true := by
  induction d generalizing base with
  | zero =>
    intro m hlo hhi
    have heq : m = base := by omega
    subst heq; exact h
  | succ d ih =>
    simp only [checkTree, Bool.and_eq_true] at h
    intro m hlo hhi
    have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by
      rw [Nat.pow_succ]; omega
    by_cases hmid : m < base + 2 ^ d
    · exact ih base h.1 m hlo hmid
    · exact ih (base + 2 ^ d) h.2 m (by omega) (by omega)

theorem checkTree_complete (f : Nat → Bool) (d base : Nat)
    (h : ∀ m : Nat, base ≤ m → m < base + 2 ^ d → f m = true) :
    checkTree f d base = true := by
  induction d generalizing base with
  | zero =>
    exact h base (by omega) (by omega)
  | succ d ih =>
    simp only [checkTree, Bool.and_eq_true]
    have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by
      rw [Nat.pow_succ]; omega
    exact ⟨ih base (fun m h1 h2 => h m h1 (by omega)),
           ih (base + 2 ^ d) (fun m h1 h2 => h m (by omega) (by omega))⟩

theorem periodicLift_periodic {w : Nat} (hw : 0 < w) (v : BitVec w) :
    IsPeriodic w (periodicLift v) := by
  intro z
  unfold periodicLift
  have hne : w ≠ 0 := Nat.ne_of_gt hw
  have hm : (z + (w : Int)) % (w : Int) = z % (w : Int) := Int.add_emod_right z (w : Int)
  simp [hne, hm]

theorem periodicLift_eq_getLsbD {w : Nat} (hw : 0 < w) (v : BitVec w)
    {i : Nat} (hi : i < w) :
    periodicLift v (i : Int) = v.getLsbD i := by
  unfold periodicLift
  have hne : w ≠ 0 := Nat.ne_of_gt hw
  have hmod : (i : Int) % (w : Int) = (i : Int) :=
    Int.emod_eq_of_lt (by omega) (by omega)
  simp [hne, hmod]

theorem packBits_getLsbD (f : Nat → Bool) (k j : Nat) :
    (packBits f k).getLsbD j = if j < k then f j else false := by
  induction k with
  | zero => simp [packBits]
  | succ k ih =>
    unfold packBits
    rw [BitVec.getLsbD_cons]
    by_cases heq : j = k
    · subst heq; simp
    · simp only [heq, ↓reduceIte]
      rw [ih]
      by_cases hlt : j < k
      · have hlt' : j < k + 1 := by omega
        simp [hlt, hlt']
      · have hlt' : ¬ j < k + 1 := by omega
        simp [hlt, hlt']

theorem extractWindow_getLsbD (s : Line) (base : Int) (k j : Nat) :
    (extractWindow s base k).getLsbD j =
      if j < k then s (base + (j : Int)) else false :=
  packBits_getLsbD (fun i => s (base + (i : Int))) k j

theorem extractWindow_periodic {w : Nat} {s : Line} (hp : IsPeriodic w s)
    (base : Int) (k : Nat) :
    extractWindow s (base + (w : Int)) k = extractWindow s base k := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [extractWindow_getLsbD, extractWindow_getLsbD]
  simp only [hj, ↓reduceIte]
  have harg : base + (w : Int) + (j : Int) = base + (j : Int) + (w : Int) := by omega
  rw [harg, hp]

theorem sliceBV_getLsbD {M : Nat} (u : BitVec M) (off k j : Nat) (hj : j < k) :
    (sliceBV u off k).getLsbD j = u.getLsbD (off + j) := by
  unfold sliceBV
  rw [BitVec.getLsbD_setWidth]
  simp only [hj, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_ushiftRight]

theorem sliceBV_extractWindow (s : Line) (base : Int) {M off k : Nat} (h : off + k ≤ M) :
    sliceBV (extractWindow s base M) off k = extractWindow s (base + (off : Int)) k := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [sliceBV_getLsbD _ _ _ _ hj]
  rw [extractWindow_getLsbD, extractWindow_getLsbD]
  have hlt : off + j < M := by omega
  simp only [hlt, hj, ↓reduceIte]
  have harg : base + ((off + j : Nat) : Int) = base + (off : Int) + (j : Int) := by omega
  rw [harg]

theorem periodicLift_extractWindow {w : Nat} (hw : 0 < w) {s : Line} (hp : IsPeriodic w s) :
    periodicLift (extractWindow s 0 w) = s := by
  funext z
  unfold periodicLift
  have hne : w ≠ 0 := Nat.ne_of_gt hw
  simp only [hne, ↓reduceIte]
  have hwpos : (0 : Int) < (w : Int) := by omega
  have hmod_nonneg : 0 ≤ z % (w : Int) := Int.emod_nonneg z (by omega)
  have hmod_lt : z % (w : Int) < (w : Int) := Int.emod_lt_of_pos z hwpos
  have htoNat_lt : (z % (w : Int)).toNat < w := by omega
  rw [extractWindow_getLsbD]
  simp only [htoNat_lt, ↓reduceIte]
  have hcast : (0 : Int) + ((z % (w : Int)).toNat : Int) = z % (w : Int) := by omega
  rw [hcast]
  have hstep : ∀ (k : Nat) (x : Int), s (x + (k : Int) * (w : Int)) = s x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      have h1 : x + ((k + 1 : Nat) : Int) * (w : Int) = (x + (k : Int) * (w : Int)) + (w : Int) := by
        have : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
        rw [this, Int.add_mul, Int.one_mul, Int.add_assoc]
      rw [h1, hp, ih]
  have hstep_int : ∀ (q : Int) (x : Int), s (x + q * (w : Int)) = s x := by
    intro q x
    cases q with
    | ofNat k => exact hstep k x
    | negSucc k =>
      have hpos := hstep (k + 1) (x + Int.negSucc k * (w : Int))
      have hzero : x + Int.negSucc k * (w : Int) + ((k + 1 : Nat) : Int) * (w : Int) = x := by
        have : Int.negSucc k = -((k + 1 : Nat) : Int) := rfl
        rw [this, Int.neg_mul]
        omega
      rw [hzero] at hpos
      exact hpos.symm
  have hdm : (w : Int) * (z / (w : Int)) + z % (w : Int) = z := Int.mul_ediv_add_emod z (w : Int)
  have hdiv : z % (w : Int) + (z / (w : Int)) * (w : Int) = z := by
    rw [Int.mul_comm] at hdm
    omega
  have hres := hstep_int (z / (w : Int)) (z % (w : Int))
  rw [hdiv] at hres
  exact hres.symm

theorem periodicLift_ringStep {w : Nat} (hw : 0 < w) {T : Line → Line}
    (hper : ∀ s, IsPeriodic w s → IsPeriodic w (T s)) (v : BitVec w) :
    periodicLift (ringStep T v) = T (periodicLift v) := by
  unfold ringStep
  exact periodicLift_extractWindow hw (hper _ (periodicLift_periodic hw v))

theorem periodicLift_ringStep_iter {w : Nat} (hw : 0 < w) {T : Line → Line}
    (hper : ∀ s, IsPeriodic w s → IsPeriodic w (T s)) (t : Nat) (v : BitVec w) :
    periodicLift (iter (ringStep T) t v) = iter T t (periodicLift v) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [iter]
    rw [periodicLift_ringStep hw hper, ih]

theorem extractWindow_periodicLift {w : Nat} (hw : 0 < w) (v : BitVec w) :
    extractWindow (periodicLift v) 0 w = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [extractWindow_getLsbD]
  simp only [hj, ↓reduceIte, Int.zero_add]
  exact periodicLift_eq_getLsbD hw v hj

/-! ## Section 2: Reusable Pure-Data Finite-Window Local-Flux Certificate Engine -/

/-- Soundness of the finite-window verifier for ALL `u : BitVec M`. -/
theorem FluxCert.verify_sound {p r s M shiftOut : Nat}
    (c : FluxCert p r s M shiftOut) (h : c.verify = true) :
    ∀ u : BitVec M,
      c.charge (c.localNext u) - c.charge (sliceBV u shiftOut r) =
        c.flux (sliceBV u p s) - c.flux (sliceBV u 0 s) := by
  intro u
  have hpt := checkTree_sound (fun m => c.checkPoint (BitVec.ofNat M m)) M 0 h u.toNat
    (Nat.zero_le _) (by simpa using u.isLt)
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hpt
  unfold checkPoint at hpt
  exact beq_iff_eq.mp hpt

/--
  MASTER THEOREM 1 (Infinite-Line Open-Segment Discrete Gauss-Noether Continuity):
  A verified finite-window certificate lifts to exact local-flux balance on EVERY
  open interval `[a, a + n)` of EVERY infinite bit-line `s : Int -> Bool`.
-/
theorem FluxCert.open_segment_continuity {p r s M shiftOut : Nat}
    (c : FluxCert p r s M shiftOut)
    (hver : c.verify = true)
    (h1 : shiftOut + r ≤ M) (h2 : p + s ≤ M)
    {T : Line → Line}
    (hrep : LocallyRepresented p r M shiftOut c.localNext T)
    (line : Line) (a : Int) (n : Nat) :
    segmentCharge p r shiftOut c.charge (T line) a n -
      segmentCharge p r shiftOut c.charge line a n =
    c.flux (extractWindow line ((p : Int) * (a + (n : Int))) s) -
      c.flux (extractWindow line ((p : Int) * a) s) := by
  have hpt := c.verify_sound hver
  induction n with
  | zero =>
    simp [segmentCharge]
  | succ n ih =>
    simp only [segmentCharge]
    have hlocal := hpt (extractWindow line ((p : Int) * (a + (n : Int))) M)
    rw [← hrep line (a + (n : Int))] at hlocal
    rw [sliceBV_extractWindow line _ h1] at hlocal
    rw [sliceBV_extractWindow line _ h2] at hlocal
    have h0 : 0 + s ≤ M := by omega
    rw [sliceBV_extractWindow line _ h0] at hlocal
    have hidx_r : (p : Int) * (a + (n : Int)) + (p : Int) =
        (p : Int) * (a + ((n + 1 : Nat) : Int)) := by
      have hcast : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by omega
      rw [hcast, Int.mul_add, Int.mul_add, Int.mul_add, Int.mul_one]
      omega
    have hidx_l : (p : Int) * (a + (n : Int)) + ((0 : Nat) : Int) =
        (p : Int) * (a + (n : Int)) := by omega
    rw [hidx_r, hidx_l] at hlocal
    omega

/--
  MASTER THEOREM 2 (Infinite-Line Boundary-Matched Conservation):
  On ANY infinite bit-line `s : Int -> Bool`, if the two boundary windows match
  (e.g., any finite excitation on a uniform/periodic vacuum), the segment charge
  is strictly conserved.
-/
theorem FluxCert.infinite_line_conserved {p r s M shiftOut : Nat}
    (c : FluxCert p r s M shiftOut)
    (hver : c.verify = true)
    (h1 : shiftOut + r ≤ M) (h2 : p + s ≤ M)
    {T : Line → Line}
    (hrep : LocallyRepresented p r M shiftOut c.localNext T)
    (line : Line) (a : Int) (n : Nat)
    (hb : extractWindow line ((p : Int) * (a + (n : Int))) s =
          extractWindow line ((p : Int) * a) s) :
    segmentCharge p r shiftOut c.charge (T line) a n =
      segmentCharge p r shiftOut c.charge line a n := by
  have hc := c.open_segment_continuity hver h1 h2 hrep line a n
  rw [hb] at hc
  omega

/--
  MASTER THEOREM 3 (Periodic-Line All-Time Conservation):
  For ANY spatial multiplicity `n : Nat`, ANY `(p * n)`-periodic line, and ALL `t : Nat`,
  total ring charge is invariant under `iter T t`.
-/
theorem FluxCert.periodic_conserved_step {p r s M shiftOut : Nat}
    (c : FluxCert p r s M shiftOut)
    (hver : c.verify = true)
    (h1 : shiftOut + r ≤ M) (h2 : p + s ≤ M)
    {T : Line → Line}
    (hrep : LocallyRepresented p r M shiftOut c.localNext T)
    (n : Nat) (line : Line) (hp : IsPeriodic (p * n) line) :
    segmentCharge p r shiftOut c.charge (T line) 0 n =
      segmentCharge p r shiftOut c.charge line 0 n := by
  apply c.infinite_line_conserved hver h1 h2 hrep line 0 n
  have harg : (p : Int) * (0 + (n : Int)) = (p : Int) * 0 + ((p * n : Nat) : Int) := by
    simp [Int.natCast_mul]
  rw [harg]
  exact extractWindow_periodic hp ((p : Int) * 0) s

theorem FluxCert.periodic_conserved_iter {p r s M shiftOut : Nat}
    (c : FluxCert p r s M shiftOut)
    (hver : c.verify = true)
    (h1 : shiftOut + r ≤ M) (h2 : p + s ≤ M)
    {T : Line → Line}
    (hrep : LocallyRepresented p r M shiftOut c.localNext T)
    (n : Nat) (hper : ∀ line, IsPeriodic (p * n) line → IsPeriodic (p * n) (T line))
    (line : Line) (hp : IsPeriodic (p * n) line) (t : Nat) :
    segmentCharge p r shiftOut c.charge (iter T t line) 0 n =
      segmentCharge p r shiftOut c.charge line 0 n := by
  have hper_iter : ∀ k, IsPeriodic (p * n) (iter T k line) := by
    intro k
    induction k with
    | zero => exact hp
    | succ k ih => exact hper _ ih
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [iter]
    rw [c.periodic_conserved_step hver h1 h2 hrep n _ (hper_iter t), ih]

/--
  MASTER THEOREM 4 (Arbitrary-Width `BitVec (p * n)` Circuit Conservation):
  For EVERY `n >= 1`, EVERY bit-vector `v : BitVec (p * n)`, and EVERY `t : Nat`,
  the finite-width silicon circuit `ringStep T` strictly conserves `ringCharge`.
-/
theorem FluxCert.ring_conserved_iter {p r s M shiftOut : Nat}
    (c : FluxCert p r s M shiftOut)
    (hver : c.verify = true)
    (hp_pos : 0 < p) (h1 : shiftOut + r ≤ M) (h2 : p + s ≤ M)
    {T : Line → Line}
    (hrep : LocallyRepresented p r M shiftOut c.localNext T)
    (n : Nat) (hn : 0 < n)
    (hper : ∀ line, IsPeriodic (p * n) line → IsPeriodic (p * n) (T line))
    (v : BitVec (p * n)) (t : Nat) :
    ringCharge p r shiftOut c.charge (iter (ringStep T) t v) =
      ringCharge p r shiftOut c.charge v := by
  have hw : 0 < p * n := Nat.mul_pos hp_pos hn
  unfold ringCharge
  rw [periodicLift_ringStep_iter hw hper t v]
  exact c.periodic_conserved_iter hver h1 h2 hrep n hper (periodicLift v)
    (periodicLift_periodic hw v) t

theorem FluxCert.linComb_verify {p r s M shiftOut : Nat}
    (a b : Int) (c1 c2 : FluxCert p r s M shiftOut)
    (hsame : c1.localNext = c2.localNext)
    (h1 : c1.verify = true) (h2 : c2.verify = true) :
    (FluxCert.linComb a b c1 c2).verify = true := by
  have hs1 := c1.verify_sound h1
  have hs2 := c2.verify_sound h2
  unfold verify
  apply checkTree_complete
  intro m _ _
  unfold checkPoint linComb
  dsimp only
  apply beq_iff_eq.mpr
  have e1 := hs1 (BitVec.ofNat M m)
  have e2 := hs2 (BitVec.ofNat M m)
  rw [← hsame] at e2
  have hmul1 : a * (c1.charge (c1.localNext (BitVec.ofNat M m)) -
                    c1.charge (sliceBV (BitVec.ofNat M m) shiftOut r)) =
               a * (c1.flux (sliceBV (BitVec.ofNat M m) p s) -
                    c1.flux (sliceBV (BitVec.ofNat M m) 0 s)) := by
    rw [e1]
  have hmul2 : b * (c2.charge (c1.localNext (BitVec.ofNat M m)) -
                    c2.charge (sliceBV (BitVec.ofNat M m) shiftOut r)) =
               b * (c2.flux (sliceBV (BitVec.ofNat M m) p s) -
                    c2.flux (sliceBV (BitVec.ofNat M m) 0 s)) := by
    rw [e2]
  simp only [Int.mul_sub] at hmul1 hmul2
  omega

/-! ## Section 3: Two Reusable Reversible Gate-Lattice Architectures -/

/-! ### Architecture I: Generic 4-Wire Margolus Reversible Brickwork (`p = 4`) -/

theorem margolusEven_at (G : Gate4) (s : Line) (q : Int) (k : Nat) (hk : k < 4) :
    margolusEven G s (4 * q + (k : Int)) =
      proj4 (G (s (4 * q), s (4 * q + 1), s (4 * q + 2), s (4 * q + 3))) k := by
  unfold margolusEven
  dsimp only
  have hd : (4 * q + (k : Int)) / 4 = q := by omega
  have hm : (4 * q + (k : Int)) % 4 = (k : Int) := by omega
  rw [hd, hm]
  simp

theorem margolusEven_inv {G Ginv : Gate4}
    (hinv : ∀ x, Ginv (G x) = x) (s : Line) :
    margolusEven Ginv (margolusEven G s) = s := by
  funext z
  have hdiv : 4 * (z / 4) + ((z % 4).toNat : Int) = z := by omega
  have hlt : (z % 4).toNat < 4 := by omega
  have h1 : margolusEven Ginv (margolusEven G s) (4 * (z / 4) + ((z % 4).toNat : Int)) =
      proj4 (Ginv (margolusEven G s (4 * (z / 4)),
                   margolusEven G s (4 * (z / 4) + 1),
                   margolusEven G s (4 * (z / 4) + 2),
                   margolusEven G s (4 * (z / 4) + 3))) (z % 4).toNat :=
    margolusEven_at Ginv (margolusEven G s) (z / 4) (z % 4).toNat hlt
  rw [hdiv] at h1
  rw [h1]
  have e0 : margolusEven G s (4 * (z / 4)) =
      (G (s (4 * (z / 4)), s (4 * (z / 4) + 1), s (4 * (z / 4) + 2), s (4 * (z / 4) + 3))).1 := by
    simpa [proj4] using margolusEven_at G s (z / 4) 0 (by omega)
  have e1 : margolusEven G s (4 * (z / 4) + 1) =
      (G (s (4 * (z / 4)), s (4 * (z / 4) + 1), s (4 * (z / 4) + 2), s (4 * (z / 4) + 3))).2.1 := by
    simpa [proj4] using margolusEven_at G s (z / 4) 1 (by omega)
  have e2 : margolusEven G s (4 * (z / 4) + 2) =
      (G (s (4 * (z / 4)), s (4 * (z / 4) + 1), s (4 * (z / 4) + 2), s (4 * (z / 4) + 3))).2.2.1 := by
    simpa [proj4] using margolusEven_at G s (z / 4) 2 (by omega)
  have e3 : margolusEven G s (4 * (z / 4) + 3) =
      (G (s (4 * (z / 4)), s (4 * (z / 4) + 1), s (4 * (z / 4) + 2), s (4 * (z / 4) + 3))).2.2.2 := by
    simpa [proj4] using margolusEven_at G s (z / 4) 3 (by omega)
  rw [e0, e1, e2, e3]
  have hquad : ∀ (t : Bool × Bool × Bool × Bool), (t.1, t.2.1, t.2.2.1, t.2.2.2) = t := by
    intro ⟨a, b, c, d⟩; rfl
  rw [hquad, hinv]
  rcases hrem : (z % 4).toNat with _ | _ | _ | _ | k
  · simp [proj4]; congr 1; omega
  · simp [proj4]; congr 1; omega
  · simp [proj4]; congr 1; omega
  · simp [proj4]; congr 1; omega
  · omega

theorem margolusOdd_inv {G Ginv : Gate4}
    (hinv : ∀ x, Ginv (G x) = x) (s : Line) :
    margolusOdd Ginv (margolusOdd G s) = s := by
  unfold margolusOdd shiftLine
  funext z
  have hsh : (fun y => margolusEven G (fun x => s (x + 2)) (y + 2 + -2)) =
             margolusEven G (fun x => s (x + 2)) := by
    funext y; congr 1; omega
  rw [hsh]
  have hi := congrFun (margolusEven_inv hinv (fun x => s (x + 2))) (z + -2)
  simpa [Int.add_assoc] using hi

theorem margolusStep_left_inv {G Ginv : Gate4}
    (hinv : ∀ x, Ginv (G x) = x) (s : Line) :
    margolusInvStep Ginv (margolusStep G s) = s := by
  unfold margolusInvStep margolusStep
  rw [margolusOdd_inv hinv, margolusEven_inv hinv]

theorem margolusStep_right_inv {G Ginv : Gate4}
    (hinv : ∀ x, G (Ginv x) = x) (s : Line) :
    margolusStep G (margolusInvStep Ginv s) = s := by
  unfold margolusInvStep margolusStep
  rw [margolusEven_inv hinv, margolusOdd_inv hinv]

theorem margolusEven_periodic (G : Gate4) (n : Nat) (s : Line) (hp : IsPeriodic (4 * n) s) :
    IsPeriodic (4 * n) (margolusEven G s) := by
  intro z
  unfold margolusEven
  dsimp only
  have hd : (z + ((4 * n : Nat) : Int)) / 4 = z / 4 + (n : Int) := by omega
  have hm : (z + ((4 * n : Nat) : Int)) % 4 = z % 4 := by omega
  rw [hd, hm]
  have h0 : 4 * (z / 4 + (n : Int)) = 4 * (z / 4) + ((4 * n : Nat) : Int) := by omega
  have h1 : 4 * (z / 4 + (n : Int)) + 1 = (4 * (z / 4) + 1) + ((4 * n : Nat) : Int) := by omega
  have h2 : 4 * (z / 4 + (n : Int)) + 2 = (4 * (z / 4) + 2) + ((4 * n : Nat) : Int) := by omega
  have h3 : 4 * (z / 4 + (n : Int)) + 3 = (4 * (z / 4) + 3) + ((4 * n : Nat) : Int) := by omega
  rw [h1, h2, h3, h0, hp, hp, hp, hp]

theorem shiftLine_periodic (d : Int) (w : Nat) (s : Line) (hp : IsPeriodic w s) :
    IsPeriodic w (shiftLine d s) := by
  intro z
  unfold shiftLine
  have h : z + (w : Int) + d = (z + d) + (w : Int) := by omega
  rw [h, hp]

theorem margolusStep_periodic (G : Gate4) (n : Nat) (s : Line) (hp : IsPeriodic (4 * n) s) :
    IsPeriodic (4 * n) (margolusStep G s) := by
  unfold margolusStep margolusOdd
  exact shiftLine_periodic (-2) (4 * n) _
    (margolusEven_periodic G n _ (shiftLine_periodic 2 (4 * n) _ (margolusEven_periodic G n s hp)))

theorem margolusInvStep_periodic (Ginv : Gate4) (n : Nat) (s : Line) (hp : IsPeriodic (4 * n) s) :
    IsPeriodic (4 * n) (margolusInvStep Ginv s) := by
  unfold margolusInvStep margolusOdd
  exact margolusEven_periodic Ginv n _
    (shiftLine_periodic (-2) (4 * n) _
      (margolusEven_periodic Ginv n _ (shiftLine_periodic 2 (4 * n) s hp)))

/-- Finite-width `BitVec (4 * n)` bijectivity of ANY reversible Margolus 4-wire gate brickwork! -/
theorem margolusStep_ring_left_inv {G Ginv : Gate4}
    (hinv : ∀ x, Ginv (G x) = x) {n : Nat} (hn : 0 < n) (v : BitVec (4 * n)) :
    ringStep (margolusInvStep Ginv) (ringStep (margolusStep G) v) = v := by
  have hw : 0 < 4 * n := by omega
  unfold ringStep
  rw [periodicLift_extractWindow hw (margolusStep_periodic G n _ (periodicLift_periodic hw v))]
  rw [margolusStep_left_inv hinv]
  exact extractWindow_periodicLift hw v

theorem margolusStep_ring_right_inv {G Ginv : Gate4}
    (hinv : ∀ x, G (Ginv x) = x) {n : Nat} (hn : 0 < n) (v : BitVec (4 * n)) :
    ringStep (margolusStep G) (ringStep (margolusInvStep Ginv) v) = v := by
  have hw : 0 < 4 * n := by omega
  unfold ringStep
  rw [periodicLift_extractWindow hw (margolusInvStep_periodic Ginv n _ (periodicLift_periodic hw v))]
  rw [margolusStep_right_inv hinv]
  exact extractWindow_periodicLift hw v

theorem pack4_getLsbD (a b c d : Bool) (j : Nat) (hj : j < 4) :
    (pack4 a b c d).getLsbD j = proj4 (a, b, c, d) j := by
  unfold pack4
  rw [packBits_getLsbD]
  simp [hj]

theorem pack8_getLsbD (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) (j : Nat) (hj : j < 8) :
    (pack8 b0 b1 b2 b3 b4 b5 b6 b7).getLsbD j = proj8 b0 b1 b2 b3 b4 b5 b6 b7 j := by
  unfold pack8
  rw [packBits_getLsbD]
  simp [hj]

/-- Generic Local Representation Theorem: EVERY 4-wire Margolus brickwork matches `margolus4Stencil G`. -/
theorem margolusStep_localRep (G : Gate4) :
    LocallyRepresented 4 4 8 2 (margolus4Stencil G) (margolusStep G) := by
  intro s i
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [extractWindow_getLsbD]
  simp only [hj, ↓reduceIte]
  unfold margolus4Stencil
  rw [pack4_getLsbD _ _ _ _ j hj]
  unfold margolusStep margolusOdd shiftLine
  have h2 : ((4 : Nat) : Int) * i + ((2 : Nat) : Int) + (j : Int) + -2 = 4 * i + (j : Int) := by omega
  rw [h2]
  rw [margolusEven_at G (fun z => margolusEven G s (z + 2)) i j hj]
  have m0 : margolusEven G s (4 * i + 2) =
      proj4 (G (s (4 * i), s (4 * i + 1), s (4 * i + 2), s (4 * i + 3))) 2 :=
    margolusEven_at G s i 2 (by omega)
  have m1 : margolusEven G s (4 * i + 1 + 2) =
      proj4 (G (s (4 * i), s (4 * i + 1), s (4 * i + 2), s (4 * i + 3))) 3 := by
    have : (4 * i + 1 + 2 : Int) = 4 * i + ((3 : Nat) : Int) := by omega
    rw [this]; exact margolusEven_at G s i 3 (by omega)
  have m2 : margolusEven G s (4 * i + 2 + 2) =
      proj4 (G (s (4 * (i + 1)), s (4 * (i + 1) + 1), s (4 * (i + 1) + 2), s (4 * (i + 1) + 3))) 0 := by
    have : (4 * i + 2 + 2 : Int) = 4 * (i + 1) + ((0 : Nat) : Int) := by omega
    rw [this]; exact margolusEven_at G s (i + 1) 0 (by omega)
  have m3 : margolusEven G s (4 * i + 3 + 2) =
      proj4 (G (s (4 * (i + 1)), s (4 * (i + 1) + 1), s (4 * (i + 1) + 2), s (4 * (i + 1) + 3))) 1 := by
    have : (4 * i + 3 + 2 : Int) = 4 * (i + 1) + ((1 : Nat) : Int) := by omega
    rw [this]; exact margolusEven_at G s (i + 1) 1 (by omega)
  rw [m0, m1, m2, m3]
  simp only [extractWindow_getLsbD, show (0 : Nat) < 8 by omega, show (1 : Nat) < 8 by omega,
    show (2 : Nat) < 8 by omega, show (3 : Nat) < 8 by omega, show (4 : Nat) < 8 by omega,
    show (5 : Nat) < 8 by omega, show (6 : Nat) < 8 by omega, show (7 : Nat) < 8 by omega,
    ↓reduceIte, proj4]
  have s0 : ((4 : Nat) : Int) * i + ((0 : Nat) : Int) = 4 * i := by omega
  have s1 : ((4 : Nat) : Int) * i + ((1 : Nat) : Int) = 4 * i + 1 := by omega
  have s2 : ((4 : Nat) : Int) * i + ((2 : Nat) : Int) = 4 * i + 2 := by omega
  have s3 : ((4 : Nat) : Int) * i + ((3 : Nat) : Int) = 4 * i + 3 := by omega
  have s4 : ((4 : Nat) : Int) * i + ((4 : Nat) : Int) = 4 * (i + 1) := by omega
  have s5 : ((4 : Nat) : Int) * i + ((5 : Nat) : Int) = 4 * (i + 1) + 1 := by omega
  have s6 : ((4 : Nat) : Int) * i + ((6 : Nat) : Int) = 4 * (i + 1) + 2 := by omega
  have s7 : ((4 : Nat) : Int) * i + ((7 : Nat) : Int) = 4 * (i + 1) + 3 := by omega
  rw [s0, s1, s2, s3, s4, s5, s6, s7]

/-! ### Architecture II: Generic 2-Sublattice Controlled-NOT Brickwork (`p = 2`) -/

theorem subOddLayer_inv (f1 : Bool → Bool → Bool) (s : Line) :
    subOddLayer f1 (subOddLayer f1 s) = s := by
  funext z
  unfold subOddLayer
  by_cases h : z % 2 = 1
  · have hm : (z - 1) % 2 ≠ 1 := by omega
    have hp : (z + 1) % 2 ≠ 1 := by omega
    simp only [h, hm, hp, ↓reduceIte]
    cases s z <;> cases f1 (s (z - 1)) (s (z + 1)) <;> rfl
  · simp [h]

theorem subEvenLayer_inv (f2 : Bool → Bool → Bool) (s : Line) :
    subEvenLayer f2 (subEvenLayer f2 s) = s := by
  funext z
  unfold subEvenLayer
  by_cases h : z % 2 = 0
  · have hm : (z - 1) % 2 ≠ 0 := by omega
    have hp : (z + 1) % 2 ≠ 0 := by omega
    simp only [h, hm, hp, ↓reduceIte]
    cases s z <;> cases f2 (s (z - 1)) (s (z + 1)) <;> rfl
  · simp [h]

theorem subCNOTStep_left_inv (f1 f2 : Bool → Bool → Bool) (s : Line) :
    subCNOTInvStep f1 f2 (subCNOTStep f1 f2 s) = s := by
  unfold subCNOTInvStep subCNOTStep
  rw [subEvenLayer_inv, subOddLayer_inv]

theorem subCNOTStep_right_inv (f1 f2 : Bool → Bool → Bool) (s : Line) :
    subCNOTStep f1 f2 (subCNOTInvStep f1 f2 s) = s := by
  unfold subCNOTInvStep subCNOTStep
  rw [subOddLayer_inv, subEvenLayer_inv]

theorem subOddLayer_periodic (f1 : Bool → Bool → Bool) (n : Nat) (s : Line)
    (hp : IsPeriodic (2 * n) s) : IsPeriodic (2 * n) (subOddLayer f1 s) := by
  intro z
  unfold subOddLayer
  have hm : (z + ((2 * n : Nat) : Int)) % 2 = z % 2 := by omega
  have h1 : z + ((2 * n : Nat) : Int) - 1 = (z - 1) + ((2 * n : Nat) : Int) := by omega
  have h2 : z + ((2 * n : Nat) : Int) + 1 = (z + 1) + ((2 * n : Nat) : Int) := by omega
  rw [hm, h1, h2, hp, hp, hp]

theorem subEvenLayer_periodic (f2 : Bool → Bool → Bool) (n : Nat) (s : Line)
    (hp : IsPeriodic (2 * n) s) : IsPeriodic (2 * n) (subEvenLayer f2 s) := by
  intro z
  unfold subEvenLayer
  have hm : (z + ((2 * n : Nat) : Int)) % 2 = z % 2 := by omega
  have h1 : z + ((2 * n : Nat) : Int) - 1 = (z - 1) + ((2 * n : Nat) : Int) := by omega
  have h2 : z + ((2 * n : Nat) : Int) + 1 = (z + 1) + ((2 * n : Nat) : Int) := by omega
  rw [hm, h1, h2, hp, hp, hp]

theorem subCNOTStep_periodic (f1 f2 : Bool → Bool → Bool) (n : Nat) (s : Line)
    (hp : IsPeriodic (2 * n) s) : IsPeriodic (2 * n) (subCNOTStep f1 f2 s) :=
  subEvenLayer_periodic f2 n _ (subOddLayer_periodic f1 n s hp)

theorem subCNOTInvStep_periodic (f1 f2 : Bool → Bool → Bool) (n : Nat) (s : Line)
    (hp : IsPeriodic (2 * n) s) : IsPeriodic (2 * n) (subCNOTInvStep f1 f2 s) :=
  subOddLayer_periodic f1 n _ (subEvenLayer_periodic f2 n s hp)

/-- Finite-width `BitVec (2 * n)` bijectivity of ANY 2-sublattice CNOT brickwork! -/
theorem subCNOTStep_ring_left_inv (f1 f2 : Bool → Bool → Bool)
    {n : Nat} (hn : 0 < n) (v : BitVec (2 * n)) :
    ringStep (subCNOTInvStep f1 f2) (ringStep (subCNOTStep f1 f2) v) = v := by
  have hw : 0 < 2 * n := by omega
  unfold ringStep
  rw [periodicLift_extractWindow hw (subCNOTStep_periodic f1 f2 n _ (periodicLift_periodic hw v))]
  rw [subCNOTStep_left_inv]
  exact extractWindow_periodicLift hw v

theorem subCNOTStep_ring_right_inv (f1 f2 : Bool → Bool → Bool)
    {n : Nat} (hn : 0 < n) (v : BitVec (2 * n)) :
    ringStep (subCNOTStep f1 f2) (ringStep (subCNOTInvStep f1 f2) v) = v := by
  have hw : 0 < 2 * n := by omega
  unfold ringStep
  rw [periodicLift_extractWindow hw (subCNOTInvStep_periodic f1 f2 n _ (periodicLift_periodic hw v))]
  rw [subCNOTStep_right_inv]
  exact extractWindow_periodicLift hw v

/-- Generic Local Representation Theorem: EVERY 2-sublattice CNOT brickwork matches `subCNOTStencil`. -/
theorem subCNOTStep_localRep (f1 f2 : Bool → Bool → Bool) :
    LocallyRepresented 2 4 8 2 (subCNOTStencil f1 f2) (subCNOTStep f1 f2) := by
  intro s i
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [extractWindow_getLsbD]
  simp only [hj, ↓reduceIte]
  unfold subCNOTStencil
  rw [pack4_getLsbD _ _ _ _ j hj]
  simp only [extractWindow_getLsbD, show (0 : Nat) < 8 by omega, show (1 : Nat) < 8 by omega,
    show (2 : Nat) < 8 by omega, show (3 : Nat) < 8 by omega, show (4 : Nat) < 8 by omega,
    show (5 : Nat) < 8 by omega, show (6 : Nat) < 8 by omega, ↓reduceIte]
  unfold subCNOTStep subEvenLayer subOddLayer
  rcases j with _ | _ | _ | _ | k
  · have hm0 : (((2 : Nat) : Int) * i + ((2 : Nat) : Int) + ((0 : Nat) : Int)) % 2 = 0 := by omega
    have hm_l : (((2 : Nat) : Int) * i + ((2 : Nat) : Int) + ((0 : Nat) : Int) - 1) % 2 = 1 := by omega
    have hm_r : (((2 : Nat) : Int) * i + ((2 : Nat) : Int) + ((0 : Nat) : Int) + 1) % 2 = 1 := by omega
    simp only [hm0, hm_l, hm_r, ↓reduceIte, proj4]
    have a0 : ((2 : Nat) : Int) * i + ((2 : Nat) : Int) + ((0 : Nat) : Int) = ((2 : Nat) : Int) * i + ((2 : Nat) : Int) := by omega
    have a1 : ((2 : Nat) : Int) * i + ((2 : Nat) : Int) + ((0 : Nat) : Int) - 1 = ((2 : Nat) : Int) * i + ((1 : Nat) : Int) := by omega
    have a2 : ((2 : Nat) : Int) * i + ((2 : Nat) : Int) + ((0 : Nat) : Int) - 1 - 1 = ((2 : Nat) : Int) * i + ((0 : Nat) : Int) := by omega
    have a3 : ((2 : Nat) : Int) * i + ((2 : Nat) : Int) + ((0 : Nat) : Int) - 1 + 1 = ((2 : Nat) : Int) * i + ((2 : Nat) : Int) := by omega
    have a4 : ((2 : Nat) : Int) * i + ((2 : Nat) : Int) + ((0 : Nat) : Int) + 1 = ((2 : Nat) : Int) * i + ((3 : Nat) : Int) := by omega
    have a5 : ((2 : Nat) : Int) * i + ((2 : Nat) : Int) + ((0 : Nat) : Int) + 1 - 1 = ((2 : Nat) : Int) * i + ((2 : Nat) : Int) := by omega
    have a6 : ((2 : Nat) : Int) * i + ((2 : Nat) : Int) + ((0 : Nat) : Int) + 1 + 1 = ((2 : Nat) : Int) * i + ((4 : Nat) : Int) := by omega
    rw [a2, a3, a5, a6, a1, a4, a0]; rfl
  · have hm1 : (((2 : Nat) : Int) * i + ((2 : Nat) : Int) + ((1 : Nat) : Int)) % 2 = 1 := by omega
    simp only [hm1, ↓reduceIte, proj4]
    have a0 : ((2 : Nat) : Int) * i + ((2 : Nat) : Int) + ((1 : Nat) : Int) = ((2 : Nat) : Int) * i + ((3 : Nat) : Int) := by omega
    have a1 : ((2 : Nat) : Int) * i + ((2 : Nat) : Int) + ((1 : Nat) : Int) - 1 = ((2 : Nat) : Int) * i + ((2 : Nat) : Int) := by omega
    have a2 : ((2 : Nat) : Int) * i + ((2 : Nat) : Int) + ((1 : Nat) : Int) + 1 = ((2 : Nat) : Int) * i + ((4 : Nat) : Int) := by omega
    rw [a1, a2, a0]; rfl
  · have hm0 : (((2 : Nat) : Int) * i + ((2 : Nat) : Int) + ((2 : Nat) : Int)) % 2 = 0 := by omega
    have hm_l : (((2 : Nat) : Int) * i + ((2 : Nat) : Int) + ((2 : Nat) : Int) - 1) % 2 = 1 := by omega
    have hm_r : (((2 : Nat) : Int) * i + ((2 : Nat) : Int) + ((2 : Nat) : Int) + 1) % 2 = 1 := by omega
    simp only [hm0, hm_l, hm_r, ↓reduceIte, proj4]
    have a0 : ((2 : Nat) : Int) * i + ((2 : Nat) : Int) + ((2 : Nat) : Int) = ((2 : Nat) : Int) * i + ((4 : Nat) : Int) := by omega
    have a1 : ((2 : Nat) : Int) * i + ((2 : Nat) : Int) + ((2 : Nat) : Int) - 1 = ((2 : Nat) : Int) * i + ((3 : Nat) : Int) := by omega
    have a2 : ((2 : Nat) : Int) * i + ((2 : Nat) : Int) + ((2 : Nat) : Int) - 1 - 1 = ((2 : Nat) : Int) * i + ((2 : Nat) : Int) := by omega
    have a3 : ((2 : Nat) : Int) * i + ((2 : Nat) : Int) + ((2 : Nat) : Int) - 1 + 1 = ((2 : Nat) : Int) * i + ((4 : Nat) : Int) := by omega
    have a4 : ((2 : Nat) : Int) * i + ((2 : Nat) : Int) + ((2 : Nat) : Int) + 1 = ((2 : Nat) : Int) * i + ((5 : Nat) : Int) := by omega
    have a5 : ((2 : Nat) : Int) * i + ((2 : Nat) : Int) + ((2 : Nat) : Int) + 1 - 1 = ((2 : Nat) : Int) * i + ((4 : Nat) : Int) := by omega
    have a6 : ((2 : Nat) : Int) * i + ((2 : Nat) : Int) + ((2 : Nat) : Int) + 1 + 1 = ((2 : Nat) : Int) * i + ((6 : Nat) : Int) := by omega
    rw [a2, a3, a5, a6, a1, a4, a0]; rfl
  · have hm1 : (((2 : Nat) : Int) * i + ((2 : Nat) : Int) + ((3 : Nat) : Int)) % 2 = 1 := by omega
    simp only [hm1, ↓reduceIte, proj4]
    have a0 : ((2 : Nat) : Int) * i + ((2 : Nat) : Int) + ((3 : Nat) : Int) = ((2 : Nat) : Int) * i + ((5 : Nat) : Int) := by omega
    have a1 : ((2 : Nat) : Int) * i + ((2 : Nat) : Int) + ((3 : Nat) : Int) - 1 = ((2 : Nat) : Int) * i + ((4 : Nat) : Int) := by omega
    have a2 : ((2 : Nat) : Int) * i + ((2 : Nat) : Int) + ((3 : Nat) : Int) + 1 = ((2 : Nat) : Int) * i + ((6 : Nat) : Int) := by omega
    rw [a1, a2, a0]; rfl
  · omega

/-! ## Section 4: Textbook Fredkin/Toffoli Silicon Gates & Concrete Infinite Theorems -/

theorem fredkin_1_02_inv (x : Bool × Bool × Bool × Bool) :
    fredkin_1_02 (fredkin_1_02 x) = x := by
  rcases x with ⟨a, b, c, d⟩; cases b <;> rfl

theorem cnotH_1_inv (h : Bool → Bool → Bool → Bool) (x : Bool × Bool × Bool × Bool) :
    cnotH_1 h (cnotH_1 h x) = x := by
  rcases x with ⟨a, b, c, d⟩; simp [cnotH_1]

theorem gateFredCNOT_left_inv (h : Bool → Bool → Bool → Bool) (x : Bool × Bool × Bool × Bool) :
    gateFredCNOT_inv h (gateFredCNOT h x) = x := by
  unfold gateFredCNOT_inv gateFredCNOT
  rw [cnotH_1_inv, fredkin_1_02_inv]

theorem gateFredCNOT_right_inv (h : Bool → Bool → Bool → Bool) (x : Bool × Bool × Bool × Bool) :
    gateFredCNOT h (gateFredCNOT_inv h x) = x := by
  unfold gateFredCNOT_inv gateFredCNOT
  rw [fredkin_1_02_inv, cnotH_1_inv]

theorem hFromMask_maskOfH (h : Bool → Bool → Bool → Bool) :
    hFromMask (maskOfH h) = h := by
  funext a c d
  unfold hFromMask maskOfH
  cases a <;> cases c <;> cases d <;>
  · rw [pack8_getLsbD _ _ _ _ _ _ _ _ _ (by decide)]; rfl

theorem ringStep_margolus_eq_step8Fast (G : Gate4) (v : BitVec 8) :
    ringStep (margolusStep G) v = step8Fast G v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  unfold ringStep step8Fast
  rw [extractWindow_getLsbD, pack8_getLsbD _ _ _ _ _ _ _ _ j hj]
  simp only [hj, ↓reduceIte, Int.zero_add]
  have hlift : ∀ z : Int, periodicLift v z = v.getLsbD (z % 8).toNat := by
    intro z; unfold periodicLift; simp
  unfold margolusStep margolusOdd margolusEven shiftLine
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | k <;> try omega
  all_goals simp [hlift, proj4, proj8]

theorem ringCharge_eq_Q8Fast (v : BitVec 8) :
    @ringCharge 4 4 2 q_FT 2 v = Q8Fast v := by
  simp only [ringCharge, segmentCharge, Q8Fast]
  have h0 : extractWindow (periodicLift v) ((4 : Nat) * (0 + (0 : Nat)) + (2 : Nat)) 4 =
      pack4 (v.getLsbD 2) (v.getLsbD 3) (v.getLsbD 4) (v.getLsbD 5) := by
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    rw [extractWindow_getLsbD, pack4_getLsbD _ _ _ _ j hj]
    simp only [hj, ↓reduceIte]
    rcases j with _ | _ | _ | _ | k <;> try omega
    all_goals (unfold periodicLift; simp [proj4])
  have h1 : extractWindow (periodicLift v) ((4 : Nat) * (0 + (1 : Nat)) + (2 : Nat)) 4 =
      pack4 (v.getLsbD 6) (v.getLsbD 7) (v.getLsbD 0) (v.getLsbD 1) := by
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    rw [extractWindow_getLsbD, pack4_getLsbD _ _ _ _ j hj]
    simp only [hj, ↓reduceIte]
    rcases j with _ | _ | _ | _ | k <;> try omega
    all_goals (unfold periodicLift; simp [proj4])
  rw [h0, h1]; omega

theorem checkAllMasks_true :
    checkTree (fun k => let m := BitVec.ofNat 8 k; checkThreeVectors m == isIdealMaskBV m) 8 0 = true := by
  decide

theorem verifyAllIdealMasks_true : verifyAllIdealMasks = true := by decide

theorem idealMaskDec_eq_isIdealMaskBV :
    checkTree (fun k => let m := BitVec.ofNat 8 k; idealMaskDec m == isIdealMaskBV m) 8 0 = true := by
  decide

theorem idealMask_iff_isIdealMaskBV (m : BitVec 8) :
    IdealMask (hFromMask m) ↔ isIdealMaskBV m = true := by
  have h1 := checkTree_sound _ 8 0 idealMaskDec_eq_isIdealMaskBV m.toNat (Nat.zero_le _) (by simpa using m.isLt)
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at h1
  have heq : idealMaskDec m = isIdealMaskBV m := beq_iff_eq.mp h1
  rw [← heq]
  unfold IdealMask idealMaskDec
  simp only [List.all_eq_true, List.mem_cons, List.not_mem_nil, or_false, Bool.or_eq_true,
    Bool.not_eq_true']
  constructor
  · intro hid a _ c _ d _
    by_cases hval : hFromMask m a c d = true
    · exact Or.inr (hid a c d hval)
    · exact Or.inl (Bool.eq_false_iff.mpr hval)
  · intro hall a c d hval
    have ha : a = false ∨ a = true := by cases a <;> simp
    have hc : c = false ∨ c = true := by cases c <;> simp
    have hd : d = false ∨ d = true := by cases d <;> simp
    rcases hall a ha c hc d hd with hfalse | htrue
    · rw [hval] at hfalse; cases hfalse
    · exact htrue

theorem idealMask_mem_eight_tree :
    checkTree (fun k =>
      let m := BitVec.ofNat 8 k
      !(isIdealMaskBV m) ||
        ([0#8, 8#8, 32#8, 40#8, 128#8, 136#8, 160#8, 168#8].any (fun x => x == m))) 8 0 = true := by
  decide

theorem idealMask_mem_eight (m : BitVec 8) (hm : isIdealMaskBV m = true) :
    m ∈ [0#8, 8#8, 32#8, 40#8, 128#8, 136#8, 160#8, 168#8] := by
  have h1 := checkTree_sound _ 8 0 idealMask_mem_eight_tree m.toNat (Nat.zero_le _) (by simpa using m.isLt)
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at h1
  simp only [hm, Bool.not_true, Bool.false_or, List.any_eq_true, beq_iff_eq] at h1
  rcases h1 with ⟨x, hx, heq⟩
  subst heq
  exact hx

/--
  CROWN JEWEL THEOREM (Exact 4-Way IFF Classification & 3-Vector Finite-to-Infinite Completeness):
  For ANY Boolean control function `h : Bool -> Bool -> Bool -> Bool` in the 256-gate
  reversible Fredkin-Controlled-NOT family `G_h = CNOT_h(0,2,3->1) o Fredkin(1; 0, 2)`:
    (1) IdealMask h : `forall a c d, h a c d = true -> (a && (c || d)) = true`
    (2) Certificate : `(certFredCNOT h).verify = true`
    (3) All-Width All-Time Conservation :
        `forall n >= 1, forall v : BitVec (4*n), forall t, Q_FT (T_h^[t] v) = Q_FT v`
    (4) 3-Vector Width-8 Test :
        `Q_FT (T_h v) = Q_FT v` on just `v in {0x04, 0x08, 0x0B}`!
  All four conditions are logically equivalent!
-/
theorem fredkin_cnot_iff_1_2 (h : Bool → Bool → Bool → Bool) :
    IdealMask h ↔ (certFredCNOT h).verify = true := by
  have hrew : h = hFromMask (maskOfH h) := (hFromMask_maskOfH h).symm
  constructor
  · intro hid
    rw [hrew] at hid ⊢
    have hbv := (idealMask_iff_isIdealMaskBV (maskOfH h)).mp hid
    have hmem := idealMask_mem_eight (maskOfH h) hbv
    exact List.all_eq_true.mp verifyAllIdealMasks_true (maskOfH h) hmem
  · intro hver
    have h3 : checkThreeVectors (maskOfH h) = true := by
      have hring := fun v : BitVec 8 =>
        (certFredCNOT h).ring_conserved_iter hver (by omega) (by omega) (by omega)
          (margolusStep_localRep (gateFredCNOT h)) 2 (by omega)
          (margolusStep_periodic (gateFredCNOT h) 2) v 1
      have heq : ∀ v : BitVec 8,
          Q8Fast (step8Fast (gateFredCNOT (hFromMask (maskOfH h))) v) = Q8Fast v := by
        intro v
        have hv := hring v
        simp only [iter, certFredCNOT] at hv
        rw [ringCharge_eq_Q8Fast, ringCharge_eq_Q8Fast, ringStep_margolus_eq_step8Fast] at hv
        rw [← hrew]
        exact hv
      unfold checkThreeVectors
      simp [heq 4#8, heq 8#8, heq 11#8]
    have hsound := checkTree_sound _ 8 0 checkAllMasks_true (maskOfH h).toNat (Nat.zero_le _) (by simpa using (maskOfH h).isLt)
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hsound
    have hbv : isIdealMaskBV (maskOfH h) = true := by
      rw [← beq_iff_eq.mp hsound]; exact h3
    rw [hrew]
    exact (idealMask_iff_isIdealMaskBV (maskOfH h)).mpr hbv

theorem fredkin_cnot_classification_1_to_3 (h : Bool → Bool → Bool → Bool)
    (hid : IdealMask h) (n : Nat) (hn : 0 < n) (v : BitVec (4 * n)) (t : Nat) :
    ringCharge 4 4 2 q_FT (iter (ringStep (margolusStep (gateFredCNOT h))) t v) =
      ringCharge 4 4 2 q_FT v := by
  have hver := (fredkin_cnot_iff_1_2 h).mp hid
  exact (certFredCNOT h).ring_conserved_iter hver (by omega) (by omega) (by omega)
    (margolusStep_localRep (gateFredCNOT h)) n hn
    (margolusStep_periodic (gateFredCNOT h) n) v t

theorem fredkin_cnot_classification_3_to_4 (h : Bool → Bool → Bool → Bool)
    (hall : ∀ n : Nat, 0 < n → ∀ (v : BitVec (4 * n)) (t : Nat),
      ringCharge 4 4 2 q_FT (iter (ringStep (margolusStep (gateFredCNOT h))) t v) =
        ringCharge 4 4 2 q_FT v) :
    (@ringCharge 4 4 2 q_FT 2 (ringStep (margolusStep (gateFredCNOT h)) 4#8) = @ringCharge 4 4 2 q_FT 2 4#8) ∧
    (@ringCharge 4 4 2 q_FT 2 (ringStep (margolusStep (gateFredCNOT h)) 8#8) = @ringCharge 4 4 2 q_FT 2 8#8) ∧
    (@ringCharge 4 4 2 q_FT 2 (ringStep (margolusStep (gateFredCNOT h)) 11#8) = @ringCharge 4 4 2 q_FT 2 11#8) :=
  ⟨hall 2 (by omega) 4#8 1, hall 2 (by omega) 8#8 1, hall 2 (by omega) 11#8 1⟩

theorem fredkin_cnot_classification_4_to_1 (h : Bool → Bool → Bool → Bool)
    (h4 : (@ringCharge 4 4 2 q_FT 2 (ringStep (margolusStep (gateFredCNOT h)) 4#8) = @ringCharge 4 4 2 q_FT 2 4#8) ∧
          (@ringCharge 4 4 2 q_FT 2 (ringStep (margolusStep (gateFredCNOT h)) 8#8) = @ringCharge 4 4 2 q_FT 2 8#8) ∧
          (@ringCharge 4 4 2 q_FT 2 (ringStep (margolusStep (gateFredCNOT h)) 11#8) = @ringCharge 4 4 2 q_FT 2 11#8)) :
    IdealMask h := by
  have hrew : h = hFromMask (maskOfH h) := (hFromMask_maskOfH h).symm
  have h3 : checkThreeVectors (maskOfH h) = true := by
    rcases h4 with ⟨e4, e8, e11⟩
    rw [ringCharge_eq_Q8Fast, ringCharge_eq_Q8Fast, ringStep_margolus_eq_step8Fast] at e4 e8 e11
    unfold checkThreeVectors
    rw [← hrew]
    simp [e4, e8, e11]
  have hsound := checkTree_sound _ 8 0 checkAllMasks_true (maskOfH h).toNat (Nat.zero_le _) (by simpa using (maskOfH h).isLt)
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hsound
  have hbv : isIdealMaskBV (maskOfH h) = true := by
    rw [← beq_iff_eq.mp hsound]; exact h3
  rw [hrew]
  exact (idealMask_iff_isIdealMaskBV (maskOfH h)).mpr hbv

theorem gateFT_ideal : IdealMask (fun a _ d => a && d) := by
  intro a c d h; cases a <;> cases c <;> cases d <;> simp_all

theorem fredkin_toffoli_conserved_all_widths (n : Nat) (hn : 0 < n) (v : BitVec (4 * n)) (t : Nat) :
    ringCharge 4 4 2 q_FT (iter (ringStep (margolusStep gateFT)) t v) = ringCharge 4 4 2 q_FT v :=
  fredkin_cnot_classification_1_to_3 _ gateFT_ideal n hn v t

theorem fredkin_toffoli_open_segment_continuity (s : Line) (a : Int) (n : Nat) :
    segmentCharge 4 4 2 q_FT (margolusStep gateFT s) a n -
      segmentCharge 4 4 2 q_FT s a n =
    J_FT (extractWindow s ((4 : Int) * (a + (n : Int))) 4) -
      J_FT (extractWindow s ((4 : Int) * a) 4) := by
  have hver := (fredkin_cnot_iff_1_2 (fun a _ d => a && d)).mp gateFT_ideal
  exact (certFredCNOT _).open_segment_continuity hver (by omega) (by omega)
    (margolusStep_localRep gateFT) s a n

theorem fredkin_toffoli_reversible_all_widths (n : Nat) (hn : 0 < n) (v : BitVec (4 * n)) :
    ringStep (margolusInvStep gateFT_inv) (ringStep (margolusStep gateFT) v) = v ∧
    ringStep (margolusStep gateFT) (ringStep (margolusInvStep gateFT_inv) v) = v :=
  ⟨margolusStep_ring_left_inv (gateFredCNOT_left_inv _) hn v,
   margolusStep_ring_right_inv (gateFredCNOT_right_inv _) hn v⟩

/-! ### Theorem Family 2: Cascaded Double-Fredkin Brickwork (`F(3;1,2) ; F(1;0,3)`) — 3-Charge Algebra -/

theorem gateFF_left_inv (x : Bool × Bool × Bool × Bool) : gateFF_inv (gateFF x) = x := by
  rcases x with ⟨a, b, c, d⟩; cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem gateFF_right_inv (x : Bool × Bool × Bool × Bool) : gateFF (gateFF_inv x) = x := by
  rcases x with ⟨a, b, c, d⟩; cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem certFF_HW_ok    : certFF_HW.verify = true := by decide

theorem certFF_dimer_ok : certFF_dimer.verify = true := by decide

theorem certFF_rail_ok  : certFF_rail.verify = true := by decide

/-- Certified algebraically via Master Theorem 5 without re-enumerating! -/
theorem certFF_asym_ok  : certFF_asym.verify = true :=
  FluxCert.linComb_verify 1 (-1) certFF_rail certFF_dimer rfl certFF_rail_ok certFF_dimer_ok

theorem double_fredkin_three_laws_all_widths (n : Nat) (hn : 0 < n) (v : BitVec (4 * n)) (t : Nat) :
    ringCharge 4 4 2 q_HW4   (iter (ringStep (margolusStep gateFF)) t v) = ringCharge 4 4 2 q_HW4   v ∧
    ringCharge 4 4 2 q_dimer (iter (ringStep (margolusStep gateFF)) t v) = ringCharge 4 4 2 q_dimer v ∧
    ringCharge 4 4 2 q_rail  (iter (ringStep (margolusStep gateFF)) t v) = ringCharge 4 4 2 q_rail  v ∧
    ringCharge 4 4 2 certFF_asym.charge (iter (ringStep (margolusStep gateFF)) t v) =
      ringCharge 4 4 2 certFF_asym.charge v :=
  ⟨certFF_HW.ring_conserved_iter    certFF_HW_ok    (by omega) (by omega) (by omega) (margolusStep_localRep gateFF) n hn (margolusStep_periodic gateFF n) v t,
   certFF_dimer.ring_conserved_iter certFF_dimer_ok (by omega) (by omega) (by omega) (margolusStep_localRep gateFF) n hn (margolusStep_periodic gateFF n) v t,
   certFF_rail.ring_conserved_iter  certFF_rail_ok  (by omega) (by omega) (by omega) (margolusStep_localRep gateFF) n hn (margolusStep_periodic gateFF n) v t,
   certFF_asym.ring_conserved_iter  certFF_asym_ok  (by omega) (by omega) (by omega) (margolusStep_localRep gateFF) n hn (margolusStep_periodic gateFF n) v t⟩

/-! ### Theorem Family 3: Dual-Control Fredkin (`CCSWAP(a^d) = F(0;1,2) ; F(3;1,2)`) — Cubic-Flux Law -/

theorem gateDF_inv (x : Bool × Bool × Bool × Bool) : gateDF (gateDF x) = x := by
  rcases x with ⟨a, b, c, d⟩; cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem certDF_ok : certDF.verify = true := by decide

theorem dual_fredkin_conserved_all_widths (n : Nat) (hn : 0 < n) (v : BitVec (4 * n)) (t : Nat) :
    ringCharge 4 4 2 q_DF (iter (ringStep (margolusStep gateDF)) t v) = ringCharge 4 4 2 q_DF v :=
  certDF.ring_conserved_iter certDF_ok (by omega) (by omega) (by omega)
    (margolusStep_localRep gateDF) n hn (margolusStep_periodic gateDF n) v t

/-! ### Theorem Family 4: Period-2 Sublattice Controlled-NOT Brickworks (Multi-Topology Reuse!) -/

theorem certCO_ok : certCO.verify = true := by decide

theorem subcnot_xor_or_conserved_all_widths (n : Nat) (hn : 0 < n) (v : BitVec (2 * n)) (t : Nat) :
    ringCharge 2 4 2 q_CO (iter (ringStep (subCNOTStep f_xor f_or)) t v) =
      ringCharge 2 4 2 q_CO v :=
  certCO.ring_conserved_iter certCO_ok (by omega) (by omega) (by omega)
    (subCNOTStep_localRep f_xor f_or) n hn (subCNOTStep_periodic f_xor f_or n) v t

theorem certDW_ok : certDW.verify = true := by decide

theorem subcnot_chiral_domain_wall_conserved_all_widths (n : Nat) (hn : 0 < n) (v : BitVec (2 * n)) (t : Nat) :
    ringCharge 2 4 2 q_DW (iter (ringStep (subCNOTStep f_impL f_impR)) t v) =
      ringCharge 2 4 2 q_DW v :=
  certDW.ring_conserved_iter certDW_ok (by omega) (by omega) (by omega)
    (subCNOTStep_localRep f_impL f_impR) n hn (subCNOTStep_periodic f_impL f_impR n) v t

/-! ## Section 5: Non-Vacuity Witnesses, Sharpness Counterexamples, and Negative Mutation Checks -/

/-- Non-vacuity 1: `gateFT` strictly BREAKS Hamming weight (`2 -> 3`) while conserving `q_FT = -1`! -/
theorem witness_FT_breaks_HW_conserves_Q :
    hw8 (step8Fast gateFT 9#8) ≠ hw8 9#8 ∧
    Q8Fast (step8Fast gateFT 9#8) = Q8Fast 9#8 := by decide

/-- Non-vacuity 2: `gateFT` is dynamically non-trivial (neither identity nor involution at `w = 8`)! -/
theorem witness_FT_nontrivial_dynamics :
    step8Fast gateFT 9#8 ≠ 9#8 ∧
    step8Fast gateFT (step8Fast gateFT 9#8) ≠ 9#8 := by decide

/-- Non-vacuity 3: `q_FT` is non-constant (`Q8Fast 0 ≠ Q8Fast 9`) and has genuine NON-ZERO boundary flux! -/
theorem witness_FT_nonconstant_and_nonzero_flux :
    Q8Fast 0#8 ≠ Q8Fast 9#8 ∧
    J_FT (sliceBV 6#8 4 4) - J_FT (sliceBV 6#8 0 4) ≠ 0 := by decide

theorem witness_FF_beyond_HW_independence :
    (Q8_HW 0x0C#8 = 2 ∧ Q8_HW 0x14#8 = 2 ∧ Q8_HW 0x24#8 = 2) ∧
    (Q8_dimer 0x0C#8 = 1 ∧ Q8_rail 0x0C#8 = 1) ∧
    (Q8_dimer 0x14#8 = 0 ∧ Q8_rail 0x14#8 = 1) ∧
    (Q8_dimer 0x24#8 = 0 ∧ Q8_rail 0x24#8 = 2) := by decide

theorem witness_DF_beyond_HW :
    hw8 0x04#8 = hw8 0x10#8 ∧ Q8_DF 0x04#8 ≠ Q8_DF 0x10#8 := by decide

theorem mutation_zero_flux_rejected : certFT_zeroFlux.verify = false := by decide

theorem sharpness_mut_cd_rejected_and_counterexample :
    certFT_mut_cd.verify = false ∧
    Q8Fast (step8Fast gateFT_mut_cd 11#8) ≠ Q8Fast 11#8 := by decide

theorem sharpness_mut_fred_rejected_and_counterexample :
    certFT_mut_fred.verify = false ∧
    Q8Fast (step8Fast gateFT_mut_fred 3#8) ≠ Q8Fast 3#8 := by decide

theorem witness_subcnot_breaks_HW :
    hw6 (step6Sub f_xor f_or 1#6) ≠ hw6 1#6 ∧
    hw6 (step6Sub f_impL f_impR 1#6) ≠ hw6 1#6 := by decide

end GateLatticeEngine
