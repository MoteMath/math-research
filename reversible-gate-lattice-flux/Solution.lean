/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ReversibleGateLatticeFlux

/-!
# Verified Solutions (`reversible-gate-lattice-flux`)
-/

namespace ReversibleGateLatticeFluxChallenge

open GateLatticeEngine in
/-- Theorem 1 (FluxCert local soundness): a passing finite FluxCert certifies the exact discrete continuity equation on every M-bit window. -/
theorem fluxCert_verify_sound {p r s M shiftOut : Nat}
    (c : FluxCert p r s M shiftOut) (h : c.verify = true) :
    ∀ u : BitVec M,
      c.charge (c.localNext u) - c.charge (sliceBV u shiftOut r) =
        c.flux (sliceBV u p s) - c.flux (sliceBV u 0 s) :=
  GateLatticeEngine.FluxCert.verify_sound c h

open GateLatticeEngine in
/-- Theorem 2 (Open-segment Gauss-Noether continuity): a passing FluxCert lifts to exact charge-flux continuity on every open segment [a, a + n) of every infinite bit-line. -/
theorem fluxCert_open_segment_continuity {p r s M shiftOut : Nat}
    (c : FluxCert p r s M shiftOut)
    (hver : c.verify = true)
    (h1 : shiftOut + r ≤ M) (h2 : p + s ≤ M)
    {T : Line → Line}
    (hrep : LocallyRepresented p r M shiftOut c.localNext T)
    (line : Line) (a : Int) (n : Nat) :
    segmentCharge p r shiftOut c.charge (T line) a n -
      segmentCharge p r shiftOut c.charge line a n =
    c.flux (extractWindow line ((p : Int) * (a + (n : Int))) s) -
      c.flux (extractWindow line ((p : Int) * a) s) :=
  GateLatticeEngine.FluxCert.open_segment_continuity c hver h1 h2 hrep line a n

open GateLatticeEngine in
/-- Theorem 3 (All-width ring conservation): a passing FluxCert proves exact conservation of the ring charge under arbitrary iterations on BitVec (p * n) for every n >= 1. -/
theorem fluxCert_ring_conserved_iter {p r s M shiftOut : Nat}
    (c : FluxCert p r s M shiftOut)
    (hver : c.verify = true)
    (hp_pos : 0 < p) (h1 : shiftOut + r ≤ M) (h2 : p + s ≤ M)
    {T : Line → Line}
    (hrep : LocallyRepresented p r M shiftOut c.localNext T)
    (n : Nat) (hn : 0 < n)
    (hper : ∀ line, IsPeriodic (p * n) line → IsPeriodic (p * n) (T line))
    (v : BitVec (p * n)) (t : Nat) :
    ringCharge p r shiftOut c.charge (iter (ringStep T) t v) =
      ringCharge p r shiftOut c.charge v :=
  GateLatticeEngine.FluxCert.ring_conserved_iter c hver hp_pos h1 h2 hrep n hn hper v t

open GateLatticeEngine in
/-- Theorem 4 (256-gate ideal-mask iff): a 3-variable mask h is ideal for cubic Fredkin-CNOT charge conservation iff its finite FluxCert passes. -/
theorem fredkin_cnot_iff_1_2 (h : Bool → Bool → Bool → Bool) :
    IdealMask h ↔ (certFredCNOT h).verify = true :=
  GateLatticeEngine.fredkin_cnot_iff_1_2 h

open GateLatticeEngine in
/-- Theorem 5 (Fredkin-Toffoli conservation): the cubic non-Hamming charge q_FT is conserved for all iterations on every 4n-bit ring. -/
theorem fredkin_toffoli_conserved_all_widths (n : Nat) (hn : 0 < n) (v : BitVec (4 * n)) (t : Nat) :
    ringCharge 4 4 2 q_FT (iter (ringStep (margolusStep gateFT)) t v) = ringCharge 4 4 2 q_FT v :=
  GateLatticeEngine.fredkin_toffoli_conserved_all_widths n hn v t

open GateLatticeEngine in
/-- Theorem 6 (Fredkin-Toffoli reversibility): the Fredkin-Toffoli Margolus lattice step is an exact bijection on every 4n-bit ring. -/
theorem fredkin_toffoli_reversible_all_widths (n : Nat) (hn : 0 < n) (v : BitVec (4 * n)) :
    ringStep (margolusInvStep gateFT_inv) (ringStep (margolusStep gateFT) v) = v ∧
    ringStep (margolusStep gateFT) (ringStep (margolusInvStep gateFT_inv) v) = v :=
  GateLatticeEngine.fredkin_toffoli_reversible_all_widths n hn v

open GateLatticeEngine in
/-- Theorem 7 (Double-Fredkin three-charge algebra): Hamming weight, dimer charge, rail charge, and asymmetric charge are all conserved at every width. -/
theorem double_fredkin_three_laws_all_widths (n : Nat) (hn : 0 < n) (v : BitVec (4 * n)) (t : Nat) :
    ringCharge 4 4 2 q_HW4   (iter (ringStep (margolusStep gateFF)) t v) = ringCharge 4 4 2 q_HW4   v ∧
    ringCharge 4 4 2 q_dimer (iter (ringStep (margolusStep gateFF)) t v) = ringCharge 4 4 2 q_dimer v ∧
    ringCharge 4 4 2 q_rail  (iter (ringStep (margolusStep gateFF)) t v) = ringCharge 4 4 2 q_rail  v ∧
    ringCharge 4 4 2 certFF_asym.charge (iter (ringStep (margolusStep gateFF)) t v) =
      ringCharge 4 4 2 certFF_asym.charge v :=
  GateLatticeEngine.double_fredkin_three_laws_all_widths n hn v t

open GateLatticeEngine in
/-- Theorem 8 (Chiral SubCNOT domain-wall conservation): the chiral SubCNOT lattice conserves the domain-wall charge q_DW at every even width. -/
theorem subcnot_chiral_domain_wall_conserved_all_widths (n : Nat) (hn : 0 < n) (v : BitVec (2 * n)) (t : Nat) :
    ringCharge 2 4 2 q_DW (iter (ringStep (subCNOTStep f_impL f_impR)) t v) =
      ringCharge 2 4 2 q_DW v :=
  GateLatticeEngine.subcnot_chiral_domain_wall_conserved_all_widths n hn v t

end ReversibleGateLatticeFluxChallenge
