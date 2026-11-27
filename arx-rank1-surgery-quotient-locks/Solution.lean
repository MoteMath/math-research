/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArxRank1SurgeryQuotientLocks

/-!
# Verified Solutions (`arx-rank1-surgery-quotient-locks`)
-/

namespace ArxRank1SurgeryQuotientLocksChallenge

open ARXInfiniteEngine

theorem rank1Surgery_spliced_minPeriod {α : Type} [DecidableEq α] {ψ : α → α} {top a : α} {B : Nat}
    (hinj : ∀ u v, ψ u = ψ v → u = v) (htop : ψ top = top) (hne : a ≠ top)
    (hmin : IsMinPeriod ψ a B) :
    IsMinPeriod (fun x => swap a top (ψ x)) a (B + 1) :=
  ARXInfiniteEngine.rank1Surgery_spliced_minPeriod hinj htop hne hmin

theorem rank1Surgery_global_order {α : Type} [DecidableEq α] {ψ : α → α} {top a : α} {B : Nat}
    (hinj : ∀ u v, ψ u = ψ v → u = v) (htop : ψ top = top) (hne : a ≠ top)
    (hmin : IsMinPeriod ψ a B) (hglob : ∀ x, iter ψ B x = x) :
    ∀ x, iter (fun y => swap a top (ψ y)) (B * (B + 1)) x = x :=
  ARXInfiniteEngine.rank1Surgery_global_order hinj htop hne hmin hglob

theorem arx_fermat_mersenne_odd {w : Nat} (hw : 2 ≤ w) (r : Nat)
    (hq_odd : (w / Nat.gcd w r) % 2 = 1) :
    let q := w / Nat.gcd w r
    (∀ x : BitVec w, iter (arxFermatMap w r) (2 * q) x = x) ∧
    IsMinPeriod (arxFermatMap w r) (0#w) (2 * q) :=
  ARXInfiniteEngine.arx_fermat_mersenne_odd hw r hq_odd

theorem arx_fermat_mersenne_even {w : Nat} (hw : 3 ≤ w) (r : Nat)
    (hq_even : (w / Nat.gcd w r) % 2 = 0) :
    let g := Nat.gcd w r
    let q := w / g
    (∀ x : BitVec w, iter (arxFermatMap w r) (q * (2 ^ g + 1)) x = x) ∧
    IsMinPeriod (arxFermatMap w r) (0#w) (q * (2 ^ g + 1)) :=
  ARXInfiniteEngine.arx_fermat_mersenne_even hw r hq_even

theorem arx_fermat_number_order {k j : Nat} (hk : 2 ≤ k) (hjk : j < k) :
    let w := 2 ^ k
    let r := 2 ^ j
    let L := 2 ^ (k - j) * (2 ^ (2 ^ j) + 1)
    (∀ x : BitVec w, iter (arxFermatMap w r) L x = x) ∧
    IsMinPeriod (arxFermatMap w r) (0#w) L :=
  ARXInfiniteEngine.arx_fermat_number_order hk hjk

theorem arx_rank1_surgery_theorem {w : Nat} (hw : 2 ≤ w) (r : Nat) :
    let g := Nat.gcd w r
    let q := w / g
    let B := q * (2 ^ g - 1)
    IsMinPeriod (arxAddRot w r) (0#w) (B + 1) ∧
    (∀ x : BitVec w, x ≠ BitVec.allOnes w →
      (∀ j, j < B → x ≠ iter (mersenneAddRotShadow w r) j (0#w)) →
      iter (arxAddRot w r) B x = x) ∧
    (∀ x : BitVec w, iter (arxAddRot w r) (B * (B + 1)) x = x) :=
  ARXInfiniteEngine.arx_rank1_surgery_theorem hw r

theorem arx_rank1_surgery_nontrivial_xor {w : Nat} (hw : 2 ≤ w) (r : Nat) :
    let g := Nat.gcd w r
    let q := w / g
    let B := q * (2 ^ g - 1)
    let G := arxRound w r (1#w ^^^ msb w) (msb w)
    IsMinPeriod G (msb w) (B + 1) ∧
    (∀ x : BitVec w, iter G (B * (B + 1)) x = x) :=
  ARXInfiniteEngine.arx_rank1_surgery_nontrivial_xor hw r

theorem speck_period3_quotient_lock {h : Nat} (hh : 1 ≤ h)
    (k1 k2 k3 : BitVec (2 * h))
    (hk1 : ValidSpeckKey h k1 ∧ k1.getLsbD (h - 1) = false)
    (hk2 : ValidSpeckKey h k2 ∧ k2.getLsbD (h - 1) = false)
    (hk3 : ValidSpeckKey h k3 ∧ k3.getLsbD (h - 1) = false)
    (p : BitVec (2 * h) × BitVec (2 * h)) (hp : InSpeckSubspace h p) :
    InSpeckSubspace h (iterKeys (speckRound (2 * h) h h) [k1, k2, k3] p) ∧
    speckQuotient h (iterKeys (speckRound (2 * h) h h) [k1, k2, k3] p) = speckQuotient h p :=
  ARXInfiniteEngine.speck_period3_quotient_lock hh k1 k2 k3 hk1 hk2 hk3 p hp

end ArxRank1SurgeryQuotientLocksChallenge
