/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArxRank1SurgeryQuotientLocks.Defs

/-!
# Trusted Challenge Statements (`arx-rank1-surgery-quotient-locks`)

Infinite-width ARX period-lock theorems via Mersenne-ring lifts, rank-1 carry-defect cycle surgery, conjugacy transport to nontrivial Add+Rotate+XOR maps, and round-varying period-3 quotient locks on Speck half-width carry-barrier subspaces.
-/

namespace ArxRank1SurgeryQuotientLocksChallenge

open ARXInfiniteEngine

/-- Theorem 1 (rank-1 surgery splices fixed point `top` into `a`s `B`-cycle for exact minimal period `B + 1`). -/
theorem rank1Surgery_spliced_minPeriod {α : Type} [DecidableEq α] {ψ : α → α} {top a : α} {B : Nat}
    (hinj : ∀ u v, ψ u = ψ v → u = v) (htop : ψ top = top) (hne : a ≠ top)
    (hmin : IsMinPeriod ψ a B) :
    IsMinPeriod (fun x => swap a top (ψ x)) a (B + 1) := by
  sorry

/-- Theorem 2 (global order dividing `B * (B + 1)` under rank-1 surgery). -/
theorem rank1Surgery_global_order {α : Type} [DecidableEq α] {ψ : α → α} {top a : α} {B : Nat}
    (hinj : ∀ u v, ψ u = ψ v → u = v) (htop : ψ top = top) (hne : a ≠ top)
    (hmin : IsMinPeriod ψ a B) (hglob : ∀ x, iter ψ B x = x) :
    ∀ x, iter (fun y => swap a top (ψ y)) (B * (B + 1)) x = x := by
  sorry

/-- Theorem 3 (odd quotient `q = w / gcd(w, r)` locks `arxFermatMap w r` to exact order `2 * q`). -/
theorem arx_fermat_mersenne_odd {w : Nat} (hw : 2 ≤ w) (r : Nat)
    (hq_odd : (w / Nat.gcd w r) % 2 = 1) :
    let q := w / Nat.gcd w r
    (∀ x : BitVec w, iter (arxFermatMap w r) (2 * q) x = x) ∧
    IsMinPeriod (arxFermatMap w r) (0#w) (2 * q) := by
  sorry

/-- Theorem 4 (even quotient, `w ≥ 3`, locks `arxFermatMap w r` to exact order `q * (2^g + 1)`). -/
theorem arx_fermat_mersenne_even {w : Nat} (hw : 3 ≤ w) (r : Nat)
    (hq_even : (w / Nat.gcd w r) % 2 = 0) :
    let g := Nat.gcd w r
    let q := w / g
    (∀ x : BitVec w, iter (arxFermatMap w r) (q * (2 ^ g + 1)) x = x) ∧
    IsMinPeriod (arxFermatMap w r) (0#w) (q * (2 ^ g + 1)) := by
  sorry

/-- Theorem 5 (Fermat-number permutation order `2^(k - j) * F_j` on power-of-two words `w = 2^k, r = 2^j`). -/
theorem arx_fermat_number_order {k j : Nat} (hk : 2 ≤ k) (hjk : j < k) :
    let w := 2 ^ k
    let r := 2 ^ j
    let L := 2 ^ (k - j) * (2 ^ (2 ^ j) + 1)
    (∀ x : BitVec w, iter (arxFermatMap w r) L x = x) ∧
    IsMinPeriod (arxFermatMap w r) (0#w) L := by
  sorry

/-- Theorem 6 (exact infinite-width rank-1 carry-defect cycle surgery on `(x + 1).rotateLeft r`). -/
theorem arx_rank1_surgery_theorem {w : Nat} (hw : 2 ≤ w) (r : Nat) :
    let g := Nat.gcd w r
    let q := w / g
    let B := q * (2 ^ g - 1)
    IsMinPeriod (arxAddRot w r) (0#w) (B + 1) ∧
    (∀ x : BitVec w, x ≠ BitVec.allOnes w →
      (∀ j, j < B → x ≠ iter (mersenneAddRotShadow w r) j (0#w)) →
      iter (arxAddRot w r) B x = x) ∧
    (∀ x : BitVec w, iter (arxAddRot w r) (B * (B + 1)) x = x) := by
  sorry

/-- Theorem 7 (conjugacy transport of rank-1 surgery to genuine Add+Rotate+XOR). -/
theorem arx_rank1_surgery_nontrivial_xor {w : Nat} (hw : 2 ≤ w) (r : Nat) :
    let g := Nat.gcd w r
    let q := w / g
    let B := q * (2 ^ g - 1)
    let G := arxRound w r (1#w ^^^ msb w) (msb w)
    IsMinPeriod G (msb w) (B + 1) ∧
    (∀ x : BitVec w, iter G (B * (B + 1)) x = x) := by
  sorry

/-- Theorem 8 (round-varying period-3 quotient lock on Speck half-width carry-barrier subspace `V_h`). -/
theorem speck_period3_quotient_lock {h : Nat} (hh : 1 ≤ h)
    (k1 k2 k3 : BitVec (2 * h))
    (hk1 : ValidSpeckKey h k1 ∧ k1.getLsbD (h - 1) = false)
    (hk2 : ValidSpeckKey h k2 ∧ k2.getLsbD (h - 1) = false)
    (hk3 : ValidSpeckKey h k3 ∧ k3.getLsbD (h - 1) = false)
    (p : BitVec (2 * h) × BitVec (2 * h)) (hp : InSpeckSubspace h p) :
    InSpeckSubspace h (iterKeys (speckRound (2 * h) h h) [k1, k2, k3] p) ∧
    speckQuotient h (iterKeys (speckRound (2 * h) h h) [k1, k2, k3] p) = speckQuotient h p := by
  sorry

end ArxRank1SurgeryQuotientLocksChallenge
