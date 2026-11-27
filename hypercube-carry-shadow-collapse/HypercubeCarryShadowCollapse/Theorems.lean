/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HypercubeCarryShadowCollapse.Defs

namespace HypercubeCarryShadowCollapse


private theorem xor_mod_two_pow (a b w : Nat) :
    ((a % 2 ^ w) ^^^ (b % 2 ^ w)) % 2 ^ w = (a ^^^ b) % 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_mod_two_pow,
      Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_xor]
  by_cases hi : i < w <;> simp [hi]

theorem stageBV_toNat {m w : Nat} (r : Fin m) (x : CubeBV m w) (y : Cube m)
    (hxy : ∀ I, (x I).toNat = y I % 2 ^ w) :
    ∀ I, (stageBV r x I).toNat = stage r y I % 2 ^ w := by
  intro I
  cases hIr : I r with
  | false =>
    simp only [stageBV, stage, hIr, ↓reduceIte, BitVec.toNat_add, hxy]
    rw [Nat.add_mod_mod, Nat.mod_add_mod]
  | true =>
    simp only [stageBV, stage, hIr, Bool.true_eq_false, ↓reduceIte, BitVec.toNat_xor, hxy]
    have hlt : (y (setBit r false I) % 2 ^ w ^^^ y (setBit r true I) % 2 ^ w) < 2 ^ w := by
      have := (x (setBit r false I) ^^^ x (setBit r true I)).isLt
      simpa only [BitVec.toNat_xor, hxy] using this
    rw [← Nat.mod_eq_of_lt hlt, xor_mod_two_pow]

theorem QBV_toNat {m w : Nat} (x : CubeBV m w) (y : Cube m)
    (hxy : ∀ I, (x I).toNat = y I % 2 ^ w) :
    ∀ I, (QBV m w x I).toNat = Q m y I % 2 ^ w := by
  have haxes : ∀ (l : List (Fin m)) (xb : CubeBV m w) (yn : Cube m),
      (∀ I, (xb I).toNat = yn I % 2 ^ w) →
      ∀ I, (applyAxesBV l xb I).toNat = applyAxes l yn I % 2 ^ w := by
    intro l
    induction l with
    | nil => intro xb yn h; exact h
    | cons r rest ih =>
      intro xb yn h
      exact stageBV_toNat r _ _ (stageBV_toNat r _ _ (ih xb yn h))
  exact haxes (List.finRange m).reverse x y hxy

theorem iter_QBV_toNat (m w : Nat) (k : Nat) (x : CubeBV m w) :
    ∀ I, (iter k (QBV m w) x I).toNat = iter k (Q m) (fun J => (x J).toNat) I % 2 ^ w := by
  induction k with
  | zero =>
    intro I
    simp only [iter]
    exact (Nat.mod_eq_of_lt (x I).isLt).symm
  | succ k ih =>
    intro I
    exact QBV_toNat _ _ ih I

/-- MAIN INFINITE-FAMILY THEOREM 3 (Universal BitVec w Nilpotency — ∀ m ≥ 1, ∀ w ≥ 0):
    On w-bit machine words (BitVec w)^{2^m}, Q_m is universally nilpotent:
      whenever m · k ≥ w,   Q_m^{k + 2}(x) = 0 identically! -/
theorem Q_bitvec_nilpotent (m w k : Nat) (hm : 1 ≤ m) (hmk : w ≤ m * k) (x : CubeBV m w) :
    iter (k + 2) (QBV m w) x = fun _ => BitVec.ofNat w 0 := by
  funext I
  apply BitVec.eq_of_toNat_eq
  rw [iter_QBV_toNat, Q_collapse_pow m hm _ k]
  simp only [scaleCube, BitVec.toNat_ofNat, Nat.zero_mod]
  have hdvd : 2 ^ w ∣ 2 ^ (m * k) := Nat.pow_dvd_pow 2 hmk
  rcases hdvd with ⟨q, hq⟩
  rw [hq, Nat.mul_assoc]
  exact Nat.mul_mod_right (2 ^ w) _

/-! ============================================================================
    SECTION 9: KERNEL-CHECKED NON-VACUITY, MUTATION TESTS & SHARPNESS WITNESSES
    ============================================================================ -/

-- 9.1 Non-Vacuity Witnesses (proving every conditional hypothesis is genuinely inhabited!)

instance (a b : Nat) : Decidable (bsub a b) :=
  inferInstanceAs (Decidable (bdiff a b = 0))

/-- Non-vacuity witness for `isCS` (0 < 6 < 7, non-trivial carry-shadow pair). -/
theorem nonvac_isCS : isCS 7 6 ∧ 0 < 6 ∧ 6 < 7 := by
  refine ⟨⟨by decide, by decide⟩, by decide, by decide⟩

/-- Non-vacuity witness for 4-operand `carryMask_dominated_absorption` with C(a, d) > 0. -/
theorem nonvac_dominated_absorption :
    bsub 5 7 ∧ bsub 3 7 ∧ bsub 1 5 ∧ bsub 1 3 ∧ carryMask 7 1 = 14 ∧ carryMask (carryMask 7 5) (carryMask 3 1) = 28 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Non-vacuity witness for `DomCube 2`: Q_2 on (3, 5, 7, 11) produces a non-trivial dominated 4-cube. -/
def cube2 (a b c d : Nat) : Cube 2 := fun I =>
  match I ⟨0, by decide⟩, I ⟨1, by decide⟩ with
  | false, false => a
  | true,  false => b
  | false, true  => c
  | true,  true  => d

theorem nonvac_domCube2 :
    DomCube 2 (Q 2 (cube2 3 5 7 11)) ∧
    Q 2 (Q 2 (cube2 3 5 7 11)) (zeroVertex 2) = 240 := by
  refine ⟨Q_dom 2 _, by decide⟩

-- 9.2 Negative / Hostile Mutation Tests on the Bisimulation Certificate Checker!

/-- Mutation Test 1: Corrupted bitmask (clearing bit 0 = initial state) MUST be rejected! -/
theorem checker_rejects_corrupted_mask :
    checkGuardedBisimWitness (compile domAbsGuard) (compile domAbsLHS) (compile domAbsRHS) (domAbsCert ^^^ 1) = false := by
  decide

/-- Mutation Test 2: Dropping ALL dominance guards causes the checker to REJECT the absorption law! -/
theorem checker_rejects_false_ungrouped_absorption :
    checkGuardedBisimWitness (zeroTransducer 4) (compile domAbsLHS) (compile domAbsRHS) domAbsCert = false := by
  decide

/-- Mutation Test 3: Checker REJECTS false identity `x + y = x ^ y`. -/
theorem checker_rejects_add_eq_xor :
    checkGuardedBisim (zeroTransducer 2) (compile (.badd x0 x1)) (compile (.bxor x0 x1)) = false := by
  decide

-- 9.3 Sharpness Counterexamples (proving EVERY hypothesis and threshold is tight!)

/-- Sharpness 1 (m = 1, k = 1 threshold): Φ³(1, 3) = (12, 0) ≠ (8, 4) = 2 · Φ¹(1, 3). -/
theorem sharp_m1_k1_fails :
    iter 3 phi (1, 3) ≠ (2 * (iter 1 phi (1, 3)).1, 2 * (iter 1 phi (1, 3)).2) := by
  decide

/-- Sharpness 2 (m = 2, k = 1 threshold): Q_2²(0, 2, 1, 1) ≠ 4 · Q_2¹(0, 2, 1, 1), proving k₀ = 2 is exact! -/
theorem sharp_m2_k1_fails :
    Q 2 (Q 2 (cube2 0 2 1 1)) (fun i => i == ⟨0, by decide⟩) ≠
    4 * Q 2 (cube2 0 2 1 1) (fun i => i == ⟨0, by decide⟩) := by
  decide

/-- Sharpness 3 (Non-commutativity outside DomCube): S_1² ∘ S_0² ≠ S_0² ∘ S_1² on (0, 1, 1, 0)! -/
theorem sharp_noncomm_on_nat :
    stageSq ⟨1, by decide⟩ (stageSq ⟨0, by decide⟩ (cube2 0 1 1 0)) (fun i => i == ⟨0, by decide⟩) ≠
    stageSq ⟨0, by decide⟩ (stageSq ⟨1, by decide⟩ (cube2 0 1 1 0)) (fun i => i == ⟨0, by decide⟩) := by
  decide

/-- Sharpness 4 (Axis-interleaving necessity): S_1⁴ ∘ S_0⁴ (2 consecutive passes per axis, NOT interleaved)
    FAILS to reach the 4-scaling invariant manifold on (0, 2, 1, 1)! -/
theorem sharp_consecutive_passes_fail :
    let y := stageSq ⟨1, by decide⟩ (stageSq ⟨1, by decide⟩
               (stageSq ⟨0, by decide⟩ (stageSq ⟨0, by decide⟩ (cube2 0 2 1 1))))
    Q 2 y (fun i => i == ⟨0, by decide⟩) ≠ 4 * y (fun i => i == ⟨0, by decide⟩) := by
  decide

/-- Sharpness 5a–5d: Dropping ANY SINGLE ONE of the 4 dominance hypotheses breaks Dominated Carry-Absorption! -/
theorem sharp_absorption_drop_ba :
    bsub 1 1 ∧ bsub 1 3 ∧ bsub 1 1 ∧ carryMask (carryMask 1 3) (carryMask 1 1) ≠ 2 * carryMask 1 1 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem sharp_absorption_drop_ca :
    bsub 1 1 ∧ bsub 1 1 ∧ bsub 1 3 ∧ carryMask (carryMask 1 1) (carryMask 3 1) ≠ 2 * carryMask 1 1 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem sharp_absorption_drop_db :
    bsub 0 1 ∧ bsub 1 1 ∧ bsub 1 1 ∧ carryMask (carryMask 1 0) (carryMask 1 1) ≠ 2 * carryMask 1 1 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem sharp_absorption_drop_dc :
    bsub 1 1 ∧ bsub 0 1 ∧ bsub 1 1 ∧ carryMask (carryMask 1 1) (carryMask 0 1) ≠ 2 * carryMask 1 1 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Sharpness 6 (Sandwich Theorem strictly sharper than subset):
    C(3947, 65146) = 2 * 65146 EVEN THOUGH 65146 ⊈ 3947! -/
theorem sharp_sandwich_strictly_stronger_than_subset :
    carryMask 3947 65146 = 2 * 65146 ∧ bdiff 65146 3947 ≠ 0 := by
  refine ⟨by decide, by decide⟩

/-- Sharpness 7 (XOR necessity in Butterfly): Replacing `^` by `|` destroys Φ⁴ = 2 · Φ²! -/
def phiOr (p : Nat × Nat) : Nat × Nat := (p.1 + p.2, p.1 ||| p.2)

theorem sharp_or_butterfly_fails :
    iter 4 phiOr (1, 3) ≠ (2 * (iter 2 phiOr (1, 3)).1, 2 * (iter 2 phiOr (1, 3)).2) := by
  decide

end HypercubeCarryShadowCollapse
