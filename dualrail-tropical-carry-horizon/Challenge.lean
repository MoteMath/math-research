/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DualrailTropicalCarryHorizon.Defs

/-!
# Trusted Challenge Statements (`dualrail-tropical-carry-horizon`)

Statements of the all-width potential identity for dual-rail carry-free addition, relational bisimulation modulo 2^w, exact integer semantics, associativity modulo 2^w, horizon-2 locality, compiler equivalence, the exact horizon lower bound, and the absence of any horizon certificate for ripple carry.
-/

namespace DualrailTropicalCarryHorizonChallenge

open DualRailCompiler DualRailCompiler.DRTransducer in
/-- Theorem 1 (Potential lift): a finite potential certificate yields the exact prefix identity at every width. -/
theorem potential_lift_all_widths (T : DRTransducer α m) (target : α → Int) (φ : Fin m → Int)
    (hcert : T.ValidPotential target φ) (q : Fin m) (u : Nat → α) (w : Nat) :
    prefixVal w (T.runOut q u) + ((2 ^ w : Nat) : Int) * φ (T.runState q u w) =
      prefixSum target w u + φ q := by
  sorry

open DualRailCompiler DualRailCompiler.DRTransducer in
/-- Theorem 2 (Relational bisimulation): a finite relational invariant forces equal prefix values modulo 2^w at every width. -/
theorem relational_bisim_mod_eq (T₁ : DRTransducer α m₁) (T₂ : DRTransducer α m₂)
    (ψ : Fin m₁ → Fin m₂ → Int) (hcert : ValidRelInvariant T₁ T₂ ψ)
    (hinit : ψ T₁.init T₂.init = 0) (u : Nat → α) (w : Nat) :
    (prefixVal w (T₁.runOut T₁.init u)) % ((2 ^ w : Nat) : Int) =
    (prefixVal w (T₂.runOut T₂.init u)) % ((2 ^ w : Nat) : Int) := by
  sorry

open DualRailCompiler in
/-- Theorem 3 (Exact integer semantics): dual-rail addition plus a boundary potential equals the sum of the operands at every width. -/
theorem avizAdd_exact_int (w : Nat) (x y : Nat → DR) :
    prefixVal w (avizAdd x y) +
      ((2 ^ w : Nat) : Int) * avizPhi (avizTransducer.runState avizTransducer.init (fun i => (x i, y i)) w) =
    prefixVal w x + prefixVal w y := by
  sorry

open DualRailCompiler in
/-- Theorem 4 (Associativity modulo 2^w): dual-rail addition is associative modulo 2^w at every width on arbitrary streams. -/
theorem avizAdd_assoc_mod (w : Nat) (x y z : Nat → DR) :
    (prefixVal w (avizAdd (avizAdd x y) z)) % ((2 ^ w : Nat) : Int) =
    (prefixVal w (avizAdd x (avizAdd y z))) % ((2 ^ w : Nat) : Int) := by
  sorry

open DualRailCompiler in
/-- Theorem 5 (Horizon 2): every output digit depends only on the two preceding input positions and the current one. -/
theorem avizAdd_horizon2 (x₁ y₁ x₂ y₂ : Nat → DR) (i : Nat)
    (hwin : ∀ j, i - 2 ≤ j → j ≤ i → x₁ j = x₂ j ∧ y₁ j = y₂ j) :
    avizAdd x₁ y₁ i = avizAdd x₂ y₂ i := by
  sorry

open DualRailCompiler in
/-- Theorem 6 (Compiler equivalence): right-chain compilation of any dual-rail expression is exact modulo 2^w at every width. -/
theorem compileRight_equiv_all_widths (w : Nat) (env : Fin n → Nat → DR) (e : DRExpr n) :
    (prefixVal w (evalRightChain env (flattenAtoms false e))) % ((2 ^ w : Nat) : Int) =
    (prefixVal w (evalDR env e)) % ((2 ^ w : Nat) : Int) := by
  sorry

open DualRailCompiler in
/-- Theorem 7 (Horizon sharpness): the computed lag bound is attained by an explicit one-bit-different pair of streams. -/
theorem exact_horizon_achieved (outer : List Port) (inner : Port) :
    (∀ j, j ≠ 0 → leafZero j = leafBit0 j) ∧
    evalPortChain (buildWitnessStages outer) inner sideInner leafZero
        ((chainMat outer inner).maxLag) ≠
      evalPortChain (buildWitnessStages outer) inner sideInner leafBit0
        ((chainMat outer inner).maxLag) := by
  sorry

open DualRailCompiler in
/-- Theorem 8 (Ripple carry has no horizon): no finite horizon certificate exists for the ripple-carry transducer. -/
theorem no_horizon_cert_for_ripple (H : Nat) (R : Fin 2 → Fin 2 → Nat) :
    ¬ rippleTransducer.ValidHorizonCert H R := by
  sorry

end DualrailTropicalCarryHorizonChallenge
