import ZeckendorfBinaryCarryBridge

namespace ZeckendorfBinaryCarryBridgeChallenge

open CarryBridge

theorem popcount_add_carry (a b : Nat) :
    popcount a + popcount b = popcount (a + b) + popcount (carryInMask a b) :=
  _root_.CarryBridge.popcount_add_carry a b

theorem master_carry_bridge_iff {c : RecCert} (hv : c.isValid = true) {x p d : Nat}
    (hsp : isRSpaced c.r d) :
    TransducerAccepts c x p d ↔
      (p = x + c.mS * d ∧ carryInMask x (c.mS * d) = (2 ^ (c.r + 1) - 2) * d) :=
  _root_.CarryBridge.master_carry_bridge_iff hv hsp

theorem not_diff_basis_refutation {c : RecCert} (hv : c.isValid = true) (hndb : c.isDiffBasis = false) :
    ∃ ks x p, SRewriteDeriv c ks x p ∧
      let d := sumPow2 ks
      ¬ isRSpaced c.r d ∧
      carryInMask x (c.mS * d) ≠ (2 ^ (c.r + 1) - 2) * d :=
  _root_.CarryBridge.not_diff_basis_refutation hv hndb

theorem rbonacci_uniqueness {r : Nat} (hr : r ≥ 2) {p₁ p₂ : Nat}
    (h1 : noROnes r p₁) (h2 : noROnes r p₂)
    (heval : evalRecNat (rBonacciWeight r) p₁ = evalRecNat (rBonacciWeight r) p₂) :
    p₁ = p₂ :=
  _root_.CarryBridge.rbonacci_uniqueness hr h1 h2 heval

theorem rbonacci_master_invariants {r : Nat} (hr : r ≥ 2) (x : Nat) :
    ∃ p d,
      noROnes r p ∧
      evalRecNat (rBonacciWeight r) p = evalRecNat (rBonacciWeight r) x ∧
      p = x + d ∧
      isRSpaced r d ∧
      carryInMask x d = (2 ^ (r + 1) - 2) * d ∧
      p ^^^ x = clmul (2 ^ (r + 1) - 1) d ∧
      popcount x = popcount p + (r - 1) * popcount d ∧
      popcount (carryInMask x d) = r * popcount d ∧
      (∀ p' d', noROnes r p' → evalRecNat (rBonacciWeight r) p' = evalRecNat (rBonacciWeight r) x →
        p' = x + d' → p' = p ∧ d' = d) :=
  _root_.CarryBridge.rbonacci_master_invariants hr x

theorem sparse_r6_diff_basis_infinite_law {ks : List Nat} {x p : Nat}
    (hd : SRewriteDeriv certDB6A ks x p) :
    let d := sumPow2 ks
    isRSpaced 6 d ∧
    p = x + 21 * d ∧
    carryInMask x (21 * d) = 126 * d ∧
    p ^^^ x = clmul 107 d ∧
    popcount x = popcount p + 3 * popcount d ∧
    popcount (carryInMask x (21 * d)) = 6 * popcount d :=
  _root_.CarryBridge.sparse_r6_diff_basis_infinite_law hd

theorem witness_nonvacuity_sparse_r6 :
    SRewriteDeriv certDB6A [6, 0] 2795 4160 :=
  _root_.CarryBridge.witness_nonvacuity_sparse_r6

theorem sharpness_non_confluence_still_obeys_carry_bridge :
    certDB4A.isDiffBasis = true ∧
    SRewriteDeriv certDB4A [2] 47 67 ∧
    SRewriteDeriv certDB4A [0] 47 52 ∧
    (67 : Nat) ≠ 52 ∧
    carryInMask 47 (certDB4A.mS * sumPow2 [2]) = 30 * sumPow2 [2] ∧
    carryInMask 47 (certDB4A.mS * sumPow2 [0]) = 30 * sumPow2 [0] :=
  _root_.CarryBridge.sharpness_non_confluence_still_obeys_carry_bridge

end ZeckendorfBinaryCarryBridgeChallenge
