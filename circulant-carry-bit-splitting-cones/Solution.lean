import CirculantCarryBitSplittingCones

namespace CirculantCarryBitSplittingConesChallenge

open Adic16

theorem hermitian_row0_telescope_symm {d m : Nat} (hd : 0 < d) (hm : 0 < m)
    (H : GRMat d m) (v : GRVec d m)
    (hH : IsRevHermitian hm H)
    (hv0 : v ⟨0, hd⟩ = grUnit 0)
    (hrow0 : ∀ j : Fin d, H ⟨0, hd⟩ j =
      grAdd (if j = ⟨0, hd⟩ then grUnit 0 else grZero m) (grRev hm (v j))) :
    (∀ k : Nat,
      grMatVec hm (grMatPow hm H (k + 1)) v ⟨0, hd⟩ =
      grAdd (grMatVec hm (grMatPow hm H k) v ⟨0, hd⟩) (grQuadForm hm v (grMatPow hm H k))) ∧
    (∀ k : Nat,
      grRev hm (grMatVec hm (grMatPow hm H k) v ⟨0, hd⟩) =
      grMatVec hm (grMatPow hm H k) v ⟨0, hd⟩) :=
  _root_.Adic16.hermitian_row0_telescope_symm hd hm H v hH hv0 hrow0

theorem mersenne_mod3_recurrence (k : Nat) :
    mersenneMod3Excess (k + 3) =
    4 * mersenneMod3Excess (k + 2) + 4 * mersenneMod3Excess (k + 1) - mersenneMod3Excess k :=
  _root_.Adic16.mersenne_mod3_recurrence k

theorem mersenne_mod6_dominance_breaks_at_2_pow_72 :
    (countMod (2 ^ (6 * 12)) 6 0 (fun n => popcount (63 * n)) : Int) -
    (countMod (2 ^ (6 * 12)) 6 2 (fun n => popcount (63 * n)) : Int) =
    -4543260596431345 ∧
    countMod (2 ^ (6 * 12)) 6 0 (fun n => popcount (63 * n)) <
    countMod (2 ^ (6 * 12)) 6 2 (fun n => popcount (63 * n)) :=
  _root_.Adic16.mersenne_mod6_dominance_breaks_at_2_pow_72

theorem mersenne_palindromy_naive_involutions_fail :
    popcount (7 * 11) % 3 = 1 ∧ popcount (7 * (64 - 11)) % 3 = 0 ∧
    popcount (7 * 13) % 3 = 2 ∧ popcount (7 * (63 - 13)) % 3 = 0 :=
  _root_.Adic16.mersenne_palindromy_naive_involutions_fail

theorem or_mul5_strict_evil_dominance :
    ∀ N : Nat, 1 ≤ N →
      countMod N 2 1 (fun n => popcount (n ||| (5 * n))) <
      countMod N 2 0 (fun n => popcount (n ||| (5 * n))) :=
  _root_.Adic16.or_mul5_strict_evil_dominance

theorem mul3_newman_benchmark :
    ∀ N : Nat, 1 ≤ N →
      countMod N 2 1 (fun n => popcount (3 * n)) <
      countMod N 2 0 (fun n => popcount (3 * n)) :=
  _root_.Adic16.mul3_newman_benchmark

theorem hostile_mutation_U0_rejected :
    checkConeCert (orMulTransducer 5 (by decide)) badCertOrMul5_U0 = false :=
  _root_.Adic16.hostile_mutation_U0_rejected

theorem engineII_three_way_sharpness :
    countMod 3 2 0 (fun n => popcount (n ^^^ (3 * n))) < countMod 3 2 1 (fun n => popcount (n ^^^ (3 * n))) ∧
    countMod 3 2 0 (fun n => popcount (n &&& (3 * n))) < countMod 3 2 1 (fun n => popcount (n &&& (3 * n))) ∧
    countMod 3 2 0 (fun n => popcount (n ^^^ (5 * n))) < countMod 3 2 1 (fun n => popcount (n ^^^ (5 * n))) ∧
    countMod 3 2 0 (fun n => popcount (n &&& (5 * n))) < countMod 3 2 1 (fun n => popcount (n &&& (5 * n))) ∧
    countMod 3 2 0 (fun n => popcount (n ||| (7 * n))) < countMod 3 2 1 (fun n => popcount (n ||| (7 * n))) :=
  _root_.Adic16.engineII_three_way_sharpness

end CirculantCarryBitSplittingConesChallenge
