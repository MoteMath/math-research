/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BitLevelKindIc3Invariants

/-!
# Verified Solutions (`bit-level-kind-ic3-invariants`)
-/

namespace BitLevelKindIc3InvariantsChallenge

open KIndIC3

theorem checkOblig_sound {r m : Nat} (sys : BVSystem r m) (steps : Nat)
    (hyps : Fin (steps + 1) → BVPred r 0) (conc : BVPred r 0) (cert : NatSet)
    (hchk : checkOblig sys steps hyps conc cert = true) :
    ∀ (w : Nat), w ≥ 1 →
    ∀ (s0 : Fin r → BitVec w) (us : Nat → Fin m → BitVec w),
      (∀ j : Fin (steps + 1), evalPred (runTrace sys s0 us j.val) Fin.elim0 (hyps j) = true) →
      evalPred (runTrace sys s0 us steps) Fin.elim0 conc = true :=
  KIndIC3.checkOblig_sound sys steps hyps conc cert hchk

theorem checkKIndIC3_sound {r m : Nat} (sys : BVSystem r m) (prop : BVPred r 0)
    (cert : KIndIC3Cert r)
    (hchk : checkKIndIC3 sys prop cert = true) :
    Safe sys prop :=
  KIndIC3.checkKIndIC3_sound sys prop cert hchk

theorem thm1_wrapSafeGray_safety :
    ∀ (w : Nat), w ≥ 1 → ∀ (t : Nat),
      let (x, g) := grayTrace w t
      (x = 0#w → g = 0#w) ∧ g.msb = x.msb :=
  KIndIC3.thm1_wrapSafeGray_safety 

theorem thm2_carrySave_safety :
    ∀ (w : Nat), w ≥ 1 → ∀ (u : Nat → BitVec w) (t : Nat),
      let (S, C, A) := csaTrace u t
      S.getLsbD 0 = A.getLsbD 0 ∧ (S + C).msb = A.msb :=
  KIndIC3.thm2_carrySave_safety 

theorem thm3_carryDefectPipeline_zero :
    ∀ (w : Nat), w ≥ 1 → ∀ (t : Nat),
      (defectPipeTrace w t).2.2 = 0#w :=
  KIndIC3.thm3_carryDefectPipeline_zero 

theorem thm4_hybridSparseAdder_msb :
    ∀ (w : Nat), w ≥ 1 → ∀ (u : Nat → BitVec w) (t : Nat),
      (hybridTrace u t).2.1.msb = (hybridTrace u t).2.2.msb :=
  KIndIC3.thm4_hybridSparseAdder_msb 

theorem thm5_avgFilter_oneULP :
    ∀ (w : Nat), w ≥ 1 → ∀ (u : Nat → BitVec w) (t : Nat),
      let (L, M) := avgFilterTrace u t
      L ≤ M ∧ M - L ≤ 1#w :=
  KIndIC3.thm5_avgFilter_oneULP 

end BitLevelKindIc3InvariantsChallenge
