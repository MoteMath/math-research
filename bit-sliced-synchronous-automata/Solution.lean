/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BitSlicedSynchronousAutomata

/-!
# Verified Solutions (`bit-sliced-synchronous-automata`)
-/

namespace BitSlicedSynchronousAutomataChallenge

open BitSync

theorem checkCert_sound {k : Nat} {S : Type} [BEq S] [LawfulBEq S]
    (M : SyncAutomaton k S) (cert : AutomatonCert S)
    (hcert : checkCert M cert = true) :
    ∀ (w : Nat) (stream : Fin w → Fin (2 ^ k)), M.accept (M.runN w stream) = true :=
  BitSync.checkCert_sound M cert hcert

theorem bvProp_cert_sound {k : Nat} (φ : BVProp k)
    (cert : AutomatonCert φ.State)
    (hcert : checkCert (compileToSync φ) cert = true) :
    ∀ (w : Nat) (env : Fin k → BitVec w), φ.eval w env = true :=
  BitSync.bvProp_cert_sound φ cert hcert

theorem thm_signed_quarter_sum_net_overflow_iff :
    ∀ (w : Nat) (x y z : BitVec w), 2 ≤ w →
      (signedQuarterSum x y z = (x + y + z).sshiftRight 2 ↔
        signedAddOverflow x y = signedAddOverflow (x + y) z) :=
  BitSync.thm_signed_quarter_sum_net_overflow_iff 

theorem thm_unsigned_quarter_sum_no_overflow_iff :
    ∀ (w : Nat) (x y z : BitVec w), 2 ≤ w →
      (unsignedQuarterSum x y z = (x + y + z) >>> 2 ↔
        (¬(x + y < x) ∧ ¬(x + y + z < x + y))) :=
  BitSync.thm_unsigned_quarter_sum_no_overflow_iff 

theorem thm_signed_eq_unsigned_quarter_sum_iff :
    ∀ (w : Nat) (x y z : BitVec w),
      signedQuarterSum x y z = unsignedQuarterSum x y z ↔
        (x.msb = false ∧ y.msb = false ∧ z.msb = false) :=
  BitSync.thm_signed_eq_unsigned_quarter_sum_iff 

theorem thm_signed_quarter_sum_mod_reconstruction :
    ∀ (w : Nat) (x y z : BitVec w),
      (signedQuarterSum x y z <<< 2) + ((x + y + z) &&& (1#w ||| (1#w <<< 1))) = x + y + z :=
  BitSync.thm_signed_quarter_sum_mod_reconstruction 

theorem thm_nested_avg_vs_quarter_sum_sandwich :
    ∀ (w : Nat) (x y z : BitVec w),
      (z >>> 2) ≤ unsignedAvg (unsignedAvg x y) z - unsignedQuarterSum x y z ∧
      unsignedAvg (unsignedAvg x y) z - unsignedQuarterSum x y z ≤ (z >>> 2) + 1#w :=
  BitSync.thm_nested_avg_vs_quarter_sum_sandwich 

theorem thm_gray_triple_zeckendorf_iff :
    ∀ (w : Nat) (x : BitVec w),
      grayCode (x + (x <<< 1)) = (x <<< 1) ^^^ (x >>> 1) ↔
        ((x &&& (x <<< 1)) = 0#w ∧ x.msb = false) :=
  BitSync.thm_gray_triple_zeckendorf_iff 

end BitSlicedSynchronousAutomataChallenge
