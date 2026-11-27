/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CarryPresburgerSkolemCompiler

/-!
# Verified Solutions (`carry-presburger-skolem-compiler`)
-/

namespace CarryPresburgerSkolemCompilerChallenge

open CPRTE

theorem cert_sound (cert : Cert) (hc : checkCert cert = true) :
    ∀ x : List Nat, x.length = cert.d →
      ∃ y : List Nat, y.length = cert.e ∧
        evalFormulaBool (cert.entries.getD 0 defaultEntry).formula (x ++ y) = true :=
  CPRTE.cert_sound cert hc

theorem synthesizeY_sound (cert : Cert) (hc : checkCert cert = true)
    (x : List Nat) (hx : x.length = cert.d) :
    (synthesizeY cert x).length = cert.e ∧
      evalFormulaBool (cert.entries.getD 0 defaultEntry).formula (x ++ synthesizeY cert x) = true :=
  CPRTE.synthesizeY_sound cert hc x hx

theorem cert_sound_univ (cert : Cert) (hc : checkCert cert = true) (he : cert.e = 0) :
    ∀ x : List Nat, x.length = cert.d →
      evalFormulaBool (cert.entries.getD 0 defaultEntry).formula x = true :=
  CPRTE.cert_sound_univ cert hc he

theorem carryCount_eq_popcount_defect (a b : Nat) (cin : Bool) :
    carryCount a b cin + popcount (a + b + cin.toNat) =
      popcount a + popcount b + cin.toNat :=
  CPRTE.carryCount_eq_popcount_defect a b cin

theorem ternary_zero_carry_r0 (x : Nat) :
    ∃ y : Nat, x &&& y = 0 ∧ (x + y) % 3 = 0 ∧ 3 * y ≤ 5 * x + 5 :=
  CPRTE.ternary_zero_carry_r0 x

theorem ternary_carry1_r2 (x : Nat) :
    ∃ y : Nat, carryCount x y false ≤ 1 ∧ (x + y) % 3 = 2 ∧ 2 * y ≤ x + 4 :=
  CPRTE.ternary_carry1_r2 x

theorem ternary_carry2_r0 (x : Nat) :
    ∃ y : Nat, carryCount x y false ≤ 2 ∧ (x + y) % 3 = 0 ∧ 4 * y ≤ x + 7 :=
  CPRTE.ternary_carry2_r0 x

theorem mersenne_collatz_rigidity_15 (x : Nat) :
    x &&& (15 * x + 1) = 0 ↔ (15 * x + 1) &&& (15 * x) = 0 :=
  CPRTE.mersenne_collatz_rigidity_15 x

end CarryPresburgerSkolemCompilerChallenge
