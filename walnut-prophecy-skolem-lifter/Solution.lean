/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WalnutProphecySkolemLifter

/-!
# Verified Solutions (`walnut-prophecy-skolem-lifter`)
-/

namespace WalnutProphecySkolemLifterChallenge

open WalnutLifter

theorem homCert_sound {k : Nat} {M₁ M₂ : DFA k} {cert : HomCert}
    (hc : checkHomCert M₁ M₂ cert = true) :
    (∀ w, (∀ a ∈ w, a < 2 ^ k) → M₂.acceptsWord w = M₁.acceptsWord w) ∧
    (M₁.PadInv → M₂.PadInv) ∧
    (∀ x : Fin k → Nat, M₂.eval x = M₁.eval x) :=
  WalnutLifter.homCert_sound hc

theorem existsCert_sound {k : Nat} {M : DFA (k + 1)} {D : DFA k} {cert : ExistsCert}
    (hMc : M.Closed) (hMp : M.PadInv) (hc : checkExistsCert M D cert = true) :
    D.PadInv ∧
    ∀ x : Fin k → Nat, D.eval x = true ↔ ∃ y : Nat, M.eval (consTuple y x) = true :=
  WalnutLifter.existsCert_sound hMc hMp hc

theorem prophecyCert_sound {k : Nat} {M : DFA (k + 1)} {P_rev : DFA k} {cert : ProphecyCert k}
    (hMp : M.PadInv) (hc : checkProphecyCert M P_rev cert = true) :
    ∀ (x : Fin k → Nat) (L : Nat), (∀ j : Fin k, x j < 2 ^ L) →
      P_rev.acceptsWord (encWord L x).reverse = true →
      ∃ y : Nat, M.eval (consTuple y x) = true :=
  WalnutLifter.prophecyCert_sound hMp hc

theorem universalCert_sound {k : Nat} {M : DFA k} {cert : UniversalCert}
    (hc : checkUniversalCert M cert = true) :
    ∀ x : Fin k → Nat, M.eval x = cert.target :=
  WalnutLifter.universalCert_sound hc

theorem dfaGrayAdd_sound (n : Nat) :
    dfaGrayAdd.eval (tuple1 n) = grayAddParity n :=
  WalnutLifter.dfaGrayAdd_sound n

theorem grayAddParity_exact_square_spectrum :
    ∀ p : Nat,
      (1 ≤ p ∧ ∃ n : Nat, ∀ i < p, grayAddParity (n + i) = grayAddParity (n + i + p)) ↔
      (1 ≤ p ∧ p ≤ 7) :=
  WalnutLifter.grayAddParity_exact_square_spectrum

theorem grayAddParity_exact_cube_spectrum :
    ∀ p : Nat,
      (1 ≤ p ∧ ∃ n : Nat, ∀ i < 2 * p, grayAddParity (n + i) = grayAddParity (n + i + p)) ↔
      p = 1 :=
  WalnutLifter.grayAddParity_exact_cube_spectrum

theorem grayAddParity_fifth_power_free :
    ∀ n p : Nat, 1 ≤ p → ∃ i : Nat, i < 4 * p ∧
      grayAddParity (n + i) ≠ grayAddParity (n + i + p) :=
  WalnutLifter.grayAddParity_fifth_power_free

end WalnutProphecySkolemLifterChallenge
