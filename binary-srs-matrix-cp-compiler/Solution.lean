/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BinarySrsMatrixCpCompiler

/-!
# Verified Solutions (`binary-srs-matrix-cp-compiler`)
-/

namespace BinarySrsMatrixCpCompilerChallenge

open CertComp16

theorem cert_sound (R : SRS) (cert : ConfluenceCert) (h : checkCert R cert = true) :
    Terminating R ∧ Confluent R ∧ UniqueNormalForms R :=
  CertComp16.cert_sound R cert h

theorem convertible_iff_normalize_eq {R : SRS} {cert : ConfluenceCert}
    (h : checkCert R cert = true) (hTerm : Terminating R) (u v : Word) :
    Convertible R u v ↔ normalize R hTerm u = normalize R hTerm v :=
  CertComp16.convertible_iff_normalize_eq h u v

theorem confluent_of_term_invariant {R : SRS} {α : Type} (inv : Word → α)
    (hTerm : Terminating R)
    (hInv : ∀ u v, Step R u v → inv u = inv v)
    (hNFInj : ∀ n₁ n₂, IsNormalForm R n₁ → IsNormalForm R n₂ → inv n₁ = inv n₂ → n₁ = n₂) :
    Confluent R ∧ UniqueNormalForms R ∧ (∀ u v, Convertible R u v ↔ inv u = inv v) :=
  CertComp16.confluent_of_term_invariant inv hTerm hInv hNFInj

theorem ampSys_terminating (b r s k d : Nat)
    (hb : 2 ≤ b) (hrs : s < r) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    Terminating (ampSys b r s k d) :=
  CertComp16.ampSys_terminating b r s k d hb hrs hk hd

theorem ampSys_confluent_iff (b r s k d : Nat)
    (hb : 2 ≤ b) (hrs : s < r) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    Confluent (ampSys b r s k d) ↔ (k ≤ b ^ s ∧ d ∣ (b ^ r - b ^ s)) :=
  CertComp16.ampSys_confluent_iff b r s k d hb hrs hk hd

theorem mod3_convertible_iff (u v : Word) :
    Convertible mod3SRS u v ↔ u.length = v.length ∧ binVal u % 3 = binVal v % 3 :=
  CertComp16.mod3_convertible_iff u v

theorem mersenneSRS_master (m : Nat) (hm : 2 ≤ m) :
    Terminating (mersenneSRS m) ∧ Confluent (mersenneSRS m) ∧
    UniqueNormalForms (mersenneSRS m) ∧
    (∀ u v, Convertible (mersenneSRS m) u v ↔
      u.length = v.length ∧ binVal u % (2 ^ m - 1) = binVal v % (2 ^ m - 1)) :=
  CertComp16.mersenneSRS_master m hm

theorem fermatModSRS_master (m : Nat) (hm : 1 ≤ m) :
    Terminating (fermatModSRS m) ∧ Confluent (fermatModSRS m) ∧
    UniqueNormalForms (fermatModSRS m) ∧
    (∀ u v, Convertible (fermatModSRS m) u v ↔
      u.length = v.length ∧ binVal u % (2 ^ m + 1) = binVal v % (2 ^ m + 1)) :=
  CertComp16.fermatModSRS_master m hm

end BinarySrsMatrixCpCompilerChallenge
