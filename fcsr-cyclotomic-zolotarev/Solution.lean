/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FcsrCyclotomicZolotarev

/-!
# Verified Solutions (`fcsr-cyclotomic-zolotarev`)
-/

namespace FcsrCyclotomicZolotarevChallenge

open SiliconFCSR SiliconFCSR.Families

theorem word_representation_exact (spec : FCSRSpec) (s : FCSRState spec) (n : Nat) :
    spec.qInt * (spec.wordRun s n : Int) + ((2 ^ n : Nat) : Int) * spec.potential (spec.stepN n s)
    = spec.potential s :=
  SiliconFCSR.FCSRSpec.word_representation_exact spec s n

theorem step_bijection_on_core (spec : FCSRSpec) {s : FCSRState spec} (hs : spec.InCore s) :
    spec.invStep (spec.step s) = s ∧ spec.step (spec.invStep s) = s :=
  SiliconFCSR.FCSRSpec.step_bijection_on_core spec hs

theorem carry_bounds_on_core (spec : FCSRSpec) {s : FCSRState spec} (hs : spec.InCore s) :
    0 ≤ s.carry ∧ s.carry ≤ (spec.tapWeight : Int) - 1 :=
  SiliconFCSR.FCSRSpec.carry_bounds_on_core spec hs

theorem universal_carry_bit_conservation (spec : FCSRSpec) (s : FCSRState spec) (T : Nat)
    (hper : spec.stepN T s = s) :
    sumInt T (fun t => (spec.stepN t s).carry) =
    ((spec.tapWeight : Int) - 1) * sumInt T (fun t => (FCSRSpec.outBit (spec.stepN t s) : Int)) :=
  SiliconFCSR.FCSRSpec.universal_carry_bit_conservation spec s T hper

theorem halfPeriod_certificate (spec : FCSRSpec) {s : FCSRState spec} (hs : spec.InCore s)
    (h : Nat) (hdvd : spec.qInt ∣ (((2 ^ h : Nat) : Int) + 1) * spec.potential s) :
    spec.stepN h s = spec.complement s ∧
    spec.stepN (2 * h) s = s ∧
    (∀ t, FCSRSpec.outBit (spec.stepN (t + h) s) = 1 - FCSRSpec.outBit (spec.stepN t s)) ∧
    (∀ t, (spec.stepN (t + h) s).carry = (spec.tapWeight : Int) - 1 - (spec.stepN t s).carry) ∧
    sumInt (2 * h) (fun t => (FCSRSpec.outBit (spec.stepN t s) : Int)) = (h : Int) ∧
    sumInt (2 * h) (fun t => (spec.stepN t s).carry) = (h : Int) * ((spec.tapWeight : Int) - 1) :=
  SiliconFCSR.FCSRSpec.halfPeriod_certificate spec hs h hdvd

theorem dSection_cyclotomic_engine (spec : FCSRSpec) {s : FCSRState spec} (hs : spec.InCore s)
    (d k : Nat) (hd : 2 ≤ d) (hq_dvd : spec.q ∣ FCSRSpec.repunit d k) :
    spec.stepN (d * k) s = s ∧
    (∀ t, 1 ≤ spec.sectionQuantum s d k t ∧ spec.sectionQuantum s d k t ≤ (d : Int) - 1) ∧
    (∀ t, spec.sectionSum s d k t = -spec.qInt * spec.sectionQuantum s d k t) ∧
    (∀ t, spec.sectionQuantum s d k (t + k) = spec.sectionQuantum s d k t) ∧
    (∀ t, sumInt d (fun j => (FCSRSpec.outBit (spec.stepN (t + j * k) s) : Int)) =
          2 * spec.sectionQuantum s d k (t + 1) - spec.sectionQuantum s d k t) ∧
    sumInt (d * k) (fun t => (FCSRSpec.outBit (spec.stepN t s) : Int)) =
      sumInt k (fun t => spec.sectionQuantum s d k t) ∧
    sumInt (d * k) (fun t => (spec.stepN t s).carry) =
      ((spec.tapWeight : Int) - 1) * sumInt k (fun t => spec.sectionQuantum s d k t) :=
  SiliconFCSR.FCSRSpec.dSection_cyclotomic_engine spec hs d k hd hq_dvd

theorem even_period_of_mod8_3_or_5 (q : Nat) (hq_odd : q % 2 = 1) (hq : 3 ≤ q)
    (hmod8 : q % 8 = 3 ∨ q % 8 = 5) (T : Nat) (hpow : 2 ^ T % q = 1) :
    T % 2 = 0 :=
  SiliconFCSR.even_period_of_mod8_3_or_5 q hq_odd hq hmod8 T hpow

theorem family_pow2_add_3 (k : Nat) (hk : 3 ≤ k) :
    let spec := specPow2Add3 k hk
    spec.q = 2 ^ k + 3 ∧
    spec.tapWeight = 2 ∧
    (∀ s, spec.InCore s → 0 ≤ s.carry ∧ s.carry ≤ 1) ∧
    (∀ s, spec.InCore s →
      spec.potential s + 3 * spec.potential (spec.stepN k s) =
        spec.qInt * ((spec.wordRun s k : Int) + spec.potential (spec.stepN k s)) ∧
      -3 ≤ (spec.wordRun s k : Int) + spec.potential (spec.stepN k s) ∧
      (spec.wordRun s k : Int) + spec.potential (spec.stepN k s) ≤ -1) ∧
    (∀ T, spec.stepN T (spec.encode (-1)) = spec.encode (-1) → T % 2 = 0) :=
  SiliconFCSR.Families.family_pow2_add_3 k hk

end FcsrCyclotomicZolotarevChallenge
