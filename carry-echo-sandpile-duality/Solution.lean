/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CarryEchoSandpileDuality

/-!
# Verified Solutions (`carry-echo-sandpile-duality`)
-/

namespace CarryEchoSandpileDualityChallenge

open SiliconSandpile in
/-- Theorem 1 (Carry-echo skew conservation): every avalanche conserves skewWeight up to top-site topplings times the repunit (b^(w+1) - 1)/(b - 1). -/
theorem carryEcho_skew_conservation (b w : Nat) (hw : 0 < w) {c c' f : Fin w → Nat}
    (h : (carryEchoSys b w).Steps c f c') :
    skewWeight b w c = skewWeight b w c' + f ⟨w - 1, by omega⟩ * repunit b (w + 1) :=
  SiliconSandpile.carryEcho_skew_conservation b w hw h

open SiliconSandpile in
/-- Theorem 2 (Total avalanche law): the quadratic-harmonic potential psiPotential drops by exactly the total toppling count times (b^(w+1) - 1). -/
theorem carryEcho_total_avalanche_law (b w : Nat) (hb : 2 ≤ b)
    {c c' f : Fin w → Nat} (h : (carryEchoSys b w).Steps c f c') :
    psiPotential b w c = psiPotential b w c' + finSum w f * (b ^ (w + 1) - 1) :=
  SiliconSandpile.carryEcho_total_avalanche_law b w hb h

open SiliconSandpile in
/-- Theorem 3 (Dual-skew recurrence classification): a carry-echo configuration is recurrent iff it satisfies the local dual-skew canonicality predicate. -/
theorem carryEcho_recurrent_iff_dualSkew (b w : Nat) (hb : 2 ≤ b) (hw : 0 < w) (c : Fin w → Nat) :
    (carryEchoSys b w).IsRecurrent (carryEchoM1Pot b w hb) c ↔ IsDualSkew b w c :=
  SiliconSandpile.carryEcho_recurrent_iff_dualSkew b w hb hw c

open SiliconSandpile in
/-- Theorem 4 (right-inverse half of the repunit bijection): for every `r : Fin (repunit b (w + 1))`, encoding the Myers greedy decoding of `r` gives back `r`. The converse half (`decode (encode c) = c` on recurrent configurations) is proved in the library but is not part of this statement. -/
theorem carryEcho_recurrent_count_left (b w : Nat) (hb : 2 ≤ b) (hw : 0 < w)
    (r : Fin (repunit b (w + 1))) :
    (carryEchoGroupCert b w hb hw).encode ((carryEchoGroupCert b w hb hw).decode r) = r :=
  SiliconSandpile.carryEcho_recurrent_count_left b w hb hw r

open SiliconSandpile in
/-- Theorem 5 (Closed-form sandpile identity): the explicit closed-form configuration explicitIdentity b w equals the sandpile group identity for all b >= 2 and w >= 1. -/
theorem carryEcho_explicitIdentity_eq (b w : Nat) (hb : 2 ≤ b) (hw : 0 < w) :
    explicitIdentity b w = (carryEchoGroupCert b w hb hw).identity :=
  SiliconSandpile.carryEcho_explicitIdentity_eq b w hb hw

open SiliconSandpile in
/-- Theorem 6 (Universal self-addition identity laws): for all b >= 2 and w >= 2, explicitIdentity satisfies exact harmonic value, top-site firing 1, and chip-mass congruence. -/
theorem carryEcho_identity_laws_ge2 (b w : Nat) (hb : 2 ≤ b) (hw : 2 ≤ w) :
    let S := carryEchoSys b w
    let P := carryEchoM1Pot b w hb
    let e := explicitIdentity b w
    let f := S.odom P (addCfg e e)
    skewWeight b w e = repunit b (w + 1) ∧
    f ⟨w - 1, by omega⟩ = 1 ∧
    (b - 1) * finSum w f + (w + 1) = firstMoment w e ∧
    chipMass w e = b * f ⟨0, by omega⟩ + 1 ∧
    baseValue b w e = b ^ w + f ⟨0, by omega⟩ :=
  SiliconSandpile.carryEcho_identity_laws_ge2 b w hb hw

open SiliconSandpile in
/-- Theorem 7 (Directed-carry all-stable recurrence): in the directed-carry sandpile, every stable configuration is recurrent. -/
theorem directedCarry_all_stable_recurrent (b w : Nat) (hb : 2 ≤ b) (hw : 0 < w) (c : Fin w → Nat) :
    (directedCarrySys b w hb).IsRecurrent (directedCarryMassPot b w hb) c ↔
    (directedCarrySys b w hb).IsStable c :=
  SiliconSandpile.directedCarry_all_stable_recurrent b w hb hw c

open SiliconSandpile in
/-- Theorem 8 (Directed-carry Kummer conservation): chip mass drops by (b - 1) times total topplings plus top-site overflow, matching Kummer's carry theorem. -/
theorem directedCarry_kummer_conservation (b w : Nat) (hb : 2 ≤ b) (hw : 0 < w)
    {c c' f : Fin w → Nat} (h : (directedCarrySys b w hb).Steps c f c') :
    chipMass w c = chipMass w c' + (b - 1) * finSum w f + f ⟨w - 1, by omega⟩ :=
  SiliconSandpile.directedCarry_kummer_conservation b w hb hw h

end CarryEchoSandpileDualityChallenge
