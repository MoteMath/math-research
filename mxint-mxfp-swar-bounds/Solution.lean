/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MxintMxfpSwar

/-!
# Verified Solutions (`mxint-mxfp-swar-bounds`)
-/

namespace MxintMxfpSwarChallenge

open MxintMxfpSwar

theorem mxint_all_b_ef21_contraction_exact :
    (∀ (w B : Nat), 2 ≤ w → 1 ≤ B →
      ∀ (u e : Fin B → Rat) (i0 : Fin B),
        ratAbs (u i0) = mxintMaxRat w → e i0 = 0 → IsMxintErr u e →
        finSum e / l2NormSq u ≤ omegaMxintAbsMax w B) ∧
    (∀ (w B : Nat), 2 ≤ w → 1 ≤ B →
      ∃ (u e : Fin B → Rat) (i0 : Fin B),
        ratAbs (u i0) = mxintMaxRat w ∧ e i0 = 0 ∧ IsMxintErr u e ∧
        finSum e / l2NormSq u = omegaMxintAbsMax w B) ∧
    (∀ (w B : Nat), 2 ≤ w → 1 ≤ B →
      ∀ (u e : Fin B → Rat) (i0 : Fin B),
        mxintMaxRat w / 2 ≤ ratAbs (u i0) → IsMxintErr u e →
        finSum e / l2NormSq u ≤ omegaMxintE8M0 w B) ∧
    (∀ (w B : Nat), 2 ≤ w → 1 ≤ B →
      ∃ (u e : Fin B → Rat) (i0 : Fin B),
        mxintMaxRat w / 2 ≤ ratAbs (u i0) ∧ IsMxintErr u e ∧
        finSum e / l2NormSq u = omegaMxintE8M0 w B) :=
  MxintMxfpSwar.mxint_all_b_ef21_contraction_exact

theorem mxint_vs_mxfp_exact_blocksize_crossover :
    (∀ (spec : MxfpSpec),
      (0 : Rat) < spec.M → (0 : Rat) < spec.rhoNorm → spec.rhoNorm < 1 →
      spec.eHi = spec.rhoNorm * (spec.vHi * spec.vHi) → (0 : Rat) ≤ spec.eHi →
      ∀ (B : Nat), 1 ≤ B → ∀ (u e : Fin B → Rat) (i0 : Fin B),
        ratAbs (u i0) = spec.M → e i0 = 0 → IsMxfpErr spec u e →
        finSum e / l2NormSq u ≤ omegaMxfpAbsMax spec B) ∧
    ((∀ B : Nat, 2 ≤ B → B < 8 → omegaMxintAbsMax 4 B < omegaMxfpAbsMax mxfp4E2M1 B) ∧
     (∀ B : Nat, 8 ≤ B → omegaMxfpAbsMax mxfp4E2M1 B < omegaMxintAbsMax 4 B) ∧
     (∀ B : Nat, 1 ≤ B → B < 3 → omegaMxintE8M0 4 B < omegaMxfp4E2M1E8M0 B) ∧
     (∀ B : Nat, 3 ≤ B → omegaMxfp4E2M1E8M0 B < omegaMxintE8M0 4 B)) ∧
    ((∀ B : Nat, 2 ≤ B → B < 12 → omegaMxintAbsMax 6 B < omegaMxfpAbsMax mxfp6E2M3 B) ∧
     (∀ B : Nat, 12 ≤ B → omegaMxfpAbsMax mxfp6E2M3 B < omegaMxintAbsMax 6 B) ∧
     (∀ B : Nat, 1 ≤ B → B < 4 → omegaMxintE8M0 6 B < omegaMxfpE8M0 mxfp6E2M3 B) ∧
     (∀ B : Nat, 4 ≤ B → omegaMxfpE8M0 mxfp6E2M3 B < omegaMxintE8M0 6 B)) ∧
    ((∀ B : Nat, 2 ≤ B → B < 47 → omegaMxintAbsMax 6 B < omegaMxfpAbsMax mxfp6E3M2 B) ∧
     (∀ B : Nat, 47 ≤ B → omegaMxfpAbsMax mxfp6E3M2 B < omegaMxintAbsMax 6 B) ∧
     (∀ B : Nat, 1 ≤ B → B < 13 → omegaMxintE8M0 6 B < omegaMxfpE8M0 mxfp6E3M2 B) ∧
     (∀ B : Nat, 13 ≤ B → omegaMxfpE8M0 mxfp6E3M2 B < omegaMxintE8M0 6 B)) ∧
    ((∀ B : Nat, 2 ≤ B → B < 223 → omegaMxintAbsMax 8 B < omegaMxfpAbsMax mxfp8E4M3 B) ∧
     (∀ B : Nat, 223 ≤ B → omegaMxfpAbsMax mxfp8E4M3 B < omegaMxintAbsMax 8 B) ∧
     (∀ B : Nat, 1 ≤ B → B < 57 → omegaMxintE8M0 8 B < omegaMxfpE8M0 mxfp8E4M3 B) ∧
     (∀ B : Nat, 57 ≤ B → omegaMxfpE8M0 mxfp8E4M3 B < omegaMxintE8M0 8 B) ∧
     omegaMxintAbsMax 8 16 < omegaMxfpAbsMax mxfp8E4M3 16 ∧
     omegaMxintAbsMax 8 32 < omegaMxfpAbsMax mxfp8E4M3 32 ∧
     omegaMxintE8M0 8 16 < omegaMxfpE8M0 mxfp8E4M3 16 ∧
     omegaMxintE8M0 8 32 < omegaMxfpE8M0 mxfp8E4M3 32) ∧
    ((∀ B : Nat, 2 ≤ B → B < 13 → omegaMxintAbsMax 8 B < omegaMxfpAbsMax mxfp8E2M5 B) ∧
     (∀ B : Nat, 13 ≤ B → omegaMxfpAbsMax mxfp8E2M5 B < omegaMxintAbsMax 8 B) ∧
     (∀ B : Nat, 1 ≤ B → B < 5 → omegaMxintE8M0 8 B < omegaMxfpE8M0 mxfp8E2M5 B) ∧
     (∀ B : Nat, 5 ≤ B → omegaMxfpE8M0 mxfp8E2M5 B < omegaMxintE8M0 8 B)) :=
  MxintMxfpSwar.mxint_vs_mxfp_exact_blocksize_crossover

theorem kulisch_mxint_zero_overflow_swar_exact :
    (∀ (w B : Nat) (x y : Fin B → Int), InSymRange w x → InSymRange w y →
      -kulischSymMax w B ≤ intDot x y ∧ intDot x y ≤ kulischSymMax w B) ∧
    (∀ (w B : Nat), ∃ (x y : Fin B → Int),
      InSymRange w x ∧ InSymRange w y ∧ intDot x y = kulischSymMax w B) ∧
    (∀ (w B : Nat), 1 ≤ w → ∀ (x y : Fin B → Int), InAsymRange w x → InAsymRange w y →
      kulischAsymMin w B ≤ intDot x y ∧ intDot x y ≤ kulischAsymMax w B) ∧
    (kulischSymMax 4 32 = 1568 ∧
     (∀ (x y : Fin 32 → Int), InSymRange 4 x → InSymRange 4 y →
       fitsSignedWidth 12 (intDot x y)) ∧
     ¬ fitsSignedWidth 11 (kulischSymMax 4 32)) ∧
    (kulischSymMax 6 32 = 30752 ∧
     (∀ (x y : Fin 32 → Int), InSymRange 6 x → InSymRange 6 y →
       fitsSignedWidth 16 (intDot x y)) ∧
     ¬ fitsSignedWidth 15 (kulischSymMax 6 32) ∧
     32 / 16 = 2) ∧
    (kulischAsymMax 6 32 = 32768 ∧
     (∃ (x y : Fin 32 → Int), InAsymRange 6 x ∧ InAsymRange 6 y ∧
       intDot x y = 32768 ∧ intDot x y = (2 ^ 15 - 1 : Int) + 1 ∧
       ¬ fitsSignedWidth 16 (intDot x y)) ∧
     (∀ (x y : Fin 32 → Int), InAsymRange 6 x → InAsymRange 6 y →
       fitsSignedWidth 17 (intDot x y)) ∧
     32 / 17 = 1) :=
  MxintMxfpSwar.kulisch_mxint_zero_overflow_swar_exact

theorem half_integer_zero_free_o_one_over_b_collapse :
    (∀ (w B : Nat), 2 ≤ w → 1 ≤ B →
      let u : Fin B → Rat := fun j => if j.val = 0 then halfIntMax w else 0
      let e : Fin B → Rat := fun j => if j.val = 0 then 0 else 1 / 4
      finSum e / l2NormSq u = omegaHalfAbsMax w B ∧
      ((1 : Rat) ≤ omegaHalfAbsMax w B ↔ (2 ^ w - 1) * (2 ^ w - 1) + 1 ≤ B)) ∧
    (∀ (w B : Nat), 2 ≤ w → 2 ≤ B →
      alphaHalfRescaled w B < ((2 ^ w - 1 : Nat) : Rat) * ((2 ^ w - 1 : Nat) : Rat) /
        ((B - 1 : Nat) : Rat)) ∧
    (∀ (w : Nat), 2 ≤ w → ∀ (ε : Rat), (0 : Rat) < ε →
      ∃ B : Nat, 1 ≤ B ∧ alphaHalfRescaled w B < ε) ∧
    (∀ (w B : Nat), 2 ≤ w → 1 ≤ B →
      let u : Fin B → Rat := fun j => if j.val = 0 then halfIntMax w / 2 else 0
      let e : Fin B → Rat := fun j => if j.val = 0 then 1 / 16 else 1 / 4
      finSum e / l2NormSq u = omegaHalfE8M0 w B ∧
      ((1 : Rat) ≤ omegaHalfE8M0 w B ↔ halfDivE8M0 w ≤ B)) ∧
    (halfDivE8M0 2 = 3 ∧ halfDivE8M0 3 = 13 ∧ halfDivE8M0 4 = 57 ∧
     halfDivE8M0 6 = 993 ∧ halfDivE8M0 8 = 16257) :=
  MxintMxfpSwar.half_integer_zero_free_o_one_over_b_collapse

theorem mxint4_asym_beats_sym_crossover_b16 :
    (omegaMxint4SymAbsMax 15 = 1 / 15 ∧ omegaMxint4AsymAbsMax 15 = 1 / 15) ∧
    (∀ B : Nat, 1 ≤ B → B ≤ 14 → omegaMxint4SymAbsMax B < omegaMxint4AsymAbsMax B) ∧
    (∀ B : Nat, 16 ≤ B → omegaMxint4AsymAbsMax B < omegaMxint4SymAbsMax B) ∧
    (omegaMxint4AsymAbsMax 16 = 19 / 271 ∧ omegaMxint4SymAbsMax 16 = 15 / 211 ∧
     omegaMxint4AsymAbsMax 32 = 5 / 41 ∧ omegaMxint4SymAbsMax 32 = 31 / 227) ∧
    (∀ B : Nat, 2 ≤ B → omegaMxint4AsymSignedAbsMax B < omegaMxint4SymAbsMax B) ∧
    (∀ (k : Nat) (xMax : Rat),
      (7 : Rat) * ((2 ^ k : Nat) : Rat) < xMax → xMax ≤ (8 : Rat) * ((2 ^ k : Nat) : Rat) →
      let sSym : Rat := ((2 ^ (k + 1) : Nat) : Rat)
      let sAsym : Rat := ((2 ^ k : Nat) : Rat)
      xMax ≤ (7 : Rat) * sSym ∧
      ¬ (xMax ≤ (7 : Rat) * sAsym) ∧
      xMax ≤ (8 : Rat) * sAsym ∧
      uniformStepMse sSym / uniformStepMse sAsym = 4) :=
  MxintMxfpSwar.mxint4_asym_beats_sym_crossover_b16

theorem mxint_exact_integer_associativity :
    (∀ a b c : Int, (a + b) + c = a + (b + c)) ∧
    (∀ (B1 B2 : Nat) (x1 y1 : Fin B1 → Int) (x2 y2 : Fin B2 → Int),
      intDot (appendVec x1 x2) (appendVec y1 y2) = intDot x1 y1 + intDot x2 y2) ∧
    (∀ (B : Nat) (x y : Fin B → Int) (σ : Fin B → Fin B),
      IsBijective σ →
      intDot (fun i => x (σ i)) (fun i => y (σ i)) = intDot x y) :=
  MxintMxfpSwar.mxint_exact_integer_associativity

end MxintMxfpSwarChallenge
