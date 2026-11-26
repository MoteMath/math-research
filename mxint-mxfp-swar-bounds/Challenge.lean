/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MxintMxfpSwar.Defs

/-!
# Trusted Challenge Statements (`mxint-mxfp-swar-bounds`)

Universal and exact pure-`Init` (zero Mathlib) Lean 4 statements for:
1. Universal all-`B` symmetric `MXINT_w` EF21 contraction bounds with tight attainment
   (Continuous AbsMax and OCP `E8M0`).
2. Exact integer block-size crossovers `B*(w)` where `MXFP_w` overtakes `MXINT_w`
   (`MXINT4/6/8` vs `MXFP4-E2M1`, `MXFP6-E2M3`, `MXFP6-E3M2`, `MXFP8-E4M3`, `MXFP8-E2M5`).
3. Exact signed Kulisch accumulator bit-width laws for `MXINT_w × MXINT_w` dot products
   (zero-overflow `int12` `MXINT4`, 2-lane `int16` SWAR `MXINT6`, and `+1` asymmetric overflow).
4. Zero-free half-integer `MXINT_w` exact `O(1/B)` rescaled collapse and `E8M0` divergence thresholds.
5. Asymmetric `MXINT4 [-8, 7]` vs symmetric `[-7, 7]` exact `B ≥ 16` AbsMax crossover and `E8M0`
   `7 vs 8` non-power-of-two scale cliff.
6. Unconditional associativity, block-split additivity, and permutation invariance of exact
   integer Kulisch dot products.
-/

namespace MxintMxfpSwarChallenge

open MxintMxfpSwar

/-- Theorem 1 (`mxint_all_b_ef21_contraction_exact`):
    Universal all-`B` (`B ≥ 1, w ≥ 2`) worst-case EF21 relative MSE bounds with tight attainment
    for symmetric `MXINT_w` (`M = 2^(w-1) - 1`) under both Continuous AbsMax
    (`(B - 1) / (4 M^2 + B - 1)`) and OCP `E8M0` (`B / (M^2 + B - 1)`). -/
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
        finSum e / l2NormSq u = omegaMxintE8M0 w B) := by
  sorry

/-- Theorem 2 (`mxint_vs_mxfp_exact_blocksize_crossover`):
    Universal `MXFP` Continuous AbsMax upper bound plus exact integer block-size crossovers
    `B*(w)` where `MXFP_w` overtakes `MXINT_w` under BOTH Continuous AbsMax and OCP `E8M0`:
    `MXINT4` vs `MXFP4-E2M1` (`8 / 3`), `MXINT6` vs `MXFP6-E2M3` (`12 / 4`) and `MXFP6-E3M2`
    (`47 / 13`), `MXINT8` vs `MXFP8-E4M3` (`223 / 57`, strictly winning at BOTH `B = 16` and
    `B = 32`), and `MXINT8` vs `MXFP8-E2M5` (`13 / 5`). -/
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
     (∀ B : Nat, 5 ≤ B → omegaMxfpE8M0 mxfp8E2M5 B < omegaMxintE8M0 8 B)) := by
  sorry

/-- Theorem 3 (`kulisch_mxint_zero_overflow_swar_exact`):
    Exact signed Kulisch accumulator bit-width laws for `MXINT_w × MXINT_w` dot products:
    symmetric `MXINT4` fits in `int12` at `B = 32`, symmetric `MXINT6` fits in `int16`
    (`[-30752, 30752] ⊂ [-32768, 32767]`, enabling 2-lane 32-bit SWAR with zero overflow),
    while asymmetric `MXINT6 [-32, 31]` attains `32 * (-32) * (-32) = 32768 > 32767`,
    overflowing `int16` by exact 1. -/
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
     32 / 17 = 1) := by
  sorry

/-- Theorem 4 (`half_integer_zero_free_o_one_over_b_collapse`):
    Zero-free half-integer `MXINT_w` suffers exact rescaled EF21 collapse
    `α_rescaled = (2^w - 1)^2 / ((2^w - 1)^2 + B - 1) = O(1/B)` and diverges (`ω ≥ 1`) under
    `E8M0` at exact integer thresholds `B_div^E8M0(w) ∈ {3, 13, 57, 993, 16257}` for
    `w ∈ {2, 3, 4, 6, 8}`. -/
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
     halfDivE8M0 6 = 993 ∧ halfDivE8M0 8 = 16257) := by
  sorry

/-- Theorem 5 (`mxint4_asym_beats_sym_crossover_b16`):
    Asymmetric `MXINT4 [-8, 7]` ties symmetric `[-7, 7]` at exact `B = 15` (`1/15`) and strictly
    beats it on AbsMax EF21 contraction for ALL `B ≥ 16`, signed-scale asymmetric beats symmetric
    for all `B ≥ 2`, and on Uniform blocks in `(7 · 2^k, 8 · 2^k]` OCP `E8M0` incurs an exact
    `4×` MSE non-power-of-two scale cliff on symmetric `[-7, 7]` versus asymmetric `[-8, 7]`. -/
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
      uniformStepMse sSym / uniformStepMse sAsym = 4) := by
  sorry

/-- Theorem 6 (`mxint_exact_integer_associativity`):
    Exact signed Kulisch accumulation of `B`-element `MXINT_w` dot products in `Int` is
    unconditionally associative, block-split additive, and permutation-invariant. -/
theorem mxint_exact_integer_associativity :
    (∀ a b c : Int, (a + b) + c = a + (b + c)) ∧
    (∀ (B1 B2 : Nat) (x1 y1 : Fin B1 → Int) (x2 y2 : Fin B2 → Int),
      intDot (appendVec x1 x2) (appendVec y1 y2) = intDot x1 y1 + intDot x2 y2) ∧
    (∀ (B : Nat) (x y : Fin B → Int) (σ : Fin B → Fin B),
      IsBijective σ →
      intDot (fun i => x (σ i)) (fun i => y (σ i)) = intDot x y) := by
  sorry

end MxintMxfpSwarChallenge
