/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BsdaMixedBitwisePermPolys.Defs

/-!
# Trusted Challenge Statements (`bsda-mixed-bitwise-perm-polys`)

Headline infinite theorems; proofs are supplied in `Solution.lean`.
-/

namespace BsdaMixedBitwisePermPolysChallenge

open MixedPermEngine

/-- Universal Bit-Slice Lifting Theorem: a coherent family `f` is bijective at width `w`
    iff every bit-slice derivative `bitDeriv f i x` is `true` for all `i < w`. -/
theorem bijective_iff_forall_bitDeriv {f : ∀ w, BitVec w → BitVec w} (hf : Coherent f) (w : Nat) :
    Bijective (f w) ↔ ∀ (i : Nat), i < w → ∀ x : BitVec i, bitDeriv f i x = true := by
  sorry

-- ----------------------------------------------------------------------------
-- 4C. Crown-Jewel Three-Way BSDA Engine Theorems (Exact ↔ Lifting ∀ w ≥ 2)
-- ----------------------------------------------------------------------------

/-- **Engine Theorem 1 (Exact Necessary & Sufficient BSDA Decision Theorem):**
    For any `MixedExpr` compiling to `D`, `e` is bijective on `BitVec w` for ALL `w ≥ 2`
    IF AND ONLY IF the pure-data finite-state checker `D.checkBijective = true`. -/
theorem bsda_bijective_iff (e : MixedExpr) (D : DerivAuto) (h : compileBSDA e = some D) :
    (∀ w, 2 ≤ w → Bijective (e.eval w)) ↔ D.checkBijective = true := by
  sorry

/-- **Engine Theorem 2 (Exact Generalized Rivest Finite-Slice Lifting Theorem):**
    For any `MixedExpr` compiling to `D`, `e` is bijective on `BitVec w` for ALL `w ≥ 2`
    IF AND ONLY IF `e` is bijective at the single computable finite width `D.horizonW`
    (which equals `2` for all classical Rivest polynomials!). -/
theorem bsda_finite_slice_iff (e : MixedExpr) (D : DerivAuto) (h : compileBSDA e = some D) :
    (∀ w, 2 ≤ w → Bijective (e.eval w)) ↔ Bijective (e.eval D.horizonW) := by
  sorry

/-- **Infinite Theorem 1 (Generalized Bitwise-Masked Mixed-Connective Rivest Theorem):**
    For ANY constant `a0 : Int` and ANY list of masked shifted polynomial terms `ts` with
    arbitrary connectives `∈ {+, -, ^}`, `evalMaskedPoly w a0 ts` is bijective on `BitVec w`
    for ALL `w ≥ 2` IF AND ONLY IF:
    (1) bit-0 parity is `true`,
    (2) linear unshifted odd-coeff masks XOR to `true` at every bit `i ≥ 1`, AND
    (3) higher-odd-degree (`d ≥ 3`) unshifted odd-coeff masks XOR to `false` at every bit `i ≥ 1`. -/
theorem maskedPoly_bijective_iff (a0 : Int) (ts : List MaskedTerm) :
    (∀ w, 2 ≤ w → Bijective (evalMaskedPoly w a0 ts)) ↔
      (xorFold termBit0Deriv ts = true ∧
       (∀ i, 1 ≤ i → xorFold (fun t => termLinDeriv t i) ts = true) ∧
       (∀ i, 1 ≤ i → xorFold (fun t => termOddDeriv t i) ts = false)) := by
  sorry

theorem rivest_classical_mod4_iff (a0 : Int) (cs : List Int) :
    (∀ w, 2 ≤ w → Bijective (evalMaskedPoly w a0 (classicalTerms cs 1))) ↔
      Bijective (evalMaskedPoly 2 a0 (classicalTerms cs 1)) := by
  sorry

/-- **Infinite Theorem 2 (Exact Carry-Coupled Congruence Theorem):**
    For ALL `c, d : Int` and ALL widths `w : Nat`:
    `F_{c,d}(x) = x + (x &&& (x + c)) + (x &&& (x + d))` is bijective on `BitVec w`
    IF AND ONLY IF `c ≡ d (mod 2^w)` (i.e., `BitVec.ofInt w c = BitVec.ofInt w d`)! -/
theorem carryPair_bijective_iff (c d : Int) (w : Nat) :
    Bijective ((carryPairExpr c d).eval w) ↔ BitVec.ofInt w c = BitVec.ofInt w d := by
  sorry

/-- **Infinite Theorem 3B (Universal Add-XOR Carry Cancellation Law):**
    For ANY coherent `f, g` and ANY width `w`, `(f(x) + g(x)) ^^^ g(x)` is bijective
    IF AND ONLY IF `f(x)` is bijective! -/
theorem addXorCancel_bijective_iff {f g : ∀ w, BitVec w → BitVec w}
    (hf : Coherent f) (hg : Coherent g) (w : Nat) :
    Bijective (fun x : BitVec w => (f w x + g w x) ^^^ g w x) ↔ Bijective (f w) := by
  sorry

/-- **Infinite Theorem 3C (Generalized Klimov-Shamir Exact ↔ Criterion):**
    For ANY coherent T-function `g` (even wild nonlinear ones!) and ANY `c : Int`,
    `x + (g(x)^2 ||| c)` is bijective for ALL `w ≥ 2` IF AND ONLY IF
    `c` is odd OR `g(0)_0 = g(1)_0`! -/
theorem klimovShamir_general_iff {g : ∀ w, BitVec w → BitVec w} (hg : Coherent g) (c : Int) :
    (∀ w, 2 ≤ w → Bijective (fun x : BitVec w => x + ((g w x * g w x) ||| BitVec.ofInt w c))) ↔
      (intBit c 0 = true ∨ bit0Val g false = bit0Val g true) := by
  sorry

end BsdaMixedBitwisePermPolysChallenge
