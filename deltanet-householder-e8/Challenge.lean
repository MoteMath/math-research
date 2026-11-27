/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DeltaNetHouseholderE8.Defs

/-!
# Trusted Challenge Statements (`deltanet-householder-e8`)

Universal and exact pure-`Init` (zero Mathlib) Lean 4 statements for:
1. Exact rational Householder spectral-contraction `iff` law (`0 ≤ β ‖k‖_2^2 ≤ 2`).
2. Quantized unit-norm squared bound `S_max^(1)(m) > 1` under a hypothesised per-coordinate ratio (not a formalisation of IEEE-754 RNE) and the `287/256` `FP8-E4M3`-grid witness.
3. 2-ULP ceiling inequalities for all `m ≥ 2`: `β_1(m) * S_max^(1)(m) > 2` and `β_2(m) * S_max^(1)(m) < 2` (rational inequalities about the stated bound).
4. Exact aligned-key WY triangular inverse `T_{i,j} = (-1)^{i-j} * 2` and `‖T‖_∞ = 2C - 1` (`127` at `C = 64`).
5. `D_8` and 240-root `2 * E_8` Weyl root exact zero-remainder (`% 8 = 0`) integer reflections.
6. Non-Weyl `Hamming[8,4,4]` integer-closure obstruction (`(2 * dot v x) % 4 = 2 ≠ 0`, `1/2 ∉ ℤ`).
-/

namespace DeltaNetHouseholderE8Challenge

open DeltaNetHouseholderE8

/-- Theorem 1 (`householder_spectral_stability_iff_exact`):
    For any vector `k ∈ ℚ^d` and scalar `β ∈ ℚ`, proves the exact rational
    norm-update identity, the exact eigenvalue `1 - β ‖k‖_2^2` along `k`,
    the exact spectral-contraction `iff` law `∀ v, ‖(I - β k k^T) v‖_2^2 ≤ ‖v‖_2^2 ↔ 0 ≤ β ‖k‖_2^2 ≤ 2`,
    and strict spectral explosion whenever `β ‖k‖_2^2 > 2` and `‖k‖_2^2 > 0`. -/
theorem householder_spectral_stability_iff_exact :
    (∀ (d : Nat) (β : Rat) (k v : Fin d → Rat),
      l2NormSq (householderApply β k v) =
        l2NormSq v - β * (2 - β * l2NormSq k) * (dotProd k v * dotProd k v)) ∧
    (∀ (d : Nat) (β : Rat) (k : Fin d → Rat),
      householderApply β k k = (fun i => (1 - β * l2NormSq k) * k i) ∧
      l2NormSq (householderApply β k k) =
        (1 - β * l2NormSq k) * (1 - β * l2NormSq k) * l2NormSq k) ∧
    (∀ (d : Nat) (β : Rat) (k : Fin d → Rat),
      (∀ v : Fin d → Rat, l2NormSq (householderApply β k v) ≤ l2NormSq v) ↔
        ((0 : Rat) ≤ β * l2NormSq k ∧ β * l2NormSq k ≤ 2)) ∧
    (∀ (d : Nat) (β : Rat) (k : Fin d → Rat),
      (0 : Rat) < l2NormSq k → (2 : Rat) < β * l2NormSq k →
        l2NormSq k < l2NormSq (householderApply β k k) ∧
        (1 : Rat) < ratAbs (1 - β * l2NormSq k)) := by
  sorry

/-- Theorem 2 (`quantized_unit_norm_supremum_exact`):
    Defines `S_max^(1)(m) = ((2^{m+1} + 2) / (2^{m+1} + 1))^2` (`sMax1`) and proves its
    closed forms and `S_max^(1)(m) > 1` for all `m ≥ 1`. The universal bound is
    conditional: for a unit vector `u`, every `uHat` whose coordinates satisfy the
    HYPOTHESIS `|uHat_i| ≤ r_m * |u_i|`, with `r_m = rneBinadeBottomRatio m`, has
    `‖uHat‖_2^2 ≤ S_max^(1)(m)`. Nothing in the statement derives this hypothesis from
    IEEE-754 round-to-nearest-even, and the bound is not shown to be attained (the
    `FP8-E4M3`-grid witness has norm^2 `287/256 < 324/289 = S_max^(1)(3)`). Also proves the
    exact values for `m = 7`, `10`, `3`, and for `fp8WitnessVec`: norm^2 `287/256`,
    `β_1(3) * ‖w‖^2 > 2` and `β_2(3) * ‖w‖^2 < 2`. -/
theorem quantized_unit_norm_supremum_exact :
    (∀ m : Nat, rneBinadeBottomRatio m = (pow2Rat (m + 1) + 2) / (pow2Rat (m + 1) + 1)) ∧
    (∀ m : Nat, sMax1 m = rneBinadeBottomRatio m * rneBinadeBottomRatio m) ∧
    (∀ m : Nat, sMax1 m =
      1 + (pow2Rat (m + 2) + 3) / ((pow2Rat (m + 1) + 1) * (pow2Rat (m + 1) + 1))) ∧
    (∀ m : Nat, 1 ≤ m → (1 : Rat) < sMax1 m) ∧
    (∀ (d m : Nat) (u uHat : Fin d → Rat),
      l2NormSq u = 1 →
      (∀ i : Fin d, ratAbs (uHat i) ≤ rneBinadeBottomRatio m * ratAbs (u i)) →
      l2NormSq uHat ≤ sMax1 m) ∧
    (sMax1 7 = 66564 / 66049 ∧
     sMax1 10 = 4202500 / 4198401 ∧
     sMax1 3 = 324 / 289) ∧
    (l2NormSq fp8WitnessVec = 287 / 256 ∧
     (1 : Rat) < l2NormSq fp8WitnessVec ∧
     l2NormSq fp8WitnessVec < sMax1 3 ∧
     (2 : Rat) < betaOneUlp 3 * l2NormSq fp8WitnessVec ∧
     betaTwoUlp 3 * l2NormSq fp8WitnessVec < 2) := by
  sorry

/-- Theorem 3 (`universal_two_ulp_safe_ceiling_theorem`):
    For all `m ≥ 2`: `β_1(m) * S_max^(1)(m) > 2` with `β_1(m) = 2 - 2^{-m}`, and
    `β_2(m) * S_max^(1)(m) < 2` with `β_2(m) = 2 - 2^{1-m}` (`127/64` for `m = 7`,
    `1023/512` for `m = 10`, `7/4` for `m = 3`). Consequently, for every `k` with
    `‖k‖_2^2 ≤ S_max^(1)(m)` the update with `β_2(m)` is non-expansive, and the single
    coordinate `k = r_m` with `β_1(m)` strictly expands. "Safe" and "unsafe" refer to the
    stated bound `S_max^(1)(m)` (see Theorem 2), not to hardware rounding. -/
theorem universal_two_ulp_safe_ceiling_theorem :
    (∀ m : Nat, 2 ≤ m → (2 : Rat) < betaOneUlp m * sMax1 m) ∧
    (∀ m : Nat, 2 ≤ m →
      (0 : Rat) < betaTwoUlp m ∧
      betaTwoUlp m * sMax1 m < 2 ∧
      betaTwoUlp m * sMax1 m ≤ 2) ∧
    (∀ m : Nat, 1 ≤ m → betaTwoUlp m = 2 - invPow2Rat (m - 1)) ∧
    (betaTwoUlp 7 = 127 / 64 ∧
     betaTwoUlp 10 = 1023 / 512 ∧
     betaTwoUlp 3 = 7 / 4) ∧
    (∀ (d m : Nat) (k : Fin d → Rat),
      2 ≤ m → l2NormSq k ≤ sMax1 m →
      ∀ v : Fin d → Rat, l2NormSq (householderApply (betaTwoUlp m) k v) ≤ l2NormSq v) ∧
    (∀ m : Nat, 2 ≤ m →
      let r := rneBinadeBottomRatio m
      let k : Fin 1 → Rat := fun _ => r
      l2NormSq k = sMax1 m ∧
      l2NormSq k < l2NormSq (householderApply (betaOneUlp m) k k) ∧
      (1 : Rat) < ratAbs (1 - betaOneUlp m * l2NormSq k)) := by
  sorry

/-- Theorem 4 (`wy_triangular_inverse_norm_growth_exact`):
    Proves that for aligned unit keys (`K K^T = 1 1^T`) at `β = 2`, the WY triangular
    matrix `I + 2 * strictLower(1 1^T)` has exact two-sided inverse `T` with alternating
    entries `T_{i,j} = (-1)^{i-j} * 2` for `i > j`, exact row `ℓ_1`-norm `2i + 1`,
    and exact matrix `∞`-norm `‖T‖_∞ = 2C - 1` (`127` at chunk size `C = 64`). -/
theorem wy_triangular_inverse_norm_growth_exact :
    (∀ (C : Nat) (i j : Fin C),
      matMul (wyAlignedMat C) (wyAlignedInv C) i j = identityMat C i j ∧
      matMul (wyAlignedInv C) (wyAlignedMat C) i j = identityMat C i j) ∧
    (∀ (C : Nat) (i j : Fin C), j.val < i.val →
      wyAlignedInv C i j = if (i.val - j.val) % 2 = 0 then 2 else -2) ∧
    (∀ (C : Nat) (i : Fin C),
      rowL1Norm (wyAlignedInv C) i = 2 * (i.val : Rat) + 1) ∧
    (∀ (C : Nat) (hC : 0 < C),
      (∀ i : Fin C, rowL1Norm (wyAlignedInv C) i ≤ 2 * (C : Rat) - 1) ∧
      rowL1Norm (wyAlignedInv C) ⟨C - 1, Nat.sub_lt hC (by decide)⟩ = 2 * (C : Rat) - 1) ∧
    (rowL1Norm (wyAlignedInv 64) ⟨63, by decide⟩ = 127) := by
  sorry

/-- Theorem 5 (`d8_and_e8_weyl_root_zero_ulp_orthogonality`):
    Proves exact zero-remainder integer reflection closure and exact Euclidean norm
    preservation for every root `v ∈ D_8` (`‖v‖_2^2 = 2`) and every root `w ∈ 2 * E_8`
    (`‖w‖_2^2 = 8`, classified into the 112 integer roots `(±2, ±2, 0^6)` + 128 half-integer
    roots `(±1)^8` with even number of minuses, total `240`), with `(2 * dot w x) % 8 = 0`
    and `dot w x % 4 = 0` identically on `2 * E_8`. -/
theorem d8_and_e8_weyl_root_zero_ulp_orthogonality :
    (∀ (v x : Fin 8 → Int), IsD8Root v →
      (2 * intDot8 v x) % 2 = 0 ∧
      intNormSq8 (reflectD8 v x) = intNormSq8 x ∧
      reflectD8 v (reflectD8 v x) = x ∧
      (InD8Lattice x → InD8Lattice (reflectD8 v x))) ∧
    (∀ w : Fin 8 → Int, IsTwoE8Root w ↔ (IsTwoE8IntRoot w ∨ IsTwoE8HalfIntRoot w)) ∧
    ((8 * 7 / 2) * 4 = 112 ∧ 2 ^ 7 = 128 ∧ 112 + 128 = 240) ∧
    (∀ (w x : Fin 8 → Int), IsTwoE8Root w → InTwoE8Lattice x →
      (2 * intDot8 w x) % 8 = 0 ∧
      intDot8 w x % 4 = 0 ∧
      InTwoE8Lattice (reflectTwoE8 w x) ∧
      intNormSq8 (reflectTwoE8 w x) = intNormSq8 x ∧
      reflectTwoE8 w (reflectTwoE8 w x) = x) := by
  sorry

/-- Theorem 6 (`non_weyl_hamming_closure_obstruction`):
    Proves that the non-Weyl `Hamming[8,4,4]` weight-4 vector `v = (1, 1, 1, 1, 0, 0, 0, 0)`
    (`‖v‖_2^2 = 4`) fails integer lattice closure under `R_v` on both `e_0` and the
    even-sum `D_8` vector `(1, 0, 0, 0, 1, 0, 0, 0)`: `2 * dot v x = 2` is not divisible
    by `4`, and the exact rational reflection produces non-integer entry `1 / 2 ∉ ℤ`. -/
theorem non_weyl_hamming_closure_obstruction :
    intNormSq8 hammingV = 4 ∧
    intDot8 hammingV hammingX = 1 ∧
    2 * intDot8 hammingV hammingX = 2 ∧
    (2 * intDot8 hammingV hammingX) % 4 = 2 ∧
    (2 * intDot8 hammingV hammingX) % 4 ≠ 0 ∧
    householderApply (2 / (4 : Rat)) (ratOfIntVec8 hammingV) (ratOfIntVec8 hammingX) ⟨0, by decide⟩ = 1 / 2 ∧
    (∀ z : Int, (z : Rat) ≠
      householderApply (2 / (4 : Rat)) (ratOfIntVec8 hammingV) (ratOfIntVec8 hammingX) ⟨0, by decide⟩) ∧
    InD8Lattice hammingXEven ∧
    (2 * intDot8 hammingV hammingXEven) % 4 = 2 ∧
    (∀ z : Int, (z : Rat) ≠
      householderApply (2 / (4 : Rat)) (ratOfIntVec8 hammingV) (ratOfIntVec8 hammingXEven) ⟨0, by decide⟩) := by
  sorry

end DeltaNetHouseholderE8Challenge
