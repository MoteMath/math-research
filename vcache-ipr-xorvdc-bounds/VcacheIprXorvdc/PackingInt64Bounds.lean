/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VcacheIprXorvdc.RatHelpers

/-!
# Theorem 6: Sub-4-Bit V-Cache Packing Density & Exact `int64` Accumulator Bounds

Pure-`Init` (zero Mathlib, zero `native_decide`) proofs of:
- Exact `128K`-context (`H = 32, L = 131072, D = 128`) V-cache VRAM footprints
  (`1024 MiB` INT16, `256 MiB` INT4, `128 MiB` INT2, `112 MiB` Ternary 5-trit/B)
  and exact compression ratios `1 : 4 : 8 : 64/7` (`64/7 > 9.14`).
- Exact lossless base-3 packing of 5 ternary trits into 1 byte (`3^5 = 243 < 256`) with
  exact `unpack5Trits (pack5Trits ...) = (...)` round-trip identity.
- Exact universal simplex and unconstrained `P * V` integer dot-product bounds and
  zero-overflow `int64` (`[-2^63, 2^63 - 1]`) guarantees for `128K` `INT16` and scaled
  `INT4`/`INT2`/`Ternary` decode kernels.
-/

namespace VcacheIprXorvdc

theorem pack5Trits_lt (t0 t1 t2 t3 t4 : Fin 3) :
    pack5Trits t0 t1 t2 t3 t4 < 243 := by
  unfold pack5Trits
  omega

theorem unpack5Trits_pack5Trits (t0 t1 t2 t3 t4 : Fin 3) :
    unpack5Trits (pack5Trits t0 t1 t2 t3 t4) = (t0, t1, t2, t3, t4) := by
  unfold unpack5Trits pack5Trits
  have h0 : t0.val < 3 := t0.isLt
  have h1 : t1.val < 3 := t1.isLt
  have h2 : t2.val < 3 := t2.isLt
  have h3 : t3.val < 3 := t3.isLt
  have h4 : t4.val < 3 := t4.isLt
  ext <;> dsimp <;> omega

theorem int_mul_abs_bound {p v vmax : Int} (hp : 0 ≤ p) (hv1 : -vmax ≤ v) (hv2 : v ≤ vmax) :
    -(p * vmax) ≤ p * v ∧ p * v ≤ p * vmax := by
  have h1 : 0 ≤ p * (v + vmax) := Int.mul_nonneg hp (by omega)
  have h2 : 0 ≤ p * (vmax - v) := Int.mul_nonneg hp (by omega)
  have eq1 : p * (v + vmax) = p * v + p * vmax := by grind
  have eq2 : p * (vmax - v) = p * vmax - p * v := by grind
  omega

theorem int_mul_box_bound {p v pmax vmax : Int}
    (hp1 : -pmax ≤ p) (hp2 : p ≤ pmax) (hv1 : -vmax ≤ v) (hv2 : v ≤ vmax) :
    -(pmax * vmax) ≤ p * v ∧ p * v ≤ pmax * vmax := by
  by_cases hp : 0 ≤ p
  · have h1 := int_mul_abs_bound hp hv1 hv2
    have hvmax : 0 ≤ vmax := by omega
    have hle : p * vmax ≤ pmax * vmax := by
      have hsub : 0 ≤ (pmax - p) * vmax := Int.mul_nonneg (by omega) hvmax
      have eq : (pmax - p) * vmax = pmax * vmax - p * vmax := by grind
      omega
    omega
  · have hnp : 0 ≤ -p := by omega
    have h1 := int_mul_abs_bound hnp (v := -v) (vmax := vmax) (by omega) (by omega)
    have hprod : (-p) * (-v) = p * v := by grind
    have hvmax : 0 ≤ vmax := by omega
    have hle : (-p) * vmax ≤ pmax * vmax := by
      have hsub : 0 ≤ (pmax - (-p)) * vmax := Int.mul_nonneg (by omega) hvmax
      have eq : (pmax - (-p)) * vmax = pmax * vmax - (-p) * vmax := by grind
      omega
    omega

theorem simplex_dot_int_bound {L : Nat} (P V : Fin L → Int) (SP Vmax : Int)
    (hP_nonneg : ∀ j, 0 ≤ P j) (hP_sum : finSumInt P = SP)
    (hV_bound : ∀ j, -Vmax ≤ V j ∧ V j ≤ Vmax) :
    -(SP * Vmax) ≤ finSumInt (fun j => P j * V j) ∧
    finSumInt (fun j => P j * V j) ≤ SP * Vmax := by
  have hb := finSumInt_le_bound (fun j => P j * V j) (fun j => P j * Vmax) (fun j =>
    int_mul_abs_bound (hP_nonneg j) (hV_bound j).1 (hV_bound j).2)
  rw [finSumInt_mul_right, hP_sum] at hb
  exact hb

theorem box_dot_int_bound {L : Nat} (P V : Fin L → Int) (Pmax Vmax : Int)
    (hP_bound : ∀ j, -Pmax ≤ P j ∧ P j ≤ Pmax)
    (hV_bound : ∀ j, -Vmax ≤ V j ∧ V j ≤ Vmax) :
    -((L : Int) * (Pmax * Vmax)) ≤ finSumInt (fun j => P j * V j) ∧
    finSumInt (fun j => P j * V j) ≤ (L : Int) * (Pmax * Vmax) := by
  have hb := finSumInt_le_bound (fun j => P j * V j) (fun _ => Pmax * Vmax) (fun j =>
    int_mul_box_bound (hP_bound j).1 (hP_bound j).2 (hV_bound j).1 (hV_bound j).2)
  rw [finSumInt_const] at hb
  exact hb

/-! ### Headline Theorem 6 (`sub4bit_vcache_packing_density_and_exact_int64_bounds`) -/

theorem sub4bit_vcache_packing_density_and_exact_int64_bounds :
    (vcacheMiB vcacheBytesPerTokenInt16 = 1024 ∧
     vcacheMiB vcacheBytesPerTokenInt4 = 256 ∧
     vcacheMiB vcacheBytesPerTokenInt2 = 128 ∧
     vcacheMiB vcacheBytesPerTokenTernary = 112 ∧
     ((vcacheMiB vcacheBytesPerTokenInt16 : Rat) / (vcacheMiB vcacheBytesPerTokenInt4 : Rat) = 4) ∧
     ((vcacheMiB vcacheBytesPerTokenInt16 : Rat) / (vcacheMiB vcacheBytesPerTokenInt2 : Rat) = 8) ∧
     ((vcacheMiB vcacheBytesPerTokenInt16 : Rat) / (vcacheMiB vcacheBytesPerTokenTernary : Rat) = 64 / 7) ∧
     (914 / 100 : Rat) < (64 / 7 : Rat)) ∧
    ((3 ^ 5 : Nat) = 243 ∧ 243 < 256 ∧ 26 * 5 = 130 ∧ vcacheHeadDim ≤ 26 * 5 ∧
     7 * 4 = vcacheBytesPerTokenTernary ∧
     ∀ t0 t1 t2 t3 t4 : Fin 3,
       pack5Trits t0 t1 t2 t3 t4 < 243 ∧
       unpack5Trits (pack5Trits t0 t1 t2 t3 t4) = (t0, t1, t2, t3, t4)) ∧
    (∀ (L : Nat) (P V : Fin L → Int) (SP Vmax : Int),
      (∀ j, 0 ≤ P j) → finSumInt P = SP →
      (∀ j, -Vmax ≤ V j ∧ V j ≤ Vmax) →
      -(SP * Vmax) ≤ finSumInt (fun j => P j * V j) ∧
      finSumInt (fun j => P j * V j) ≤ SP * Vmax) ∧
    (∀ (L : Nat) (P V : Fin L → Int) (Pmax Vmax : Int),
      (∀ j, -Pmax ≤ P j ∧ P j ≤ Pmax) →
      (∀ j, -Vmax ≤ V j ∧ V j ≤ Vmax) →
      -((L : Int) * (Pmax * Vmax)) ≤ finSumInt (fun j => P j * V j) ∧
      finSumInt (fun j => P j * V j) ≤ (L : Int) * (Pmax * Vmax)) ∧
    (∀ (P V : Fin vcacheCtx128K → Int),
      (∀ j, -(2 ^ 20 : Int) ≤ P j ∧ P j ≤ (2 ^ 20 : Int)) →
      (∀ j, -(7 * (2 ^ 20 : Int)) ≤ V j ∧ V j ≤ 7 * (2 ^ 20 : Int)) →
      int64Min < finSumInt (fun j => P j * V j) ∧
      finSumInt (fun j => P j * V j) < int64Max) ∧
    (((2 ^ 20 : Int) * (2 ^ 15 : Int) < int64Max) ∧
     ((vcacheCtx128K : Int) * ((2 ^ 20 : Int) * (2 ^ 15 : Int)) < int64Max) ∧
     ((vcacheCtx128K : Int) * ((2 ^ 20 : Int) * (7 * (2 ^ 20 : Int))) < int64Max)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨by decide, by decide, by decide, by decide,
            by simp [vcacheMiB, vcacheHeads, vcacheCtx128K, vcacheBytesPerTokenInt16, vcacheBytesPerTokenInt4]; grind,
            by simp [vcacheMiB, vcacheHeads, vcacheCtx128K, vcacheBytesPerTokenInt16, vcacheBytesPerTokenInt2]; grind,
            by simp [vcacheMiB, vcacheHeads, vcacheCtx128K, vcacheBytesPerTokenInt16, vcacheBytesPerTokenTernary]; grind,
            by grind⟩
  · refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
    intro t0 t1 t2 t3 t4
    exact ⟨pack5Trits_lt t0 t1 t2 t3 t4, unpack5Trits_pack5Trits t0 t1 t2 t3 t4⟩
  · intro L P V SP Vmax hP hsum hV
    exact simplex_dot_int_bound P V SP Vmax hP hsum hV
  · intro L P V Pmax Vmax hP hV
    exact box_dot_int_bound P V Pmax Vmax hP hV
  · intro P V hP hV
    have hb := box_dot_int_bound P V (2 ^ 20 : Int) (7 * (2 ^ 20 : Int)) hP hV
    have hhi : (vcacheCtx128K : Int) * ((2 ^ 20 : Int) * (7 * (2 ^ 20 : Int))) < int64Max := by decide
    have hlo : int64Min < -((vcacheCtx128K : Int) * ((2 ^ 20 : Int) * (7 * (2 ^ 20 : Int)))) := by decide
    omega
  · refine ⟨by decide, by decide, by decide⟩

end VcacheIprXorvdc
