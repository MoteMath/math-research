/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EmbedZipfLazyStamp.RatOrder

/-!
# Theorem 5: Exact Lazy-Stamp Memory-Bandwidth & FLOP Work Speedup

Pure-`Init` exact rational complexity proofs:
1. Universal exact memory-traffic and FLOP speedup `V / U` per step and over `T` steps
   for any `V, U, d, bRow, fRow, T > 0`.
2. Exact memory-traffic savings fraction `1 - U / V` whenever `U ≤ V`.
3. Exact `V = 131,072` (`128K`) instantiations:
   - `32×` exact speedup at `U = 4,096` (`96.875% = 31/32` traffic saved;
     `6,442,450,944` dense bytes vs `201,326,592` lazy bytes at `d = 4096, bRow = 12`),
   - `≥ 25×` speedup for all `0 < U ≤ 5,242`.
-/

namespace EmbedZipfLazyStamp

theorem ratio_cancel_right (V U c : Nat) (hU : 0 < U) (hc : 0 < c) :
    ((V * c : Nat) : Rat) / ((U * c : Nat) : Rat) = (V : Rat) / (U : Rat) := by
  have hUc_ne : ((U * c : Nat) : Rat) ≠ 0 := Rat.ne_of_gt (rat_natCast_pos (Nat.mul_pos hU hc))
  have hU_ne : (U : Rat) ≠ 0 := Rat.ne_of_gt (rat_natCast_pos hU)
  rw [rat_div_eq_iff hUc_ne, Rat.natCast_mul, Rat.natCast_mul]
  have hmul : (V : Rat) / (U : Rat) * ((U : Rat) * (c : Rat)) =
      ((V : Rat) / (U : Rat) * (U : Rat)) * (c : Rat) := by grind
  rw [hmul, rat_div_mul_cancel hU_ne]

theorem bandwidth_savings_fraction (V U c : Nat) (hV : 0 < V) (hc : 0 < c) (hUV : U ≤ V) :
    (((V * c - U * c : Nat) : Rat)) / ((V * c : Nat) : Rat) = 1 - (U : Rat) / (V : Rat) := by
  have hVc_ne : ((V * c : Nat) : Rat) ≠ 0 := Rat.ne_of_gt (rat_natCast_pos (Nat.mul_pos hV hc))
  have hV_ne : (V : Rat) ≠ 0 := Rat.ne_of_gt (rat_natCast_pos hV)
  have hsub_nat : V * c - U * c = (V - U) * c := (Nat.sub_mul V U c).symm
  rw [hsub_nat, ratio_cancel_right (V - U) V c hV hc]
  rw [rat_div_eq_iff hV_ne]
  have hmul : (1 - (U : Rat) / (V : Rat)) * (V : Rat) =
      (V : Rat) - ((U : Rat) / (V : Rat)) * (V : Rat) := by grind
  rw [hmul, rat_div_mul_cancel hV_ne]
  have hcast : ((V - U : Nat) : Rat) + (U : Rat) = (V : Rat) := by
    rw [← Rat.natCast_add, Nat.sub_add_cancel hUV]
  grind

/-- Headline Theorem 5 (`lazy_stamp_bandwidth_and_work_speedup_exact`):
    Exact rational work-complexity theorem proving that for vocabulary size `V` and
    `U` unique active tokens per step (`0 < U`), Lazy-Stamp AdamW achieves exact
    memory-traffic and FLOP speedup `V / U` (both per step and over `T` steps),
    exact traffic reduction fraction `1 - U / V`, exact `32×` speedup at `V = 131,072, U = 4,096`
    (`6,442,450,944` vs `201,326,592` bytes at `d = 4096, bRow = 12`), and `≥ 25×` speedup
    for all `0 < U ≤ 5,242`. -/
theorem lazy_stamp_bandwidth_and_work_speedup_exact :
    (∀ (V U d bRow fRow T : Nat), 0 < U → 0 < d → 0 < bRow → 0 < fRow → 0 < T →
      (denseBytes V d bRow : Rat) / (lazyBytes U d bRow : Rat) = (V : Rat) / (U : Rat) ∧
      (denseFlops V d fRow : Rat) / (lazyFlops U d fRow : Rat) = (V : Rat) / (U : Rat) ∧
      ((T * denseBytes V d bRow : Nat) : Rat) / ((T * lazyBytes U d bRow : Nat) : Rat) =
        (V : Rat) / (U : Rat)) ∧
    (∀ (V U d bRow : Nat), 0 < V → 0 < d → 0 < bRow → U ≤ V →
      ((denseBytes V d bRow - lazyBytes U d bRow : Nat) : Rat) / (denseBytes V d bRow : Rat) =
        1 - (U : Rat) / (V : Rat)) ∧
    ((denseBytes 131072 4096 12 = 6442450944) ∧
     (lazyBytes 4096 4096 12 = 201326592) ∧
     ((131072 : Rat) / 4096 = 32) ∧
     ((1 : Rat) - (4096 : Rat) / 131072 = 31 / 32)) ∧
    (∀ U : Nat, 0 < U → U ≤ 5242 → (25 : Rat) ≤ (131072 : Rat) / (U : Rat)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro V U d bRow fRow T hU hd hb hf hT
    have hdb : 0 < d * bRow := Nat.mul_pos hd hb
    have hdf : 0 < d * fRow := Nat.mul_pos hd hf
    have hTdb : 0 < T * (d * bRow) := Nat.mul_pos hT hdb
    refine ⟨?_, ?_, ?_⟩
    · unfold denseBytes lazyBytes
      rw [Nat.mul_assoc V d bRow, Nat.mul_assoc U d bRow]
      exact ratio_cancel_right V U (d * bRow) hU hdb
    · unfold denseFlops lazyFlops
      rw [Nat.mul_assoc V d fRow, Nat.mul_assoc U d fRow]
      exact ratio_cancel_right V U (d * fRow) hU hdf
    · unfold denseBytes lazyBytes
      have h1 : T * (V * d * bRow) = V * (T * (d * bRow)) := by
        rw [Nat.mul_assoc V d bRow, Nat.mul_left_comm]
      have h2 : T * (U * d * bRow) = U * (T * (d * bRow)) := by
        rw [Nat.mul_assoc U d bRow, Nat.mul_left_comm]
      rw [h1, h2]
      exact ratio_cancel_right V U (T * (d * bRow)) hU hTdb
  · intro V U d bRow hV hd hb hUV
    unfold denseBytes lazyBytes
    rw [Nat.mul_assoc V d bRow, Nat.mul_assoc U d bRow]
    exact bandwidth_savings_fraction V U (d * bRow) hV (Nat.mul_pos hd hb) hUV
  · refine ⟨rfl, rfl, by grind, by grind⟩
  · intro U hU hUle
    apply rat_le_div_of_mul_le (rat_natCast_pos hU)
    have h25 : (25 : Rat) * (U : Rat) = (((25 * U : Nat) : Int) : Rat) := by
      have hcast : ((25 : Nat) : Rat) * (U : Rat) = ((25 * U : Nat) : Rat) := (Rat.natCast_mul 25 U).symm
      exact hcast
    have h131 : (131072 : Rat) = (((131072 : Nat) : Int) : Rat) := rfl
    rw [h25, h131]
    exact Rat.intCast_le_intCast.mpr (by omega)

end EmbedZipfLazyStamp
