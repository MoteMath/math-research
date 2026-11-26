/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TernaryLop3Circuits

/-!
# Verified Solutions (`ternary-lop3-circuits`)
-/

namespace TernaryLop3Challenge

open TernaryLop3Circuits

theorem unpack_3t5b_sound_and_surjective :
    (∀ x : Fin 32,
      let (tr0, tr1, tr2) := unpack3t5b x
      tritDisjoint tr0 = true ∧ tritDisjoint tr1 = true ∧ tritDisjoint tr2 = true) ∧
    (∀ t0 t1 t2 : Fin 3,
      ∃ x : Fin 32, esc3t5b x = false ∧
        let (tr0, tr1, tr2) := unpack3t5b x
        tritVal tr0 = fin3ToTrit t0 ∧
        tritVal tr1 = fin3ToTrit t1 ∧
        tritVal tr2 = fin3ToTrit t2) :=
  TernaryLop3Circuits.unpack_3t5b_sound_and_surjective

theorem unpack_3t5b_six_gate_lower_bound
    (D : Fin 32 → (Bool × Bool) × (Bool × Bool) × (Bool × Bool))
    (hdisj : ∀ x : Fin 32,
      tritDisjoint (D x).1 = true ∧
      tritDisjoint (D x).2.1 = true ∧
      tritDisjoint (D x).2.2 = true)
    (hsurj : ∀ t0 t1 t2 : Fin 3, ∃ x : Fin 32,
      tritVal (D x).1 = fin3ToTrit t0 ∧
      tritVal (D x).2.1 = fin3ToTrit t1 ∧
      tritVal (D x).2.2 = fin3ToTrit t2) :
    (∀ k : Fin 6,
      9 ≤ countTrue (fun x => lane3t (D x) k) ∧
      18 ≤ countTrue (fun x => !(lane3t (D x) k))) ∧
    (∀ (k : Fin 6) (j : Fin 5) (neg : Bool),
      ¬ (∀ x : Fin 32,
        lane3t (D x) k = if neg then !(bitAt x.val j.val) else bitAt x.val j.val)) :=
  TernaryLop3Circuits.unpack_3t5b_six_gate_lower_bound D hdisj hsurj

theorem unpack_5t8b_sound_and_surjective :
    (∀ x : Fin 256,
      let (tr0, tr1, tr2, tr3, tr4) := unpack5t8b x
      tritDisjoint tr0 = true ∧ tritDisjoint tr1 = true ∧ tritDisjoint tr2 = true ∧
      tritDisjoint tr3 = true ∧ tritDisjoint tr4 = true) ∧
    (∀ t0 t1 t2 t3 t4 : Fin 3,
      ∃ x : Fin 256,
        let (tr0, tr1, tr2, tr3, tr4) := unpack5t8b x
        tritVal tr0 = fin3ToTrit t0 ∧
        tritVal tr1 = fin3ToTrit t1 ∧
        tritVal tr2 = fin3ToTrit t2 ∧
        tritVal tr3 = fin3ToTrit t3 ∧
        tritVal tr4 = fin3ToTrit t4) :=
  TernaryLop3Circuits.unpack_5t8b_sound_and_surjective

theorem unpack_5t8b_four_var_impossibility
    (D : Fin 256 → (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool))
    (hdisj : ∀ x : Fin 256,
      tritDisjoint (D x).1 = true ∧
      tritDisjoint (D x).2.1 = true ∧
      tritDisjoint (D x).2.2.1 = true ∧
      tritDisjoint (D x).2.2.2.1 = true ∧
      tritDisjoint (D x).2.2.2.2 = true)
    (hsurj : ∀ t0 t1 t2 t3 t4 : Fin 3, ∃ x : Fin 256,
      tritVal (D x).1 = fin3ToTrit t0 ∧
      tritVal (D x).2.1 = fin3ToTrit t1 ∧
      tritVal (D x).2.2.1 = fin3ToTrit t2 ∧
      tritVal (D x).2.2.2.1 = fin3ToTrit t3 ∧
      tritVal (D x).2.2.2.2 = fin3ToTrit t4) :
    (∀ k : Fin 10,
      81 ≤ countTrue (fun x => lane5t (D x) k) ∧
      162 ≤ countTrue (fun x => !(lane5t (D x) k))) ∧
    (∀ k : Fin 10, ¬ DependsOnAtMost4 (fun x => lane5t (D x) k)) :=
  TernaryLop3Circuits.unpack_5t8b_four_var_impossibility D hdisj hsurj

theorem ternary_int4_exact5_sound (p n a0 a1 a2 a3 : Bool)
    (hdisj : tritDisjoint (p, n) = true) :
    let (y0, y1, y2, y3, y4) := ternaryInt4Exact5 p n a0 a1 a2 a3
    boolToInt y0 + 2 * boolToInt y1 + 4 * boolToInt y2 + 8 * boolToInt y3 + 16 * boolToInt y4 =
      tritVal (p, n) * int4Signed a0 a1 a2 a3 + 8 ∧
    (int4Signed a0 a1 a2 a3 ≠ -8 → y4 = false) :=
  TernaryLop3Circuits.ternary_int4_exact5_sound p n a0 a1 a2 a3 hdisj

theorem ternary_fp4_exact5_sound (p n s e1 e0 m0 : Bool)
    (hdisj : tritDisjoint (p, n) = true) :
    let (y0, y1, y2, y3, t4) := ternaryFp4Exact5 p n s e1 e0 m0
    boolToInt y0 + 2 * boolToInt y1 + 4 * boolToInt y2 + 8 * boolToInt y3 - 16 * boolToInt t4 =
      tritVal (p, n) * fp4Scaled2 s e1 e0 m0 :=
  TernaryLop3Circuits.ternary_fp4_exact5_sound p n s e1 e0 m0 hdisj

theorem csa32_popcnt_conservation (a b c : Nat) :
    popcnt a + popcnt b + popcnt c =
      popcnt (a ^^^ b ^^^ c) + 2 * popcnt ((a &&& b) ||| (b &&& c) ||| (a &&& c)) :=
  TernaryLop3Circuits.csa32_popcnt_conservation a b c

end TernaryLop3Challenge
