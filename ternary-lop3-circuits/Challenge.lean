/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TernaryLop3Circuits.Defs

/-!
# Trusted Challenge Statements (`ternary-lop3-circuits`)

Statements of the seven headline theorems for minimal-`LOP3` packed ternary bit-plane circuits:
1. Soundness and escape-cube surjectivity of the 6-`LOP3` depth-2 3-trit / 5-bit decoder.
2. Exact 6-gate information-theoretic lower bound for any surjective disjoint 3-trit / 5-bit decoder.
3. Soundness and 243/243 surjectivity of the 14-`LOP3` depth-4 5-trit / 8-bit escape-cube decoder.
4. Pigeonhole 4-variable support impossibility for any surjective disjoint 5-trit / 8-bit decoder.
5. Exactness of the 9-`LOP3` ternary × signed INT4 `[-8, 7]` (and 8-`LOP3` symmetric `[-7, 7]`) circuit.
6. Exactness of the 4+10-`LOP3` ternary × FP4 (E2M1) zero-offset, zero-FP-op circuit.
7. Universal 3:2 Carry-Save-Adder `popcnt` conservation over all `a b c : Nat`.
-/

namespace TernaryLop3Challenge

open TernaryLop3Circuits

/-- Theorem 1 (6-`LOP3` depth-2 3-trit / 5-bit soundness and escape-cube surjectivity):
every 5-bit input has zero invalid `(true, true)` lanes, and all 27 ternary triples are hit
outside the 4-codeword escape cube `x0 && !x1 && x3`. -/
theorem unpack_3t5b_sound_and_surjective :
    (∀ x : Fin 32,
      let (tr0, tr1, tr2) := unpack3t5b x
      tritDisjoint tr0 = true ∧ tritDisjoint tr1 = true ∧ tritDisjoint tr2 = true) ∧
    (∀ t0 t1 t2 : Fin 3,
      ∃ x : Fin 32, esc3t5b x = false ∧
        let (tr0, tr1, tr2) := unpack3t5b x
        tritVal tr0 = fin3ToTrit t0 ∧
        tritVal tr1 = fin3ToTrit t1 ∧
        tritVal tr2 = fin3ToTrit t2) := by
  sorry

/-- Theorem 2 (Exact 6-gate information-theoretic lower bound for 3-trit / 5-bit decoders):
for ANY disjoint decoder `D : Fin 32 → (Bool × Bool)^3` hitting all 27 ternary triples,
every one of the 6 output lanes `p0, n0, p1, n1, p2, n2` is `true` on at least 9 inputs and
`false` on at least 18 inputs, so no output lane can equal any input bit `x_j` or its negation `!x_j`. -/
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
        lane3t (D x) k = if neg then !(bitAt x.val j.val) else bitAt x.val j.val)) := by
  sorry

/-- Theorem 3 (14-`LOP3` depth-4 5-trit / 8-bit soundness and surjectivity):
every 8-bit input has zero invalid `(true, true)` lanes, and all 243 ternary 5-tuples are hit. -/
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
        tritVal tr4 = fin3ToTrit t4) := by
  sorry

/-- Theorem 4 (Exact pigeonhole 4-variable impossibility for 5-trit / 8-bit decoders):
for ANY disjoint decoder `D : Fin 256 → (Bool × Bool)^5` hitting all 243 ternary 5-tuples,
every one of the 10 output lanes is `true` on at least 81 inputs and `false` on at least 162 inputs,
so NO output lane can depend on at most 4 of the 8 input bits (since `80 < 81` and `94 < 96`). -/
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
    (∀ k : Fin 10, ¬ DependsOnAtMost4 (fun x => lane5t (D x) k)) := by
  sorry

/-- Theorem 5 (Exact 9-`LOP3` Ternary × Signed INT4 `[-8, 7]` product):
for every disjoint ternary weight `(p, n)` and 4-bit two's-complement integer `(a0, a1, a2, a3)`,
`y0 + 2*y1 + 4*y2 + 8*y3 + 16*y4 = w * x + 8`, and `y4 = false` whenever `x ≠ -8`. -/
theorem ternary_int4_exact5_sound (p n a0 a1 a2 a3 : Bool)
    (hdisj : tritDisjoint (p, n) = true) :
    let (y0, y1, y2, y3, y4) := ternaryInt4Exact5 p n a0 a1 a2 a3
    boolToInt y0 + 2 * boolToInt y1 + 4 * boolToInt y2 + 8 * boolToInt y3 + 16 * boolToInt y4 =
      tritVal (p, n) * int4Signed a0 a1 a2 a3 + 8 ∧
    (int4Signed a0 a1 a2 a3 ≠ -8 → y4 = false) := by
  sorry

/-- Theorem 6 (Exact 4+10-`LOP3` Ternary × FP4 E2M1 product):
for every disjoint ternary weight `(p, n)` and FP4 (E2M1) code `(s, e1, e0, m0)`,
`y0 + 2*y1 + 4*y2 + 8*y3 - 16*t4 = w * fp4Scaled2(s, e1, e0, m0)` with zero offset and zero FP ops. -/
theorem ternary_fp4_exact5_sound (p n s e1 e0 m0 : Bool)
    (hdisj : tritDisjoint (p, n) = true) :
    let (y0, y1, y2, y3, t4) := ternaryFp4Exact5 p n s e1 e0 m0
    boolToInt y0 + 2 * boolToInt y1 + 4 * boolToInt y2 + 8 * boolToInt y3 - 16 * boolToInt t4 =
      tritVal (p, n) * fp4Scaled2 s e1 e0 m0 := by
  sorry

/-- Theorem 7 (Universal 3:2 Carry-Save-Adder `popcnt` conservation over all `Nat`):
for all `a b c : Nat`,
`popcnt a + popcnt b + popcnt c = popcnt (a ^^^ b ^^^ c) + 2 * popcnt ((a &&& b) ||| (b &&& c) ||| (a &&& c))`. -/
theorem csa32_popcnt_conservation (a b c : Nat) :
    popcnt a + popcnt b + popcnt c =
      popcnt (a ^^^ b ^^^ c) + 2 * popcnt ((a &&& b) ||| (b &&& c) ||| (a &&& c)) := by
  sorry

end TernaryLop3Challenge
