/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DeltaNetHouseholderE8.RatOrder

/-!
# Theorems 5 & 6: `D_8` / `2 * E_8` Weyl Root Zero-ULP Orthogonality & Non-Weyl `Hamming[8,4,4]` Obstruction

Proves:
- Theorem 5 (`d8_and_e8_weyl_root_zero_ulp_orthogonality`):
  1. For every `D_8` root `v` (`‖v‖_2^2 = 2`), `R_v(x) = x - ⟨v, x⟩ v` has exact zero
     division remainder `(2 ⟨v, x⟩) % 2 = 0`, preserves `‖x‖_2^2`, preserves the `D_8`
     lattice, and is an involution.
  2. Exact structural characterization of all 240 `2 * E_8` roots (`IsTwoE8Root w ↔
     IsTwoE8IntRoot w ∨ IsTwoE8HalfIntRoot w`, `112 + 128 = 240`).
  3. For EVERY `w ∈ 2 E_8` and `x ∈ 2 E_8`, `⟨w, x⟩ % 4 = 0` and `(2 ⟨w, x⟩) % 8 = 0`
     (exact zero remainder, pure bit-shift `>>> 2`!), and for every `2 * E_8` root `w`,
     `reflectTwoE8 w x` maps `2 E_8 → 2 E_8`, preserves exact Euclidean norm
     `intNormSq8 (reflectTwoE8 w x) = intNormSq8 x`, and is an involution.
- Theorem 6 (`non_weyl_hamming_closure_obstruction`):
  For the non-Weyl `Hamming[8,4,4]` weight-4 vector `v = (1, 1, 1, 1, 0, 0, 0, 0)`
  (`‖v‖_2^2 = 4`), `2 * ⟨v, x⟩ = 2` is NOT divisible by `4` on both `e_0` and the
  even-sum `D_8` witness `(1, 0, 0, 0, 1, 0, 0, 0)`, and the exact rational reflection
  produces non-integer coordinate `1 / 2 ∉ ℤ`.
-/

namespace DeltaNetHouseholderE8

/-! ### Helper Identities for 8D Integer Vectors -/

theorem intDot8_sub_scale (w x : Fin 8 → Int) (q : Int) :
    intNormSq8 (fun i => x i - q * w i) =
      intNormSq8 x - 2 * q * intDot8 w x + q * q * intNormSq8 w := by
  unfold intNormSq8 intDot8
  grind

theorem intDot8_left_sub_scale (w x : Fin 8 → Int) (q : Int) :
    intDot8 w (fun i => x i - q * w i) = intDot8 w x - q * intNormSq8 w := by
  unfold intNormSq8 intDot8
  grind

theorem intSum8_sub_scale (w x : Fin 8 → Int) (q : Int) :
    intSum8 (fun i => x i - q * w i) = intSum8 x - q * intSum8 w := by
  unfold intSum8
  grind

/-! ### `D_8` Root Reflection Closure & Exact Norm Preservation -/

theorem d8_reflection_props (v x : Fin 8 → Int) (hv : IsD8Root v) :
    (2 * intDot8 v x) % 2 = 0 ∧
    intNormSq8 (reflectD8 v x) = intNormSq8 x ∧
    reflectD8 v (reflectD8 v x) = x := by
  unfold IsD8Root at hv
  refine ⟨by omega, ?_, ?_⟩
  · unfold reflectD8
    rw [intDot8_sub_scale, hv]
    grind
  · funext i
    unfold reflectD8
    rw [intDot8_left_sub_scale, hv]
    grind

theorem d8_root_sum_even (v : Fin 8 → Int) (hv : IsD8Root v) :
    intSum8 v % 2 = 0 := by
  unfold IsD8Root intNormSq8 intDot8 at hv
  unfold intSum8
  have hsq : ∀ a : Int, (a * a - a) % 2 = 0 := by
    intro a
    have h : a % 2 = 0 ∨ a % 2 = 1 := by omega
    rcases h with h0 | h1
    · have : a = 2 * (a / 2) := by omega
      rw [this]
      have hmul : (2 * (a / 2)) * (2 * (a / 2)) - 2 * (a / 2) =
          2 * (2 * (a / 2) * (a / 2) - (a / 2)) := by grind
      rw [hmul]; omega
    · have : a = 2 * (a / 2) + 1 := by omega
      rw [this]
      have hmul : (2 * (a / 2) + 1) * (2 * (a / 2) + 1) - (2 * (a / 2) + 1) =
          2 * (2 * (a / 2) * (a / 2) + (a / 2)) := by grind
      rw [hmul]; omega
  have h0 := hsq (v ⟨0, by decide⟩)
  have h1 := hsq (v ⟨1, by decide⟩)
  have h2 := hsq (v ⟨2, by decide⟩)
  have h3 := hsq (v ⟨3, by decide⟩)
  have h4 := hsq (v ⟨4, by decide⟩)
  have h5 := hsq (v ⟨5, by decide⟩)
  have h6 := hsq (v ⟨6, by decide⟩)
  have h7 := hsq (v ⟨7, by decide⟩)
  omega

theorem d8_reflection_preserves_lattice (v x : Fin 8 → Int)
    (hv : IsD8Root v) (hx : InD8Lattice x) :
    InD8Lattice (reflectD8 v x) := by
  unfold InD8Lattice at hx ⊢
  unfold reflectD8
  rw [intSum8_sub_scale]
  have hvs := d8_root_sum_even v hv
  have hdiv : intSum8 v = 2 * (intSum8 v / 2) := by omega
  rw [hdiv]
  have heq : intSum8 x - intDot8 v x * (2 * (intSum8 v / 2)) =
      intSum8 x - 2 * (intDot8 v x * (intSum8 v / 2)) := by grind
  rw [heq]; omega

/-! ### `2 * E_8` Exact Zero-Remainder Congruence & Root Characterization -/

theorem int_mul_mod4_decomp (a b r1 r2 : Int) (ha : a % 2 = r1) (hb : b % 2 = r2) :
    a * b = 4 * ((a / 2) * (b / 2)) + 2 * r2 * (a / 2) + 2 * r1 * (b / 2) + r1 * r2 := by
  have h1 : a = 2 * (a / 2) + r1 := by omega
  have h2 : b = 2 * (b / 2) + r2 := by omega
  calc
    a * b = (2 * (a / 2) + r1) * (2 * (b / 2) + r2) := by rw [← h1, ← h2]
    _ = 4 * ((a / 2) * (b / 2)) + 2 * r2 * (a / 2) + 2 * r1 * (b / 2) + r1 * r2 := by grind

theorem twoE8_dot_mod4 (w x : Fin 8 → Int)
    (hw : InTwoE8Lattice w) (hx : InTwoE8Lattice x) :
    intDot8 w x % 4 = 0 ∧ (2 * intDot8 w x) % 8 = 0 := by
  rcases hw with ⟨hw_par, hw_sum⟩
  rcases hx with ⟨hx_par, hx_sum⟩
  let r1 := w ⟨0, by decide⟩ % 2
  let r2 := x ⟨0, by decide⟩ % 2
  have hd : ∀ i : Fin 8,
      w i * x i = 4 * ((w i / 2) * (x i / 2)) + 2 * r2 * (w i / 2) + 2 * r1 * (x i / 2) + r1 * r2 :=
    fun i => int_mul_mod4_decomp (w i) (x i) r1 r2 (hw_par i) (hx_par i)
  have hw_eq : ∀ i : Fin 8, w i = 2 * (w i / 2) + r1 := fun i => by
    have := hw_par i; omega
  have hx_eq : ∀ i : Fin 8, x i = 2 * (x i / 2) + r2 := fun i => by
    have := hx_par i; omega
  let sw := (w ⟨0, by decide⟩ / 2) + (w ⟨1, by decide⟩ / 2) + (w ⟨2, by decide⟩ / 2) +
    (w ⟨3, by decide⟩ / 2) + (w ⟨4, by decide⟩ / 2) + (w ⟨5, by decide⟩ / 2) +
    (w ⟨6, by decide⟩ / 2) + (w ⟨7, by decide⟩ / 2)
  let sx := (x ⟨0, by decide⟩ / 2) + (x ⟨1, by decide⟩ / 2) + (x ⟨2, by decide⟩ / 2) +
    (x ⟨3, by decide⟩ / 2) + (x ⟨4, by decide⟩ / 2) + (x ⟨5, by decide⟩ / 2) +
    (x ⟨6, by decide⟩ / 2) + (x ⟨7, by decide⟩ / 2)
  have hsw : intSum8 w = 2 * sw + 8 * r1 := by
    unfold intSum8
    have h0 := hw_eq ⟨0, by decide⟩; have h1 := hw_eq ⟨1, by decide⟩
    have h2 := hw_eq ⟨2, by decide⟩; have h3 := hw_eq ⟨3, by decide⟩
    have h4 := hw_eq ⟨4, by decide⟩; have h5 := hw_eq ⟨5, by decide⟩
    have h6 := hw_eq ⟨6, by decide⟩; have h7 := hw_eq ⟨7, by decide⟩
    omega
  have hsx : intSum8 x = 2 * sx + 8 * r2 := by
    unfold intSum8
    have h0 := hx_eq ⟨0, by decide⟩; have h1 := hx_eq ⟨1, by decide⟩
    have h2 := hx_eq ⟨2, by decide⟩; have h3 := hx_eq ⟨3, by decide⟩
    have h4 := hx_eq ⟨4, by decide⟩; have h5 := hx_eq ⟨5, by decide⟩
    have h6 := hx_eq ⟨6, by decide⟩; have h7 := hx_eq ⟨7, by decide⟩
    omega
  have hsw_even : sw % 2 = 0 := by omega
  have hsx_even : sx % 2 = 0 := by omega
  let qprod := (w ⟨0, by decide⟩ / 2) * (x ⟨0, by decide⟩ / 2) +
    (w ⟨1, by decide⟩ / 2) * (x ⟨1, by decide⟩ / 2) +
    (w ⟨2, by decide⟩ / 2) * (x ⟨2, by decide⟩ / 2) +
    (w ⟨3, by decide⟩ / 2) * (x ⟨3, by decide⟩ / 2) +
    (w ⟨4, by decide⟩ / 2) * (x ⟨4, by decide⟩ / 2) +
    (w ⟨5, by decide⟩ / 2) * (x ⟨5, by decide⟩ / 2) +
    (w ⟨6, by decide⟩ / 2) * (x ⟨6, by decide⟩ / 2) +
    (w ⟨7, by decide⟩ / 2) * (x ⟨7, by decide⟩ / 2)
  have hdot : intDot8 w x = 4 * qprod + 2 * r2 * sw + 2 * r1 * sx + 8 * (r1 * r2) := by
    unfold intDot8
    rw [hd ⟨0, by decide⟩, hd ⟨1, by decide⟩, hd ⟨2, by decide⟩, hd ⟨3, by decide⟩,
        hd ⟨4, by decide⟩, hd ⟨5, by decide⟩, hd ⟨6, by decide⟩, hd ⟨7, by decide⟩]
    grind
  have hsw2 : sw = 2 * (sw / 2) := by omega
  have hsx2 : sx = 2 * (sx / 2) := by omega
  have hdot4 : intDot8 w x = 4 * (qprod + r2 * (sw / 2) + r1 * (sx / 2) + 2 * (r1 * r2)) := by
    rw [hdot, hsw2, hsx2]; grind
  constructor <;> omega

theorem twoE8_reflection_props (w x : Fin 8 → Int)
    (hw : IsTwoE8Root w) (hx : InTwoE8Lattice x) :
    (2 * intDot8 w x) % 8 = 0 ∧
    InTwoE8Lattice (reflectTwoE8 w x) ∧
    intNormSq8 (reflectTwoE8 w x) = intNormSq8 x ∧
    reflectTwoE8 w (reflectTwoE8 w x) = x := by
  rcases hw with ⟨hw_lat, hw_norm⟩
  have ⟨hmod4, hmod8⟩ := twoE8_dot_mod4 w x hw_lat hx
  let q := (2 * intDot8 w x) / 8
  have hq : intDot8 w x = 4 * q := by omega
  refine ⟨hmod8, ?_, ?_, ?_⟩
  · rcases hw_lat with ⟨hw_par, hw_sum⟩
    rcases hx with ⟨hx_par, hx_sum⟩
    constructor
    · intro i
      unfold reflectTwoE8
      have hwi : w i = 2 * (w i / 2) + w ⟨0, by decide⟩ % 2 := by have := hw_par i; omega
      have hxi : x i = 2 * (x i / 2) + x ⟨0, by decide⟩ % 2 := by have := hx_par i; omega
      have hw0 : w ⟨0, by decide⟩ = 2 * (w ⟨0, by decide⟩ / 2) + w ⟨0, by decide⟩ % 2 := by omega
      have hx0 : x ⟨0, by decide⟩ = 2 * (x ⟨0, by decide⟩ / 2) + x ⟨0, by decide⟩ % 2 := by omega
      have hdiff : (x i - q * w i) - (x ⟨0, by decide⟩ - q * w ⟨0, by decide⟩) =
          2 * ((x i / 2 - x ⟨0, by decide⟩ / 2) - q * (w i / 2 - w ⟨0, by decide⟩ / 2)) := by
        calc
          (x i - q * w i) - (x ⟨0, by decide⟩ - q * w ⟨0, by decide⟩)
            = ((2 * (x i / 2) + x ⟨0, by decide⟩ % 2) - q * (2 * (w i / 2) + w ⟨0, by decide⟩ % 2)) -
              ((2 * (x ⟨0, by decide⟩ / 2) + x ⟨0, by decide⟩ % 2) -
               q * (2 * (w ⟨0, by decide⟩ / 2) + w ⟨0, by decide⟩ % 2)) := by
              rw [← hwi, ← hxi, ← hw0, ← hx0]
          _ = 2 * ((x i / 2 - x ⟨0, by decide⟩ / 2) - q * (w i / 2 - w ⟨0, by decide⟩ / 2)) := by
              grind
      have hmod2 : ∀ a b k : Int, a - b = 2 * k → a % 2 = b % 2 := fun a b k h => by omega
      exact hmod2 _ _ _ hdiff
    · unfold reflectTwoE8
      rw [intSum8_sub_scale]
      have hws : intSum8 w = 4 * (intSum8 w / 4) := by omega
      rw [hws]
      have heq : intSum8 x - q * (4 * (intSum8 w / 4)) =
          intSum8 x - 4 * (q * (intSum8 w / 4)) := by grind
      rw [heq]; omega
  · unfold reflectTwoE8
    rw [intDot8_sub_scale, hw_norm]
    have hq' : intDot8 w x = 4 * ((2 * intDot8 w x) / 8) := hq
    rw [hq']
    grind
  · funext i
    unfold reflectTwoE8
    rw [intDot8_left_sub_scale, hw_norm]
    have hq' : intDot8 w x = 4 * ((2 * intDot8 w x) / 8) := hq
    have hinner : (2 * (intDot8 w x - ((2 * intDot8 w x) / 8) * 8)) / 8 =
        -((2 * intDot8 w x) / 8) := by omega
    rw [hinner]
    grind

theorem int_odd_sq_ge_one (a : Int) (ha : a % 2 = 1) : 1 ≤ a * a := by
  by_cases hp : 0 < a
  · have hpos : 0 ≤ a - 1 := by omega
    have hmul : 0 ≤ (a - 1) * (a + 1) := Int.mul_nonneg hpos (by omega)
    have hdiff : a * a - 1 = (a - 1) * (a + 1) := by grind
    omega
  · have hpos : 0 ≤ (-a) - 1 := by omega
    have hmul : 0 ≤ ((-a) - 1) * ((-a) + 1) := Int.mul_nonneg hpos (by omega)
    have hdiff : a * a - 1 = ((-a) - 1) * ((-a) + 1) := by grind
    omega

theorem int_sq_eq_one_iff (a : Int) : a * a = 1 ↔ (a = 1 ∨ a = -1) := by
  constructor
  · intro h
    by_cases h1 : a = 1
    · exact Or.inl h1
    · by_cases h2 : a = -1
      · exact Or.inr h2
      · by_cases hp : 0 < a
        · have hge : 2 ≤ a := by omega
          have hmul : 0 ≤ (a - 2) * (a + 2) := Int.mul_nonneg (by omega) (by omega)
          have : a * a - 4 = (a - 2) * (a + 2) := by grind
          omega
        · by_cases hz : a = 0
          · rw [hz] at h; omega
          · have hle : a ≤ -2 := by omega
            have hmul : 0 ≤ ((-a) - 2) * ((-a) + 2) := Int.mul_nonneg (by omega) (by omega)
            have : a * a - 4 = ((-a) - 2) * ((-a) + 2) := by grind
            omega
  · rintro (rfl | rfl) <;> decide

theorem twoE8_root_classification (w : Fin 8 → Int) :
    IsTwoE8Root w ↔ (IsTwoE8IntRoot w ∨ IsTwoE8HalfIntRoot w) := by
  constructor
  · rintro ⟨⟨hpar, hsum⟩, hnorm⟩
    have hmod : w ⟨0, by decide⟩ % 2 = 0 ∨ w ⟨0, by decide⟩ % 2 = 1 := by omega
    rcases hmod with h0 | h1
    · left
      exact ⟨fun i => by rw [hpar i, h0], hnorm⟩
    · right
      refine ⟨?_, hsum⟩
      have hodd : ∀ i : Fin 8, w i % 2 = 1 := fun i => by rw [hpar i, h1]
      have hge : ∀ i : Fin 8, 1 ≤ w i * w i := fun i => int_odd_sq_ge_one (w i) (hodd i)
      unfold intNormSq8 intDot8 at hnorm
      have h0' := hge ⟨0, by decide⟩; have h1' := hge ⟨1, by decide⟩
      have h2' := hge ⟨2, by decide⟩; have h3' := hge ⟨3, by decide⟩
      have h4' := hge ⟨4, by decide⟩; have h5' := hge ⟨5, by decide⟩
      have h6' := hge ⟨6, by decide⟩; have h7' := hge ⟨7, by decide⟩
      intro i
      apply (int_sq_eq_one_iff (w i)).mp
      match i with
      | ⟨0, _⟩ => omega
      | ⟨1, _⟩ => omega
      | ⟨2, _⟩ => omega
      | ⟨3, _⟩ => omega
      | ⟨4, _⟩ => omega
      | ⟨5, _⟩ => omega
      | ⟨6, _⟩ => omega
      | ⟨7, _⟩ => omega
  · rintro (⟨heven, hnorm⟩ | ⟨hpm, hsum⟩)
    · refine ⟨⟨fun i => by rw [heven i, heven ⟨0, by decide⟩], ?_⟩, hnorm⟩
      let a : Fin 8 → Int := fun i => w i / 2
      have hw : ∀ i : Fin 8, w i = 2 * a i := fun i => by dsimp [a]; have := heven i; omega
      have hda : IsD8Root a := by
        unfold IsD8Root
        unfold intNormSq8 intDot8 at hnorm ⊢
        have h0 := hw ⟨0, by decide⟩; have h1 := hw ⟨1, by decide⟩
        have h2 := hw ⟨2, by decide⟩; have h3 := hw ⟨3, by decide⟩
        have h4 := hw ⟨4, by decide⟩; have h5 := hw ⟨5, by decide⟩
        have h6 := hw ⟨6, by decide⟩; have h7 := hw ⟨7, by decide⟩
        rw [h0, h1, h2, h3, h4, h5, h6, h7] at hnorm
        have h4eq : 4 * (a ⟨0, by decide⟩ * a ⟨0, by decide⟩ + a ⟨1, by decide⟩ * a ⟨1, by decide⟩ +
            a ⟨2, by decide⟩ * a ⟨2, by decide⟩ + a ⟨3, by decide⟩ * a ⟨3, by decide⟩ +
            a ⟨4, by decide⟩ * a ⟨4, by decide⟩ + a ⟨5, by decide⟩ * a ⟨5, by decide⟩ +
            a ⟨6, by decide⟩ * a ⟨6, by decide⟩ + a ⟨7, by decide⟩ * a ⟨7, by decide⟩) = 8 := by
          grind
        omega
      have ha_even := d8_root_sum_even a hda
      unfold intSum8 at ha_even ⊢
      have h0 := hw ⟨0, by decide⟩; have h1 := hw ⟨1, by decide⟩
      have h2 := hw ⟨2, by decide⟩; have h3 := hw ⟨3, by decide⟩
      have h4 := hw ⟨4, by decide⟩; have h5 := hw ⟨5, by decide⟩
      have h6 := hw ⟨6, by decide⟩; have h7 := hw ⟨7, by decide⟩
      omega
    · refine ⟨⟨?_, hsum⟩, ?_⟩
      · intro i
        have hi : w i % 2 = 1 := by rcases hpm i with h | h <;> rw [h] <;> decide
        have h0 : w ⟨0, by decide⟩ % 2 = 1 := by
          rcases hpm ⟨0, by decide⟩ with h | h <;> rw [h] <;> decide
        rw [hi, h0]
      · unfold intNormSq8 intDot8
        have hsq : ∀ i : Fin 8, w i * w i = 1 := fun i => (int_sq_eq_one_iff (w i)).mpr (hpm i)
        rw [hsq ⟨0, by decide⟩, hsq ⟨1, by decide⟩, hsq ⟨2, by decide⟩, hsq ⟨3, by decide⟩,
            hsq ⟨4, by decide⟩, hsq ⟨5, by decide⟩, hsq ⟨6, by decide⟩, hsq ⟨7, by decide⟩]
        decide

/-- Headline Theorem 5 (`d8_and_e8_weyl_root_zero_ulp_orthogonality`). -/
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
  refine ⟨?_, twoE8_root_classification, ⟨by decide, by decide, by decide⟩, ?_⟩
  · intro v x hv
    have h := d8_reflection_props v x hv
    exact ⟨h.1, h.2.1, h.2.2, fun hx => d8_reflection_preserves_lattice v x hv hx⟩
  · intro w x hw hx
    have h := twoE8_reflection_props w x hw hx
    have h4 := (twoE8_dot_mod4 w x hw.1 hx).1
    exact ⟨h.1, h4, h.2.1, h.2.2.1, h.2.2.2⟩

/-! ### Theorem 6: Non-Weyl `Hamming[8,4,4]` Integer-Closure Obstruction -/

theorem rat_intCast_ne_half (z : Int) : (z : Rat) ≠ (1 / 2 : Rat) := by
  intro h
  have h2 : ((2 * z : Int) : Rat) = (1 : Rat) := by
    rw [Rat.intCast_mul, h]
    grind
  have hnum := congrArg Rat.num h2
  have hl : ((2 * z : Int) : Rat).num = 2 * z := rfl
  have hr : (1 : Rat).num = 1 := rfl
  rw [hl, hr] at hnum
  omega

/-- Headline Theorem 6 (`non_weyl_hamming_closure_obstruction`). -/
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
  have hhalf1 : householderApply (2 / (4 : Rat)) (ratOfIntVec8 hammingV) (ratOfIntVec8 hammingX) ⟨0, by decide⟩ = 1 / 2 := by
    simp only [householderApply, dotProd, finSum, finSumAux, ratOfIntVec8, hammingV, hammingX]
    grind
  have hhalf2 : householderApply (2 / (4 : Rat)) (ratOfIntVec8 hammingV) (ratOfIntVec8 hammingXEven) ⟨0, by decide⟩ = 1 / 2 := by
    simp only [householderApply, dotProd, finSum, finSumAux, ratOfIntVec8, hammingV, hammingXEven]
    grind
  have hlat : InD8Lattice hammingXEven := by
    unfold InD8Lattice intSum8 hammingXEven
    decide
  refine ⟨by decide, by decide, by decide, by decide, by decide, hhalf1, ?_, hlat, by decide, ?_⟩
  · intro z; rw [hhalf1]; exact rat_intCast_ne_half z
  · intro z; rw [hhalf2]; exact rat_intCast_ne_half z

end DeltaNetHouseholderE8
