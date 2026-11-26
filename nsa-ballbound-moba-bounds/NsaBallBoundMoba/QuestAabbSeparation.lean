/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NsaBallBoundMoba.RatOrder

/-!
# Theorem 3: Ball-Bound Strictly Tighter Than Quest-AABB & Half Metadata

Proves:
1. **Exact Metadata Dominance:** For all `d ≥ 1`, Ball-Bound uses `d + 1` scalars per block
   vs Quest-AABB's `2d` scalars, with exact rational ratio `(d + 1)/(2d) = 1/2 + 1/(2d)`
   (`65/128` at `d = 64`), and strictly `d + 1 < 2d` for all `d ≥ 2`.
2. **Exact All-`d` (`d = m^2`) Geometric Separation (`√d ×` AABB Over-Estimate vs `0`-Slack
   Ball-Bound):** On the explicit integer sphere block `sphereWitnessBlock m` of `B = 2m^2 + 2`
   keys in `ℤ^(m^2)` with diagonal query `q = (1, ..., 1)`:
   - `blockSum = 0`, `‖q‖_2^2 = m^2 = d`, and `max_j (q^T k_j) = m^2 = d`.
   - `blockSqRadius = B^2 * d`, so `‖q‖_2^2 * R_b^2 = (B * d)^2`, giving **exact `0` slack**
     for Ball-Bound (`B * max_j = B * d`).
   - Every coordinate attains tight bounds `[-m, +m]`, so `Quest-AABB` gives `m * d = m^3`,
     over-estimating the exact maximum (and Ball-Bound) by exact factor `m = √d`
     (`2×` at `d = 4`, `8×` at `d = 64`, and strictly larger for all `m ≥ 2`).
-/

namespace NsaBallBoundMoba

theorem nat_cast_rat_ne_zero {n : Nat} (hn : 1 ≤ n) : (n : Rat) ≠ 0 := by
  intro h0
  cases n with
  | zero => omega
  | succ k =>
    have hpos : (0 : Rat) < ((k + 1 : Nat) : Rat) := by
      have hnn : ∀ t : Nat, (0 : Rat) ≤ (t : Rat) := by
        intro t
        induction t with
        | zero => exact Rat.le_refl
        | succ r ih =>
          have h1 : ((r + 1 : Nat) : Rat) = (r : Rat) + 1 := by grind
          rw [h1]
          exact rat_add_nonneg ih (by decide)
      have h1 : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by grind
      rw [h1]
      have hge : (1 : Rat) ≤ (k : Rat) + 1 := by
        have := rat_add_le_add (hnn k) (Rat.le_refl (a := (1 : Rat)))
        rw [Rat.zero_add] at this
        exact this
      have h01 : (0 : Rat) < (1 : Rat) := by decide
      have hle : (0 : Rat) ≤ (k : Rat) + 1 := Rat.le_trans (Rat.le_of_lt h01) hge
      have hne : (0 : Rat) ≠ (k : Rat) + 1 := by
        intro heq
        rw [← heq] at hge
        exact Rat.not_le.mpr h01 hge
      exact Rat.lt_of_le_of_ne hle hne
    exact Rat.ne_of_gt hpos h0

theorem metadata_ratio_exact (d : Nat) (hd : 1 ≤ d) :
    ((d : Rat) + 1) / (2 * (d : Rat)) = (1 / 2 : Rat) + 1 / (2 * (d : Rat)) := by
  have hd0 : (d : Rat) ≠ 0 := nat_cast_rat_ne_zero hd
  have h2d : 2 * (d : Rat) ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact absurd h (by decide)
    | inr h => exact hd0 h
  have hmul : (((d : Rat) + 1) / (2 * (d : Rat))) * (2 * (d : Rat)) =
      ((1 / 2 : Rat) + 1 / (2 * (d : Rat))) * (2 * (d : Rat)) := by
    rw [rat_div_mul_cancel h2d, Rat.add_mul, rat_div_mul_cancel h2d]
    grind
  have hsub : ((((d : Rat) + 1) / (2 * (d : Rat))) - ((1 / 2 : Rat) + 1 / (2 * (d : Rat)))) *
      (2 * (d : Rat)) = 0 := by grind
  cases Rat.mul_eq_zero.mp hsub with
  | inl h => grind
  | inr h => exact absurd h h2d

/-- Helper: sum of `sphereWitnessBlock m` over the first `2 * k + 2` keys is `0` in every coord. -/
theorem sphereWitness_sum_aux (m : Nat) (c : Fin (m * m)) :
    ∀ k : Nat, (hk : k ≤ m * m) →
      intFinSumAux (2 * k + 2)
        (fun j : Fin (2 * k + 2) =>
          sphereWitnessBlock m ⟨j.val, by have := j.isLt; omega⟩ c) = 0 := by
  intro k hk
  induction k with
  | zero =>
    simp [intFinSumAux, sphereWitnessBlock]
  | succ r ih =>
    have hr : r ≤ m * m := by omega
    change intFinSumAux ((2 * r + 2) + 2)
      (fun j : Fin ((2 * r + 2) + 2) =>
        sphereWitnessBlock m ⟨j.val, by have := j.isLt; omega⟩ c) = 0
    rw [intFinSumAux, intFinSumAux]
    have hih := ih hr
    rw [hih]
    unfold sphereWitnessBlock
    have hne0a : 2 * r + 2 ≠ 0 := by omega
    have hne1a : 2 * r + 2 ≠ 1 := by omega
    have hne0b : 2 * r + 2 + 1 ≠ 0 := by omega
    have hne1b : 2 * r + 2 + 1 ≠ 1 := by omega
    have hdiv_a : (2 * r + 2 - 2) / 2 = r := by omega
    have hdiv_b : (2 * r + 2 + 1 - 2) / 2 = r := by omega
    have hmod_a : (2 * r + 2 - 2) % 2 = 0 := by omega
    have hmod_b : (2 * r + 2 + 1 - 2) % 2 = 1 := by omega
    simp only [hne0a, hne1a, hne0b, hne1b, hdiv_a, hdiv_b, hmod_a, hmod_b, ↓reduceIte]
    by_cases hc : c.val = r
    · simp [hc]; omega
    · simp [hc]

theorem sphereWitness_blockSum_zero (m : Nat) :
    blockSum (sphereWitnessBlock m) = fun _ => 0 := by
  funext c
  unfold blockSum intFinSum
  exact sphereWitness_sum_aux m c (m * m) (Nat.le_refl _)

theorem sphereWitness_normSq (m : Nat) (j : Fin (2 * (m * m) + 2)) :
    normSqInt (sphereWitnessBlock m j) = (m * m : Int) := by
  unfold normSqInt dotInt sphereWitnessBlock
  by_cases hj0 : j.val = 0
  · simp only [hj0, ↓reduceIte]
    have h1 := intFinSum_const (m * m) (1 * 1)
    grind
  · by_cases hj1 : j.val = 1
    · simp only [hj1, ↓reduceIte]
      have h1 := intFinSum_const (m * m) ((-1) * (-1))
      grind
    · simp only [hj0, hj1, ↓reduceIte]
      have hidx : (j.val - 2) / 2 < m * m := by omega
      have hcongr : intFinSum (fun c : Fin (m * m) =>
          (if c.val = (j.val - 2) / 2 then if (j.val - 2) % 2 = 0 then (m : Int) else -(m : Int) else 0) *
          (if c.val = (j.val - 2) / 2 then if (j.val - 2) % 2 = 0 then (m : Int) else -(m : Int) else 0)) =
          intFinSum (fun c : Fin (m * m) =>
            if c.val = (j.val - 2) / 2 then (m : Int) * (m : Int) else 0) := by
        apply intFinSum_congr
        intro c
        by_cases hc : c.val = (j.val - 2) / 2
        · simp only [hc, ↓reduceIte]
          by_cases hm : (j.val - 2) % 2 = 0
          · simp [hm]
          · simp [hm]; grind
        · simp [hc]
      rw [hcongr]
      exact intFinSum_single (⟨(j.val - 2) / 2, hidx⟩ : Fin (m * m)) ((m : Int) * (m : Int))

theorem sphereWitness_blockSqRadius (m : Nat) :
    blockSqRadius (sphereWitnessBlock m) =
      ((2 * (m * m) + 2 : Nat) : Int) * ((2 * (m * m) + 2 : Nat) : Int) * (m * m : Int) := by
  let B : Nat := 2 * (m * m) + 2
  have hpt : ∀ j : Fin B,
      normSqInt (fun c => (B : Int) * sphereWitnessBlock m j c - blockSum (sphereWitnessBlock m) c) =
      (B : Int) * (B : Int) * (m * m : Int) := by
    intro j
    rw [sphereWitness_blockSum_zero m]
    have h1 : normSqInt (fun c => (B : Int) * sphereWitnessBlock m j c - 0) =
        (B : Int) * (B : Int) * normSqInt (sphereWitnessBlock m j) := by
      unfold normSqInt dotInt
      have hc : intFinSum (fun c => ((B : Int) * sphereWitnessBlock m j c - 0) *
                                    ((B : Int) * sphereWitnessBlock m j c - 0)) =
          intFinSum (fun c => ((B : Int) * (B : Int)) *
                              (sphereWitnessBlock m j c * sphereWitnessBlock m j c)) := by
        apply intFinSum_congr
        intro c
        grind
      rw [hc, intFinSum_mul_left]
    rw [h1, sphereWitness_normSq m j]
  unfold blockSqRadius
  dsimp only
  have hle : intFinMaxNonneg (fun j : Fin B =>
      normSqInt (fun c => (B : Int) * sphereWitnessBlock m j c - blockSum (sphereWitnessBlock m) c)) ≤
      (B : Int) * (B : Int) * (m * m : Int) := by
    apply intFinMaxNonneg_le
    · have h1 : 0 ≤ (B : Int) * (B : Int) := int_sq_nonneg (B : Int)
      have h2 : (0 : Int) ≤ (m : Int) * (m : Int) := int_sq_nonneg (m : Int)
      exact Int.mul_nonneg h1 h2
    · intro j
      rw [hpt j]
      exact Int.le_refl _
  have hge : (B : Int) * (B : Int) * (m * m : Int) ≤
      intFinMaxNonneg (fun j : Fin B =>
        normSqInt (fun c => (B : Int) * sphereWitnessBlock m j c - blockSum (sphereWitnessBlock m) c)) := by
    have h0 := le_intFinMaxNonneg (fun j : Fin B =>
      normSqInt (fun c => (B : Int) * sphereWitnessBlock m j c - blockSum (sphereWitnessBlock m) c))
      ⟨0, by omega⟩
    rw [hpt ⟨0, by omega⟩] at h0
    exact h0
  exact Int.le_antisymm hle hge

theorem allOnesVec_normSq (d : Nat) : normSqInt (allOnesVec d) = (d : Int) := by
  unfold normSqInt dotInt allOnesVec
  have h := intFinSum_const d (1 * 1)
  grind

theorem sphereWitness_dot_le (m : Nat) (hm : 1 ≤ m) (j : Fin (2 * (m * m) + 2)) :
    dotInt (allOnesVec (m * m)) (sphereWitnessBlock m j) ≤ (m * m : Int) := by
  unfold dotInt allOnesVec sphereWitnessBlock
  by_cases hj0 : j.val = 0
  · simp only [hj0, ↓reduceIte]
    have h := intFinSum_const (m * m) (1 * 1)
    grind
  · by_cases hj1 : j.val = 1
    · simp only [hj1, ↓reduceIte]
      have h := intFinSum_const (m * m) (1 * (-1))
      have hmm : (0 : Int) ≤ (m : Int) * (m : Int) := int_sq_nonneg (m : Int)
      grind
    · simp only [hj0, hj1, ↓reduceIte]
      have hidx : (j.val - 2) / 2 < m * m := by omega
      let sgn : Int := if (j.val - 2) % 2 = 0 then (m : Int) else -(m : Int)
      have hcongr : intFinSum (fun c : Fin (m * m) =>
          1 * (if c.val = (j.val - 2) / 2 then sgn else 0)) =
          intFinSum (fun c : Fin (m * m) =>
            if c.val = (j.val - 2) / 2 then sgn else 0) := by
        apply intFinSum_congr
        intro c
        by_cases hc : c.val = (j.val - 2) / 2 <;> simp [hc]
      rw [hcongr]
      rw [intFinSum_single (⟨(j.val - 2) / 2, hidx⟩ : Fin (m * m)) sgn]
      have hm_le_sq : (m : Int) ≤ (m * m : Int) := by
        have h1 : m * 1 ≤ m * m := Nat.mul_le_mul_left m hm
        omega
      dsimp [sgn]
      split <;> omega

theorem sphereWitness_dot_zero (m : Nat) :
    dotInt (allOnesVec (m * m)) (sphereWitnessBlock m ⟨0, by omega⟩) = (m * m : Int) := by
  unfold dotInt allOnesVec sphereWitnessBlock
  have h : intFinSum (fun _ : Fin (m * m) => (1 : Int) * (1 : Int)) = (m * m : Int) := by
    have hc := intFinSum_const (m * m) (1 * 1)
    grind
  exact h

theorem sphereWitness_coord_bounds (m : Nat) (hm : 1 ≤ m) :
    (∀ (j : Fin (2 * (m * m) + 2)) (c : Fin (m * m)),
      -(m : Int) ≤ sphereWitnessBlock m j c ∧ sphereWitnessBlock m j c ≤ (m : Int)) ∧
    (∀ c : Fin (m * m),
      (∃ j : Fin (2 * (m * m) + 2), sphereWitnessBlock m j c = (m : Int)) ∧
      (∃ j : Fin (2 * (m * m) + 2), sphereWitnessBlock m j c = -(m : Int))) := by
  constructor
  · intro j c
    unfold sphereWitnessBlock
    by_cases hj0 : j.val = 0
    · simp [hj0]; omega
    · by_cases hj1 : j.val = 1
      · simp [hj1]; omega
      · simp only [hj0, hj1, ↓reduceIte]
        by_cases hc : c.val = (j.val - 2) / 2
        · simp only [hc, ↓reduceIte]
          split <;> omega
        · simp [hc]
  · intro c
    constructor
    · refine ⟨⟨2 + 2 * c.val, by omega⟩, ?_⟩
      unfold sphereWitnessBlock
      have hne0 : 2 + 2 * c.val ≠ 0 := by omega
      have hne1 : 2 + 2 * c.val ≠ 1 := by omega
      have hdiv : (2 + 2 * c.val - 2) / 2 = c.val := by omega
      have hmod : (2 + 2 * c.val - 2) % 2 = 0 := by omega
      simp only [hne0, hne1, hdiv, hmod, ↓reduceIte]
    · refine ⟨⟨2 + 2 * c.val + 1, by omega⟩, ?_⟩
      unfold sphereWitnessBlock
      have hne0 : 2 + 2 * c.val + 1 ≠ 0 := by omega
      have hne1 : 2 + 2 * c.val + 1 ≠ 1 := by omega
      have hdiv : (2 + 2 * c.val + 1 - 2) / 2 = c.val := by omega
      have hmod : (2 + 2 * c.val + 1 - 2) % 2 = 1 := by omega
      simp only [hne0, hne1, hdiv, hmod, ↓reduceIte]
      rfl

theorem sphereWitness_aabb_upper (m : Nat) :
    aabbUpper (allOnesVec (m * m)) (fun _ => -(m : Int)) (fun _ => (m : Int)) =
      (m : Int) * (m * m : Int) := by
  unfold aabbUpper allOnesVec
  have hcongr : intFinSum (fun _ : Fin (m * m) => max (1 * -(m : Int)) (1 * (m : Int))) =
      intFinSum (fun _ : Fin (m * m) => (m : Int)) := by
    apply intFinSum_congr
    intro _
    omega
  rw [hcongr, intFinSum_const]
  grind

/-- Headline Theorem 3 (`ball_bound_strictly_tighter_than_quest_aabb_and_half_metadata`):
    1. **Half Metadata:** For all `d ≥ 1`, `(d + 1)/(2d) = 1/2 + 1/(2d)` (`65/128` at `d = 64`),
       and `d + 1 < 2d` for all `d ≥ 2`.
    2. **Exact All-`d` (`d = m^2`) Geometric Separation:** For every `m ≥ 1`, on
       `sphereWitnessBlock m` (`B = 2m^2 + 2`, `d = m^2`, `q = allOnesVec d`):
       - `blockSum = 0` and exact `max_j (q^T k_j) = d = m^2` (attained at `j = 0`).
       - `Ball-Bound` is **exact (`0` slack):** `‖q‖_2^2 * R_b^2 = (B * d)^2`.
       - Tight coordinatewise `Quest-AABB` (`[-m, +m]^d`, both bounds attained per coordinate)
         gives `aabbUpper = m * d = √d * exactMax` (`> exactMax` for all `m ≥ 2`).
    3. **Concrete instantiations:** `2×` over-estimate at `d = 4` (`8` vs `4`) and `8×`
       over-estimate at `d = 64` (`512` vs `64`). -/
theorem ball_bound_strictly_tighter_than_quest_aabb_and_half_metadata :
    (∀ d : Nat, 1 ≤ d →
      ((d : Rat) + 1) / (2 * (d : Rat)) = (1 / 2 : Rat) + 1 / (2 * (d : Rat))) ∧
    (∀ d : Nat, 2 ≤ d → d + 1 < 2 * d) ∧
    (((64 : Rat) + 1) / (2 * (64 : Rat)) = 65 / 128) ∧
    (∀ m : Nat, 1 ≤ m →
      let d := m * m
      let B := 2 * d + 2
      let q := allOnesVec d
      let ks := sphereWitnessBlock m
      blockSum ks = (fun _ => 0) ∧
      (∀ j : Fin B, dotInt q (ks j) ≤ (d : Int)) ∧
      dotInt q (ks ⟨0, by omega⟩) = (d : Int) ∧
      normSqInt q * blockSqRadius ks = ((B : Int) * (d : Int)) * ((B : Int) * (d : Int)) ∧
      (∀ (j : Fin B) (c : Fin d), -(m : Int) ≤ ks j c ∧ ks j c ≤ (m : Int)) ∧
      (∀ c : Fin d, (∃ j : Fin B, ks j c = (m : Int)) ∧ (∃ j : Fin B, ks j c = -(m : Int))) ∧
      aabbUpper q (fun _ => -(m : Int)) (fun _ => (m : Int)) = (m : Int) * (d : Int) ∧
      (2 ≤ m → (d : Int) < aabbUpper q (fun _ => -(m : Int)) (fun _ => (m : Int)))) ∧
    (aabbUpper (allOnesVec 4) (fun _ => -2) (fun _ => 2) = 2 * 4 ∧
     aabbUpper (allOnesVec 64) (fun _ => -8) (fun _ => 8) = 8 * 64) := by
  refine ⟨metadata_ratio_exact, fun _ hd => by omega, by grind, ?_, ?_⟩
  · intro m hm
    dsimp only
    have hbounds := sphereWitness_coord_bounds m hm
    refine ⟨sphereWitness_blockSum_zero m,
            sphereWitness_dot_le m hm,
            sphereWitness_dot_zero m,
            ?_, hbounds.1, hbounds.2, sphereWitness_aabb_upper m, ?_⟩
    · rw [allOnesVec_normSq, sphereWitness_blockSqRadius]
      grind
    · intro hm2
      rw [sphereWitness_aabb_upper m]
      have h1 : (m * m : Int) < (m : Int) * (m * m : Int) := by
        have hpos : (0 : Int) < (m * m : Int) := by
          have : 0 < m * m := Nat.mul_pos (by omega) (by omega)
          omega
        have hmul : 0 < ((m : Int) - 1) * (m * m : Int) := Int.mul_pos (by omega) hpos
        grind
      exact h1
  · constructor
    · exact sphereWitness_aabb_upper 2
    · exact sphereWitness_aabb_upper 8

end NsaBallBoundMoba
