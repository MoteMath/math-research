/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RagPopcntMatryoshka.RatOrder

/-!
# Theorem 5: Stage-2 Symmetric `INT4` Rescore Gap Preservation

Proves:
1. Universal Top-`K` ranking preservation under perturbation `≤ ε`: whenever the true score gap
   satisfies `2 ε < sTrue pos - sTrue neg`, quantized rescoring strictly preserves `sQuant neg < sQuant pos`.
2. Exact rational `Fin d` dot-product quantization perturbation bound:
   `|⟨q, x̂⟩ - ⟨q, x⟩| ≤ δ · ‖q‖_1`.
3. Exact pure-integer certification of the GPU kernel `quantInt4Step64` (`[-7, +7]`, step `64`):
   for all `v ∈ [-480, 480]`, `-7 ≤ quantInt4Step64 v ≤ 7` and `|v - 64 * quantInt4Step64 v| ≤ 32`.
4. Exact Stage-2 `INT4` integer dot-product margin preservation: whenever
   `64 · ‖q‖_1 < ⟨q, xPos⟩ - ⟨q, xNeg⟩`, the Stage-2 `INT4` integer dot product strictly preserves
   `⟨q, quantInt4(xNeg)⟩ < ⟨q, quantInt4(xPos)⟩`.
-/

namespace RagPopcntMatryoshka

theorem ranking_preserved_of_gap_gt_two_eps {sTruePos sTrueNeg sQuantPos sQuantNeg eps : Rat}
    (hpos : ratAbs (sQuantPos - sTruePos) ≤ eps)
    (hneg : ratAbs (sQuantNeg - sTrueNeg) ≤ eps)
    (hgap : 2 * eps < sTruePos - sTrueNeg) :
    sQuantNeg < sQuantPos := by
  have ⟨hposLo, _⟩ := ratAbs_le_iff.mp hpos
  have ⟨_, hnegHi⟩ := ratAbs_le_iff.mp hneg
  apply rat_lt_of_sub_pos
  have h1 : (0 : Rat) ≤ (sQuantPos - sTruePos) - (-eps) := rat_sub_nonneg hposLo
  have h2 : (0 : Rat) ≤ eps - (sQuantNeg - sTrueNeg) := rat_sub_nonneg hnegHi
  have h3 : (0 : Rat) < (sTruePos - sTrueNeg) - 2 * eps := rat_sub_pos hgap
  have hsum := rat_add_pos_of_pos_of_nonneg h3 (rat_add_nonneg h1 h2)
  have eq :
      ((sTruePos - sTrueNeg) - 2 * eps) +
      (((sQuantPos - sTruePos) - (-eps)) + (eps - (sQuantNeg - sTrueNeg))) =
      sQuantPos - sQuantNeg := by grind
  rw [eq] at hsum
  exact hsum

theorem dotRat_perturbation_bound {d : Nat} (q x xHat : Fin d → Rat) (delta : Rat)
    (h : ∀ i, ratAbs (xHat i - x i) ≤ delta) :
    ratAbs (dotRat q xHat - dotRat q x) ≤ delta * l1NormRat q := by
  unfold dotRat l1NormRat
  rw [← finSumRat_sub]
  have hrew : (fun i : Fin d => q i * xHat i - q i * x i) =
      (fun i : Fin d => q i * (xHat i - x i)) := by
    funext i; grind
  rw [hrew]
  apply Rat.le_trans (ratAbs_finSumRat_le _)
  rw [← finSumRat_mul_left]
  apply finSumRat_le_finSumRat
  intro i
  rw [ratAbs_mul, Rat.mul_comm delta (ratAbs (q i))]
  exact rat_mul_le_mul_of_nonneg_left (h i) (ratAbs_nonneg (q i))

theorem quantInt4Step64_exact_bounds (v : Int) (hlo : (-480 : Int) ≤ v) (hhi : v ≤ 480) :
    (-7 : Int) ≤ quantInt4Step64 v ∧
    quantInt4Step64 v ≤ 7 ∧
    intAbs (v - 64 * quantInt4Step64 v) ≤ 32 := by
  unfold quantInt4Step64 clampInt intAbs
  by_cases hv : (0 : Int) ≤ v
  · simp only [hv, ↓reduceIte]
    by_cases h1 : (v + 32) / 64 < -7
    · omega
    · simp only [h1, ↓reduceIte]
      by_cases h2 : (7 : Int) < (v + 32) / 64
      · simp only [h2, ↓reduceIte]
        split <;> omega
      · simp only [h2, ↓reduceIte]
        split <;> omega
  · simp only [hv, ↓reduceIte]
    by_cases h1 : -((-v + 32) / 64) < -7
    · simp only [h1, ↓reduceIte]
      split <;> omega
    · simp only [h1, ↓reduceIte]
      by_cases h2 : (7 : Int) < -((-v + 32) / 64)
      · omega
      · simp only [h2, ↓reduceIte]
        split <;> omega

theorem intAbs_add_le (x y : Int) : intAbs (x + y) ≤ intAbs x + intAbs y := by
  unfold intAbs
  split <;> split <;> split <;> omega

theorem intAbs_mul (x y : Int) : intAbs (x * y) = intAbs x * intAbs y := by
  unfold intAbs
  by_cases hx : (0 : Int) ≤ x <;> by_cases hy : (0 : Int) ≤ y
  · have hxy : (0 : Int) ≤ x * y := Int.mul_nonneg hx hy
    simp [hx, hy, hxy]
  · by_cases hx0 : x = 0
    · subst hx0; simp
    · have hxy : x * y < 0 := by
        have hxp : 0 < x := by omega
        have hyn : y < 0 := by omega
        have := Int.mul_pos hxp (by omega : 0 < -y)
        grind
      have hnot : ¬((0 : Int) ≤ x * y) := by omega
      simp only [hx, hy, hnot, ↓reduceIte]
      grind
  · by_cases hy0 : y = 0
    · subst hy0; simp
    · have hxy : x * y < 0 := by
        have hxn : x < 0 := by omega
        have hyp : 0 < y := by omega
        have := Int.mul_pos (by omega : 0 < -x) hyp
        grind
      have hnot : ¬((0 : Int) ≤ x * y) := by omega
      simp only [hx, hy, hnot, ↓reduceIte]
      grind
  · have hxy : (0 : Int) ≤ x * y := by
      have := Int.mul_nonneg (by omega : (0 : Int) ≤ -x) (by omega : (0 : Int) ≤ -y)
      grind
    simp only [hx, hy, hxy, ↓reduceIte]
    grind

theorem intAbs_finSumInt_le {n : Nat} (f : Fin n → Int) :
    intAbs (finSumInt f) ≤ finSumInt (fun i => intAbs (f i)) := by
  induction n with
  | zero => simp [finSumInt, intAbs]
  | succ n ih =>
    simp only [finSumInt]
    have h1 := intAbs_add_le (finSumInt (fun i : Fin n => f i.castSucc)) (f (Fin.last n))
    have h2 := ih (fun i => f i.castSucc)
    omega

theorem int4_dot_perturbation_bound {d : Nat} (q x : Fin d → Int)
    (hx : ∀ i, (-480 : Int) ≤ x i ∧ x i ≤ 480) :
    intAbs (dotInt q x - 64 * dotInt q (fun i => quantInt4Step64 (x i))) ≤ 32 * l1NormInt q := by
  unfold dotInt l1NormInt
  rw [← finSumInt_mul_left, ← finSumInt_sub]
  have hrew : (fun i : Fin d => q i * x i - 64 * (q i * quantInt4Step64 (x i))) =
      (fun i : Fin d => q i * (x i - 64 * quantInt4Step64 (x i))) := by
    funext i; grind
  rw [hrew]
  apply Int.le_trans (intAbs_finSumInt_le _)
  rw [← finSumInt_mul_left]
  apply finSumInt_le_finSumInt
  intro i
  rw [intAbs_mul]
  have ⟨_, _, herr⟩ := quantInt4Step64_exact_bounds (x i) (hx i).1 (hx i).2
  have hqnn : (0 : Int) ≤ intAbs (q i) := by unfold intAbs; split <;> omega
  have hmul : intAbs (q i) * intAbs (x i - 64 * quantInt4Step64 (x i)) ≤ intAbs (q i) * 32 :=
    Int.mul_le_mul_of_nonneg_left herr hqnn
  rw [Int.mul_comm (32 : Int) (intAbs (q i))]
  exact hmul

theorem int4_rescore_ranking_preserved {d : Nat} (q xPos xNeg : Fin d → Int)
    (hPos : ∀ i, (-480 : Int) ≤ xPos i ∧ xPos i ≤ 480)
    (hNeg : ∀ i, (-480 : Int) ≤ xNeg i ∧ xNeg i ≤ 480)
    (hgap : 64 * l1NormInt q < dotInt q xPos - dotInt q xNeg) :
    dotInt q (fun i => quantInt4Step64 (xNeg i)) <
    dotInt q (fun i => quantInt4Step64 (xPos i)) := by
  have hp := int4_dot_perturbation_bound q xPos hPos
  have hn := int4_dot_perturbation_bound q xNeg hNeg
  unfold intAbs at hp hn
  split at hp <;> split at hn <;> omega

/-- Headline Theorem 5 (`stage2_int4_rescore_gap_preservation_exact`). -/
theorem stage2_int4_rescore_gap_preservation_exact :
    (∀ sTruePos sTrueNeg sQuantPos sQuantNeg eps : Rat,
      ratAbs (sQuantPos - sTruePos) ≤ eps →
      ratAbs (sQuantNeg - sTrueNeg) ≤ eps →
      2 * eps < sTruePos - sTrueNeg →
      sQuantNeg < sQuantPos) ∧
    (∀ (d : Nat) (q x xHat : Fin d → Rat) (delta : Rat),
      (∀ i, ratAbs (xHat i - x i) ≤ delta) →
      ratAbs (dotRat q xHat - dotRat q x) ≤ delta * l1NormRat q) ∧
    (∀ v : Int, (-480 : Int) ≤ v → v ≤ 480 →
      (-7 : Int) ≤ quantInt4Step64 v ∧
      quantInt4Step64 v ≤ 7 ∧
      intAbs (v - 64 * quantInt4Step64 v) ≤ 32) ∧
    (∀ (d : Nat) (q xPos xNeg : Fin d → Int),
      (∀ i, (-480 : Int) ≤ xPos i ∧ xPos i ≤ 480) →
      (∀ i, (-480 : Int) ≤ xNeg i ∧ xNeg i ≤ 480) →
      64 * l1NormInt q < dotInt q xPos - dotInt q xNeg →
      dotInt q (fun i => quantInt4Step64 (xNeg i)) <
      dotInt q (fun i => quantInt4Step64 (xPos i))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro sTruePos sTrueNeg sQuantPos sQuantNeg eps hpos hneg hgap
    exact ranking_preserved_of_gap_gt_two_eps hpos hneg hgap
  · intro d q x xHat delta h
    exact dotRat_perturbation_bound q x xHat delta h
  · intro v hlo hhi
    exact quantInt4Step64_exact_bounds v hlo hhi
  · intro d q xPos xNeg hPos hNeg hgap
    exact int4_rescore_ranking_preserved q xPos xNeg hPos hNeg hgap

end RagPopcntMatryoshka
