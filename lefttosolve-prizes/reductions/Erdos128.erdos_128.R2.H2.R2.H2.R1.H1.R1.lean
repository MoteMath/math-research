import OMAReductions.R_Erdos128_erdos_128_R2_H2_R2_H2_R1

/-!
# Reduction Erdos128.erdos_128.R2.H2.R2.H2.R1.H1.R1 of Erdos128.erdos_128.R2.H2.R2.H2.R1.H1

Proves directly inside `main` (zero `sorry`, standard axioms only):
1. Continuous Razborov Theorem A (`exists_sparse_half_of_indep_ge_two_fifths`):
   for any finite triangle-free graph `G` on `V` and any probability weight `w : V → ℝ`
   (`∀ z, 0 ≤ w z`, `∑ z, w z = 1`), if any independent set `I : Finset V` satisfies
   `2 / 5 ≤ ∑ z ∈ I, w z`, then there exists a fractional sparse half `s : V → ℝ`
   with `0 ≤ s z ≤ w z`, `∑ z, s z = 1 / 2`, and `25 * ∑ x, ∑ y, [G.Adj x y] * s x * s y ≤ 1`.
   This eliminates all tight C₅ extrema and >99.9% of the 13-simplex Δ₁₃.
2. Continuous Random-Half Edge Cutoff (`exists_sparse_half_of_quad_le`):
   if `25 * (∑ x, ∑ y, [G.Adj x y] * w x * w y) ≤ 4`, then `s = (1 / 2) • w` is a sparse half.
3. Exact `ℤ₂ × ℤ₂` Automorphism Symmetry Reduction on the 13-vertex Vega graph `Υ₂⁰⁰`:
   - `σ₁` swaps `E₀ ↔ E₁` (`b0↔b3, b1↔b4, b2↔b5, b6↔b7`), reducing WLOG to `w(E₀) ≤ w(E₁)`.
   - `σ₂` reverses `C₅` (`a0↔a3, a1↔a2, b0↔b4, b3↔b1`), reducing WLOG to `w(a0)+w(a1) ≤ w(a2)+w(a3)`.

Reduces `Erdos128.erdos_128.R2.H2.R2.H2.R1.H1` cleanly to the tiny strictly-subcritical
symmetry-reduced polytope `∀ I indep, w(I) < 2/5` (where `min_s 25 sᵀ A s` has >11% slack),
split into two clean complementary sub-bands on `w(inl)`:
- `H1`: `w(inl) ≤ 1 / 3`
- `H2`: `1 / 3 < w(inl)`
-/

-- Credit: @DevinWatson

namespace OMA.R_Erdos128_erdos_128_R2_H2_R2_H2_R1_H1_R1

open Finset SimpleGraph

/-- Strictly-subcritical symmetry-reduced polytope on `Υ₂⁰⁰` with `w(inl) ≤ 1 / 3`. -/
def H1 : Prop :=
  let adj : Fin 5 ⊕ Fin 8 → Fin 5 ⊕ Fin 8 → Prop := fun x y => match x, y with
    | .inl p, .inl q => 2 ≤ (q.val + 5 - p.val) % 5 ∧ (q.val + 5 - p.val) % 5 ≤ 3
    | .inl p, .inr t | .inr t, .inl p =>
        ((t.val = 0 ∨ t.val = 3) ∧ p.val < 2) ∨
        ((t.val = 4 ∨ t.val = 1) ∧ 2 ≤ p.val ∧ p.val < 4) ∨
        ((t.val = 2 ∨ t.val = 5) ∧ 4 ≤ p.val)
    | .inr t₁, .inr t₂ =>
        (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
        (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
        (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
        (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
        (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))
  ∀ [DecidableRel adj], ∀ w : Fin 5 ⊕ Fin 8 → ℝ,
    (∀ z, 0 ≤ w z) → (∑ z, w z) = 1 →
    (∀ I : Finset (Fin 5 ⊕ Fin 8), (∀ x ∈ I, ∀ y ∈ I, ¬ adj x y) → (∑ z ∈ I, w z) < 2 / 5) →
    4 < 25 * (∑ x, ∑ y, if adj x y then w x * w y else 0) →
    w (.inr 0) + w (.inr 2) + w (.inr 4) + w (.inr 7) ≤
      w (.inr 1) + w (.inr 3) + w (.inr 5) + w (.inr 6) →
    w (.inl 0) + w (.inl 1) ≤ w (.inl 2) + w (.inl 3) →
    (∑ p : Fin 5, w (.inl p)) ≤ 1 / 3 →
    ∃ s : Fin 5 ⊕ Fin 8 → ℝ, (∀ z, 0 ≤ s z ∧ s z ≤ w z) ∧ (∑ z, s z) = 1 / 2 ∧
      25 * (∑ x, ∑ y, if adj x y then s x * s y else 0) ≤ 1

/-- Strictly-subcritical symmetry-reduced polytope on `Υ₂⁰⁰` with `1 / 3 < w(inl)`. -/
def H2 : Prop :=
  let adj : Fin 5 ⊕ Fin 8 → Fin 5 ⊕ Fin 8 → Prop := fun x y => match x, y with
    | .inl p, .inl q => 2 ≤ (q.val + 5 - p.val) % 5 ∧ (q.val + 5 - p.val) % 5 ≤ 3
    | .inl p, .inr t | .inr t, .inl p =>
        ((t.val = 0 ∨ t.val = 3) ∧ p.val < 2) ∨
        ((t.val = 4 ∨ t.val = 1) ∧ 2 ≤ p.val ∧ p.val < 4) ∨
        ((t.val = 2 ∨ t.val = 5) ∧ 4 ≤ p.val)
    | .inr t₁, .inr t₂ =>
        (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
        (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
        (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
        (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
        (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))
  ∀ [DecidableRel adj], ∀ w : Fin 5 ⊕ Fin 8 → ℝ,
    (∀ z, 0 ≤ w z) → (∑ z, w z) = 1 →
    (∀ I : Finset (Fin 5 ⊕ Fin 8), (∀ x ∈ I, ∀ y ∈ I, ¬ adj x y) → (∑ z ∈ I, w z) < 2 / 5) →
    4 < 25 * (∑ x, ∑ y, if adj x y then w x * w y else 0) →
    w (.inr 0) + w (.inr 2) + w (.inr 4) + w (.inr 7) ≤
      w (.inr 1) + w (.inr 3) + w (.inr 5) + w (.inr 6) →
    w (.inl 0) + w (.inl 1) ≤ w (.inl 2) + w (.inl 3) →
    1 / 3 < (∑ p : Fin 5, w (.inl p)) →
    ∃ s : Fin 5 ⊕ Fin 8 → ℝ, (∀ z, 0 ≤ s z ∧ s z ≤ w z) ∧ (∑ z, s z) = 1 / 2 ∧
      25 * (∑ x, ∑ y, if adj x y then s x * s y else 0) ≤ 1

/- ### Part 1: Continuous Random-Half Edge Cutoff -/

lemma exists_sparse_half_of_quad_le {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw0 : ∀ z, 0 ≤ w z) (hw1 : (∑ z, w z) = 1)
    (hquad : 25 * (∑ x : V, ∑ y : V, if G.Adj x y then w x * w y else 0) ≤ 4) :
    ∃ s : V → ℝ,
      (∀ z, 0 ≤ s z ∧ s z ≤ w z) ∧
      (∑ z, s z) = 1 / 2 ∧
      25 * (∑ x : V, ∑ y : V, if G.Adj x y then s x * s y else 0) ≤ 1 := by
  refine ⟨fun z => w z / 2, ?_, ?_, ?_⟩
  · intro z; have := hw0 z; constructor <;> linarith
  · rw [← Finset.sum_div, hw1]
  · have hscale : (∑ x : V, ∑ y : V, if G.Adj x y then (w x / 2) * (w y / 2) else 0) =
        (∑ x : V, ∑ y : V, if G.Adj x y then w x * w y else 0) / 4 := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun y _ => ?_
      split_ifs <;> ring
    rw [hscale]; linarith

/- ### Part 2: Continuous Razborov Theorem A (`α(G, w) ≥ 2/5 → sparse half`) -/

lemma quad_indep_plus_scaled {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (A B : Finset V) (hdisj : Disjoint A B)
    (hA : ∀ x ∈ A, ∀ y ∈ A, ¬ G.Adj x y) (c : ℝ) :
    let s : V → ℝ := fun z => if z ∈ A then w z else if z ∈ B then c * w z else 0
    (∑ x : V, ∑ y : V, if G.Adj x y then s x * s y else 0) =
      2 * c * (∑ x ∈ A, ∑ y ∈ B, if G.Adj x y then w x * w y else 0) +
      c ^ 2 * (∑ x ∈ B, ∑ y ∈ B, if G.Adj x y then w x * w y else 0) := by
  intro s
  have hzero : ∀ x : V, x ∉ A ∪ B → s x = 0 := by
    intro x hx
    simp only [Finset.mem_union, not_or] at hx
    simp only [s, if_neg hx.1, if_neg hx.2]
  have hsub1 : (∑ x : V, ∑ y : V, if G.Adj x y then s x * s y else 0) =
      ∑ x ∈ A ∪ B, ∑ y ∈ A ∪ B, if G.Adj x y then s x * s y else 0 := by
    symm
    refine Finset.sum_subset_zero_on_sdiff (Finset.subset_univ _) ?_ ?_
    · intro x hx
      have hx' : x ∉ A ∪ B := (Finset.mem_sdiff.mp hx).2
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [hzero x hx', zero_mul, ite_self]
    · intro x _
      refine Finset.sum_subset (Finset.subset_univ _) fun y _ hy => ?_
      rw [hzero y hy, mul_zero, ite_self]
  rw [hsub1, Finset.sum_union hdisj]
  simp_rw [Finset.sum_union hdisj]
  have hAA : (∑ x ∈ A, ∑ y ∈ A, if G.Adj x y then s x * s y else 0) = 0 := by
    refine Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y hy => ?_
    rw [if_neg (hA x hx y hy)]
  have hAB : (∑ x ∈ A, ∑ y ∈ B, if G.Adj x y then s x * s y else 0) =
      c * (∑ x ∈ A, ∑ y ∈ B, if G.Adj x y then w x * w y else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    have hyA : y ∉ A := Finset.disjoint_right.mp hdisj hy
    simp only [s, if_pos hx, if_neg hyA, if_pos hy]
    split_ifs <;> ring
  have hBA : (∑ x ∈ B, ∑ y ∈ A, if G.Adj x y then s x * s y else 0) =
      c * (∑ x ∈ A, ∑ y ∈ B, if G.Adj x y then w x * w y else 0) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    have hyA : y ∉ A := Finset.disjoint_right.mp hdisj hy
    simp only [s, if_pos hx, if_neg hyA, if_pos hy]
    by_cases hxy : G.Adj x y
    · rw [if_pos hxy.symm, if_pos hxy]; ring
    · rw [if_neg (fun h => hxy h.symm), if_neg hxy]; ring
  have hBB : (∑ x ∈ B, ∑ y ∈ B, if G.Adj x y then s x * s y else 0) =
      c ^ 2 * (∑ x ∈ B, ∑ y ∈ B, if G.Adj x y then w x * w y else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    have hxA : x ∉ A := Finset.disjoint_right.mp hdisj hx
    have hyA : y ∉ A := Finset.disjoint_right.mp hdisj hy
    simp only [s, if_neg hxA, if_pos hx, if_neg hyA, if_pos hy]
    split_ifs <;> ring
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hAA, hAB, hBA, hBB]
  ring

lemma exists_sparse_half_of_indep_ge_two_fifths {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hTF : G.CliqueFree 3)
    (w : V → ℝ) (hw0 : ∀ z, 0 ≤ w z) (hw1 : (∑ z, w z) = 1)
    (I₀ : Finset V) (hI₀ : ∀ x ∈ I₀, ∀ y ∈ I₀, ¬ G.Adj x y)
    (hwI₀ : 2 / 5 ≤ ∑ z ∈ I₀, w z) :
    ∃ s : V → ℝ,
      (∀ z, 0 ≤ s z ∧ s z ≤ w z) ∧
      (∑ z, s z) = 1 / 2 ∧
      25 * (∑ x : V, ∑ y : V, if G.Adj x y then s x * s y else 0) ≤ 1 := by
  classical
  let indepSets : Finset (Finset V) :=
    Finset.univ.filter (fun S => ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y)
  have hI₀_mem : I₀ ∈ indepSets := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI₀⟩
  obtain ⟨I, hI_mem, hI_max⟩ :=
    Finset.exists_max_image indepSets (fun S => ∑ z ∈ S, w z) ⟨I₀, hI₀_mem⟩
  have hI : ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y := (Finset.mem_filter.mp hI_mem).2
  have hI_le : ∀ J : Finset V, (∀ x ∈ J, ∀ y ∈ J, ¬ G.Adj x y) →
      (∑ z ∈ J, w z) ≤ ∑ z ∈ I, w z :=
    fun J hJ => hI_max J (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hJ⟩)
  set α : ℝ := ∑ z ∈ I, w z
  have hα_ge : 2 / 5 ≤ α := hwI₀.trans (hI_max I₀ hI₀_mem)
  by_cases hα_half : 1 / 2 ≤ α
  · have hα_pos : 0 < α := by linarith
    let c : ℝ := (1 / 2) / α
    have hc0 : 0 ≤ c := by positivity
    have hc1 : c ≤ 1 := by dsimp only [c]; rw [div_le_one hα_pos]; linarith
    refine ⟨fun z => if z ∈ I then c * w z else 0, ?_, ?_, ?_⟩
    · intro z
      by_cases hz : z ∈ I
      · simp only [if_pos hz]
        exact ⟨mul_nonneg hc0 (hw0 z), by nlinarith [hw0 z]⟩
      · simp only [if_neg hz]; exact ⟨le_refl 0, hw0 z⟩
    · have hsum : (∑ z : V, if z ∈ I then c * w z else 0) = ∑ z ∈ I, c * w z := by
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
      rw [hsum, ← Finset.mul_sum]
      change c * α = 1 / 2
      dsimp only [c]; exact div_mul_cancel₀ _ (ne_of_gt hα_pos)
    · have hzero : (∑ x : V, ∑ y : V, if G.Adj x y then
          (if x ∈ I then c * w x else 0) * (if y ∈ I then c * w y else 0) else 0) = 0 := by
        refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
        by_cases hx : x ∈ I
        · by_cases hy : y ∈ I
          · rw [if_neg (hI x hx y hy)]
          · simp only [if_neg hy, mul_zero, ite_self]
        · simp only [if_neg hx, zero_mul, ite_self]
      rw [hzero]; norm_num
  · push Not at hα_half
    set r : ℝ := 1 / 2 - α
    have hr_pos : 0 < r := by dsimp only [r]; linarith
    have hα_pos : 0 < α := by linarith
    have h25ar : 25 * (α * r) ≤ 1 := by
      have hsq : 0 ≤ (5 * α - 2) * (10 * α - 1) := mul_nonneg (by linarith) (by linarith)
      dsimp only [r]; nlinarith
    let dI : V → ℝ := fun v => ∑ x ∈ I, if G.Adj v x then w x else 0
    let R₁ : Finset V := (Finset.univ \ I).filter (fun v => α < 2 * dI v)
    let R₀ : Finset V := (Finset.univ \ I).filter (fun v => 2 * dI v ≤ α)
    have hR₁_indep : ∀ u ∈ R₁, ∀ v ∈ R₁, ¬ G.Adj u v := by
      intro u hu v hv huv
      have hu' : α < 2 * dI u := (Finset.mem_filter.mp hu).2
      have hv' : α < 2 * dI v := (Finset.mem_filter.mp hv).2
      have hsum_le : dI u + dI v ≤ α := by
        dsimp only [dI]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun x _ => ?_
        by_cases hux : G.Adj u x
        · have hnvx : ¬ G.Adj v x := fun hvx =>
            OMA.R_Erdos128_erdos_128_R2.not_adj_of_cliqueFree_three hTF huv hvx hux
          rw [if_pos hux, if_neg hnvx, add_zero]
        · rw [if_neg hux, zero_add]
          split_ifs
          · exact le_refl _
          · exact hw0 x
      linarith
    have hdisj_IR₁ : Disjoint I R₁ := by
      rw [Finset.disjoint_left]; intro x hx hx1
      exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx1).1).2 hx
    have hdisj_IR₀ : Disjoint I R₀ := by
      rw [Finset.disjoint_left]; intro x hx hx0
      exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx0).1).2 hx
    have hdisj_R₁R₀ : Disjoint R₁ R₀ := by
      rw [Finset.disjoint_left]; intro x hx1 hx0
      have h1 := (Finset.mem_filter.mp hx1).2
      have h0 := (Finset.mem_filter.mp hx0).2
      linarith
    set m₁ : ℝ := ∑ z ∈ R₁, w z
    set m₀ : ℝ := ∑ z ∈ R₀, w z
    have hm₁_le : m₁ ≤ α := hI_le R₁ hR₁_indep
    have hpart : α + m₁ + m₀ = 1 := by
      have hunion : I ∪ (R₁ ∪ R₀) = Finset.univ := by
        ext x
        simp only [Finset.mem_union, Finset.mem_univ, iff_true, R₁, R₀, Finset.mem_filter,
          Finset.mem_sdiff, true_and]
        by_cases hx : x ∈ I
        · exact Or.inl hx
        · by_cases hd : α < 2 * dI x
          · exact Or.inr (Or.inl ⟨hx, hd⟩)
          · exact Or.inr (Or.inr ⟨hx, by linarith⟩)
      have hdisj_I_R : Disjoint I (R₁ ∪ R₀) := Finset.disjoint_union_right.mpr ⟨hdisj_IR₁, hdisj_IR₀⟩
      have h1 : (∑ z ∈ I ∪ (R₁ ∪ R₀), w z) = 1 := by rw [hunion]; exact hw1
      rw [Finset.sum_union hdisj_I_R, Finset.sum_union hdisj_R₁R₀] at h1
      linarith
    set r₁ : ℝ := 1 / 2 - m₁
    have hm₀_pos : 0 < m₀ := by linarith
    let indepR₀ : Finset (Finset V) :=
      R₀.powerset.filter (fun S => ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y)
    have hEmpty_R₀ : (∅ : Finset V) ∈ indepR₀ := by simp [indepR₀]
    obtain ⟨J, hJ_mem, hJ_max⟩ :=
      Finset.exists_max_image indepR₀ (fun S => ∑ z ∈ S, w z) ⟨∅, hEmpty_R₀⟩
    have hJ_sub : J ⊆ R₀ := Finset.mem_powerset.mp (Finset.mem_filter.mp hJ_mem).1
    have hJ_indep : ∀ x ∈ J, ∀ y ∈ J, ¬ G.Adj x y := (Finset.mem_filter.mp hJ_mem).2
    set β : ℝ := ∑ z ∈ J, w z
    by_cases hβ : r ≤ β
    · have hβ_pos : 0 < β := lt_of_lt_of_le hr_pos hβ
      let c : ℝ := r / β
      have hc0 : 0 ≤ c := by positivity
      have hc1 : c ≤ 1 := by dsimp only [c]; rw [div_le_one hβ_pos]; exact hβ
      have hdisj_IJ : Disjoint I J := hdisj_IR₀.mono_right hJ_sub
      let s : V → ℝ := fun z => if z ∈ I then w z else if z ∈ J then c * w z else 0
      refine ⟨s, ?_, ?_, ?_⟩
      · intro z
        by_cases hzI : z ∈ I
        · simp only [s, if_pos hzI]; exact ⟨hw0 z, le_refl _⟩
        · by_cases hzJ : z ∈ J
          · simp only [s, if_neg hzI, if_pos hzJ]
            exact ⟨mul_nonneg hc0 (hw0 z), by nlinarith [hw0 z]⟩
          · simp only [s, if_neg hzI, if_neg hzJ]; exact ⟨le_refl 0, hw0 z⟩
      · have hsum : (∑ z : V, s z) = ∑ z ∈ I ∪ J, s z := by
          symm; refine Finset.sum_subset (Finset.subset_univ _) fun z _ hz => ?_
          simp only [Finset.mem_union, not_or] at hz
          simp only [s, if_neg hz.1, if_neg hz.2]
        rw [hsum, Finset.sum_union hdisj_IJ]
        have h1 : (∑ z ∈ I, s z) = α := Finset.sum_congr rfl fun z hz => by simp only [s, if_pos hz]
        have h2 : (∑ z ∈ J, s z) = c * β := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun z hz => ?_
          simp only [s, if_neg (Finset.disjoint_right.mp hdisj_IJ hz), if_pos hz]
        rw [h1, h2]
        have hcb : c * β = r := div_mul_cancel₀ _ (ne_of_gt hβ_pos)
        rw [hcb]; dsimp only [r]; ring
      · have hq := quad_indep_plus_scaled G w I J hdisj_IJ hI c
        have hJJ : (∑ x ∈ J, ∑ y ∈ J, if G.Adj x y then w x * w y else 0) = 0 := by
          refine Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y hy => ?_
          rw [if_neg (hJ_indep x hx y hy)]
        have hIJ_le : 2 * (∑ x ∈ I, ∑ y ∈ J, if G.Adj x y then w x * w y else 0) ≤ α * β := by
          rw [Finset.sum_comm, Finset.mul_sum]
          calc (∑ y ∈ J, 2 * ∑ x ∈ I, if G.Adj x y then w x * w y else 0)
              = ∑ y ∈ J, (2 * dI y) * w y := by
                refine Finset.sum_congr rfl fun y _ => ?_
                dsimp only [dI]
                rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
                refine Finset.sum_congr rfl fun x _ => ?_
                by_cases hxy : G.Adj x y
                · rw [if_pos hxy, if_pos hxy.symm]; ring
                · rw [if_neg hxy, if_neg (fun h => hxy h.symm)]; ring
            _ ≤ ∑ y ∈ J, α * w y := by
                refine Finset.sum_le_sum fun y hy => ?_
                have hy0 : 2 * dI y ≤ α := (Finset.mem_filter.mp (hJ_sub hy)).2
                exact mul_le_mul_of_nonneg_right hy0 (hw0 y)
            _ = α * β := by rw [← Finset.mul_sum]
        have hq_le : (∑ x : V, ∑ y : V, if G.Adj x y then s x * s y else 0) ≤ α * r := by
          rw [hq, hJJ, mul_zero, add_zero]
          have h1 : 2 * c * (∑ x ∈ I, ∑ y ∈ J, if G.Adj x y then w x * w y else 0) =
              c * (2 * (∑ x ∈ I, ∑ y ∈ J, if G.Adj x y then w x * w y else 0)) := by ring
          rw [h1]
          have h2 := mul_le_mul_of_nonneg_left hIJ_le hc0
          have h3 : c * (α * β) = α * r := by
            dsimp only [c]; field_simp [ne_of_gt hβ_pos]
          linarith
        linarith
    · push Not at hβ
      set e₁ : ℝ := ∑ x ∈ I, ∑ y ∈ R₀, if G.Adj x y then w x * w y else 0
      set e₂ : ℝ := ∑ x ∈ R₁, ∑ y ∈ R₀, if G.Adj x y then w x * w y else 0
      set d₀ : ℝ := ∑ x ∈ R₀, ∑ y ∈ R₀, if G.Adj x y then w x * w y else 0
      have hF1 : e₁ + e₂ + d₀ ≤ m₀ * α := by
        have hswap1 : e₁ = ∑ y ∈ R₀, w y * ∑ x ∈ I, if G.Adj y x then w x else 0 := by
          dsimp only [e₁]; rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => ?_
          by_cases h : G.Adj x y
          · rw [if_pos h, if_pos h.symm]; ring
          · rw [if_neg h, if_neg (fun h' => h h'.symm)]; ring
        have hswap2 : e₂ = ∑ y ∈ R₀, w y * ∑ x ∈ R₁, if G.Adj y x then w x else 0 := by
          dsimp only [e₂]; rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => ?_
          by_cases h : G.Adj x y
          · rw [if_pos h, if_pos h.symm]; ring
          · rw [if_neg h, if_neg (fun h' => h h'.symm)]; ring
        have hswap3 : d₀ = ∑ y ∈ R₀, w y * ∑ x ∈ R₀, if G.Adj y x then w x else 0 := by
          dsimp only [d₀]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => ?_
          split_ifs <;> ring
        rw [hswap1, hswap2, hswap3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        calc (∑ y ∈ R₀, (w y * (∑ x ∈ I, if G.Adj y x then w x else 0) +
                w y * (∑ x ∈ R₁, if G.Adj y x then w x else 0) +
                w y * (∑ x ∈ R₀, if G.Adj y x then w x else 0)))
            ≤ ∑ y ∈ R₀, w y * α := by
              refine Finset.sum_le_sum fun y _ => ?_
              have htot : (∑ x ∈ I, if G.Adj y x then w x else 0) +
                  (∑ x ∈ R₁, if G.Adj y x then w x else 0) +
                  (∑ x ∈ R₀, if G.Adj y x then w x else 0) ≤ α := by
                have hdisj1 : Disjoint I (R₁ ∪ R₀) :=
                  Finset.disjoint_union_right.mpr ⟨hdisj_IR₁, hdisj_IR₀⟩
                have hu : (∑ x ∈ I, if G.Adj y x then w x else 0) +
                    (∑ x ∈ R₁, if G.Adj y x then w x else 0) +
                    (∑ x ∈ R₀, if G.Adj y x then w x else 0) =
                    ∑ x ∈ I ∪ (R₁ ∪ R₀), if G.Adj y x then w x else 0 := by
                  rw [Finset.sum_union hdisj1, Finset.sum_union hdisj_R₁R₀]; ring
                rw [hu, ← Finset.sum_filter]
                exact hI_le _ (OMA.R_Erdos128_erdos_128_R2.filter_adj_indep hTF _ y)
              nlinarith [hw0 y]
          _ = m₀ * α := by rw [← Finset.sum_mul]
      have hF2 : e₁ ≤ α * r := by
        have h1 : e₁ = ∑ x ∈ I, w x * ∑ y ∈ R₀.filter (G.Adj x), w y := by
          dsimp only [e₁]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_filter (s := R₀), Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => by split_ifs <;> ring
        rw [h1]
        calc (∑ x ∈ I, w x * ∑ y ∈ R₀.filter (G.Adj x), w y)
            ≤ ∑ x ∈ I, w x * r := by
              refine Finset.sum_le_sum fun x _ => ?_
              have hmem : R₀.filter (G.Adj x) ∈ indepR₀ :=
                Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _),
                  OMA.R_Erdos128_erdos_128_R2.filter_adj_indep hTF R₀ x⟩
              have hle : (∑ y ∈ R₀.filter (G.Adj x), w y) ≤ β := hJ_max _ hmem
              nlinarith [hw0 x]
          _ = α * r := by rw [← Finset.sum_mul]
      let c₁ : ℝ := r / m₀
      have hc₁0 : 0 ≤ c₁ := by positivity
      have hc₁1 : c₁ ≤ 1 := by dsimp only [c₁]; rw [div_le_one hm₀_pos]; dsimp only [r]; linarith
      let s₁ : V → ℝ := fun z => if z ∈ I then w z else if z ∈ R₀ then c₁ * w z else 0
      by_cases hs₁ : 25 * (∑ x : V, ∑ y : V, if G.Adj x y then s₁ x * s₁ y else 0) ≤ 1
      · refine ⟨s₁, ?_, ?_, hs₁⟩
        · intro z
          by_cases hzI : z ∈ I
          · simp only [s₁, if_pos hzI]; exact ⟨hw0 z, le_refl _⟩
          · by_cases hzR : z ∈ R₀
            · simp only [s₁, if_neg hzI, if_pos hzR]
              exact ⟨mul_nonneg hc₁0 (hw0 z), by nlinarith [hw0 z]⟩
            · simp only [s₁, if_neg hzI, if_neg hzR]; exact ⟨le_refl 0, hw0 z⟩
        · have hsum : (∑ z : V, s₁ z) = ∑ z ∈ I ∪ R₀, s₁ z := by
            symm; refine Finset.sum_subset (Finset.subset_univ _) fun z _ hz => ?_
            simp only [Finset.mem_union, not_or] at hz
            simp only [s₁, if_neg hz.1, if_neg hz.2]
          rw [hsum, Finset.sum_union hdisj_IR₀]
          have h1 : (∑ z ∈ I, s₁ z) = α := Finset.sum_congr rfl fun z hz => by simp only [s₁, if_pos hz]
          have h2 : (∑ z ∈ R₀, s₁ z) = c₁ * m₀ := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun z hz => ?_
            simp only [s₁, if_neg (Finset.disjoint_right.mp hdisj_IR₀ hz), if_pos hz]
          rw [h1, h2]
          have hc1m : c₁ * m₀ = r := div_mul_cancel₀ _ (ne_of_gt hm₀_pos)
          rw [hc1m]; dsimp only [r]; ring
      · push Not at hs₁
        let c₂ : ℝ := r₁ / m₀
        have hr₁_pos : 0 < r₁ := by linarith
        have hc₂0 : 0 ≤ c₂ := by positivity
        have hc₂1 : c₂ ≤ 1 := by dsimp only [c₂]; rw [div_le_one hm₀_pos]; dsimp only [r₁]; linarith
        let s₂ : V → ℝ := fun z => if z ∈ R₁ then w z else if z ∈ R₀ then c₂ * w z else 0
        refine ⟨s₂, ?_, ?_, ?_⟩
        · intro z
          by_cases hz1 : z ∈ R₁
          · simp only [s₂, if_pos hz1]; exact ⟨hw0 z, le_refl _⟩
          · by_cases hzR : z ∈ R₀
            · simp only [s₂, if_neg hz1, if_pos hzR]
              exact ⟨mul_nonneg hc₂0 (hw0 z), by nlinarith [hw0 z]⟩
            · simp only [s₂, if_neg hz1, if_neg hzR]; exact ⟨le_refl 0, hw0 z⟩
        · have hsum : (∑ z : V, s₂ z) = ∑ z ∈ R₁ ∪ R₀, s₂ z := by
            symm; refine Finset.sum_subset (Finset.subset_univ _) fun z _ hz => ?_
            simp only [Finset.mem_union, not_or] at hz
            simp only [s₂, if_neg hz.1, if_neg hz.2]
          rw [hsum, Finset.sum_union hdisj_R₁R₀]
          have h1 : (∑ z ∈ R₁, s₂ z) = m₁ := Finset.sum_congr rfl fun z hz => by simp only [s₂, if_pos hz]
          have h2 : (∑ z ∈ R₀, s₂ z) = c₂ * m₀ := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun z hz => ?_
            simp only [s₂, if_neg (Finset.disjoint_right.mp hdisj_R₁R₀ hz), if_pos hz]
          rw [h1, h2]
          have hc2m : c₂ * m₀ = r₁ := div_mul_cancel₀ _ (ne_of_gt hm₀_pos)
          rw [hc2m]; dsimp only [r₁]; ring
        · by_contra hs₂
          push Not at hs₂
          have hq1 := quad_indep_plus_scaled G w I R₀ hdisj_IR₀ hI c₁
          have hq2 := quad_indep_plus_scaled G w R₁ R₀ hdisj_R₁R₀ hR₁_indep c₂
          have hgt1 : α * r < 2 * c₁ * e₁ + c₁ ^ 2 * d₀ := by linarith
          have hgt2 : α * r < 2 * c₂ * e₂ + c₂ ^ 2 * d₀ := by linarith
          have hF3 : α * m₀ ^ 2 < 2 * m₀ * e₁ + r * d₀ := by
            have hm2 : 0 < m₀ ^ 2 := sq_pos_of_pos hm₀_pos
            have h1 : α * r * m₀ ^ 2 < (2 * c₁ * e₁ + c₁ ^ 2 * d₀) * m₀ ^ 2 :=
              mul_lt_mul_of_pos_right hgt1 hm2
            have h2 : (2 * c₁ * e₁ + c₁ ^ 2 * d₀) * m₀ ^ 2 = r * (2 * m₀ * e₁ + r * d₀) := by
              dsimp only [c₁]; field_simp [ne_of_gt hm₀_pos]
            rw [h2] at h1
            nlinarith
          have hF4 : α * r * m₀ ^ 2 < 2 * r₁ * m₀ * e₂ + r₁ ^ 2 * d₀ := by
            have hm2 : 0 < m₀ ^ 2 := sq_pos_of_pos hm₀_pos
            have h1 : α * r * m₀ ^ 2 < (2 * c₂ * e₂ + c₂ ^ 2 * d₀) * m₀ ^ 2 :=
              mul_lt_mul_of_pos_right hgt2 hm2
            have h2 : (2 * c₂ * e₂ + c₂ ^ 2 * d₀) * m₀ ^ 2 = 2 * r₁ * m₀ * e₂ + r₁ ^ 2 * d₀ := by
              dsimp only [c₂]; field_simp [ne_of_gt hm₀_pos]
            linarith
          have hw1_pos : 0 < r₁ * (m₀ + r) := mul_pos hr₁_pos (by linarith)
          have hc1 := mul_lt_mul_of_pos_left hF3 hw1_pos
          have hc2 := mul_lt_mul_of_pos_left hF4 hr_pos
          have hadd := add_lt_add hc1 hc2
          have hnn1 : 0 ≤ 2 * m₀ * r₁ * r := by positivity
          have hnn2 : 0 ≤ 2 * m₀ ^ 2 * r₁ := by positivity
          have hterm1 : 2 * m₀ * r₁ * r * (e₁ + e₂ + d₀) ≤ 2 * m₀ * r₁ * r * (m₀ * α) :=
            mul_le_mul_of_nonneg_left hF1 hnn1
          have hterm2 : 2 * m₀ ^ 2 * r₁ * e₁ ≤ 2 * m₀ ^ 2 * r₁ * (α * r) :=
            mul_le_mul_of_nonneg_left hF2 hnn2
          have hrhs_id : r₁ * (m₀ + r) * (2 * m₀ * e₁ + r * d₀) + r * (2 * r₁ * m₀ * e₂ + r₁ ^ 2 * d₀) =
              2 * m₀ * r₁ * r * (e₁ + e₂ + d₀) + 2 * m₀ ^ 2 * r₁ * e₁ +
              r * r₁ * d₀ * (r + r₁ - m₀) := by ring
          have hsum_rr1 : r + r₁ = m₀ := by dsimp only [r, r₁]; linarith
          have hzero_term : r * r₁ * d₀ * (r + r₁ - m₀) = 0 := by
            rw [show r + r₁ - m₀ = 0 by linarith [hsum_rr1], mul_zero]
          have hlhs_ge : 4 * α * m₀ ^ 2 * r₁ * r ≤
              r₁ * (m₀ + r) * (α * m₀ ^ 2) + r * (α * r * m₀ ^ 2) := by
            have hdiff : r₁ * (m₀ + r) * (α * m₀ ^ 2) + r * (α * r * m₀ ^ 2) - 4 * α * m₀ ^ 2 * r₁ * r =
                α * m₀ ^ 2 * (r₁ - r) ^ 2 := by
              rw [← hsum_rr1]; ring
            have hsq : 0 ≤ α * m₀ ^ 2 * (r₁ - r) ^ 2 := by positivity
            linarith
          have h4eq : 2 * m₀ * r₁ * r * (m₀ * α) + 2 * m₀ ^ 2 * r₁ * (α * r) =
              4 * α * m₀ ^ 2 * r₁ * r := by ring
          linarith

/- ### Part 3: Generic Involution Pullback Helpers -/

lemma pullback_invol {V : Type} [Fintype V] [DecidableEq V]
    (R : V → V → Prop) [DecidableRel R]
    (σ : V → V) (hinvol : Function.Involutive σ)
    (hadj : ∀ x y, R (σ x) (σ y) ↔ R x y)
    (w : V → ℝ)
    (hs : ∃ s : V → ℝ,
      (∀ z, 0 ≤ s z ∧ s z ≤ w (σ z)) ∧
      (∑ z, s z) = 1 / 2 ∧
      25 * (∑ x, ∑ y, if R x y then s x * s y else 0) ≤ 1) :
    ∃ s : V → ℝ,
      (∀ z, 0 ≤ s z ∧ s z ≤ w z) ∧
      (∑ z, s z) = 1 / 2 ∧
      25 * (∑ x, ∑ y, if R x y then s x * s y else 0) ≤ 1 := by
  obtain ⟨s, hs0, hsum, hq⟩ := hs
  let e : V ≃ V := hinvol.toPerm
  refine ⟨fun z => s (σ z), ?_, ?_, ?_⟩
  · intro z
    have h := hs0 (σ z)
    rw [hinvol z] at h
    exact h
  · rw [← hsum]
    exact Fintype.sum_equiv e (fun z => s (σ z)) s (fun _ => rfl)
  · have hqeq : (∑ x, ∑ y, if R x y then s (σ x) * s (σ y) else 0) =
        ∑ x, ∑ y, if R x y then s x * s y else 0 := by
      have h1 : ∀ x, (∑ y, if R x y then s (σ x) * s (σ y) else 0) =
          ∑ y, if R (σ x) y then s (σ x) * s y else 0 := by
        intro x
        refine Fintype.sum_equiv e _ _ fun y => ?_
        change (if R x y then s (σ x) * s (σ y) else 0) =
          if R (σ x) (σ y) then s (σ x) * s (σ y) else 0
        by_cases h : R x y
        · rw [if_pos h, if_pos ((hadj x y).mpr h)]
        · rw [if_neg h, if_neg (fun h' => h ((hadj x y).mp h'))]
      simp_rw [h1]
      exact Fintype.sum_equiv e _ _ (fun _ => rfl)
    rw [hqeq]; exact hq

lemma sum_invol_eq {V : Type} [Fintype V]
    (σ : V → V) (hinvol : Function.Involutive σ) (f : V → ℝ) :
    (∑ z, f (σ z)) = ∑ z, f z :=
  Fintype.sum_equiv hinvol.toPerm (fun z => f (σ z)) f (fun _ => rfl)

lemma quad_invol_eq {V : Type} [Fintype V]
    (R : V → V → Prop) [DecidableRel R]
    (σ : V → V) (hinvol : Function.Involutive σ)
    (hadj : ∀ x y, R (σ x) (σ y) ↔ R x y) (w : V → ℝ) :
    (∑ x, ∑ y, if R x y then w (σ x) * w (σ y) else 0) =
      ∑ x, ∑ y, if R x y then w x * w y else 0 := by
  let e := hinvol.toPerm
  have h1 : ∀ x, (∑ y, if R x y then w (σ x) * w (σ y) else 0) =
      ∑ y, if R (σ x) y then w (σ x) * w y else 0 := by
    intro x
    refine Fintype.sum_equiv e _ _ fun y => ?_
    change (if R x y then w (σ x) * w (σ y) else 0) =
      if R (σ x) (σ y) then w (σ x) * w (σ y) else 0
    by_cases h : R x y
    · rw [if_pos h, if_pos ((hadj x y).mpr h)]
    · rw [if_neg h, if_neg (fun h' => h ((hadj x y).mp h'))]
  simp_rw [h1]
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

lemma indep_invol_lt {V : Type} [DecidableEq V]
    (R : V → V → Prop) (σ : V → V) (hinvol : Function.Involutive σ)
    (hadj : ∀ x y, R (σ x) (σ y) ↔ R x y) (w : V → ℝ)
    (hα : ∀ I : Finset V, (∀ x ∈ I, ∀ y ∈ I, ¬ R x y) → (∑ z ∈ I, w z) < 2 / 5) :
    ∀ I : Finset V, (∀ x ∈ I, ∀ y ∈ I, ¬ R x y) → (∑ z ∈ I, w (σ z)) < 2 / 5 := by
  intro I hI
  have himg : (∑ z ∈ I, w (σ z)) = ∑ z ∈ I.image σ, w z := by
    symm
    exact Finset.sum_image (fun a _ b _ hab => hinvol.injective hab)
  rw [himg]
  apply hα (I.image σ)
  intro x hx y hy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
  intro h
  exact hI a ha b hb ((hadj a b).mp h)

/- ### Part 4: Main Reduction Theorem -/

set_option maxHeartbeats 1000000 in
theorem main : H1 → H2 → OMA.R_Erdos128_erdos_128_R2_H2_R2_H2_R1.H1 := by
  intro h1 h2 w hw0 hw1 _ _ _ _ _ _
  classical
  let R : Fin 5 ⊕ Fin 8 → Fin 5 ⊕ Fin 8 → Prop := fun x y =>
    match x, y with
    | Sum.inl p, Sum.inl q =>
        2 ≤ (q.val + 5 - p.val) % 5 ∧ (q.val + 5 - p.val) % 5 ≤ 3
    | Sum.inl p, Sum.inr t =>
        ((t.val = 0 ∨ t.val = 3) ∧ p.val < 2) ∨
        ((t.val = 4 ∨ t.val = 1) ∧ 2 ≤ p.val ∧ p.val < 4) ∨
        ((t.val = 2 ∨ t.val = 5) ∧ 4 ≤ p.val)
    | Sum.inr t, Sum.inl p =>
        ((t.val = 0 ∨ t.val = 3) ∧ p.val < 2) ∨
        ((t.val = 4 ∨ t.val = 1) ∧ 2 ≤ p.val ∧ p.val < 4) ∨
        ((t.val = 2 ∨ t.val = 5) ∧ 4 ≤ p.val)
    | Sum.inr t₁, Sum.inr t₂ =>
        (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
        (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
        (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
        (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
        (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))
  have hR_symm : Symmetric R := by
    intro x y h
    have h' := OMA.R_Erdos128_erdos_128_R2_H2_R2_H2_R1.vega_adj_symm (i := 2) (by omega) x y
      (by cases x <;> cases y <;> simpa [R] using h)
    cases x <;> cases y <;> simpa [R] using h'
  have hR_irrefl : Irreflexive R := by
    intro x
    cases x with
    | inl p => dsimp only [R]; fin_cases p <;> decide
    | inr t => dsimp only [R]; fin_cases t <;> decide
  let G : SimpleGraph (Fin 5 ⊕ Fin 8) :=
    { Adj := R, symm := ⟨hR_symm⟩, loopless := ⟨hR_irrefl⟩ }
  have hG_TF : G.CliqueFree 3 :=
    OMA.R_Erdos128_erdos_128_R2_H2_R2_H2_R1.vega_cliqueFree_three G 2 (by omega) id
      (fun x y h => by cases x <;> cases y <;> simpa [G, R] using h)
  suffices hgoal : ∃ s : Fin 5 ⊕ Fin 8 → ℝ,
      (∀ z, 0 ≤ s z ∧ s z ≤ w z) ∧
      (∑ z, s z) = 1 / 2 ∧
      25 * (∑ x, ∑ y, if R x y then s x * s y else 0) ≤ 1 by
    obtain ⟨s, hs0, hsum, hq⟩ := hgoal
    refine ⟨s, hs0, hsum, ?_⟩
    convert hq using 2
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    cases x <;> cases y <;> dsimp [R] <;> split_ifs <;> simp_all
  -- Step 1: Continuous Razborov Theorem A eliminates any independent set of weight ≥ 2/5
  by_cases hα : ∃ I : Finset (Fin 5 ⊕ Fin 8),
      (∀ x ∈ I, ∀ y ∈ I, ¬ R x y) ∧ 2 / 5 ≤ ∑ z ∈ I, w z
  · obtain ⟨I, hI, hwI⟩ := hα
    exact exists_sparse_half_of_indep_ge_two_fifths G hG_TF w hw0 hw1 I hI hwI
  push Not at hα
  -- Step 2: Continuous Random-Half Cutoff eliminates 25 * wᵀ A w ≤ 4
  by_cases hq : 25 * (∑ x, ∑ y, if R x y then w x * w y else 0) ≤ 4
  · exact exists_sparse_half_of_quad_le G w hw0 hw1 hq
  push Not at hq
  -- Involution σ₁: swaps E₀ ↔ E₁
  let σ₁ : Fin 5 ⊕ Fin 8 → Fin 5 ⊕ Fin 8 := fun z =>
    match z with
    | Sum.inl p => Sum.inl p
    | Sum.inr t => Sum.inr (
        if t.val = 0 then ⟨3, by omega⟩
        else if t.val = 3 then ⟨0, by omega⟩
        else if t.val = 1 then ⟨4, by omega⟩
        else if t.val = 4 then ⟨1, by omega⟩
        else if t.val = 2 then ⟨5, by omega⟩
        else if t.val = 5 then ⟨2, by omega⟩
        else if t.val = 6 then ⟨7, by omega⟩
        else ⟨6, by omega⟩)
  -- Involution σ₂: reverses C₅, preserving E₀ and E₁
  let σ₂ : Fin 5 ⊕ Fin 8 → Fin 5 ⊕ Fin 8 := fun z =>
    match z with
    | Sum.inl p => Sum.inl (
        if p.val = 0 then ⟨3, by omega⟩
        else if p.val = 3 then ⟨0, by omega⟩
        else if p.val = 1 then ⟨2, by omega⟩
        else if p.val = 2 then ⟨1, by omega⟩
        else ⟨4, by omega⟩)
    | Sum.inr t => Sum.inr (
        if t.val = 0 then ⟨4, by omega⟩
        else if t.val = 4 then ⟨0, by omega⟩
        else if t.val = 1 then ⟨3, by omega⟩
        else if t.val = 3 then ⟨1, by omega⟩
        else t)
  have hσ₁_invol : Function.Involutive σ₁ := by
    intro x; cases x with
    | inl p => rfl
    | inr t => fin_cases t <;> rfl
  have hσ₂_invol : Function.Involutive σ₂ := by
    intro x; cases x with
    | inl p => fin_cases p <;> rfl
    | inr t => fin_cases t <;> rfl
  have hσ₁_adj : ∀ x y, R (σ₁ x) (σ₁ y) ↔ R x y := by
    intro x y; cases x with
    | inl p => cases y with
      | inl q => rfl
      | inr t => dsimp only [R, σ₁]; fin_cases p <;> fin_cases t <;> decide
    | inr t => cases y with
      | inl p => dsimp only [R, σ₁]; fin_cases t <;> fin_cases p <;> decide
      | inr s => dsimp only [R, σ₁]; fin_cases t <;> fin_cases s <;> decide
  have hσ₂_adj : ∀ x y, R (σ₂ x) (σ₂ y) ↔ R x y := by
    intro x y; cases x with
    | inl p => cases y with
      | inl q => dsimp only [R, σ₂]; fin_cases p <;> fin_cases q <;> decide
      | inr t => dsimp only [R, σ₂]; fin_cases p <;> fin_cases t <;> decide
    | inr t => cases y with
      | inl p => dsimp only [R, σ₂]; fin_cases t <;> fin_cases p <;> decide
      | inr s => dsimp only [R, σ₂]; fin_cases t <;> fin_cases s <;> decide
  have solve_sym : ∀ u : Fin 5 ⊕ Fin 8 → ℝ,
      (∀ z, 0 ≤ u z) →
      (∑ z, u z) = 1 →
      (∀ I : Finset (Fin 5 ⊕ Fin 8), (∀ x ∈ I, ∀ y ∈ I, ¬ R x y) → (∑ z ∈ I, u z) < 2 / 5) →
      4 < 25 * (∑ x, ∑ y, if R x y then u x * u y else 0) →
      u (Sum.inr 0) + u (Sum.inr 2) + u (Sum.inr 4) + u (Sum.inr 7) ≤
        u (Sum.inr 1) + u (Sum.inr 3) + u (Sum.inr 5) + u (Sum.inr 6) →
      u (Sum.inl 0) + u (Sum.inl 1) ≤ u (Sum.inl 2) + u (Sum.inl 3) →
      ∃ s : Fin 5 ⊕ Fin 8 → ℝ,
        (∀ z, 0 ≤ s z ∧ s z ≤ u z) ∧
        (∑ z, s z) = 1 / 2 ∧
        25 * (∑ x, ∑ y, if R x y then s x * s y else 0) ≤ 1 := by
    intro u hu0 hu1 huα huq hs1 hs2
    by_cases hL : (∑ p : Fin 5, u (Sum.inl p)) ≤ 1 / 3
    · exact h1 u hu0 hu1 huα huq hs1 hs2 hL
    · push Not at hL
      exact h2 u hu0 hu1 huα huq hs1 hs2 hL
  have solve_sym1 : ∀ u : Fin 5 ⊕ Fin 8 → ℝ,
      (∀ z, 0 ≤ u z) →
      (∑ z, u z) = 1 →
      (∀ I : Finset (Fin 5 ⊕ Fin 8), (∀ x ∈ I, ∀ y ∈ I, ¬ R x y) → (∑ z ∈ I, u z) < 2 / 5) →
      4 < 25 * (∑ x, ∑ y, if R x y then u x * u y else 0) →
      u (Sum.inr 0) + u (Sum.inr 2) + u (Sum.inr 4) + u (Sum.inr 7) ≤
        u (Sum.inr 1) + u (Sum.inr 3) + u (Sum.inr 5) + u (Sum.inr 6) →
      ∃ s : Fin 5 ⊕ Fin 8 → ℝ,
        (∀ z, 0 ≤ s z ∧ s z ≤ u z) ∧
        (∑ z, s z) = 1 / 2 ∧
        25 * (∑ x, ∑ y, if R x y then s x * s y else 0) ≤ 1 := by
    intro u hu0 hu1 huα huq hs1
    by_cases hs2 : u (Sum.inl 0) + u (Sum.inl 1) ≤ u (Sum.inl 2) + u (Sum.inl 3)
    · exact solve_sym u hu0 hu1 huα huq hs1 hs2
    · push Not at hs2
      apply pullback_invol R σ₂ hσ₂_invol hσ₂_adj u
      apply solve_sym (fun z => u (σ₂ z))
      · intro z; exact hu0 (σ₂ z)
      · rw [sum_invol_eq σ₂ hσ₂_invol]; exact hu1
      · exact indep_invol_lt R σ₂ hσ₂_invol hσ₂_adj u huα
      · rw [quad_invol_eq R σ₂ hσ₂_invol hσ₂_adj]; exact huq
      · change u (Sum.inr 4) + u (Sum.inr 2) + u (Sum.inr 0) + u (Sum.inr 7) ≤
          u (Sum.inr 3) + u (Sum.inr 1) + u (Sum.inr 5) + u (Sum.inr 6)
        linarith
      · change u (Sum.inl 3) + u (Sum.inl 2) ≤ u (Sum.inl 1) + u (Sum.inl 0)
        linarith
  by_cases hs1 : w (Sum.inr 0) + w (Sum.inr 2) + w (Sum.inr 4) + w (Sum.inr 7) ≤
      w (Sum.inr 1) + w (Sum.inr 3) + w (Sum.inr 5) + w (Sum.inr 6)
  · exact solve_sym1 w hw0 hw1 hα hq hs1
  · push Not at hs1
    apply pullback_invol R σ₁ hσ₁_invol hσ₁_adj w
    apply solve_sym1 (fun z => w (σ₁ z))
    · intro z; exact hw0 (σ₁ z)
    · rw [sum_invol_eq σ₁ hσ₁_invol]; exact hw1
    · exact indep_invol_lt R σ₁ hσ₁_invol hσ₁_adj w hα
    · rw [quad_invol_eq R σ₁ hσ₁_invol hσ₁_adj]; exact hq
    · change w (Sum.inr 3) + w (Sum.inr 5) + w (Sum.inr 1) + w (Sum.inr 6) ≤
        w (Sum.inr 4) + w (Sum.inr 0) + w (Sum.inr 2) + w (Sum.inr 7)
      linarith

end OMA.R_Erdos128_erdos_128_R2_H2_R2_H2_R1_H1_R1
