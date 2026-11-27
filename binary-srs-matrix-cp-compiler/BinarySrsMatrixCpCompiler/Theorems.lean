/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BinarySrsMatrixCpCompiler.Defs

/-!
# Proofs for the Binary SRS Matrix/Critical-Pair Compiler (Pure `Init`)

Newman's lemma, matrix-interpretation termination soundness, critical-pair completeness, master
certificate soundness `cert_sound`, the Church-Rosser word-problem compiler, the Euler-Fermat
confluence dichotomy for `ampSys`, the infinite Mersenne/Fermat residue families, and the
kernel-checked sharpness and mutation-rejection tests.
-/

namespace CertComp16

/-! ## Section 1: Core Binary String Rewriting Theory -/

/-! ### Basic Closure & Congruence Lemmas -/

theorem Steps.single {R : SRS} {u v : Word} (h : Step R u v) : Steps R u v :=
  .tail h (.refl v)

theorem Steps.trans {R : SRS} {u v w : Word} (h₁ : Steps R u v) (h₂ : Steps R v w) :
    Steps R u w := by
  induction h₁ with
  | refl _ => exact h₂
  | tail hs _ ih => exact .tail hs (ih h₂)

theorem Step.context {R : SRS} (p s : Word) {u v : Word} (h : Step R u v) :
    Step R (p ++ u ++ s) (p ++ v ++ s) := by
  cases h with
  | mk p' s' l r hmem =>
    have h1 : p ++ (p' ++ l ++ s') ++ s = (p ++ p') ++ l ++ (s' ++ s) := by
      simp [List.append_assoc]
    have h2 : p ++ (p' ++ r ++ s') ++ s = (p ++ p') ++ r ++ (s' ++ s) := by
      simp [List.append_assoc]
    rw [h1, h2]
    exact Step.mk (p ++ p') (s' ++ s) l r hmem

theorem Steps.context {R : SRS} (p s : Word) {u v : Word} (h : Steps R u v) :
    Steps R (p ++ u ++ s) (p ++ v ++ s) := by
  induction h with
  | refl _ => exact .refl _
  | tail hs _ ih => exact .tail (hs.context p s) ih

theorem Joinable.refl {R : SRS} (x : Word) : Joinable R x x :=
  ⟨x, .refl x, .refl x⟩

theorem Joinable.symm {R : SRS} {x y : Word} (h : Joinable R x y) : Joinable R y x :=
  let ⟨z, hx, hy⟩ := h; ⟨z, hy, hx⟩

theorem Joinable.context {R : SRS} (p s : Word) {x y : Word} (h : Joinable R x y) :
    Joinable R (p ++ x ++ s) (p ++ y ++ s) :=
  let ⟨z, hx, hy⟩ := h; ⟨p ++ z ++ s, hx.context p s, hy.context p s⟩

theorem Steps.nf_eq {R : SRS} {u v : Word} (h : Steps R u v) (hnf : IsNormalForm R u) :
    u = v := by
  cases h with
  | refl _ => rfl
  | tail hs _ => exact absurd hs (hnf _)

theorem Convertible.of_steps {R : SRS} {u v : Word} (h : Steps R u v) : Convertible R u v := by
  induction h with
  | refl _ => exact .refl _
  | tail hs _ ih => exact .fwd hs ih

theorem Convertible.trans {R : SRS} {u v w : Word}
    (h₁ : Convertible R u v) (h₂ : Convertible R v w) : Convertible R u w := by
  induction h₁ with
  | refl _ => exact h₂
  | fwd hs _ ih => exact .fwd hs (ih h₂)
  | bwd hs _ ih => exact .bwd hs (ih h₂)

theorem Convertible.symm {R : SRS} {u v : Word} (h : Convertible R u v) : Convertible R v u := by
  induction h with
  | refl _ => exact .refl _
  | fwd hs _ ih => exact ih.trans (.bwd hs (.refl _))
  | bwd hs _ ih => exact ih.trans (.fwd hs (.refl _))

/-- Newman's Lemma: Termination + Local Confluence implies Global Confluence (constructive). -/
theorem newman {R : SRS} (hTerm : Terminating R) (hLoc : LocallyConfluent R) : Confluent R := by
  intro u
  have hAcc := hTerm.apply u
  induction hAcc with
  | intro x _ ih =>
    intro v₁ v₂ h₁ h₂
    cases h₁ with
    | refl _ => exact ⟨v₂, h₂, .refl v₂⟩
    | tail step₁ rest₁ =>
      rename_i w₁
      cases h₂ with
      | refl _ => exact ⟨v₁, .refl v₁, .tail step₁ rest₁⟩
      | tail step₂ rest₂ =>
        rename_i w₂
        obtain ⟨z₀, hz₁, hz₂⟩ := hLoc x w₁ w₂ step₁ step₂
        obtain ⟨z₁, hv₁z₁, hz₀z₁⟩ := ih w₁ step₁ v₁ z₀ rest₁ hz₁
        have hw₂z₁ : Steps R w₂ z₁ := hz₂.trans hz₀z₁
        obtain ⟨z₂, hz₁z₂, hv₂z₂⟩ := ih w₂ step₂ z₁ v₂ hw₂z₁ rest₂
        exact ⟨z₂, hv₁z₁.trans hz₁z₂, hv₂z₂⟩

/-- Church-Rosser property from Confluence: Convertible u v ↔ Joinable u v. -/
theorem confluent_church_rosser {R : SRS} (hConf : Confluent R) {u v : Word}
    (hConv : Convertible R u v) : Joinable R u v := by
  induction hConv with
  | refl w => exact .refl w
  | fwd hs _ ih =>
    obtain ⟨z, hz₁, hz₂⟩ := ih
    exact ⟨z, .tail hs hz₁, hz₂⟩
  | bwd hs _ ih =>
    obtain ⟨z, hz₁, hz₂⟩ := ih
    obtain ⟨z', h1, h2⟩ := hConf _ _ _ (.single hs) hz₁
    exact ⟨z', h1, hz₂.trans h2⟩

theorem joinable_of_convertible_nf {R : SRS} (hConf : Confluent R) {u v : Word}
    (hConv : Convertible R u v) (hu : IsNormalForm R u) (hv : IsNormalForm R v) : u = v := by
  obtain ⟨z, hz₁, hz₂⟩ := confluent_church_rosser hConf hConv
  rw [hz₁.nf_eq hu, hz₂.nf_eq hv]

/-! ## Section 2: Layered Arbitrary-Dimension Matrix-Weight Termination Engine -/

theorem sumRange_congr {n : Nat} {f g : Nat → Nat} (h : ∀ k < n, f k = g k) :
    sumRange n f = sumRange n g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [sumRange]
    rw [ih (fun k hk => h k (Nat.lt_succ_of_lt hk)), h m (Nat.lt_succ_self m)]

theorem sumRange_mono {n : Nat} {f g : Nat → Nat} (h : ∀ k < n, f k ≤ g k) :
    sumRange n f ≤ sumRange n g := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ m ih =>
    simp only [sumRange]
    exact Nat.add_le_add (ih (fun k hk => h k (Nat.lt_succ_of_lt hk))) (h m (Nat.lt_succ_self m))

theorem sumRange_strict_at {n k₀ : Nat} {f g : Nat → Nat}
    (hk₀ : k₀ < n) (hle : ∀ k < n, f k ≤ g k) (hlt : f k₀ < g k₀) :
    sumRange n f < sumRange n g := by
  induction n with
  | zero => cases hk₀
  | succ m ih =>
    simp only [sumRange]
    by_cases hEq : k₀ = m
    · subst hEq
      exact Nat.add_lt_add_of_le_of_lt
        (sumRange_mono (fun k hk => hle k (Nat.lt_succ_of_lt hk))) hlt
    · have hk' : k₀ < m := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hk₀) hEq
      exact Nat.add_lt_add_of_lt_of_le
        (ih hk' (fun k hk => hle k (Nat.lt_succ_of_lt hk))) (hle m (Nat.lt_succ_self m))

theorem sumRange_ge_at {n k₀ : Nat} {f : Nat → Nat} (hk₀ : k₀ < n) :
    f k₀ ≤ sumRange n f := by
  induction n with
  | zero => cases hk₀
  | succ m ih =>
    simp only [sumRange]
    by_cases hEq : k₀ = m
    · subst hEq; omega
    · have hk' : k₀ < m := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hk₀) hEq
      have := ih hk'
      omega

theorem sumRange_mul_left {n c : Nat} {f : Nat → Nat} :
    c * sumRange n f = sumRange n (fun k => c * f k) := by
  induction n with
  | zero => simp [sumRange]
  | succ m ih => simp [sumRange, Nat.mul_add, ih]

theorem sumRange_mul_right {n c : Nat} {f : Nat → Nat} :
    sumRange n f * c = sumRange n (fun k => f k * c) := by
  induction n with
  | zero => simp [sumRange]
  | succ m ih => simp [sumRange, Nat.add_mul, ih]

theorem sumRange_add {n : Nat} {f g : Nat → Nat} :
    sumRange n (fun k => f k + g k) = sumRange n f + sumRange n g := by
  induction n with
  | zero => simp [sumRange]
  | succ m ih => simp [sumRange, ih]; omega

theorem sumRange_swap {m n : Nat} {f : Nat → Nat → Nat} :
    sumRange m (fun i => sumRange n (fun j => f i j)) =
    sumRange n (fun j => sumRange m (fun i => f i j)) := by
  induction m with
  | zero =>
    change 0 = sumRange n (fun _ => 0)
    induction n with
    | zero => rfl
    | succ k ih =>
      show 0 = sumRange k (fun _ => 0) + 0
      rw [← ih]
  | succ m' ih =>
    change sumRange m' (fun i => sumRange n (fun j => f i j)) + sumRange n (fun j => f m' j) =
           sumRange n (fun j => sumRange m' (fun i => f i j) + f m' j)
    rw [ih, sumRange_add]

theorem sumRange_zero {n : Nat} {f : Nat → Nat} (h : ∀ k < n, f k = 0) :
    sumRange n f = 0 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [sumRange, ih (fun k hk => h k (Nat.lt_succ_of_lt hk)), h m (Nat.lt_succ_self m)]

theorem sumRange_delta_left {n i : Nat} {f : Nat → Nat} (hi : i < n) :
    sumRange n (fun k => (if i = k then 1 else 0) * f k) = f i := by
  induction n with
  | zero => cases hi
  | succ m ih =>
    simp only [sumRange]
    by_cases hEq : i = m
    · subst hEq
      have hz : sumRange i (fun k => (if i = k then 1 else 0) * f k) = 0 :=
        sumRange_zero (fun k hk => by
          have hne : i ≠ k := Nat.ne_of_gt hk
          simp [hne])
      simp [hz]
    · have hi' : i < m := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hi) hEq
      simp [hEq, ih hi']

theorem sumRange_delta_right {n j : Nat} {f : Nat → Nat} (hj : j < n) :
    sumRange n (fun k => f k * (if k = j then 1 else 0)) = f j := by
  induction n with
  | zero => cases hj
  | succ m ih =>
    simp only [sumRange]
    by_cases hEq : m = j
    · subst hEq
      have hz : sumRange m (fun k => f k * (if k = m then 1 else 0)) = 0 :=
        sumRange_zero (fun k hk => by
          have hne : k ≠ m := Nat.ne_of_lt hk
          simp [hne])
      simp [hz]
    · have hj' : j < m := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hj) (Ne.symm hEq)
      simp [hEq, ih hj']

/-! ### Materialized `d × d` Natural-Number Matrices -/

/-! ### Helper Lemmas on `List.getD`, `List.map`, `List.range` -/

private theorem getD_map_lt {α β : Type} (f : α → β) (l : List α) (i : Nat) (da : α) (db : β)
    (hi : i < l.length) : (l.map f).getD i db = f (l.getD i da) := by
  induction l generalizing i with
  | nil => cases hi
  | cons a as ih =>
    cases i with
    | zero => rfl
    | succ i' =>
      simp only [List.map, List.getD_cons_succ]
      exact ih i' (Nat.lt_of_succ_lt_succ hi)

private theorem getD_range_lt (n i : Nat) (hi : i < n) :
    (List.range n).getD i 0 = i := by
  have h1 : (List.range n)[i]? = some i := List.getElem?_range hi
  simp [List.getD, h1]

theorem matGet_matId {d i j : Nat} (hi : i < d) (hj : j < d) :
    matGet (matId d) i j = if i = j then 1 else 0 := by
  unfold matGet matId
  have hlen : (List.range d).length = d := List.length_range
  rw [getD_map_lt _ (List.range d) i 0 [] (by omega)]
  rw [getD_range_lt d i hi]
  rw [getD_map_lt _ (List.range d) j 0 0 (by omega)]
  rw [getD_range_lt d j hj]
  by_cases h : i = j <;> simp [h]

theorem matGet_matMul {d i j : Nat} (A B : Mat) (hi : i < d) (hj : j < d) :
    matGet (matMul d A B) i j = sumRange d (fun k => matGet A i k * matGet B k j) := by
  change ((matMul d A B).getD i []).getD j 0 = _
  unfold matMul
  have hlen : (List.range d).length = d := List.length_range
  rw [getD_map_lt _ (List.range d) i 0 [] (by omega)]
  rw [getD_range_lt d i hi]
  rw [getD_map_lt _ (List.range d) j 0 0 (by omega)]
  rw [getD_range_lt d j hj]

theorem matId_wf (d : Nat) : MatWF d (matId d) := by
  constructor
  · simp [matId]
  · intro row hrow
    simp only [matId, List.mem_map, List.mem_range] at hrow
    rcases hrow with ⟨_, _, rfl⟩
    simp

theorem matMul_wf (d : Nat) (A B : Mat) : MatWF d (matMul d A B) := by
  constructor
  · simp [matMul]
  · intro row hrow
    simp only [matMul, List.mem_map, List.mem_range] at hrow
    rcases hrow with ⟨_, _, rfl⟩
    simp

theorem checkMatWF_sound {d : Nat} {M : Mat} (h : checkMatWF d M = true) : MatWF d M := by
  unfold checkMatWF at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact ⟨h.1, fun row hrow => h.2 row hrow⟩

theorem matEval_wf {d : Nat} {m0 m1 : Mat} (w : Word) : MatWF d (matEval d m0 m1 w) := by
  cases w with
  | nil => exact matId_wf d
  | cons _ _ => exact matMul_wf d _ _

theorem matEq_of_get {d : Nat} {A B : Mat} (hA : MatWF d A) (hB : MatWF d B)
    (h : ∀ i < d, ∀ j < d, matGet A i j = matGet B i j) : A = B := by
  have hAlen : A.length = d := hA.1
  have hBlen : B.length = d := hB.1
  apply List.ext_getElem
  · omega
  · intro i hiA hiB
    have hi : i < d := by omega
    have hrowA : A[i].length = d := hA.2 A[i] (List.getElem_mem hiA)
    have hrowB : B[i].length = d := hB.2 B[i] (List.getElem_mem hiB)
    apply List.ext_getElem
    · omega
    · intro j hjA hjB
      have hj : j < d := by omega
      have hget := h i hi j hj
      unfold matGet at hget
      have hAi : A.getD i [] = A[i] := by simp [List.getD, List.getElem?_eq_getElem hiA]
      have hBi : B.getD i [] = B[i] := by simp [List.getD, List.getElem?_eq_getElem hiB]
      rw [hAi, hBi] at hget
      have hAij : A[i].getD j 0 = A[i][j] := by simp [List.getD, List.getElem?_eq_getElem hjA]
      have hBij : B[i].getD j 0 = B[i][j] := by simp [List.getD, List.getElem?_eq_getElem hjB]
      rw [hAij, hBij] at hget
      exact hget

theorem matMul_id_left {d : Nat} {A : Mat} (hA : MatWF d A) :
    matMul d (matId d) A = A := by
  apply matEq_of_get (matMul_wf d _ _) hA
  intro i hi j hj
  rw [matGet_matMul _ _ hi hj]
  have h1 : sumRange d (fun k => matGet (matId d) i k * matGet A k j) =
            sumRange d (fun k => (if i = k then 1 else 0) * matGet A k j) :=
    sumRange_congr (fun k hk => by rw [matGet_matId hi hk])
  rw [h1, sumRange_delta_left hi]

theorem matMul_id_right {d : Nat} {A : Mat} (hA : MatWF d A) :
    matMul d A (matId d) = A := by
  apply matEq_of_get (matMul_wf d _ _) hA
  intro i hi j hj
  rw [matGet_matMul _ _ hi hj]
  have h1 : sumRange d (fun k => matGet A i k * matGet (matId d) k j) =
            sumRange d (fun k => matGet A i k * (if k = j then 1 else 0)) :=
    sumRange_congr (fun k hk => by rw [matGet_matId hk hj])
  rw [h1, sumRange_delta_right hj]

theorem matMul_assoc {d : Nat} (A B C : Mat) :
    matMul d (matMul d A B) C = matMul d A (matMul d B C) := by
  apply matEq_of_get (matMul_wf d _ _) (matMul_wf d _ _)
  intro i hi j hj
  rw [matGet_matMul _ _ hi hj, matGet_matMul _ _ hi hj]
  have hL : sumRange d (fun k => matGet (matMul d A B) i k * matGet C k j) =
            sumRange d (fun k => sumRange d (fun t => matGet A i t * matGet B t k * matGet C k j)) := by
    apply sumRange_congr
    intro k hk
    rw [matGet_matMul _ _ hi hk, sumRange_mul_right]
  have hR : sumRange d (fun t => matGet A i t * matGet (matMul d B C) t j) =
            sumRange d (fun t => sumRange d (fun k => matGet A i t * (matGet B t k * matGet C k j))) := by
    apply sumRange_congr
    intro t ht
    rw [matGet_matMul _ _ ht hj, sumRange_mul_left]
  rw [hL, hR, sumRange_swap]
  apply sumRange_congr; intro t _
  apply sumRange_congr; intro k _
  exact Nat.mul_assoc _ _ _

theorem matEval_append {d : Nat} {m0 m1 : Mat} (u v : Word) :
    matEval d m0 m1 (u ++ v) = matMul d (matEval d m0 m1 u) (matEval d m0 m1 v) := by
  induction u with
  | nil =>
    simp only [List.nil_append, matEval]
    exact (matMul_id_left (matEval_wf v)).symm
  | cons b u' ih =>
    simp only [List.cons_append, matEval, ih, matMul_assoc]

/-! ### Monotonicity & Top-Right Strict Compatibility -/

def MatLe (d : Nat) (A B : Mat) : Prop :=
  ∀ i < d, ∀ j < d, matGet A i j ≤ matGet B i j

theorem matGe_sound {d : Nat} {A B : Mat} (h : matGe d A B = true) : MatLe d B A := by
  unfold matGe at h
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h

theorem matGtTR_sound {d : Nat} {A B : Mat} (h : matGtTR d A B = true) :
    MatLe d B A ∧ matGet B 0 (d - 1) < matGet A 0 (d - 1) := by
  unfold matGtTR at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨matGe_sound h.1, h.2⟩

theorem matMul_mono_left {d : Nat} {A L R : Mat} (h : MatLe d R L) :
    MatLe d (matMul d A R) (matMul d A L) := by
  intro i hi j hj
  rw [matGet_matMul _ _ hi hj, matGet_matMul _ _ hi hj]
  exact sumRange_mono fun k hk => Nat.mul_le_mul_left _ (h k hk j hj)

theorem matMul_mono_right {d : Nat} {L R B : Mat} (h : MatLe d R L) :
    MatLe d (matMul d R B) (matMul d L B) := by
  intro i hi j hj
  rw [matGet_matMul _ _ hi hj, matGet_matMul _ _ hi hj]
  exact sumRange_mono fun k hk => Nat.mul_le_mul_right _ (h i hi k hk)

theorem matMul_strict_tr {d : Nat} {A L R B : Mat}
    (hd : 1 ≤ d)
    (hA : 1 ≤ matGet A 0 0)
    (hB : 1 ≤ matGet B (d - 1) (d - 1))
    (hle : MatLe d R L)
    (hlt : matGet R 0 (d - 1) < matGet L 0 (d - 1)) :
    matGet (matMul d (matMul d A R) B) 0 (d - 1) <
    matGet (matMul d (matMul d A L) B) 0 (d - 1) := by
  have h0 : 0 < d := by omega
  have hlast : d - 1 < d := by omega
  have hMidLe : MatLe d (matMul d A R) (matMul d A L) := matMul_mono_left hle
  have hMidLt : matGet (matMul d A R) 0 (d - 1) < matGet (matMul d A L) 0 (d - 1) := by
    rw [matGet_matMul _ _ h0 hlast, matGet_matMul _ _ h0 hlast]
    apply sumRange_strict_at h0
    · intro k hk; exact Nat.mul_le_mul_left _ (hle k hk (d - 1) hlast)
    · exact Nat.mul_lt_mul_of_pos_left hlt (by omega)
  rw [matGet_matMul _ _ h0 hlast, matGet_matMul _ _ h0 hlast]
  apply sumRange_strict_at hlast
  · intro k hk; exact Nat.mul_le_mul_right _ (hMidLe 0 h0 k hk)
  · exact Nat.mul_lt_mul_of_pos_right hMidLt (by omega)

theorem matEval_tl_pos {d : Nat} {m0 m1 : Mat} (hd : 1 ≤ d)
    (h0 : 1 ≤ matGet m0 0 0) (h1 : 1 ≤ matGet m1 0 0) (w : Word) :
    1 ≤ matGet (matEval d m0 m1 w) 0 0 := by
  have h0d : 0 < d := by omega
  induction w with
  | nil =>
    simp only [matEval]
    rw [matGet_matId h0d h0d]
    simp
  | cons b w' ih =>
    simp only [matEval]
    rw [matGet_matMul _ _ h0d h0d]
    have hge := sumRange_ge_at (n := d) (k₀ := 0)
      (f := fun k => matGet (if b then m1 else m0) 0 k * matGet (matEval d m0 m1 w') k 0) h0d
    have hb : 1 ≤ matGet (if b then m1 else m0) 0 0 := by cases b <;> assumption
    have hmul : 1 ≤ matGet (if b then m1 else m0) 0 0 * matGet (matEval d m0 m1 w') 0 0 :=
      Nat.mul_le_mul hb ih
    omega

theorem matEval_br_pos {d : Nat} {m0 m1 : Mat} (hd : 1 ≤ d)
    (h0 : 1 ≤ matGet m0 (d - 1) (d - 1)) (h1 : 1 ≤ matGet m1 (d - 1) (d - 1)) (w : Word) :
    1 ≤ matGet (matEval d m0 m1 w) (d - 1) (d - 1) := by
  have hlast : d - 1 < d := by omega
  induction w with
  | nil =>
    simp only [matEval]
    rw [matGet_matId hlast hlast]
    simp
  | cons b w' ih =>
    simp only [matEval]
    rw [matGet_matMul _ _ hlast hlast]
    have hge := sumRange_ge_at (n := d) (k₀ := d - 1)
      (f := fun k => matGet (if b then m1 else m0) (d - 1) k * matGet (matEval d m0 m1 w') k (d - 1)) hlast
    have hb : 1 ≤ matGet (if b then m1 else m0) (d - 1) (d - 1) := by cases b <;> assumption
    have hmul : 1 ≤ matGet (if b then m1 else m0) (d - 1) (d - 1) *
                    matGet (matEval d m0 m1 w') (d - 1) (d - 1) :=
      Nat.mul_le_mul hb ih
    omega

/-! ### Fixed-Length Lexicographic Well-Foundedness & Termination Soundness -/

inductive LexLt : List Nat → List Nat → Prop where
  | head {a b : Nat} {as bs : List Nat} : a < b → as.length = bs.length → LexLt (a :: as) (b :: bs)
  | tail {a : Nat} {as bs : List Nat} : LexLt as bs → LexLt (a :: as) (a :: bs)

theorem LexLt.length_eq {xs ys : List Nat} (h : LexLt xs ys) : xs.length = ys.length := by
  induction h with
  | head _ hlen => simp [hlen]
  | tail _ ih => simp [ih]

theorem acc_lexLt_of_length : ∀ (k : Nat) (xs : List Nat), xs.length = k → Acc LexLt xs := by
  intro k
  induction k with
  | zero =>
    intro xs hlen
    cases xs with
    | nil => exact Acc.intro [] fun ys hy => by cases hy
    | cons _ _ => cases hlen
  | succ k ih_k =>
    intro xs hlen
    cases xs with
    | nil => cases hlen
    | cons x xs' =>
      have hlen' : xs'.length = k := by simpa using hlen
      have hOuter : ∀ (a : Nat) (as : List Nat), as.length = k → Acc LexLt (a :: as) := by
        intro a
        induction a using Nat.strongRecOn with
        | ind a ih_a =>
          intro as has
          have hAccTail : Acc LexLt as := ih_k as has
          induction hAccTail with
          | intro bs _ ih_bs =>
            apply Acc.intro (a :: bs)
            intro ys hlt
            cases hlt with
            | head hlt_a hlen_ys =>
              exact ih_a _ hlt_a _ (hlen_ys.trans has)
            | tail hlt_bs =>
              exact ih_bs _ hlt_bs (hlt_bs.length_eq.trans has)
      exact hOuter x xs' hlen'

theorem wf_lexLt : WellFounded LexLt :=
  ⟨fun xs => acc_lexLt_of_length xs.length xs rfl⟩

def layerMeasure (L : MatrixLayer) (w : Word) : Nat :=
  matGet (matEval L.dim L.m0 L.m1 w) 0 (L.dim - 1)

def measureVec (layers : List MatrixLayer) (w : Word) : List Nat :=
  layers.map (fun L => layerMeasure L w)

theorem layerMeasure_le_of_step {L : MatrixLayer} {p s l r : Word}
    (hValid : checkLayerValid L = true)
    (hle : MatLe L.dim (matEval L.dim L.m0 L.m1 r) (matEval L.dim L.m0 L.m1 l)) :
    layerMeasure L (p ++ r ++ s) ≤ layerMeasure L (p ++ l ++ s) := by
  unfold checkLayerValid at hValid
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hValid
  have hd : 1 ≤ L.dim := hValid.1.1.1.1.1.1
  have h0 : 0 < L.dim := by omega
  have hlast : L.dim - 1 < L.dim := by omega
  unfold layerMeasure
  rw [matEval_append, matEval_append, matEval_append, matEval_append]
  have h1 : MatLe L.dim
      (matMul L.dim (matMul L.dim (matEval L.dim L.m0 L.m1 p) (matEval L.dim L.m0 L.m1 r))
        (matEval L.dim L.m0 L.m1 s))
      (matMul L.dim (matMul L.dim (matEval L.dim L.m0 L.m1 p) (matEval L.dim L.m0 L.m1 l))
        (matEval L.dim L.m0 L.m1 s)) :=
    matMul_mono_right (matMul_mono_left hle)
  exact h1 0 h0 (L.dim - 1) hlast

theorem layerMeasure_lt_of_step {L : MatrixLayer} {p s l r : Word}
    (hValid : checkLayerValid L = true)
    (hle : MatLe L.dim (matEval L.dim L.m0 L.m1 r) (matEval L.dim L.m0 L.m1 l))
    (hlt : matGet (matEval L.dim L.m0 L.m1 r) 0 (L.dim - 1) <
           matGet (matEval L.dim L.m0 L.m1 l) 0 (L.dim - 1)) :
    layerMeasure L (p ++ r ++ s) < layerMeasure L (p ++ l ++ s) := by
  unfold checkLayerValid at hValid
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hValid
  have hd : 1 ≤ L.dim := hValid.1.1.1.1.1.1
  have hm0_tl : 1 ≤ matGet L.m0 0 0 := hValid.1.1.1.2
  have hm0_br : 1 ≤ matGet L.m0 (L.dim - 1) (L.dim - 1) := hValid.1.1.2
  have hm1_tl : 1 ≤ matGet L.m1 0 0 := hValid.1.2
  have hm1_br : 1 ≤ matGet L.m1 (L.dim - 1) (L.dim - 1) := hValid.2
  unfold layerMeasure
  rw [matEval_append, matEval_append, matEval_append, matEval_append]
  exact matMul_strict_tr hd
    (matEval_tl_pos hd hm0_tl hm1_tl p)
    (matEval_br_pos hd hm0_br hm1_br s)
    hle hlt

theorem measureVec_lexLt_of_rule {layers : List MatrixLayer} {p s l r : Word}
    (hValid : ∀ L ∈ layers, checkLayerValid L = true)
    (hRule : checkRuleAgainstLayers layers (l, r) = true) :
    LexLt (measureVec layers (p ++ r ++ s)) (measureVec layers (p ++ l ++ s)) := by
  induction layers with
  | nil => simp [checkRuleAgainstLayers] at hRule
  | cons L Ls ih =>
    simp only [measureVec, List.map]
    have hLV : checkLayerValid L = true := hValid L (by simp)
    have hLsV : ∀ L' ∈ Ls, checkLayerValid L' = true := fun L' h => hValid L' (by simp [h])
    simp only [checkRuleAgainstLayers] at hRule
    by_cases hStrict : matGtTR L.dim (matEval L.dim L.m0 L.m1 l) (matEval L.dim L.m0 L.m1 r) = true
    · obtain ⟨hle, hlt⟩ := matGtTR_sound hStrict
      have hltM := layerMeasure_lt_of_step (p := p) (s := s) hLV hle hlt
      exact LexLt.head hltM (by simp)
    · simp only [hStrict] at hRule
      by_cases hWeak : matGe L.dim (matEval L.dim L.m0 L.m1 l) (matEval L.dim L.m0 L.m1 r) = true
      · simp only [hWeak, ↓reduceIte] at hRule
        have hle := matGe_sound hWeak
        have hleM := layerMeasure_le_of_step (p := p) (s := s) hLV hle
        by_cases hEq : layerMeasure L (p ++ r ++ s) = layerMeasure L (p ++ l ++ s)
        · rw [hEq]
          exact LexLt.tail (ih hLsV hRule)
        · exact LexLt.head (Nat.lt_of_le_of_ne hleM hEq) (by simp)
      · simp [hWeak] at hRule

/-- Master Termination Soundness Theorem:
A verified layered matrix certificate proves global termination for ALL bit-strings. -/
theorem checkTermination_sound {R : SRS} {layers : List MatrixLayer}
    (h : checkTermination R layers = true) : Terminating R := by
  unfold checkTermination at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  have hValid : ∀ L ∈ layers, checkLayerValid L = true := h.1.2
  have hRules : ∀ r ∈ R, checkRuleAgainstLayers layers r = true := fun r hr => (h.2 r hr).2
  have hSub : ∀ {v u}, Step R u v → LexLt (measureVec layers v) (measureVec layers u) := by
    intro v u hstep
    cases hstep with
    | mk p s l r hmem =>
      exact measureVec_lexLt_of_rule hValid (hRules (l, r) hmem)
  exact Subrelation.wf (r := InvImage LexLt (measureVec layers))
    (fun hstep => hSub hstep) (InvImage.wf (measureVec layers) wf_lexLt)

/-! ## Section 3: Complete Critical-Pair Enumeration & Trace-Replay Joinability Engine -/

/-! ### Critical-Pair Completeness & Trace-Replay Soundness Proofs -/

theorem applyStepCert_sound {R : SRS} {w w' : Word} {sc : StepCert}
    (h : applyStepCert R w sc = some w') : Step R w w' := by
  rcases sc with ⟨ri, pos⟩
  unfold applyStepCert at h
  cases hget : R[ri]? with
  | none => simp [hget] at h
  | some lr =>
    rcases lr with ⟨l, r⟩
    simp only [hget] at h
    split at h
    · split at h
      · rename_i _ hmatch
        simp only [beq_iff_eq] at hmatch
        simp only [Option.some.injEq] at h
        have hmem : (l, r) ∈ R := List.mem_of_getElem? hget
        have hw : w.take pos ++ l ++ (w.drop pos).drop l.length = w := by
          have h1 : w.take pos ++ w.drop pos = w := List.take_append_drop pos w
          have h2 : (w.drop pos).take l.length ++ (w.drop pos).drop l.length = w.drop pos :=
            List.take_append_drop l.length (w.drop pos)
          rw [hmatch] at h2
          rw [List.append_assoc, h2, h1]
        have hstep := Step.mk (w.take pos) ((w.drop pos).drop l.length) l r hmem
        rw [hw, h] at hstep
        exact hstep
      · cases h
    · cases h

theorem replayTrace_sound {R : SRS} {w z : Word} {tr : List StepCert}
    (h : replayTrace R w tr = some z) : Steps R w z := by
  induction tr generalizing w with
  | nil =>
    simp only [replayTrace, Option.some.injEq] at h
    rw [h]
    exact .refl z
  | cons sc scs ih =>
    simp only [replayTrace] at h
    cases hstep : applyStepCert R w sc with
    | none => simp [hstep] at h
    | some w' =>
      simp only [hstep] at h
      exact .tail (applyStepCert_sound hstep) (ih h)

private theorem list_eq_append_of_append_eq {α : Type} {a b c d : List α}
    (h : a ++ b = c ++ d) (hle : a.length ≤ c.length) :
    ∃ m, c = a ++ m ∧ b = m ++ d := by
  refine ⟨c.drop a.length, ?_, ?_⟩
  · have htake : (a ++ b).take a.length = (c ++ d).take a.length := congrArg (List.take a.length) h
    have hta : (a ++ b).take a.length = a := by simp
    have htc : (c ++ d).take a.length = c.take a.length :=
      List.take_append_of_le_length hle
    rw [hta, htc] at htake
    calc c = c.take a.length ++ c.drop a.length := (List.take_append_drop a.length c).symm
         _ = a ++ c.drop a.length := by rw [← htake]
  · have hdrop : (a ++ b).drop a.length = (c ++ d).drop a.length := congrArg (List.drop a.length) h
    have hda : (a ++ b).drop a.length = b := by simp
    have hdc : (c ++ d).drop a.length = c.drop a.length ++ d :=
      List.drop_append_of_le_length hle
    rw [hda, hdc] at hdrop
    exact hdrop

/-- One-sided peak analysis (`p₁.length ≤ p₂.length`):
every peak is either disjoint (1-step join) or an instance of a critical pair in `criticalPairs R`. -/
theorem peak_joinable_of_le {R : SRS}
    (hCP : ∀ cp ∈ criticalPairs R, Joinable R cp.1 cp.2)
    {p₁ s₁ l₁ r₁ p₂ s₂ l₂ r₂ : Word}
    (h1 : (l₁, r₁) ∈ R) (h2 : (l₂, r₂) ∈ R)
    (heq : p₁ ++ l₁ ++ s₁ = p₂ ++ l₂ ++ s₂)
    (hle : p₁.length ≤ p₂.length) :
    Joinable R (p₁ ++ r₁ ++ s₁) (p₂ ++ r₂ ++ s₂) := by
  have heq' : p₁ ++ (l₁ ++ s₁) = p₂ ++ (l₂ ++ s₂) := by simpa [List.append_assoc] using heq
  obtain ⟨a, hp₂, hmid⟩ := list_eq_append_of_append_eq heq' hle
  by_cases hdisj : l₁.length ≤ a.length
  · -- Case 1: Disjoint redexes
    obtain ⟨m, ha, hs₁⟩ := list_eq_append_of_append_eq hmid hdisj
    subst hp₂; subst ha; subst hs₁
    refine ⟨p₁ ++ r₁ ++ m ++ r₂ ++ s₂, ?_, ?_⟩
    · have hA : p₁ ++ r₁ ++ (m ++ (l₂ ++ s₂)) = (p₁ ++ r₁ ++ m) ++ l₂ ++ s₂ := by simp [List.append_assoc]
      have hB : p₁ ++ r₁ ++ m ++ r₂ ++ s₂ = (p₁ ++ r₁ ++ m) ++ r₂ ++ s₂ := by simp [List.append_assoc]
      rw [hA, hB]
      exact Steps.single (Step.mk (p₁ ++ r₁ ++ m) s₂ l₂ r₂ h2)
    · have hA : p₁ ++ (l₁ ++ m) ++ r₂ ++ s₂ = p₁ ++ l₁ ++ (m ++ r₂ ++ s₂) := by simp [List.append_assoc]
      have hB : p₁ ++ r₁ ++ m ++ r₂ ++ s₂ = p₁ ++ r₁ ++ (m ++ r₂ ++ s₂) := by simp [List.append_assoc]
      rw [hA, hB]
      exact Steps.single (Step.mk p₁ (m ++ r₂ ++ s₂) l₁ r₁ h1)
  · -- Case 2: Overlapping redexes (`a.length < l₁.length`)
    have hk : a.length < l₁.length := Nat.lt_of_not_ge hdisj
    let k := a.length
    have ha_take : a = l₁.take k := by
      have htk := congrArg (List.take k) hmid
      have hL : (l₁ ++ s₁).take k = l₁.take k := List.take_append_of_le_length (Nat.le_of_lt hk)
      have hR : (a ++ (l₂ ++ s₂)).take k = a := by simp [k]
      rw [hL, hR] at htk
      exact htk.symm
    let c := l₁.drop k
    have hc_eq : c ++ s₁ = l₂ ++ s₂ := by
      have hdr := congrArg (List.drop k) hmid
      have hL : (l₁ ++ s₁).drop k = c ++ s₁ := List.drop_append_of_le_length (Nat.le_of_lt hk)
      have hR : (a ++ (l₂ ++ s₂)).drop k = l₂ ++ s₂ := by simp [k]
      rw [hL, hR] at hdr
      exact hdr
    have hclen : c.length = l₁.length - k := List.length_drop
    by_cases hincl : k + l₂.length ≤ l₁.length
    · -- Subcase 2a: Inclusion overlap (`l₂` is a prefix of `c`)
      have hl₂c : l₂.length ≤ c.length := by omega
      have hctake : c.take l₂.length = l₂ := by
        have htk := congrArg (List.take l₂.length) hc_eq
        rw [List.take_append_of_le_length hl₂c] at htk
        simpa using htk
      let b := c.drop l₂.length
      have hs₂ : s₂ = b ++ s₁ := by
        have hdr := congrArg (List.drop l₂.length) hc_eq
        rw [List.drop_append_of_le_length hl₂c] at hdr
        simpa [b] using hdr.symm
      have hmemCP : (r₁, a ++ r₂ ++ b) ∈ criticalPairs R := by
        unfold criticalPairs criticalPairsPair
        simp only [List.mem_flatMap, List.mem_range]
        refine ⟨(l₁, r₁), h1, (l₂, r₂), h2, k, hk, ?_⟩
        unfold overlapsForOffset
        simp only [hincl, ↓reduceIte, beq_iff_eq]
        have hct' : (l₁.drop k).take l₂.length = l₂ := hctake
        simp only [hct', ↓reduceIte, List.mem_singleton, Prod.mk.injEq, true_and]
        rw [ha_take]
      have hJ := (hCP _ hmemCP).context p₁ s₁
      have hR_eq : p₁ ++ (a ++ r₂ ++ b) ++ s₁ = p₂ ++ r₂ ++ s₂ := by
        rw [hp₂, hs₂]; simp [List.append_assoc]
      rw [hR_eq] at hJ
      exact hJ
    · -- Subcase 2b: Suffix-prefix overlap (`c` is a prefix of `l₂`)
      have hcl₂ : c.length ≤ l₂.length := by omega
      have hl₂take : l₂.take c.length = c := by
        have htk := congrArg (List.take c.length) hc_eq
        rw [List.take_append_of_le_length hcl₂] at htk
        simpa using htk.symm
      let d := l₂.drop c.length
      have hs₁ : s₁ = d ++ s₂ := by
        have hdr := congrArg (List.drop c.length) hc_eq
        rw [List.drop_append_of_le_length hcl₂] at hdr
        simpa [d] using hdr
      have hmemCP : (r₁ ++ d, a ++ r₂) ∈ criticalPairs R := by
        unfold criticalPairs criticalPairsPair
        simp only [List.mem_flatMap, List.mem_range]
        refine ⟨(l₁, r₁), h1, (l₂, r₂), h2, k, hk, ?_⟩
        unfold overlapsForOffset
        simp only [hincl, ↓reduceIte, beq_iff_eq]
        have hl2' : l₂.take (l₁.drop k).length = l₁.drop k := hl₂take
        simp only [hl2', ↓reduceIte, List.mem_singleton, Prod.mk.injEq]
        rw [ha_take]
        exact ⟨rfl, rfl⟩
      have hJ := (hCP _ hmemCP).context p₁ s₂
      have hL_eq : p₁ ++ (r₁ ++ d) ++ s₂ = p₁ ++ r₁ ++ s₁ := by
        rw [hs₁]; simp [List.append_assoc]
      have hR_eq : p₁ ++ (a ++ r₂) ++ s₂ = p₂ ++ r₂ ++ s₂ := by
        rw [hp₂]; simp [List.append_assoc]
      rw [hL_eq, hR_eq] at hJ
      exact hJ

theorem Step.dest {R : SRS} {u v : Word} (h : Step R u v) :
    ∃ p s l r, (l, r) ∈ R ∧ u = p ++ l ++ s ∧ v = p ++ r ++ s := by
  cases h with
  | mk p s l r hmem => exact ⟨p, s, l, r, hmem, rfl, rfl⟩

/-- Complete Critical-Pair Lemma for Binary String Rewriting Systems. -/
theorem locallyConfluent_of_criticalPairs {R : SRS}
    (hCP : ∀ cp ∈ criticalPairs R, Joinable R cp.1 cp.2) : LocallyConfluent R := by
  intro u v₁ v₂ hs₁ hs₂
  obtain ⟨p₁, s₁, l₁, r₁, h1, hu₁, hv₁⟩ := hs₁.dest
  obtain ⟨p₂, s₂, l₂, r₂, h2, hu₂, hv₂⟩ := hs₂.dest
  subst hv₁; subst hv₂
  have heq : p₁ ++ l₁ ++ s₁ = p₂ ++ l₂ ++ s₂ := hu₁.symm.trans hu₂
  by_cases hle : p₁.length ≤ p₂.length
  · exact peak_joinable_of_le hCP h1 h2 heq hle
  · exact (peak_joinable_of_le hCP h2 h1 heq.symm (Nat.le_of_not_ge hle)).symm

private theorem all_zip_sound {α β : Type} {xs : List α} {ys : List β} (P : α → β → Prop)
    (hlen : xs.length = ys.length)
    (hall : ∀ p ∈ List.zip xs ys, P p.1 p.2) :
    ∀ x ∈ xs, ∃ y, P x y := by
  induction xs generalizing ys with
  | nil => intro x hx; cases hx
  | cons a as ih =>
    cases ys with
    | nil => cases hlen
    | cons b bs =>
      intro x hx
      cases hx with
      | head => exact ⟨b, hall (a, b) (by simp)⟩
      | tail _ hmem =>
        exact ih (by simpa using hlen) (fun p hp => hall p (by simp [hp])) x hmem

theorem checkJoinability_sound {R : SRS} {wits : List JoinWitness}
    (h : checkJoinability R wits = true) : LocallyConfluent R := by
  unfold checkJoinability at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  apply locallyConfluent_of_criticalPairs
  intro cp hcp
  have hall : ∀ p ∈ List.zip (criticalPairs R) wits, checkWitness R p.1 p.2 = true := h.2
  obtain ⟨wit, hwit⟩ := all_zip_sound (fun c w => checkWitness R c w = true) h.1.symm hall cp hcp
  unfold checkWitness at hwit
  cases hx : replayTrace R cp.1 wit.1 with
  | none => simp [hx] at hwit
  | some z₁ =>
    cases hy : replayTrace R cp.2 wit.2 with
    | none => simp [hx, hy] at hwit
    | some z₂ =>
      simp only [hx, hy, beq_iff_eq] at hwit
      subst hwit
      exact ⟨z₁, replayTrace_sound hx, replayTrace_sound hy⟩

/-! ## Section 4: Master Reflection Soundness & Verified Computable Normalizer -/

theorem findMatchAt_complete {p s l r : Word} :
    ∃ v, findMatchAt (p ++ l ++ s) l r p.length = some v := by
  refine ⟨p ++ r ++ s, ?_⟩
  unfold findMatchAt
  have hle : p.length + l.length ≤ (p ++ l ++ s).length := by simp
  have hdrop : (p ++ l ++ s).drop p.length = l ++ s := by
    rw [List.append_assoc, List.drop_left]
  have htake : (l ++ s).take l.length = l := by simp
  have hdrop2 : (l ++ s).drop l.length = s := by simp
  have hptake : (p ++ l ++ s).take p.length = p := by
    rw [List.append_assoc, List.take_left]
  simp only [hle, ↓reduceIte, hdrop, htake, beq_self_eq_true, hdrop2, hptake]

theorem findRuleStepFrom_complete {w l r : Word} {pos k : Nat}
    (hle : pos ≤ k) (hmatch : ∃ v, findMatchAt w l r pos = some v) :
    ∃ v, findRuleStepFrom w l r k = some v := by
  induction k with
  | zero =>
    have h0 : pos = 0 := Nat.eq_zero_of_le_zero hle
    subst h0; exact hmatch
  | succ k' ih =>
    simp only [findRuleStepFrom]
    by_cases hlt : pos ≤ k'
    · obtain ⟨v, hv⟩ := ih hlt
      rw [hv]; exact ⟨v, rfl⟩
    · have heq : pos = k' + 1 := by omega
      subst heq
      cases hrec : findRuleStepFrom w l r k' with
      | some u => exact ⟨u, rfl⟩
      | none => exact hmatch

private theorem findStep_none_all {R : SRS} {w : Word} (h : findStep R w = none) :
    ∀ rule ∈ R, findRuleStep w rule = none := by
  unfold findStep at h
  induction R with
  | nil => intro _ hx; cases hx
  | cons hd tl ih =>
    simp only [List.findSome?_cons] at h
    cases hhd : findRuleStep w hd with
    | some _ => simp [hhd] at h
    | none =>
      simp only [hhd] at h
      intro rule hrm
      cases hrm with
      | head => exact hhd
      | tail _ htl => exact ih h rule htl

theorem findStep_none_nf {R : SRS} {w : Word} (h : findStep R w = none) : IsNormalForm R w := by
  intro v hstep
  obtain ⟨p, s, l, r, hmem, hw, _⟩ := hstep.dest
  have hmatch := findMatchAt_complete (p := p) (s := s) (l := l) (r := r)
  have hpos : p.length ≤ (p ++ l ++ s).length := by simp
  obtain ⟨v', hv'⟩ := findRuleStepFrom_complete hpos hmatch
  have hnone := findStep_none_all h (l, r) hmem
  rw [hw] at hnone
  change findRuleStepFrom (p ++ l ++ s) l r (p ++ l ++ s).length = none at hnone
  rw [hv'] at hnone
  cases hnone

theorem normalize_spec (R : SRS) (hTerm : Terminating R) (w : Word) :
    Steps R w (normalize R hTerm w) ∧ IsNormalForm R (normalize R hTerm w) := by
  have hAcc := hTerm.apply w
  induction hAcc with
  | intro x _ ih =>
    have hEq : normalize R hTerm x =
        match h : findStep R x with
        | none => x
        | some v => normalize R hTerm v :=
      WellFounded.fix_eq (hwf := hTerm) _ x
    rw [hEq]
    split
    · rename_i hnone
      exact ⟨.refl x, findStep_none_nf hnone⟩
    · rename_i v hsome
      have ⟨hsteps, hnf⟩ := ih v (findStep_sound hsome)
      exact ⟨.tail (findStep_sound hsome) hsteps, hnf⟩

theorem normalize_steps (R : SRS) (hTerm : Terminating R) (w : Word) :
    Steps R w (normalize R hTerm w) := (normalize_spec R hTerm w).1

theorem normalize_nf (R : SRS) (hTerm : Terminating R) (w : Word) :
    IsNormalForm R (normalize R hTerm w) := (normalize_spec R hTerm w).2

theorem uniqueNormalForms_of_term_conf {R : SRS}
    (hTerm : Terminating R) (hConf : Confluent R) : UniqueNormalForms R := by
  intro w
  refine ⟨⟨normalize R hTerm w, normalize_steps R hTerm w, normalize_nf R hTerm w⟩, ?_⟩
  intro n₁ n₂ h₁ hn₁ h₂ hn₂
  obtain ⟨z, hz₁, hz₂⟩ := hConf w n₁ n₂ h₁ h₂
  rw [hz₁.nf_eq hn₁, hz₂.nf_eq hn₂]

/-- Master Soundness Meta-Theorem for the Finite Binary Certificate Engine. -/
theorem cert_sound (R : SRS) (cert : ConfluenceCert) (h : checkCert R cert = true) :
    Terminating R ∧ Confluent R ∧ UniqueNormalForms R := by
  unfold checkCert at h
  simp only [Bool.and_eq_true] at h
  have hTerm := checkTermination_sound h.1
  have hLoc := checkJoinability_sound h.2
  have hConf := newman hTerm hLoc
  exact ⟨hTerm, hConf, uniqueNormalForms_of_term_conf hTerm hConf⟩

/-- Verified Word-Problem Decision Equivalence (Church-Rosser Compiler):
For ANY certified system and ALL bit-strings `u, v` of arbitrary length,
`Convertible R u v ↔ normalize R hTerm u = normalize R hTerm v`. -/
theorem convertible_iff_normalize_eq {R : SRS} {cert : ConfluenceCert}
    (h : checkCert R cert = true) (u v : Word) :
    Convertible R u v ↔
    normalize R (cert_sound R cert h).1 u = normalize R (cert_sound R cert h).1 v := by
  have ⟨hTerm, hConf, _⟩ := cert_sound R cert h
  constructor
  · intro hConv
    have hC' : Convertible R (normalize R hTerm u) (normalize R hTerm v) :=
      (Convertible.of_steps (normalize_steps R hTerm u)).symm.trans
        (hConv.trans (Convertible.of_steps (normalize_steps R hTerm v)))
    exact joinable_of_convertible_nf hConf hC' (normalize_nf R hTerm u) (normalize_nf R hTerm v)
  · intro heq
    have h1 := Convertible.of_steps (normalize_steps R hTerm u)
    have h2 := Convertible.of_steps (normalize_steps R hTerm v)
    rw [heq] at h1
    exact h1.trans h2.symm

theorem normalize_idempotent {R : SRS} (hTerm : Terminating R) (w : Word) :
    normalize R hTerm (normalize R hTerm w) = normalize R hTerm w := by
  have hsteps := normalize_steps R hTerm (normalize R hTerm w)
  exact (hsteps.nf_eq (normalize_nf R hTerm w)).symm

/-! ## Section 5: Infinite Parametric Dichotomy Theorem (Modular Amplification Monoids) -/

private theorem replicate_add_eq {α : Type} (x : α) (m n : Nat) :
    List.replicate (m + n) x = List.replicate m x ++ List.replicate n x := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.succ_add, List.replicate_succ, List.replicate_succ, List.cons_append, ih]

theorem zeros_add (m n : Nat) : zeros (m + n) = zeros m ++ zeros n :=
  replicate_add_eq false m n

theorem ones_add (m n : Nat) : ones (m + n) = ones m ++ ones n :=
  replicate_add_eq true m n

theorem zeros_succ (n : Nat) : zeros (n + 1) = false :: zeros n := rfl

theorem ones_succ (n : Nat) : ones (n + 1) = true :: ones n := rfl

theorem zeros_length (n : Nat) : (zeros n).length = n := List.length_replicate

theorem ones_length (n : Nat) : (ones n).length = n := List.length_replicate

def ampLayer (b : Nat) : MatrixLayer :=
  { dim := 2, m0 := [[1, 1], [0, 1]], m1 := [[b + 1, 1], [0, 1]] }

def geomSum (a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => 1 + a * geomSum a n

theorem geomSum_mono_lt {a s r : Nat} (ha : 1 ≤ a) (hsr : s < r) :
    geomSum a s < geomSum a r := by
  induction r with
  | zero => cases hsr
  | succ r' ih =>
    change geomSum a s < 1 + a * geomSum a r'
    by_cases hEq : s = r'
    · subst hEq
      have h1 : geomSum a s ≤ a * geomSum a s := Nat.le_mul_of_pos_left _ (by omega)
      omega
    · have hlt : s < r' := by omega
      have h1 := ih hlt
      have h2 : geomSum a r' ≤ a * geomSum a r' := Nat.le_mul_of_pos_left _ (by omega)
      omega

theorem pow_le_pow_of_le {a s r : Nat} (ha : 1 ≤ a) (hsr : s ≤ r) : a ^ s ≤ a ^ r := by
  induction r with
  | zero =>
    have hs : s = 0 := Nat.eq_zero_of_le_zero hsr
    subst hs; exact Nat.le_refl 1
  | succ r' ih =>
    by_cases hEq : s = r' + 1
    · subst hEq; exact Nat.le_refl _
    · have hle : s ≤ r' := by omega
      have h1 := ih hle
      have h2 : a ^ r' ≤ a ^ r' * a := Nat.le_mul_of_pos_right _ (by omega)
      calc a ^ s ≤ a ^ r' := h1
           _ ≤ a ^ r' * a := h2
           _ = a ^ (r' + 1) := by rw [Nat.pow_succ]

theorem pow_lt_pow_of_lt {a s r : Nat} (ha : 2 ≤ a) (hsr : s < r) : a ^ s < a ^ r := by
  induction r with
  | zero => cases hsr
  | succ r' ih =>
    have hpos : 1 ≤ a ^ r' := Nat.one_le_pow r' a (by omega)
    by_cases hEq : s = r'
    · subst hEq
      rw [Nat.pow_succ]
      have : a ^ s * 2 ≤ a ^ s * a := Nat.mul_le_mul_left _ ha
      omega
    · have h1 := ih (by omega)
      rw [Nat.pow_succ]
      have : a ^ r' * 2 ≤ a ^ r' * a := Nat.mul_le_mul_left _ ha
      omega

private theorem matMul2_eq (a b c d e f g h : Nat) :
    matMul 2 [[a, b], [c, d]] [[e, f], [g, h]] =
    [[a * e + b * g, a * f + b * h], [c * e + d * g, c * f + d * h]] := by
  simp [matMul, List.range, List.range.loop, sumRange, matGet]

theorem amp_matEval_zeros (b n : Nat) :
    matEval 2 [[1, 1], [0, 1]] [[b + 1, 1], [0, 1]] (zeros n) = [[1, n], [0, 1]] := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    simp only [zeros_succ, matEval, Bool.false_eq_true, ↓reduceIte, ih]
    rw [matMul2_eq]
    simp [Nat.add_comm]

theorem amp_matEval_ones (b n : Nat) :
    matEval 2 [[1, 1], [0, 1]] [[b + 1, 1], [0, 1]] (ones n) =
    [[(b + 1) ^ n, geomSum (b + 1) n], [0, 1]] := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    simp only [ones_succ, matEval, ↓reduceIte, ih]
    rw [matMul2_eq]
    simp only [geomSum, Nat.zero_mul, Nat.one_mul, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
    have hpow : (b + 1) * (b + 1) ^ n' = (b + 1) ^ (n' + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm]
    have hsum : (b + 1) * geomSum (b + 1) n' + 1 = 1 + (b + 1) * geomSum (b + 1) n' :=
      Nat.add_comm _ _
    rw [hpow, hsum]

/-- Universal Matrix Termination Theorem:
For ALL parameters `b ≥ 2, s < r, k ≥ 1, d ≥ 1`, our 2×2 matrix layer certifies termination of
`ampSys b r s k d` on ALL bit-strings of arbitrary length (despite exponential length growth). -/
theorem ampSys_checkTermination (b r s k d : Nat) (hb : 2 ≤ b) (hrs : s < r) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    checkTermination (ampSys b r s k d) [ampLayer b] = true := by
  have hLValid : checkLayerValid (ampLayer b) = true := by
    simp [checkLayerValid, ampLayer, checkMatWF, matGet]
  have hr1 : checkRuleAgainstLayers [ampLayer b] ([true, false], zeros b ++ [true]) = true := by
    have hLHS : matEval 2 [[1, 1], [0, 1]] [[b + 1, 1], [0, 1]] [true, false] =
        [[b + 1, b + 2], [0, 1]] := by
      simp only [matEval, ↓reduceIte, Bool.false_eq_true]
      change matMul 2 [[b + 1, 1], [0, 1]] (matMul 2 [[1, 1], [0, 1]] [[1, 0], [0, 1]]) = _
      rw [matMul2_eq, matMul2_eq]
      simp
    have hRHS : matEval 2 [[1, 1], [0, 1]] [[b + 1, 1], [0, 1]] (zeros b ++ [true]) =
        [[b + 1, b + 1], [0, 1]] := by
      rw [matEval_append, amp_matEval_zeros]
      have h1 : matEval 2 [[1, 1], [0, 1]] [[b + 1, 1], [0, 1]] [true] = [[b + 1, 1], [0, 1]] := by
        simp only [matEval, ↓reduceIte]
        change matMul 2 [[b + 1, 1], [0, 1]] [[1, 0], [0, 1]] = _
        rw [matMul2_eq]; simp
      rw [h1, matMul2_eq]
      simp; omega
    have hgt : matGtTR 2 [[b + 1, b + 2], [0, 1]] [[b + 1, b + 1], [0, 1]] = true := by
      simp [matGtTR, matGe, List.range, List.range.loop, matGet]
    simp only [checkRuleAgainstLayers, ampLayer, hLHS, hRHS, hgt, ↓reduceIte]
  have hr2 : checkRuleAgainstLayers [ampLayer b] (zeros (k + d), zeros k) = true := by
    have hgt : matGtTR 2 [[1, k + d], [0, 1]] [[1, k], [0, 1]] = true := by
      simp [matGtTR, matGe, List.range, List.range.loop, matGet]; omega
    simp only [checkRuleAgainstLayers, ampLayer, amp_matEval_zeros, hgt, ↓reduceIte]
  have hr3 : checkRuleAgainstLayers [ampLayer b] (ones r, ones s) = true := by
    have hpow : (b + 1) ^ s ≤ (b + 1) ^ r := pow_le_pow_of_le (by omega) (Nat.le_of_lt hrs)
    have hgs : geomSum (b + 1) s < geomSum (b + 1) r := geomSum_mono_lt (by omega) hrs
    have hgt : matGtTR 2 [[(b + 1) ^ r, geomSum (b + 1) r], [0, 1]]
                         [[(b + 1) ^ s, geomSum (b + 1) s], [0, 1]] = true := by
      simp [matGtTR, matGe, List.range, List.range.loop, matGet]
      omega
    simp only [checkRuleAgainstLayers, ampLayer, amp_matEval_ones, hgt, ↓reduceIte]
  have hne2 : zeros (k + d) ≠ [] := by
    intro h; have := congrArg List.length h; rw [zeros_length] at this; simp at this; omega
  have hne3 : ones r ≠ [] := by
    intro h; have := congrArg List.length h; rw [ones_length] at this; simp at this; omega
  simp [checkTermination, ampSys, hLValid, hr1, hr2, hr3, hne2, hne3]

theorem ampSys_terminating (b r s k d : Nat) (hb : 2 ≤ b) (hrs : s < r) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    Terminating (ampSys b r s k d) :=
  checkTermination_sound (ampSys_checkTermination b r s k d hb hrs hk hd)

/-! ### Auxiliary Derivations & Normal-Form Characterization for `ampSys` -/

private theorem amp_rule1_step (b r s k d : Nat) :
    Step (ampSys b r s k d) [true, false] (zeros b ++ [true]) := by
  have h : Step (ampSys b r s k d) ([] ++ [true, false] ++ []) ([] ++ (zeros b ++ [true]) ++ []) :=
    Step.mk [] [] [true, false] (zeros b ++ [true]) (List.Mem.head _)
  simpa using h

private theorem amp_rule2_step (b r s k d : Nat) :
    Step (ampSys b r s k d) (zeros (k + d)) (zeros k) := by
  have h : Step (ampSys b r s k d) ([] ++ zeros (k + d) ++ []) ([] ++ zeros k ++ []) :=
    Step.mk [] [] (zeros (k + d)) (zeros k) (List.Mem.tail _ (List.Mem.head _))
  simpa using h

private theorem amp_rule3_step (b r s k d : Nat) :
    Step (ampSys b r s k d) (ones r) (ones s) := by
  have h : Step (ampSys b r s k d) ([] ++ ones r ++ []) ([] ++ ones s ++ []) :=
    Step.mk [] [] (ones r) (ones s) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  simpa using h

private theorem amp_push_one_zeros (b r s k d n : Nat) :
    Steps (ampSys b r s k d) ([true] ++ zeros n) (zeros (b * n) ++ [true]) := by
  induction n with
  | zero => simp [zeros]; exact .refl _
  | succ n' ih =>
    have h1 : [true] ++ zeros (n' + 1) = [] ++ [true, false] ++ zeros n' := by
      simp [zeros_succ]
    have h2 : [] ++ (zeros b ++ [true]) ++ zeros n' = zeros b ++ ([true] ++ zeros n') := by
      simp [List.append_assoc]
    have hstep : Step (ampSys b r s k d) ([true] ++ zeros (n' + 1)) (zeros b ++ ([true] ++ zeros n')) := by
      rw [h1, ← h2]
      exact (amp_rule1_step b r s k d).context [] (zeros n')
    have hrest : Steps (ampSys b r s k d) (zeros b ++ ([true] ++ zeros n'))
        (zeros b ++ (zeros (b * n') ++ [true])) := by
      have hctx := ih.context (zeros b) []
      simpa using hctx
    have heq : zeros b ++ (zeros (b * n') ++ [true]) = zeros (b * (n' + 1)) ++ [true] := by
      rw [← List.append_assoc, ← zeros_add, Nat.mul_succ, Nat.add_comm]
    rw [heq] at hrest
    exact .tail hstep hrest

private theorem amp_push_ones_zeros (b r s k d m n : Nat) :
    Steps (ampSys b r s k d) (ones m ++ zeros n) (zeros (b ^ m * n) ++ ones m) := by
  induction m generalizing n with
  | zero => simp [ones]; exact .refl _
  | succ m' ih =>
    have h1 : ones (m' + 1) ++ zeros n = [true] ++ (ones m' ++ zeros n) := by
      simp [ones_succ]
    have hstep1 : Steps (ampSys b r s k d) ([true] ++ (ones m' ++ zeros n))
        ([true] ++ (zeros (b ^ m' * n) ++ ones m')) := by
      have := (ih n).context [true] []
      simpa using this
    have hstep2 : Steps (ampSys b r s k d) (([true] ++ zeros (b ^ m' * n)) ++ ones m')
        ((zeros (b * (b ^ m' * n)) ++ [true]) ++ ones m') := by
      have := (amp_push_one_zeros b r s k d (b ^ m' * n)).context [] (ones m')
      simpa using this
    have hAssoc1 : [true] ++ (zeros (b ^ m' * n) ++ ones m') = ([true] ++ zeros (b ^ m' * n)) ++ ones m' := by
      simp
    have hAssoc2 : (zeros (b * (b ^ m' * n)) ++ [true]) ++ ones m' = zeros (b ^ (m' + 1) * n) ++ ones (m' + 1) := by
      have hmul : b * (b ^ m' * n) = b ^ (m' + 1) * n := by
        rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm b (b ^ m')]
      rw [hmul, List.append_assoc]
      rfl
    rw [h1]
    exact hstep1.trans (by rw [hAssoc1]; exact hAssoc2 ▸ hstep2)

private theorem amp_compress_zeros (b r s k d m q : Nat) (hm : k ≤ m) :
    Steps (ampSys b r s k d) (zeros (m + q * d)) (zeros m) := by
  induction q with
  | zero => simp; exact .refl _
  | succ q' ih =>
    have hsplit : m + (q' + 1) * d = (m - k + q' * d) + (k + d) := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    have hmerge : (m - k + q' * d) + k = m + q' * d := by omega
    have hstep : Step (ampSys b r s k d) (zeros (m + (q' + 1) * d)) (zeros (m + q' * d)) := by
      have hs := (amp_rule2_step b r s k d).context (zeros (m - k + q' * d)) []
      simp only [List.append_nil] at hs
      rw [hsplit, ← hmerge, zeros_add (m - k + q' * d) (k + d), zeros_add (m - k + q' * d) k]
      exact hs
    exact .tail hstep ih

private theorem amp_compress_zeros_of_dvd (b r s k d m₁ m₂ : Nat)
    (hm : k ≤ m₁) (hle : m₁ ≤ m₂) (hdvd : d ∣ (m₂ - m₁)) :
    Steps (ampSys b r s k d) (zeros m₂) (zeros m₁) := by
  obtain ⟨q, hq⟩ := hdvd
  have heq : m₂ = m₁ + q * d := by rw [Nat.mul_comm]; omega
  rw [heq]
  exact amp_compress_zeros b r s k d m₁ q hm

private theorem replicate_take_eq {α : Type} (x : α) (n m : Nat) :
    (List.replicate n x).take m = List.replicate (min n m) x := by
  induction n generalizing m with
  | zero => simp
  | succ n' ih =>
    cases m with
    | zero => simp
    | succ m' =>
      simp only [List.replicate_succ, List.take_succ_cons, ih]
      have : min (n' + 1) (m' + 1) = min n' m' + 1 := by omega
      rw [this, List.replicate_succ]

private theorem replicate_drop_eq {α : Type} (x : α) (n m : Nat) :
    (List.replicate n x).drop m = List.replicate (n - m) x := by
  induction n generalizing m with
  | zero => simp
  | succ n' ih =>
    cases m with
    | zero => simp
    | succ m' =>
      simp only [List.replicate_succ, List.drop_succ_cons, ih]
      have : n' + 1 - (m' + 1) = n' - m' := by omega
      rw [this]

private theorem mem_zeros_eq_false {n : Nat} {x : Bool} (h : x ∈ zeros n) : x = false :=
  List.eq_of_mem_replicate h

private theorem mem_ones_eq_true {n : Nat} {x : Bool} (h : x ∈ ones n) : x = true :=
  List.eq_of_mem_replicate h

private theorem zeros_ne_ones_of_pos {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    zeros m ≠ ones n := by
  cases m with
  | zero => omega
  | succ m' =>
    cases n with
    | zero => omega
    | succ n' => simp [zeros_succ, ones_succ]

private theorem mem_overlapsForOffset {l₁ r₁ l₂ r₂ : Word} {j : Nat} {cp : Word × Word}
    (h : cp ∈ overlapsForOffset l₁ r₁ l₂ r₂ j) :
    (j + l₂.length ≤ l₁.length ∧ (l₁.drop j).take l₂.length = l₂ ∧
      cp = (r₁, l₁.take j ++ r₂ ++ (l₁.drop j).drop l₂.length)) ∨
    (l₁.length < j + l₂.length ∧ l₂.take (l₁.drop j).length = l₁.drop j ∧
      cp = (r₁ ++ l₂.drop (l₁.drop j).length, l₁.take j ++ r₂)) := by
  unfold overlapsForOffset at h
  dsimp only at h
  split at h
  · rename_i hle
    split at h
    · rename_i hmatch
      simp only [beq_iff_eq] at hmatch
      simp only [List.mem_singleton] at h
      exact Or.inl ⟨hle, hmatch, h⟩
    · cases h
  · rename_i hgt
    split at h
    · rename_i hmatch
      simp only [beq_iff_eq] at hmatch
      simp only [List.mem_singleton] at h
      exact Or.inr ⟨Nat.lt_of_not_ge hgt, hmatch, h⟩
    · cases h

/-- Sufficiency (`←`) of the Euler-Fermat Confluence Dichotomy. -/
theorem ampSys_confluent_of_cond (b r s k d : Nat)
    (hb : 2 ≤ b) (hrs : s < r) (hk : 1 ≤ k) (hd : 1 ≤ d)
    (hks : k ≤ b ^ s) (hdvd : d ∣ (b ^ r - b ^ s)) :
    Confluent (ampSys b r s k d) := by
  apply newman (ampSys_terminating b r s k d hb hrs hk hd)
  apply locallyConfluent_of_criticalPairs
  intro cp hcp
  unfold criticalPairs criticalPairsPair at hcp
  simp only [ampSys, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false, List.mem_range] at hcp
  rcases hcp with ⟨rule₁, hr₁, rule₂, hr₂, j, hj, hmem⟩
  rcases hr₁ with rfl | rfl | rfl
  · -- rule₁ = (10, 0^b 1), length 2 so j = 0 or j = 1
    simp only [List.length_cons, List.length_nil] at hj
    have hj01 : j = 0 ∨ j = 1 := by omega
    rcases hr₂ with rfl | rfl | rfl
    · -- rule₂ = (10, 0^b 1)
      rcases hj01 with rfl | rfl
      · rcases mem_overlapsForOffset hmem with ⟨_, _, rfl⟩ | ⟨hgt, _, _⟩
        · simp; exact .refl _
        · simp at hgt
      · rcases mem_overlapsForOffset hmem with ⟨hle, _, _⟩ | ⟨_, hmatch, _⟩
        · simp at hle
        · simp at hmatch
    · -- rule₂ = (0^(k+d), 0^k)
      rcases hj01 with rfl | rfl
      · rcases mem_overlapsForOffset hmem with ⟨hle, hmatch, _⟩ | ⟨_, hmatch, _⟩
        · have hkd2 : k + d = 2 := by simp [zeros_length] at hle; omega
          simp [hkd2, zeros] at hmatch
        · have : true ∈ (zeros (k + d)).take 2 := by simpa using hmatch ▸ (by simp : true ∈ [true, false])
          cases mem_zeros_eq_false (List.mem_of_mem_take this)
      · rcases mem_overlapsForOffset hmem with ⟨hle, _, _⟩ | ⟨_, _, rfl⟩
        · simp [zeros_length] at hle; omega
        · have hdrop1 : (zeros (k + d)).drop 1 = zeros (k + d - 1) := replicate_drop_eq false (k + d) 1
          change Joinable (ampSys b r s k d) ((zeros b ++ [true]) ++ (zeros (k + d)).drop 1) ([true] ++ zeros k)
          rw [hdrop1]
          refine ⟨zeros (b * k) ++ [true], ?_, ?_⟩
          · have hL1 : (zeros b ++ [true]) ++ zeros (k + d - 1) =
                zeros b ++ ([true] ++ zeros (k + d - 1)) := by simp [List.append_assoc]
            rw [hL1]
            have hs1 : Steps (ampSys b r s k d) (zeros b ++ ([true] ++ zeros (k + d - 1)))
                (zeros b ++ (zeros (b * (k + d - 1)) ++ [true])) := by
              have := (amp_push_one_zeros b r s k d (k + d - 1)).context (zeros b) []
              simpa using this
            have hmerge : zeros b ++ (zeros (b * (k + d - 1)) ++ [true]) =
                zeros (b * k + b * d) ++ [true] := by
              rw [← List.append_assoc, ← zeros_add]
              have harith : b + b * (k + d - 1) = b * k + b * d := by
                have h1 : k + d - 1 + 1 = k + d := by omega
                calc b + b * (k + d - 1) = b * (k + d - 1 + 1) := by rw [Nat.mul_succ, Nat.add_comm]
                     _ = b * (k + d) := by rw [h1]
                     _ = b * k + b * d := Nat.mul_add b k d
              rw [harith]
            rw [hmerge] at hs1
            have hkb : k ≤ b * k := Nat.le_mul_of_pos_left k (by omega)
            have hs2 : Steps (ampSys b r s k d) (zeros (b * k + b * d) ++ [true])
                (zeros (b * k) ++ [true]) := by
              have := (amp_compress_zeros b r s k d (b * k) b hkb).context [] [true]
              simpa using this
            exact hs1.trans hs2
          · exact amp_push_one_zeros b r s k d k
    · -- rule₂ = (1^r, 1^s)
      rcases hj01 with rfl | rfl
      · rcases mem_overlapsForOffset hmem with ⟨hle, hmatch, rfl⟩ | ⟨_, hmatch, _⟩
        · have hr12 : r = 1 ∨ r = 2 := by simp [ones_length] at hle; omega
          rcases hr12 with rfl | rfl
          · have hs0 : s = 0 := by omega
            subst hs0
            change Joinable (ampSys b 1 0 k d) (zeros b ++ [true]) [false]
            refine ⟨zeros 1, ?_, .refl _⟩
            have hstep : Step (ampSys b 1 0 k d) (zeros b ++ [true]) (zeros b) := by
              have h := (amp_rule3_step b 1 0 k d).context (zeros b) []
              simpa [ones] using h
            have hcomp : Steps (ampSys b 1 0 k d) (zeros b) (zeros 1) :=
              amp_compress_zeros_of_dvd b 1 0 k d 1 b (by simpa using hks) (by omega) (by simpa using hdvd)
            exact .tail hstep hcomp
          · simp [ones] at hmatch
        · have : false ∈ (ones r).take 2 := by simpa using hmatch ▸ (by simp : false ∈ [true, false])
          cases mem_ones_eq_true (List.mem_of_mem_take this)
      · rcases mem_overlapsForOffset hmem with ⟨hle, hmatch, _⟩ | ⟨_, hmatch, _⟩
        · have hr1 : r = 1 := by simp [ones_length] at hle; omega
          subst hr1; simp [ones] at hmatch
        · have : false ∈ (ones r).take 1 := by simpa using hmatch ▸ (by simp : false ∈ [false])
          cases mem_ones_eq_true (List.mem_of_mem_take this)
  · -- rule₁ = (0^(k+d), 0^k)
    rw [zeros_length] at hj
    rcases hr₂ with rfl | rfl | rfl
    · -- rule₂ = (10, 0^b 1)
      rcases mem_overlapsForOffset hmem with ⟨_, hmatch, _⟩ | ⟨hgt, hmatch, _⟩
      · have : true ∈ ((zeros (k + d)).drop j).take 2 := by
          simpa using hmatch ▸ (by simp : true ∈ [true, false])
        cases mem_zeros_eq_false (List.mem_of_mem_drop (List.mem_of_mem_take this))
      · have hkdj : k + d - j = 1 := by simp [zeros_length] at hgt; omega
        have hdrop : (zeros (k + d)).drop j = [false] := by
          rw [zeros, replicate_drop_eq, hkdj]; rfl
        rw [hdrop] at hmatch; simp at hmatch
    · -- rule₂ = (0^(k+d), 0^k): self-overlap
      rcases mem_overlapsForOffset hmem with ⟨hle, _, rfl⟩ | ⟨_, _, rfl⟩
      · have hj0 : j = 0 := by simp [zeros_length] at hle; omega
        subst hj0; simp; exact .refl _
      · change Joinable (ampSys b r s k d)
          (zeros k ++ (zeros (k + d)).drop ((zeros (k + d)).drop j).length)
          ((zeros (k + d)).take j ++ zeros k)
        have h1 : (zeros (k + d)).take j = zeros j := by
          rw [zeros, replicate_take_eq]; have : min (k + d) j = j := by omega
          rw [this]; rfl
        have hlen_drop : ((zeros (k + d)).drop j).length = k + d - j := by
          rw [List.length_drop, zeros_length]
        have h2 : (zeros (k + d)).drop ((zeros (k + d)).drop j).length = zeros j := by
          rw [hlen_drop, zeros, replicate_drop_eq]
          have : k + d - (k + d - j) = j := by omega
          rw [this]; rfl
        rw [h1, h2, ← zeros_add, ← zeros_add, Nat.add_comm k j]
        exact .refl _
    · -- rule₂ = (1^r, 1^s)
      rcases mem_overlapsForOffset hmem with ⟨_, hmatch, _⟩ | ⟨_, hmatch, _⟩
      · have : true ∈ ((zeros (k + d)).drop j).take (ones r).length := by
          rw [hmatch]; exact List.mem_replicate.mpr ⟨by omega, rfl⟩
        cases mem_zeros_eq_false (List.mem_of_mem_drop (List.mem_of_mem_take this))
      · have hcdrop : (zeros (k + d)).drop j = zeros (k + d - j) := replicate_drop_eq false (k + d) j
        have : false ∈ (ones r).take ((zeros (k + d)).drop j).length := by
          rw [hmatch, hcdrop]; exact List.mem_replicate.mpr ⟨by omega, rfl⟩
        cases mem_ones_eq_true (List.mem_of_mem_take this)
  · -- rule₁ = (1^r, 1^s)
    rw [ones_length] at hj
    rcases hr₂ with rfl | rfl | rfl
    · -- rule₂ = (10, 0^b 1): only matches at j = r - 1!
      rcases mem_overlapsForOffset hmem with ⟨_, hmatch, _⟩ | ⟨hgt, _, rfl⟩
      · have : false ∈ ((ones r).drop j).take ([true, false] : Word).length := by
          rw [hmatch]; simp
        cases mem_ones_eq_true (List.mem_of_mem_drop (List.mem_of_mem_take this))
      · have hj_eq : j = r - 1 := by simp [ones_length] at hgt; omega
        subst hj_eq
        have hdrop : (ones r).drop (r - 1) = [true] := by
          rw [ones, replicate_drop_eq]; have : r - (r - 1) = 1 := by omega
          rw [this]; rfl
        have htake : (ones r).take (r - 1) = ones (r - 1) := by
          rw [ones, replicate_take_eq]; have : min r (r - 1) = r - 1 := by omega
          rw [this]; rfl
        change Joinable (ampSys b r s k d)
          (ones s ++ ([true, false] : Word).drop ((ones r).drop (r - 1)).length)
          ((ones r).take (r - 1) ++ (zeros b ++ [true]))
        rw [hdrop, htake]
        change Joinable (ampSys b r s k d) (ones s ++ [false]) (ones (r - 1) ++ (zeros b ++ [true]))
        refine ⟨zeros (b ^ s) ++ ones s, ?_, ?_⟩
        · have hs := amp_push_ones_zeros b r s k d s 1
          simpa [zeros] using hs
        · have hR1 : ones (r - 1) ++ (zeros b ++ [true]) = (ones (r - 1) ++ zeros b) ++ [true] := by
            simp [List.append_assoc]
          rw [hR1]
          have hpush : Steps (ampSys b r s k d) ((ones (r - 1) ++ zeros b) ++ [true])
              ((zeros (b ^ (r - 1) * b) ++ ones (r - 1)) ++ [true]) := by
            have := (amp_push_ones_zeros b r s k d (r - 1) b).context [] [true]
            simpa using this
          have hpow : b ^ (r - 1) * b = b ^ r := by
            have hr1 : r - 1 + 1 = r := by omega
            calc b ^ (r - 1) * b = b ^ (r - 1 + 1) := (Nat.pow_succ b (r - 1)).symm
                 _ = b ^ r := by rw [hr1]
          have hones : (zeros (b ^ (r - 1) * b) ++ ones (r - 1)) ++ [true] = zeros (b ^ r) ++ ones r := by
            have hr1 : r - 1 + 1 = r := by omega
            have h1 : ones (r - 1) ++ [true] = ones r := by
              have : [true] = ones 1 := rfl
              rw [this, ← ones_add, hr1]
            rw [hpow, List.append_assoc, h1]
          rw [hones] at hpush
          have hred1 : Step (ampSys b r s k d) (zeros (b ^ r) ++ ones r) (zeros (b ^ r) ++ ones s) := by
            have := (amp_rule3_step b r s k d).context (zeros (b ^ r)) []
            simpa using this
          have hcomp : Steps (ampSys b r s k d) (zeros (b ^ r) ++ ones s) (zeros (b ^ s) ++ ones s) := by
            have hle_pow : b ^ s ≤ b ^ r := pow_le_pow_of_le (by omega) (Nat.le_of_lt hrs)
            have := (amp_compress_zeros_of_dvd b r s k d (b ^ s) (b ^ r) hks hle_pow hdvd).context [] (ones s)
            simpa using this
          exact hpush.trans (.tail hred1 hcomp)
    · -- rule₂ = (0^(k+d), 0^k)
      rcases mem_overlapsForOffset hmem with ⟨_, hmatch, _⟩ | ⟨_, hmatch, _⟩
      · have : false ∈ ((ones r).drop j).take (zeros (k + d)).length := by
          rw [hmatch]; exact List.mem_replicate.mpr ⟨by omega, rfl⟩
        cases mem_ones_eq_true (List.mem_of_mem_drop (List.mem_of_mem_take this))
      · have hcdrop : (ones r).drop j = ones (r - j) := replicate_drop_eq true r j
        have : true ∈ (zeros (k + d)).take ((ones r).drop j).length := by
          rw [hmatch, hcdrop]; exact List.mem_replicate.mpr ⟨by omega, rfl⟩
        cases mem_zeros_eq_false (List.mem_of_mem_take this)
    · -- rule₂ = (1^r, 1^s): self-overlap
      rcases mem_overlapsForOffset hmem with ⟨hle, _, rfl⟩ | ⟨_, _, rfl⟩
      · have hj0 : j = 0 := by simp [ones_length] at hle; omega
        subst hj0; simp; exact .refl _
      · change Joinable (ampSys b r s k d)
          (ones s ++ (ones r).drop ((ones r).drop j).length)
          ((ones r).take j ++ ones s)
        have h1 : (ones r).take j = ones j := by
          rw [ones, replicate_take_eq]; have : min r j = j := by omega
          rw [this]; rfl
        have hlen_drop : ((ones r).drop j).length = r - j := by
          rw [List.length_drop, ones_length]
        have h2 : (ones r).drop ((ones r).drop j).length = ones j := by
          rw [hlen_drop, ones, replicate_drop_eq]
          have : r - (r - j) = j := by omega
          rw [this]; rfl
        rw [h1, h2, ← ones_add, ← ones_add, Nat.add_comm s j]
        exact .refl _

/-! ### Necessity / Sharpness (`→`) of the Euler-Fermat Confluence Dichotomy -/

def redZero (k d n : Nat) : Nat :=
  if n < k then n else k + (n - k) % d

theorem redZero_lt (k d n : Nat) (hd : 1 ≤ d) : redZero k d n < k + d := by
  unfold redZero
  split
  · omega
  · have : (n - k) % d < d := Nat.mod_lt _ (by omega)
    omega

theorem amp_redZero_steps (b r s k d n m : Nat) :
    Steps (ampSys b r s k d) (zeros n ++ ones m) (zeros (redZero k d n) ++ ones m) := by
  unfold redZero
  split
  · exact .refl _
  · rename_i hge
    have hkn : k ≤ n := by omega
    have hdiv : n = (k + (n - k) % d) + ((n - k) / d) * d := by
      have hdm := Nat.div_add_mod (n - k) d
      rw [Nat.mul_comm] at hdm
      omega
    have hcomp : Steps (ampSys b r s k d) (zeros n) (zeros (k + (n - k) % d)) := by
      have hstep := amp_compress_zeros b r s k d (k + (n - k) % d) ((n - k) / d) (by omega)
      rw [← hdiv] at hstep
      exact hstep
    have := hcomp.context [] (ones m)
    simpa using this

private theorem no_one_zero_in_zeros_ones (z o : Nat) (p s : Word) :
    p ++ [true, false] ++ s ≠ zeros z ++ ones o := by
  intro heq
  have h1 := congrArg (fun w => w[p.length]?) heq
  have h2 := congrArg (fun w => w[p.length + 1]?) heq
  have hl1 : (p ++ [true, false] ++ s)[p.length]? = some true := by
    rw [List.append_assoc, List.getElem?_append_right (Nat.le_refl _)]
    simp
  have hl2 : (p ++ [true, false] ++ s)[p.length + 1]? = some false := by
    rw [List.append_assoc, List.getElem?_append_right (by omega)]
    have : p.length + 1 - p.length = 1 := by omega
    rw [this]; simp
  rw [hl1] at h1; rw [hl2] at h2
  by_cases hpz : p.length < z
  · have hget : (zeros z ++ ones o)[p.length]? = some false := by
      rw [List.getElem?_append_left (by rw [zeros_length]; exact hpz)]
      rw [zeros, List.getElem?_replicate]
      simp [hpz]
    rw [hget] at h1; cases h1
  · have hge : z ≤ p.length + 1 := by omega
    have hget : (zeros z ++ ones o)[p.length + 1]? = (ones o)[p.length + 1 - z]? := by
      rw [List.getElem?_append_right (by rw [zeros_length]; omega)]
      rw [zeros_length]
    rw [hget] at h2
    rw [ones, List.getElem?_replicate] at h2
    split at h2 <;> cases h2

private theorem count_zeros (n : Nat) : (zeros n).count false = n := by
  induction n with
  | zero => rfl
  | succ n' ih => simp [zeros_succ, ih]

private theorem count_ones_false (n : Nat) : (ones n).count false = 0 := by
  induction n with
  | zero => rfl
  | succ n' ih => simp [ones_succ, ih]

private theorem count_ones (n : Nat) : (ones n).count true = n := by
  induction n with
  | zero => rfl
  | succ n' ih => simp [ones_succ, ih]

private theorem count_zeros_true (n : Nat) : (zeros n).count true = 0 := by
  induction n with
  | zero => rfl
  | succ n' ih => simp [zeros_succ, ih]

theorem amp_nf_zeros_ones (b r s k d z o : Nat) (hz : z < k + d) (ho : o < r) :
    IsNormalForm (ampSys b r s k d) (zeros z ++ ones o) := by
  intro v hstep
  obtain ⟨p, suf, l, r', hmem, heq, _⟩ := hstep.dest
  simp only [ampSys, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact no_one_zero_in_zeros_ones z o p suf heq.symm
  · have hc := congrArg (List.count false) heq
    simp only [List.count_append, count_zeros, count_ones_false] at hc
    omega
  · have hc := congrArg (List.count true) heq
    simp only [List.count_append, count_ones, count_zeros_true] at hc
    omega

/-- Exact Euler-Fermat Confluence Dichotomy Theorem for the 5-parameter family `ampSys b r s k d`:
Globally confluent (on ALL bit-strings of arbitrary length) if and only if
`k ≤ b ^ s ∧ d ∣ (b ^ r - b ^ s)`. -/
theorem ampSys_confluent_iff (b r s k d : Nat)
    (hb : 2 ≤ b) (hrs : s < r) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    Confluent (ampSys b r s k d) ↔ (k ≤ b ^ s ∧ d ∣ (b ^ r - b ^ s)) := by
  constructor
  · intro hConf
    -- Witness word: w = 1^r 0
    have hLeft : Steps (ampSys b r s k d) (ones r ++ [false]) (zeros (redZero k d (b ^ s)) ++ ones s) := by
      have hs1 : Step (ampSys b r s k d) (ones r ++ [false]) (ones s ++ [false]) := by
        have := (amp_rule3_step b r s k d).context [] [false]
        simpa using this
      have hs2 : Steps (ampSys b r s k d) (ones s ++ [false]) (zeros (b ^ s) ++ ones s) := by
        have := amp_push_ones_zeros b r s k d s 1
        simpa [zeros] using this
      exact .tail hs1 (hs2.trans (amp_redZero_steps b r s k d (b ^ s) s))
    have hRight : Steps (ampSys b r s k d) (ones r ++ [false]) (zeros (redZero k d (b ^ r)) ++ ones s) := by
      have hs1 : Steps (ampSys b r s k d) (ones r ++ [false]) (zeros (b ^ r) ++ ones r) := by
        have := amp_push_ones_zeros b r s k d r 1
        simpa [zeros] using this
      have hs2 : Step (ampSys b r s k d) (zeros (b ^ r) ++ ones r) (zeros (b ^ r) ++ ones s) := by
        have := (amp_rule3_step b r s k d).context (zeros (b ^ r)) []
        simpa using this
      exact hs1.trans (.tail hs2 (amp_redZero_steps b r s k d (b ^ r) s))
    have hnfL := amp_nf_zeros_ones b r s k d (redZero k d (b ^ s)) s (redZero_lt k d _ hd) hrs
    have hnfR := amp_nf_zeros_ones b r s k d (redZero k d (b ^ r)) s (redZero_lt k d _ hd) hrs
    obtain ⟨z, hzL, hzR⟩ := hConf _ _ _ hLeft hRight
    have hEqW : zeros (redZero k d (b ^ s)) ++ ones s = zeros (redZero k d (b ^ r)) ++ ones s :=
      (hzL.nf_eq hnfL).trans (hzR.nf_eq hnfR).symm
    have hEqLen := congrArg List.length hEqW
    simp only [List.length_append, zeros_length, ones_length] at hEqLen
    have hRedEq : redZero k d (b ^ s) = redZero k d (b ^ r) := by omega
    have hPowLt : b ^ s < b ^ r := pow_lt_pow_of_lt hb hrs
    have hks : k ≤ b ^ s := by
      by_cases hlt : b ^ s < k
      · unfold redZero at hRedEq
        simp only [hlt, ↓reduceIte] at hRedEq
        split at hRedEq
        · omega
        · omega
      · omega
    have hkr : k ≤ b ^ r := by omega
    have hModEq : (b ^ s - k) % d = (b ^ r - k) % d := by
      unfold redZero at hRedEq
      have h1 : ¬(b ^ s < k) := by omega
      have h2 : ¬(b ^ r < k) := by omega
      simp only [h1, h2, ↓reduceIte] at hRedEq
      omega
    have hdvd : d ∣ (b ^ r - b ^ s) := by
      have hsub : b ^ r - b ^ s = (b ^ r - k) - (b ^ s - k) := by omega
      have hdm1 := Nat.div_add_mod (b ^ r - k) d
      have hdm2 := Nat.div_add_mod (b ^ s - k) d
      have hqle : (b ^ s - k) / d ≤ (b ^ r - k) / d := Nat.div_le_div_right (by omega)
      refine ⟨(b ^ r - k) / d - (b ^ s - k) / d, ?_⟩
      rw [Nat.mul_sub_left_distrib]
      omega
    exact ⟨hks, hdvd⟩
  · intro ⟨hks, hdvd⟩
    exact ampSys_confluent_of_cond b r s k d hb hrs hk hd hks hdvd

theorem ampSys_uniqueNormalForms (b r s k d : Nat)
    (hb : 2 ≤ b) (hrs : s < r) (hk : 1 ≤ k) (hd : 1 ≤ d)
    (hks : k ≤ b ^ s) (hdvd : d ∣ (b ^ r - b ^ s)) :
    UniqueNormalForms (ampSys b r s k d) :=
  uniqueNormalForms_of_term_conf
    (ampSys_terminating b r s k d hb hrs hk hd)
    (ampSys_confluent_of_cond b r s k d hb hrs hk hd hks hdvd)

/-! ## Section 6: Concrete Novel Binary Systems Discharged Directly via `decide` -/

def mod3Cert : ConfluenceCert := {
  layers := [
    { dim := 2, m0 := [[1, 0], [0, 1]], m1 := [[1, 1], [0, 1]] },
    { dim := 3, m0 := [[1, 0, 0], [0, 1, 1], [0, 0, 1]], m1 := [[1, 1, 0], [0, 1, 0], [0, 0, 1]] }
  ],
  witnesses := [
    ([], []),
    ([(2, 1), (1, 3)], [(2, 0), (1, 2)]),
    ([(0, 1)], [(2, 0)]),
    ([(2, 1)], [(2, 0), (0, 2)]),
    ([], [(0, 0), (2, 1)]),
    ([], []),
    ([], [(2, 0)]),
    ([], [(2, 0), (1, 2)]),
    ([], [])
  ]
}

theorem mod3_cert_ok : checkCert mod3SRS mod3Cert = true := by decide

theorem mod3_certified :
    Terminating mod3SRS ∧ Confluent mod3SRS ∧ UniqueNormalForms mod3SRS :=
  cert_sound mod3SRS mod3Cert mod3_cert_ok

/-- System 2: Fermat-Order Doubling Mod-7 `S(2, 4, 1, 1, 7)` (Length-Increasing, 2×2 Matrix). -/
def fermat7SRS : SRS := [
  ([true, false], [false, false, true]),
  ([false, false, false, false, false, false, false, false], [false]),
  ([true, true, true, true], [true])
]

def fermat7Cert : ConfluenceCert := {
  layers := [
    { dim := 2, m0 := [[1, 1], [0, 1]], m1 := [[3, 1], [0, 1]] }
  ],
  witnesses := [
    ([], []),
    ([(0, 2), (0, 4), (0, 6), (0, 8), (0, 10), (0, 12), (0, 14), (1, 0), (1, 0)], [(0, 0)]),
    ([], []),
    ([], []),
    ([], []),
    ([], []),
    ([], []),
    ([], []),
    ([], []),
    ([], []),
    ([(0, 0)], [(0, 2), (0, 1), (0, 0), (0, 2), (0, 5), (0, 4), (0, 6), (0, 10), (0, 9), (0, 8),
                (0, 10), (0, 13), (0, 12), (0, 14), (1, 0), (1, 0), (2, 2)]),
    ([], []),
    ([], []),
    ([], []),
    ([], [])
  ]
}

theorem fermat7_cert_ok : checkCert fermat7SRS fermat7Cert = true := by decide

theorem fermat7_certified :
    Terminating fermat7SRS ∧ Confluent fermat7SRS ∧ UniqueNormalForms fermat7SRS :=
  cert_sound fermat7SRS fermat7Cert fermat7_cert_ok

/-- System 3: Length-Increasing Affine Emission Doubling (`c = 2`, 2×2 Matrix, 10 CPs). -/
def affineEmitSRS : SRS := [
  ([true, false], [false, false, true]),
  ([false, false, false, false], [false, false]),
  ([true, true, true], [false, false, true])
]

def affineEmitCert : ConfluenceCert := {
  layers := [
    { dim := 2, m0 := [[1, 1], [0, 1]], m1 := [[3, 3], [0, 1]] }
  ],
  witnesses := [
    ([], []),
    ([(0, 2), (0, 4), (0, 6), (1, 0), (1, 0), (1, 0)], [(0, 0), (0, 2), (1, 0)]),
    ([], []),
    ([], []),
    ([], []),
    ([], []),
    ([(0, 2), (1, 0)], [(0, 1), (0, 0), (0, 2), (0, 5), (0, 4), (0, 6), (1, 0), (1, 0), (1, 0), (2, 2), (1, 0)]),
    ([], []),
    ([], [(0, 0), (0, 2), (1, 0)]),
    ([(2, 2), (1, 0)], [(0, 1), (0, 0), (0, 2), (0, 5), (0, 4), (0, 6), (1, 0), (1, 0), (1, 0), (2, 2), (1, 0)])
  ]
}

theorem affineEmit_cert_ok : checkCert affineEmitSRS affineEmitCert = true := by decide

theorem affineEmit_certified :
    Terminating affineEmitSRS ∧ Confluent affineEmitSRS ∧ UniqueNormalForms affineEmitSRS :=
  cert_sound affineEmitSRS affineEmitCert affineEmit_cert_ok

/-- System 4: Mixed Increasing/Preserving/Decreasing Bubble-Emission System (2-Layer: 2×2 + 3×3). -/
def bubbleEmitSRS : SRS := [
  ([true, true], [false, true, false]),
  ([true, false], [false, true]),
  ([false, false, false, false], [false, false])
]

def bubbleEmitCert : ConfluenceCert := {
  layers := [
    { dim := 2, m0 := [[1, 0], [0, 1]], m1 := [[1, 1], [0, 1]] },
    { dim := 3, m0 := [[1, 0, 1], [0, 1, 1], [0, 0, 1]], m1 := [[1, 1, 0], [0, 1, 0], [0, 0, 1]] }
  ],
  witnesses := [
    ([], []),
    ([(1, 1), (0, 2), (1, 3), (2, 0)], [(1, 0), (0, 1), (1, 2), (1, 3), (2, 0)]),
    ([(1, 1), (1, 2)], [(1, 0), (0, 1), (1, 2)]),
    ([], []),
    ([(1, 1), (1, 2), (1, 3), (2, 0)], [(1, 0), (1, 1)]),
    ([], []),
    ([], []),
    ([], []),
    ([], [])
  ]
}

theorem bubbleEmit_cert_ok : checkCert bubbleEmitSRS bubbleEmitCert = true := by decide

theorem bubbleEmit_certified :
    Terminating bubbleEmitSRS ∧ Confluent bubbleEmitSRS ∧ UniqueNormalForms bubbleEmitSRS :=
  cert_sound bubbleEmitSRS bubbleEmitCert bubbleEmit_cert_ok

/-! ### Semantic Completeness of the Binary Mod-3 Local Normalizer (`mod3SRS`) -/

theorem binValAux_eq (acc : Nat) (w : Word) :
    binValAux acc w = acc * 2 ^ w.length + binVal w := by
  induction w generalizing acc with
  | nil => simp [binValAux, binVal]
  | cons b w' ih =>
    unfold binVal
    simp only [binValAux, List.length_cons, Nat.mul_zero, Nat.zero_add]
    rw [ih (2 * acc + if b then 1 else 0), ih (if b then 1 else 0)]
    rw [Nat.pow_succ]
    have : (2 * acc + (if b then 1 else 0)) * 2 ^ w'.length =
           acc * (2 ^ w'.length * 2) + (if b then 1 else 0) * 2 ^ w'.length := by
      rw [Nat.add_mul, Nat.mul_comm (2 ^ w'.length) 2, ← Nat.mul_assoc, Nat.mul_comm 2 acc, Nat.mul_assoc]
    omega

theorem binVal_append (u v : Word) :
    binVal (u ++ v) = binVal u * 2 ^ v.length + binVal v := by
  unfold binVal
  have hAux : ∀ acc, binValAux acc (u ++ v) = binValAux (binValAux acc u) v := by
    induction u with
    | nil => intro acc; rfl
    | cons b u' ih => intro acc; simp [binValAux, ih]
  rw [hAux 0, binValAux_eq]
  rfl

theorem binVal_zeros (n : Nat) : binVal (zeros n) = 0 := by
  unfold binVal
  have h : ∀ k, binValAux 0 (zeros k) = 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k' ih => simpa [zeros_succ, binValAux] using ih
  exact h n

theorem mod3_step_invariant {u v : Word} (h : Step mod3SRS u v) :
    u.length = v.length ∧ binVal u % 3 = binVal v % 3 := by
  obtain ⟨p, s, l, r, hmem, hu, hv⟩ := h.dest
  subst hu; subst hv
  have hrule : l.length = r.length ∧ binVal l % 3 = binVal r % 3 := by
    simp only [mod3SRS, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  constructor
  · simp [hrule.1]
  · rw [binVal_append, binVal_append, binVal_append, binVal_append, hrule.1]
    have h1 : (binVal p * 2 ^ r.length + binVal l) % 3 =
              (binVal p * 2 ^ r.length + binVal r) % 3 := by
      rw [Nat.add_mod, hrule.2, ← Nat.add_mod]
    rw [Nat.add_mod, Nat.mul_mod, h1, ← Nat.mul_mod, ← Nat.add_mod]

theorem mod3_steps_invariant {u v : Word} (h : Steps mod3SRS u v) :
    u.length = v.length ∧ binVal u % 3 = binVal v % 3 := by
  induction h with
  | refl _ => exact ⟨rfl, rfl⟩
  | tail hs _ ih =>
    have h1 := mod3_step_invariant hs
    exact ⟨h1.1.trans ih.1, h1.2.trans ih.2⟩

theorem mod3_convertible_invariant {u v : Word} (h : Convertible mod3SRS u v) :
    u.length = v.length ∧ binVal u % 3 = binVal v % 3 := by
  induction h with
  | refl _ => exact ⟨rfl, rfl⟩
  | fwd hs _ ih =>
    have h1 := mod3_step_invariant hs
    exact ⟨h1.1.trans ih.1, h1.2.trans ih.2⟩
  | bwd hs _ ih =>
    have h1 := mod3_step_invariant hs
    exact ⟨h1.1.symm.trans ih.1, h1.2.symm.trans ih.2⟩

theorem mod3_nf_tail {b : Bool} {w : Word} (hnf : IsNormalForm mod3SRS (b :: w)) :
    IsNormalForm mod3SRS w := by
  intro v hs
  have hs' := hs.context [b] []
  simp only [List.singleton_append, List.append_nil] at hs'
  exact hnf _ hs'

/-- Structural Classification of ALL Normal Forms of `mod3SRS`:
Every normal form of arbitrary length `n` is uniquely determined by `(n, binVal w % 3)`:
`0^n` (mod 0), `0^(n-1) 1` (mod 1), or `0^(n-2) 10` (mod 2). -/
theorem mod3_nf_classify (w : Word) (hnf : IsNormalForm mod3SRS w) :
    w = zeros w.length ∨
    (1 ≤ w.length ∧ w = zeros (w.length - 1) ++ [true]) ∨
    (2 ≤ w.length ∧ w = zeros (w.length - 2) ++ [true, false]) := by
  induction w with
  | nil => left; rfl
  | cons b rest ih =>
    cases b with
    | false =>
      rcases ih (mod3_nf_tail hnf) with h0 | ⟨h1, heq1⟩ | ⟨h2, heq2⟩
      · left
        simp only [List.length_cons, zeros_succ]
        exact congrArg (false :: ·) h0
      · right; left
        refine ⟨by simp, ?_⟩
        simp only [List.length_cons, Nat.add_sub_cancel]
        have hEq : rest.length = (rest.length - 1) + 1 := by omega
        rw [hEq, zeros_succ, List.cons_append]
        exact congrArg (false :: ·) heq1
      · right; right
        refine ⟨by simp; omega, ?_⟩
        have hEq : (false :: rest).length - 2 = (rest.length - 2) + 1 := by simp; omega
        rw [hEq, zeros_succ, List.cons_append]
        exact congrArg (false :: ·) heq2
    | true =>
      cases rest with
      | nil =>
        right; left; exact ⟨by simp, rfl⟩
      | cons b2 rest2 =>
        cases b2 with
        | true =>
          -- Starts with `11`: contradicts NF!
          exfalso
          have hstep : Step mod3SRS ([] ++ [true, true] ++ rest2) ([] ++ [false, false] ++ rest2) :=
            Step.mk [] rest2 [true, true] [false, false] (List.Mem.tail _ (List.Mem.head _))
          exact hnf _ (by simpa using hstep)
        | false =>
          cases rest2 with
          | nil =>
            right; right; exact ⟨by simp, rfl⟩
          | cons b3 rest3 =>
            cases b3 with
            | false =>
              -- Starts with `100`: contradicts NF!
              exfalso
              have hstep : Step mod3SRS ([] ++ [true, false, false] ++ rest3) ([] ++ [false, false, true] ++ rest3) :=
                Step.mk [] rest3 [true, false, false] [false, false, true]
                  (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
              exact hnf _ (by simpa using hstep)
            | true =>
              -- Starts with `101`: contradicts NF!
              exfalso
              have hstep : Step mod3SRS ([] ++ [true, false, true] ++ rest3) ([] ++ [false, true, false] ++ rest3) :=
                Step.mk [] rest3 [true, false, true] [false, true, false] (List.Mem.head _)
              exact hnf _ (by simpa using hstep)

theorem mod3_nf_eq_of_len_mod {u v : Word}
    (hu : IsNormalForm mod3SRS u) (hv : IsNormalForm mod3SRS v)
    (hlen : u.length = v.length) (hmod : binVal u % 3 = binVal v % 3) : u = v := by
  have hval0 : ∀ n, binVal (zeros n) % 3 = 0 := fun n => by rw [binVal_zeros]
  have hval1 : ∀ n, binVal (zeros n ++ [true]) % 3 = 1 := fun n => by
    rw [binVal_append, binVal_zeros]; rfl
  have hval2 : ∀ n, binVal (zeros n ++ [true, false]) % 3 = 2 := fun n => by
    rw [binVal_append, binVal_zeros]; rfl
  rcases mod3_nf_classify u hu with hu0 | ⟨hu1l, hu1⟩ | ⟨hu2l, hu2⟩ <;>
  rcases mod3_nf_classify v hv with hv0 | ⟨hv1l, hv1⟩ | ⟨hv2l, hv2⟩
  · rw [hu0, hv0, hlen]
  · rw [hu0, hv1, hval0, hval1] at hmod; cases hmod
  · rw [hu0, hv2, hval0, hval2] at hmod; cases hmod
  · rw [hu1, hv0, hval1, hval0] at hmod; cases hmod
  · rw [hu1, hv1, hlen]
  · rw [hu1, hv2, hval1, hval2] at hmod; cases hmod
  · rw [hu2, hv0, hval2, hval0] at hmod; cases hmod
  · rw [hu2, hv1, hval2, hval1] at hmod; cases hmod
  · rw [hu2, hv2, hlen]

/-- Complete Semantic Characterization of the minimal 3-rule `mod3SRS` for ALL bit-strings:
Two arbitrary bit-strings are convertible under `mod3SRS` IF AND ONLY IF they have the same
bit-width and the same binary residue modulo 3. -/
theorem mod3_convertible_iff (u v : Word) :
    Convertible mod3SRS u v ↔ u.length = v.length ∧ binVal u % 3 = binVal v % 3 := by
  constructor
  · exact mod3_convertible_invariant
  · intro ⟨hlen, hmod⟩
    rw [convertible_iff_normalize_eq mod3_cert_ok u v]
    have hTerm := (cert_sound mod3SRS mod3Cert mod3_cert_ok).1
    have huInv := mod3_steps_invariant (normalize_steps mod3SRS hTerm u)
    have hvInv := mod3_steps_invariant (normalize_steps mod3SRS hTerm v)
    exact mod3_nf_eq_of_len_mod
      (normalize_nf mod3SRS hTerm u)
      (normalize_nf mod3SRS hTerm v)
      (by omega)
      (by omega)

/-! ## Section 6B: Infinite Parametric Odd-Modulus Families (Mersenne `2^m - 1` & Fermat `2^m + 1`) -/

/-- General Semantic-Invariant Confluence Meta-Theorem:
If a terminating SRS preserves an invariant `inv` that is injective on normal forms,
then it is globally confluent, has unique normal forms, and `Convertible R u v ↔ inv u = inv v`. -/
theorem confluent_of_term_invariant {R : SRS} {α : Type} (inv : Word → α)
    (hTerm : Terminating R)
    (hInv : ∀ u v, Step R u v → inv u = inv v)
    (hNFInj : ∀ n₁ n₂, IsNormalForm R n₁ → IsNormalForm R n₂ → inv n₁ = inv n₂ → n₁ = n₂) :
    Confluent R ∧ UniqueNormalForms R ∧ (∀ u v, Convertible R u v ↔ inv u = inv v) := by
  have hStepsInv : ∀ u v, Steps R u v → inv u = inv v := by
    intro u v hs
    induction hs with
    | refl _ => rfl
    | tail h1 _ ih => exact (hInv _ _ h1).trans ih
  have hConvInv : ∀ u v, Convertible R u v → inv u = inv v := by
    intro u v hc
    induction hc with
    | refl _ => rfl
    | fwd h1 _ ih => exact (hInv _ _ h1).trans ih
    | bwd h1 _ ih => exact (hInv _ _ h1).symm.trans ih
  have hConf : Confluent R := by
    intro u v₁ v₂ h₁ h₂
    let n₁ := normalize R hTerm v₁
    let n₂ := normalize R hTerm v₂
    have hn₁_s : Steps R v₁ n₁ := normalize_steps R hTerm v₁
    have hn₂_s : Steps R v₂ n₂ := normalize_steps R hTerm v₂
    have hInvEq : inv n₁ = inv n₂ :=
      (hStepsInv u n₁ (h₁.trans hn₁_s)).symm.trans (hStepsInv u n₂ (h₂.trans hn₂_s))
    have hEq : n₁ = n₂ := hNFInj n₁ n₂ (normalize_nf R hTerm v₁) (normalize_nf R hTerm v₂) hInvEq
    exact ⟨n₁, hn₁_s, hEq ▸ hn₂_s⟩
  have hUNF : UniqueNormalForms R := uniqueNormalForms_of_term_conf hTerm hConf
  have hIff : ∀ u v, Convertible R u v ↔ inv u = inv v := by
    intro u v
    constructor
    · exact hConvInv u v
    · intro hEq
      let nu := normalize R hTerm u
      let nv := normalize R hTerm v
      have hu_s : Steps R u nu := normalize_steps R hTerm u
      have hv_s : Steps R v nv := normalize_steps R hTerm v
      have hInvEq : inv nu = inv nv :=
        (hStepsInv u nu hu_s).symm.trans (hEq.trans (hStepsInv v nv hv_s))
      have hNEq : nu = nv := hNFInj nu nv (normalize_nf R hTerm u) (normalize_nf R hTerm v) hInvEq
      exact (Convertible.of_steps hu_s).trans (hNEq ▸ (Convertible.of_steps hv_s).symm)
  exact ⟨hConf, hUNF, hIff⟩

/-- Universal 2×2 Binary-Value Matrix Layer:
`matEval 2 [[1,0],[0,2]] [[1,1],[0,2]] w = [[1, binVal w], [0, 2^w.length]]`. -/
def binValLayer : MatrixLayer :=
  { dim := 2, m0 := [[1, 0], [0, 2]], m1 := [[1, 1], [0, 2]] }

theorem binVal_cons (b : Bool) (w : Word) :
    binVal (b :: w) = (if b then 1 else 0) * 2 ^ w.length + binVal w := by
  have h : b :: w = [b] ++ w := rfl
  rw [h, binVal_append]
  cases b <;> rfl

theorem binVal_lt_pow (w : Word) : binVal w < 2 ^ w.length := by
  induction w with
  | nil => decide
  | cons b w' ih =>
    rw [binVal_cons, List.length_cons, Nat.pow_succ]
    cases b <;> simp <;> omega

theorem binVal_ones (m : Nat) : binVal (ones m) = 2 ^ m - 1 := by
  induction m with
  | zero => rfl
  | succ m' ih =>
    rw [ones_succ, binVal_cons, ones_length, ih, Nat.pow_succ]
    have hpos : 1 ≤ 2 ^ m' := Nat.one_le_pow m' 2 (by decide)
    simp; omega

theorem binVal_injective_of_length_eq {u v : Word}
    (hlen : u.length = v.length) (hval : binVal u = binVal v) : u = v := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons a u' ih =>
    cases v with
    | nil => simp at hlen
    | cons b v' =>
      have hlen' : u'.length = v'.length := by simpa using hlen
      rw [binVal_cons, binVal_cons, hlen'] at hval
      have hu := binVal_lt_pow u'
      have hv := binVal_lt_pow v'
      rw [hlen'] at hu
      have hab : a = b := by
        cases a <;> cases b <;> simp at hval ⊢ <;> omega
      subst hab
      have hval' : binVal u' = binVal v' := by cases a <;> simp at hval <;> omega
      exact congrArg (a :: ·) (ih hlen' hval')

theorem toBits_length (m x : Nat) : (toBits m x).length = m := by
  induction m generalizing x with
  | zero => rfl
  | succ m' ih => simp [toBits, ih]

theorem binVal_toBits (m x : Nat) (hx : x < 2 ^ m) : binVal (toBits m x) = x := by
  induction m generalizing x with
  | zero => simp [toBits, binVal, binValAux]; omega
  | succ m' ih =>
    simp only [toBits]
    rw [binVal_append]
    have hdiv : x / 2 < 2 ^ m' := by rw [Nat.pow_succ] at hx; omega
    rw [ih (x / 2) hdiv]
    have hbit : binVal [decide (x % 2 = 1)] = x % 2 := by
      unfold binVal binValAux
      by_cases h1 : x % 2 = 1
      · simp [h1, binValAux]
      · have h0 : x % 2 = 0 := by omega
        simp [h0, binValAux]
    simp only [List.length_cons, List.length_nil, hbit]
    omega

theorem toBits_binVal (w : Word) : toBits w.length (binVal w) = w :=
  binVal_injective_of_length_eq (toBits_length w.length (binVal w))
    (binVal_toBits w.length (binVal w) (binVal_lt_pow w))

theorem binValLayer_eval (w : Word) :
    matEval 2 [[1, 0], [0, 2]] [[1, 1], [0, 2]] w = [[1, binVal w], [0, 2 ^ w.length]] := by
  induction w with
  | nil => rfl
  | cons b w' ih =>
    simp only [matEval, ih]
    cases b with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [matMul2_eq, binVal_cons, List.length_cons, Nat.pow_succ]
      simp [Nat.mul_comm]
    | true =>
      simp only [↓reduceIte]
      rw [matMul2_eq, binVal_cons, List.length_cons, Nat.pow_succ]
      simp [Nat.add_comm, Nat.mul_comm]

/-- Universal Matrix Termination for ANY length-preserving value-decreasing binary SRS via `binValLayer`. -/
theorem binValLayer_terminating {R : SRS}
    (hRules : ∀ r ∈ R, r.1 ≠ [] ∧ r.1.length = r.2.length ∧ binVal r.2 < binVal r.1) :
    Terminating R := by
  apply checkTermination_sound (layers := [binValLayer])
  have hLV : checkLayerValid binValLayer = true := by
    simp [checkLayerValid, binValLayer, checkMatWF, matGet]
  have hAll : R.all (fun r => (!r.1.isEmpty) && checkRuleAgainstLayers [binValLayer] r) = true := by
    rw [List.all_eq_true]
    intro r hr
    obtain ⟨hne, hlen, hlt⟩ := hRules r hr
    have hneB : (!r.1.isEmpty) = true := by
      cases h1 : r.1 with
      | nil => exact absurd h1 hne
      | cons _ _ => rfl
    have hgt : matGtTR 2 [[1, binVal r.1], [0, 2 ^ r.1.length]]
                         [[1, binVal r.2], [0, 2 ^ r.2.length]] = true := by
      rw [hlen]
      simp [matGtTR, matGe, List.range, List.range.loop, matGet]
      omega
    have hcheck : checkRuleAgainstLayers [binValLayer] r = true := by
      rcases r with ⟨l, rhs⟩
      simp only [checkRuleAgainstLayers, binValLayer, binValLayer_eval, hgt, ↓reduceIte]
    simp [hneB, hcheck]
  simp [checkTermination, hLV, hAll]

theorem step_len_mod_invariant {R : SRS} {M : Nat}
    (hRules : ∀ r ∈ R, r.1.length = r.2.length ∧ binVal r.1 % M = binVal r.2 % M)
    {u v : Word} (h : Step R u v) :
    u.length = v.length ∧ binVal u % M = binVal v % M := by
  obtain ⟨p, s, l, r, hmem, hu, hv⟩ := h.dest
  subst hu; subst hv
  obtain ⟨hlen, hmod⟩ := hRules (l, r) hmem
  constructor
  · simp [hlen]
  · rw [binVal_append, binVal_append, binVal_append, binVal_append, hlen]
    have h1 : (binVal p * 2 ^ r.length + binVal l) % M =
              (binVal p * 2 ^ r.length + binVal r) % M := by
      rw [Nat.add_mod, hmod, ← Nat.add_mod]
    rw [Nat.add_mod, Nat.mul_mod, h1, ← Nat.mul_mod, ← Nat.add_mod]

/-! ### Family 2: Parametric Irredundant Mersenne Mod-`(2^m - 1)` Local Normalizers (`∀ m ≥ 2`) -/

theorem mersenneSRS_rules_spec (m : Nat) (hm : 2 ≤ m) :
    ∀ r ∈ mersenneSRS m,
      r.1 ≠ [] ∧ r.1.length = r.2.length ∧ binVal r.2 < binVal r.1 ∧
      binVal r.1 % (2 ^ m - 1) = binVal r.2 % (2 ^ m - 1) := by
  have h2m : 4 ≤ 2 ^ m := by
    have : 2 ^ 2 ≤ 2 ^ m := pow_le_pow_of_le (by decide) hm
    simpa using this
  intro r hr
  simp only [mersenneSRS, List.mem_cons, List.mem_map, List.mem_range] at hr
  rcases hr with rfl | ⟨x, hx, rfl⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro h; have := congrArg List.length h; rw [ones_length] at this; simp at this; omega
    · simp [ones_length, zeros_length]
    · rw [binVal_ones, binVal_zeros]; omega
    · rw [binVal_ones, binVal_zeros, Nat.mod_self, Nat.zero_mod]
  · have hlen1 : (true :: toBits m x).length = m + 1 := by simp [toBits_length]
    have hlen2 : (false :: toBits m (x + 1)).length = m + 1 := by simp [toBits_length]
    have hv1 : binVal (true :: toBits m x) = 2 ^ m + x := by
      rw [binVal_cons, toBits_length, binVal_toBits m x (by omega)]; simp
    have hv2 : binVal (false :: toBits m (x + 1)) = x + 1 := by
      rw [binVal_cons, toBits_length, binVal_toBits m (x + 1) (by omega)]; simp
    refine ⟨by simp, by dsimp only; omega, by dsimp only; omega, ?_⟩
    dsimp only
    rw [hv1, hv2]
    have heq : 2 ^ m + x = (2 ^ m - 1) + (x + 1) := by omega
    rw [heq, Nat.add_mod_left]

theorem mersenneSRS_terminating (m : Nat) (hm : 2 ≤ m) : Terminating (mersenneSRS m) :=
  binValLayer_terminating (fun r hr =>
    let ⟨h1, h2, h3, _⟩ := mersenneSRS_rules_spec m hm r hr; ⟨h1, h2, h3⟩)

theorem mersenneSRS_nf_binVal_lt (m : Nat) (hm : 2 ≤ m) :
    ∀ w, IsNormalForm (mersenneSRS m) w → binVal w < 2 ^ m - 1 := by
  have h2m : 4 ≤ 2 ^ m := by
    have : 2 ^ 2 ≤ 2 ^ m := pow_le_pow_of_le (by decide) hm
    simpa using this
  intro w
  induction w with
  | nil => intro _; simp [binVal, binValAux]; omega
  | cons b rest ih =>
    intro hnf
    have hnf_rest : IsNormalForm (mersenneSRS m) rest := by
      intro v hs
      have hs' := hs.context [b] []
      simp only [List.singleton_append, List.append_nil] at hs'
      exact hnf _ hs'
    cases b with
    | false =>
      rw [binVal_cons]; simp; exact ih hnf_rest
    | true =>
      by_cases hlt : rest.length < m - 1
      · have hlen : (true :: rest).length ≤ m - 1 := by simp; omega
        have hv := binVal_lt_pow (true :: rest)
        have hpow : 2 ^ (true :: rest).length ≤ 2 ^ (m - 1) := pow_le_pow_of_le (by decide) hlen
        have hhalf : 2 ^ (m - 1) * 2 = 2 ^ m := by
          have : m - 1 + 1 = m := by omega
          calc 2 ^ (m - 1) * 2 = 2 ^ (m - 1 + 1) := (Nat.pow_succ 2 (m - 1)).symm
               _ = 2 ^ m := by rw [this]
        have hpos : 1 ≤ 2 ^ (m - 1) := Nat.one_le_pow (m - 1) 2 (by decide)
        omega
      · by_cases heq : rest.length = m - 1
        · have hlen : (true :: rest).length = m := by simp; omega
          have hv := binVal_lt_pow (true :: rest)
          rw [hlen] at hv
          by_cases hmax : binVal (true :: rest) = 2 ^ m - 1
          · exfalso
            have hEqOnes : true :: rest = ones m :=
              binVal_injective_of_length_eq (by rw [hlen, ones_length]) (by rw [hmax, binVal_ones])
            have hstep : Step (mersenneSRS m) ([] ++ ones m ++ []) ([] ++ zeros m ++ []) :=
              Step.mk [] [] (ones m) (zeros m) (List.Mem.head _)
            simp only [List.nil_append, List.append_nil] at hstep
            rw [← hEqOnes] at hstep
            exact hnf _ hstep
          · omega
        · -- `m ≤ rest.length`: split `rest = u ++ s` with `u.length = m`
          exfalso
          have hge : m ≤ rest.length := by omega
          let u := rest.take m
          let s := rest.drop m
          have hulen : u.length = m := by simp [u, hge]
          have hrest : rest = u ++ s := (List.take_append_drop m rest).symm
          let x := binVal u
          have hxlt : x < 2 ^ m := by have := binVal_lt_pow u; rw [hulen] at this; exact this
          by_cases hx1 : x < 2 ^ m - 2
          · have hu : u = toBits m x := by
              rw [← hulen]; exact (toBits_binVal u).symm
            have hmem : (true :: toBits m x, false :: toBits m (x + 1)) ∈ mersenneSRS m := by
              unfold mersenneSRS
              exact List.Mem.tail _ (List.mem_map.mpr ⟨x, List.mem_range.mpr hx1, rfl⟩)
            have hstep : Step (mersenneSRS m) ([] ++ (true :: toBits m x) ++ s)
                ([] ++ (false :: toBits m (x + 1)) ++ s) :=
              Step.mk [] s _ _ hmem
            have hw : [] ++ (true :: toBits m x) ++ s = true :: rest := by
              simp [← hu, hrest]
            rw [hw] at hstep
            exact hnf _ hstep
          · by_cases hx2 : x = 2 ^ m - 1
            · have hu : u = ones m :=
                binVal_injective_of_length_eq (by rw [hulen, ones_length]) (by rw [binVal_ones]; exact hx2)
              have hstep : Step (mersenneSRS m) ([true] ++ ones m ++ s) ([true] ++ zeros m ++ s) :=
                Step.mk [true] s (ones m) (zeros m) (List.Mem.head _)
              have hw : [true] ++ ones m ++ s = true :: rest := by
                simp [← hu, hrest]
              rw [hw] at hstep
              exact hnf _ hstep
            · -- `x = 2^m - 2`: `u = ones (m - 1) ++ [false]`, so `true :: u = ones m ++ [false]`
              have hxEq : x = 2 ^ m - 2 := by omega
              have hval_of : binVal (ones (m - 1) ++ [false]) = 2 ^ m - 2 := by
                rw [binVal_append, binVal_ones]
                have hhalf : 2 ^ (m - 1) * 2 = 2 ^ m := by
                  have : m - 1 + 1 = m := by omega
                  calc 2 ^ (m - 1) * 2 = 2 ^ (m - 1 + 1) := (Nat.pow_succ 2 (m - 1)).symm
                       _ = 2 ^ m := by rw [this]
                have hpos : 1 ≤ 2 ^ (m - 1) := Nat.one_le_pow (m - 1) 2 (by decide)
                simp [binVal, binValAux]
                rw [Nat.mul_sub_right_distrib]; omega
              have hlen_of : (ones (m - 1) ++ [false]).length = m := by
                simp [ones_length]; omega
              have hu : u = ones (m - 1) ++ [false] :=
                binVal_injective_of_length_eq (by omega) (by rw [hval_of]; exact hxEq)
              have honesm : true :: ones (m - 1) = ones m := by
                have : m - 1 + 1 = m := by omega
                rw [← ones_succ, this]
              have hstep : Step (mersenneSRS m) ([] ++ ones m ++ (false :: s))
                  ([] ++ zeros m ++ (false :: s)) :=
                Step.mk [] (false :: s) (ones m) (zeros m) (List.Mem.head _)
              have hw : [] ++ ones m ++ (false :: s) = true :: rest := by
                rw [List.nil_append, ← honesm, hrest, hu]
                simp [List.append_assoc]
              rw [hw] at hstep
              exact hnf _ hstep

/-- Parametric Mersenne Local Normalizer Master Theorem (`∀ m ≥ 2`):
`mersenneSRS m` is terminating, globally confluent, has unique normal forms, and computes
exact arbitrary-width binary equivalence modulo `2^m - 1`. -/
theorem mersenneSRS_master (m : Nat) (hm : 2 ≤ m) :
    Terminating (mersenneSRS m) ∧ Confluent (mersenneSRS m) ∧
    UniqueNormalForms (mersenneSRS m) ∧
    (∀ u v, Convertible (mersenneSRS m) u v ↔
      u.length = v.length ∧ binVal u % (2 ^ m - 1) = binVal v % (2 ^ m - 1)) := by
  have hTerm := mersenneSRS_terminating m hm
  have hInv : ∀ u v, Step (mersenneSRS m) u v →
      (u.length, binVal u % (2 ^ m - 1)) = (v.length, binVal v % (2 ^ m - 1)) := by
    intro u v hs
    have ⟨h1, h2⟩ := step_len_mod_invariant (M := 2 ^ m - 1)
      (fun r hr => let ⟨_, hl, _, hm'⟩ := mersenneSRS_rules_spec m hm r hr; ⟨hl, hm'⟩) hs
    exact Prod.ext h1 h2
  have hNFInj : ∀ n₁ n₂, IsNormalForm (mersenneSRS m) n₁ → IsNormalForm (mersenneSRS m) n₂ →
      (n₁.length, binVal n₁ % (2 ^ m - 1)) = (n₂.length, binVal n₂ % (2 ^ m - 1)) → n₁ = n₂ := by
    intro n₁ n₂ h1 h2 heq
    have hlen : n₁.length = n₂.length := congrArg Prod.fst heq
    have hmod : binVal n₁ % (2 ^ m - 1) = binVal n₂ % (2 ^ m - 1) := congrArg Prod.snd heq
    have hlt1 := mersenneSRS_nf_binVal_lt m hm n₁ h1
    have hlt2 := mersenneSRS_nf_binVal_lt m hm n₂ h2
    rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hmod
    exact binVal_injective_of_length_eq hlen hmod
  obtain ⟨hConf, hUNF, hIff⟩ := confluent_of_term_invariant
    (fun w => (w.length, binVal w % (2 ^ m - 1))) hTerm hInv hNFInj
  refine ⟨hTerm, hConf, hUNF, fun u v => ?_⟩
  rw [hIff u v, Prod.mk.injEq]

/-! ### Family 3: Parametric Irredundant Fermat Mod-`(2^m + 1)` Local Normalizers (`∀ m ≥ 1`) -/

theorem fermatModSRS_rules_spec (m : Nat) (hm : 1 ≤ m) :
    ∀ r ∈ fermatModSRS m,
      r.1 ≠ [] ∧ r.1.length = r.2.length ∧ binVal r.2 < binVal r.1 ∧
      binVal r.1 % (2 ^ m + 1) = binVal r.2 % (2 ^ m + 1) := by
  have h2m : 2 ≤ 2 ^ m := by
    have : 2 ^ 1 ≤ 2 ^ m := pow_le_pow_of_le (by decide) hm
    simpa using this
  intro r hr
  simp only [fermatModSRS, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with ⟨x, hx, rfl⟩ | rfl | rfl
  · have hv1 : binVal (true :: toBits m (x + 1)) = 2 ^ m + (x + 1) := by
      rw [binVal_cons, toBits_length, binVal_toBits m (x + 1) (by omega)]; simp
    have hv2 : binVal (false :: toBits m x) = x := by
      rw [binVal_cons, toBits_length, binVal_toBits m x (by omega)]; simp
    refine ⟨by simp, by simp [toBits_length], by dsimp only; omega, ?_⟩
    dsimp only; rw [hv1, hv2]
    have heq : 2 ^ m + (x + 1) = (2 ^ m + 1) + x := by omega
    rw [heq, Nat.add_mod_left]
  · have hv1 : binVal (true :: zeros m ++ [false]) = 2 * 2 ^ m := by
      have : true :: zeros m ++ [false] = true :: (zeros m ++ [false]) := rfl
      rw [this, binVal_cons, List.length_append, zeros_length, binVal_append, binVal_zeros]
      simp [binVal, binValAux, Nat.pow_succ, Nat.mul_comm]
    have hv2 : binVal ([false, false] ++ ones m) = 2 ^ m - 1 := by
      rw [binVal_append, binVal_ones]; simp [binVal, binValAux]
    refine ⟨by simp, by simp [zeros_length, ones_length], by dsimp only; omega, ?_⟩
    dsimp only; rw [hv1, hv2]
    have heq : 2 * 2 ^ m = (2 ^ m + 1) + (2 ^ m - 1) := by omega
    rw [heq, Nat.add_mod_left]
  · have hv1 : binVal (true :: zeros m ++ [true]) = 2 * 2 ^ m + 1 := by
      have : true :: zeros m ++ [true] = true :: (zeros m ++ [true]) := rfl
      rw [this, binVal_cons, List.length_append, zeros_length, binVal_append, binVal_zeros]
      simp [binVal, binValAux, Nat.pow_succ, Nat.mul_comm]
    have hv2 : binVal ([false, true] ++ zeros m) = 2 ^ m := by
      rw [binVal_append, binVal_zeros, zeros_length]; simp [binVal, binValAux]
    refine ⟨by simp, by simp [zeros_length], by dsimp only; omega, ?_⟩
    dsimp only; rw [hv1, hv2]
    have heq : 2 * 2 ^ m + 1 = (2 ^ m + 1) + 2 ^ m := by omega
    rw [heq, Nat.add_mod_left]

theorem fermatModSRS_terminating (m : Nat) (hm : 1 ≤ m) : Terminating (fermatModSRS m) :=
  binValLayer_terminating (fun r hr =>
    let ⟨h1, h2, h3, _⟩ := fermatModSRS_rules_spec m hm r hr; ⟨h1, h2, h3⟩)

theorem fermatModSRS_nf_binVal_lt (m : Nat) (hm : 1 ≤ m) :
    ∀ w, IsNormalForm (fermatModSRS m) w → binVal w < 2 ^ m + 1 := by
  have h2m : 2 ≤ 2 ^ m := by
    have : 2 ^ 1 ≤ 2 ^ m := pow_le_pow_of_le (by decide) hm
    simpa using this
  intro w
  induction w with
  | nil => intro _; simp [binVal, binValAux]
  | cons b rest ih =>
    intro hnf
    have hnf_rest : IsNormalForm (fermatModSRS m) rest := by
      intro v hs
      have hs' := hs.context [b] []
      simp only [List.singleton_append, List.append_nil] at hs'
      exact hnf _ hs'
    cases b with
    | false =>
      rw [binVal_cons]; simp; exact ih hnf_rest
    | true =>
      by_cases hlt : rest.length < m
      · have hlen : (true :: rest).length ≤ m := by simp; omega
        have hv := binVal_lt_pow (true :: rest)
        have hpow : 2 ^ (true :: rest).length ≤ 2 ^ m := pow_le_pow_of_le (by decide) hlen
        omega
      · by_cases heq : rest.length = m
        · let x := binVal rest
          have hxlt : x < 2 ^ m := by have := binVal_lt_pow rest; rw [heq] at this; exact this
          by_cases hx0 : x = 0
          · rw [binVal_cons, heq]; simp [x] at hx0; simp [hx0]
          · exfalso
            have hrest : rest = toBits m ((x - 1) + 1) := by
              have h1 : (x - 1) + 1 = x := by omega
              rw [h1, ← heq]; exact (toBits_binVal rest).symm
            have hmem : (true :: toBits m ((x - 1) + 1), false :: toBits m (x - 1)) ∈ fermatModSRS m := by
              unfold fermatModSRS
              exact List.mem_append_left _ (List.mem_map.mpr ⟨x - 1, List.mem_range.mpr (by omega), rfl⟩)
            have hstep : Step (fermatModSRS m) ([] ++ (true :: toBits m ((x - 1) + 1)) ++ [])
                ([] ++ (false :: toBits m (x - 1)) ++ []) :=
              Step.mk [] [] _ _ hmem
            simp only [List.nil_append, List.append_nil, ← hrest] at hstep
            exact hnf _ hstep
        · -- `m + 1 ≤ rest.length`: split `rest = u ++ (b2 :: s)` with `u.length = m`
          exfalso
          have hge : m + 1 ≤ rest.length := by omega
          let u := rest.take m
          let tail := rest.drop m
          have hulen : u.length = m := by simp [u]; omega
          have hrest : rest = u ++ tail := (List.take_append_drop m rest).symm
          let x := binVal u
          have hxlt : x < 2 ^ m := by have := binVal_lt_pow u; rw [hulen] at this; exact this
          by_cases hx0 : x = 0
          · have hu : u = zeros m :=
              binVal_injective_of_length_eq (by rw [hulen, zeros_length]) (by rw [binVal_zeros]; exact hx0)
            have htlen : 1 ≤ tail.length := by simp [tail]; omega
            cases htail : tail with
            | nil => simp [htail] at htlen
            | cons b2 s =>
              cases b2 with
              | false =>
                have hmem : (true :: zeros m ++ [false], [false, false] ++ ones m) ∈ fermatModSRS m := by
                  unfold fermatModSRS
                  exact List.mem_append_right _ (List.Mem.head _)
                have hstep : Step (fermatModSRS m) ([] ++ (true :: zeros m ++ [false]) ++ s)
                    ([] ++ ([false, false] ++ ones m) ++ s) :=
                  Step.mk [] s _ _ hmem
                have hw : [] ++ (true :: zeros m ++ [false]) ++ s = true :: rest := by
                  rw [hrest, htail, hu]; simp [List.append_assoc]
                rw [hw] at hstep
                exact hnf _ hstep
              | true =>
                have hmem : (true :: zeros m ++ [true], [false, true] ++ zeros m) ∈ fermatModSRS m := by
                  unfold fermatModSRS
                  exact List.mem_append_right _ (List.Mem.tail _ (List.Mem.head _))
                have hstep : Step (fermatModSRS m) ([] ++ (true :: zeros m ++ [true]) ++ s)
                    ([] ++ ([false, true] ++ zeros m) ++ s) :=
                  Step.mk [] s _ _ hmem
                have hw : [] ++ (true :: zeros m ++ [true]) ++ s = true :: rest := by
                  rw [hrest, htail, hu]; simp [List.append_assoc]
                rw [hw] at hstep
                exact hnf _ hstep
          · have hu : u = toBits m ((x - 1) + 1) := by
              have h1 : (x - 1) + 1 = x := by omega
              rw [h1, ← hulen]; exact (toBits_binVal u).symm
            have hmem : (true :: toBits m ((x - 1) + 1), false :: toBits m (x - 1)) ∈ fermatModSRS m := by
              unfold fermatModSRS
              exact List.mem_append_left _ (List.mem_map.mpr ⟨x - 1, List.mem_range.mpr (by omega), rfl⟩)
            have hstep : Step (fermatModSRS m) ([] ++ (true :: toBits m ((x - 1) + 1)) ++ tail)
                ([] ++ (false :: toBits m (x - 1)) ++ tail) :=
              Step.mk [] tail _ _ hmem
            have hw : [] ++ (true :: toBits m ((x - 1) + 1)) ++ tail = true :: rest := by
              simp [← hu, hrest]
            rw [hw] at hstep
            exact hnf _ hstep

/-- Parametric Fermat Local Normalizer Master Theorem (`∀ m ≥ 1`):
`fermatModSRS m` is terminating, globally confluent, has unique normal forms, and computes
exact arbitrary-width binary equivalence modulo `2^m + 1`. -/
theorem fermatModSRS_master (m : Nat) (hm : 1 ≤ m) :
    Terminating (fermatModSRS m) ∧ Confluent (fermatModSRS m) ∧
    UniqueNormalForms (fermatModSRS m) ∧
    (∀ u v, Convertible (fermatModSRS m) u v ↔
      u.length = v.length ∧ binVal u % (2 ^ m + 1) = binVal v % (2 ^ m + 1)) := by
  have hTerm := fermatModSRS_terminating m hm
  have hInv : ∀ u v, Step (fermatModSRS m) u v →
      (u.length, binVal u % (2 ^ m + 1)) = (v.length, binVal v % (2 ^ m + 1)) := by
    intro u v hs
    have ⟨h1, h2⟩ := step_len_mod_invariant (M := 2 ^ m + 1)
      (fun r hr => let ⟨_, hl, _, hm'⟩ := fermatModSRS_rules_spec m hm r hr; ⟨hl, hm'⟩) hs
    exact Prod.ext h1 h2
  have hNFInj : ∀ n₁ n₂, IsNormalForm (fermatModSRS m) n₁ → IsNormalForm (fermatModSRS m) n₂ →
      (n₁.length, binVal n₁ % (2 ^ m + 1)) = (n₂.length, binVal n₂ % (2 ^ m + 1)) → n₁ = n₂ := by
    intro n₁ n₂ h1 h2 heq
    have hlen : n₁.length = n₂.length := congrArg Prod.fst heq
    have hmod : binVal n₁ % (2 ^ m + 1) = binVal n₂ % (2 ^ m + 1) := congrArg Prod.snd heq
    have hlt1 := fermatModSRS_nf_binVal_lt m hm n₁ h1
    have hlt2 := fermatModSRS_nf_binVal_lt m hm n₂ h2
    rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hmod
    exact binVal_injective_of_length_eq hlen hmod
  obtain ⟨hConf, hUNF, hIff⟩ := confluent_of_term_invariant
    (fun w => (w.length, binVal w % (2 ^ m + 1))) hTerm hInv hNFInj
  refine ⟨hTerm, hConf, hUNF, fun u v => ?_⟩
  rw [hIff u v, Prod.mk.injEq]

/-- System 5: Concrete `decide` Certificate for Fermat Mod-5 (`fermatModSRS 2`, 5 rules, 25 CPs, 65 trace steps). -/
def mod5SRS : SRS := fermatModSRS 2

def mod5Cert : ConfluenceCert := {
  layers := [binValLayer],
  witnesses := [
    ([], []),
    ([], [(3, 0), (1, 2)]),
    ([], [(3, 0), (2, 2)]),
    ([], [(4, 0), (3, 1)]),
    ([], [(3, 0), (2, 2), (0, 3)]),
    ([], [(4, 0), (3, 1), (1, 3)]),
    ([], [(3, 0)]),
    ([], []),
    ([], [(4, 0), (4, 1)]),
    ([(0, 2)], [(0, 0)]),
    ([(4, 1)], [(1, 0)]),
    ([], [(4, 0)]),
    ([(0, 1)], [(1, 0), (0, 2)]),
    ([], []),
    ([(0, 1)], [(0, 0)]),
    ([(0, 1)], [(0, 1), (3, 0), (1, 2)]),
    ([(3, 1), (1, 3)], [(1, 0), (0, 2)]),
    ([(3, 1), (2, 3)], [(0, 1), (3, 0), (1, 2)]),
    ([], []),
    ([(3, 1), (2, 3)], [(3, 0), (1, 2)]),
    ([(4, 1), (3, 2)], [(3, 0), (0, 3), (3, 2)]),
    ([(4, 1), (4, 2)], [(3, 0), (1, 3), (4, 2)]),
    ([(3, 1), (1, 3)], [(3, 0), (0, 3), (3, 2), (2, 4)]),
    ([], []),
    ([(3, 1), (0, 4), (3, 3)], [(3, 0), (1, 3), (4, 2), (3, 3)])
  ]
}

theorem mod5_cert_ok : checkCert mod5SRS mod5Cert = true := by decide

theorem mod5_certified :
    Terminating mod5SRS ∧ Confluent mod5SRS ∧ UniqueNormalForms mod5SRS :=
  cert_sound mod5SRS mod5Cert mod5_cert_ok

/-- System 6: Concrete `decide` Certificate for Mersenne Mod-7 (`mersenneSRS 3`, 7 rules, 49 CPs, 140 trace steps). -/
def mod7SRS : SRS := mersenneSRS 3

def mod7Cert : ConfluenceCert := {
  layers := [binValLayer],
  witnesses := [
    ([], []),
    ([], [(1, 0)]),
    ([], [(1, 1), (1, 0)]),
    ([], [(1, 1), (1, 0), (0, 3)]),
    ([], [(2, 1), (2, 0), (1, 2)]),
    ([], [(2, 1), (2, 0), (2, 2)]),
    ([], [(3, 1), (2, 0), (3, 2)]),
    ([], [(3, 0), (0, 2)]),
    ([], [(3, 1), (0, 3), (1, 0)]),
    ([], [(4, 0), (1, 1)]),
    ([], [(4, 1), (1, 2), (1, 0)]),
    ([], []),
    ([(4, 2)], [(1, 0)]),
    ([(1, 2)], [(1, 0), (2, 3)]),
    ([], []),
    ([(1, 2)], [(1, 0), (3, 3)]),
    ([(2, 2)], [(1, 0), (4, 3)]),
    ([(2, 2)], [(1, 0), (5, 3)]),
    ([(3, 2)], [(1, 0), (6, 3)]),
    ([(3, 2), (0, 4)], [(1, 0), (0, 3)]),
    ([(5, 2)], [(1, 0)]),
    ([(6, 2)], [(1, 0)]),
    ([], []),
    ([(0, 2)], [(1, 0), (0, 3)]),
    ([(0, 2)], [(2, 0), (1, 2)]),
    ([(2, 1)], [(1, 0)]),
    ([(2, 1)], [(1, 2), (1, 0)]),
    ([(1, 1)], [(1, 2), (1, 0), (4, 3)]),
    ([(1, 1)], [(2, 2), (1, 0), (5, 3)]),
    ([(1, 1)], [(2, 2), (1, 0), (6, 3)]),
    ([], []),
    ([(1, 1), (0, 4)], [(3, 0), (0, 2)]),
    ([(1, 1)], [(2, 0), (2, 2)]),
    ([(2, 1), (1, 3)], [(3, 0), (0, 2)]),
    ([(1, 1)], [(2, 0), (3, 2)]),
    ([(2, 1), (2, 3)], [(3, 0), (0, 2)]),
    ([(3, 1)], [(1, 0)]),
    ([(4, 1)], [(2, 0)]),
    ([], []),
    ([(4, 2), (3, 1)], [(1, 1), (1, 0)]),
    ([(1, 2), (1, 1)], [(1, 1), (1, 0), (6, 3)]),
    ([(1, 2), (1, 1), (0, 4)], [(1, 1), (1, 0), (0, 3)]),
    ([(5, 1)], [(2, 0)]),
    ([(2, 2), (2, 1), (1, 3)], [(1, 1), (0, 4), (1, 0), (1, 3)]),
    ([(6, 1)], [(3, 0)]),
    ([(2, 2), (2, 1), (2, 3)], [(2, 1), (1, 3), (1, 0), (2, 3)]),
    ([(3, 2), (2, 1), (3, 3)], [(2, 1), (2, 0), (1, 2)]),
    ([], []),
    ([(3, 2), (0, 4), (1, 1)], [(2, 1), (2, 0), (2, 2)])
  ]
}

theorem mod7_cert_ok : checkCert mod7SRS mod7Cert = true := by decide

theorem mod7_certified :
    Terminating mod7SRS ∧ Confluent mod7SRS ∧ UniqueNormalForms mod7SRS :=
  cert_sound mod7SRS mod7Cert mod7_cert_ok

/-! ## Section 7: Negative / Mutation Tests, Sharp Counterexamples & Non-Vacuity Witnesses -/

/-- Mutation 1: Zero top-left corner `m0[0,0] = 0` breaks left-context monotonicity -> REJECTED. -/
def badCert_zeroTL : ConfluenceCert :=
  { fermat7Cert with layers := [{ dim := 2, m0 := [[0, 1], [0, 1]], m1 := [[3, 1], [0, 1]] }] }

theorem badCert_zeroTL_rejected : checkCert fermat7SRS badCert_zeroTL = false := by decide

/-- Mutation 2: Zero bottom-right corner `m1[1,1] = 0` breaks right-context monotonicity -> REJECTED. -/
def badCert_zeroBR : ConfluenceCert :=
  { fermat7Cert with layers := [{ dim := 2, m0 := [[1, 1], [0, 1]], m1 := [[3, 1], [0, 0]] }] }

theorem badCert_zeroBR_rejected : checkCert fermat7SRS badCert_zeroBR = false := by decide

/-- Mutation 3: Violated strict top-right decrease (`A = 2` on `10 → 001`) -> REJECTED. -/
def badCert_nonStrict : ConfluenceCert :=
  { fermat7Cert with layers := [{ dim := 2, m0 := [[1, 1], [0, 1]], m1 := [[2, 1], [0, 1]] }] }

theorem badCert_nonStrict_rejected : checkCert fermat7SRS badCert_nonStrict = false := by decide

/-- Mutation 4: Weak-only identity matrix layer -> REJECTED. -/
def badCert_weakOnly : ConfluenceCert :=
  { fermat7Cert with layers := [{ dim := 2, m0 := [[1, 0], [0, 1]], m1 := [[1, 0], [0, 1]] }] }

theorem badCert_weakOnly_rejected : checkCert fermat7SRS badCert_weakOnly = false := by decide

/-- Mutation 5: Corrupted joinability trace position `(0, 99)` -> REJECTED. -/
def badCert_corruptTrace : ConfluenceCert :=
  { fermat7Cert with witnesses := ([(0, 99)], []) :: fermat7Cert.witnesses.tail }

theorem badCert_corruptTrace_rejected : checkCert fermat7SRS badCert_corruptTrace = false := by decide

/-- Mutation 6: Missing critical-pair witness -> REJECTED. -/
def badCert_missingWitness : ConfluenceCert :=
  { fermat7Cert with witnesses := fermat7Cert.witnesses.dropLast }

theorem badCert_missingWitness_rejected : checkCert fermat7SRS badCert_missingWitness = false := by decide

/-- Mutation 7: Empty matrix layer list -> REJECTED. -/
def badCert_emptyLayers : ConfluenceCert :=
  { fermat7Cert with layers := [] }

theorem badCert_emptyLayers_rejected : checkCert fermat7SRS badCert_emptyLayers = false := by decide

/-- Mutation 8: Ragged matrix (row length ≠ dim) -> REJECTED. -/
def badCert_raggedMat : ConfluenceCert :=
  { fermat7Cert with layers := [{ dim := 2, m0 := [[1, 1], [0]], m1 := [[3, 1], [0, 1]] }] }

theorem badCert_raggedMat_rejected : checkCert fermat7SRS badCert_raggedMat = false := by decide

/-- Mutation 9: Dropping Layer 0 from `mod3Cert` leaves only Layer 1 (3×3 inversion matrix),
which fails componentwise monotonicity on `101 → 010` -> REJECTED. -/
def badCert_mod3SingleLayer : ConfluenceCert :=
  { mod3Cert with layers := mod3Cert.layers.tail }

theorem badCert_mod3SingleLayer_rejected : checkCert mod3SRS badCert_mod3SingleLayer = false := by decide

/-- Mutation 10: Valid replay traces that end at distinct words (`z₁ ≠ z₂`) -> REJECTED. -/
def badCert_mismatchJoin : ConfluenceCert :=
  { fermat7Cert with witnesses := List.replicate (criticalPairs fermat7SRS).length ([], []) }

theorem badCert_mismatchJoin_rejected : checkCert fermat7SRS badCert_mismatchJoin = false := by decide

/-- Sharpness Counterexample 1: `S(2, 4, 1, 1, 5)` (`5 ∤ 2^4 - 2^1 = 14`) is provably NOT confluent! -/
theorem fermat5_not_confluent : ¬ Confluent (ampSys 2 4 1 1 5) := by
  rw [ampSys_confluent_iff 2 4 1 1 5 (by decide) (by decide) (by decide) (by decide)]
  intro ⟨_, hdvd⟩
  rcases hdvd with ⟨q, hq⟩
  omega

/-- Sharpness Counterexample 2: `S(2, 4, 1, 3, 7)` (`k = 3 > 2^1 = 2`, even though `7 ∣ 14`) is NOT confluent! -/
theorem threshold_violation_not_confluent : ¬ Confluent (ampSys 2 4 1 3 7) := by
  rw [ampSys_confluent_iff 2 4 1 3 7 (by decide) (by decide) (by decide) (by decide)]
  intro ⟨hks, _⟩
  omega

/-- Sharpness Counterexample 3: Symmetric swap `{10 → 01, 01 → 10}` is provably NOT terminating. -/
def swapLoopSRS : SRS := [([true, false], [false, true]), ([false, true], [true, false])]

theorem swapLoop_not_terminating : ¬ Terminating swapLoopSRS := by
  intro hTerm
  have h1 : Step swapLoopSRS [true, false] [false, true] := by
    simpa using Step.mk [] [] [true, false] [false, true] (by simp [swapLoopSRS])
  have h2 : Step swapLoopSRS [false, true] [true, false] := by
    simpa using Step.mk [] [] [false, true] [true, false] (by simp [swapLoopSRS])
  have hNoCycle : ∀ w, Acc (fun v u => Step swapLoopSRS u v) w →
      w ≠ [true, false] ∧ w ≠ [false, true] := by
    intro w hAcc
    induction hAcc with
    | intro x _ ih =>
      constructor
      · intro hx; subst hx; exact (ih [false, true] h1).2 rfl
      · intro hx; subst hx; exact (ih [true, false] h2).1 rfl
  exact (hNoCycle [true, false] (hTerm.apply [true, false])).1 rfl

/-- Sharpness Counterexample 4 (3-Rule Minimality of `mod3SRS`, drop rule 0 `101 → 010`):
`mod3_drop0 = {11 → 00, 100 → 001}` remains confluent (certified by `decide`), YET loses
mod-3 semantic completeness: `101` (5 ≡ 2 mod 3) and `010` (2 ≡ 2 mod 3) are NOT convertible! -/
def mod3_drop0 : SRS := [([true, true], [false, false]), ([true, false, false], [false, false, true])]

def mod3_drop0Cert : ConfluenceCert := {
  layers := [binValLayer],
  witnesses := [([], []), ([], [(1, 0)]), ([], [(1, 0), (0, 2)]), ([], [])]
}

theorem mod3_drop0_cert_ok : checkCert mod3_drop0 mod3_drop0Cert = true := by decide

theorem mod3_drop0_incomplete :
    ¬ Convertible mod3_drop0 [true, false, true] [false, true, false] := by
  intro hConv
  have hConf := (cert_sound mod3_drop0 mod3_drop0Cert mod3_drop0_cert_ok).2.1
  have hnf1 : IsNormalForm mod3_drop0 [true, false, true] := findStep_none_nf (by decide)
  have hnf2 : IsNormalForm mod3_drop0 [false, true, false] := findStep_none_nf (by decide)
  have heq := joinable_of_convertible_nf hConf hConv hnf1 hnf2
  cases heq

/-- Sharpness Counterexample 5 (3-Rule Minimality of `mod3SRS`, drop rule 1 `11 → 00`):
Witness `10101` reduces to distinct normal forms `00011 ≠ 00110`. -/
def mod3_drop1 : SRS := [([true, false, true], [false, true, false]), ([true, false, false], [false, false, true])]

theorem mod3_drop1_not_confluent : ¬ Confluent mod3_drop1 := by
  intro hConf
  have h1 : Steps mod3_drop1 [true, false, true, false, true] [false, false, false, true, true] :=
    replayTrace_sound (tr := [(0, 0), (1, 1)]) (by decide)
  have h2 : Steps mod3_drop1 [true, false, true, false, true] [false, false, true, true, false] :=
    replayTrace_sound (tr := [(0, 2), (1, 0)]) (by decide)
  have hnf1 : IsNormalForm mod3_drop1 [false, false, false, true, true] := findStep_none_nf (by decide)
  have hnf2 : IsNormalForm mod3_drop1 [false, false, true, true, false] := findStep_none_nf (by decide)
  obtain ⟨z, hz1, hz2⟩ := hConf _ _ _ h1 h2
  have heq : [false, false, false, true, true] = [false, false, true, true, false] :=
    (hz1.nf_eq hnf1).trans (hz2.nf_eq hnf2).symm
  cases heq

/-- Sharpness Counterexample 6 (3-Rule Minimality of `mod3SRS`, drop rule 2 `100 → 001`):
Witness `10101` reduces to distinct normal forms `01001 ≠ 10010`. -/
def mod3_drop2 : SRS := [([true, false, true], [false, true, false]), ([true, true], [false, false])]

theorem mod3_drop2_not_confluent : ¬ Confluent mod3_drop2 := by
  intro hConf
  have h1 : Steps mod3_drop2 [true, false, true, false, true] [false, true, false, false, true] :=
    replayTrace_sound (tr := [(0, 0)]) (by decide)
  have h2 : Steps mod3_drop2 [true, false, true, false, true] [true, false, false, true, false] :=
    replayTrace_sound (tr := [(0, 2)]) (by decide)
  have hnf1 : IsNormalForm mod3_drop2 [false, true, false, false, true] := findStep_none_nf (by decide)
  have hnf2 : IsNormalForm mod3_drop2 [true, false, false, true, false] := findStep_none_nf (by decide)
  obtain ⟨z, hz1, hz2⟩ := hConf _ _ _ h1 h2
  have heq : [false, true, false, false, true] = [true, false, false, true, false] :=
    (hz1.nf_eq hnf1).trans (hz2.nf_eq hnf2).symm
  cases heq

/-! ### Non-Vacuity Witnesses (Concrete Instantiations of Engine & Family Theorems) -/

/-- Non-vacuity witness 1: `11011` (27 ≡ 0 mod 3) and `00110` (6 ≡ 0 mod 3) are provably convertible in `mod3SRS`. -/
example : Convertible mod3SRS [true, true, false, true, true] [false, false, true, true, false] :=
  (mod3_convertible_iff _ _).mpr (by decide)

/-- Non-vacuity witness 2: `11011` (27 ≡ 0 mod 3) and `11010` (26 ≡ 2 mod 3) are provably NOT convertible in `mod3SRS`. -/
example : ¬ Convertible mod3SRS [true, true, false, true, true] [true, true, false, true, false] := by
  rw [mod3_convertible_iff]; decide

/-- Non-vacuity witness 3: Infinite family instantiation `S(3, 3, 0, 1, 13)` (`13 ∣ 3^3 - 1 = 26`). -/
example : UniqueNormalForms (ampSys 3 3 0 1 13) :=
  ampSys_uniqueNormalForms 3 3 0 1 13 (by decide) (by decide) (by decide) (by decide)
    (by decide) ⟨2, by decide⟩

/-- Non-vacuity witness 4: Parametric Mersenne Mod-15 (`mersenneSRS 4`): `101101` (45 ≡ 0 mod 15) ↔ `001111` (15 ≡ 0 mod 15). -/
example : Convertible (mersenneSRS 4) [true, false, true, true, false, true] [false, false, true, true, true, true] :=
  ((mersenneSRS_master 4 (by decide)).2.2.2 _ _).mpr (by decide)

/-- Non-vacuity witness 5: Parametric Fermat Mod-9 (`fermatModSRS 3`): `11011` (27 ≡ 0 mod 9) ↔ `01001` (9 ≡ 0 mod 9). -/
example : Convertible (fermatModSRS 3) [true, true, false, true, true] [false, true, false, false, true] :=
  ((fermatModSRS_master 3 (by decide)).2.2.2 _ _).mpr (by decide)

end CertComp16
