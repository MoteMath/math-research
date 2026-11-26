/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LoftqCyclesRank1.Defs
import LoftqCyclesRank1.Rank1Ternary2x2

/-!
# Theorem 3: Coupled Orthogonal / Integer Matrices Strictly Beating `I_k ⊗ R(π/8)`

Proves `coupled_orthogonal_beats_block_2x2_rotations` for `n = 3` and `n = 4`:
1. `n = 3`: `W_3x3_coupled` achieves exact rank-1 ternary contraction ratio `≤ 2162403 / 7239976`,
   strictly beating the uncoupled `3 × 3` block-diagonal `R(π/8)` upper bound `(9 + 4√2) / 49`.
2. `n = 4`: `W_4x4_coupled` is **exact orthogonal** (`W^T W = 16680999 · I_4`) and achieves
   exact rank-1 ternary contraction ratio `≤ 28440889 / 133447992`, strictly beating the
   uncoupled `4 × 4` block-diagonal `I_2 ⊗ R(π/8)` upper bound `(2 + √2) / 16`.
-/

namespace LoftqCyclesRank1

/-! ### Exact `QSqrt2` Strict Comparison Against Block-Diagonal `R(π/8)` Bounds -/

theorem coupled3_beats_blockUB3 :
    QSqrt2.ofRat (2162403 / 7239976) < QSqrt2.blockUB3 := by
  constructor
  · show QSqrt2.nonneg (QSqrt2.blockUB3 - QSqrt2.ofRat (2162403 / 7239976))
    have hrew : QSqrt2.blockUB3 - QSqrt2.ofRat (2162403 / 7239976) =
        ⟨(9 : Rat) / 49 - 2162403 / 7239976, 4 / 49⟩ := by
      simp only [QSqrt2.blockUB3, QSqrt2.ofRat, q2_sub_mk]
      congr 1 <;> grind
    rw [hrew]
    right; right
    refine ⟨by grind, by grind, ?_⟩
    grind
  · intro heq
    have hb : (QSqrt2.ofRat (2162403 / 7239976)).b = QSqrt2.blockUB3.b :=
      congrArg QSqrt2.b heq
    simp only [QSqrt2.ofRat, QSqrt2.blockUB3] at hb
    grind

theorem coupled4_beats_blockUB4 :
    QSqrt2.ofRat (28440889 / 133447992) < QSqrt2.blockUB4 := by
  constructor
  · show QSqrt2.nonneg (QSqrt2.blockUB4 - QSqrt2.ofRat (28440889 / 133447992))
    have hrew : QSqrt2.blockUB4 - QSqrt2.ofRat (28440889 / 133447992) =
        ⟨(1 : Rat) / 8 - 28440889 / 133447992, 1 / 16⟩ := by
      simp only [QSqrt2.blockUB4, QSqrt2.ofRat, q2_sub_mk]
      congr 1 <;> grind
    rw [hrew]
    right; right
    refine ⟨by grind, by grind, ?_⟩
    grind
  · intro heq
    have hb : (QSqrt2.ofRat (28440889 / 133447992)).b = QSqrt2.blockUB4.b :=
      congrArg QSqrt2.b heq
    simp only [QSqrt2.ofRat, QSqrt2.blockUB4] at hb
    grind

/-! ### Exact Orthogonality of `W_4x4_coupled` (`W^T W = 16680999 · I_4`) -/

theorem W_4x4_coupled_orthogonal : isOrthogonalInt W_4x4_coupled 16680999 := by
  intro i j
  match i, j with
  | ⟨0, _⟩, ⟨0, _⟩ => rfl | ⟨0, _⟩, ⟨1, _⟩ => rfl | ⟨0, _⟩, ⟨2, _⟩ => rfl | ⟨0, _⟩, ⟨3, _⟩ => rfl
  | ⟨1, _⟩, ⟨0, _⟩ => rfl | ⟨1, _⟩, ⟨1, _⟩ => rfl | ⟨1, _⟩, ⟨2, _⟩ => rfl | ⟨1, _⟩, ⟨3, _⟩ => rfl
  | ⟨2, _⟩, ⟨0, _⟩ => rfl | ⟨2, _⟩, ⟨1, _⟩ => rfl | ⟨2, _⟩, ⟨2, _⟩ => rfl | ⟨2, _⟩, ⟨3, _⟩ => rfl
  | ⟨3, _⟩, ⟨0, _⟩ => rfl | ⟨3, _⟩, ⟨1, _⟩ => rfl | ⟨3, _⟩, ⟨2, _⟩ => rfl | ⟨3, _⟩, ⟨3, _⟩ => rfl

/-! ### Fast Pure-`Int` Kernel Verification for `W_3x3_coupled` (13 × 13 Canonical Pairs) -/

/-- The 13 canonical nonzero ternary vectors in `{-1, 0, 1}^3 \ {0}` (first nonzero entry is `+1`). -/
def canonTern3 : List (Int × Int × Int) :=
  [ (1, -1, -1), (1, -1, 0), (1, -1, 1),
    (1,  0, -1), (1,  0, 0), (1,  0, 1),
    (1,  1, -1), (1,  1, 0), (1,  1, 1),
    (0,  1, -1), (0,  1, 0), (0,  1, 1),
    (0,  0,  1) ]

def quad3 (u v : Int × Int × Int) : Int :=
  let (u0, u1, u2) := u
  let (v0, v1, v2) := v
  let y0 := u0 * (-3602) + u1 * 1492 + u2 * (-127)
  let y1 := u0 * 127     + u1 * (-127) + u2 * (-3602)
  let y2 := u0 * (-1492) + u1 * (-3602) + u2 * 127
  y0 * v0 + y1 * v1 + y2 * v2

def norm3 (u : Int × Int × Int) : Int :=
  let (u0, u1, u2) := u
  u0 * u0 + u1 * u1 + u2 * u2

theorem W_3x3_frobSq : frobSqInt W_3x3_coupled = 43439856 := by decide

theorem check_W_3x3_canon :
    canonTern3.all (fun u =>
      canonTern3.all (fun v =>
        let q := quad3 u v
        decide (q * q * 7239976 ≤ 2162403 * (norm3 u * norm3 v * 43439856)))) = true := by
  decide

theorem canon3_cover (a b c : Int)
    (ha : a = -1 ∨ a = 0 ∨ a = 1)
    (hb : b = -1 ∨ b = 0 ∨ b = 1)
    (hc : c = -1 ∨ c = 0 ∨ c = 1)
    (hne : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    (a, b, c) ∈ canonTern3 ∨ (-a, -b, -c) ∈ canonTern3 := by
  rcases ha with rfl | rfl | rfl <;>
  rcases hb with rfl | rfl | rfl <;>
  rcases hc with rfl | rfl | rfl
  all_goals first | decide | (exfalso; omega)

theorem quadFormInt_3x3_eq (u v : Fin 3 → Int) :
    quadFormInt W_3x3_coupled u v = quad3 (u 0, u 1, u 2) (v 0, v 1, v 2) := by
  simp only [quadFormInt, sumFinInt, W_3x3_coupled, quad3, Fin.val_castSucc, Fin.val_last]
  have h0 : (Fin.castSucc (Fin.castSucc (Fin.last 0)) : Fin 3) = 0 := rfl
  have h1 : (Fin.castSucc (Fin.last 1) : Fin 3) = 1 := rfl
  have h2 : (Fin.last 2 : Fin 3) = 2 := rfl
  rw [h0, h1, h2]
  grind

theorem vecSqNormInt_3_eq (u : Fin 3 → Int) :
    vecSqNormInt u = norm3 (u 0, u 1, u 2) := by
  simp only [vecSqNormInt, sumFinInt, norm3]
  have h0 : (Fin.castSucc (Fin.castSucc (Fin.last 0)) : Fin 3) = 0 := rfl
  have h1 : (Fin.castSucc (Fin.last 1) : Fin 3) = 1 := rfl
  have h2 : (Fin.last 2 : Fin 3) = 2 := rfl
  rw [h0, h1, h2]
  omega

theorem W_3x3_coupled_bound (u v : Fin 3 → Int) (hu : isTernVec u) (hv : isTernVec v) :
    quadFormInt W_3x3_coupled u v * quadFormInt W_3x3_coupled u v * 7239976 ≤
      2162403 * (vecSqNormInt u * vecSqNormInt v * frobSqInt W_3x3_coupled) := by
  rw [quadFormInt_3x3_eq, vecSqNormInt_3_eq u, vecSqNormInt_3_eq v, W_3x3_frobSq]
  have hu_ne : u 0 ≠ 0 ∨ u 1 ≠ 0 ∨ u 2 ≠ 0 := by
    obtain ⟨i, hi⟩ := hu.2
    match i with
    | ⟨0, _⟩ => left; exact hi
    | ⟨1, _⟩ => right; left; exact hi
    | ⟨2, _⟩ => right; right; exact hi
  have hv_ne : v 0 ≠ 0 ∨ v 1 ≠ 0 ∨ v 2 ≠ 0 := by
    obtain ⟨i, hi⟩ := hv.2
    match i with
    | ⟨0, _⟩ => left; exact hi
    | ⟨1, _⟩ => right; left; exact hi
    | ⟨2, _⟩ => right; right; exact hi
  have hcheck : ∀ p ∈ canonTern3, ∀ q ∈ canonTern3,
      quad3 p q * quad3 p q * 7239976 ≤ 2162403 * (norm3 p * norm3 q * 43439856) := by
    intro p hp q hq
    have h1 := List.all_eq_true.mp check_W_3x3_canon p hp
    have h2 := List.all_eq_true.mp h1 q hq
    exact of_decide_eq_true h2
  have hneg_u : ∀ a b c q, quad3 (-a, -b, -c) q = -quad3 (a, b, c) q := by
    intro a b c ⟨q0, q1, q2⟩; simp only [quad3]; grind
  have hneg_v : ∀ p a b c, quad3 p (-a, -b, -c) = -quad3 p (a, b, c) := by
    intro ⟨p0, p1, p2⟩ a b c; simp only [quad3]; grind
  have hnorm_neg : ∀ a b c, norm3 (-a, -b, -c) = norm3 (a, b, c) := by
    intro a b c; simp only [norm3]; grind
  rcases canon3_cover (u 0) (u 1) (u 2) (hu.1 0) (hu.1 1) (hu.1 2) hu_ne with hu_in | hu_in <;>
  rcases canon3_cover (v 0) (v 1) (v 2) (hv.1 0) (hv.1 1) (hv.1 2) hv_ne with hv_in | hv_in
  · exact hcheck _ hu_in _ hv_in
  · have h := hcheck _ hu_in _ hv_in
    rw [hneg_v, hnorm_neg] at h
    have hsq : (-quad3 (u 0, u 1, u 2) (v 0, v 1, v 2)) * (-quad3 (u 0, u 1, u 2) (v 0, v 1, v 2)) =
        quad3 (u 0, u 1, u 2) (v 0, v 1, v 2) * quad3 (u 0, u 1, u 2) (v 0, v 1, v 2) := by grind
    rw [hsq] at h; exact h
  · have h := hcheck _ hu_in _ hv_in
    rw [hneg_u, hnorm_neg] at h
    have hsq : (-quad3 (u 0, u 1, u 2) (v 0, v 1, v 2)) * (-quad3 (u 0, u 1, u 2) (v 0, v 1, v 2)) =
        quad3 (u 0, u 1, u 2) (v 0, v 1, v 2) * quad3 (u 0, u 1, u 2) (v 0, v 1, v 2) := by grind
    rw [hsq] at h; exact h
  · have h := hcheck _ hu_in _ hv_in
    rw [hneg_u, hneg_v, hnorm_neg, hnorm_neg] at h
    have hsq : (- -quad3 (u 0, u 1, u 2) (v 0, v 1, v 2)) * (- -quad3 (u 0, u 1, u 2) (v 0, v 1, v 2)) =
        quad3 (u 0, u 1, u 2) (v 0, v 1, v 2) * quad3 (u 0, u 1, u 2) (v 0, v 1, v 2) := by grind
    rw [hsq] at h; exact h

/-! ### Fast Pure-`Int` Kernel Verification for `W_4x4_coupled` (40 × 40 Canonical Pairs) -/

/-- The 40 canonical nonzero ternary vectors in `{-1, 0, 1}^4 \ {0}` (first nonzero entry is `+1`). -/
def canonTern4 : List (Int × Int × Int × Int) :=
  let t : List Int := [-1, 0, 1]
  (t.flatMap fun b => t.flatMap fun c => t.map fun d => (1, b, c, d)) ++
  (t.flatMap fun c => t.map fun d => (0, 1, c, d)) ++
  (t.map fun d => (0, 0, 1, d)) ++
  [(0, 0, 0, 1)]

def quad4 (u v : Int × Int × Int × Int) : Int :=
  let (u0, u1, u2, u3) := u
  let (v0, v1, v2, v3) := v
  let y0 := u0 * (-1562) + u1 * (-55)   + u2 * 3771    + u3 * 133
  let y1 := u0 * 3771    + u1 * 133     + u2 * 1562    + u3 * 55
  let y2 := u0 * 55      + u1 * (-1562) + u2 * 133     + u3 * (-3771)
  let y3 := u0 * 133     + u1 * (-3771) + u2 * (-55)   + u3 * 1562
  y0 * v0 + y1 * v1 + y2 * v2 + y3 * v3

def norm4 (u : Int × Int × Int × Int) : Int :=
  let (u0, u1, u2, u3) := u
  u0 * u0 + u1 * u1 + u2 * u2 + u3 * u3

theorem W_4x4_frobSq : frobSqInt W_4x4_coupled = 66723996 := by decide

theorem check_W_4x4_canon :
    canonTern4.all (fun u =>
      canonTern4.all (fun v =>
        let q := quad4 u v
        decide (q * q * 133447992 ≤ 28440889 * (norm4 u * norm4 v * 66723996)))) = true := by
  decide

theorem canon4_cover (a b c d : Int)
    (ha : a = -1 ∨ a = 0 ∨ a = 1)
    (hb : b = -1 ∨ b = 0 ∨ b = 1)
    (hc : c = -1 ∨ c = 0 ∨ c = 1)
    (hd : d = -1 ∨ d = 0 ∨ d = 1)
    (hne : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0) :
    (a, b, c, d) ∈ canonTern4 ∨ (-a, -b, -c, -d) ∈ canonTern4 := by
  rcases ha with rfl | rfl | rfl <;>
  rcases hb with rfl | rfl | rfl <;>
  rcases hc with rfl | rfl | rfl <;>
  rcases hd with rfl | rfl | rfl
  all_goals first | decide | (exfalso; omega)

theorem quadFormInt_4x4_eq (u v : Fin 4 → Int) :
    quadFormInt W_4x4_coupled u v = quad4 (u 0, u 1, u 2, u 3) (v 0, v 1, v 2, v 3) := by
  simp only [quadFormInt, sumFinInt, W_4x4_coupled, quad4, Fin.val_castSucc, Fin.val_last]
  have h0 : (Fin.castSucc (Fin.castSucc (Fin.castSucc (Fin.last 0))) : Fin 4) = 0 := rfl
  have h1 : (Fin.castSucc (Fin.castSucc (Fin.last 1)) : Fin 4) = 1 := rfl
  have h2 : (Fin.castSucc (Fin.last 2) : Fin 4) = 2 := rfl
  have h3 : (Fin.last 3 : Fin 4) = 3 := rfl
  rw [h0, h1, h2, h3]
  grind

theorem vecSqNormInt_4_eq (u : Fin 4 → Int) :
    vecSqNormInt u = norm4 (u 0, u 1, u 2, u 3) := by
  simp only [vecSqNormInt, sumFinInt, norm4]
  have h0 : (Fin.castSucc (Fin.castSucc (Fin.castSucc (Fin.last 0))) : Fin 4) = 0 := rfl
  have h1 : (Fin.castSucc (Fin.castSucc (Fin.last 1)) : Fin 4) = 1 := rfl
  have h2 : (Fin.castSucc (Fin.last 2) : Fin 4) = 2 := rfl
  have h3 : (Fin.last 3 : Fin 4) = 3 := rfl
  rw [h0, h1, h2, h3]
  omega

theorem W_4x4_coupled_bound (u v : Fin 4 → Int) (hu : isTernVec u) (hv : isTernVec v) :
    quadFormInt W_4x4_coupled u v * quadFormInt W_4x4_coupled u v * 133447992 ≤
      28440889 * (vecSqNormInt u * vecSqNormInt v * frobSqInt W_4x4_coupled) := by
  rw [quadFormInt_4x4_eq, vecSqNormInt_4_eq u, vecSqNormInt_4_eq v, W_4x4_frobSq]
  have hu_ne : u 0 ≠ 0 ∨ u 1 ≠ 0 ∨ u 2 ≠ 0 ∨ u 3 ≠ 0 := by
    obtain ⟨i, hi⟩ := hu.2
    match i with
    | ⟨0, _⟩ => left; exact hi
    | ⟨1, _⟩ => right; left; exact hi
    | ⟨2, _⟩ => right; right; left; exact hi
    | ⟨3, _⟩ => right; right; right; exact hi
  have hv_ne : v 0 ≠ 0 ∨ v 1 ≠ 0 ∨ v 2 ≠ 0 ∨ v 3 ≠ 0 := by
    obtain ⟨i, hi⟩ := hv.2
    match i with
    | ⟨0, _⟩ => left; exact hi
    | ⟨1, _⟩ => right; left; exact hi
    | ⟨2, _⟩ => right; right; left; exact hi
    | ⟨3, _⟩ => right; right; right; exact hi
  have hcheck : ∀ p ∈ canonTern4, ∀ q ∈ canonTern4,
      quad4 p q * quad4 p q * 133447992 ≤ 28440889 * (norm4 p * norm4 q * 66723996) := by
    intro p hp q hq
    have h1 := List.all_eq_true.mp check_W_4x4_canon p hp
    have h2 := List.all_eq_true.mp h1 q hq
    exact of_decide_eq_true h2
  have hneg_u : ∀ a b c d q, quad4 (-a, -b, -c, -d) q = -quad4 (a, b, c, d) q := by
    intro a b c d ⟨q0, q1, q2, q3⟩; simp only [quad4]; grind
  have hneg_v : ∀ p a b c d, quad4 p (-a, -b, -c, -d) = -quad4 p (a, b, c, d) := by
    intro ⟨p0, p1, p2, p3⟩ a b c d; simp only [quad4]; grind
  have hnorm_neg : ∀ a b c d, norm4 (-a, -b, -c, -d) = norm4 (a, b, c, d) := by
    intro a b c d; simp only [norm4]; grind
  rcases canon4_cover (u 0) (u 1) (u 2) (u 3) (hu.1 0) (hu.1 1) (hu.1 2) (hu.1 3) hu_ne with hu_in | hu_in <;>
  rcases canon4_cover (v 0) (v 1) (v 2) (v 3) (hv.1 0) (hv.1 1) (hv.1 2) (hv.1 3) hv_ne with hv_in | hv_in
  · exact hcheck _ hu_in _ hv_in
  · have h := hcheck _ hu_in _ hv_in
    rw [hneg_v, hnorm_neg] at h
    have hsq : (-quad4 (u 0, u 1, u 2, u 3) (v 0, v 1, v 2, v 3)) * (-quad4 (u 0, u 1, u 2, u 3) (v 0, v 1, v 2, v 3)) =
        quad4 (u 0, u 1, u 2, u 3) (v 0, v 1, v 2, v 3) * quad4 (u 0, u 1, u 2, u 3) (v 0, v 1, v 2, v 3) := by grind
    rw [hsq] at h; exact h
  · have h := hcheck _ hu_in _ hv_in
    rw [hneg_u, hnorm_neg] at h
    have hsq : (-quad4 (u 0, u 1, u 2, u 3) (v 0, v 1, v 2, v 3)) * (-quad4 (u 0, u 1, u 2, u 3) (v 0, v 1, v 2, v 3)) =
        quad4 (u 0, u 1, u 2, u 3) (v 0, v 1, v 2, v 3) * quad4 (u 0, u 1, u 2, u 3) (v 0, v 1, v 2, v 3) := by grind
    rw [hsq] at h; exact h
  · have h := hcheck _ hu_in _ hv_in
    rw [hneg_u, hneg_v, hnorm_neg, hnorm_neg] at h
    have hsq : (- -quad4 (u 0, u 1, u 2, u 3) (v 0, v 1, v 2, v 3)) * (- -quad4 (u 0, u 1, u 2, u 3) (v 0, v 1, v 2, v 3)) =
        quad4 (u 0, u 1, u 2, u 3) (v 0, v 1, v 2, v 3) * quad4 (u 0, u 1, u 2, u 3) (v 0, v 1, v 2, v 3) := by grind
    rw [hsq] at h; exact h

/-! ### Main Theorem 3 -/

theorem coupled_orthogonal_beats_block_2x2_rotations :
    (∀ u v : Fin 3 → Int, isTernVec u → isTernVec v →
      quadFormInt W_3x3_coupled u v * quadFormInt W_3x3_coupled u v * 7239976 ≤
        2162403 * (vecSqNormInt u * vecSqNormInt v * frobSqInt W_3x3_coupled)) ∧
    QSqrt2.ofRat (2162403 / 7239976) < QSqrt2.blockUB3 ∧
    isOrthogonalInt W_4x4_coupled 16680999 ∧
    (∀ u v : Fin 4 → Int, isTernVec u → isTernVec v →
      quadFormInt W_4x4_coupled u v * quadFormInt W_4x4_coupled u v * 133447992 ≤
        28440889 * (vecSqNormInt u * vecSqNormInt v * frobSqInt W_4x4_coupled)) ∧
    QSqrt2.ofRat (28440889 / 133447992) < QSqrt2.blockUB4 :=
  ⟨W_3x3_coupled_bound, coupled3_beats_blockUB3,
   W_4x4_coupled_orthogonal, W_4x4_coupled_bound, coupled4_beats_blockUB4⟩

end LoftqCyclesRank1
