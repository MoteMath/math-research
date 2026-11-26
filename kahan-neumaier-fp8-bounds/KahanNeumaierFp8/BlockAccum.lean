/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KahanNeumaierFp8.KulischInt32

/-!
# Unconditional Associativity & Permutation Invariance of Shared-Exponent INT32/INT64 Block Accumulation

Proves Theorem 6 (`shared_exponent_int32_block_accum_associativity`).
-/

namespace KahanNeumaierFp8

theorem blockAdd_assoc {d : Nat} (a b c : Fin d → Int) :
    blockAdd (blockAdd a b) c = blockAdd a (blockAdd b c) := by
  funext j; unfold blockAdd; omega

theorem blockAdd_comm {d : Nat} (a b : Fin d → Int) :
    blockAdd a b = blockAdd b a := by
  funext j; unfold blockAdd; omega

theorem blockAdd_zero_left {d : Nat} (a : Fin d → Int) :
    blockAdd (blockZero d) a = a := by
  funext j; unfold blockAdd blockZero; omega

theorem blockAdd_zero_right {d : Nat} (a : Fin d → Int) :
    blockAdd a (blockZero d) = a := by
  funext j; unfold blockAdd blockZero; omega

theorem blockAccum_cons {d : Nat} (g : Fin d → Int) (gs : List (Fin d → Int)) :
    blockAccum (g :: gs) = blockAdd g (blockAccum gs) := by
  unfold blockAccum
  have hgen : ∀ (acc : Fin d → Int) (ys : List (Fin d → Int)),
      ys.foldl blockAdd acc = blockAdd acc (ys.foldl blockAdd (blockZero d)) := by
    intro acc ys
    induction ys generalizing acc with
    | nil => simp [blockAdd_zero_right]
    | cons y ys ih =>
      simp only [List.foldl_cons, blockAdd_zero_left]
      rw [ih (blockAdd acc y), ih y, blockAdd_assoc]
  simpa [blockAdd_zero_left] using hgen g gs

theorem blockAccum_append {d : Nat} (gs hs : List (Fin d → Int)) :
    blockAccum (gs ++ hs) = blockAdd (blockAccum gs) (blockAccum hs) := by
  induction gs with
  | nil => simp [blockAccum, blockAdd_zero_left]
  | cons g gs ih =>
    rw [List.cons_append, blockAccum_cons, blockAccum_cons, ih, blockAdd_assoc]

theorem blockAccum_perm {d : Nat} {gs hs : List (Fin d → Int)} (h : List.Perm gs hs) :
    blockAccum gs = blockAccum hs := by
  induction h with
  | nil => rfl
  | cons g _ ih => rw [blockAccum_cons, blockAccum_cons, ih]
  | swap g1 g2 l =>
    rw [blockAccum_cons, blockAccum_cons, blockAccum_cons, blockAccum_cons,
        ← blockAdd_assoc, blockAdd_comm g2 g1, blockAdd_assoc]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ### `Int32` Register Block Accumulation -/

theorem blockAddInt32_assoc {d : Nat} (a b c : Fin d → Int32) :
    blockAddInt32 (blockAddInt32 a b) c = blockAddInt32 a (blockAddInt32 b c) := by
  funext j; unfold blockAddInt32; exact Int32.add_assoc (a j) (b j) (c j)

theorem blockAddInt32_comm {d : Nat} (a b : Fin d → Int32) :
    blockAddInt32 a b = blockAddInt32 b a := by
  funext j; unfold blockAddInt32; exact Int32.add_comm (a j) (b j)

theorem blockAddInt32_zero_left {d : Nat} (a : Fin d → Int32) :
    blockAddInt32 (blockZeroInt32 d) a = a := by
  funext j; unfold blockAddInt32 blockZeroInt32; exact Int32.zero_add (a j)

theorem blockAddInt32_zero_right {d : Nat} (a : Fin d → Int32) :
    blockAddInt32 a (blockZeroInt32 d) = a := by
  funext j; unfold blockAddInt32 blockZeroInt32; exact Int32.add_zero (a j)

theorem blockAccumInt32_cons {d : Nat} (g : Fin d → Int32) (gs : List (Fin d → Int32)) :
    blockAccumInt32 (g :: gs) = blockAddInt32 g (blockAccumInt32 gs) := by
  unfold blockAccumInt32
  have hgen : ∀ (acc : Fin d → Int32) (ys : List (Fin d → Int32)),
      ys.foldl blockAddInt32 acc = blockAddInt32 acc (ys.foldl blockAddInt32 (blockZeroInt32 d)) := by
    intro acc ys
    induction ys generalizing acc with
    | nil => simp [blockAddInt32_zero_right]
    | cons y ys ih =>
      simp only [List.foldl_cons, blockAddInt32_zero_left]
      rw [ih (blockAddInt32 acc y), ih y, blockAddInt32_assoc]
  simpa [blockAddInt32_zero_left] using hgen g gs

theorem blockAccumInt32_append {d : Nat} (gs hs : List (Fin d → Int32)) :
    blockAccumInt32 (gs ++ hs) = blockAddInt32 (blockAccumInt32 gs) (blockAccumInt32 hs) := by
  induction gs with
  | nil => simp [blockAccumInt32, blockAddInt32_zero_left]
  | cons g gs ih =>
    rw [List.cons_append, blockAccumInt32_cons, blockAccumInt32_cons, ih, blockAddInt32_assoc]

theorem blockAccumInt32_perm {d : Nat} {gs hs : List (Fin d → Int32)} (h : List.Perm gs hs) :
    blockAccumInt32 gs = blockAccumInt32 hs := by
  induction h with
  | nil => rfl
  | cons g _ ih => rw [blockAccumInt32_cons, blockAccumInt32_cons, ih]
  | swap g1 g2 l =>
    rw [blockAccumInt32_cons, blockAccumInt32_cons, blockAccumInt32_cons, blockAccumInt32_cons,
        ← blockAddInt32_assoc, blockAddInt32_comm g2 g1, blockAddInt32_assoc]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ### `Int64` Register Block Accumulation -/

theorem blockAddInt64_assoc {d : Nat} (a b c : Fin d → Int64) :
    blockAddInt64 (blockAddInt64 a b) c = blockAddInt64 a (blockAddInt64 b c) := by
  funext j; unfold blockAddInt64; exact Int64.add_assoc (a j) (b j) (c j)

theorem blockAddInt64_comm {d : Nat} (a b : Fin d → Int64) :
    blockAddInt64 a b = blockAddInt64 b a := by
  funext j; unfold blockAddInt64; exact Int64.add_comm (a j) (b j)

theorem blockAddInt64_zero_left {d : Nat} (a : Fin d → Int64) :
    blockAddInt64 (blockZeroInt64 d) a = a := by
  funext j; unfold blockAddInt64 blockZeroInt64; exact Int64.zero_add (a j)

theorem blockAddInt64_zero_right {d : Nat} (a : Fin d → Int64) :
    blockAddInt64 a (blockZeroInt64 d) = a := by
  funext j; unfold blockAddInt64 blockZeroInt64; exact Int64.add_zero (a j)

theorem blockAccumInt64_cons {d : Nat} (g : Fin d → Int64) (gs : List (Fin d → Int64)) :
    blockAccumInt64 (g :: gs) = blockAddInt64 g (blockAccumInt64 gs) := by
  unfold blockAccumInt64
  have hgen : ∀ (acc : Fin d → Int64) (ys : List (Fin d → Int64)),
      ys.foldl blockAddInt64 acc = blockAddInt64 acc (ys.foldl blockAddInt64 (blockZeroInt64 d)) := by
    intro acc ys
    induction ys generalizing acc with
    | nil => simp [blockAddInt64_zero_right]
    | cons y ys ih =>
      simp only [List.foldl_cons, blockAddInt64_zero_left]
      rw [ih (blockAddInt64 acc y), ih y, blockAddInt64_assoc]
  simpa [blockAddInt64_zero_left] using hgen g gs

theorem blockAccumInt64_append {d : Nat} (gs hs : List (Fin d → Int64)) :
    blockAccumInt64 (gs ++ hs) = blockAddInt64 (blockAccumInt64 gs) (blockAccumInt64 hs) := by
  induction gs with
  | nil => simp [blockAccumInt64, blockAddInt64_zero_left]
  | cons g gs ih =>
    rw [List.cons_append, blockAccumInt64_cons, blockAccumInt64_cons, ih, blockAddInt64_assoc]

theorem blockAccumInt64_perm {d : Nat} {gs hs : List (Fin d → Int64)} (h : List.Perm gs hs) :
    blockAccumInt64 gs = blockAccumInt64 hs := by
  induction h with
  | nil => rfl
  | cons g _ ih => rw [blockAccumInt64_cons, blockAccumInt64_cons, ih]
  | swap g1 g2 l =>
    rw [blockAccumInt64_cons, blockAccumInt64_cons, blockAccumInt64_cons, blockAccumInt64_cons,
        ← blockAddInt64_assoc, blockAddInt64_comm g2 g1, blockAddInt64_assoc]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ### Exact Register-to-Integer Bridge & Pairwise Tree Equivalence -/

theorem blockAccumInt32_eval {d : Nat} (gs : List (Fin d → Int)) (j : Fin d) :
    blockAccumInt32 (gs.map (fun g k => Int32.ofInt (g k))) j =
      Int32.ofInt (blockAccum gs j) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, blockAccumInt32_cons, blockAccum_cons]
    unfold blockAddInt32 blockAdd
    rw [ih, Int32.ofInt_add]

theorem blockAccumInt64_eval {d : Nat} (gs : List (Fin d → Int)) (j : Fin d) :
    blockAccumInt64 (gs.map (fun g k => Int64.ofInt (g k))) j =
      Int64.ofInt (blockAccum gs j) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, blockAccumInt64_cons, blockAccum_cons]
    unfold blockAddInt64 blockAdd
    rw [ih, Int64.ofInt_add]

theorem int64_toInt_ofInt_exact {x : Int} (hlo : int64Min ≤ x) (hhi : x ≤ int64Max) :
    (Int64.ofInt x).toInt = x := by
  rw [Int64.toInt_ofInt]
  unfold int64Min at hlo
  unfold int64Max at hhi
  unfold Int.bmod Int64.size
  dsimp only
  split <;> omega

theorem pairwiseStep_seqIntSum (xs : List Int) :
    seqIntSum (pairwiseStep (· + ·) xs) = seqIntSum xs := by
  match xs with
  | [] => rfl
  | [a] => rfl
  | a :: b :: rest =>
    simp only [pairwiseStep]
    rw [seqIntSum_cons, seqIntSum_cons, seqIntSum_cons, pairwiseStep_seqIntSum rest]
    omega

theorem pairwiseStep_length_lt {α : Type} (op : α → α → α) (a b : α) (rest : List α) :
    (pairwiseStep op (a :: b :: rest)).length < (a :: b :: rest).length := by
  match rest with
  | [] => simp [pairwiseStep]
  | [c] => simp [pairwiseStep]
  | c :: d :: rest' =>
    have ih := pairwiseStep_length_lt op c d rest'
    change (op a b :: pairwiseStep op (c :: d :: rest')).length < (a :: b :: c :: d :: rest').length
    simp only [List.length_cons] at ih ⊢
    omega

theorem treeReduceAux_int_eq_seqIntSum :
    ∀ (fuel : Nat) (xs : List Int), xs.length ≤ fuel →
      treeReduceAux (· + ·) 0 fuel xs = seqIntSum xs
  | 0, [], _ => rfl
  | 0, _ :: _, h => by simp at h
  | _ + 1, [], _ => rfl
  | _ + 1, [a], _ => by simp [treeReduceAux, seqIntSum]
  | fuel + 1, a :: b :: rest, h => by
    simp only [treeReduceAux]
    have hlt := pairwiseStep_length_lt (· + ·) a b rest
    have hle : (pairwiseStep (· + ·) (a :: b :: rest)).length ≤ fuel := by omega
    rw [treeReduceAux_int_eq_seqIntSum fuel _ hle, pairwiseStep_seqIntSum]

theorem treeIntSum_eq_seqIntSum (xs : List Int) :
    treeIntSum xs = seqIntSum xs :=
  treeReduceAux_int_eq_seqIntSum xs.length xs (Nat.le_refl _)

/-- Headline Theorem 6 (`shared_exponent_int32_block_accum_associativity`):
    Unconditional associativity, permutation invariance, reversal invariance, pairwise-tree
    equivalence, and zero-overflow exactness of `Int`, `Int32`, and `Int64` shared-exponent
    microbatch block accumulators. -/
theorem shared_exponent_int32_block_accum_associativity :
    (∀ (d : Nat) (gs hs : List (Fin d → Int)),
      blockAccum (gs ++ hs) = blockAdd (blockAccum gs) (blockAccum hs)) ∧
    (∀ (d : Nat) (gs hs : List (Fin d → Int)), List.Perm gs hs →
      blockAccum gs = blockAccum hs) ∧
    (∀ (d : Nat) (gs hs : List (Fin d → Int32)),
      blockAccumInt32 (gs ++ hs) = blockAddInt32 (blockAccumInt32 gs) (blockAccumInt32 hs)) ∧
    (∀ (d : Nat) (gs hs : List (Fin d → Int32)), List.Perm gs hs →
      blockAccumInt32 gs = blockAccumInt32 hs) ∧
    (∀ (d : Nat) (gs hs : List (Fin d → Int64)),
      blockAccumInt64 (gs ++ hs) = blockAddInt64 (blockAccumInt64 gs) (blockAccumInt64 hs)) ∧
    (∀ (d : Nat) (gs hs : List (Fin d → Int64)), List.Perm gs hs →
      blockAccumInt64 gs = blockAccumInt64 hs) ∧
    (∀ (d : Nat) (gs : List (Fin d → Int32)),
      blockAccumInt32 gs.reverse = blockAccumInt32 gs) ∧
    (∀ (xs : List Int), treeIntSum xs = seqIntSum xs) ∧
    (∀ (d : Nat) (gs : List (Fin d → Int)) (j : Fin d),
      int32Min ≤ blockAccum gs j → blockAccum gs j ≤ int32Max →
      (blockAccumInt32 (gs.map (fun g k => Int32.ofInt (g k))) j).toInt = blockAccum gs j) ∧
    (∀ (d : Nat) (gs : List (Fin d → Int)) (j : Fin d),
      int64Min ≤ blockAccum gs j → blockAccum gs j ≤ int64Max →
      (blockAccumInt64 (gs.map (fun g k => Int64.ofInt (g k))) j).toInt = blockAccum gs j) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d gs hs; exact blockAccum_append gs hs
  · intro d gs hs h; exact blockAccum_perm h
  · intro d gs hs; exact blockAccumInt32_append gs hs
  · intro d gs hs h; exact blockAccumInt32_perm h
  · intro d gs hs; exact blockAccumInt64_append gs hs
  · intro d gs hs h; exact blockAccumInt64_perm h
  · intro d gs; exact blockAccumInt32_perm (List.reverse_perm gs)
  · intro xs; exact treeIntSum_eq_seqIntSum xs
  · intro d gs j hlo hhi
    rw [blockAccumInt32_eval, int32_toInt_ofInt_exact hlo hhi]
  · intro d gs j hlo hhi
    rw [blockAccumInt64_eval, int64_toInt_ofInt_exact hlo hhi]

end KahanNeumaierFp8
