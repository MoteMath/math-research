/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SparseE2M1Rotations.MatrixAlg

/-!
# Headline Theorems (`sparse-e2m1-rotations`)

1. `walshHadamard_doubly24_factorization`: Universal doubly-2:4-sparse orthogonal factorization
   `H_{2^(k+2)} = (H_{2^k} ⊗ B1)(I_{2^k} ⊗ B2)` for all `k : Nat`.
2. `single24_coherence_lower_bound` & `walsh_weighing_attains_coherence_bound`:
   Sharp single-2:4 coherence lower bound `(4m) * M^2 ≥ 2c` for all `m ≥ 1`, attained with
   exact equality by `W_{4 * 2^k} = H_{2^k} ⊗ B1` for all `k : Nat`.
3. `skewConference_e2m1_orthogonal`: Universal skew-conference orthogonality
   `(a I + C)^T (a I + C) = (a^2 + n - 1) I` and E2M1-native entry preservation for all `n : Nat`.
4. `q32_pow2_e2m1_exact` & `q16_skew41_e2m1_exact`:
   Exact power-of-2 norm `Q32^T Q32 = 16^2 I_32` with entries in `{-3, -1, 1, 3} ⊂ 2*E2M1`
   and NVFP4 winner `Q16^T Q16 = 31 I_16` with entries in `{-1, 1, 4} ⊂ 2*E2M1`.
5. `g4k_doubly24_e2m1_orthogonal`: Universal doubly-2:4-sparse E2M1-native Givens-Hadamard
   family `G_{4 * 2^k}(1, 2) = H_{2^k} ⊗ G_4(1, 2)` with `G^T G = (5 * 2^k) I` for all `k : Nat`.
-/

namespace SparseE2M1Rotations

/-! ### Part 1: Universal Doubly-2:4-Sparse Walsh–Hadamard Factorization -/

theorem B1_matMul_B2 : matMul B1 B2 = walshHadamardOf 4 := by
  funext i j; revert i j; decide

theorem B1_orthogonal : isOrthogonal B1 2 := by
  funext i j; revert i j; decide

theorem B1_rowOrthogonal : isRowOrthogonal B1 2 := by
  funext i j; revert i j; decide

theorem B2_orthogonal : isOrthogonal B2 2 := by
  funext i j; revert i j; decide

theorem B1_24_rows : ∀ i : Fin 4,
    nzCount4 (B1 i ⟨0, by omega⟩) (B1 i ⟨1, by omega⟩)
             (B1 i ⟨2, by omega⟩) (B1 i ⟨3, by omega⟩) ≤ 2 := by
  decide

theorem B1_24_cols : ∀ i : Fin 4,
    nzCount4 (transpose B1 i ⟨0, by omega⟩) (transpose B1 i ⟨1, by omega⟩)
             (transpose B1 i ⟨2, by omega⟩) (transpose B1 i ⟨3, by omega⟩) ≤ 2 := by
  decide

theorem B2_24_rows : ∀ i : Fin 4,
    nzCount4 (B2 i ⟨0, by omega⟩) (B2 i ⟨1, by omega⟩)
             (B2 i ⟨2, by omega⟩) (B2 i ⟨3, by omega⟩) ≤ 2 := by
  decide

theorem B2_24_cols : ∀ i : Fin 4,
    nzCount4 (transpose B2 i ⟨0, by omega⟩) (transpose B2 i ⟨1, by omega⟩)
             (transpose B2 i ⟨2, by omega⟩) (transpose B2 i ⟨3, by omega⟩) ≤ 2 := by
  decide

theorem B1_ternary : matEntriesIn isTernary B1 := by
  intro i j; unfold isTernary; revert i j; decide

theorem B2_ternary : matEntriesIn isTernary B2 := by
  intro i j; unfold isTernary; revert i j; decide

theorem idMat_ternary (n : Nat) : matEntriesIn isTernary (idMat n) := by
  intro i j
  simp only [idMat, isTernary]
  by_cases h : i = j <;> simp [h]

theorem idMat_orthogonal (n : Nat) : isOrthogonal (idMat n) 1 := by
  unfold isOrthogonal
  rw [transpose_idMat, matMul_idMat_left]
  funext i j
  simp [scaleMat]

/-- Theorem 1 (Universal Doubly-2:4-Sparse Walsh–Hadamard Factorization):
    For every `k : Nat`, `H_{2^(k+2)} = (H_{2^k} ⊗ B1)(I_{2^k} ⊗ B2)`, where both factors
    are doubly-2:4-sparse, ternary (`{-1, 0, 1}`), and exact integer orthogonal. -/
theorem walshHadamard_doubly24_factorization (k : Nat) :
    let Q1 := kron (walshHadamard k) B1
    let Q2 := kron (idMat (2 ^ k)) B2
    matMul Q1 Q2 = walshHadamardOf (2 ^ k * 4) ∧
    isDoubly24Sparse Q1 ∧
    isDoubly24Sparse Q2 ∧
    matEntriesIn isTernary Q1 ∧
    matEntriesIn isTernary Q2 ∧
    isOrthogonal Q1 (2 * ((2 ^ k : Nat) : Int)) ∧
    isOrthogonal Q2 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [kron_matMul, matMul_idMat_right, B1_matMul_B2, walshHadamardOf_mul_four]
  · exact kron_isDoubly24Sparse (walshHadamard k) B1 B1_24_rows B1_24_cols
  · exact kron_isDoubly24Sparse (idMat (2 ^ k)) B2 B2_24_rows B2_24_cols
  · exact kron_matEntriesIn_ternary (walshHadamard_ternary k) B1_ternary
  · exact kron_matEntriesIn_ternary (idMat_ternary (2 ^ k)) B2_ternary
  · have h := kron_isOrthogonal (walshHadamard_orthogonal k) B1_orthogonal
    rw [Int.mul_comm] at h
    exact h
  · have h := kron_isOrthogonal (idMat_orthogonal (2 ^ k)) B2_orthogonal
    rw [Int.one_mul] at h
    exact h

/-! ### Part 2: Sharp Single-2:4 Coherence Lower Bound & Walsh-Weighing Attainment -/

private theorem sq_le_of_bounds {x M : Int} (hlo : -M ≤ x) (hhi : x ≤ M) :
    x * x ≤ M * M := by
  have h1 : 0 ≤ M - x := by omega
  have h2 : 0 ≤ M + x := by omega
  have hprod : 0 ≤ (M - x) * (M + x) := Int.mul_nonneg h1 h2
  have hexpand : (M - x) * (M + x) = M * M - x * x := by
    rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.mul_comm x M]
    omega
  omega

private theorem sq_term_le {x M : Int} (hsq : x * x ≤ M * M) :
    x * x ≤ ((if x != 0 then (1 : Nat) else 0) : Nat) * (M * M) := by
  by_cases hx : x = 0
  · subst hx; simp
  · simp [hx, hsq]

private theorem sum4_sq_le_two_mul {a b d e M : Int}
    (hnz : nzCount4 a b d e ≤ 2)
    (ha : a * a ≤ M * M) (hb : b * b ≤ M * M)
    (hd : d * d ≤ M * M) (he : e * e ≤ M * M) :
    a * a + b * b + d * d + e * e ≤ 2 * (M * M) := by
  have h0 : 0 ≤ M * M := by
    by_cases hM : 0 ≤ M
    · exact Int.mul_nonneg hM hM
    · have hM' : 0 ≤ -M := by omega
      have h := Int.mul_nonneg hM' hM'
      simpa [Int.neg_mul, Int.mul_neg] using h
  have hta := sq_term_le ha
  have htb := sq_term_le hb
  have htd := sq_term_le hd
  have hte := sq_term_le he
  have hsum : a * a + b * b + d * d + e * e ≤ (nzCount4 a b d e : Int) * (M * M) := by
    unfold nzCount4
    simp only [Int.natCast_add, Int.add_mul]
    omega
  have hle : (nzCount4 a b d e : Int) * (M * M) ≤ 2 * (M * M) := by
    have hnzI : (nzCount4 a b d e : Int) ≤ 2 := by omega
    have hdiff : 0 ≤ (2 - (nzCount4 a b d e : Int)) * (M * M) :=
      Int.mul_nonneg (by omega) h0
    rw [Int.sub_mul] at hdiff
    omega
  omega

/-- Theorem 2a (Universal Single-2:4 Coherence Lower Bound):
    For any `m ≥ 1`, any `(4m) × (4m)` row-2:4-sparse row-orthogonal integer matrix `Q`
    with `Q Q^T = c I` and entry bound `|Q_{ij}| ≤ M`, we have `2 c ≤ (4 m) M^2`,
    equivalently `μ = M / √c ≥ √(2 / N)`. -/
theorem single24_coherence_lower_bound (m : Nat) (hm : 1 ≤ m)
    (c M : Int) (_hM : 0 ≤ M) (Q : IntMat (m * 4) (m * 4))
    (hsp : is24SparseRows Q)
    (horth : isRowOrthogonal Q c)
    (hbound : ∀ i j, -M ≤ Q i j ∧ Q i j ≤ M) :
    2 * c ≤ ((m * 4 : Nat) : Int) * (M * M) := by
  let i0 : Fin (m * 4) := ⟨0, by omega⟩
  have hdiag : matMul Q (transpose Q) i0 i0 = c := by
    have h := congrFun (congrFun horth i0) i0
    simp only [scaleMat, idMat, ↓reduceIte, Int.mul_one] at h
    exact h
  have hnorm : sumFin (m * 4) (fun j => Q i0 j * Q i0 j) = c := by
    simpa [matMul, transpose] using hdiag
  rw [sumFin_prod m 4] at hnorm
  have hgroup : ∀ g : Fin m,
      sumFin 4 (fun r => Q i0 ⟨g.val * 4 + r.val, by omega⟩ *
                         Q i0 ⟨g.val * 4 + r.val, by omega⟩) ≤ 2 * (M * M) := by
    intro g
    have hspg := hsp i0 g
    have h0 := hbound i0 ⟨g.val * 4 + 0, by omega⟩
    have h1 := hbound i0 ⟨g.val * 4 + 1, by omega⟩
    have h2 := hbound i0 ⟨g.val * 4 + 2, by omega⟩
    have h3 := hbound i0 ⟨g.val * 4 + 3, by omega⟩
    have hsum4 := sum4_sq_le_two_mul hspg
      (sq_le_of_bounds h0.1 h0.2) (sq_le_of_bounds h1.1 h1.2)
      (sq_le_of_bounds h2.1 h2.2) (sq_le_of_bounds h3.1 h3.2)
    simp only [sumFin, Fin.castSucc, Fin.last, Int.zero_add]
    exact hsum4
  have htotal : c ≤ (m : Int) * (2 * (M * M)) := by
    rw [← hnorm, ← sumFin_const m (2 * (M * M))]
    exact sumFin_le hgroup
  have hcast : ((m * 4 : Nat) : Int) * (M * M) = 2 * ((m : Int) * (2 * (M * M))) := by
    have h1 : ((m * 4 : Nat) : Int) = (m : Int) * 4 := by omega
    rw [h1]
    have h2 : (m : Int) * 4 * (M * M) = 2 * ((m : Int) * (2 * (M * M))) := by
      have : (m : Int) * 4 = (m : Int) * (2 * 2) := by omega
      rw [this, Int.mul_assoc, Int.mul_assoc, ← Int.mul_assoc (m : Int) 2, Int.mul_comm (m : Int) 2, Int.mul_assoc]
    exact h2
  omega

/-- Theorem 2b (Exact Attainment by Walsh Weighing Matrices):
    For every `k : Nat`, `W_{4 * 2^k} = H_{2^k} ⊗ B1` is doubly-2:4-sparse, orthogonal with
    `c = 2 * 2^k`, has entries in `[-1, 1]`, and attains exact equality `(4 * 2^k) * 1^2 = 2c`. -/
theorem walsh_weighing_attains_coherence_bound (k : Nat) :
    let W := kron (walshHadamard k) B1
    let c : Int := 2 * ((2 ^ k : Nat) : Int)
    isDoubly24Sparse W ∧
    isOrthogonal W c ∧
    isRowOrthogonal W c ∧
    (∀ i j, -1 ≤ W i j ∧ W i j ≤ 1) ∧
    ((2 ^ k * 4 : Nat) : Int) * (1 * 1) = 2 * c := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact kron_isDoubly24Sparse (walshHadamard k) B1 B1_24_rows B1_24_cols
  · have h := kron_isOrthogonal (walshHadamard_orthogonal k) B1_orthogonal
    rw [Int.mul_comm] at h
    exact h
  · have h := kron_isRowOrthogonal (walshHadamard_rowOrthogonal k) B1_rowOrthogonal
    rw [Int.mul_comm] at h
    exact h
  · intro i j
    have ht := kron_matEntriesIn_ternary (walshHadamard_ternary k) B1_ternary i j
    rcases ht with h | h | h <;> omega
  · omega

/-! ### Part 3: Universal Skew-Conference E2M1 Orthogonality -/

/-- Two-parameter universal skew-conference orthogonality:
    if `C^T = -C` and `C^T C = (n - 1) I`, then `(a I + b C)^T (a I + b C) = (a^2 + b^2(n - 1)) I`. -/
theorem skewConference_ab_orthogonal (n : Nat) (C : IntMat n n) (a b : Int)
    (hskew : transpose C = negMat C)
    (hconf : matMul (transpose C) C = scaleMat ((n : Int) - 1) (idMat n)) :
    isOrthogonal (addMat (scaleMat a (idMat n)) (scaleMat b C))
      (a * a + b * b * ((n : Int) - 1)) := by
  unfold isOrthogonal
  rw [transpose_addMat, transpose_scaleMat, transpose_scaleMat, transpose_idMat, hskew]
  rw [matMul_add_left, matMul_add_right, matMul_add_right]
  rw [matMul_scaleMat_left, matMul_scaleMat_right, matMul_idMat_left]
  rw [matMul_scaleMat_left, matMul_scaleMat_right, matMul_idMat_left]
  rw [matMul_scaleMat_left, matMul_scaleMat_right, matMul_neg_left, matMul_idMat_right]
  rw [matMul_scaleMat_left, matMul_scaleMat_right]
  have hnegC : matMul (negMat C) C = scaleMat ((n : Int) - 1) (idMat n) := by
    rw [← hskew]; exact hconf
  rw [hnegC]
  funext i j
  simp only [addMat, scaleMat, negMat]
  have hba : b * (a * -(C i j)) = -(a * (b * C i j)) := by
    rw [Int.mul_neg, Int.mul_neg, ← Int.mul_assoc, Int.mul_comm b a, Int.mul_assoc]
  have h1 : a * (a * idMat n i j) = (a * a) * idMat n i j := by rw [Int.mul_assoc]
  have h2 : b * (b * (((n : Int) - 1) * idMat n i j)) = (b * b * ((n : Int) - 1)) * idMat n i j := by
    rw [Int.mul_assoc, Int.mul_assoc]
  rw [hba, h1, h2, Int.add_mul]
  omega

/-- Theorem 3 (Universal Skew-Conference E2M1 Orthogonality):
    For any `n : Nat`, skew-conference matrix `C` (`C^T = -C`, `C^T C = (n - 1) I`), and `a : Int`,
    `(a I + C)^T (a I + C) = (a^2 + n - 1) I`, and if `a ∈ 2*E2M1`, `diag(C) = 0`, and `C` is
    ternary, then `a I + C` is E2M1-native. -/
theorem skewConference_e2m1_orthogonal (n : Nat) (C : IntMat n n) (a : Int)
    (hskew : transpose C = negMat C)
    (hconf : matMul (transpose C) C = scaleMat ((n : Int) - 1) (idMat n)) :
    isOrthogonal (addMat (scaleMat a (idMat n)) C) (a * a + (n : Int) - 1) ∧
    (isDoubledE2M1 a → (∀ i, C i i = 0) → matEntriesIn isTernary C →
      matEntriesIn isDoubledE2M1 (addMat (scaleMat a (idMat n)) C)) := by
  constructor
  · have h := skewConference_ab_orthogonal n C a 1 hskew hconf
    have hscale1 : scaleMat 1 C = C := by
      funext i j; simp [scaleMat]
    rw [hscale1] at h
    have hc : a * a + 1 * 1 * ((n : Int) - 1) = a * a + (n : Int) - 1 := by omega
    rw [hc] at h
    exact h
  · intro ha hdiag htern i j
    simp only [addMat, scaleMat, idMat]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte, Int.mul_one, hdiag i, Int.add_zero]
      exact ha
    · simp only [hij, ↓reduceIte, Int.mul_zero, Int.zero_add]
      rcases htern i j with h | h | h <;> simp [h, isDoubledE2M1]

/-! ### Part 4: Exact Power-of-2 `Q32` and NVFP4 Winner `Q16` -/

theorem paleyC8_skew : transpose paleyC8 = negMat paleyC8 := by
  funext i j; revert i j; decide

theorem paleyC8_conf : matMul (transpose paleyC8) paleyC8 = scaleMat 7 (idMat 8) := by
  funext i j; revert i j; decide

theorem paleyC8_diag : ∀ i : Fin 8, paleyC8 i i = 0 := by
  decide

theorem paleyC8_offdiag : ∀ i j : Fin 8, i ≠ j → paleyC8 i j = -1 ∨ paleyC8 i j = 1 := by
  decide

theorem walshHadamardOf_four_orthogonal : isOrthogonal (walshHadamardOf 4) 4 := by
  have h := walshHadamard_orthogonal 2
  exact h

theorem walshHadamardOf_four_pm1 :
    matEntriesIn (fun x => x = -1 ∨ x = 1) (walshHadamardOf 4) := by
  intro i j
  simp only [walshHadamardOf, walshEntry]
  cases bitParity (i.val &&& j.val) <;> simp

/-- Theorem 4a (Exact Power-of-2 Dense E2M1-Native `32 × 32` Rotation):
    `Q32 = H_4 ⊗ (I_8 + 3 C_8)` satisfies `Q32^T Q32 = 16^2 I_32 = 256 I_32`
    with all entries strictly in `{-3, -1, 1, 3} ⊂ 2*E2M1`. -/
theorem q32_pow2_e2m1_exact :
    isOrthogonal Q32 (16 * 16) ∧
    matEntriesIn (fun x => x = -3 ∨ x = -1 ∨ x = 1 ∨ x = 3) Q32 ∧
    matEntriesIn isDoubledE2M1 Q32 := by
  have hQ8 : isOrthogonal (addMat (idMat 8) (scaleMat 3 paleyC8)) 64 := by
    have h := skewConference_ab_orthogonal 8 paleyC8 1 3 paleyC8_skew paleyC8_conf
    have hscale1 : scaleMat 1 (idMat 8) = idMat 8 := by
      funext i j; simp [scaleMat]
    rw [hscale1] at h
    exact h
  have hQ32_orth : isOrthogonal Q32 (16 * 16) := by
    unfold Q32
    have h := kron_isOrthogonal walshHadamardOf_four_orthogonal hQ8
    exact h
  have hQ8_entries : ∀ i j : Fin 8,
      addMat (idMat 8) (scaleMat 3 paleyC8) i j = -3 ∨
      addMat (idMat 8) (scaleMat 3 paleyC8) i j = 1 ∨
      addMat (idMat 8) (scaleMat 3 paleyC8) i j = 3 := by
    intro i j
    simp only [addMat, idMat, scaleMat]
    by_cases hij : i = j
    · subst hij
      simp [paleyC8_diag i]
    · simp only [hij, ↓reduceIte, Int.zero_add]
      rcases paleyC8_offdiag i j hij with h | h <;> simp [h]
  have hQ32_entries : matEntriesIn (fun x => x = -3 ∨ x = -1 ∨ x = 1 ∨ x = 3) Q32 := by
    intro i j
    unfold Q32
    simp only [kron]
    have hH := walshHadamardOf_four_pm1
      ⟨i.val / 8, div_lt_left_of_fin_mul i⟩ ⟨j.val / 8, div_lt_left_of_fin_mul j⟩
    have h8 := hQ8_entries
      ⟨i.val % 8, Nat.mod_lt _ (pos_right_of_fin_mul i)⟩
      ⟨j.val % 8, Nat.mod_lt _ (pos_right_of_fin_mul j)⟩
    rcases hH with hH | hH <;> rcases h8 with h8 | h8 | h8 <;> simp [hH, h8]
  refine ⟨hQ32_orth, hQ32_entries, ?_⟩
  intro i j
  rcases hQ32_entries i j with h | h | h | h <;> simp [h, isDoubledE2M1]

/-- Universal skew-conference doubling: if `C` is an `n × n` skew-conference matrix,
    then `skewDouble C` is a `(2 * n) × (2 * n)` skew-conference matrix. -/
theorem skewDouble_skew {n : Nat} (C : IntMat n n) (hskew : transpose C = negMat C) :
    transpose (skewDouble C) = negMat (skewDouble C) := by
  funext i j
  simp only [transpose, negMat, skewDouble]
  have hC : ∀ a b : Fin n, C b a = -C a b := fun a b => congrFun (congrFun hskew a) b
  have hI : ∀ a b : Fin n, idMat n b a = idMat n a b := fun a b => congrFun (congrFun (transpose_idMat n) a) b
  by_cases hi : i.val / n = 0 <;> by_cases hj : j.val / n = 0 <;>
    simp only [hi, hj, ↓reduceIte]
  · exact hC _ _
  · rw [hI, hC]; omega
  · rw [hI, hC]; omega
  · rw [hC]

theorem skewDouble_conf {n : Nat} (C : IntMat n n)
    (hskew : transpose C = negMat C)
    (hconf : matMul (transpose C) C = scaleMat ((n : Int) - 1) (idMat n)) :
    matMul (transpose (skewDouble C)) (skewDouble C) =
      scaleMat (((2 * n : Nat) : Int) - 1) (idMat (2 * n)) := by
  funext i j
  have hn : 0 < n := pos_right_of_fin_mul i
  rw [skewDouble_skew C hskew]
  simp only [matMul, negMat, scaleMat, idMat]
  have h2n : 2 * n = n + n := by omega
  rw [sumFin_cast h2n, sumFin_add_split n n]
  have hCsq : ∀ a b : Fin n,
      sumFin n (fun t => C a t * C t b) = -(((n : Int) - 1) * idMat n a b) := by
    intro a b
    have h1 := congrFun (congrFun hconf a) b
    rw [hskew] at h1
    simp only [matMul, negMat, scaleMat] at h1
    have hneg : sumFin n (fun t => (-C a t) * C t b) = -(sumFin n (fun t => C a t * C t b)) := by
      have : ∀ t : Fin n, (-C a t) * C t b = -(C a t * C t b) := fun t => Int.neg_mul _ _
      rw [sumFin_congr this, sumFin_neg]
    rw [hneg] at h1
    omega
  have hIC : ∀ a b : Fin n, sumFin n (fun t => idMat n a t * C t b) = C a b := by
    intro a b
    exact congrFun (congrFun (matMul_idMat_left C) a) b
  have hCI : ∀ a b : Fin n, sumFin n (fun t => C a t * idMat n t b) = C a b := by
    intro a b
    exact congrFun (congrFun (matMul_idMat_right C) a) b
  have hII : ∀ a b : Fin n, sumFin n (fun t => idMat n a t * idMat n t b) = idMat n a b := by
    intro a b
    exact congrFun (congrFun (matMul_idMat_left (idMat n)) a) b
  have hdiv0 : ∀ t : Fin n, t.val / n = 0 := fun t => Nat.div_eq_of_lt t.isLt
  have hmod0 : ∀ t : Fin n, t.val % n = t.val := fun t => Nat.mod_eq_of_lt t.isLt
  have hdiv1 : ∀ t : Fin n, (n + t.val) / n = 1 := by
    intro t
    rw [Nat.add_div_left t.val hn, Nat.div_eq_of_lt t.isLt]
  have hmod1 : ∀ t : Fin n, (n + t.val) % n = t.val := by
    intro t
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt t.isLt]
  let ri : Fin n := ⟨i.val % n, Nat.mod_lt _ hn⟩
  let rj : Fin n := ⟨j.val % n, Nat.mod_lt _ hn⟩
  have hi_lt : i.val / n < 2 := div_lt_left_of_fin_mul i
  have hj_lt : j.val / n < 2 := div_lt_left_of_fin_mul j
  have hsum0 : ∀ t : Fin n,
      (⟨t.val % n, Nat.mod_lt _ hn⟩ : Fin n) = t := fun t => Fin.ext (hmod0 t)
  have hsum1 : ∀ t : Fin n,
      (⟨(n + t.val) % n, Nat.mod_lt _ hn⟩ : Fin n) = t := fun t => Fin.ext (hmod1 t)
  have hmul_expand : ∀ (u v w z : Int),
      (u + v) * (w + z) = u * w + u * z + (v * w + v * z) := by
    intro u v w z
    rw [Int.add_mul, Int.mul_add, Int.mul_add]
  have hri_eq_rj : (ri = rj) ↔ (i.val % n = j.val % n) := by
    constructor
    · intro h; exact congrArg Fin.val h
    · intro h; exact Fin.ext h
  have hij_iff_same : i.val / n = j.val / n → (i = j ↔ ri = rj) := by
    intro hdiv
    constructor
    · intro h; subst h; rfl
    · intro h
      have hm : i.val % n = j.val % n := congrArg Fin.val h
      have hi := Nat.div_add_mod i.val n
      have hj := Nat.div_add_mod j.val n
      exact Fin.ext (by rw [hdiv, hm] at hi; omega)
  have hij_ne_diff : i.val / n ≠ j.val / n → i ≠ j := by
    intro hne h
    subst h
    exact hne rfl
  by_cases hi0 : i.val / n = 0 <;> by_cases hj0 : j.val / n = 0
  · -- Block (0, 0): (-C)(C) + (-(I+C))(-I+C) = -C^2 + I - C^2 = (2n - 1) I
    have hA : sumFin n (fun t => -(skewDouble C i ⟨t.val, by omega⟩) * skewDouble C ⟨t.val, by omega⟩ j) =
        -(sumFin n (fun t => C ri t * C t rj)) := by
      rw [← sumFin_neg]
      apply sumFin_congr; intro t
      simp only [skewDouble, hi0, hj0, hdiv0 t, ↓reduceIte, hsum0 t, Int.neg_mul, ri, rj]
    have hB : sumFin n (fun t => -(skewDouble C i ⟨n + t.val, by omega⟩) * skewDouble C ⟨n + t.val, by omega⟩ j) =
        sumFin n (fun t => idMat n ri t * idMat n t rj) +
        -(sumFin n (fun t => idMat n ri t * C t rj)) +
        (sumFin n (fun t => C ri t * idMat n t rj) +
        -(sumFin n (fun t => C ri t * C t rj))) := by
      rw [← sumFin_neg, ← sumFin_neg, ← sumFin_add, ← sumFin_add, ← sumFin_add]
      apply sumFin_congr; intro t
      have hne1 : (n + t.val) / n ≠ 0 := by rw [hdiv1 t]; omega
      simp only [skewDouble, hi0, hj0, hne1, ↓reduceIte, hsum1 t, ri, rj]
      rw [Int.neg_add, hmul_expand]
      simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    rw [hA, hB, hII, hIC, hCI, hCsq]
    have hsame : (i = j) ↔ (ri = rj) := hij_iff_same (by omega)
    by_cases hij : i = j
    · have hr : ri = rj := hsame.mp hij
      simp only [hij, hr, idMat, ↓reduceIte]
      omega
    · have hr : ri ≠ rj := fun h => hij (hsame.mpr h)
      simp only [hij, hr, idMat, ↓reduceIte]
      omega
  · -- Block (0, 1): (-C)(I+C) + (-(I+C))(-C) = -C - C^2 + C + C^2 = 0
    have hA : sumFin n (fun t => -(skewDouble C i ⟨t.val, by omega⟩) * skewDouble C ⟨t.val, by omega⟩ j) =
        -(sumFin n (fun t => C ri t * idMat n t rj)) +
        -(sumFin n (fun t => C ri t * C t rj)) := by
      rw [← sumFin_neg, ← sumFin_neg, ← sumFin_add]
      apply sumFin_congr; intro t
      simp only [skewDouble, hi0, hj0, hdiv0 t, ↓reduceIte, hsum0 t, ri, rj]
      rw [Int.neg_mul, Int.mul_add, Int.neg_add]
    have hB : sumFin n (fun t => -(skewDouble C i ⟨n + t.val, by omega⟩) * skewDouble C ⟨n + t.val, by omega⟩ j) =
        sumFin n (fun t => idMat n ri t * C t rj) +
        sumFin n (fun t => C ri t * C t rj) := by
      rw [← sumFin_add]
      apply sumFin_congr; intro t
      have hne1 : (n + t.val) / n ≠ 0 := by rw [hdiv1 t]; omega
      simp only [skewDouble, hi0, hj0, hne1, ↓reduceIte, hsum1 t, ri, rj]
      rw [Int.neg_mul, Int.mul_neg, Int.neg_neg, Int.add_mul]
    rw [hA, hB, hIC, hCI]
    have hij : i ≠ j := hij_ne_diff (by omega)
    simp only [hij, ↓reduceIte]
    omega
  · -- Block (1, 0): (-(-I+C))(C) + (-(-C))(-I+C) = C - C^2 - C + C^2 = 0
    have hA : sumFin n (fun t => -(skewDouble C i ⟨t.val, by omega⟩) * skewDouble C ⟨t.val, by omega⟩ j) =
        sumFin n (fun t => idMat n ri t * C t rj) +
        -(sumFin n (fun t => C ri t * C t rj)) := by
      rw [← sumFin_neg, ← sumFin_add]
      apply sumFin_congr; intro t
      simp only [skewDouble, hi0, hj0, hdiv0 t, ↓reduceIte, hsum0 t, ri, rj]
      rw [Int.neg_add, Int.neg_neg, Int.add_mul, Int.neg_mul]
    have hB : sumFin n (fun t => -(skewDouble C i ⟨n + t.val, by omega⟩) * skewDouble C ⟨n + t.val, by omega⟩ j) =
        -(sumFin n (fun t => C ri t * idMat n t rj)) +
        sumFin n (fun t => C ri t * C t rj) := by
      rw [← sumFin_neg, ← sumFin_add]
      apply sumFin_congr; intro t
      have hne1 : (n + t.val) / n ≠ 0 := by rw [hdiv1 t]; omega
      simp only [skewDouble, hi0, hj0, hne1, ↓reduceIte, hsum1 t, ri, rj]
      rw [Int.neg_neg, Int.mul_add, Int.mul_neg]
    rw [hA, hB, hIC, hCI]
    have hij : i ≠ j := hij_ne_diff (by omega)
    simp only [hij, ↓reduceIte]
    omega
  · -- Block (1, 1): (-(-I+C))(I+C) + (-(-C))(-C) = I - C^2 - C^2 = (2n - 1) I
    have hA : sumFin n (fun t => -(skewDouble C i ⟨t.val, by omega⟩) * skewDouble C ⟨t.val, by omega⟩ j) =
        sumFin n (fun t => idMat n ri t * idMat n t rj) +
        sumFin n (fun t => idMat n ri t * C t rj) +
        (-(sumFin n (fun t => C ri t * idMat n t rj)) +
        -(sumFin n (fun t => C ri t * C t rj))) := by
      rw [← sumFin_neg, ← sumFin_neg, ← sumFin_add, ← sumFin_add, ← sumFin_add]
      apply sumFin_congr; intro t
      simp only [skewDouble, hi0, hj0, hdiv0 t, ↓reduceIte, hsum0 t, ri, rj]
      rw [Int.neg_add, Int.neg_neg, hmul_expand]
      simp only [Int.neg_mul]
    have hB : sumFin n (fun t => -(skewDouble C i ⟨n + t.val, by omega⟩) * skewDouble C ⟨n + t.val, by omega⟩ j) =
        -(sumFin n (fun t => C ri t * C t rj)) := by
      rw [← sumFin_neg]
      apply sumFin_congr; intro t
      have hne1 : (n + t.val) / n ≠ 0 := by rw [hdiv1 t]; omega
      simp only [skewDouble, hi0, hj0, hne1, ↓reduceIte, hsum1 t, ri, rj]
      rw [Int.neg_neg, Int.mul_neg]
    rw [hA, hB, hII, hIC, hCI, hCsq]
    have hdiv11 : i.val / n = j.val / n := by
      have h1 : i.val / n = 1 := Nat.le_antisymm (Nat.le_of_lt_succ hi_lt) (Nat.pos_of_ne_zero hi0)
      have h2 : j.val / n = 1 := Nat.le_antisymm (Nat.le_of_lt_succ hj_lt) (Nat.pos_of_ne_zero hj0)
      rw [h1, h2]
    have hsame : (i = j) ↔ (ri = rj) := hij_iff_same hdiv11
    by_cases hij : i = j
    · have hr : ri = rj := hsame.mp hij
      simp only [hij, hr, idMat, ↓reduceIte]
      omega
    · have hr : ri ≠ rj := fun h => hij (hsame.mpr h)
      simp only [hij, hr, idMat, ↓reduceIte]
      omega

theorem C16_skew : transpose C16 = negMat C16 :=
  skewDouble_skew paleyC8 paleyC8_skew

theorem C16_conf : matMul (transpose C16) C16 = scaleMat 15 (idMat (2 * 8)) :=
  skewDouble_conf paleyC8 paleyC8_skew paleyC8_conf

theorem C16_diag : ∀ i : Fin (2 * 8), C16 i i = 0 := by
  intro i
  simp only [C16, skewDouble]
  by_cases hi : i.val / 8 = 0
  · simp only [hi, ↓reduceIte]
    exact paleyC8_diag _
  · simp only [hi, ↓reduceIte]
    rw [paleyC8_diag _]
    rfl

theorem C16_offdiag : ∀ i j : Fin (2 * 8), i ≠ j → C16 i j = -1 ∨ C16 i j = 1 := by
  intro i j hij
  simp only [C16, skewDouble]
  have hi_lt : i.val / 8 < 2 := div_lt_left_of_fin_mul i
  have hj_lt : j.val / 8 < 2 := div_lt_left_of_fin_mul j
  let ri : Fin 8 := ⟨i.val % 8, Nat.mod_lt _ (by omega)⟩
  let rj : Fin 8 := ⟨j.val % 8, Nat.mod_lt _ (by omega)⟩
  by_cases hi0 : i.val / 8 = 0 <;> by_cases hj0 : j.val / 8 = 0 <;>
    simp only [hi0, hj0, ↓reduceIte]
  · have hne : ri ≠ rj := by
      intro h
      apply hij
      have hm : i.val % 8 = j.val % 8 := congrArg Fin.val h
      exact Fin.ext (by omega)
    exact paleyC8_offdiag ri rj hne
  · by_cases hrr : ri = rj
    · have h1 : (⟨i.val % 8, Nat.mod_lt _ (pos_right_of_fin_mul i)⟩ : Fin 8) = ri := rfl
      have h2 : (⟨j.val % 8, Nat.mod_lt _ (pos_right_of_fin_mul i)⟩ : Fin 8) = rj := rfl
      rw [h1, h2, hrr]
      simp [idMat, paleyC8_diag]
    · have h1 : (⟨i.val % 8, Nat.mod_lt _ (pos_right_of_fin_mul i)⟩ : Fin 8) = ri := rfl
      have h2 : (⟨j.val % 8, Nat.mod_lt _ (pos_right_of_fin_mul i)⟩ : Fin 8) = rj := rfl
      rw [h1, h2]
      simp only [idMat, hrr, ↓reduceIte, Int.zero_add]
      exact paleyC8_offdiag ri rj hrr
  · by_cases hrr : ri = rj
    · have h1 : (⟨i.val % 8, Nat.mod_lt _ (pos_right_of_fin_mul i)⟩ : Fin 8) = ri := rfl
      have h2 : (⟨j.val % 8, Nat.mod_lt _ (pos_right_of_fin_mul i)⟩ : Fin 8) = rj := rfl
      rw [h1, h2, hrr]
      simp [idMat, paleyC8_diag]
    · have h1 : (⟨i.val % 8, Nat.mod_lt _ (pos_right_of_fin_mul i)⟩ : Fin 8) = ri := rfl
      have h2 : (⟨j.val % 8, Nat.mod_lt _ (pos_right_of_fin_mul i)⟩ : Fin 8) = rj := rfl
      rw [h1, h2]
      simp only [idMat, hrr, ↓reduceIte, Int.neg_zero, Int.zero_add]
      exact paleyC8_offdiag ri rj hrr
  · have hne : ri ≠ rj := by
      intro h
      apply hij
      have hm : i.val % 8 = j.val % 8 := congrArg Fin.val h
      exact Fin.ext (by omega)
    have h1 : (⟨i.val % 8, Nat.mod_lt _ (pos_right_of_fin_mul i)⟩ : Fin 8) = ri := rfl
    have h2 : (⟨j.val % 8, Nat.mod_lt _ (pos_right_of_fin_mul i)⟩ : Fin 8) = rj := rfl
    rw [h1, h2]
    rcases paleyC8_offdiag ri rj hne with h | h <;> simp [h]

/-- Theorem 4b (Exact NVFP4 Winner `Q16 = 4 I_16 + C_16`):
    `Q16^T Q16 = 31 I_16`, with all entries strictly in `{-1, 1, 4} ⊂ 2*E2M1`. -/
theorem q16_skew41_e2m1_exact :
    isOrthogonal Q16 31 ∧
    matEntriesIn (fun x => x = -1 ∨ x = 1 ∨ x = 4) Q16 ∧
    matEntriesIn isDoubledE2M1 Q16 := by
  have horth : isOrthogonal Q16 31 := by
    unfold Q16
    have h := (skewConference_e2m1_orthogonal (2 * 8) C16 4 C16_skew C16_conf).1
    exact h
  have hentries : matEntriesIn (fun x => x = -1 ∨ x = 1 ∨ x = 4) Q16 := by
    intro i j
    simp only [Q16, addMat, scaleMat, idMat]
    by_cases hij : i = j
    · subst hij
      simp [C16_diag i]
    · simp only [hij, ↓reduceIte, Int.mul_zero, Int.zero_add]
      rcases C16_offdiag i j hij with h | h <;> simp [h]
  refine ⟨horth, hentries, ?_⟩
  intro i j
  rcases hentries i j with h | h | h <;> simp [h, isDoubledE2M1]

/-! ### Part 5: Universal Doubly-2:4-Sparse E2M1-Native Givens–Hadamard Family -/

theorem G4_1_2_orthogonal : isOrthogonal G4_1_2 5 := by
  funext i j; revert i j; decide

theorem G4_1_2_24_rows : ∀ i : Fin 4,
    nzCount4 (G4_1_2 i ⟨0, by omega⟩) (G4_1_2 i ⟨1, by omega⟩)
             (G4_1_2 i ⟨2, by omega⟩) (G4_1_2 i ⟨3, by omega⟩) ≤ 2 := by
  decide

theorem G4_1_2_24_cols : ∀ i : Fin 4,
    nzCount4 (transpose G4_1_2 i ⟨0, by omega⟩) (transpose G4_1_2 i ⟨1, by omega⟩)
             (transpose G4_1_2 i ⟨2, by omega⟩) (transpose G4_1_2 i ⟨3, by omega⟩) ≤ 2 := by
  decide

theorem G4_1_2_e2m1 : matEntriesIn isDoubledE2M1 G4_1_2 := by
  intro i j; unfold isDoubledE2M1; revert i j; decide

/-- Theorem 5 (Universal Doubly-2:4-Sparse E2M1-Native Givens–Hadamard Family):
    For every `k : Nat`, `G_{4 * 2^k}(1, 2) = H_{2^k} ⊗ G_4(1, 2)` is doubly-2:4-sparse,
    E2M1-native (entries in `{0, ±1, ±2} ⊂ 2*E2M1`), and exact orthogonal with
    `G^T G = (5 * 2^k) I`. -/
theorem g4k_doubly24_e2m1_orthogonal (k : Nat) :
    let G := kron (walshHadamard k) G4_1_2
    isDoubly24Sparse G ∧
    matEntriesIn isDoubledE2M1 G ∧
    isOrthogonal G (5 * ((2 ^ k : Nat) : Int)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact kron_isDoubly24Sparse (walshHadamard k) G4_1_2 G4_1_2_24_rows G4_1_2_24_cols
  · exact kron_matEntriesIn_e2m1 (walshHadamard_ternary k) G4_1_2_e2m1
  · have h := kron_isOrthogonal (walshHadamard_orthogonal k) G4_1_2_orthogonal
    rw [Int.mul_comm] at h
    exact h

end SparseE2M1Rotations
