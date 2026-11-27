/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MlaKantorovichRope.RatOrder

/-!
# Theorems 1 & 2: Kantorovich Bilinear Spectral Leakage & `GL(d_c)` Absorbed-KV Invariance

Pure-`Init` (zero Mathlib, zero `native_decide`) proofs of:
1. `kantorovich_bilinear_spectral_leakage_exact`: universal Kantorovich bound `(κ + 1/κ)^2 / 4`
   on bilinear unbalanced quantization error, exact 2-level attainment witness, universal Cauchy-Schwarz
   lower bound on diagonal balancing, exact leakage elimination at `D_j^2 = w_j / γ_j`, and exact
   rational evaluations for `κ ∈ {1, 2, 4, 8, 16, 32, 64}`.
2. `absorbed_kv_gl_invariance_exact`: universal `GL(d_c)` invariance of absorbed-KV attention logits
   `q^T W_UQ^T (W_UK M^{-1}) (M c_KV) = q^T W_UQ^T W_UK c_KV`, and exact specialization to
   orthogonal-diagonal Kantorovich-Hadamard preconditioning `M = U D`, `M^{-1} = D^{-1} U^T`.
-/

namespace MlaKantorovichRope

/-! ### Matrix algebra helpers for `GL(d_c)` invariance -/

theorem dot_matVec_transpose {m n : Nat} (A : Fin m → Fin n → Rat)
    (u : Fin m → Rat) (v : Fin n → Rat) :
    dot (matVec (matTranspose A) u) v = dot u (matVec A v) := by
  unfold dot matVec matTranspose
  have h1 : finSum n (fun j => finSum m (fun i => A i j * u i) * v j) =
      finSum n (fun j => finSum m (fun i => u i * (A i j * v j))) := by
    apply finSum_congr; intro j
    rw [← finSum_mul_const]
    apply finSum_congr; intro i
    grind
  have h2 : finSum m (fun i => u i * finSum n (fun j => A i j * v j)) =
      finSum m (fun i => finSum n (fun j => u i * (A i j * v j))) := by
    apply finSum_congr; intro i
    rw [← finSum_const_mul]
  rw [h1, h2, finSum_swap]

theorem matVec_matMul {m k n : Nat} (A : Fin m → Fin k → Rat) (B : Fin k → Fin n → Rat)
    (x : Fin n → Rat) :
    matVec (matMul A B) x = matVec A (matVec B x) := by
  funext i
  unfold matVec matMul
  have h1 : finSum n (fun j => finSum k (fun r => A i r * B r j) * x j) =
      finSum n (fun j => finSum k (fun r => A i r * (B r j * x j))) := by
    apply finSum_congr; intro j
    rw [← finSum_mul_const]
    apply finSum_congr; intro r
    grind
  have h2 : finSum k (fun r => A i r * finSum n (fun j => B r j * x j)) =
      finSum k (fun r => finSum n (fun j => A i r * (B r j * x j))) := by
    apply finSum_congr; intro r
    rw [← finSum_const_mul]
  rw [h1, h2, finSum_swap]

theorem matVec_matId {n : Nat} (x : Fin n → Rat) :
    matVec (matId n) x = x := by
  funext i
  unfold matVec matId
  have h : finSum n (fun j => (if i = j then (1 : Rat) else 0) * x j) =
      finSum n (fun j => if i = j then x j else 0) := by
    apply finSum_congr; intro j
    by_cases hij : i = j
    · simp [hij]
    · simp [hij]
  rw [h, finSum_ite_eq_right]

theorem matMul_assoc {m k p n : Nat} (A : Fin m → Fin k → Rat)
    (B : Fin k → Fin p → Rat) (C : Fin p → Fin n → Rat) :
    matMul (matMul A B) C = matMul A (matMul B C) := by
  funext i j
  unfold matMul
  have h1 : finSum p (fun r => finSum k (fun t => A i t * B t r) * C r j) =
      finSum p (fun r => finSum k (fun t => A i t * (B t r * C r j))) := by
    apply finSum_congr; intro r
    rw [← finSum_mul_const]
    apply finSum_congr; intro t
    grind
  have h2 : finSum k (fun t => A i t * finSum p (fun r => B t r * C r j)) =
      finSum k (fun t => finSum p (fun r => A i t * (B t r * C r j))) := by
    apply finSum_congr; intro t
    rw [← finSum_const_mul]
  rw [h1, h2, finSum_swap]

theorem matMul_matId_right {m n : Nat} (A : Fin m → Fin n → Rat) :
    matMul A (matId n) = A := by
  funext i j
  unfold matMul matId
  have h : finSum n (fun r => A i r * (if r = j then (1 : Rat) else 0)) =
      finSum n (fun r => if r = j then A i r else 0) := by
    apply finSum_congr; intro r
    by_cases hrj : r = j
    · simp [hrj]
    · simp [hrj]
  rw [h, finSum_ite_eq]

theorem matMul_matId_left {m n : Nat} (A : Fin m → Fin n → Rat) :
    matMul (matId m) A = A := by
  funext i j
  unfold matMul matId
  have h : finSum m (fun r => (if i = r then (1 : Rat) else 0) * A r j) =
      finSum m (fun r => if i = r then A r j else 0) := by
    apply finSum_congr; intro r
    by_cases hir : i = r
    · simp [hir]
    · simp [hir]
  rw [h, finSum_ite_eq_right]

theorem diagInv_mul_diagMat {n : Nat} (d : Fin n → Rat) (hd : ∀ j, d j ≠ 0) :
    matMul (diagInv d) (diagMat d) = matId n := by
  funext i j
  unfold matMul diagInv diagMat matId
  have h : finSum n (fun r => (if i = r then (d i)⁻¹ else 0) * (if r = j then d r else 0)) =
      finSum n (fun r => if i = r then (if r = j then (d i)⁻¹ * d r else 0) else 0) := by
    apply finSum_congr; intro r
    by_cases hir : i = r
    · by_cases hrj : r = j <;> simp [hir, hrj]
    · simp [hir]
  rw [h, finSum_ite_eq_right]
  by_cases hij : i = j
  · simp [hij, Rat.inv_mul_cancel (d j) (hd j)]
  · simp [hij]

theorem orthogonal_diag_left_inverse {n : Nat} (U : Fin n → Fin n → Rat) (d : Fin n → Rat)
    (hU : isOrthogonal U) (hd : ∀ j, d j ≠ 0) :
    isLeftInverse (matMul (diagInv d) (matTranspose U)) (matMul U (diagMat d)) := by
  unfold isLeftInverse
  rw [matMul_assoc, ← matMul_assoc (matTranspose U) U (diagMat d)]
  unfold isOrthogonal at hU
  rw [hU, matMul_matId_left, diagInv_mul_diagMat d hd]

theorem gl_absorbed_logit_invariant {d_h d_c : Nat}
    (W_UK : Fin d_h → Fin d_c → Rat)
    (M M_inv : Fin d_c → Fin d_c → Rat)
    (hinv : isLeftInverse M_inv M)
    (q : Fin d_h → Rat) (c : Fin d_c → Rat) :
    dot (matVec (matTranspose (matMul W_UK M_inv)) q) (matVec M c) =
      dot (matVec (matTranspose W_UK) q) c := by
  rw [dot_matVec_transpose, dot_matVec_transpose]
  rw [← matVec_matMul, matMul_assoc]
  unfold isLeftInverse at hinv
  rw [hinv, matMul_matId_right]

/-- Theorem 2 (Universal Exact `GL(d_c)` Absorbed-KV Invariance):
    Proves that absorbing `M^{-1}` into `W_UK' = W_UK M^{-1}` and `c' = M c` preserves exact
    attention logits for any invertible `M ∈ GL(d_c)` (both directly and with `q = W_UQ q_0`),
    and specializes to zero-FLOP orthogonal-diagonal Kantorovich-Hadamard preconditioning
    `M = U D`, `M^{-1} = D^{-1} U^T`. -/
theorem absorbed_kv_gl_invariance_exact :
    (∀ (d_h d_c : Nat) (W_UK : Fin d_h → Fin d_c → Rat)
       (M M_inv : Fin d_c → Fin d_c → Rat) (q : Fin d_h → Rat) (c : Fin d_c → Rat),
      isLeftInverse M_inv M →
      dot (matVec (matTranspose (matMul W_UK M_inv)) q) (matVec M c) =
        dot (matVec (matTranspose W_UK) q) c) ∧
    (∀ (d_q d_h d_c : Nat) (W_UQ : Fin d_h → Fin d_q → Rat)
       (W_UK : Fin d_h → Fin d_c → Rat)
       (M M_inv : Fin d_c → Fin d_c → Rat) (q0 : Fin d_q → Rat) (c : Fin d_c → Rat),
      isLeftInverse M_inv M →
      dot (matVec (matTranspose (matMul W_UK M_inv)) (matVec W_UQ q0)) (matVec M c) =
        dot (matVec (matTranspose W_UK) (matVec W_UQ q0)) c) ∧
    (∀ (d_h d_c : Nat) (W_UK : Fin d_h → Fin d_c → Rat)
       (U : Fin d_c → Fin d_c → Rat) (d : Fin d_c → Rat)
       (q : Fin d_h → Rat) (c : Fin d_c → Rat),
      isOrthogonal U → (∀ j, d j ≠ 0) →
      isLeftInverse (matMul (diagInv d) (matTranspose U)) (matMul U (diagMat d)) ∧
      dot (matVec (matTranspose (matMul W_UK (matMul (diagInv d) (matTranspose U)))) q)
          (matVec (matMul U (diagMat d)) c) =
        dot (matVec (matTranspose W_UK) q) c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d_h d_c W_UK M M_inv q c hinv
    exact gl_absorbed_logit_invariant W_UK M M_inv hinv q c
  · intro d_q d_h d_c W_UQ W_UK M M_inv q0 c hinv
    exact gl_absorbed_logit_invariant W_UK M M_inv hinv (matVec W_UQ q0) c
  · intro d_h d_c W_UK U d q c hU hd
    have hinv := orthogonal_diag_left_inverse U d hU hd
    exact ⟨hinv, gl_absorbed_logit_invariant W_UK _ _ hinv q c⟩

/-! ### Theorem 1: Kantorovich Bilinear Spectral Leakage & Diagonal Balancing -/

/-- Elementary AM-GM in `Rat`: `4 * a * b ≤ (a + b)^2`. -/
theorem rat_four_mul_le_sq_add (a b : Rat) : 4 * a * b ≤ (a + b) * (a + b) := by
  apply rat_le_of_sub_nonneg
  have eq : (a + b) * (a + b) - 4 * a * b = (a - b) * (a - b) := by grind
  rw [eq]
  exact rat_sq_nonneg (a - b)

/-- Pointwise Kantorovich envelope: for `0 < m ≤ x ≤ M`, `x + m * M / x ≤ m + M`. -/
theorem kantorovich_pointwise {m M x : Rat} (_hm : 0 < m) (hx : 0 < x)
    (hl : m ≤ x) (hu : x ≤ M) :
    x + m * M / x ≤ m + M := by
  have h1 : (0 : Rat) ≤ x - m := rat_sub_nonneg hl
  have h2 : (0 : Rat) ≤ M - x := rat_sub_nonneg hu
  have hprod : (0 : Rat) ≤ (M - x) * (x - m) := Rat.mul_nonneg h2 h1
  have hdiv : (0 : Rat) ≤ ((M - x) * (x - m)) / x := rat_div_nonneg hprod hx
  have hxne : x ≠ 0 := Rat.ne_of_gt hx
  have heq : (m + M) - (x + m * M / x) = ((M - x) * (x - m)) / x := by
    have hmul : ((m + M) - (x + m * M / x)) * x = (M - x) * (x - m) := by
      have hdivc : (m * M / x) * x = m * M := rat_div_mul_cancel hxne
      have hdist : ((m + M) - (x + m * M / x)) * x = (m + M) * x - x * x - (m * M / x) * x := by grind
      rw [hdist, hdivc]
      grind
    rw [← hmul, rat_mul_div_cancel hxne]
  apply rat_le_of_sub_nonneg
  rw [heq]
  exact hdiv

/-- Universal Kantorovich inequality in bilinear absorbed-MLA form:
    If `0 < σmin ≤ σmax`, `κ = σmax / σmin`, and `σmin^2 ≤ w_j / γ_j ≤ σmax^2` for all `j`,
    then `(∑ w_j^2)(∑ γ_j^2) ≤ ((κ + κ^{-1})^2 / 4) * (∑ w_j γ_j)^2`. -/
theorem kantorovich_bilinear_universal {n : Nat} (σmin σmax : Rat)
    (w γ : Fin n → Rat)
    (hmin : 0 < σmin) (hminmax : σmin ≤ σmax)
    (hw : ∀ j, 0 < w j) (hγ : ∀ j, 0 < γ j)
    (hlo : ∀ j, σmin * σmin ≤ w j / γ j)
    (hhi : ∀ j, w j / γ j ≤ σmax * σmax) :
    unbalancedCost w γ ≤
      kantorovichFactor (σmax / σmin) *
        (finSum n (fun j => w j * γ j) * finSum n (fun j => w j * γ j)) := by
  let m : Rat := σmin * σmin
  let M : Rat := σmax * σmax
  have hm : 0 < m := rat_mul_pos hmin hmin
  have hmax : 0 < σmax := rat_lt_of_lt_of_le hmin hminmax
  have hM : 0 < M := rat_mul_pos hmax hmax
  let A : Rat := finSum n (fun j => w j * w j)
  let B : Rat := finSum n (fun j => γ j * γ j)
  let S : Rat := finSum n (fun j => w j * γ j)
  -- Step 1: A + m * M * B ≤ (m + M) * S
  have hlin : A + m * M * B ≤ (m + M) * S := by
    have hsum_lhs : A + m * M * B =
        finSum n (fun j => w j * w j + (m * M) * (γ j * γ j)) := by
      dsimp only [A, B]
      rw [finSum_add, finSum_const_mul]
    have hsum_rhs : (m + M) * S =
        finSum n (fun j => (m + M) * (w j * γ j)) := by
      dsimp only [S]
      rw [finSum_const_mul]
    rw [hsum_lhs, hsum_rhs]
    apply finSum_le_finSum
    intro j
    have hwj : 0 < w j := hw j
    have hγj : 0 < γ j := hγ j
    have hxj : 0 < w j / γ j := rat_div_pos hwj hγj
    have hpt := kantorovich_pointwise hm hxj (hlo j) (hhi j)
    have hpj : 0 ≤ w j * γ j := Rat.le_of_lt (rat_mul_pos hwj hγj)
    have hmul := rat_mul_le_mul_of_nonneg_right hpt hpj
    have hwne : w j ≠ 0 := Rat.ne_of_gt hwj
    have hγne : γ j ≠ 0 := Rat.ne_of_gt hγj
    have hlhs : (w j / γ j + m * M / (w j / γ j)) * (w j * γ j) =
        w j * w j + m * M * (γ j * γ j) := by
      have h1 : (w j / γ j) * (w j * γ j) = w j * w j := by
        rw [Rat.mul_comm (w j) (γ j), ← Rat.mul_assoc, rat_div_mul_cancel hγne]
      have h2 : (m * M / (w j / γ j)) * (w j * γ j) = m * M * (γ j * γ j) := by
        have hinv : (w j / γ j)⁻¹ = γ j / w j := rat_div_inv hwne hγne
        rw [Rat.div_def (m * M), hinv]
        have hstep : (γ j / w j) * (w j * γ j) = γ j * γ j := by
          rw [← Rat.mul_assoc, rat_div_mul_cancel hwne]
        rw [Rat.mul_assoc, hstep]
      have hdist : (w j / γ j + m * M / (w j / γ j)) * (w j * γ j) =
          (w j / γ j) * (w j * γ j) + (m * M / (w j / γ j)) * (w j * γ j) := by grind
      rw [hdist, h1, h2]
    rw [hlhs] at hmul
    exact hmul
  -- Step 2: 0 ≤ A + m * M * B
  have hA0 : 0 ≤ A := finSum_nonneg (fun j => rat_sq_nonneg (w j))
  have hB0 : 0 ≤ B := finSum_nonneg (fun j => rat_sq_nonneg (γ j))
  have hAB0 : 0 ≤ A + m * M * B := rat_add_nonneg hA0 (Rat.mul_nonneg (Rat.le_of_lt (rat_mul_pos hm hM)) hB0)
  have hS0 : 0 ≤ (m + M) * S := Rat.le_trans hAB0 hlin
  -- Step 3: 4 * m * M * (A * B) ≤ (A + m * M * B)^2 ≤ ((m + M) * S)^2
  have hamgm : 4 * A * (m * M * B) ≤ (A + m * M * B) * (A + m * M * B) :=
    rat_four_mul_le_sq_add A (m * M * B)
  have hsq : (A + m * M * B) * (A + m * M * B) ≤ ((m + M) * S) * ((m + M) * S) := by
    have h1 := rat_mul_le_mul_of_nonneg_right hlin hAB0
    have h2 := rat_mul_le_mul_of_nonneg_left hlin hS0
    exact Rat.le_trans h1 h2
  have hchain : 4 * m * M * (A * B) ≤ (m + M) * (m + M) * (S * S) := by
    have h1 : 4 * m * M * (A * B) = 4 * A * (m * M * B) := by grind
    have h2 : ((m + M) * S) * ((m + M) * S) = (m + M) * (m + M) * (S * S) := by grind
    rw [h1, ← h2]
    exact Rat.le_trans hamgm hsq
  -- Step 4: Divide by 4 * m * M > 0 and identify (m + M)^2 / (4 m M) = kantorovichFactor (σmax / σmin)
  have h4mM : 0 < 4 * m * M := rat_mul_pos (rat_mul_pos (by decide) hm) hM
  have h4mM_ne : 4 * m * M ≠ 0 := Rat.ne_of_gt h4mM
  have hdiv := rat_div_le_div_of_pos_right hchain h4mM
  have hlhs_simp : (4 * m * M * (A * B)) / (4 * m * M) = A * B := by
    rw [Rat.mul_comm (4 * m * M), rat_mul_div_cancel h4mM_ne]
  rw [hlhs_simp] at hdiv
  have hfactor : ((m + M) * (m + M) * (S * S)) / (4 * m * M) =
      kantorovichFactor (σmax / σmin) * (S * S) := by
    unfold kantorovichFactor
    have hmin_ne : σmin ≠ 0 := Rat.ne_of_gt hmin
    have hmax_ne : σmax ≠ 0 := Rat.ne_of_gt hmax
    have hinv_k : (σmax / σmin)⁻¹ = σmin / σmax := rat_div_inv hmax_ne hmin_ne
    rw [hinv_k]
    have hsum_k : σmax / σmin + σmin / σmax = (m + M) / (σmin * σmax) := by
      have hmul_eq : (σmax / σmin + σmin / σmax) * (σmin * σmax) = m + M := by
        have h1 : (σmax / σmin) * (σmin * σmax) = σmax * σmax := by
          rw [← Rat.mul_assoc, rat_div_mul_cancel hmin_ne]
        have h2 : (σmin / σmax) * (σmin * σmax) = σmin * σmin := by
          rw [Rat.mul_comm σmin σmax, ← Rat.mul_assoc, rat_div_mul_cancel hmax_ne]
        have hd : (σmax / σmin + σmin / σmax) * (σmin * σmax) =
            (σmax / σmin) * (σmin * σmax) + (σmin / σmax) * (σmin * σmax) := by grind
        rw [hd, h1, h2]
        dsimp only [m, M]
        grind
      have hsm_ne : σmin * σmax ≠ 0 := Rat.ne_of_gt (rat_mul_pos hmin hmax)
      rw [← hmul_eq, rat_mul_div_cancel hsm_ne]
    rw [hsum_k]
    -- Both sides equal ((m + M)^2 / (4 * m * M)) * (S * S)
    have hsm_ne : σmin * σmax ≠ 0 := Rat.ne_of_gt (rat_mul_pos hmin hmax)
    have hsq_div : ((m + M) / (σmin * σmax)) * ((m + M) / (σmin * σmax)) =
        ((m + M) * (m + M)) / (m * M) := by
      have hprod : ((m + M) / (σmin * σmax)) * ((m + M) / (σmin * σmax)) * (m * M) =
          (m + M) * (m + M) := by
        have hmM_eq : m * M = (σmin * σmax) * (σmin * σmax) := by
          dsimp only [m, M]; grind
        rw [hmM_eq]
        have hre : ((m + M) / (σmin * σmax)) * ((m + M) / (σmin * σmax)) *
            ((σmin * σmax) * (σmin * σmax)) =
            (((m + M) / (σmin * σmax)) * (σmin * σmax)) *
            (((m + M) / (σmin * σmax)) * (σmin * σmax)) := by grind
        rw [hre, rat_div_mul_cancel hsm_ne]
      have hmM_ne : m * M ≠ 0 := Rat.ne_of_gt (rat_mul_pos hm hM)
      rw [← hprod, rat_mul_div_cancel hmM_ne]
    rw [hsq_div]
    have hdiv4 : (((m + M) * (m + M)) / (m * M)) / 4 = ((m + M) * (m + M)) / (4 * m * M) := by
      rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.mul_assoc]
      have hmM_ne : m * M ≠ 0 := Rat.ne_of_gt (rat_mul_pos hm hM)
      have hinv4 : (m * M)⁻¹ * (4 : Rat)⁻¹ = (4 * m * M)⁻¹ := by
        rw [← rat_mul_inv hmM_ne (by decide)]
        congr 1; grind
      rw [hinv4]
    rw [hdiv4]
    rw [Rat.div_def, Rat.div_def]
    grind
  rw [hfactor] at hdiv
  exact hdiv

/-- Exact 2-level attainment witness for Kantorovich's inequality. -/
theorem kantorovich_two_level_attainment (σmin σmax : Rat)
    (hmin : 0 < σmin) (hmax : 0 < σmax) :
    unbalancedCost (twoLevelW σmin σmax) (twoLevelGamma σmin σmax) =
      kantorovichFactor (σmax / σmin) *
        (finSum 2 (fun j => twoLevelW σmin σmax j * twoLevelGamma σmin σmax j) *
         finSum 2 (fun j => twoLevelW σmin σmax j * twoLevelGamma σmin σmax j)) := by
  have hmin_ne : σmin ≠ 0 := Rat.ne_of_gt hmin
  have hmax_ne : σmax ≠ 0 := Rat.ne_of_gt hmax
  unfold unbalancedCost kantorovichFactor twoLevelW twoLevelGamma
  simp only [finSum, ↓reduceIte, Nat.one_ne_zero]
  have hinv1 : σmin * σmin⁻¹ = 1 := Rat.mul_inv_cancel σmin hmin_ne
  have hinv2 : σmax * σmax⁻¹ = 1 := Rat.mul_inv_cancel σmax hmax_ne
  rw [hinv1, hinv2]
  have hinv_k : (σmax / σmin)⁻¹ = σmin / σmax := rat_div_inv hmax_ne hmin_ne
  rw [hinv_k]
  have hmul_lhs : (0 + σmin * σmin + σmax * σmax) * (0 + σmin⁻¹ * σmin⁻¹ + σmax⁻¹ * σmax⁻¹) =
      (σmax / σmin + σmin / σmax) * (σmax / σmin + σmin / σmax) := by
    have hsq1 : σmin * σmin * (σmin⁻¹ * σmin⁻¹) = 1 := by
      have : σmin * σmin * (σmin⁻¹ * σmin⁻¹) = (σmin * σmin⁻¹) * (σmin * σmin⁻¹) := by grind
      rw [this, hinv1]; grind
    have hsq2 : σmax * σmax * (σmax⁻¹ * σmax⁻¹) = 1 := by
      have : σmax * σmax * (σmax⁻¹ * σmax⁻¹) = (σmax * σmax⁻¹) * (σmax * σmax⁻¹) := by grind
      rw [this, hinv2]; grind
    have hcross1 : σmax * σmax * (σmin⁻¹ * σmin⁻¹) = (σmax / σmin) * (σmax / σmin) := by
      rw [Rat.div_def]; grind
    have hcross2 : σmin * σmin * (σmax⁻¹ * σmax⁻¹) = (σmin / σmax) * (σmin / σmax) := by
      rw [Rat.div_def]; grind
    have hprod_k : (σmax / σmin) * (σmin / σmax) = 1 := by
      rw [Rat.div_def, Rat.div_def]
      have : σmax * σmin⁻¹ * (σmin * σmax⁻¹) = (σmax * σmax⁻¹) * (σmin⁻¹ * σmin) := by grind
      rw [this, hinv2, Rat.inv_mul_cancel σmin hmin_ne]; grind
    have hexp1 : (0 + σmin * σmin + σmax * σmax) * (0 + σmin⁻¹ * σmin⁻¹ + σmax⁻¹ * σmax⁻¹) =
        σmin * σmin * (σmin⁻¹ * σmin⁻¹) + σmax * σmax * (σmax⁻¹ * σmax⁻¹) +
        σmax * σmax * (σmin⁻¹ * σmin⁻¹) + σmin * σmin * (σmax⁻¹ * σmax⁻¹) := by grind
    have hexp2 : (σmax / σmin + σmin / σmax) * (σmax / σmin + σmin / σmax) =
        (σmax / σmin) * (σmax / σmin) + (σmin / σmax) * (σmin / σmax) +
        2 * ((σmax / σmin) * (σmin / σmax)) := by grind
    rw [hexp1, hexp2, hsq1, hsq2, hcross1, hcross2, hprod_k]
    grind
  rw [hmul_lhs]
  have h22 : ((0 : Rat) + 1 + 1) * (0 + 1 + 1) = 4 := by grind
  rw [h22, rat_div_mul_cancel (by decide)]

/-- Universal lower bound on diagonal balancing (Cauchy-Schwarz) and exact attainment
    at `dSq j = w j / γ j` (`D_j = √(w_j / γ_j)`). -/
theorem kantorovich_diagonal_balancing_optimal {n : Nat} (w γ dSq : Fin n → Rat)
    (hw : ∀ j, 0 < w j) (hγ : ∀ j, 0 < γ j) (hd : ∀ j, 0 < dSq j) :
    finSum n (fun j => w j * γ j) * finSum n (fun j => w j * γ j) ≤
      bilinearWeightedCost w γ dSq ∧
    bilinearWeightedCost w γ (fun j => w j / γ j) =
      finSum n (fun j => w j * γ j) * finSum n (fun j => w j * γ j) := by
  constructor
  · -- Prove by Lagrange-like identity: ∑_i ∑_j (w_i^2 / d_i) * (d_j * γ_j^2) ...
    -- Even cleaner: write a_j = w_j / d_j, b_j = d_j * γ_j is not rational if d_j = √dSq_j.
    -- Directly prove: ∑_i ∑_j dSq_i dSq_j (w_i γ_j / dSq_i - w_j γ_i / dSq_j)^2 ≥ 0!
    -- (w_i γ_j * dSq_j - w_j γ_i * dSq_i)^2 / (dSq_i * dSq_j)
    -- = (w_i^2 / dSq_i) * (dSq_j * γ_j^2) + (w_j^2 / dSq_j) * (dSq_i * γ_i^2) - 2 (w_i γ_i)(w_j γ_j)
    have hnonneg : (0 : Rat) ≤
        finSum n (fun i => finSum n (fun j =>
          ((w i * γ j * dSq j - w j * γ i * dSq i) *
           (w i * γ j * dSq j - w j * γ i * dSq i)) / (dSq i * dSq j))) := by
      apply finSum_nonneg; intro i
      apply finSum_nonneg; intro j
      exact rat_div_nonneg (rat_sq_nonneg _) (rat_mul_pos (hd i) (hd j))
    have hident :
        finSum n (fun i => finSum n (fun j =>
          ((w i * γ j * dSq j - w j * γ i * dSq i) *
           (w i * γ j * dSq j - w j * γ i * dSq i)) / (dSq i * dSq j))) =
        2 * (bilinearWeightedCost w γ dSq -
             finSum n (fun j => w j * γ j) * finSum n (fun j => w j * γ j)) := by
      have hterm : ∀ i j : Fin n,
          ((w i * γ j * dSq j - w j * γ i * dSq i) *
           (w i * γ j * dSq j - w j * γ i * dSq i)) / (dSq i * dSq j) =
          (w i * w i / dSq i) * (dSq j * γ j * γ j) +
          (dSq i * γ i * γ i) * (w j * w j / dSq j) -
          2 * ((w i * γ i) * (w j * γ j)) := by
        intro i j
        have hdi : dSq i ≠ 0 := Rat.ne_of_gt (hd i)
        have hdj : dSq j ≠ 0 := Rat.ne_of_gt (hd j)
        have hdij : dSq i * dSq j ≠ 0 := Rat.ne_of_gt (rat_mul_pos (hd i) (hd j))
        have hmul :
            ((w i * w i / dSq i) * (dSq j * γ j * γ j) +
             (dSq i * γ i * γ i) * (w j * w j / dSq j) -
             2 * ((w i * γ i) * (w j * γ j))) * (dSq i * dSq j) =
            (w i * γ j * dSq j - w j * γ i * dSq i) *
            (w i * γ j * dSq j - w j * γ i * dSq i) := by
          have ht1 : (w i * w i / dSq i) * (dSq j * γ j * γ j) * (dSq i * dSq j) =
              (w i * w i) * (γ j * γ j) * (dSq j * dSq j) := by
            have hre : (w i * w i / dSq i) * (dSq j * γ j * γ j) * (dSq i * dSq j) =
                ((w i * w i / dSq i) * dSq i) * ((γ j * γ j) * (dSq j * dSq j)) := by grind
            rw [hre, rat_div_mul_cancel hdi]
            grind
          have ht2 : (dSq i * γ i * γ i) * (w j * w j / dSq j) * (dSq i * dSq j) =
              (w j * w j) * (γ i * γ i) * (dSq i * dSq i) := by
            have hre : (dSq i * γ i * γ i) * (w j * w j / dSq j) * (dSq i * dSq j) =
                ((w j * w j / dSq j) * dSq j) * ((γ i * γ i) * (dSq i * dSq i)) := by grind
            rw [hre, rat_div_mul_cancel hdj]
            grind
          have hdist : ((w i * w i / dSq i) * (dSq j * γ j * γ j) +
              (dSq i * γ i * γ i) * (w j * w j / dSq j) -
              2 * ((w i * γ i) * (w j * γ j))) * (dSq i * dSq j) =
              (w i * w i / dSq i) * (dSq j * γ j * γ j) * (dSq i * dSq j) +
              (dSq i * γ i * γ i) * (w j * w j / dSq j) * (dSq i * dSq j) -
              2 * ((w i * γ i) * (w j * γ j)) * (dSq i * dSq j) := by grind
          rw [hdist, ht1, ht2]
          grind
        rw [← hmul, rat_mul_div_cancel hdij]
      rw [finSum_congr (fun i => finSum_congr (fun j => hterm i j))]
      have hinner : ∀ i : Fin n,
          finSum n (fun j =>
            (w i * w i / dSq i) * (dSq j * γ j * γ j) +
            (dSq i * γ i * γ i) * (w j * w j / dSq j) -
            2 * ((w i * γ i) * (w j * γ j))) =
          (w i * w i / dSq i) * finSum n (fun j => dSq j * γ j * γ j) +
          (dSq i * γ i * γ i) * finSum n (fun j => w j * w j / dSq j) -
          2 * ((w i * γ i) * finSum n (fun j => w j * γ j)) := by
        intro i
        rw [finSum_sub, finSum_add, finSum_const_mul, finSum_const_mul, finSum_const_mul, finSum_const_mul]
      rw [finSum_congr hinner]
      rw [finSum_sub, finSum_add, finSum_mul_const, finSum_mul_const, finSum_const_mul, finSum_mul_const]
      unfold bilinearWeightedCost
      grind
    rw [hident] at hnonneg
    have hdiv := rat_div_nonneg hnonneg (by decide : (0 : Rat) < 2)
    have hsimp : (2 * (bilinearWeightedCost w γ dSq -
        finSum n (fun j => w j * γ j) * finSum n (fun j => w j * γ j))) / 2 =
        bilinearWeightedCost w γ dSq -
        finSum n (fun j => w j * γ j) * finSum n (fun j => w j * γ j) := by
      rw [Rat.mul_comm, rat_mul_div_cancel (by decide)]
    rw [hsimp] at hdiv
    exact rat_le_of_sub_nonneg hdiv
  · unfold bilinearWeightedCost
    have h1 : finSum n (fun j => w j * w j / (w j / γ j)) = finSum n (fun j => w j * γ j) := by
      apply finSum_congr; intro j
      have hwne : w j ≠ 0 := Rat.ne_of_gt (hw j)
      have hγne : γ j ≠ 0 := Rat.ne_of_gt (hγ j)
      have hinv : (w j / γ j)⁻¹ = γ j / w j := rat_div_inv hwne hγne
      rw [Rat.div_def (w j * w j), hinv]
      have hre : w j * w j * (γ j / w j) = w j * ((γ j / w j) * w j) := by grind
      rw [hre, rat_div_mul_cancel hwne]
    have h2 : finSum n (fun j => (w j / γ j) * γ j * γ j) = finSum n (fun j => w j * γ j) := by
      apply finSum_congr; intro j
      have hγne : γ j ≠ 0 := Rat.ne_of_gt (hγ j)
      rw [rat_div_mul_cancel hγne]
    rw [h1, h2]

/-- Theorem 1 (Exact Bilinear Kantorovich Spectral Leakage & Zero-FLOP Diagonal Balancing):
    Combines the universal Kantorovich upper bound `(κ + κ^{-1})^2 / 4`, exact 2-level attainment,
    universal Cauchy-Schwarz optimality of diagonal balancing `D_j^2 = w_j / γ_j`, and exact
    rational values for `κ ∈ {1, 2, 4, 8, 16, 32, 64}`. -/
theorem kantorovich_bilinear_spectral_leakage_exact :
    (∀ (n : Nat) (σmin σmax : Rat) (w γ : Fin n → Rat),
      0 < σmin → σmin ≤ σmax →
      (∀ j, 0 < w j) → (∀ j, 0 < γ j) →
      (∀ j, σmin * σmin ≤ w j / γ j) → (∀ j, w j / γ j ≤ σmax * σmax) →
      unbalancedCost w γ ≤
        kantorovichFactor (σmax / σmin) *
          (finSum n (fun j => w j * γ j) * finSum n (fun j => w j * γ j))) ∧
    (∀ (σmin σmax : Rat), 0 < σmin → 0 < σmax →
      unbalancedCost (twoLevelW σmin σmax) (twoLevelGamma σmin σmax) =
        kantorovichFactor (σmax / σmin) *
          (finSum 2 (fun j => twoLevelW σmin σmax j * twoLevelGamma σmin σmax j) *
           finSum 2 (fun j => twoLevelW σmin σmax j * twoLevelGamma σmin σmax j))) ∧
    (∀ (n : Nat) (w γ dSq : Fin n → Rat),
      (∀ j, 0 < w j) → (∀ j, 0 < γ j) → (∀ j, 0 < dSq j) →
      finSum n (fun j => w j * γ j) * finSum n (fun j => w j * γ j) ≤
        bilinearWeightedCost w γ dSq ∧
      bilinearWeightedCost w γ (fun j => w j / γ j) =
        finSum n (fun j => w j * γ j) * finSum n (fun j => w j * γ j)) ∧
    (kantorovichFactor 1 = 1 ∧
     kantorovichFactor 2 = 25 / 16 ∧
     kantorovichFactor 4 = 289 / 64 ∧
     kantorovichFactor 8 = 4225 / 256 ∧
     kantorovichFactor 16 = 66049 / 1024 ∧
     kantorovichFactor 32 = 1050625 / 4096 ∧
     kantorovichFactor 64 = 16785409 / 16384) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n σmin σmax w γ hmin hminmax hw hγ hlo hhi
    exact kantorovich_bilinear_universal σmin σmax w γ hmin hminmax hw hγ hlo hhi
  · intro σmin σmax hmin hmax
    exact kantorovich_two_level_attainment σmin σmax hmin hmax
  · intro n w γ dSq hw hγ hd
    exact kantorovich_diagonal_balancing_optimal w γ dSq hw hγ hd
  · unfold kantorovichFactor; grind

end MlaKantorovichRope
