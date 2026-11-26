/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mxfp6Ef21Rotations.RatOrder

/-!
# Hadamard Defects, Minimum Dyadic Coherence, Goethals–Seidel Native Orthonormal Matrices,
and Universal 4:8-Sparse Hamilton Quaternion Factorizations

Pure Lean 4 `Init` (zero Mathlib, zero `native_decide`) proofs of:
4. `hadamard_weight_quantization_defect_and_min_dyadic_coherence`
5. `goethals_seidel_native_e2m1_orthonormal_exact`
6. `quaternion_4of8_sparse_orthogonality_universal`
-/

namespace Mxfp6Ef21Rotations

/-! ### 1. Pure-`Init` Integer Matrix Algebra & Sparsity Helpers -/

theorem sumFinInt_congr {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i = g i) :
    sumFinInt n f = sumFinInt n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumFinInt]
    rw [ih (fun i => h i.castSucc), h (Fin.last n)]

theorem sumFinInt_zero (n : Nat) : sumFinInt n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumFinInt]
    rw [ih]; omega

theorem sumFinInt_add {n : Nat} (f g : Fin n → Int) :
    sumFinInt n (fun i => f i + g i) = sumFinInt n f + sumFinInt n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumFinInt]
    rw [ih]; omega

theorem sumFinInt_mul_left {n : Nat} (c : Int) (f : Fin n → Int) :
    sumFinInt n (fun i => c * f i) = c * sumFinInt n f := by
  induction n with
  | zero => simp [sumFinInt]
  | succ n ih =>
    simp only [sumFinInt]
    rw [ih, Int.mul_add]

theorem sumFinInt_mul_right {n : Nat} (f : Fin n → Int) (c : Int) :
    sumFinInt n (fun i => f i * c) = sumFinInt n f * c := by
  induction n with
  | zero => simp [sumFinInt]
  | succ n ih =>
    simp only [sumFinInt]
    rw [ih, Int.add_mul]

theorem sumFinInt_swap {m n : Nat} (f : Fin m → Fin n → Int) :
    sumFinInt m (fun i => sumFinInt n (fun j => f i j)) =
    sumFinInt n (fun j => sumFinInt m (fun i => f i j)) := by
  induction m with
  | zero =>
    simp only [sumFinInt]
    exact (sumFinInt_zero n).symm
  | succ m ih =>
    simp only [sumFinInt]
    rw [ih, ← sumFinInt_add]

theorem sumFinInt_single {n : Nat} (j : Fin n) (v : Int) :
    sumFinInt n (fun i => if i = j then v else 0) = v := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    simp only [sumFinInt]
    by_cases h : j = Fin.last n
    · subst h
      have hleft : sumFinInt n (fun i => if i.castSucc = Fin.last n then v else 0) = 0 := by
        rw [sumFinInt_congr (g := fun _ => 0)]
        · exact sumFinInt_zero n
        · intro i
          have hne : i.castSucc ≠ Fin.last n := by
            intro heq; have hv := congrArg Fin.val heq
            simp only [Fin.val_castSucc, Fin.val_last] at hv; omega
          simp [hne]
      rw [hleft]; simp
    · have hlt : j.val < n := by
        have := j.isLt
        have hne : j.val ≠ n := fun hv => h (Fin.ext hv)
        omega
      let j' : Fin n := ⟨j.val, hlt⟩
      have hleft : sumFinInt n (fun i => if i.castSucc = j then v else 0) =
          sumFinInt n (fun i => if i = j' then v else 0) := by
        apply sumFinInt_congr
        intro i
        have hiff : (i.castSucc = j) ↔ (i = j') := by
          constructor <;> intro heq <;> exact Fin.ext (by have := congrArg Fin.val heq; simpa [Fin.val_castSucc, j'] using this)
        simp only [hiff]
      have hlast : (if Fin.last n = j then v else 0) = 0 := by
        have : Fin.last n ≠ j := Ne.symm h
        simp [this]
      rw [hleft, hlast, ih j']; omega

theorem sumFinInt_single_right {n : Nat} (j : Fin n) (v : Int) :
    sumFinInt n (fun i => if j = i then v else 0) = v := by
  have hcongr : (fun i => if j = i then v else 0) = (fun i => if i = j then v else 0) := by
    funext i
    have hiff : (j = i) ↔ (i = j) := ⟨Eq.symm, Eq.symm⟩
    simp only [hiff]
  rw [hcongr]
  exact sumFinInt_single j v

theorem sumFinInt_cast {m n : Nat} (h : m = n) (f : Fin m → Int) :
    sumFinInt m f = sumFinInt n (fun i => f ⟨i.val, h ▸ i.isLt⟩) := by
  subst h; rfl

theorem sumFinInt_add_split (p q : Nat) (f : Fin (p + q) → Int) :
    sumFinInt (p + q) f =
      sumFinInt p (fun i => f ⟨i.val, by omega⟩) +
      sumFinInt q (fun j => f ⟨p + j.val, by omega⟩) := by
  induction q with
  | zero =>
    simp only [Nat.add_zero, sumFinInt, Int.add_zero]
    exact sumFinInt_congr (fun _ => rfl)
  | succ q ih =>
    have hstep : sumFinInt (p + (q + 1)) f =
        sumFinInt (p + q) (fun i => f ⟨i.val, by omega⟩) + f ⟨p + q, by omega⟩ := rfl
    rw [hstep, ih (fun i => f ⟨i.val, by omega⟩)]
    have hrhs : sumFinInt (q + 1) (fun j => f ⟨p + j.val, by omega⟩) =
        sumFinInt q (fun j => f ⟨p + j.val, by omega⟩) + f ⟨p + q, by omega⟩ := by
      simp only [sumFinInt]; rfl
    rw [hrhs, Int.add_assoc]

theorem sumFinInt_mul_prod (a b : Nat) (f : Fin (a * b) → Int) :
    sumFinInt (a * b) f =
    sumFinInt a (fun i => sumFinInt b (fun j => f ⟨i.val * b + j.val, by
      have hi := i.isLt; have hj := j.isLt
      have h1 : (i.val + 1) * b ≤ a * b := Nat.mul_le_mul_right b hi
      rw [Nat.add_mul, Nat.one_mul] at h1
      omega⟩)) := by
  induction a with
  | zero =>
    rw [sumFinInt_cast (Nat.zero_mul b)]; rfl
  | succ a ih =>
    have hmul : (a + 1) * b = a * b + b := by rw [Nat.add_mul, Nat.one_mul]
    rw [sumFinInt_cast hmul, sumFinInt_add_split (a * b) b, ih]
    simp only [sumFinInt]
    rfl

theorem matMul_assoc {m k l n : Nat} (A : IntMat m k) (B : IntMat k l) (C : IntMat l n) :
    matMul (matMul A B) C = matMul A (matMul B C) := by
  funext i j
  unfold matMul
  have h1 : sumFinInt l (fun s => sumFinInt k (fun t => A i t * B t s) * C s j) =
      sumFinInt l (fun s => sumFinInt k (fun t => A i t * B t s * C s j)) := by
    apply sumFinInt_congr; intro s; exact (sumFinInt_mul_right _ _).symm
  have h2 : sumFinInt k (fun t => A i t * sumFinInt l (fun s => B t s * C s j)) =
      sumFinInt k (fun t => sumFinInt l (fun s => A i t * (B t s * C s j))) := by
    apply sumFinInt_congr; intro t; exact (sumFinInt_mul_left _ _).symm
  rw [h1, h2, sumFinInt_swap]
  apply sumFinInt_congr; intro t
  apply sumFinInt_congr; intro s
  exact Int.mul_assoc (A i t) (B t s) (C s j)

theorem transpose_matMul {m k n : Nat} (A : IntMat m k) (B : IntMat k n) :
    transpose (matMul A B) = matMul (transpose B) (transpose A) := by
  funext i j
  unfold transpose matMul
  apply sumFinInt_congr; intro t
  exact Int.mul_comm (A j t) (B t i)

theorem matMul_id_left {m n : Nat} (A : IntMat m n) : matMul (idMat m) A = A := by
  funext i j
  unfold matMul idMat
  have hcongr : (fun t => (if i = t then (1 : Int) else 0) * A t j) =
      (fun t => if i = t then A i j else 0) := by
    funext t; by_cases h : i = t
    · subst h; simp
    · simp [h]
  rw [hcongr, sumFinInt_single_right]

theorem matMul_id_right {m n : Nat} (A : IntMat m n) : matMul A (idMat n) = A := by
  funext i j
  unfold matMul idMat
  have hcongr : (fun t => A i t * (if t = j then (1 : Int) else 0)) =
      (fun t => if t = j then A i j else 0) := by
    funext t; by_cases h : t = j
    · subst h; simp
    · simp [h]
  rw [hcongr, sumFinInt_single]

theorem matMul_scale_left {m k n : Nat} (c : Int) (A : IntMat m k) (B : IntMat k n) :
    matMul (scaleMat c A) B = scaleMat c (matMul A B) := by
  funext i j
  unfold matMul scaleMat
  rw [← sumFinInt_mul_left]
  apply sumFinInt_congr; intro t
  exact Int.mul_assoc c (A i t) (B t j)

theorem matMul_scale_right {m k n : Nat} (c : Int) (A : IntMat m k) (B : IntMat k n) :
    matMul A (scaleMat c B) = scaleMat c (matMul A B) := by
  funext i j
  unfold matMul scaleMat
  rw [← sumFinInt_mul_left]
  apply sumFinInt_congr; intro t
  grind

theorem isOrthogonal_id (n : Nat) : isOrthogonal (idMat n) 1 := by
  unfold isOrthogonal
  have ht : transpose (idMat n) = idMat n := by
    funext i j; unfold transpose idMat
    have hiff : (j = i) ↔ (i = j) := ⟨Eq.symm, Eq.symm⟩
    simp only [hiff]
  rw [ht, matMul_id_left]
  funext i j; unfold scaleMat; simp

theorem isOrthogonal_matMul {n : Nat} {A B : IntMat n n} {c1 c2 : Int}
    (hA : isOrthogonal A c1) (hB : isOrthogonal B c2) :
    isOrthogonal (matMul A B) (c1 * c2) := by
  unfold isOrthogonal at hA hB ⊢
  rw [transpose_matMul, matMul_assoc, ← matMul_assoc (transpose A) A B, hA,
      matMul_scale_left, matMul_id_left, matMul_scale_right, hB]
  funext i j; unfold scaleMat; exact (Int.mul_assoc c1 c2 _).symm

/-! ### 2. Theorem 4: Hadamard Weight-Quantization Defect & Minimum Dyadic Coherence -/

private theorem int_sq_ge_128_imp_abs_ge_12 (k : Int) (h : (128 : Int) ≤ k * k) :
    12 ≤ k.natAbs := by
  match Nat.lt_or_ge k.natAbs 12 with
  | .inr hge => exact hge
  | .inl hlt =>
    have hle : k.natAbs ≤ 11 := by omega
    have hsq : k * k = ((k.natAbs * k.natAbs : Nat) : Int) := by
      have := Int.natAbs_mul_self (a := k)
      exact this.symm
    have h121 : k.natAbs * k.natAbs ≤ 11 * 11 := Nat.mul_le_mul hle hle
    omega

private theorem rat_div_sq_ge_imp_int_sq {k : Int} {D N : Nat} (hD : 0 < D) (hN : 0 < N)
    (h : (1 : Rat) / (N : Rat) ≤ ((k : Rat) / (D : Rat)) * ((k : Rat) / (D : Rat))) :
    ((D * D : Nat) : Int) ≤ (N : Int) * (k * k) := by
  have hDpos : (0 : Rat) < (D : Rat) := rat_natCast_pos hD
  have hNpos : (0 : Rat) < (N : Rat) := rat_natCast_pos hN
  have hD2pos : (0 : Rat) < (D : Rat) * (D : Rat) := rat_mul_pos hDpos hDpos
  have hND2 : (0 : Rat) < (N : Rat) * ((D : Rat) * (D : Rat)) := rat_mul_pos hNpos hD2pos
  have hmul := rat_mul_le_mul_of_nonneg_right h (Rat.le_of_lt hND2)
  have hlhs : ((1 : Rat) / (N : Rat)) * ((N : Rat) * ((D : Rat) * (D : Rat))) = (D : Rat) * (D : Rat) := by
    rw [Rat.div_def, Rat.one_mul, ← Rat.mul_assoc, Rat.inv_mul_cancel _ (Rat.ne_of_gt hNpos), Rat.one_mul]
  have hrhs : (((k : Rat) / (D : Rat)) * ((k : Rat) / (D : Rat))) * ((N : Rat) * ((D : Rat) * (D : Rat))) =
      (N : Rat) * ((k : Rat) * (k : Rat)) := by
    have hDinv : (D : Rat)⁻¹ * (D : Rat) = 1 := Rat.inv_mul_cancel _ (Rat.ne_of_gt hDpos)
    rw [Rat.div_def]; grind
  rw [hlhs, hrhs] at hmul
  have hcastL : (D : Rat) * (D : Rat) = ((((D * D : Nat) : Int)) : Rat) := by
    simp only [Rat.intCast_natCast, Rat.natCast_mul]
  have hcastR : ((((N : Int) * (k * k)) : Int) : Rat) = (N : Rat) * ((k : Rat) * (k : Rat)) := by
    rw [Rat.intCast_mul, Rat.intCast_mul, Rat.intCast_natCast]
  rw [hcastL, ← hcastR] at hmul
  exact Rat.intCast_le_intCast.mp hmul

private theorem rat_mul_div_sq_eq {c a b p q : Rat} (hb : b ≠ 0) (hq : q ≠ 0)
    (h : c * (a * a) * q = p * (b * b)) : c * ((a / b) * (a / b)) = p / q := by
  have hb2 : b * b ≠ 0 := fun hx => by
    cases Rat.mul_eq_zero.mp hx with | inl h0 => exact hb h0 | inr h0 => exact hb h0
  have heq : c * ((a / b) * (a / b)) = (c * (a * a)) / (b * b) := by
    rw [Rat.div_def, Rat.div_def]
    have hinv : (b * b)⁻¹ = b⁻¹ * b⁻¹ := by
      have hmul : ((b * b)⁻¹ - b⁻¹ * b⁻¹) * (b * b) = 0 := by
        have h1 : b⁻¹ * b = 1 := Rat.inv_mul_cancel b hb
        have h2 : (b * b)⁻¹ * (b * b) = 1 := Rat.inv_mul_cancel (b * b) hb2
        grind
      cases Rat.mul_eq_zero.mp hmul with
      | inl h0 => grind
      | inr h0 => exact False.elim (hb2 h0)
    rw [hinv]; grind
  rw [heq]
  exact rat_div_eq_of_cross hb2 hq h

theorem hadamard_weight_quantization_defect_and_min_dyadic_coherence :
    (8 * ((3/8 : Rat) * (3/8)) = 9/8) ∧
    (8 * ((11/32 : Rat) * (11/32)) = 121/128) ∧
    (32 * ((3/16 : Rat) * (3/16)) = 9/8) ∧
    (32 * ((11/64 : Rat) * (11/64)) = 121/128) ∧
    (∀ k : Int, (1/8 : Rat) ≤ ((k : Rat) / 32) * ((k : Rat) / 32) → 12 ≤ k.natAbs) ∧
    (∀ k : Int, (1/32 : Rat) ≤ ((k : Rat) / 64) * ((k : Rat) / 64) → 12 ≤ k.natAbs) := by
  refine ⟨rat_mul_div_sq_eq (by decide) (by decide) (by grind),
          rat_mul_div_sq_eq (by decide) (by decide) (by grind),
          rat_mul_div_sq_eq (by decide) (by decide) (by grind),
          rat_mul_div_sq_eq (by decide) (by decide) (by grind), ?_, ?_⟩
  · intro k hk
    have h := rat_div_sq_ge_imp_int_sq (D := 32) (N := 8) (by decide) (by decide) hk
    apply int_sq_ge_128_imp_abs_ge_12
    omega
  · intro k hk
    have h := rat_div_sq_ge_imp_int_sq (D := 64) (N := 32) (by decide) (by decide) hk
    apply int_sq_ge_128_imp_abs_ge_12
    omega

/-! ### 3. Theorem 5: Exact Goethals–Seidel Native `E2M1`/`E3M2`/`E2M3` Orthonormal Matrices -/

/-- Block-level Goethals–Seidel orthogonality reduction: checking the `16` block products
    of `m × m` matrices reduces `4m × 4m` orthogonality to `m × m` checks! -/
private def gsBlock (m : Nat) (a b c d : Fin m → Int) (bi bj : Fin 4) : IntMat m m :=
  let A := circMat m a
  let B := circMat m b
  let C := circMat m c
  let D := circMat m d
  let BR := mulBackRev m B
  let CR := mulBackRev m C
  let DR := mulBackRev m D
  let BtR := mulBackRev m (transpose B)
  let CtR := mulBackRev m (transpose C)
  let DtR := mulBackRev m (transpose D)
  match bi.val, bj.val with
  | 0, 0 => A | 0, 1 => BR | 0, 2 => CR | 0, 3 => DR
  | 1, 0 => negMat BR | 1, 1 => A | 1, 2 => negMat DtR | 1, 3 => CtR
  | 2, 0 => negMat CR | 2, 1 => DtR | 2, 2 => A | 2, 3 => negMat BtR
  | 3, 0 => negMat DR | 3, 1 => negMat CtR | 3, 2 => BtR | _, _ => A

private theorem div_lt_four_of_lt_four_mul {m x : Nat} (h : x < 4 * m) : x / m < 4 := by
  have hm : 0 < m := by omega
  have h' : x < m * 4 := by rw [Nat.mul_comm]; exact h
  exact Nat.div_lt_of_lt_mul h'

private theorem goethalsSeidelMat_eq_gsBlock (m : Nat) (a b c d : Fin m → Int)
    (i j : Fin (4 * m)) :
    goethalsSeidelMat m a b c d i j =
    gsBlock m a b c d ⟨i.val / m, div_lt_four_of_lt_four_mul i.isLt⟩
      ⟨j.val / m, div_lt_four_of_lt_four_mul j.isLt⟩
      ⟨i.val % m, Nat.mod_lt _ (by have := i.isLt; omega)⟩
      ⟨j.val % m, Nat.mod_lt _ (by have := j.isLt; omega)⟩ := by
  unfold goethalsSeidelMat gsBlock negMat
  dsimp only
  have hi : i.val / m < 4 := div_lt_four_of_lt_four_mul i.isLt
  have hj : j.val / m < 4 := div_lt_four_of_lt_four_mul j.isLt
  generalize i.val / m = bi at hi ⊢
  generalize j.val / m = bj at hj ⊢
  match bi, bj with
  | 0, 0 | 0, 1 | 0, 2 | 0, 3
  | 1, 0 | 1, 1 | 1, 2 | 1, 3
  | 2, 0 | 2, 1 | 2, 2 | 2, 3
  | 3, 0 | 3, 1 | 3, 2 | 3, 3 => rfl
  | bi + 4, _ => omega
  | _, bj + 4 => omega

private theorem goethalsSeidel_isOrthogonal_of_blocks (m : Nat) (hm : 0 < m)
    (a b c d : Fin m → Int) (c_norm : Int)
    (hblk : ∀ bi bj : Fin 4, ∀ ri rj : Fin m,
      sumFinInt 4 (fun bt => matMul (transpose (gsBlock m a b c d bt bi))
        (gsBlock m a b c d bt bj) ri rj) =
      if bi = bj ∧ ri = rj then c_norm else 0) :
    isOrthogonal (goethalsSeidelMat m a b c d) c_norm := by
  funext i j
  unfold matMul transpose scaleMat idMat
  rw [sumFinInt_mul_prod 4 m]
  let bi : Fin 4 := ⟨i.val / m, div_lt_four_of_lt_four_mul i.isLt⟩
  let bj : Fin 4 := ⟨j.val / m, div_lt_four_of_lt_four_mul j.isLt⟩
  let ri : Fin m := ⟨i.val % m, Nat.mod_lt _ hm⟩
  let rj : Fin m := ⟨j.val % m, Nat.mod_lt _ hm⟩
  have hinner : sumFinInt 4 (fun bt => sumFinInt m (fun rt =>
      goethalsSeidelMat m a b c d ⟨bt.val * m + rt.val, by
        have h1 := bt.isLt; have h2 := rt.isLt
        have h3 : (bt.val + 1) * m ≤ 4 * m := Nat.mul_le_mul_right m h1
        rw [Nat.add_mul, Nat.one_mul] at h3; omega⟩ i *
      goethalsSeidelMat m a b c d ⟨bt.val * m + rt.val, by
        have h1 := bt.isLt; have h2 := rt.isLt
        have h3 : (bt.val + 1) * m ≤ 4 * m := Nat.mul_le_mul_right m h1
        rw [Nat.add_mul, Nat.one_mul] at h3; omega⟩ j)) =
      sumFinInt 4 (fun bt => matMul (transpose (gsBlock m a b c d bt bi))
        (gsBlock m a b c d bt bj) ri rj) := by
    apply sumFinInt_congr; intro bt
    unfold matMul transpose
    apply sumFinInt_congr; intro rt
    rw [goethalsSeidelMat_eq_gsBlock, goethalsSeidelMat_eq_gsBlock]
    have hdiv : (bt.val * m + rt.val) / m = bt.val := by
      rw [Nat.mul_comm, Nat.mul_add_div hm, Nat.div_eq_of_lt rt.isLt, Nat.add_zero]
    have hmod : (bt.val * m + rt.val) % m = rt.val := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt rt.isLt]
    have hbt : (⟨(bt.val * m + rt.val) / m, div_lt_four_of_lt_four_mul (by
        have h1 := bt.isLt; have h2 := rt.isLt
        have h3 : (bt.val + 1) * m ≤ 4 * m := Nat.mul_le_mul_right m h1
        rw [Nat.add_mul, Nat.one_mul] at h3; omega)⟩ : Fin 4) = bt := Fin.ext hdiv
    have hrt : (⟨(bt.val * m + rt.val) % m, Nat.mod_lt _ hm⟩ : Fin m) = rt := Fin.ext hmod
    rw [hbt, hrt]
  rw [hinner, hblk bi bj ri rj]
  have hiff : (bi = bj ∧ ri = rj) ↔ (i = j) := by
    constructor
    · intro ⟨h1, h2⟩
      apply Fin.ext
      have hd : i.val / m = j.val / m := congrArg Fin.val h1
      have hmo : i.val % m = j.val % m := congrArg Fin.val h2
      have hi_eq := (Nat.div_add_mod i.val m).symm
      rw [hd, hmo, Nat.div_add_mod] at hi_eq
      exact hi_eq
    · intro heq; subst heq; exact ⟨rfl, rfl⟩
  by_cases h : i = j
  · have h' : bi = bj ∧ ri = rj := hiff.mpr h
    simp only [h, h', and_self, ↓reduceIte, Int.mul_one]
  · have h' : ¬(bi = bj ∧ ri = rj) := fun hx => h (hiff.mp hx)
    simp only [h, h', ↓reduceIte, Int.mul_zero]

private theorem gs16_isOrthogonal : isOrthogonal GS_n16_E2M1_low 64 := by
  apply goethalsSeidel_isOrthogonal_of_blocks 4 (by decide) gs16_a gs16_b gs16_c gs16_d 64
  decide

private theorem gs32_isOrthogonal : isOrthogonal GS_n32_E2M1_pm13 64 := by
  apply goethalsSeidel_isOrthogonal_of_blocks 8 (by decide) gs32_a gs32_b gs32_c gs32_d 64
  decide

private theorem goethalsSeidel_entries_prop (m : Nat) (a b c d : Fin m → Int) (P : Int → Prop)
    (hneg : ∀ x, P x → P (-x))
    (ha : ∀ k, P (a k)) (hb : ∀ k, P (b k)) (hc : ∀ k, P (c k)) (hd : ∀ k, P (d k)) :
    ∀ i j, P (goethalsSeidelMat m a b c d i j) := by
  intro i j
  unfold goethalsSeidelMat circMat mulBackRev transpose
  dsimp only
  split
  · exact ha _
  · exact hb _
  · exact hc _
  · exact hd _
  · exact hneg _ (hb _)
  · exact ha _
  · exact hneg _ (hd _)
  · exact hc _
  · exact hneg _ (hc _)
  · exact hd _
  · exact ha _
  · exact hneg _ (hb _)
  · exact hneg _ (hd _)
  · exact hneg _ (hc _)
  · exact hb _
  · exact ha _

/-! #### Exact OCP `E2M1 ∩ E3M2 ∩ E2M3` Grid Membership for `±1/8, ±2/8, ±3/8` -/

private theorem inAllThreeOCPGrids_pos_nat (k : Nat) (hk : k = 1 ∨ k = 2 ∨ k = 3) :
    inAllThreeOCPGrids (((k : Nat) : Rat) / 8) := by
  have hx_nn : (0 : Rat) ≤ ((k : Nat) : Rat) / 8 := rat_div_nonneg_nat k 8 (by decide)
  have h4x_eq : (4 : Rat) * (((k : Nat) : Rat) / 8) = ((k : Nat) : Rat) / 2 := by
    have h8i : (8 : Rat) * (8 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 8 (by decide)
    have h2i : (2 : Rat) * (2 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 2 (by decide)
    have hmul : ((4 : Rat) * (((k : Nat) : Rat) / 8) - ((k : Nat) : Rat) / 2) * 8 = 0 := by
      rw [Rat.div_def, Rat.div_def]; grind
    cases Rat.mul_eq_zero.mp hmul with
    | inl h0 => grind
    | inr h0 => exact False.elim ((by decide : (8 : Rat) ≠ 0) h0)
  have h4x_nn : (0 : Rat) ≤ ((k : Nat) : Rat) / 2 := rat_div_nonneg_nat k 2 (by decide)
  unfold inAllThreeOCPGrids
  rw [h4x_eq, absRat_of_nonneg h4x_nn, absRat_of_nonneg hx_nn]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e2m1Levels_eq_map]
    exact List.mem_map.mpr ⟨k, by rcases hk with rfl | rfl | rfl <;> decide, rfl⟩
  · rw [e3m2Levels_eq_map]
    refine List.mem_map.mpr ⟨2 * k, by rcases hk with rfl | rfl | rfl <;> decide, ?_⟩
    rw [Rat.natCast_mul]
    exact rat_div_eq_of_cross (by decide) (by decide) (by grind)
  · rw [e2m3Levels_eq_map]
    exact List.mem_map.mpr ⟨k, by rcases hk with rfl | rfl | rfl <;> decide, rfl⟩
  · unfold e2m1Quant symQuant
    have hn : ¬(((k : Nat) : Rat) / 2 < 0) := Rat.not_lt.mpr h4x_nn
    simp only [hn, ↓reduceIte]
    rw [e2m1Levels_eq_map]
    have hq := nearestNonneg_map_div 2 k 2 (by decide) (by decide) e2m1Nums
    have hnat : nearestNonnegNat 2 e2m1Nums k 2 = k := by rcases hk with rfl | rfl | rfl <;> decide
    rw [hnat] at hq
    exact hq
  · unfold e3m2Quant symQuant
    have hn : ¬(((k : Nat) : Rat) / 8 < 0) := Rat.not_lt.mpr hx_nn
    simp only [hn, ↓reduceIte]
    rw [e3m2Levels_eq_map]
    have hq := nearestNonneg_map_div 16 k 8 (by decide) (by decide) e3m2Nums
    have hnat : nearestNonnegNat 16 e3m2Nums k 8 = 2 * k := by rcases hk with rfl | rfl | rfl <;> decide
    rw [hnat, Rat.natCast_mul] at hq
    exact Eq.trans hq (rat_div_eq_of_cross (by decide) (by decide) (by grind))
  · unfold e2m3Quant symQuant
    have hn : ¬(((k : Nat) : Rat) / 8 < 0) := Rat.not_lt.mpr hx_nn
    simp only [hn, ↓reduceIte]
    rw [e2m3Levels_eq_map]
    have hq := nearestNonneg_map_div 8 k 8 (by decide) (by decide) e2m3Nums
    have hnat : nearestNonnegNat 8 e2m3Nums k 8 = k := by rcases hk with rfl | rfl | rfl <;> decide
    rw [hnat] at hq
    exact hq

private theorem symQuant_neg_of_pos (levels : List Rat) {x : Rat} (hx : (0 : Rat) < x)
    (hq : symQuant levels x = x) : symQuant levels (-x) = -x := by
  unfold symQuant at hq ⊢
  have hn1 : ¬(x < 0) := Rat.not_lt.mpr (Rat.le_of_lt hx)
  have hneg : -x < 0 := by
    apply rat_lt_of_sub_pos
    have : (0 : Rat) - -x = x := by grind
    rw [this]; exact hx
  simp only [hn1, hneg, ↓reduceIte] at hq ⊢
  have heq : -(-x) = x := by grind
  rw [heq, hq]

private theorem inAllThreeOCPGrids_neg_of_pos {x : Rat} (hx : (0 : Rat) < x)
    (h : inAllThreeOCPGrids x) : inAllThreeOCPGrids (-x) := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
  have h4x : (0 : Rat) < 4 * x := rat_mul_pos (by decide) hx
  have habs_neg : ∀ t : Rat, (0 : Rat) < t → absRat (-t) = absRat t := by
    intro t ht
    unfold absRat
    have hn1 : -t < 0 := by
      apply rat_lt_of_sub_pos; have : (0 : Rat) - -t = t := by grind
      rw [this]; exact ht
    have hn2 : ¬(t < 0) := Rat.not_lt.mpr (Rat.le_of_lt ht)
    simp only [hn1, hn2, ↓reduceIte]; grind
  have h4neg : 4 * (-x) = -(4 * x) := by grind
  unfold inAllThreeOCPGrids
  rw [h4neg, habs_neg (4 * x) h4x, habs_neg x hx]
  exact ⟨h1, h2, h3, symQuant_neg_of_pos e2m1Levels h4x h4,
         symQuant_neg_of_pos e3m2Levels hx h5, symQuant_neg_of_pos e2m3Levels hx h6⟩

private theorem inAllThreeOCPGrids_div8 (z : Int)
    (hz : z = -3 ∨ z = -2 ∨ z = -1 ∨ z = 1 ∨ z = 2 ∨ z = 3) :
    inAllThreeOCPGrids ((z : Rat) / 8) := by
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
  · have h : (((-3 : Int) : Rat) / 8) = -(((3 : Nat) : Rat) / 8) := by
      rw [Rat.div_def, Rat.div_def]; grind
    rw [h]; exact inAllThreeOCPGrids_neg_of_pos (rat_div_pos_nat 3 8 (by decide) (by decide))
      (inAllThreeOCPGrids_pos_nat 3 (Or.inr (Or.inr rfl)))
  · have h : (((-2 : Int) : Rat) / 8) = -(((2 : Nat) : Rat) / 8) := by
      rw [Rat.div_def, Rat.div_def]; grind
    rw [h]; exact inAllThreeOCPGrids_neg_of_pos (rat_div_pos_nat 2 8 (by decide) (by decide))
      (inAllThreeOCPGrids_pos_nat 2 (Or.inr (Or.inl rfl)))
  · have h : (((-1 : Int) : Rat) / 8) = -(((1 : Nat) : Rat) / 8) := by
      rw [Rat.div_def, Rat.div_def]; grind
    rw [h]; exact inAllThreeOCPGrids_neg_of_pos (rat_div_pos_nat 1 8 (by decide) (by decide))
      (inAllThreeOCPGrids_pos_nat 1 (Or.inl rfl))
  · exact inAllThreeOCPGrids_pos_nat 1 (Or.inl rfl)
  · exact inAllThreeOCPGrids_pos_nat 2 (Or.inr (Or.inl rfl))
  · exact inAllThreeOCPGrids_pos_nat 3 (Or.inr (Or.inr rfl))

theorem goethals_seidel_native_e2m1_orthonormal_exact :
    isOrthogonal GS_n16_E2M1_low 64 ∧
    (∀ i j : Fin 16, inAllThreeOCPGrids ((GS_n16_E2M1_low i j : Rat) / 8)) ∧
    isOrthogonal GS_n32_E2M1_pm13 64 ∧
    (∀ i j : Fin 32, inAllThreeOCPGrids ((GS_n32_E2M1_pm13 i j : Rat) / 8)) ∧
    (∀ i j : Fin 32, GS_n32_E2M1_pm13 i j ≠ 0) := by
  have h16_ent : ∀ i j : Fin 16,
      GS_n16_E2M1_low i j = -3 ∨ GS_n16_E2M1_low i j = -2 ∨ GS_n16_E2M1_low i j = -1 ∨
      GS_n16_E2M1_low i j = 1 ∨ GS_n16_E2M1_low i j = 2 ∨ GS_n16_E2M1_low i j = 3 :=
    goethalsSeidel_entries_prop 4 gs16_a gs16_b gs16_c gs16_d
      (fun x => x = -3 ∨ x = -2 ∨ x = -1 ∨ x = 1 ∨ x = 2 ∨ x = 3)
      (by intro x hx; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by decide) (by decide) (by decide) (by decide)
  have h32_ent : ∀ i j : Fin 32,
      GS_n32_E2M1_pm13 i j = -3 ∨ GS_n32_E2M1_pm13 i j = -1 ∨
      GS_n32_E2M1_pm13 i j = 1 ∨ GS_n32_E2M1_pm13 i j = 3 :=
    goethalsSeidel_entries_prop 8 gs32_a gs32_b gs32_c gs32_d
      (fun x => x = -3 ∨ x = -1 ∨ x = 1 ∨ x = 3)
      (by intro x hx; rcases hx with rfl | rfl | rfl | rfl <;> decide)
      (by decide) (by decide) (by decide) (by decide)
  refine ⟨gs16_isOrthogonal, ?_, gs32_isOrthogonal, ?_, ?_⟩
  · intro i j; exact inAllThreeOCPGrids_div8 _ (h16_ent i j)
  · intro i j
    rcases h32_ent i j with h | h | h | h
    · exact inAllThreeOCPGrids_div8 _ (Or.inl h)
    · exact inAllThreeOCPGrids_div8 _ (Or.inr (Or.inr (Or.inl h)))
    · exact inAllThreeOCPGrids_div8 _ (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact inAllThreeOCPGrids_div8 _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  · intro i j
    rcases h32_ent i j with h | h | h | h <;> rw [h] <;> decide

/-! ### 4. Theorem 6: Universal Hamilton 4:8-Sparse Quaternion Orthogonality & Multi-Stage Lifting -/

theorem quatMat_isOrthogonal (a b c d : Int) :
    isOrthogonal (quatMat a b c d) (a * a + b * b + c * c + d * d) := by
  funext i j
  rcases i with ⟨iv, hiv⟩
  rcases j with ⟨jv, hjv⟩
  unfold matMul transpose scaleMat idMat
  match iv, jv with
  | 0, 0 | 0, 1 | 0, 2 | 0, 3
  | 1, 0 | 1, 1 | 1, 2 | 1, 3
  | 2, 0 | 2, 1 | 2, 2 | 2, 3
  | 3, 0 | 3, 1 | 3, 2 | 3, 3 =>
    simp only [sumFinInt, Fin.last, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.val_mk, quatMat, Fin.mk.injEq]
    grind
  | iv + 4, _ => omega
  | _, jv + 4 => omega

private def sumFinNat : (k : Nat) → (Fin k → Nat) → Nat
  | 0, _ => 0
  | k + 1, g => sumFinNat k (fun i => g i.castSucc) + g (Fin.last k)

private theorem countNonzero_congr {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i = g i) :
    countNonzero n f = countNonzero n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [countNonzero]
    rw [ih (fun i => h i.castSucc), h (Fin.last n)]

private theorem countNonzero_zero (n : Nat) : countNonzero n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [countNonzero]
    rw [ih]; simp

private theorem countNonzero_le_n (n : Nat) (f : Fin n → Int) : countNonzero n f ≤ n := by
  induction n with
  | zero => simp [countNonzero]
  | succ n ih =>
    simp only [countNonzero]
    have h1 := ih (fun i => f i.castSucc)
    split <;> omega

private theorem countNonzero_cast {m n : Nat} (h : m = n) (f : Fin m → Int) :
    countNonzero m f = countNonzero n (fun i => f ⟨i.val, h ▸ i.isLt⟩) := by
  subst h; rfl

private theorem countNonzero_add_split (p q : Nat) (f : Fin (p + q) → Int) :
    countNonzero (p + q) f =
      countNonzero p (fun i => f ⟨i.val, by omega⟩) +
      countNonzero q (fun j => f ⟨p + j.val, by omega⟩) := by
  induction q with
  | zero =>
    simp only [Nat.add_zero, countNonzero]
    exact countNonzero_congr (fun _ => rfl)
  | succ q ih =>
    have hstep : countNonzero (p + (q + 1)) f =
        countNonzero (p + q) (fun i => f ⟨i.val, by omega⟩) +
        (if f ⟨p + q, by omega⟩ ≠ 0 then 1 else 0) := rfl
    rw [hstep, ih (fun i => f ⟨i.val, by omega⟩)]
    have hrhs : countNonzero (q + 1) (fun j => f ⟨p + j.val, by omega⟩) =
        countNonzero q (fun j => f ⟨p + j.val, by omega⟩) +
        (if f ⟨p + q, by omega⟩ ≠ 0 then 1 else 0) := by
      simp only [countNonzero]; rfl
    rw [hrhs, Nat.add_assoc]

private theorem countNonzero_mul_prod (a b : Nat) (f : Fin (a * b) → Int) :
    countNonzero (a * b) f =
    sumFinNat a (fun i => countNonzero b (fun j => f ⟨i.val * b + j.val, by
      have hi := i.isLt; have hj := j.isLt
      have h1 : (i.val + 1) * b ≤ a * b := Nat.mul_le_mul_right b hi
      rw [Nat.add_mul, Nat.one_mul] at h1; omega⟩)) := by
  induction a with
  | zero =>
    rw [countNonzero_cast (Nat.zero_mul b)]; rfl
  | succ a ih =>
    have hmul : (a + 1) * b = a * b + b := by rw [Nat.add_mul, Nat.one_mul]
    rw [countNonzero_cast hmul, countNonzero_add_split (a * b) b, ih]
    simp only [sumFinNat]
    rfl

private theorem sumNat_single_le (m : Nat) (b0 : Fin m) (g : Fin m → Nat) (K : Nat)
    (hb0 : g b0 ≤ K) (hrest : ∀ b, b ≠ b0 → g b = 0) :
    sumFinNat m g ≤ K := by
  induction m with
  | zero => exact Fin.elim0 b0
  | succ m ih =>
    simp only [sumFinNat]
    by_cases h : b0 = Fin.last m
    · subst h
      have hzero : ∀ (k : Nat) (hfn : Fin k → Nat), (∀ i, hfn i = 0) →
          sumFinNat k hfn = 0 := by
        intro k; induction k with
        | zero => intro _ _; rfl
        | succ k ihk =>
          intro hfn hz
          simp only [sumFinNat]
          rw [ihk _ (fun i => hz i.castSucc), hz (Fin.last k)]
      have hl : sumFinNat m (fun i => g i.castSucc) = 0 := by
        apply hzero; intro i
        apply hrest
        intro heq; have hv := congrArg Fin.val heq
        simp only [Fin.val_castSucc, Fin.val_last] at hv; omega
      rw [hl]; omega
    · have hlt : b0.val < m := by
        have := b0.isLt
        have hne : b0.val ≠ m := fun hv => h (Fin.ext hv)
        omega
      let b0' : Fin m := ⟨b0.val, hlt⟩
      have hlast : g (Fin.last m) = 0 := hrest (Fin.last m) (Ne.symm h)
      have h1 : sumFinNat m (fun i => g i.castSucc) ≤ K := by
        apply ih b0' (fun i => g i.castSucc)
        · have heq : b0'.castSucc = b0 := Fin.ext rfl
          rw [heq]; exact hb0
        · intro b hb
          apply hrest
          intro heq; apply hb; exact Fin.ext (by have := congrArg Fin.val heq; simpa [Fin.val_castSucc, b0'] using this)
      rw [hlast]; omega

theorem blockDiagQuat_isRow4Sparse (m : Nat) (params : Fin m → Int × Int × Int × Int) :
    isRow4Sparse (blockDiagQuat m params) := by
  intro i
  rw [countNonzero_cast (Nat.mul_comm 4 m), countNonzero_mul_prod m 4]
  let b0 : Fin m := ⟨i.val / 4, by have := i.isLt; omega⟩
  apply sumNat_single_le m b0 _ 4
  · exact countNonzero_le_n 4 _
  · intro b hb
    have hzero : ∀ j : Fin 4,
        blockDiagQuat m params i ⟨b.val * 4 + j.val, by
          have h1 := b.isLt; have h2 := j.isLt
          have h3 : (b.val + 1) * 4 ≤ m * 4 := Nat.mul_le_mul_right 4 h1
          rw [Nat.add_mul, Nat.one_mul] at h3; omega⟩ = 0 := by
      intro j
      unfold blockDiagQuat
      have hdiv : (b.val * 4 + j.val) / 4 = b.val := by
        have := j.isLt; omega
      have hne : i.val / 4 ≠ (b.val * 4 + j.val) / 4 := by
        rw [hdiv]; intro heq; apply hb; exact Fin.ext heq.symm
      simp [hne]
    rw [countNonzero_congr hzero, countNonzero_zero]

theorem blockDiagQuat_isOrthogonal (m : Nat) (params : Fin m → Int × Int × Int × Int) (c : Int)
    (hnorm : ∀ b : Fin m, let (a, b1, c1, d) := params b; a * a + b1 * b1 + c1 * c1 + d * d = c) :
    isOrthogonal (blockDiagQuat m params) c := by
  funext i j
  unfold matMul transpose scaleMat idMat
  rw [sumFinInt_cast (Nat.mul_comm 4 m), sumFinInt_mul_prod m 4]
  let bi : Fin m := ⟨i.val / 4, by have := i.isLt; omega⟩
  let bj : Fin m := ⟨j.val / 4, by have := j.isLt; omega⟩
  let ri : Fin 4 := ⟨i.val % 4, by omega⟩
  let rj : Fin 4 := ⟨j.val % 4, by omega⟩
  have houter : ∀ bt : Fin m,
      sumFinInt 4 (fun rt =>
        blockDiagQuat m params ⟨bt.val * 4 + rt.val, by
          have h1 := bt.isLt; have h2 := rt.isLt
          have h3 : (bt.val + 1) * 4 ≤ m * 4 := Nat.mul_le_mul_right 4 h1
          rw [Nat.add_mul, Nat.one_mul] at h3; omega⟩ i *
        blockDiagQuat m params ⟨bt.val * 4 + rt.val, by
          have h1 := bt.isLt; have h2 := rt.isLt
          have h3 : (bt.val + 1) * 4 ≤ m * 4 := Nat.mul_le_mul_right 4 h1
          rw [Nat.add_mul, Nat.one_mul] at h3; omega⟩ j) =
      if bt = bi then (if bi = bj then (if ri = rj then c else 0) else 0) else 0 := by
    intro bt
    by_cases hbi : bt = bi
    · subst hbi
      simp only [↓reduceIte]
      by_cases hbj : bi = bj
      · rw [ite_eq_left_iff.mpr (fun hn => False.elim (hn hbj))]
        have hinner : ∀ rt : Fin 4,
            blockDiagQuat m params ⟨bi.val * 4 + rt.val, by
              have h1 := bi.isLt; have h2 := rt.isLt
              have h3 : (bi.val + 1) * 4 ≤ m * 4 := Nat.mul_le_mul_right 4 h1
              rw [Nat.add_mul, Nat.one_mul] at h3; omega⟩ i *
            blockDiagQuat m params ⟨bi.val * 4 + rt.val, by
              have h1 := bi.isLt; have h2 := rt.isLt
              have h3 : (bi.val + 1) * 4 ≤ m * 4 := Nat.mul_le_mul_right 4 h1
              rw [Nat.add_mul, Nat.one_mul] at h3; omega⟩ j =
            let (a, b1, c1, d) := params bi
            quatMat a b1 c1 d rt ri * quatMat a b1 c1 d rt rj := by
          intro rt
          unfold blockDiagQuat
          dsimp only
          have hdiv : (bi.val * 4 + rt.val) / 4 = bi.val := by have := rt.isLt; omega
          have hmod : (bi.val * 4 + rt.val) % 4 = rt.val := by have := rt.isLt; omega
          have h1 : (bi.val * 4 + rt.val) / 4 = i.val / 4 := hdiv
          have h_ij : i.val / 4 = j.val / 4 := congrArg Fin.val hbj
          simp only [h1, h_ij, ↓reduceDIte]
          have hrt_eq : (⟨(bi.val * 4 + rt.val) % 4, by omega⟩ : Fin 4) = rt := Fin.ext hmod
          have hbj_eq : (⟨j.val / 4, by have := j.isLt; omega⟩ : Fin m) = bi := hbj.symm
          simp only [hrt_eq, hbj_eq]
          rfl
        rw [sumFinInt_congr hinner]
        rcases hpar : params bi with ⟨a, b1, c1, d⟩
        have hq := congrFun (congrFun (quatMat_isOrthogonal a b1 c1 d) ri) rj
        unfold matMul transpose scaleMat idMat at hq
        have hnm := hnorm bi
        rw [hpar] at hnm
        dsimp only at hnm
        rw [hnm] at hq
        rw [hq]
        by_cases hrr : ri = rj <;> simp [hrr]
      · rw [ite_eq_right_iff.mpr (fun hp => False.elim (hbj hp))]
        have hzero : ∀ rt : Fin 4,
            blockDiagQuat m params ⟨bi.val * 4 + rt.val, by
              have h1 := bi.isLt; have h2 := rt.isLt
              have h3 : (bi.val + 1) * 4 ≤ m * 4 := Nat.mul_le_mul_right 4 h1
              rw [Nat.add_mul, Nat.one_mul] at h3; omega⟩ i *
            blockDiagQuat m params ⟨bi.val * 4 + rt.val, by
              have h1 := bi.isLt; have h2 := rt.isLt
              have h3 : (bi.val + 1) * 4 ≤ m * 4 := Nat.mul_le_mul_right 4 h1
              rw [Nat.add_mul, Nat.one_mul] at h3; omega⟩ j = 0 := by
          intro rt
          unfold blockDiagQuat
          have hdiv : (bi.val * 4 + rt.val) / 4 = bi.val := by have := rt.isLt; omega
          have hne : (bi.val * 4 + rt.val) / 4 ≠ j.val / 4 := by
            rw [hdiv]; intro heq; apply hbj; exact Fin.ext heq
          simp [hne]
        rw [sumFinInt_congr hzero, sumFinInt_zero]
    · simp only [hbi, ↓reduceIte]
      have hzero : ∀ rt : Fin 4,
          blockDiagQuat m params ⟨bt.val * 4 + rt.val, by
            have h1 := bt.isLt; have h2 := rt.isLt
            have h3 : (bt.val + 1) * 4 ≤ m * 4 := Nat.mul_le_mul_right 4 h1
            rw [Nat.add_mul, Nat.one_mul] at h3; omega⟩ i *
          blockDiagQuat m params ⟨bt.val * 4 + rt.val, by
            have h1 := bt.isLt; have h2 := rt.isLt
            have h3 : (bt.val + 1) * 4 ≤ m * 4 := Nat.mul_le_mul_right 4 h1
            rw [Nat.add_mul, Nat.one_mul] at h3; omega⟩ j = 0 := by
        intro rt
        unfold blockDiagQuat
        have hdiv : (bt.val * 4 + rt.val) / 4 = bt.val := by have := rt.isLt; omega
        have hne : (bt.val * 4 + rt.val) / 4 ≠ i.val / 4 := by
          rw [hdiv]; intro heq; apply hbi; exact Fin.ext heq
        simp [hne]
      rw [sumFinInt_congr hzero, sumFinInt_zero]
  rw [sumFinInt_congr houter, sumFinInt_single bi]
  have hiff : (bi = bj ∧ ri = rj) ↔ (i = j) := by
    constructor
    · intro ⟨h1, h2⟩
      apply Fin.ext
      have hd : i.val / 4 = j.val / 4 := congrArg Fin.val h1
      have hmo : i.val % 4 = j.val % 4 := congrArg Fin.val h2
      omega
    · intro heq; subst heq; exact ⟨rfl, rfl⟩
  by_cases h : i = j
  · have ⟨h1, h2⟩ := hiff.mpr h
    simp only [h, h1, h2, ↓reduceIte]; omega
  · by_cases h1 : bi = bj
    · have h2 : ri ≠ rj := fun hr => h (hiff.mp ⟨h1, hr⟩)
      simp only [h, h1, h2, ↓reduceIte]; omega
    · simp only [h, h1, ↓reduceIte]; omega

theorem permMat_isOrthogonal (n : Nat) (σ : Fin n → Fin n) (hσ : isBijection σ) :
    isOrthogonal (permMat n σ) 1 := by
  rcases hσ with ⟨inv, hinvL, hinvR⟩
  funext i j
  unfold matMul transpose permMat scaleMat idMat
  have hcongr : ∀ t : Fin n,
      (if σ t = i then (1 : Int) else 0) * (if σ t = j then (1 : Int) else 0) =
      if t = inv i then (if i = j then 1 else 0) else 0 := by
    intro t
    have hiff : (σ t = i) ↔ (t = inv i) := by
      constructor
      · intro h; rw [← h, hinvL]
      · intro h; rw [h, hinvR]
    by_cases ht : t = inv i
    · have h1 : σ t = i := hiff.mpr ht
      rw [h1]
      by_cases hij : i = j <;> simp [ht, hij]
    · have h1 : σ t ≠ i := fun hx => ht (hiff.mp hx)
      simp only [ht, h1, ↓reduceIte]; omega
  rw [sumFinInt_congr hcongr, sumFinInt_single (inv i)]
  by_cases hij : i = j <;> simp [hij]

theorem quatStage_isOrthogonal (m : Nat) (params : Fin m → Int × Int × Int × Int)
    (σ : Fin (4 * m) → Fin (4 * m)) (c : Int)
    (hσ : isBijection σ)
    (hnorm : ∀ b : Fin m, let (a, b1, c1, d) := params b; a * a + b1 * b1 + c1 * c1 + d * d = c) :
    isOrthogonal (quatStage m params σ) c := by
  have h := isOrthogonal_matMul (permMat_isOrthogonal (4 * m) σ hσ)
    (blockDiagQuat_isOrthogonal m params c hnorm)
  simpa [quatStage, Int.one_mul] using h

theorem quatStage_isRow4Sparse (m : Nat) (params : Fin m → Int × Int × Int × Int)
    (σ : Fin (4 * m) → Fin (4 * m)) :
    isRow4Sparse (quatStage m params σ) := by
  intro i
  have hrow : ∀ j : Fin (4 * m),
      quatStage m params σ i j = blockDiagQuat m params (σ i) j := by
    intro j
    unfold quatStage matMul permMat
    have hcongr : ∀ t : Fin (4 * m),
        (if σ i = t then (1 : Int) else 0) * blockDiagQuat m params t j =
        if σ i = t then blockDiagQuat m params (σ i) j else 0 := by
      intro t; by_cases h : σ i = t
      · subst h; simp
      · simp [h]
    rw [sumFinInt_congr hcongr, sumFinInt_single_right]
  rw [countNonzero_congr hrow]
  exact blockDiagQuat_isRow4Sparse m params (σ i)

theorem matProd_isOrthogonal (n : Nat) :
    ∀ stages : List (IntMat n n × Int),
      (∀ s ∈ stages, isOrthogonal s.1 s.2) →
      isOrthogonal (matProd n (stages.map Prod.fst)) (prodInt (stages.map Prod.snd)) := by
  intro stages
  induction stages with
  | nil =>
    intro _
    exact isOrthogonal_id n
  | cons s rest ih =>
    intro h
    simp only [List.map, matProd, prodInt]
    exact isOrthogonal_matMul (h s (by simp)) (ih (fun x hx => h x (by simp [hx])))

/-- Theorem 6: Universal Hamilton 4-square orthogonality, 4:8-sparse block-diagonal &
    permutation-coupled stage lifting to arbitrary `4m` dimensions, and multi-stage closure. -/
theorem quaternion_4of8_sparse_orthogonality_universal :
    (∀ a b c d : Int, isOrthogonal (quatMat a b c d) (a * a + b * b + c * c + d * d)) ∧
    (∀ (m : Nat) (params : Fin m → Int × Int × Int × Int) (σ : Fin (4 * m) → Fin (4 * m)) (c : Int),
      isBijection σ →
      (∀ b : Fin m, let (a, b1, c1, d) := params b; a * a + b1 * b1 + c1 * c1 + d * d = c) →
      isOrthogonal (quatStage m params σ) c ∧ isRow4Sparse (quatStage m params σ)) ∧
    (∀ (n : Nat) (stages : List (IntMat n n × Int)),
      (∀ s ∈ stages, isOrthogonal s.1 s.2) →
      isOrthogonal (matProd n (stages.map Prod.fst)) (prodInt (stages.map Prod.snd))) :=
  ⟨quatMat_isOrthogonal,
   fun m params σ c hσ hnorm => ⟨quatStage_isOrthogonal m params σ c hσ hnorm, quatStage_isRow4Sparse m params σ⟩,
   matProd_isOrthogonal⟩

end Mxfp6Ef21Rotations
