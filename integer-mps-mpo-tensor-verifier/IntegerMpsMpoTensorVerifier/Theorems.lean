/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import IntegerMpsMpoTensorVerifier.Defs

/-!
# Theorems (`IntegerMpsMpoTensorVerifier`)

# Verified Lean 4 Exact Integer MPS/MPO Tensor-Network Contraction Engine

Self-contained standalone Lean 4.34.1 proof-reflection and certificate-compiler engine
(zero Mathlib, zero `sorry`, zero custom axioms).

## Architecture
1. Exact integer finite-dimensional vector, matrix, and Kronecker algebra over `Fin D` and `Int`,
   with pure `Bool`-valued decidable checkers (`vecEq`, `matEq`) verified sound.
2. Exact binary Matrix Product States (`MPS D`) and Matrix Product Operators (`MPO D`) over
   $w$-bit integers $\{0, \dots, 2^w - 1\}$ with general contraction meta-theorems
   (`mps_inner_eq_transfer`, `mpo_trace_eq_transfer`, `mpo_apply_mps_eq`, `mpo_compose_eq`,
   `mpo_transpose_eq`, `mpo_hilbert_schmidt_eq_transfer`, `mps_mpo_mps_eq_transfer`).
3. Kernel-verified pure-silicon certificate compilers (`decide`-checked):
   - Engine A: Right & Left Exact Integer Krylov / Ho-Kalman Reduction (`RightReductionCert`,
     `LeftReductionCert`, `TwoStageCert`)
   - Engine B: Exact Orthogonality / Vanishing Certificates (`OrthogonalityCert`, Stage-1 & Stage-2)
   - Engine C: Minimal-Order Linear Recurrence & Closed-Form Certificates (`RecurrenceCert`,
     `ClosedForm1Cert`)
   - Engine D: Two-Stage Pointwise MPS & MPO Gauge-Intertwiner Certificates (`MPSGaugeRightCert`,
     `MPSGaugeLeftCert`, `MPOGaugeRightCert`, `MPOGaugeLeftCert`)
4. Direct bit-level pure-silicon binary functions (`carries`, `carriesInt`, `borrows`, `popcount`,
   `rudinShapiro`, `thueMorse`, `walshHadamard`, `modInc`, `grayCode`) and proved tensor bridges.
5. Seven novel infinite binary theorems (including a 2-parameter $\forall q : \mathbb{Z}, \forall w : \mathbb{N}$
   master law, a 16-to-2 irrational-spectrum 4th-moment collapse, Fibonacci-weighted Walsh-Carry trace,
   Hilbert-Schmidt & cyclic-shift orthogonalities, pointwise MPO-MPS & unitarity gauge identities,
   and chiral anti-symmetry $\forall k, \mathrm{Tr}(C_w^{2k+1}) = 0$), plus sharpness counterexamples,
   negative mutation rejection tests, non-vacuity witnesses, and `#print axioms`.
-/


namespace SiliconTensorEngine
theorem allFin_eq_true {n : Nat} {p : Fin n → Bool} (h : allFin n p = true) :
    ∀ i : Fin n, p i = true := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    simp only [allFin, Bool.and_eq_true] at h
    intro i
    by_cases hlast : i.val < n
    · exact ih h.1 ⟨i.val, hlast⟩
    · have heq : i = Fin.last n := Fin.ext (by simp [Fin.last]; omega)
      rw [heq]; exact h.2

theorem sumFin_congr {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i = g i) :
    sumFin n f = sumFin n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumFin]
    rw [ih (fun i => h i.castSucc), h (Fin.last n)]

theorem sumFin_zero (n : Nat) : sumFin n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumFin, ih]

theorem sumFin_add {n : Nat} (f g : Fin n → Int) :
    sumFin n (fun i => f i + g i) = sumFin n f + sumFin n g := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih =>
    simp only [sumFin]
    rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc)]
    omega

theorem sumFin_mul_left {n : Nat} (c : Int) (f : Fin n → Int) :
    sumFin n (fun i => c * f i) = c * sumFin n f := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih =>
    simp only [sumFin]
    rw [ih (fun i => f i.castSucc), Int.mul_add]

theorem sumFin_mul_right {n : Nat} (f : Fin n → Int) (c : Int) :
    sumFin n (fun i => f i * c) = sumFin n f * c := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih =>
    simp only [sumFin]
    rw [ih (fun i => f i.castSucc), Int.add_mul]

theorem sumFin_swap {m n : Nat} (f : Fin m → Fin n → Int) :
    sumFin m (fun i => sumFin n (fun j => f i j)) =
    sumFin n (fun j => sumFin m (fun i => f i j)) := by
  induction m with
  | zero =>
    simp only [sumFin]
    symm
    exact sumFin_zero n
  | succ m ih =>
    simp only [sumFin]
    rw [ih (fun i j => f i.castSucc j)]
    rw [← sumFin_add]

theorem sumFin_cast {m n : Nat} (h : m = n) (f : Fin m → Int) :
    sumFin m f = sumFin n (fun i => f ⟨i.val, h ▸ i.isLt⟩) := by
  subst h
  exact sumFin_congr (fun i => rfl)

theorem sumFin_split (a b : Nat) (f : Fin (a + b) → Int) :
    sumFin (a + b) f =
    sumFin a (fun i => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right a b)⟩) +
    sumFin b (fun j => f ⟨a + j.val, Nat.add_lt_add_left j.isLt a⟩) := by
  induction b with
  | zero =>
    simp only [sumFin, Int.add_zero]
    exact sumFin_congr (fun i => rfl)
  | succ b ih =>
    have hstep : sumFin (a + (b + 1)) f =
        sumFin (a + b) (fun i => f i.castSucc) + f (Fin.last (a + b)) := rfl
    rw [hstep, ih (fun i => f i.castSucc)]
    simp only [sumFin]
    have h1 : sumFin a (fun i => f (⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right a b)⟩ : Fin (a + b)).castSucc) =
        sumFin a (fun i => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right a (b + 1))⟩) :=
      sumFin_congr (fun i => rfl)
    have h2 : sumFin b (fun j => f (⟨a + j.val, Nat.add_lt_add_left j.isLt a⟩ : Fin (a + b)).castSucc) =
        sumFin b (fun j => f ⟨a + j.castSucc.val, Nat.add_lt_add_left j.castSucc.isLt a⟩) :=
      sumFin_congr (fun j => rfl)
    have hlast : f (Fin.last (a + b)) = f ⟨a + (Fin.last b).val, Nat.add_lt_add_left (Fin.last b).isLt a⟩ := rfl
    rw [h1, h2, hlast]
    omega

theorem finMulLt {a b : Nat} (i : Fin a) (j : Fin b) : i.val * b + j.val < a * b := by
  have hi : i.val + 1 ≤ a := i.isLt
  have h1 : i.val * b + j.val < i.val * b + b := Nat.add_lt_add_left j.isLt _
  have h2 : i.val * b + b = (i.val + 1) * b := (Nat.succ_mul i.val b).symm
  have h3 : (i.val + 1) * b ≤ a * b := Nat.mul_le_mul_right b hi
  omega

theorem sumFin_mul_split (a b : Nat) (f : Fin (a * b) → Int) :
    sumFin (a * b) f =
    sumFin a (fun i => sumFin b (fun j => f ⟨i.val * b + j.val, finMulLt i j⟩)) := by
  induction a with
  | zero =>
    rw [sumFin_cast (Nat.zero_mul b) f]
    rfl
  | succ a ih =>
    rw [sumFin_cast (Nat.succ_mul a b) f]
    rw [sumFin_split (a * b) b]
    rw [ih]
    simp only [sumFin]
    congr 1

theorem sumFin_single {n : Nat} (k : Fin n) (v : Int) :
    sumFin n (fun i => if i = k then v else 0) = v := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    simp only [sumFin]
    by_cases hk : k.val < n
    · have hne : Fin.last n ≠ k := by
        intro h; have := congrArg Fin.val h; simp [Fin.last] at this; omega
      have hcast : ∀ i : Fin n, (i.castSucc = k) ↔ (i = ⟨k.val, hk⟩) := by
        intro i; constructor
        · intro h; exact Fin.ext (by have := congrArg Fin.val h; simpa [Fin.castSucc] using this)
        · intro h; exact Fin.ext (by have := congrArg Fin.val h; simpa [Fin.castSucc] using this)
      have h1 : sumFin n (fun i => if i.castSucc = k then v else 0) =
          sumFin n (fun i => if i = ⟨k.val, hk⟩ then v else 0) :=
        sumFin_congr (fun i => by simp [hcast i])
      rw [h1, ih ⟨k.val, hk⟩]
      simp [hne]
    · have heq : k = Fin.last n := Fin.ext (by simp [Fin.last]; omega)
      subst heq
      have hzero : sumFin n (fun i => if i.castSucc = Fin.last n then v else 0) =
          sumFin n (fun _ => 0) :=
        sumFin_congr (fun i => by
          have hne : i.castSucc ≠ Fin.last n := by
            intro h; have := congrArg Fin.val h; simp [Fin.last] at this; omega
          simp [hne])
      rw [hzero, sumFin_zero]
      simp

def vecAdd {D : Nat} (u v : Vec D) : Vec D := fun i => u i + v i
def matZero (R C : Nat) : Mat R C := fun _ _ => 0
def matAdd {R C : Nat} (A B : Mat R C) : Mat R C := fun i j => A i j + B i j
def matScale {R C : Nat} (c : Int) (A : Mat R C) : Mat R C := fun i j => c * A i j
-- Kronecker Product
def kronVec {D1 D2 : Nat} (u1 : Vec D1) (u2 : Vec D2) : Vec (D1 * D2) :=
  fun i =>
    if h2 : 0 < D2 then
      u1 ⟨i.val / D2, Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq i.isLt (Nat.mul_comm D1 D2))⟩ *
      u2 ⟨i.val % D2, Nat.mod_lt _ h2⟩
    else 0

def kronMat {R1 C1 R2 C2 : Nat} (A1 : Mat R1 C1) (A2 : Mat R2 C2) : Mat (R1 * R2) (C1 * C2) :=
  fun i j =>
    if hR2 : 0 < R2 then
      if hC2 : 0 < C2 then
        A1 ⟨i.val / R2, Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq i.isLt (Nat.mul_comm R1 R2))⟩
           ⟨j.val / C2, Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq j.isLt (Nat.mul_comm C1 C2))⟩ *
        A2 ⟨i.val % R2, Nat.mod_lt _ hR2⟩
           ⟨j.val % C2, Nat.mod_lt _ hC2⟩
      else 0
    else 0

theorem vecEq_eq_true {D : Nat} {u v : Vec D} (h : vecEq u v = true) : u = v := by
  funext i
  exact of_decide_eq_true (allFin_eq_true h i)

theorem matEq_eq_true {R C : Nat} {A B : Mat R C} (h : matEq A B = true) : A = B := by
  funext i j
  exact of_decide_eq_true (allFin_eq_true (allFin_eq_true h i) j)

-- Core Algebraic Lemmas
theorem vecDot_zero_left {D : Nat} (v : Vec D) : vecDot (vecZero D) v = 0 := by
  unfold vecDot vecZero
  rw [sumFin_congr (fun i => Int.zero_mul (v i))]
  exact sumFin_zero D

theorem vecDot_zero_right {D : Nat} (u : Vec D) : vecDot u (vecZero D) = 0 := by
  unfold vecDot vecZero
  rw [sumFin_congr (fun i => Int.mul_zero (u i))]
  exact sumFin_zero D

theorem vecDot_add_left {D : Nat} (u1 u2 v : Vec D) :
    vecDot (vecAdd u1 u2) v = vecDot u1 v + vecDot u2 v := by
  unfold vecDot vecAdd
  rw [sumFin_congr (fun i => Int.add_mul (u1 i) (u2 i) (v i))]
  exact sumFin_add _ _

theorem vecDot_scale_left {D : Nat} (c : Int) (u v : Vec D) :
    vecDot (vecScale c u) v = c * vecDot u v := by
  unfold vecDot vecScale
  rw [sumFin_congr (fun i => Int.mul_assoc c (u i) (v i))]
  exact sumFin_mul_left c _

theorem vecDot_scale_right {D : Nat} (c : Int) (u v : Vec D) :
    vecDot u (vecScale c v) = c * vecDot u v := by
  unfold vecDot vecScale
  rw [sumFin_congr (fun i => by rw [← Int.mul_assoc, Int.mul_comm (u i) c, Int.mul_assoc])]
  exact sumFin_mul_left c _

theorem vecDot_matVec {R C : Nat} (u : Vec R) (A : Mat R C) (v : Vec C) :
    vecDot u (matVec A v) = vecDot (vecMat u A) v := by
  unfold vecDot matVec vecMat
  rw [sumFin_congr (fun i => (sumFin_mul_left (u i) (fun j => A i j * v j)).symm)]
  rw [sumFin_swap]
  apply sumFin_congr; intro j
  rw [← sumFin_mul_right]
  apply sumFin_congr; intro i
  exact (Int.mul_assoc (u i) (A i j) (v j)).symm

theorem matVec_matMul {R K C : Nat} (A : Mat R K) (B : Mat K C) (v : Vec C) :
    matVec (matMul A B) v = matVec A (matVec B v) := by
  funext i
  unfold matVec matMul
  rw [sumFin_congr (fun j => (sumFin_mul_right (fun k => A i k * B k j) (v j)).symm)]
  rw [sumFin_swap]
  apply sumFin_congr; intro k
  rw [← sumFin_mul_left]
  apply sumFin_congr; intro j
  exact Int.mul_assoc (A i k) (B k j) (v j)

theorem vecMat_matMul {R K C : Nat} (u : Vec R) (A : Mat R K) (B : Mat K C) :
    vecMat u (matMul A B) = vecMat (vecMat u A) B := by
  funext j
  unfold vecMat matMul
  rw [sumFin_congr (fun i => (sumFin_mul_left (u i) (fun k => A i k * B k j)).symm)]
  rw [sumFin_swap]
  apply sumFin_congr; intro k
  rw [← sumFin_mul_right]
  apply sumFin_congr; intro i
  exact (Int.mul_assoc (u i) (A i k) (B k j)).symm

theorem matMul_assoc {A B C D : Nat} (X : Mat A B) (Y : Mat B C) (Z : Mat C D) :
    matMul (matMul X Y) Z = matMul X (matMul Y Z) := by
  funext i j
  unfold matMul
  rw [sumFin_congr (fun k => (sumFin_mul_right (fun m => X i m * Y m k) (Z k j)).symm)]
  rw [sumFin_swap]
  apply sumFin_congr; intro m
  rw [← sumFin_mul_left]
  apply sumFin_congr; intro k
  exact Int.mul_assoc (X i m) (Y m k) (Z k j)

theorem matVec_id {D : Nat} (v : Vec D) : matVec (matId D) v = v := by
  funext i
  unfold matVec matId
  have h : (fun j => (if i = j then (1 : Int) else 0) * v j) =
           (fun j => if j = i then v i else 0) := by
    funext j
    by_cases hji : j = i
    · subst hji; simp
    · have hij : i ≠ j := fun h => hji h.symm
      simp [hij, hji]
  rw [h]
  exact sumFin_single i (v i)

theorem vecMat_id {D : Nat} (u : Vec D) : vecMat u (matId D) = u := by
  funext j
  unfold vecMat matId
  have h : (fun i => u i * (if i = j then (1 : Int) else 0)) =
           (fun i => if i = j then u j else 0) := by
    funext i
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  rw [h]
  exact sumFin_single j (u j)

theorem matMul_id_left {R C : Nat} (A : Mat R C) : matMul (matId R) A = A := by
  funext i j
  exact congrFun (matVec_id (fun k => A k j)) i

theorem matMul_id_right {R C : Nat} (A : Mat R C) : matMul A (matId C) = A := by
  funext i j
  exact congrFun (vecMat_id (fun k => A i k)) j

theorem matVec_scale {R C : Nat} (c : Int) (A : Mat R C) (v : Vec C) :
    matVec A (vecScale c v) = vecScale c (matVec A v) := by
  funext i
  unfold matVec vecScale
  rw [← sumFin_mul_left]
  apply sumFin_congr; intro j
  rw [← Int.mul_assoc, Int.mul_comm (A i j) c, Int.mul_assoc]

theorem vecMat_scale {R C : Nat} (c : Int) (u : Vec R) (A : Mat R C) :
    vecMat (vecScale c u) A = vecScale c (vecMat u A) := by
  funext j
  unfold vecMat vecScale
  rw [← sumFin_mul_left]
  apply sumFin_congr; intro i
  exact Int.mul_assoc c (u i) (A i j)

theorem vecMat_matAdd {R C : Nat} (u : Vec R) (A B : Mat R C) :
    vecMat u (matAdd A B) = vecAdd (vecMat u A) (vecMat u B) := by
  funext j
  unfold vecMat matAdd vecAdd
  rw [sumFin_congr (fun i => Int.mul_add (u i) (A i j) (B i j))]
  exact sumFin_add _ _

theorem matPow_add {D : Nat} (A : Mat D D) (m n : Nat) :
    matPow A (m + n) = matMul (matPow A m) (matPow A n) := by
  induction m with
  | zero =>
    simp [Nat.zero_add, matPow, matMul_id_left]
  | succ m ih =>
    rw [Nat.succ_add]
    simp only [matPow]
    rw [ih, matMul_assoc]

theorem matPow_intertwine_right {K r : Nat} (T : Mat K K) (M : Mat r r) (P : Mat K r)
    (h : matMul T P = matMul P M) :
    ∀ w : Nat, matMul (matPow T w) P = matMul P (matPow M w) := by
  intro w
  induction w with
  | zero =>
    simp [matPow, matMul_id_left, matMul_id_right]
  | succ w ih =>
    simp only [matPow]
    rw [matMul_assoc, ih, ← matMul_assoc, h, matMul_assoc]

theorem matPow_intertwine_left {K r : Nat} (T : Mat K K) (M : Mat r r) (Q : Mat r K)
    (h : matMul Q T = matMul M Q) :
    ∀ w : Nat, matMul Q (matPow T w) = matMul (matPow M w) Q := by
  intro w
  induction w with
  | zero =>
    simp [matPow, matMul_id_left, matMul_id_right]
  | succ w ih =>
    simp only [matPow]
    rw [← matMul_assoc, h, matMul_assoc, ih, ← matMul_assoc]

-- Kronecker Lemmas
theorem kronVec_eval {D1 D2 : Nat} (u1 : Vec D1) (u2 : Vec D2) (i : Fin D1) (j : Fin D2)
    (hlt : i.val * D2 + j.val < D1 * D2) :
    kronVec u1 u2 ⟨i.val * D2 + j.val, hlt⟩ = u1 i * u2 j := by
  have h2 : 0 < D2 := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
  unfold kronVec
  simp only [h2, ↓reduceDIte]
  have hdiv : (i.val * D2 + j.val) / D2 = i.val := by
    rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ h2, Nat.div_eq_of_lt j.isLt, Nat.zero_add]
  have hmod : (i.val * D2 + j.val) % D2 = j.val := by
    rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.isLt]
  congr 1
  · exact congrArg u1 (Fin.ext hdiv)
  · exact congrArg u2 (Fin.ext hmod)

theorem kronMat_eval {R1 C1 R2 C2 : Nat} (A1 : Mat R1 C1) (A2 : Mat R2 C2)
    (i1 : Fin R1) (i2 : Fin R2) (j1 : Fin C1) (j2 : Fin C2)
    (hltR : i1.val * R2 + i2.val < R1 * R2) (hltC : j1.val * C2 + j2.val < C1 * C2) :
    kronMat A1 A2 ⟨i1.val * R2 + i2.val, hltR⟩ ⟨j1.val * C2 + j2.val, hltC⟩ =
    A1 i1 j1 * A2 i2 j2 := by
  have hR2 : 0 < R2 := Nat.lt_of_le_of_lt (Nat.zero_le _) i2.isLt
  have hC2 : 0 < C2 := Nat.lt_of_le_of_lt (Nat.zero_le _) j2.isLt
  unfold kronMat
  simp only [hR2, hC2, ↓reduceDIte]
  have hdivR : (i1.val * R2 + i2.val) / R2 = i1.val := by
    rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ hR2, Nat.div_eq_of_lt i2.isLt, Nat.zero_add]
  have hmodR : (i1.val * R2 + i2.val) % R2 = i2.val := by
    rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i2.isLt]
  have hdivC : (j1.val * C2 + j2.val) / C2 = j1.val := by
    rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ hC2, Nat.div_eq_of_lt j2.isLt, Nat.zero_add]
  have hmodC : (j1.val * C2 + j2.val) % C2 = j2.val := by
    rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j2.isLt]
  have h1 : A1 ⟨(i1.val * R2 + i2.val) / R2, Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq hltR (Nat.mul_comm R1 R2))⟩
               ⟨(j1.val * C2 + j2.val) / C2, Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq hltC (Nat.mul_comm C1 C2))⟩ = A1 i1 j1 := by
    congr 1
    · exact Fin.ext hdivR
    · exact Fin.ext hdivC
  have h2 : A2 ⟨(i1.val * R2 + i2.val) % R2, Nat.mod_lt _ hR2⟩
               ⟨(j1.val * C2 + j2.val) % C2, Nat.mod_lt _ hC2⟩ = A2 i2 j2 := by
    congr 1
    · exact Fin.ext hmodR
    · exact Fin.ext hmodC
  rw [h1, h2]

theorem vecDot_kron {D1 D2 : Nat} (u1 v1 : Vec D1) (u2 v2 : Vec D2) :
    vecDot (kronVec u1 u2) (kronVec v1 v2) = vecDot u1 v1 * vecDot u2 v2 := by
  unfold vecDot
  rw [sumFin_mul_split D1 D2]
  have hstep : ∀ i : Fin D1,
      sumFin D2 (fun j => kronVec u1 u2 ⟨i.val * D2 + j.val, finMulLt i j⟩ *
                          kronVec v1 v2 ⟨i.val * D2 + j.val, finMulLt i j⟩) =
      (u1 i * v1 i) * sumFin D2 (fun j => u2 j * v2 j) := by
    intro i
    rw [← sumFin_mul_left]
    apply sumFin_congr; intro j
    rw [kronVec_eval, kronVec_eval]
    calc (u1 i * u2 j) * (v1 i * v2 j)
      _ = u1 i * (u2 j * (v1 i * v2 j)) := Int.mul_assoc _ _ _
      _ = u1 i * (v1 i * (u2 j * v2 j)) := by rw [← Int.mul_assoc (u2 j), Int.mul_comm (u2 j) (v1 i), Int.mul_assoc]
      _ = (u1 i * v1 i) * (u2 j * v2 j) := (Int.mul_assoc _ _ _).symm
  rw [sumFin_congr hstep]
  exact sumFin_mul_right _ _

theorem vecMat_kron {R1 C1 R2 C2 : Nat} (u1 : Vec R1) (u2 : Vec R2)
    (A1 : Mat R1 C1) (A2 : Mat R2 C2) :
    vecMat (kronVec u1 u2) (kronMat A1 A2) = kronVec (vecMat u1 A1) (vecMat u2 A2) := by
  funext j
  by_cases hC2 : 0 < C2
  · let j1 : Fin C1 := ⟨j.val / C2, Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq j.isLt (Nat.mul_comm C1 C2))⟩
    let j2 : Fin C2 := ⟨j.val % C2, Nat.mod_lt _ hC2⟩
    have hj : j = ⟨j1.val * C2 + j2.val, finMulLt j1 j2⟩ := by
      apply Fin.ext
      change j.val = j.val / C2 * C2 + j.val % C2
      have hdm := Nat.div_add_mod j.val C2
      have hmc : C2 * (j.val / C2) = j.val / C2 * C2 := Nat.mul_comm C2 (j.val / C2)
      omega
    rw [hj, kronVec_eval]
    unfold vecMat
    rw [sumFin_mul_split R1 R2]
    have hstep : ∀ i1 : Fin R1,
        sumFin R2 (fun i2 => kronVec u1 u2 ⟨i1.val * R2 + i2.val, finMulLt i1 i2⟩ *
          kronMat A1 A2 ⟨i1.val * R2 + i2.val, finMulLt i1 i2⟩ ⟨j1.val * C2 + j2.val, finMulLt j1 j2⟩) =
        (u1 i1 * A1 i1 j1) * sumFin R2 (fun i2 => u2 i2 * A2 i2 j2) := by
      intro i1
      rw [← sumFin_mul_left]
      apply sumFin_congr; intro i2
      rw [kronVec_eval, kronMat_eval]
      calc (u1 i1 * u2 i2) * (A1 i1 j1 * A2 i2 j2)
        _ = u1 i1 * (u2 i2 * (A1 i1 j1 * A2 i2 j2)) := Int.mul_assoc _ _ _
        _ = u1 i1 * (A1 i1 j1 * (u2 i2 * A2 i2 j2)) := by
            rw [← Int.mul_assoc (u2 i2), Int.mul_comm (u2 i2) (A1 i1 j1), Int.mul_assoc]
        _ = (u1 i1 * A1 i1 j1) * (u2 i2 * A2 i2 j2) := (Int.mul_assoc _ _ _).symm
    rw [sumFin_congr hstep]
    exact sumFin_mul_right _ _
  · have hC2z : C2 = 0 := by omega
    have hlt : j.val < 0 := by
      have h1 := j.isLt
      have h2 : C1 * C2 = 0 := by rw [hC2z, Nat.mul_zero]
      omega
    exact absurd hlt (Nat.not_lt_zero _)

-- ============================================================================
-- PART 2: Exact Binary MPS/MPO Tensor-Network Contraction Engine
-- ============================================================================

structure MPS (D : Nat) where
  L : Vec D
  A : Bool → Mat D D
  R : Vec D

structure MPO (D : Nat) where
  L : Vec D
  W : Bool → Bool → Mat D D
  R : Vec D

def MPS.evalAux {D : Nat} (M : MPS D) : Nat → Vec D → Nat → Int
  | 0, u, _ => vecDot u M.R
  | w + 1, u, x => M.evalAux w (vecMat u (M.A (x % 2 == 1))) (x / 2)

def MPS.eval {D : Nat} (M : MPS D) (w : Nat) (x : Nat) : Int :=
  M.evalAux w M.L x

def MPO.evalAux {D : Nat} (O : MPO D) : Nat → Vec D → Nat → Nat → Int
  | 0, u, _, _ => vecDot u O.R
  | w + 1, u, x, y => O.evalAux w (vecMat u (O.W (x % 2 == 1) (y % 2 == 1))) (x / 2) (y / 2)

def MPO.eval {D : Nat} (O : MPO D) (w : Nat) (x y : Nat) : Int :=
  O.evalAux w O.L x y

theorem sumNat_congr {n : Nat} {f g : Nat → Int} (h : ∀ k, k < n → f k = g k) :
    sumNat n f = sumNat n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumNat]
    rw [ih (fun k hk => h k (Nat.lt_succ_of_lt hk)), h n (Nat.lt_succ_self n)]

theorem sumNat_add {n : Nat} (f g : Nat → Int) :
    sumNat n (fun k => f k + g k) = sumNat n f + sumNat n g := by
  induction n with
  | zero => simp [sumNat]
  | succ n ih => simp only [sumNat]; rw [ih]; omega

theorem sumNat_zero (n : Nat) : sumNat n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumNat, ih]

theorem sumNat_mul_left {n : Nat} (c : Int) (f : Nat → Int) :
    sumNat n (fun k => c * f k) = c * sumNat n f := by
  induction n with
  | zero => simp [sumNat]
  | succ n ih => simp only [sumNat]; rw [ih, Int.mul_add]

theorem sumNat_two_mul (n : Nat) (f : Nat → Int) :
    sumNat (2 * n) f = sumNat n (fun m => f (2 * m)) + sumNat n (fun m => f (2 * m + 1)) := by
  induction n with
  | zero => simp [sumNat]
  | succ n ih =>
    have h2 : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
    rw [h2]
    simp only [sumNat]
    rw [ih]
    omega

theorem sumNat_pow2_succ (w : Nat) (f : Nat → Int) :
    sumNat (2 ^ (w + 1)) f =
    sumNat (2 ^ w) (fun m => f (2 * m)) + sumNat (2 ^ w) (fun m => f (2 * m + 1)) := by
  have hp : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [hp]
  exact sumNat_two_mul (2 ^ w) f

-- Tensor Network Constructors
def mpsInnerTM {D1 D2 : Nat} (M1 : MPS D1) (M2 : MPS D2) : Mat (D1 * D2) (D1 * D2) :=
  matAdd (kronMat (M1.A false) (M2.A false)) (kronMat (M1.A true) (M2.A true))

def mpoTraceTM {D : Nat} (O : MPO D) : Mat D D :=
  matAdd (O.W false false) (O.W true true)

def mpoTranspose {D : Nat} (O : MPO D) : MPO D :=
  { L := O.L, W := fun b1 b2 => O.W b2 b1, R := O.R }

def mpoApplyMPS {DO DM : Nat} (O : MPO DO) (M : MPS DM) : MPS (DO * DM) :=
  { L := kronVec O.L M.L
    A := fun b1 => matAdd (kronMat (O.W b1 false) (M.A false)) (kronMat (O.W b1 true) (M.A true))
    R := kronVec O.R M.R }

def mpoCompose {D1 D2 : Nat} (O1 : MPO D1) (O2 : MPO D2) : MPO (D1 * D2) :=
  { L := kronVec O1.L O2.L
    W := fun b1 b3 => matAdd (kronMat (O1.W b1 false) (O2.W false b3))
                             (kronMat (O1.W b1 true) (O2.W true b3))
    R := kronVec O1.R O2.R }

-- General Transfer-Matrix & Contraction Meta-Theorems (ALL bond dimensions D1, D2, ALL w : Nat!)

private theorem mod2_two_mul (m : Nat) : (2 * m) % 2 = 0 := by omega
private theorem div2_two_mul (m : Nat) : (2 * m) / 2 = m := by omega
private theorem mod2_two_mul_succ (m : Nat) : (2 * m + 1) % 2 = 1 := by omega
private theorem div2_two_mul_succ (m : Nat) : (2 * m + 1) / 2 = m := by omega

theorem mps_inner_aux_eq_transfer {D1 D2 : Nat} (M1 : MPS D1) (M2 : MPS D2) :
    ∀ (w : Nat) (u1 : Vec D1) (u2 : Vec D2),
      sumNat (2 ^ w) (fun x => M1.evalAux w u1 x * M2.evalAux w u2 x) =
      vecDot (kronVec u1 u2) (matVec (matPow (mpsInnerTM M1 M2) w) (kronVec M1.R M2.R)) := by
  intro w
  induction w with
  | zero =>
    intro u1 u2
    simp only [Nat.pow_zero, sumNat, Int.zero_add, MPS.evalAux, matPow, matVec_id]
    exact (vecDot_kron u1 M1.R u2 M2.R).symm
  | succ w ih =>
    intro u1 u2
    rw [sumNat_pow2_succ]
    have h0 : sumNat (2 ^ w) (fun m => M1.evalAux (w + 1) u1 (2 * m) * M2.evalAux (w + 1) u2 (2 * m)) =
        vecDot (kronVec (vecMat u1 (M1.A false)) (vecMat u2 (M2.A false)))
               (matVec (matPow (mpsInnerTM M1 M2) w) (kronVec M1.R M2.R)) := by
      have hc : (fun m => M1.evalAux (w + 1) u1 (2 * m) * M2.evalAux (w + 1) u2 (2 * m)) =
          (fun m => M1.evalAux w (vecMat u1 (M1.A false)) m * M2.evalAux w (vecMat u2 (M2.A false)) m) := by
        funext m; simp [MPS.evalAux]
      rw [hc]; exact ih _ _
    have h1 : sumNat (2 ^ w) (fun m => M1.evalAux (w + 1) u1 (2 * m + 1) * M2.evalAux (w + 1) u2 (2 * m + 1)) =
        vecDot (kronVec (vecMat u1 (M1.A true)) (vecMat u2 (M2.A true)))
               (matVec (matPow (mpsInnerTM M1 M2) w) (kronVec M1.R M2.R)) := by
      have hc : (fun m => M1.evalAux (w + 1) u1 (2 * m + 1) * M2.evalAux (w + 1) u2 (2 * m + 1)) =
          (fun m => M1.evalAux w (vecMat u1 (M1.A true)) m * M2.evalAux w (vecMat u2 (M2.A true)) m) := by
        funext m; simp [MPS.evalAux, mod2_two_mul_succ, div2_two_mul_succ]
      rw [hc]; exact ih _ _
    rw [h0, h1, ← vecDot_add_left, ← vecMat_kron, ← vecMat_kron, ← vecMat_matAdd]
    change vecDot (vecMat (kronVec u1 u2) (mpsInnerTM M1 M2)) _ = _
    rw [← vecDot_matVec, ← matVec_matMul]
    rfl

theorem mps_inner_eq_transfer {D1 D2 : Nat} (M1 : MPS D1) (M2 : MPS D2) (w : Nat) :
    sumNat (2 ^ w) (fun x => M1.eval w x * M2.eval w x) =
    vecDot (kronVec M1.L M2.L) (matVec (matPow (mpsInnerTM M1 M2) w) (kronVec M1.R M2.R)) :=
  mps_inner_aux_eq_transfer M1 M2 w M1.L M2.L

theorem mpo_trace_aux_eq_transfer {D : Nat} (O : MPO D) :
    ∀ (w : Nat) (u : Vec D),
      sumNat (2 ^ w) (fun x => O.evalAux w u x x) =
      vecDot u (matVec (matPow (mpoTraceTM O) w) O.R) := by
  intro w
  induction w with
  | zero =>
    intro u
    simp [sumNat, MPO.evalAux, matPow, matVec_id]
  | succ w ih =>
    intro u
    rw [sumNat_pow2_succ]
    have h0 : sumNat (2 ^ w) (fun m => O.evalAux (w + 1) u (2 * m) (2 * m)) =
        vecDot (vecMat u (O.W false false)) (matVec (matPow (mpoTraceTM O) w) O.R) := by
      have hc : (fun m => O.evalAux (w + 1) u (2 * m) (2 * m)) =
          (fun m => O.evalAux w (vecMat u (O.W false false)) m m) := by
        funext m; simp [MPO.evalAux]
      rw [hc]; exact ih _
    have h1 : sumNat (2 ^ w) (fun m => O.evalAux (w + 1) u (2 * m + 1) (2 * m + 1)) =
        vecDot (vecMat u (O.W true true)) (matVec (matPow (mpoTraceTM O) w) O.R) := by
      have hc : (fun m => O.evalAux (w + 1) u (2 * m + 1) (2 * m + 1)) =
          (fun m => O.evalAux w (vecMat u (O.W true true)) m m) := by
        funext m; simp [MPO.evalAux, mod2_two_mul_succ, div2_two_mul_succ]
      rw [hc]; exact ih _
    rw [h0, h1, ← vecDot_add_left, ← vecMat_matAdd]
    change vecDot (vecMat u (mpoTraceTM O)) _ = _
    rw [← vecDot_matVec, ← matVec_matMul]
    rfl

theorem mpo_trace_eq_transfer {D : Nat} (O : MPO D) (w : Nat) :
    sumNat (2 ^ w) (fun x => O.eval w x x) =
    vecDot O.L (matVec (matPow (mpoTraceTM O) w) O.R) :=
  mpo_trace_aux_eq_transfer O w O.L

theorem mpo_transpose_aux_eq {D : Nat} (O : MPO D) :
    ∀ (w : Nat) (u : Vec D) (x y : Nat),
      (mpoTranspose O).evalAux w u x y = O.evalAux w u y x := by
  intro w
  induction w with
  | zero => intro u x y; rfl
  | succ w ih =>
    intro u x y
    simp only [MPO.evalAux, mpoTranspose]
    exact ih _ _ _

theorem mpo_transpose_eq {D : Nat} (O : MPO D) (w x y : Nat) :
    (mpoTranspose O).eval w x y = O.eval w y x :=
  mpo_transpose_aux_eq O w O.L x y

theorem mpo_evalAux_add {D : Nat} (O : MPO D) :
    ∀ (w : Nat) (u1 u2 : Vec D) (x y : Nat),
      O.evalAux w (vecAdd u1 u2) x y = O.evalAux w u1 x y + O.evalAux w u2 x y := by
  intro w
  induction w with
  | zero => intro u1 u2 x y; exact vecDot_add_left u1 u2 O.R
  | succ w ih =>
    intro u1 u2 x y
    simp only [MPO.evalAux]
    have hadd : vecMat (vecAdd u1 u2) (O.W (x % 2 == 1) (y % 2 == 1)) =
        vecAdd (vecMat u1 (O.W (x % 2 == 1) (y % 2 == 1)))
               (vecMat u2 (O.W (x % 2 == 1) (y % 2 == 1))) := by
      funext j; unfold vecMat vecAdd
      rw [sumFin_congr (fun i => Int.add_mul (u1 i) (u2 i) _)]
      exact sumFin_add _ _
    rw [hadd]
    exact ih _ _ _ _

theorem mps_evalAux_add {D : Nat} (M : MPS D) :
    ∀ (w : Nat) (u1 u2 : Vec D) (x : Nat),
      M.evalAux w (vecAdd u1 u2) x = M.evalAux w u1 x + M.evalAux w u2 x := by
  intro w
  induction w with
  | zero => intro u1 u2 x; exact vecDot_add_left u1 u2 M.R
  | succ w ih =>
    intro u1 u2 x
    simp only [MPS.evalAux]
    have hadd : vecMat (vecAdd u1 u2) (M.A (x % 2 == 1)) =
        vecAdd (vecMat u1 (M.A (x % 2 == 1))) (vecMat u2 (M.A (x % 2 == 1))) := by
      funext j; unfold vecMat vecAdd
      rw [sumFin_congr (fun i => Int.add_mul (u1 i) (u2 i) _)]
      exact sumFin_add _ _
    rw [hadd]
    exact ih _ _ _

theorem mpo_apply_mps_aux_eq {DO DM : Nat} (O : MPO DO) (M : MPS DM) :
    ∀ (w : Nat) (uo : Vec DO) (um : Vec DM) (x : Nat),
      sumNat (2 ^ w) (fun y => O.evalAux w uo x y * M.evalAux w um y) =
      (mpoApplyMPS O M).evalAux w (kronVec uo um) x := by
  intro w
  induction w with
  | zero =>
    intro uo um x
    simp only [Nat.pow_zero, sumNat, Int.zero_add, MPO.evalAux, MPS.evalAux, mpoApplyMPS]
    exact (vecDot_kron uo O.R um M.R).symm
  | succ w ih =>
    intro uo um x
    rw [sumNat_pow2_succ]
    have h0 : sumNat (2 ^ w) (fun m => O.evalAux (w + 1) uo x (2 * m) * M.evalAux (w + 1) um (2 * m)) =
        (mpoApplyMPS O M).evalAux w (kronVec (vecMat uo (O.W (x % 2 == 1) false)) (vecMat um (M.A false))) (x / 2) := by
      have hc : (fun m => O.evalAux (w + 1) uo x (2 * m) * M.evalAux (w + 1) um (2 * m)) =
          (fun m => O.evalAux w (vecMat uo (O.W (x % 2 == 1) false)) (x / 2) m *
                    M.evalAux w (vecMat um (M.A false)) m) := by
        funext m; simp [MPO.evalAux, MPS.evalAux]
      rw [hc]; exact ih _ _ _
    have h1 : sumNat (2 ^ w) (fun m => O.evalAux (w + 1) uo x (2 * m + 1) * M.evalAux (w + 1) um (2 * m + 1)) =
        (mpoApplyMPS O M).evalAux w (kronVec (vecMat uo (O.W (x % 2 == 1) true)) (vecMat um (M.A true))) (x / 2) := by
      have hc : (fun m => O.evalAux (w + 1) uo x (2 * m + 1) * M.evalAux (w + 1) um (2 * m + 1)) =
          (fun m => O.evalAux w (vecMat uo (O.W (x % 2 == 1) true)) (x / 2) m *
                    M.evalAux w (vecMat um (M.A true)) m) := by
        funext m; simp [MPO.evalAux, MPS.evalAux, mod2_two_mul_succ, div2_two_mul_succ]
      rw [hc]; exact ih _ _ _
    rw [h0, h1, ← mps_evalAux_add, ← vecMat_kron, ← vecMat_kron, ← vecMat_matAdd]
    rfl

theorem mpo_apply_mps_eq {DO DM : Nat} (O : MPO DO) (M : MPS DM) (w x : Nat) :
    sumNat (2 ^ w) (fun y => O.eval w x y * M.eval w y) =
    (mpoApplyMPS O M).eval w x :=
  mpo_apply_mps_aux_eq O M w O.L M.L x

theorem mpo_compose_aux_eq {D1 D2 : Nat} (O1 : MPO D1) (O2 : MPO D2) :
    ∀ (w : Nat) (u1 : Vec D1) (u2 : Vec D2) (x z : Nat),
      sumNat (2 ^ w) (fun y => O1.evalAux w u1 x y * O2.evalAux w u2 y z) =
      (mpoCompose O1 O2).evalAux w (kronVec u1 u2) x z := by
  intro w
  induction w with
  | zero =>
    intro u1 u2 x z
    simp only [Nat.pow_zero, sumNat, Int.zero_add, MPO.evalAux, mpoCompose]
    exact (vecDot_kron u1 O1.R u2 O2.R).symm
  | succ w ih =>
    intro u1 u2 x z
    rw [sumNat_pow2_succ]
    have h0 : sumNat (2 ^ w) (fun m => O1.evalAux (w + 1) u1 x (2 * m) * O2.evalAux (w + 1) u2 (2 * m) z) =
        (mpoCompose O1 O2).evalAux w
          (kronVec (vecMat u1 (O1.W (x % 2 == 1) false)) (vecMat u2 (O2.W false (z % 2 == 1))))
          (x / 2) (z / 2) := by
      have hc : (fun m => O1.evalAux (w + 1) u1 x (2 * m) * O2.evalAux (w + 1) u2 (2 * m) z) =
          (fun m => O1.evalAux w (vecMat u1 (O1.W (x % 2 == 1) false)) (x / 2) m *
                    O2.evalAux w (vecMat u2 (O2.W false (z % 2 == 1))) m (z / 2)) := by
        funext m; simp [MPO.evalAux]
      rw [hc]; exact ih _ _ _ _
    have h1 : sumNat (2 ^ w) (fun m => O1.evalAux (w + 1) u1 x (2 * m + 1) * O2.evalAux (w + 1) u2 (2 * m + 1) z) =
        (mpoCompose O1 O2).evalAux w
          (kronVec (vecMat u1 (O1.W (x % 2 == 1) true)) (vecMat u2 (O2.W true (z % 2 == 1))))
          (x / 2) (z / 2) := by
      have hc : (fun m => O1.evalAux (w + 1) u1 x (2 * m + 1) * O2.evalAux (w + 1) u2 (2 * m + 1) z) =
          (fun m => O1.evalAux w (vecMat u1 (O1.W (x % 2 == 1) true)) (x / 2) m *
                    O2.evalAux w (vecMat u2 (O2.W true (z % 2 == 1))) m (z / 2)) := by
        funext m; simp [MPO.evalAux, mod2_two_mul_succ, div2_two_mul_succ]
      rw [hc]; exact ih _ _ _ _
    rw [h0, h1, ← mpo_evalAux_add, ← vecMat_kron, ← vecMat_kron, ← vecMat_matAdd]
    rfl

theorem mpo_compose_eq {D1 D2 : Nat} (O1 : MPO D1) (O2 : MPO D2) (w x z : Nat) :
    sumNat (2 ^ w) (fun y => O1.eval w x y * O2.eval w y z) =
    (mpoCompose O1 O2).eval w x z :=
  mpo_compose_aux_eq O1 O2 w O1.L O2.L x z

theorem mpo_hilbert_schmidt_eq_transfer {D1 D2 : Nat} (O1 : MPO D1) (O2 : MPO D2) (w : Nat) :
    sumNat (2 ^ w) (fun x => sumNat (2 ^ w) (fun y => O1.eval w x y * O2.eval w y x)) =
    vecDot (mpoCompose O1 O2).L (matVec (matPow (mpoTraceTM (mpoCompose O1 O2)) w) (mpoCompose O1 O2).R) := by
  rw [← mpo_trace_eq_transfer (mpoCompose O1 O2) w]
  apply sumNat_congr; intro x _
  exact mpo_compose_eq O1 O2 w x x

theorem mps_mpo_mps_eq_transfer {D1 DO D2 : Nat} (M1 : MPS D1) (O : MPO DO) (M2 : MPS D2) (w : Nat) :
    sumNat (2 ^ w) (fun x => sumNat (2 ^ w) (fun y => M1.eval w x * (O.eval w x y * M2.eval w y))) =
    vecDot (kronVec M1.L (mpoApplyMPS O M2).L)
           (matVec (matPow (mpsInnerTM M1 (mpoApplyMPS O M2)) w) (kronVec M1.R (mpoApplyMPS O M2).R)) := by
  rw [← mps_inner_eq_transfer M1 (mpoApplyMPS O M2) w]
  apply sumNat_congr; intro x _
  rw [sumNat_mul_left, mpo_apply_mps_eq]

theorem sound_rightReductionCert {K r : Nat} {u : Vec K} {T : Mat K K} {v : Vec K}
    {cert : RightReductionCert K r} (h : checkRightReductionCert u T v cert = true) :
    ∀ w : Nat, cert.d * transferSeq u T v (w + cert.w0) =
      transferSeq cert.u_r cert.M cert.v_r w := by
  simp only [checkRightReductionCert, Bool.and_eq_true] at h
  have hTP : matMul T cert.P = matMul cert.P cert.M := matEq_eq_true h.1.1.2
  have hPv : matVec cert.P cert.v_r = vecScale cert.d (matVec (matPow T cert.w0) v) := vecEq_eq_true h.1.2
  have huP : vecMat u cert.P = cert.u_r := vecEq_eq_true h.2
  intro w
  unfold transferSeq
  rw [matPow_add, matVec_matMul, ← vecDot_scale_right, ← matVec_scale, ← hPv,
      ← matVec_matMul, matPow_intertwine_right T cert.M cert.P hTP w,
      matVec_matMul, vecDot_matVec, huP]

theorem sound_leftReductionCert {K r : Nat} {u : Vec K} {T : Mat K K} {v : Vec K}
    {cert : LeftReductionCert K r} (h : checkLeftReductionCert u T v cert = true) :
    ∀ w : Nat, cert.d * transferSeq u T v (w + cert.w0) =
      transferSeq cert.u_r cert.M cert.v_r w := by
  simp only [checkLeftReductionCert, Bool.and_eq_true] at h
  have hQT : matMul cert.Q T = matMul cert.M cert.Q := matEq_eq_true h.1.1.2
  have huQ : vecMat cert.u_r cert.Q = vecScale cert.d (vecMat u (matPow T cert.w0)) := vecEq_eq_true h.1.2
  have hQv : matVec cert.Q v = cert.v_r := vecEq_eq_true h.2
  intro w
  unfold transferSeq
  have hcomm : w + cert.w0 = cert.w0 + w := Nat.add_comm w cert.w0
  rw [hcomm, matPow_add, matVec_matMul, vecDot_matVec, ← vecDot_scale_left, ← huQ,
      ← vecDot_matVec, ← matVec_matMul, matPow_intertwine_left T cert.M cert.Q hQT w,
      matVec_matMul, hQv]

theorem sound_twoStageCert {K r1 r2 : Nat} {u : Vec K} {T : Mat K K} {v : Vec K}
    {cert : TwoStageCert K r1 r2} (h : checkTwoStageCert u T v cert = true) :
    ∀ w : Nat, (cert.stage2.d * cert.stage1.d) * transferSeq u T v (w + cert.stage1.w0) =
      transferSeq cert.stage2.u_r cert.stage2.M cert.stage2.v_r w := by
  simp only [checkTwoStageCert, Bool.and_eq_true] at h
  have hw0 : cert.stage2.w0 = 0 := of_decide_eq_true h.1.1
  have h1 := sound_rightReductionCert h.1.2
  have h2 := sound_leftReductionCert h.2
  intro w
  have h2w := h2 w
  rw [hw0, Nat.add_zero] at h2w
  rw [Int.mul_assoc, h1 w, h2w]

-- --- ENGINE B: Exact Orthogonality / Vanishing Certificates ---

-- Stage-1 Direct Vanishing: T^{w0} v = 0
def checkStage1ZeroCert {K : Nat} (T : Mat K K) (v : Vec K) (w0 : Nat) : Bool :=
  vecEq (matVec (matPow T w0) v) (vecZero K)

theorem sound_stage1ZeroCert {K : Nat} {u : Vec K} {T : Mat K K} {v : Vec K} {w0 : Nat}
    (h : checkStage1ZeroCert T v w0 = true) :
    ∀ w : Nat, transferSeq u T v (w + w0) = 0 := by
  have hv : matVec (matPow T w0) v = vecZero K := vecEq_eq_true h
  intro w
  unfold transferSeq
  rw [matPow_add, matVec_matMul, hv]
  have hz : matVec (matPow T w) (vecZero K) = vecZero K := by
    funext i; unfold matVec vecZero
    rw [sumFin_congr (fun j => Int.mul_zero _)]; exact sumFin_zero K
  rw [hz, vecDot_zero_right]

theorem sound_orthogonalityCert {K r : Nat} {u : Vec K} {T : Mat K K} {v : Vec K}
    {cert : RightReductionCert K r} (h : checkOrthogonalityCert u T v cert = true) :
    ∀ w : Nat, transferSeq u T v (w + cert.w0) = 0 := by
  simp only [checkOrthogonalityCert, Bool.and_eq_true] at h
  have hd : cert.d ≠ 0 := by
    have h1 := h.1
    simp only [checkRightReductionCert, Bool.and_eq_true] at h1
    exact of_decide_eq_true h1.1.1.1
  have hu0 : cert.u_r = vecZero r := vecEq_eq_true h.2
  have hred := sound_rightReductionCert h.1
  intro w
  have heq := hred w
  rw [hu0] at heq
  unfold transferSeq at heq
  rw [vecDot_zero_left] at heq
  exact (Int.mul_eq_zero.mp heq).resolve_left hd

theorem sound_recurrenceCert {K r1 r2 : Nat} {u : Vec K} {T : Mat K K} {v : Vec K}
    {cert : TwoStageCert K r1 r2} {coeffs : Vec r2}
    (h : checkRecurrenceCert u T v cert coeffs = true) :
    ∀ w : Nat,
      transferSeq u T v (w + cert.stage1.w0 + r2) =
      sumFin r2 (fun k => coeffs k * transferSeq u T v (w + cert.stage1.w0 + k.val)) := by
  simp only [checkRecurrenceCert, Bool.and_eq_true] at h
  have hts := sound_twoStageCert h.1
  have hM : matPow cert.stage2.M r2 = matLinearComb cert.stage2.M coeffs := matEq_eq_true h.2
  have hd1 : cert.stage1.d ≠ 0 := by
    have h1 := h.1
    simp only [checkTwoStageCert, checkRightReductionCert, Bool.and_eq_true] at h1
    exact of_decide_eq_true h1.1.2.1.1.1
  have hd2 : cert.stage2.d ≠ 0 := by
    have h1 := h.1
    simp only [checkTwoStageCert, checkLeftReductionCert, Bool.and_eq_true] at h1
    exact of_decide_eq_true h1.2.1.1.1
  have hdd : cert.stage2.d * cert.stage1.d ≠ 0 := Int.mul_ne_zero hd2 hd1
  intro w
  let D := cert.stage2.d * cert.stage1.d
  suffices hscaled : D * transferSeq u T v (w + cert.stage1.w0 + r2) =
      D * sumFin r2 (fun k => coeffs k * transferSeq u T v (w + cert.stage1.w0 + k.val)) by
    exact Int.eq_of_mul_eq_mul_left hdd hscaled
  have hlhs : D * transferSeq u T v (w + cert.stage1.w0 + r2) =
      transferSeq cert.stage2.u_r cert.stage2.M cert.stage2.v_r (w + r2) := by
    have ha : w + cert.stage1.w0 + r2 = (w + r2) + cert.stage1.w0 := by omega
    rw [ha]; exact hts (w + r2)
  have hrhs : D * sumFin r2 (fun k => coeffs k * transferSeq u T v (w + cert.stage1.w0 + k.val)) =
      sumFin r2 (fun k => coeffs k * transferSeq cert.stage2.u_r cert.stage2.M cert.stage2.v_r (w + k.val)) := by
    rw [← sumFin_mul_left]
    apply sumFin_congr; intro k
    have ha : w + cert.stage1.w0 + k.val = (w + k.val) + cert.stage1.w0 := by omega
    rw [ha, ← Int.mul_assoc, Int.mul_comm D (coeffs k), Int.mul_assoc, hts (w + k.val)]
  rw [hlhs, hrhs]
  unfold transferSeq
  rw [matPow_add, hM, matVec_matMul, vecDot_matVec]
  -- Expand vecDot (vecMat u2 (M^w)) (matVec (matLinearComb M coeffs) v2)
  let lw := vecMat cert.stage2.u_r (matPow cert.stage2.M w)
  have hstep : vecDot lw (matVec (matLinearComb cert.stage2.M coeffs) cert.stage2.v_r) =
      sumFin r2 (fun k => coeffs k * vecDot lw (matVec (matPow cert.stage2.M k.val) cert.stage2.v_r)) := by
    unfold vecDot matVec matLinearComb
    calc sumFin r2 (fun i => lw i * sumFin r2 (fun j => (sumFin r2 (fun k => coeffs k * matPow cert.stage2.M k.val i j)) * cert.stage2.v_r j))
      _ = sumFin r2 (fun i => sumFin r2 (fun j => sumFin r2 (fun k =>
            lw i * (coeffs k * matPow cert.stage2.M k.val i j) * cert.stage2.v_r j))) := by
          apply sumFin_congr; intro i
          rw [← sumFin_mul_left]
          apply sumFin_congr; intro j
          rw [← sumFin_mul_right, ← sumFin_mul_left]
          apply sumFin_congr; intro k
          exact (Int.mul_assoc _ _ _).symm
      _ = sumFin r2 (fun i => sumFin r2 (fun k => sumFin r2 (fun j =>
            lw i * (coeffs k * matPow cert.stage2.M k.val i j) * cert.stage2.v_r j))) := by
          apply sumFin_congr; intro i
          exact sumFin_swap _
      _ = sumFin r2 (fun k => sumFin r2 (fun i => sumFin r2 (fun j =>
            lw i * (coeffs k * matPow cert.stage2.M k.val i j) * cert.stage2.v_r j))) :=
          sumFin_swap _
      _ = sumFin r2 (fun k => coeffs k * sumFin r2 (fun i => lw i * sumFin r2 (fun j =>
            matPow cert.stage2.M k.val i j * cert.stage2.v_r j))) := by
          apply sumFin_congr; intro k
          rw [← sumFin_mul_left]
          apply sumFin_congr; intro i
          rw [← sumFin_mul_left, ← sumFin_mul_left]
          apply sumFin_congr; intro j
          calc lw i * (coeffs k * matPow cert.stage2.M k.val i j) * cert.stage2.v_r j
            _ = (lw i * coeffs k) * (matPow cert.stage2.M k.val i j * cert.stage2.v_r j) := by
                rw [← Int.mul_assoc, Int.mul_assoc (lw i * coeffs k)]
            _ = coeffs k * (lw i * (matPow cert.stage2.M k.val i j * cert.stage2.v_r j)) := by
                rw [Int.mul_comm (lw i) (coeffs k), Int.mul_assoc]
  change vecDot lw (matVec (matLinearComb cert.stage2.M coeffs) cert.stage2.v_r) = _
  rw [hstep]
  apply sumFin_congr; intro k
  congr 1
  dsimp only [lw]
  rw [matPow_add, matVec_matMul, ← vecDot_matVec]

-- Rank-1 exact exponential closed form corollary: r2 = 1 -> transferSeq = u2[0] * v2[0] * M[0,0]^w
theorem matPow_one_dim (M : Mat 1 1) (w : Nat) :
    matPow M w ⟨0, by omega⟩ ⟨0, by omega⟩ = (M ⟨0, by omega⟩ ⟨0, by omega⟩) ^ w := by
  induction w with
  | zero => simp [matPow, matId]
  | succ w ih =>
    simp only [matPow, matMul, sumFin, Int.zero_add]
    change M ⟨0, by omega⟩ ⟨0, by omega⟩ * matPow M w ⟨0, by omega⟩ ⟨0, by omega⟩ = _
    rw [ih, Int.pow_succ, Int.mul_comm]

theorem transferSeq_one_dim (u : Vec 1) (M : Mat 1 1) (v : Vec 1) (w : Nat) :
    transferSeq u M v w =
    (u ⟨0, by omega⟩ * v ⟨0, by omega⟩) * (M ⟨0, by omega⟩ ⟨0, by omega⟩) ^ w := by
  unfold transferSeq vecDot matVec
  simp only [sumFin, Int.zero_add]
  change u ⟨0, by omega⟩ * (matPow M w ⟨0, by omega⟩ ⟨0, by omega⟩ * v ⟨0, by omega⟩) = _
  rw [matPow_one_dim]
  calc u ⟨0, by omega⟩ * ((M ⟨0, by omega⟩ ⟨0, by omega⟩) ^ w * v ⟨0, by omega⟩)
    _ = u ⟨0, by omega⟩ * (v ⟨0, by omega⟩ * (M ⟨0, by omega⟩ ⟨0, by omega⟩) ^ w) := by rw [Int.mul_comm (_ ^ w)]
    _ = (u ⟨0, by omega⟩ * v ⟨0, by omega⟩) * (M ⟨0, by omega⟩ ⟨0, by omega⟩) ^ w := (Int.mul_assoc _ _ _).symm

-- --- ENGINE D: Pointwise MPS & MPO Two-Stage Gauge-Intertwiner Engine ---

structure MPSGaugeRightCert (D1 D2 : Nat) where
  d : Int
  P : Mat D1 D2

def checkMPSGaugeRightCert {D1 D2 : Nat} (M1 : MPS D1) (M2 : MPS D2)
    (cert : MPSGaugeRightCert D1 D2) : Bool :=
  decide (cert.d ≠ 0) &&
  matEq (matMul (M1.A false) cert.P) (matMul cert.P (M2.A false)) &&
  matEq (matMul (M1.A true) cert.P) (matMul cert.P (M2.A true)) &&
  vecEq (matVec cert.P M2.R) (vecScale cert.d M1.R) &&
  vecEq (vecMat M1.L cert.P) M2.L

theorem sound_mpsGaugeRightAux {D1 D2 : Nat} (M1 : MPS D1) (M2 : MPS D2)
    (d : Int) (P : Mat D1 D2)
    (hA : ∀ b, matMul (M1.A b) P = matMul P (M2.A b))
    (hR : matVec P M2.R = vecScale d M1.R) :
    ∀ (w : Nat) (u1 : Vec D1) (x : Nat),
      d * M1.evalAux w u1 x = M2.evalAux w (vecMat u1 P) x := by
  intro w
  induction w with
  | zero =>
    intro u1 x
    simp only [MPS.evalAux]
    rw [← vecDot_scale_right, ← hR, vecDot_matVec]
  | succ w ih =>
    intro u1 x
    simp only [MPS.evalAux]
    rw [ih (vecMat u1 (M1.A (x % 2 == 1))) (x / 2)]
    rw [← vecMat_matMul, hA (x % 2 == 1), vecMat_matMul]

theorem sound_mpsGaugeRightCert {D1 D2 : Nat} {M1 : MPS D1} {M2 : MPS D2}
    {cert : MPSGaugeRightCert D1 D2} (h : checkMPSGaugeRightCert M1 M2 cert = true) :
    ∀ (w x : Nat), cert.d * M1.eval w x = M2.eval w x := by
  simp only [checkMPSGaugeRightCert, Bool.and_eq_true] at h
  have hA : ∀ b, matMul (M1.A b) cert.P = matMul cert.P (M2.A b) := by
    intro b; cases b
    · exact matEq_eq_true h.1.1.1.2
    · exact matEq_eq_true h.1.1.2
  have hR : matVec cert.P M2.R = vecScale cert.d M1.R := vecEq_eq_true h.1.2
  have hL : vecMat M1.L cert.P = M2.L := vecEq_eq_true h.2
  intro w x
  unfold MPS.eval
  rw [sound_mpsGaugeRightAux M1 M2 cert.d cert.P hA hR w M1.L x, hL]

structure MPSGaugeLeftCert (D1 D2 : Nat) where
  d : Int
  Q : Mat D2 D1

def checkMPSGaugeLeftCert {D1 D2 : Nat} (M1 : MPS D1) (M2 : MPS D2)
    (cert : MPSGaugeLeftCert D1 D2) : Bool :=
  decide (cert.d ≠ 0) &&
  matEq (matMul cert.Q (M1.A false)) (matMul (M2.A false) cert.Q) &&
  matEq (matMul cert.Q (M1.A true)) (matMul (M2.A true) cert.Q) &&
  vecEq (vecMat M2.L cert.Q) (vecScale cert.d M1.L) &&
  vecEq (matVec cert.Q M1.R) M2.R

theorem mps_evalAux_scale_public {D : Nat} (M : MPS D) :
    ∀ (w : Nat) (c : Int) (u : Vec D) (x : Nat),
      M.evalAux w (vecScale c u) x = c * M.evalAux w u x := by
  intro w
  induction w with
  | zero => intro c u x; exact vecDot_scale_left c u M.R
  | succ w ih =>
    intro c u x
    simp only [MPS.evalAux, vecMat_scale]
    exact ih c _ _

theorem sound_mpsGaugeLeftAux {D1 D2 : Nat} (M1 : MPS D1) (M2 : MPS D2)
    (Q : Mat D2 D1)
    (hA : ∀ b, matMul Q (M1.A b) = matMul (M2.A b) Q)
    (hR : matVec Q M1.R = M2.R) :
    ∀ (w : Nat) (u2 : Vec D2) (x : Nat),
      M1.evalAux w (vecMat u2 Q) x = M2.evalAux w u2 x := by
  intro w
  induction w with
  | zero =>
    intro u2 x
    simp only [MPS.evalAux]
    rw [← vecDot_matVec, hR]
  | succ w ih =>
    intro u2 x
    simp only [MPS.evalAux]
    rw [← vecMat_matMul, hA (x % 2 == 1), vecMat_matMul]
    exact ih (vecMat u2 (M2.A (x % 2 == 1))) (x / 2)

theorem sound_mpsGaugeLeftCert {D1 D2 : Nat} {M1 : MPS D1} {M2 : MPS D2}
    {cert : MPSGaugeLeftCert D1 D2} (h : checkMPSGaugeLeftCert M1 M2 cert = true) :
    ∀ (w x : Nat), cert.d * M1.eval w x = M2.eval w x := by
  simp only [checkMPSGaugeLeftCert, Bool.and_eq_true] at h
  have hA : ∀ b, matMul cert.Q (M1.A b) = matMul (M2.A b) cert.Q := by
    intro b; cases b
    · exact matEq_eq_true h.1.1.1.2
    · exact matEq_eq_true h.1.1.2
  have hL : vecMat M2.L cert.Q = vecScale cert.d M1.L := vecEq_eq_true h.1.2
  have hR : matVec cert.Q M1.R = M2.R := vecEq_eq_true h.2
  intro w x
  unfold MPS.eval
  rw [← mps_evalAux_scale_public, ← hL]
  exact sound_mpsGaugeLeftAux M1 M2 cert.Q hA hR w M2.L x

structure MPOGaugeRightCert (D1 D2 : Nat) where
  d : Int
  P : Mat D1 D2

def checkMPOGaugeRightCert {D1 D2 : Nat} (O1 : MPO D1) (O2 : MPO D2)
    (cert : MPOGaugeRightCert D1 D2) : Bool :=
  decide (cert.d ≠ 0) &&
  matEq (matMul (O1.W false false) cert.P) (matMul cert.P (O2.W false false)) &&
  matEq (matMul (O1.W false true) cert.P) (matMul cert.P (O2.W false true)) &&
  matEq (matMul (O1.W true false) cert.P) (matMul cert.P (O2.W true false)) &&
  matEq (matMul (O1.W true true) cert.P) (matMul cert.P (O2.W true true)) &&
  vecEq (matVec cert.P O2.R) (vecScale cert.d O1.R) &&
  vecEq (vecMat O1.L cert.P) O2.L

theorem sound_mpoGaugeRightAux {D1 D2 : Nat} (O1 : MPO D1) (O2 : MPO D2)
    (d : Int) (P : Mat D1 D2)
    (hW : ∀ b1 b2, matMul (O1.W b1 b2) P = matMul P (O2.W b1 b2))
    (hR : matVec P O2.R = vecScale d O1.R) :
    ∀ (w : Nat) (u1 : Vec D1) (x y : Nat),
      d * O1.evalAux w u1 x y = O2.evalAux w (vecMat u1 P) x y := by
  intro w
  induction w with
  | zero =>
    intro u1 x y
    simp only [MPO.evalAux]
    rw [← vecDot_scale_right, ← hR, vecDot_matVec]
  | succ w ih =>
    intro u1 x y
    simp only [MPO.evalAux]
    rw [ih (vecMat u1 (O1.W (x % 2 == 1) (y % 2 == 1))) (x / 2) (y / 2)]
    rw [← vecMat_matMul, hW (x % 2 == 1) (y % 2 == 1), vecMat_matMul]

theorem sound_mpoGaugeRightCert {D1 D2 : Nat} {O1 : MPO D1} {O2 : MPO D2}
    {cert : MPOGaugeRightCert D1 D2} (h : checkMPOGaugeRightCert O1 O2 cert = true) :
    ∀ (w x y : Nat), cert.d * O1.eval w x y = O2.eval w x y := by
  simp only [checkMPOGaugeRightCert, Bool.and_eq_true] at h
  have hW : ∀ b1 b2, matMul (O1.W b1 b2) cert.P = matMul cert.P (O2.W b1 b2) := by
    intro b1 b2; cases b1 <;> cases b2
    · exact matEq_eq_true h.1.1.1.1.1.2
    · exact matEq_eq_true h.1.1.1.1.2
    · exact matEq_eq_true h.1.1.1.2
    · exact matEq_eq_true h.1.1.2
  have hR : matVec cert.P O2.R = vecScale cert.d O1.R := vecEq_eq_true h.1.2
  have hL : vecMat O1.L cert.P = O2.L := vecEq_eq_true h.2
  intro w x y
  unfold MPO.eval
  rw [sound_mpoGaugeRightAux O1 O2 cert.d cert.P hW hR w O1.L x y, hL]

structure MPOGaugeLeftCert (D1 D2 : Nat) where
  d : Int
  Q : Mat D2 D1

def checkMPOGaugeLeftCert {D1 D2 : Nat} (O1 : MPO D1) (O2 : MPO D2)
    (cert : MPOGaugeLeftCert D1 D2) : Bool :=
  decide (cert.d ≠ 0) &&
  matEq (matMul cert.Q (O1.W false false)) (matMul (O2.W false false) cert.Q) &&
  matEq (matMul cert.Q (O1.W false true)) (matMul (O2.W false true) cert.Q) &&
  matEq (matMul cert.Q (O1.W true false)) (matMul (O2.W true false) cert.Q) &&
  matEq (matMul cert.Q (O1.W true true)) (matMul (O2.W true true) cert.Q) &&
  vecEq (vecMat O2.L cert.Q) (vecScale cert.d O1.L) &&
  vecEq (matVec cert.Q O1.R) O2.R

theorem sound_mpoGaugeLeftAux {D1 D2 : Nat} (O1 : MPO D1) (O2 : MPO D2)
    (Q : Mat D2 D1)
    (hW : ∀ b1 b2, matMul Q (O1.W b1 b2) = matMul (O2.W b1 b2) Q)
    (hR : matVec Q O1.R = O2.R) :
    ∀ (w : Nat) (u2 : Vec D2) (x y : Nat),
      O1.evalAux w (vecMat u2 Q) x y = O2.evalAux w u2 x y := by
  intro w
  induction w with
  | zero =>
    intro u2 x y
    simp only [MPO.evalAux]
    rw [← vecDot_matVec, hR]
  | succ w ih =>
    intro u2 x y
    simp only [MPO.evalAux]
    rw [← vecMat_matMul, hW (x % 2 == 1) (y % 2 == 1), vecMat_matMul]
    exact ih (vecMat u2 (O2.W (x % 2 == 1) (y % 2 == 1))) (x / 2) (y / 2)

theorem mpo_evalAux_scale {D : Nat} (O : MPO D) :
    ∀ (w : Nat) (c : Int) (u : Vec D) (x y : Nat),
      O.evalAux w (vecScale c u) x y = c * O.evalAux w u x y := by
  intro w
  induction w with
  | zero => intro c u x y; exact vecDot_scale_left c u O.R
  | succ w ih =>
    intro c u x y
    simp only [MPO.evalAux, vecMat_scale]
    exact ih c _ _ _

theorem sound_mpoGaugeLeftCert {D1 D2 : Nat} {O1 : MPO D1} {O2 : MPO D2}
    {cert : MPOGaugeLeftCert D1 D2} (h : checkMPOGaugeLeftCert O1 O2 cert = true) :
    ∀ (w x y : Nat), cert.d * O1.eval w x y = O2.eval w x y := by
  simp only [checkMPOGaugeLeftCert, Bool.and_eq_true] at h
  have hW : ∀ b1 b2, matMul cert.Q (O1.W b1 b2) = matMul (O2.W b1 b2) cert.Q := by
    intro b1 b2; cases b1 <;> cases b2
    · exact matEq_eq_true h.1.1.1.1.1.2
    · exact matEq_eq_true h.1.1.1.1.2
    · exact matEq_eq_true h.1.1.1.2
    · exact matEq_eq_true h.1.1.2
  have hL : vecMat O2.L cert.Q = vecScale cert.d O1.L := vecEq_eq_true h.1.2
  have hR : matVec cert.Q O1.R = O2.R := vecEq_eq_true h.2
  intro w x y
  unfold MPO.eval
  rw [← mpo_evalAux_scale, ← hL]
  exact sound_mpoGaugeLeftAux O1 O2 cert.Q hW hR w O2.L x y

-- ============================================================================
-- PART 4: Concrete Pure-Silicon Binary Functions & Semantic Tensor Bridges
-- ============================================================================

-- Helper constructors for small concrete vectors and matrices
def vec1 (a : Int) : Vec 1 := fun _ => a
def vec2 (a b : Int) : Vec 2 := fun i => match i.val with | 0 => a | _ => b
def vec3 (a b c : Int) : Vec 3 := fun i => match i.val with | 0 => a | 1 => b | _ => c

def mat11 (a : Int) : Mat 1 1 := fun _ _ => a
def mat22 (a b c d : Int) : Mat 2 2 := fun i j =>
  match i.val, j.val with
  | 0, 0 => a | 0, 1 => b | 1, 0 => c | _, _ => d

def mat33 (r0 r1 r2 : Vec 3) : Mat 3 3 := fun i =>
  match i.val with | 0 => r0 | 1 => r1 | _ => r2

def vecOfList {D : Nat} (xs : List Int) : Vec D :=
  fun i => xs.getD i.val 0

def matOfLists {R C : Nat} (rows : List (List Int)) : Mat R C :=
  fun i j => (rows.getD i.val []).getD j.val 0

def carriesIntAux : Nat → Nat → Nat → Nat → Nat
  | _, 0, _, _ => 0
  | c, w + 1, x, y =>
      let c' := (x % 2 + y % 2 + c) / 2
      c + carriesIntAux c' w (x / 2) (y / 2)

def carriesInt (w x y : Nat) : Nat := carriesIntAux 0 w x y

def modInc (w x : Nat) : Nat := (x + 1) % (2 ^ w)

def grayCode (w x : Nat) : Nat := (x % (2 ^ w)) ^^^ ((x % (2 ^ w)) / 2)

-- Exact Bond-Dimension-1 & 2 MPS / MPO Realizations

def carryMPO (q : Int) : MPO 2 :=
  { L := vec2 1 0
    W := fun bx by_ =>
      let xb : Nat := if bx then 1 else 0
      let yb : Nat := if by_ then 1 else 0
      fun c c' =>
        let cnext := (xb + yb + c.val) / 2
        if c'.val = cnext then (if cnext = 1 then q else 1) else 0
    R := vec2 1 1 }

def carryIntMPO (q : Int) : MPO 2 :=
  { L := vec2 1 0
    W := fun bx by_ =>
      let xb : Nat := if bx then 1 else 0
      let yb : Nat := if by_ then 1 else 0
      fun c c' =>
        let cnext := (xb + yb + c.val) / 2
        if c'.val = cnext then (if c.val = 1 then q else 1) else 0
    R := vec2 1 1 }

def borrowMPO (q : Int) : MPO 2 :=
  { L := vec2 1 0
    W := fun bx by_ =>
      let xb : Nat := if bx then 1 else 0
      let yb : Nat := if by_ then 1 else 0
      fun b b' =>
        let bnext := if xb < yb + b.val then 1 else 0
        if b'.val = bnext then (if bnext = 1 then q else 1) else 0
    R := vec2 1 1 }

def hadamardMPO : MPO 1 :=
  { L := vec1 1
    W := fun bx by_ => mat11 (if bx && by_ then -1 else 1)
    R := vec1 1 }

def idMPO : MPO 1 :=
  { L := vec1 1
    W := fun bx by_ => mat11 (if bx == by_ then 1 else 0)
    R := vec1 1 }

def incMPO : MPO 2 :=
  { L := vec2 0 1
    W := fun bx by_ =>
      fun c c' =>
        let cb : Bool := (c.val == 1)
        let c'b : Bool := (c'.val == 1)
        if (by_ == xor bx cb) && (c'b == (bx && cb)) then 1 else 0
    R := vec2 1 1 }

def grayMPO : MPO 2 :=
  { L := vec2 1 1
    W := fun bx by_ =>
      fun s s' =>
        let sb : Bool := (s.val == 1)
        let s'b : Bool := (s'.val == 1)
        if (sb == bx) && (s'b == xor bx by_) then 1 else 0
    R := vec2 1 0 }

def tmMPS : MPS 1 :=
  { L := vec1 1
    A := fun b => mat11 (if b then -1 else 1)
    R := vec1 1 }

def rsMPS : MPS 2 :=
  { L := vec2 1 0
    A := fun b => if b then mat22 0 1 0 (-1) else mat22 1 0 1 0
    R := vec2 1 1 }

-- Basis vector helper for 2-state automata bridges
def e2 (b : Bool) : Vec 2 := if b then vec2 0 1 else vec2 1 0

private theorem mps_evalAux_scale {D : Nat} (M : MPS D) :
    ∀ (w : Nat) (c : Int) (u : Vec D) (x : Nat),
      M.evalAux w (vecScale c u) x = c * M.evalAux w u x := by
  intro w
  induction w with
  | zero => intro c u x; exact vecDot_scale_left c u M.R
  | succ w ih =>
    intro c u x
    simp only [MPS.evalAux, vecMat_scale]
    exact ih c _ _

-- Core Lean 4 helper for modulo 2*m
private theorem mod_two_mul (x m : Nat) : x % (2 * m) = x % 2 + 2 * ((x / 2) % m) := by
  by_cases hm : m = 0
  · subst hm; simp; omega
  · have hpos : 0 < m := by omega
    have h1 : x = x % 2 + 2 * (x / 2) := by omega
    have h2 : x / 2 = (x / 2) % m + m * ((x / 2) / m) := by
      have := Nat.div_add_mod (x / 2) m; omega
    have hma : 2 * (m * ((x / 2) / m)) = (2 * m) * ((x / 2) / m) := (Nat.mul_assoc 2 m _).symm
    have hmul : 2 * (x / 2) = 2 * ((x / 2) % m) + (2 * m) * ((x / 2) / m) := by
      rw [← hma, ← Nat.mul_add, ← h2]
    have h3 : x = (x % 2 + 2 * ((x / 2) % m)) + (2 * m) * ((x / 2) / m) := by omega
    have hlt : x % 2 + 2 * ((x / 2) % m) < 2 * m := by
      have hm1 : (x / 2) % m < m := Nat.mod_lt _ hpos
      omega
    calc x % (2 * m)
      _ = ((x % 2 + 2 * ((x / 2) % m)) + (2 * m) * ((x / 2) / m)) % (2 * m) := by rw [← h3]
      _ = (x % 2 + 2 * ((x / 2) % m)) % (2 * m) := Nat.add_mul_mod_self_left _ _ _
      _ = x % 2 + 2 * ((x / 2) % m) := Nat.mod_eq_of_lt hlt

-- Semantic Bridge 1: carryMPO q
private theorem carryMPO_step (q : Int) (c bx by_ : Bool) :
    let xb : Nat := if bx then 1 else 0
    let yb : Nat := if by_ then 1 else 0
    let cb : Nat := if c then 1 else 0
    let cnext := (xb + yb + cb) / 2
    vecMat (e2 c) ((carryMPO q).W bx by_) =
      vecScale (if cnext = 1 then q else 1) (e2 (cnext == 1)) := by
  cases c <;> cases bx <;> cases by_ <;>
  · funext ⟨j, hj⟩
    match j with
    | 0 => simp [vecMat, sumFin, e2, carryMPO, vec2, vecScale]
    | 1 => simp [vecMat, sumFin, e2, carryMPO, vec2, vecScale]
    | _ + 2 => omega

theorem carryMPO_evalAux (q : Int) :
    ∀ (w : Nat) (c : Bool) (x y : Nat),
      (carryMPO q).evalAux w (e2 c) x y = q ^ carriesAux (if c then 1 else 0) w x y := by
  intro w
  induction w with
  | zero =>
    intro c x y
    cases c <;> simp [MPO.evalAux, carriesAux, e2, carryMPO, vecDot, sumFin, vec2]
  | succ w ih =>
    intro c x y
    simp only [MPO.evalAux, carriesAux]
    have hstep := carryMPO_step q c (x % 2 == 1) (y % 2 == 1)
    dsimp only at hstep
    rw [hstep, mpo_evalAux_scale, ih]
    have hx : x % 2 = 0 ∨ x % 2 = 1 := by omega
    have hy : y % 2 = 0 ∨ y % 2 = 1 := by omega
    cases c <;> rcases hx with hx | hx <;> rcases hy with hy | hy <;>
      simp [hx, hy, Int.pow_add, Int.pow_one]

theorem carryMPO_eval (q : Int) (w x y : Nat) :
    (carryMPO q).eval w x y = q ^ carries w x y :=
  carryMPO_evalAux q w false x y

-- Semantic Bridge 2: carryIntMPO q
private theorem carryIntMPO_step (q : Int) (c bx by_ : Bool) :
    let xb : Nat := if bx then 1 else 0
    let yb : Nat := if by_ then 1 else 0
    let cb : Nat := if c then 1 else 0
    let cnext := (xb + yb + cb) / 2
    vecMat (e2 c) ((carryIntMPO q).W bx by_) =
      vecScale (if c then q else 1) (e2 (cnext == 1)) := by
  cases c <;> cases bx <;> cases by_ <;>
  · funext ⟨j, hj⟩
    match j with
    | 0 => simp [vecMat, sumFin, e2, carryIntMPO, vec2, vecScale]
    | 1 => simp [vecMat, sumFin, e2, carryIntMPO, vec2, vecScale]
    | _ + 2 => omega

theorem carryIntMPO_evalAux (q : Int) :
    ∀ (w : Nat) (c : Bool) (x y : Nat),
      (carryIntMPO q).evalAux w (e2 c) x y = q ^ carriesIntAux (if c then 1 else 0) w x y := by
  intro w
  induction w with
  | zero =>
    intro c x y
    cases c <;> simp [MPO.evalAux, carriesIntAux, e2, carryIntMPO, vecDot, sumFin, vec2]
  | succ w ih =>
    intro c x y
    simp only [MPO.evalAux, carriesIntAux]
    have hstep := carryIntMPO_step q c (x % 2 == 1) (y % 2 == 1)
    dsimp only at hstep
    rw [hstep, mpo_evalAux_scale, ih]
    have hx : x % 2 = 0 ∨ x % 2 = 1 := by omega
    have hy : y % 2 = 0 ∨ y % 2 = 1 := by omega
    cases c <;> rcases hx with hx | hx <;> rcases hy with hy | hy <;>
      simp [hx, hy, Int.pow_add, Int.pow_one]

theorem carryIntMPO_eval (q : Int) (w x y : Nat) :
    (carryIntMPO q).eval w x y = q ^ carriesInt w x y :=
  carryIntMPO_evalAux q w false x y

-- Semantic Bridge 3: borrowMPO q
private theorem borrowMPO_step (q : Int) (b bx by_ : Bool) :
    let xb : Nat := if bx then 1 else 0
    let yb : Nat := if by_ then 1 else 0
    let bb : Nat := if b then 1 else 0
    let bnext := if xb < yb + bb then 1 else 0
    vecMat (e2 b) ((borrowMPO q).W bx by_) =
      vecScale (if bnext = 1 then q else 1) (e2 (bnext == 1)) := by
  cases b <;> cases bx <;> cases by_ <;>
  · funext ⟨j, hj⟩
    match j with
    | 0 => simp [vecMat, sumFin, e2, borrowMPO, vec2, vecScale]
    | 1 => simp [vecMat, sumFin, e2, borrowMPO, vec2, vecScale]
    | _ + 2 => omega

theorem borrowMPO_evalAux (q : Int) :
    ∀ (w : Nat) (b : Bool) (x y : Nat),
      (borrowMPO q).evalAux w (e2 b) x y = q ^ borrowsAux (if b then 1 else 0) w x y := by
  intro w
  induction w with
  | zero =>
    intro b x y
    cases b <;> simp [MPO.evalAux, borrowsAux, e2, borrowMPO, vecDot, sumFin, vec2]
  | succ w ih =>
    intro b x y
    simp only [MPO.evalAux, borrowsAux]
    have hstep := borrowMPO_step q b (x % 2 == 1) (y % 2 == 1)
    dsimp only at hstep
    rw [hstep, mpo_evalAux_scale, ih]
    have hx : x % 2 = 0 ∨ x % 2 = 1 := by omega
    have hy : y % 2 = 0 ∨ y % 2 = 1 := by omega
    cases b <;> rcases hx with hx | hx <;> rcases hy with hy | hy <;>
      simp [hx, hy, Int.pow_add, Int.pow_one]

theorem borrowMPO_eval (q : Int) (w x y : Nat) :
    (borrowMPO q).eval w x y = q ^ borrows w x y :=
  borrowMPO_evalAux q w false x y

-- Semantic Bridge 4: hadamardMPO
theorem hadamardMPO_eval (w x y : Nat) :
    hadamardMPO.eval w x y = walshHadamard w x y := by
  unfold MPO.eval walshHadamard
  induction w generalizing x y with
  | zero => simp [MPO.evalAux, bitAndPopcount, hadamardMPO, vecDot, sumFin, vec1]
  | succ w ih =>
    simp only [MPO.evalAux, bitAndPopcount]
    have hx : x % 2 = 0 ∨ x % 2 = 1 := by omega
    have hy : y % 2 = 0 ∨ y % 2 = 1 := by omega
    have hvm : vecMat hadamardMPO.L (hadamardMPO.W (x % 2 == 1) (y % 2 == 1)) =
        vecScale (if (x % 2 == 1) && (y % 2 == 1) then -1 else 1) hadamardMPO.L := by
      funext ⟨j, hj⟩
      match j with
      | 0 => rcases hx with hx | hx <;> rcases hy with hy | hy <;>
          simp [vecMat, sumFin, hadamardMPO, vec1, mat11, vecScale, hx, hy]
      | _ + 1 => omega
    rw [hvm, mpo_evalAux_scale, ih (x / 2) (y / 2)]
    rcases hx with hx | hx <;> rcases hy with hy | hy <;>
      simp [hx, hy, Int.pow_add, Int.pow_one]

-- Semantic Bridge 5: idMPO
theorem idMPO_eval (w x y : Nat) :
    idMPO.eval w x y = if x % (2 ^ w) = y % (2 ^ w) then 1 else 0 := by
  unfold MPO.eval
  induction w generalizing x y with
  | zero => simp [MPO.evalAux, idMPO, vecDot, sumFin, vec1, Nat.mod_one]
  | succ w ih =>
    simp only [MPO.evalAux]
    have hx : x % 2 = 0 ∨ x % 2 = 1 := by omega
    have hy : y % 2 = 0 ∨ y % 2 = 1 := by omega
    have hvm : vecMat idMPO.L (idMPO.W (x % 2 == 1) (y % 2 == 1)) =
        vecScale (if (x % 2 == 1) == (y % 2 == 1) then 1 else 0) idMPO.L := by
      funext ⟨j, hj⟩
      match j with
      | 0 => rcases hx with hx | hx <;> rcases hy with hy | hy <;>
          simp [vecMat, sumFin, idMPO, vec1, mat11, vecScale, hx, hy]
      | _ + 1 => omega
    rw [hvm, mpo_evalAux_scale, ih (x / 2) (y / 2)]
    have hmod : (x % (2 ^ (w + 1)) = y % (2 ^ (w + 1))) ↔
        (x % 2 = y % 2 ∧ (x / 2) % (2 ^ w) = (y / 2) % (2 ^ w)) := by
      have hp : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [hp, mod_two_mul, mod_two_mul]
      constructor
      · intro h; constructor <;> omega
      · intro ⟨h1, h2⟩; rw [h1, h2]
    rcases hx with hx | hx <;> rcases hy with hy | hy <;>
      simp [hx, hy, hmod]

-- Semantic Bridge 6: incMPO
private theorem incMPO_step (c bx by_ : Bool) :
    vecMat (e2 c) (incMPO.W bx by_) =
      if by_ == xor bx c then e2 (bx && c) else vecZero 2 := by
  cases c <;> cases bx <;> cases by_ <;>
  · funext ⟨j, hj⟩
    match j with
    | 0 => simp [vecMat, sumFin, e2, incMPO, vec2, vecZero]
    | 1 => simp [vecMat, sumFin, e2, incMPO, vec2, vecZero]
    | _ + 2 => omega

private theorem mpo_evalAux_zero {D : Nat} (O : MPO D) (w x y : Nat) :
    O.evalAux w (vecZero D) x y = 0 := by
  have h : vecZero D = vecScale 0 (vecZero D) := by funext i; simp [vecZero, vecScale]
  rw [h, mpo_evalAux_scale, Int.zero_mul]

theorem incMPO_evalAux :
    ∀ (w : Nat) (c : Bool) (x y : Nat),
      incMPO.evalAux w (e2 c) x y =
        if y % (2 ^ w) = (x + if c then 1 else 0) % (2 ^ w) then 1 else 0 := by
  intro w
  induction w with
  | zero =>
    intro c x y
    cases c <;> simp [MPO.evalAux, e2, incMPO, vecDot, sumFin, vec2, Nat.mod_one]
  | succ w ih =>
    intro c x y
    simp only [MPO.evalAux]
    rw [incMPO_step]
    have hx : x % 2 = 0 ∨ x % 2 = 1 := by omega
    have hy : y % 2 = 0 ∨ y % 2 = 1 := by omega
    have hsplit : ∀ a b : Nat, (a % (2 ^ (w + 1)) = b % (2 ^ (w + 1))) ↔
        (a % 2 = b % 2 ∧ (a / 2) % (2 ^ w) = (b / 2) % (2 ^ w)) := by
      intro a b
      have hp : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [hp, mod_two_mul, mod_two_mul]
      constructor
      · intro h; constructor <;> omega
      · intro ⟨h1, h2⟩; rw [h1, h2]
    cases c <;> rcases hx with hx | hx <;> rcases hy with hy | hy
    · have h1 : (y % 2 == 1) = false := by simp [hy]
      have h2 : (x % 2 == 1) = false := by simp [hx]
      rw [h1, h2]; simp only [Bool.xor_false, beq_self_eq_true, ↓reduceIte, Bool.and_false, ih, hsplit]
      simp [hx, hy]
    · have h1 : (y % 2 == 1) = true := by simp [hy]
      have h2 : (x % 2 == 1) = false := by simp [hx]
      rw [h1, h2]; simp only [Bool.xor_false, beq_iff_eq, Bool.true_eq_false, ↓reduceIte, mpo_evalAux_zero, hsplit]
      simp [hx, hy]
    · have h1 : (y % 2 == 1) = false := by simp [hy]
      have h2 : (x % 2 == 1) = true := by simp [hx]
      rw [h1, h2]; simp only [Bool.xor_false, beq_iff_eq, Bool.false_eq_true, ↓reduceIte, mpo_evalAux_zero, hsplit]
      simp [hx, hy]
    · have h1 : (y % 2 == 1) = true := by simp [hy]
      have h2 : (x % 2 == 1) = true := by simp [hx]
      rw [h1, h2]; simp only [Bool.xor_false, beq_self_eq_true, ↓reduceIte, Bool.and_false, ih, hsplit]
      simp [hx, hy]
    · have h1 : (y % 2 == 1) = false := by simp [hy]
      have h2 : (x % 2 == 1) = false := by simp [hx]
      rw [h1, h2]; simp only [Bool.xor_true, Bool.not_false, beq_iff_eq, Bool.false_eq_true, ↓reduceIte, mpo_evalAux_zero, hsplit]
      have hmod : (x + 1) % 2 = 1 := by omega
      simp [hy, hmod]
    · have h1 : (y % 2 == 1) = true := by simp [hy]
      have h2 : (x % 2 == 1) = false := by simp [hx]
      rw [h1, h2]; simp only [Bool.xor_true, Bool.not_false, beq_self_eq_true, ↓reduceIte, Bool.false_and, ih, hsplit]
      have hmod : (x + 1) % 2 = 1 := by omega
      have hdiv : (x + 1) / 2 = x / 2 := by omega
      simp [hy, hmod, hdiv]
    · have h1 : (y % 2 == 1) = false := by simp [hy]
      have h2 : (x % 2 == 1) = true := by simp [hx]
      rw [h1, h2]; simp only [Bool.xor_true, Bool.not_true, beq_self_eq_true, ↓reduceIte, Bool.and_self, ih, hsplit]
      have hmod : (x + 1) % 2 = 0 := by omega
      have hdiv : (x + 1) / 2 = x / 2 + 1 := by omega
      simp [hy, hmod, hdiv]
    · have h1 : (y % 2 == 1) = true := by simp [hy]
      have h2 : (x % 2 == 1) = true := by simp [hx]
      rw [h1, h2]; simp only [Bool.xor_true, Bool.not_true, beq_iff_eq, Bool.true_eq_false, ↓reduceIte, mpo_evalAux_zero, hsplit]
      have hmod : (x + 1) % 2 = 0 := by omega
      simp [hy, hmod]

theorem incMPO_eval (w x y : Nat) :
    incMPO.eval w x y = if y % (2 ^ w) = modInc w x then 1 else 0 :=
  incMPO_evalAux w true x y

-- Semantic Bridge 7: tmMPS & rsMPS
theorem tmMPS_eval (w x : Nat) : tmMPS.eval w x = thueMorse w x := by
  unfold MPS.eval thueMorse
  induction w generalizing x with
  | zero => simp [MPS.evalAux, popcount, tmMPS, vecDot, sumFin, vec1]
  | succ w ih =>
    simp only [MPS.evalAux, popcount]
    have hx : x % 2 = 0 ∨ x % 2 = 1 := by omega
    have hvm : vecMat tmMPS.L (tmMPS.A (x % 2 == 1)) =
        vecScale (if x % 2 == 1 then -1 else 1) tmMPS.L := by
      funext ⟨j, hj⟩
      match j with
      | 0 => rcases hx with hx | hx <;> simp [vecMat, sumFin, tmMPS, vec1, mat11, vecScale, hx]
      | _ + 1 => omega
    rw [hvm, mps_evalAux_scale, ih (x / 2)]
    rcases hx with hx | hx <;> simp [hx, Int.pow_add, Int.pow_one]

private theorem rsMPS_step (prev bx : Bool) :
    vecMat (e2 prev) (rsMPS.A bx) =
      vecScale (if prev && bx then -1 else 1) (e2 bx) := by
  cases prev <;> cases bx <;>
  · funext ⟨j, hj⟩
    match j with
    | 0 => simp [vecMat, sumFin, e2, rsMPS, vec2, mat22, vecScale]
    | 1 => simp [vecMat, sumFin, e2, rsMPS, vec2, mat22, vecScale]
    | _ + 2 => omega

theorem rsMPS_evalAux :
    ∀ (w : Nat) (prev : Bool) (x : Nat),
      rsMPS.evalAux w (e2 prev) x = rudinShapiroAux prev w x := by
  intro w
  induction w with
  | zero =>
    intro prev x
    cases prev <;> simp [MPS.evalAux, rudinShapiroAux, e2, rsMPS, vecDot, sumFin, vec2]
  | succ w ih =>
    intro prev x
    simp only [MPS.evalAux, rudinShapiroAux]
    rw [rsMPS_step, mps_evalAux_scale, ih]

theorem rsMPS_eval (w x : Nat) : rsMPS.eval w x = rudinShapiro w x :=
  rsMPS_evalAux w false x

-- Semantic Bridge 8: grayMPO
private theorem grayMPO_step (s bx by_ : Bool) :
    vecMat (e2 s) (grayMPO.W bx by_) =
      if s == bx then e2 (xor bx by_) else vecZero 2 := by
  cases s <;> cases bx <;> cases by_ <;>
  · funext ⟨j, hj⟩
    match j with
    | 0 => simp [vecMat, sumFin, e2, grayMPO, vec2, vecZero]
    | 1 => simp [vecMat, sumFin, e2, grayMPO, vec2, vecZero]
    | _ + 2 => omega

theorem grayMPO_evalAux :
    ∀ (w : Nat) (s : Bool) (x y : Nat),
      grayMPO.evalAux w (e2 s) x y =
        if (y % (2 ^ w) = grayCode w x) ∧
           (if w = 0 then s = false else (x % 2 == 1) = s)
        then 1 else 0 := by
  intro w
  induction w with
  | zero =>
    intro s x y
    cases s <;> simp [MPO.evalAux, grayCode, e2, grayMPO, vecDot, sumFin, vec2, Nat.mod_one]
  | succ w ih =>
    intro s x y
    simp only [MPO.evalAux]
    rw [grayMPO_step]
    have hx : x % 2 = 0 ∨ x % 2 = 1 := by omega
    have hy : y % 2 = 0 ∨ y % 2 = 1 := by omega
    by_cases hs : s = (x % 2 == 1)
    · subst hs
      simp only [beq_self_eq_true, ↓reduceIte, ih]
      have hgray_split : (y % (2 ^ (w + 1)) = grayCode (w + 1) x) ↔
          ((y / 2) % (2 ^ w) = grayCode w (x / 2) ∧
           (if w = 0 then xor (x % 2 == 1) (y % 2 == 1) = false
            else ((x / 2) % 2 == 1) = xor (x % 2 == 1) (y % 2 == 1))) := by
        unfold grayCode
        have hp : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
        have hxmod : x % (2 ^ (w + 1)) = x % 2 + 2 * ((x / 2) % (2 ^ w)) := by
          rw [hp, mod_two_mul]
        have hxdiv : (x % (2 ^ (w + 1))) / 2 = (x / 2) % (2 ^ w) := by
          rw [hxmod]; omega
        have hxor_mod2 : ∀ a b : Nat, (a ^^^ b) % 2 = (a % 2 + b % 2) % 2 := by
          intro a b
          have htb : (a ^^^ b).testBit 0 = xor (a.testBit 0) (b.testBit 0) := Nat.testBit_xor a b 0
          rw [Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero] at htb
          have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
          have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
          have hab : (a ^^^ b) % 2 = 0 ∨ (a ^^^ b) % 2 = 1 := by omega
          rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hab with hab | hab <;>
            (rw [ha, hb, hab] at htb ⊢; try (simp at htb ⊢))
        have hxor_div2 : ∀ a b : Nat, (a ^^^ b) / 2 = (a / 2) ^^^ (b / 2) := by
          intro a b
          apply Nat.eq_of_testBit_eq
          intro i
          simp only [Nat.testBit_div_two, Nat.testBit_xor]
        have hsplit_eq : ∀ a b : Nat, (a = b) ↔ (a % 2 = b % 2 ∧ a / 2 = b / 2) := by
          intro a b; constructor
          · intro h; subst h; exact ⟨rfl, rfl⟩
          · intro ⟨h1, h2⟩; omega
        rw [hsplit_eq]
        have hymod_lsb : (y % (2 ^ (w + 1))) % 2 = y % 2 := by
          rw [hp, mod_two_mul]; omega
        have hymod_div : (y % (2 ^ (w + 1))) / 2 = (y / 2) % (2 ^ w) := by
          rw [hp, mod_two_mul]; omega
        rw [hymod_lsb, hymod_div, hxor_mod2, hxor_div2, hxdiv]
        have hxm_lsb : (x % (2 ^ (w + 1))) % 2 = x % 2 := by rw [hxmod]; omega
        rw [hxm_lsb]
        cases w with
        | zero =>
          simp only [Nat.pow_zero, Nat.mod_one, Nat.zero_xor, ↓reduceIte]
          rcases hx with hx | hx <;> rcases hy with hy | hy <;> simp [hx, hy]
        | succ w' =>
          have hxm2 : ((x / 2) % (2 ^ (w' + 1))) % 2 = (x / 2) % 2 := by
            have hp' : 2 ^ (w' + 1) = 2 * 2 ^ w' := by rw [Nat.pow_succ, Nat.mul_comm]
            rw [hp', mod_two_mul]; omega
          rw [hxm2]
          have hxd : (x / 2) % 2 = 0 ∨ (x / 2) % 2 = 1 := by omega
          simp only [Nat.succ_ne_zero, ↓reduceIte]
          rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hxd with hxd | hxd <;>
            simp [hx, hy, hxd, And.comm]
      simp [hgray_split]
    · have hbeq : (s == (x % 2 == 1)) = false := by
        cases s <;> cases h : (x % 2 == 1) <;> simp_all
      rw [hbeq]
      simp only [Bool.false_eq_true, ↓reduceIte, mpo_evalAux_zero]
      have hne : ¬((x % 2 == 1) = s) := fun h => hs h.symm
      simp [hne]

theorem grayMPO_eval (w x y : Nat) :
    grayMPO.eval w x y = if y % (2 ^ w) = grayCode w x then 1 else 0 := by
  have hL : grayMPO.L = vecAdd (e2 false) (e2 true) := by
    funext ⟨i, hi⟩
    match i with
    | 0 => simp [grayMPO, vecAdd, e2, vec2]
    | 1 => simp [grayMPO, vecAdd, e2, vec2]
    | _ + 2 => omega
  unfold MPO.eval
  rw [hL, mpo_evalAux_add, grayMPO_evalAux, grayMPO_evalAux]
  cases w with
  | zero => simp [grayCode, Nat.mod_one]
  | succ w =>
    cases h : (x % 2 == 1) <;> by_cases hg : y % (2 ^ (w + 1)) = grayCode (w + 1) x <;> simp [hg]

def rsCarryP (q : Int) : Mat 8 2 := fun i j =>
  match j.val with
  | 0 => 1
  | _ =>
    match i.val with
    | 0 => q + 3
    | 2 => 3 * q + 1
    | 5 => q - 1
    | _ => 1 - q

def rsCarryM (q : Int) : Mat 2 2 := mat22 0 (2 * (q + 1)) 1 (1 - q)
def rsCarryU (q : Int) : Vec 2 := vec2 1 (q + 3)
def rsCarryV : Vec 2 := vec2 1 0

def rsCarryRightCert (q : Int) : RightReductionCert 8 2 :=
  { w0 := 0, d := 1, M := rsCarryM q, P := rsCarryP q, u_r := rsCarryU q, v_r := rsCarryV }

theorem rsCarrySum_eq_transfer (q : Int) (w : Nat) :
    rsCarrySum q w =
    transferSeq (kronVec rsMPS.L (mpoApplyMPS (carryMPO q) rsMPS).L)
                (mpsInnerTM rsMPS (mpoApplyMPS (carryMPO q) rsMPS))
                (kronVec rsMPS.R (mpoApplyMPS (carryMPO q) rsMPS).R) w := by
  unfold rsCarrySum transferSeq
  rw [← mps_mpo_mps_eq_transfer rsMPS (carryMPO q) rsMPS w]
  apply sumNat_congr; intro x _
  apply sumNat_congr; intro y _
  rw [rsMPS_eval, rsMPS_eval, carryMPO_eval]

-- Exact finite-sum expanders (avoiding Fin numeral coercions during symbolic simp)
private theorem sumFin2_expand (f : Fin 2 → Int) :
    sumFin 2 f = f ⟨0, by omega⟩ + f ⟨1, by omega⟩ := by
  simp [sumFin]

private theorem sumFin8_expand (f : Fin 8 → Int) :
    sumFin 8 f = f ⟨0, by omega⟩ + f ⟨1, by omega⟩ + f ⟨2, by omega⟩ + f ⟨3, by omega⟩ +
                 f ⟨4, by omega⟩ + f ⟨5, by omega⟩ + f ⟨6, by omega⟩ + f ⟨7, by omega⟩ := by
  simp only [sumFin, Int.zero_add]; rfl

-- Symbolic verification of the 8×2 parametric certificate for ALL q : Int
private theorem fin4_val3 : (3 : Fin 4).val = 3 := rfl

set_option maxHeartbeats 800000 in
private theorem rsCarry_parametric_TP (q : Int) :
    matMul (mpsInnerTM rsMPS (mpoApplyMPS (carryMPO q) rsMPS)) (rsCarryP q) =
    matMul (rsCarryP q) (rsCarryM q) := by
  funext ⟨i, hi⟩ ⟨j, hj⟩
  unfold matMul
  rw [sumFin8_expand, sumFin2_expand]
  match i, j with
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 2, 0 | 2, 1 | 3, 0 | 3, 1
  | 4, 0 | 4, 1 | 5, 0 | 5, 1 | 6, 0 | 6, 1 | 7, 0 | 7, 1 =>
    simp [mpsInnerTM, mpoApplyMPS, matAdd, kronMat, rsMPS, carryMPO, rsCarryP, rsCarryM, mat22, fin4_val3]
    try grind
  | _ + 8, _ => omega
  | _, _ + 2 => omega

private theorem rsCarry_parametric_Pv (q : Int) :
    matVec (rsCarryP q) rsCarryV =
    vecScale 1 (matVec (matPow (mpsInnerTM rsMPS (mpoApplyMPS (carryMPO q) rsMPS)) 0)
      (kronVec rsMPS.R (mpoApplyMPS (carryMPO q) rsMPS).R)) := by
  funext ⟨i, hi⟩
  rw [matPow, matVec_id]
  unfold matVec
  rw [sumFin2_expand]
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 =>
    simp [rsCarryP, rsCarryV, vecScale, kronVec, rsMPS, mpoApplyMPS, carryMPO, vec2]
    try (split <;> rfl)
  | _ + 8 => omega

private theorem rsCarry_parametric_uP (q : Int) :
    vecMat (kronVec rsMPS.L (mpoApplyMPS (carryMPO q) rsMPS).L) (rsCarryP q) = rsCarryU q := by
  funext ⟨j, hj⟩
  unfold vecMat
  rw [sumFin8_expand]
  match j with
  | 0 | 1 =>
    simp [kronVec, rsMPS, mpoApplyMPS, carryMPO, rsCarryP, rsCarryU, vec2]
  | _ + 2 => omega

theorem rsCarrySum_eq_reduced (q : Int) (w : Nat) :
    rsCarrySum q w = transferSeq (rsCarryU q) (rsCarryM q) rsCarryV w := by
  rw [rsCarrySum_eq_transfer]
  have h1 : (1 : Int) * transferSeq (kronVec rsMPS.L (mpoApplyMPS (carryMPO q) rsMPS).L)
      (mpsInnerTM rsMPS (mpoApplyMPS (carryMPO q) rsMPS))
      (kronVec rsMPS.R (mpoApplyMPS (carryMPO q) rsMPS).R) (w + 0) =
      transferSeq (rsCarryU q) (rsCarryM q) rsCarryV w := by
    have hTP := rsCarry_parametric_TP q
    have hPv := rsCarry_parametric_Pv q
    have huP := rsCarry_parametric_uP q
    unfold transferSeq
    rw [Nat.add_zero, ← vecDot_scale_right]
    have hPv' : matVec (rsCarryP q) rsCarryV = vecScale 1 (kronVec rsMPS.R (mpoApplyMPS (carryMPO q) rsMPS).R) := by
      simpa [matPow, matVec_id] using hPv
    rw [← matVec_scale, ← hPv', ← matVec_matMul,
        matPow_intertwine_right _ _ _ hTP w, matVec_matMul, vecDot_matVec, huP]
  simpa using h1

-- Theorem 1a: Uniform Parametric Recurrence (∀ q : Int, ∀ w : Nat)
theorem thm_rs_carry_parametric_recurrence (q : Int) (w : Nat) :
    rsCarrySum q (w + 2) = (1 - q) * rsCarrySum q (w + 1) + 2 * (q + 1) * rsCarrySum q w := by
  rw [rsCarrySum_eq_reduced, rsCarrySum_eq_reduced, rsCarrySum_eq_reduced]
  unfold transferSeq
  have hM2 : matPow (rsCarryM q) 2 =
      matAdd (matScale (1 - q) (matPow (rsCarryM q) 1)) (matScale (2 * (q + 1)) (matPow (rsCarryM q) 0)) := by
    funext ⟨i, hi⟩ ⟨j, hj⟩
    match i, j with
    | 0, 0 | 0, 1 | 1, 0 | 1, 1 =>
      simp [matPow, matMul, matAdd, matScale, matId, sumFin, rsCarryM, mat22]
      try grind
    | _ + 2, _ => omega
    | _, _ + 2 => omega
  have hpow2 : matPow (rsCarryM q) (w + 2) = matMul (matPow (rsCarryM q) w) (matPow (rsCarryM q) 2) :=
    matPow_add _ w 2
  have hpow1 : matPow (rsCarryM q) (w + 1) = matMul (matPow (rsCarryM q) w) (matPow (rsCarryM q) 1) :=
    matPow_add _ w 1
  have hstep : ∀ (lw : Vec 2),
      vecDot lw (matVec (matAdd (matScale (1 - q) (matPow (rsCarryM q) 1))
        (matScale (2 * (q + 1)) (matPow (rsCarryM q) 0))) rsCarryV) =
      (1 - q) * vecDot lw (matVec (matPow (rsCarryM q) 1) rsCarryV) +
      2 * (q + 1) * vecDot lw rsCarryV := by
    intro lw
    unfold vecDot matVec matAdd matScale matPow matId
    simp only [sumFin]
    grind
  rw [hpow2, hM2, matVec_matMul, vecDot_matVec, hstep]
  rw [hpow1, matVec_matMul, ← vecDot_matVec, ← vecDot_matVec]

theorem rsCarrySum_zero (q : Int) : rsCarrySum q 0 = 1 := by
  rw [rsCarrySum_eq_reduced]
  simp [transferSeq, matPow, matVec_id, vecDot, sumFin, rsCarryU, rsCarryV, vec2]

theorem rsCarrySum_one (q : Int) : rsCarrySum q 1 = q + 3 := by
  rw [rsCarrySum_eq_reduced]
  simp [transferSeq, matPow, matMul, matId, matVec, vecDot, sumFin, rsCarryU, rsCarryM, rsCarryV, vec2, mat22]

-- Theorem 1b: Uniform Parametric Closed Form (∀ q : Int, ∀ w : Nat)
theorem thm_rs_carry_parametric_closed (q : Int) (w : Nat) :
    (q + 3) * rsCarrySum q w = (q + 2) * (2 : Int) ^ (w + 1) + (-(q + 1)) ^ (w + 1) := by
  suffices h : ∀ n : Nat,
      (q + 3) * rsCarrySum q n = (q + 2) * (2 : Int) ^ (n + 1) + (-(q + 1)) ^ (n + 1) ∧
      (q + 3) * rsCarrySum q (n + 1) = (q + 2) * (2 : Int) ^ (n + 2) + (-(q + 1)) ^ (n + 2) from
    (h w).1
  intro n
  induction n with
  | zero =>
    constructor
    · rw [rsCarrySum_zero]; simp only [Int.pow_succ, Int.pow_zero]; grind
    · rw [rsCarrySum_one]; simp only [Int.pow_succ, Int.pow_zero]; grind
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [thm_rs_carry_parametric_recurrence q n]
    have h1 := ih.1
    have h2 := ih.2
    have hpow2 : (2 : Int) ^ (n + 3) = 2 * (2 : Int) ^ (n + 2) := by rw [Int.pow_succ]; grind
    have hpow2' : (2 : Int) ^ (n + 2) = 2 * (2 : Int) ^ (n + 1) := by rw [Int.pow_succ]; grind
    have hpowq : (-(q + 1)) ^ (n + 3) = (-(q + 1)) * (-(q + 1)) ^ (n + 2) := by rw [Int.pow_succ]; grind
    have hpowq' : (-(q + 1)) ^ (n + 2) = (-(q + 1)) * (-(q + 1)) ^ (n + 1) := by rw [Int.pow_succ]; grind
    grind

-- Four Concrete Degenerate Regimes — ALSO independently certified via `decide` TwoStageCerts!

def cert_rsCarryNeg1 : TwoStageCert 8 2 1 :=
  { stage1 := rsCarryRightCert (-1)
    stage2 := { w0 := 0, d := 1, M := mat11 2, Q := matOfLists [[1, 2]], u_r := vec1 1, v_r := vec1 1 } }

theorem check_rsCarryNeg1 :
    checkTwoStageCert (kronVec rsMPS.L (mpoApplyMPS (carryMPO (-1)) rsMPS).L)
                      (mpsInnerTM rsMPS (mpoApplyMPS (carryMPO (-1)) rsMPS))
                      (kronVec rsMPS.R (mpoApplyMPS (carryMPO (-1)) rsMPS).R)
                      cert_rsCarryNeg1 = true := by decide

-- Corollary 1.1 (q = -1, Binary Carry-Parity): ∀ w : Nat, <RS_w | C_w | RS_w> = 2^w (via `decide`!)
theorem thm_rs_carry_parity (w : Nat) :
    rsCarrySum (-1) w = (2 : Int) ^ w := by
  rw [rsCarrySum_eq_transfer]
  have h := sound_twoStageCert check_rsCarryNeg1 w
  simp only [cert_rsCarryNeg1, rsCarryRightCert, Nat.add_zero, Int.mul_one, Int.one_mul] at h
  rw [h, transferSeq_one_dim]
  simp [vec1, mat11]

def cert_rsCarryNeg2 : TwoStageCert 8 2 1 :=
  { stage1 := rsCarryRightCert (-2)
    stage2 := { w0 := 0, d := 1, M := mat11 1, Q := matOfLists [[1, 1]], u_r := vec1 1, v_r := vec1 1 } }

theorem check_rsCarryNeg2 :
    checkTwoStageCert (kronVec rsMPS.L (mpoApplyMPS (carryMPO (-2)) rsMPS).L)
                      (mpsInnerTM rsMPS (mpoApplyMPS (carryMPO (-2)) rsMPS))
                      (kronVec rsMPS.R (mpoApplyMPS (carryMPO (-2)) rsMPS).R)
                      cert_rsCarryNeg2 = true := by decide

-- Corollary 1.2 (q = -2, Constant-1 Collapse): ∀ w : Nat, <RS_w | C_w(-2) | RS_w> = 1 (via `decide`!)
theorem thm_rs_carry_neg2 (w : Nat) :
    rsCarrySum (-2) w = 1 := by
  rw [rsCarrySum_eq_transfer]
  have h := sound_twoStageCert check_rsCarryNeg2 w
  simp only [cert_rsCarryNeg2, rsCarryRightCert, Nat.add_zero, Int.mul_one, Int.one_mul] at h
  rw [h, transferSeq_one_dim]
  simp [vec1, mat11, Int.one_pow]

-- Corollary 1.3 (q = -3, Jordan-Block Collision): ∀ w : Nat, <RS_w | C_w(-3) | RS_w> = (1 - w) * 2^w
theorem thm_rs_carry_jordan (w : Nat) :
    rsCarrySum (-3) w = (1 - (w : Int)) * (2 : Int) ^ w := by
  suffices h : ∀ n : Nat,
      rsCarrySum (-3) n = (1 - (n : Int)) * (2 : Int) ^ n ∧
      rsCarrySum (-3) (n + 1) = (1 - ((n + 1 : Nat) : Int)) * (2 : Int) ^ (n + 1) from
    (h w).1
  intro n
  induction n with
  | zero =>
    constructor
    · rw [rsCarrySum_zero]; simp
    · rw [rsCarrySum_one]; simp
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [thm_rs_carry_parametric_recurrence (-3) n, ih.1, ih.2]
    have h1 : (2 : Int) ^ (n + 2) = 2 * (2 : Int) ^ (n + 1) := by rw [Int.pow_succ]; grind
    have h2 : (2 : Int) ^ (n + 1) = 2 * (2 : Int) ^ n := by rw [Int.pow_succ]; grind
    grind

-- Corollary 1.4 (q = 0, Zero-Carry Jacobsthal Law): ∀ w : Nat, 3 * <RS_w | Z_w | RS_w> = 2^(w+2) - (-1)^w
theorem thm_rs_zero_carry (w : Nat) :
    3 * rsCarrySum 0 w = (2 : Int) ^ (w + 2) - (-1 : Int) ^ w := by
  have h := thm_rs_carry_parametric_closed 0 w
  have h2 : (2 : Int) * (2 : Int) ^ (w + 1) = (2 : Int) ^ (w + 2) := by rw [Int.pow_succ]; grind
  have h1 : (-1 : Int) ^ (w + 1) = -((-1 : Int) ^ w) := by rw [Int.pow_succ]; grind
  grind

-- ----------------------------------------------------------------------------
-- THEOREM 2: Binary Carry-Parity 4th Spectral Moment Irrational Collapse
--   16×16 Transfer Matrix -> 3×3 -> 2×2 Companion M2 = [[0,1],[64,4]] (λ = 2 ± 2√17)
--   Checked purely in Z by `decide`!
-- ----------------------------------------------------------------------------

def carryMPO2 : MPO 4 := mpoCompose (carryMPO (-1)) (carryMPO (-1))
def carryMPO4 : MPO 16 := mpoCompose carryMPO2 carryMPO2

def carryTrace4 (w : Nat) : Int :=
  sumNat (2 ^ w) (fun x => sumNat (2 ^ w) (fun y =>
    sumNat (2 ^ w) (fun z => sumNat (2 ^ w) (fun t =>
      (-1 : Int) ^ carries w x y * (-1 : Int) ^ carries w y z *
      (-1 : Int) ^ carries w z t * (-1 : Int) ^ carries w t x))))

theorem carryTrace4_eq_transfer (w : Nat) :
    carryTrace4 w = transferSeq carryMPO4.L (mpoTraceTM carryMPO4) carryMPO4.R w := by
  unfold carryTrace4 transferSeq
  rw [← mpo_trace_eq_transfer carryMPO4 w]
  apply sumNat_congr; intro x _
  unfold carryMPO4 carryMPO2
  rw [← mpo_compose_eq]
  have hinner : ∀ z, (mpoCompose (carryMPO (-1)) (carryMPO (-1))).eval w x z *
                     (mpoCompose (carryMPO (-1)) (carryMPO (-1))).eval w z x =
      sumNat (2 ^ w) (fun y => sumNat (2 ^ w) (fun t =>
        (-1 : Int) ^ carries w x y * (-1 : Int) ^ carries w y z *
        (-1 : Int) ^ carries w z t * (-1 : Int) ^ carries w t x)) := by
    intro z
    rw [← mpo_compose_eq, ← mpo_compose_eq]
    have hmul : ∀ n (f : Nat → Int) (c : Int), sumNat n f * c = sumNat n (fun k => f k * c) := by
      intro n f c; induction n with
      | zero => simp [sumNat]
      | succ n ih => simp only [sumNat, Int.add_mul, ih]
    rw [hmul]
    apply sumNat_congr; intro y _
    rw [← sumNat_mul_left]
    apply sumNat_congr; intro t _
    rw [carryMPO_eval, carryMPO_eval, carryMPO_eval, carryMPO_eval]
    grind
  rw [sumNat_congr (fun z _ => hinner z)]
  -- Swap sum_z and sum_y
  have hswap : ∀ m n (F : Nat → Nat → Int),
      sumNat m (fun a => sumNat n (fun b => F a b)) =
      sumNat n (fun b => sumNat m (fun a => F a b)) := by
    intro m n F
    induction m with
    | zero => simp [sumNat, sumNat_zero]
    | succ m ih => simp only [sumNat]; rw [ih, ← sumNat_add]
  exact hswap (2 ^ w) (2 ^ w) (fun y z => sumNat (2 ^ w) (fun t =>
    (-1 : Int) ^ carries w x y * (-1 : Int) ^ carries w y z *
    (-1 : Int) ^ carries w z t * (-1 : Int) ^ carries w t x))

def cert_carryTrace4 : TwoStageCert 16 3 2 :=
  { stage1 :=
      { w0 := 0, d := 1
        M := mat33 (vec3 0 0 (-128)) (vec3 1 0 56) (vec3 0 1 6)
        P := matOfLists [
          [1, 8, 96], [1, 0, 64], [1, 0, 64], [1, 8, 96],
          [1, 0, 64], [1, -8, 0], [1, 8, 96], [1, 0, 64],
          [1, 0, 64], [1, 8, 96], [1, -8, 0], [1, 0, 64],
          [1, 8, 96], [1, 0, 64], [1, 0, 64], [1, 8, 96]]
        u_r := vec3 1 8 96
        v_r := vec3 1 0 0 }
    stage2 :=
      { w0 := 0, d := 1
        M := mat22 0 1 64 4
        Q := matOfLists [[1, 8, 96], [8, 96, 896]]
        u_r := vec2 1 0
        v_r := vec2 1 8 } }

theorem check_carryTrace4 :
    checkRecurrenceCert carryMPO4.L (mpoTraceTM carryMPO4) carryMPO4.R
      cert_carryTrace4 (vec2 64 4) = true := by decide

theorem thm_carry_trace4_recurrence (w : Nat) :
    carryTrace4 (w + 2) = 4 * carryTrace4 (w + 1) + 64 * carryTrace4 w := by
  rw [carryTrace4_eq_transfer, carryTrace4_eq_transfer, carryTrace4_eq_transfer]
  have h := sound_recurrenceCert check_carryTrace4 w
  simp only [cert_carryTrace4, Nat.add_zero, sumFin, vec2] at h
  change transferSeq carryMPO4.L (mpoTraceTM carryMPO4) carryMPO4.R (w + 2) =
    0 + 64 * transferSeq carryMPO4.L (mpoTraceTM carryMPO4) carryMPO4.R w +
    4 * transferSeq carryMPO4.L (mpoTraceTM carryMPO4) carryMPO4.R (w + 1) at h
  omega

theorem thm_carry_trace4_init : carryTrace4 0 = 1 ∧ carryTrace4 1 = 8 := by
  rw [carryTrace4_eq_transfer, carryTrace4_eq_transfer]
  constructor <;> decide

def carryHadamardMPO : MPO 2 := mpoCompose (carryMPO (-1)) hadamardMPO

private theorem bitAndPopcount_comm (w x y : Nat) :
    bitAndPopcount w y x = bitAndPopcount w x y := by
  induction w generalizing x y with
  | zero => rfl
  | succ w ih =>
    simp only [bitAndPopcount]
    rw [ih (x / 2) (y / 2), Nat.mul_comm (y % 2) (x % 2)]

theorem carryHadamardTrace_eq_transfer (w : Nat) :
    carryHadamardTrace w =
    transferSeq carryHadamardMPO.L (mpoTraceTM carryHadamardMPO) carryHadamardMPO.R w := by
  unfold carryHadamardTrace transferSeq carryHadamardMPO
  rw [← mpo_hilbert_schmidt_eq_transfer (carryMPO (-1)) hadamardMPO w]
  apply sumNat_congr; intro x _
  apply sumNat_congr; intro y _
  rw [carryMPO_eval, hadamardMPO_eval]
  unfold walshHadamard
  rw [bitAndPopcount_comm]

def cert_carryHadamard : TwoStageCert 2 2 2 :=
  { stage1 := { w0 := 0, d := 1, M := mat22 0 4 1 2, P := mat22 1 4 1 0, u_r := vec2 1 4, v_r := vec2 1 0 }
    stage2 := { w0 := 0, d := 1, M := mat22 0 1 4 2, Q := mat22 1 4 4 12, u_r := vec2 1 0, v_r := vec2 1 4 } }

theorem check_carryHadamard :
    checkRecurrenceCert carryHadamardMPO.L (mpoTraceTM carryHadamardMPO) carryHadamardMPO.R
      cert_carryHadamard (vec2 4 2) = true := by decide

theorem thm_carry_hadamard_fibonacci (w : Nat) :
    carryHadamardTrace w = (2 : Int) ^ w * (fib (w + 2) : Int) := by
  have hrec : ∀ n, carryHadamardTrace (n + 2) = 2 * carryHadamardTrace (n + 1) + 4 * carryHadamardTrace n := by
    intro n
    rw [carryHadamardTrace_eq_transfer, carryHadamardTrace_eq_transfer, carryHadamardTrace_eq_transfer]
    have h := sound_recurrenceCert check_carryHadamard n
    simp only [cert_carryHadamard, Nat.add_zero, sumFin, vec2] at h
    change transferSeq carryHadamardMPO.L (mpoTraceTM carryHadamardMPO) carryHadamardMPO.R (n + 2) =
      0 + 4 * transferSeq carryHadamardMPO.L (mpoTraceTM carryHadamardMPO) carryHadamardMPO.R n +
      2 * transferSeq carryHadamardMPO.L (mpoTraceTM carryHadamardMPO) carryHadamardMPO.R (n + 1) at h
    omega
  have h0 : carryHadamardTrace 0 = 1 := by rw [carryHadamardTrace_eq_transfer]; decide
  have h1 : carryHadamardTrace 1 = 4 := by rw [carryHadamardTrace_eq_transfer]; decide
  suffices hs : ∀ n, carryHadamardTrace n = (2 : Int) ^ n * (fib (n + 2) : Int) ∧
                     carryHadamardTrace (n + 1) = (2 : Int) ^ (n + 1) * (fib (n + 3) : Int) from (hs w).1
  intro n
  induction n with
  | zero =>
    rw [h0, h1]; decide
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [hrec n, ih.1, ih.2]
    have hfib : (fib (n + 4) : Int) = (fib (n + 3) : Int) + (fib (n + 2) : Int) := by
      simp [fib]
    have hp1 : (2 : Int) ^ (n + 2) = 2 * (2 : Int) ^ (n + 1) := by rw [Int.pow_succ]; grind
    have hp2 : (2 : Int) ^ (n + 1) = 2 * (2 : Int) ^ n := by rw [Int.pow_succ]; grind
    grind

-- Contrast: Borrow-Parity(q) vs Walsh-Hadamard = (q + 1)^w (exact orthogonality iff q = -1!)
def borrowHadamardTrace (q : Int) (w : Nat) : Int :=
  sumNat (2 ^ w) (fun x => sumNat (2 ^ w) (fun y =>
    q ^ borrows w x y * walshHadamard w x y))

theorem borrowHadamardTrace_eq_transfer (q : Int) (w : Nat) :
    borrowHadamardTrace q w =
    transferSeq (mpoCompose (borrowMPO q) hadamardMPO).L
                (mpoTraceTM (mpoCompose (borrowMPO q) hadamardMPO))
                (mpoCompose (borrowMPO q) hadamardMPO).R w := by
  unfold borrowHadamardTrace transferSeq
  rw [← mpo_hilbert_schmidt_eq_transfer (borrowMPO q) hadamardMPO w]
  apply sumNat_congr; intro x _
  apply sumNat_congr; intro y _
  rw [borrowMPO_eval, hadamardMPO_eval]
  unfold walshHadamard; rw [bitAndPopcount_comm]

theorem thm_borrow_hadamard_parametric (q : Int) (w : Nat) :
    borrowHadamardTrace q w = (q + 1) ^ w := by
  rw [borrowHadamardTrace_eq_transfer]
  let O := mpoCompose (borrowMPO q) hadamardMPO
  let P : Mat 2 1 := fun _ _ => 1
  let M : Mat 1 1 := mat11 (q + 1)
  have hTP : matMul (mpoTraceTM O) P = matMul P M := by
    funext ⟨i, hi⟩ ⟨j, hj⟩
    match i, j with
    | 0, 0 | 1, 0 =>
      simp only [O, P, M, matMul, sumFin, mpoTraceTM, mpoCompose, matAdd, kronMat,
        borrowMPO, hadamardMPO, mat11]
      grind
    | _ + 2, _ => omega
    | _, _ + 1 => omega
  have hPv : matVec P (vec1 1) = O.R := by
    funext ⟨i, hi⟩
    match i with
    | 0 | 1 => simp [O, P, matVec, sumFin, mpoCompose, kronVec, borrowMPO, hadamardMPO, vec1, vec2]
    | _ + 2 => omega
  have huP : vecMat O.L P = vec1 1 := by
    funext ⟨j, hj⟩
    match j with
    | 0 => simp [O, P, vecMat, sumFin, mpoCompose, kronVec, borrowMPO, hadamardMPO, vec1, vec2]
    | _ + 1 => omega
  unfold transferSeq
  rw [← hPv, ← matVec_matMul, matPow_intertwine_right _ _ _ hTP w, matVec_matMul, vecDot_matVec, huP]
  have h1 := transferSeq_one_dim (vec1 1) M (vec1 1) w
  unfold transferSeq at h1
  rw [h1]
  simp [M, vec1, mat11]

theorem thm_borrow_hadamard_orthogonal (w : Nat) :
    borrowHadamardTrace (-1) (w + 1) = 0 := by
  rw [thm_borrow_hadamard_parametric]
  simp [Int.pow_succ]

-- ----------------------------------------------------------------------------
-- THEOREM 4: Exact Hilbert-Schmidt & Quadratic-Form Orthogonalities (via `decide`!)
-- ----------------------------------------------------------------------------

-- 4a: Carry-Parity ⊥ Borrow-Parity: ∀ w ≥ 1, Tr(C_w B_w) = 0 and Tr(C_w B_w^T) = 0
def carryBorrowMPO : MPO 4 := mpoCompose (carryMPO (-1)) (borrowMPO (-1))
def carryBorrowTMPO : MPO 4 := mpoCompose (carryMPO (-1)) (mpoTranspose (borrowMPO (-1)))

theorem check_carryBorrow_zero :
    checkStage1ZeroCert (mpoTraceTM carryBorrowMPO) carryBorrowMPO.R 1 = true := by decide

theorem check_carryBorrowT_zero :
    checkStage1ZeroCert (mpoTraceTM carryBorrowTMPO) carryBorrowTMPO.R 1 = true := by decide

theorem thm_carry_borrow_orthogonal (w : Nat) :
    sumNat (2 ^ (w + 1)) (fun x => sumNat (2 ^ (w + 1)) (fun y =>
      (-1 : Int) ^ carries (w + 1) x y * (-1 : Int) ^ borrows (w + 1) y x)) = 0 ∧
    sumNat (2 ^ (w + 1)) (fun x => sumNat (2 ^ (w + 1)) (fun y =>
      (-1 : Int) ^ carries (w + 1) x y * (-1 : Int) ^ borrows (w + 1) x y)) = 0 := by
  constructor
  · have h := sound_stage1ZeroCert (u := carryBorrowMPO.L) check_carryBorrow_zero w
    unfold transferSeq carryBorrowMPO at h
    rw [← mpo_hilbert_schmidt_eq_transfer (carryMPO (-1)) (borrowMPO (-1)) (w + 1)] at h
    rw [← h]
    apply sumNat_congr; intro x _
    apply sumNat_congr; intro y _
    rw [carryMPO_eval, borrowMPO_eval]
  · have h := sound_stage1ZeroCert (u := carryBorrowTMPO.L) check_carryBorrowT_zero w
    unfold transferSeq carryBorrowTMPO at h
    rw [← mpo_hilbert_schmidt_eq_transfer (carryMPO (-1)) (mpoTranspose (borrowMPO (-1))) (w + 1)] at h
    rw [← h]
    apply sumNat_congr; intro x _
    apply sumNat_congr; intro y _
    rw [carryMPO_eval, mpo_transpose_eq, borrowMPO_eval]

-- 4b: Rudin-Shapiro Cyclic-Shift Orthogonality (Non-trivial Stage-2 8->1->0 Eigenline Cert!)
--     ∀ w ≥ 2, Σ_{x=0}^{2^w-1} RS_w(x) * RS_w((x + 1) mod 2^w) = 0
def rsIncCert : RightReductionCert 8 1 :=
  { w0 := 2, d := 1, M := mat11 2
    P := matOfLists [[1], [0], [0], [0], [0], [1], [0], [0]]
    u_r := vec1 0, v_r := vec1 4 }

theorem check_rsInc_orthogonal :
    checkOrthogonalityCert
      (kronVec rsMPS.L (mpoApplyMPS incMPO rsMPS).L)
      (mpsInnerTM rsMPS (mpoApplyMPS incMPO rsMPS))
      (kronVec rsMPS.R (mpoApplyMPS incMPO rsMPS).R)
      rsIncCert = true := by decide

private theorem sumNat_single_mod (w x : Nat) (f : Nat → Int) :
    sumNat (2 ^ w) (fun y => (if y % (2 ^ w) = x % (2 ^ w) then (1 : Int) else 0) * f y) =
    f (x % (2 ^ w)) := by
  have hlt : x % (2 ^ w) < 2 ^ w := Nat.mod_lt x (Nat.two_pow_pos w)
  have hgen : ∀ n, n ≤ 2 ^ w →
      sumNat n (fun y => (if y % (2 ^ w) = x % (2 ^ w) then (1 : Int) else 0) * f y) =
      if x % (2 ^ w) < n then f (x % (2 ^ w)) else 0 := by
    intro n hn
    induction n with
    | zero => simp [sumNat]
    | succ n ih =>
      simp only [sumNat]
      rw [ih (Nat.le_of_lt hn)]
      have hmodn : n % (2 ^ w) = n := Nat.mod_eq_of_lt hn
      rw [hmodn]
      by_cases hlt' : x % (2 ^ w) < n
      · have hne : n ≠ x % (2 ^ w) := by omega
        have hlt2 : x % (2 ^ w) < n + 1 := by omega
        simp [hlt', hne, hlt2]
      · by_cases heq : n = x % (2 ^ w)
        · simp [heq]
        · have hnot2 : ¬(x % (2 ^ w) < n + 1) := by omega
          simp [hlt', heq, hnot2]
  rw [hgen (2 ^ w) (Nat.le_refl _)]
  simp [hlt]

theorem thm_rs_inc_orthogonal (w : Nat) :
    sumNat (2 ^ (w + 2)) (fun x => rudinShapiro (w + 2) x * rudinShapiro (w + 2) (modInc (w + 2) x)) = 0 := by
  have h := sound_orthogonalityCert check_rsInc_orthogonal w
  unfold transferSeq at h
  simp only [rsIncCert] at h
  rw [← mps_mpo_mps_eq_transfer rsMPS incMPO rsMPS (w + 2)] at h
  rw [← h]
  apply sumNat_congr; intro x _
  rw [sumNat_mul_left, rsMPS_eval]
  congr 1
  have hc : sumNat (2 ^ (w + 2)) (fun y => incMPO.eval (w + 2) x y * rsMPS.eval (w + 2) y) =
      sumNat (2 ^ (w + 2)) (fun y => (if y % (2 ^ (w + 2)) = (x + 1) % (2 ^ (w + 2)) then (1 : Int) else 0) * rudinShapiro (w + 2) y) := by
    apply sumNat_congr; intro y _
    rw [incMPO_eval, rsMPS_eval]; rfl
  rw [hc, sumNat_single_mod]
  rfl

-- 4c: Rudin-Shapiro Borrow-Parity Alternating Law (dim 8 -> 3 -> 2 via `decide`!)
--     ∀ k ≥ 1, <RS_{2k} | B_{2k} | RS_{2k}> = 0  AND  ∀ k, <RS_{2k+1} | B_{2k+1} | RS_{2k+1}> = 2^{2k+1}
def rsBorrowSum (w : Nat) : Int :=
  sumNat (2 ^ w) (fun x => sumNat (2 ^ w) (fun y =>
    rudinShapiro w x * ((-1 : Int) ^ borrows w x y * rudinShapiro w y)))

def cert_rsBorrow : TwoStageCert 8 3 2 :=
  { stage1 :=
      { w0 := 1, d := 1
        M := mat33 (vec3 0 0 0) (vec3 1 0 4) (vec3 0 1 0)
        P := matOfLists [
          [1, 0, 4], [1, 0, -4], [-1, 0, -4], [1, 0, 4],
          [-1, 0, -4], [1, 4, 4], [-1, 0, 4], [-1, 4, -4]]
        u_r := vec3 1 0 4
        v_r := vec3 2 0 0 }
    stage2 :=
      { w0 := 0, d := 1
        M := mat22 0 1 4 0
        Q := matOfLists [[1, 0, 4], [0, 4, 0]]
        u_r := vec2 1 0
        v_r := vec2 2 0 } }

theorem check_rsBorrow :
    checkRecurrenceCert
      (kronVec rsMPS.L (mpoApplyMPS (borrowMPO (-1)) rsMPS).L)
      (mpsInnerTM rsMPS (mpoApplyMPS (borrowMPO (-1)) rsMPS))
      (kronVec rsMPS.R (mpoApplyMPS (borrowMPO (-1)) rsMPS).R)
      cert_rsBorrow (vec2 4 0) = true := by decide

theorem thm_rs_borrow_parity_alternating :
    (∀ k : Nat, rsBorrowSum (2 * k + 1) = (2 : Int) ^ (2 * k + 1)) ∧
    (∀ k : Nat, rsBorrowSum (2 * k + 2) = 0) := by
  have htr : ∀ w, rsBorrowSum w =
      transferSeq (kronVec rsMPS.L (mpoApplyMPS (borrowMPO (-1)) rsMPS).L)
                  (mpsInnerTM rsMPS (mpoApplyMPS (borrowMPO (-1)) rsMPS))
                  (kronVec rsMPS.R (mpoApplyMPS (borrowMPO (-1)) rsMPS).R) w := by
    intro w; unfold rsBorrowSum transferSeq
    rw [← mps_mpo_mps_eq_transfer rsMPS (borrowMPO (-1)) rsMPS w]
    apply sumNat_congr; intro x _; apply sumNat_congr; intro y _
    rw [rsMPS_eval, rsMPS_eval, borrowMPO_eval]
  have hrec : ∀ w, rsBorrowSum (w + 3) = 4 * rsBorrowSum (w + 1) := by
    intro w
    rw [htr, htr]
    have h := sound_recurrenceCert check_rsBorrow w
    simp only [cert_rsBorrow, sumFin, vec2] at h
    change transferSeq _ _ _ (w + 1 + 2) =
      0 + 4 * transferSeq _ _ _ (w + 1 + 0) + 0 * transferSeq _ _ _ (w + 1 + 1) at h
    simp only [Nat.add_zero] at h
    have ha : w + 1 + 2 = w + 3 := by omega
    rw [ha] at h; omega
  have h1 : rsBorrowSum 1 = 2 := by rw [htr]; decide
  have h2 : rsBorrowSum 2 = 0 := by rw [htr]; decide
  constructor
  · intro k
    induction k with
    | zero => simpa using h1
    | succ k ih =>
      have ha : 2 * (k + 1) + 1 = (2 * k) + 3 := by omega
      rw [ha, hrec (2 * k), ih]
      have hp : (2 : Int) ^ (2 * k + 3) = 4 * (2 : Int) ^ (2 * k + 1) := by
        rw [Int.pow_succ, Int.pow_succ]; grind
      rw [← ha]; exact hp.symm
  · intro k
    induction k with
    | zero => simpa using h2
    | succ k ih =>
      have ha : 2 * (k + 1) + 2 = (2 * k + 1) + 3 := by omega
      rw [ha, hrec (2 * k + 1), ih]
      simp

-- 4d: 3rd Spectral Moment Vanishing of Full & Internal Carry-Parity (dim 8 -> 0 via `decide`!)
def carryMPO3 : MPO 8 := mpoCompose carryMPO2 (carryMPO (-1))
def carryIntMPO3 : MPO 8 := mpoCompose (mpoCompose (carryIntMPO (-1)) (carryIntMPO (-1))) (carryIntMPO (-1))

theorem check_carryTrace3_zero :
    checkStage1ZeroCert (mpoTraceTM carryMPO3) carryMPO3.R 1 = true := by decide

theorem check_carryIntTrace3_zero :
    checkStage1ZeroCert (mpoTraceTM carryIntMPO3) carryIntMPO3.R 2 = true := by decide

theorem thm_carry_trace3_zero (w : Nat) :
    sumNat (2 ^ (w + 1)) (fun x => sumNat (2 ^ (w + 1)) (fun y => sumNat (2 ^ (w + 1)) (fun z =>
      (-1 : Int) ^ carries (w + 1) x y * (-1 : Int) ^ carries (w + 1) y z * (-1 : Int) ^ carries (w + 1) z x))) = 0 := by
  have h := sound_stage1ZeroCert (u := carryMPO3.L) check_carryTrace3_zero w
  unfold transferSeq at h
  rw [← mpo_trace_eq_transfer carryMPO3 (w + 1)] at h
  rw [← h]
  apply sumNat_congr; intro x _
  unfold carryMPO3 carryMPO2
  rw [← mpo_compose_eq]
  have hmul : ∀ n (f : Nat → Int) (c : Int), sumNat n f * c = sumNat n (fun k => f k * c) := by
    intro n f c; induction n with
    | zero => simp [sumNat]
    | succ n ih => simp only [sumNat, Int.add_mul, ih]
  have hswap : ∀ m n (F : Nat → Nat → Int),
      sumNat m (fun a => sumNat n (fun b => F a b)) =
      sumNat n (fun b => sumNat m (fun a => F a b)) := by
    intro m n F; induction m with
    | zero => simp [sumNat, sumNat_zero]
    | succ m ih => simp only [sumNat]; rw [ih, ← sumNat_add]
  have hstep : ∀ z, (mpoCompose (carryMPO (-1)) (carryMPO (-1))).eval (w + 1) x z * (carryMPO (-1)).eval (w + 1) z x =
      sumNat (2 ^ (w + 1)) (fun y =>
        (-1 : Int) ^ carries (w + 1) x y * (-1 : Int) ^ carries (w + 1) y z * (-1 : Int) ^ carries (w + 1) z x) := by
    intro z
    rw [← mpo_compose_eq, hmul]
    apply sumNat_congr; intro y _
    rw [carryMPO_eval, carryMPO_eval, carryMPO_eval]
  rw [sumNat_congr (fun z _ => hstep z)]
  exact hswap _ _ _

theorem thm_carryInt_trace3_zero (w : Nat) :
    sumNat (2 ^ (w + 2)) (fun x => sumNat (2 ^ (w + 2)) (fun y => sumNat (2 ^ (w + 2)) (fun z =>
      (-1 : Int) ^ carriesInt (w + 2) x y * (-1 : Int) ^ carriesInt (w + 2) y z * (-1 : Int) ^ carriesInt (w + 2) z x))) = 0 := by
  have h := sound_stage1ZeroCert (u := carryIntMPO3.L) check_carryIntTrace3_zero w
  unfold transferSeq at h
  rw [← mpo_trace_eq_transfer carryIntMPO3 (w + 2)] at h
  rw [← h]
  apply sumNat_congr; intro x _
  unfold carryIntMPO3
  rw [← mpo_compose_eq]
  have hmul : ∀ n (f : Nat → Int) (c : Int), sumNat n f * c = sumNat n (fun k => f k * c) := by
    intro n f c; induction n with
    | zero => simp [sumNat]
    | succ n ih => simp only [sumNat, Int.add_mul, ih]
  have hswap : ∀ m n (F : Nat → Nat → Int),
      sumNat m (fun a => sumNat n (fun b => F a b)) =
      sumNat n (fun b => sumNat m (fun a => F a b)) := by
    intro m n F; induction m with
    | zero => simp [sumNat, sumNat_zero]
    | succ m ih => simp only [sumNat]; rw [ih, ← sumNat_add]
  have hstep : ∀ z, (mpoCompose (carryIntMPO (-1)) (carryIntMPO (-1))).eval (w + 2) x z * (carryIntMPO (-1)).eval (w + 2) z x =
      sumNat (2 ^ (w + 2)) (fun y =>
        (-1 : Int) ^ carriesInt (w + 2) x y * (-1 : Int) ^ carriesInt (w + 2) y z * (-1 : Int) ^ carriesInt (w + 2) z x) := by
    intro z
    rw [← mpo_compose_eq, hmul]
    apply sumNat_congr; intro y _
    rw [carryIntMPO_eval, carryIntMPO_eval, carryIntMPO_eval]
  rw [sumNat_congr (fun z _ => hstep z)]
  exact hswap _ _ _

-- ----------------------------------------------------------------------------
-- THEOREM 5: Exact Constant-2 Carry-Increment Trace Law (4 -> 2 -> 1 via `decide`!)
--   ∀ w ≥ 1, Σ_{x=0}^{2^w-1} (-1)^{carries(x, (x + 1) mod 2^w)} = 2
-- ----------------------------------------------------------------------------

def carryIncMPO : MPO 4 := mpoCompose (carryMPO (-1)) (mpoTranspose incMPO)

def cert_carryInc : TwoStageCert 4 2 1 :=
  { stage1 :=
      { w0 := 1, d := 1
        M := mat22 0 1 1 0
        P := matOfLists [[0, 0], [1, 1], [0, 0], [-1, 1]]
        u_r := vec2 1 1
        v_r := vec2 2 0 }
    stage2 :=
      { w0 := 0, d := 1
        M := mat11 1
        Q := matOfLists [[1, 1]]
        u_r := vec1 1
        v_r := vec1 2 } }

theorem check_carryInc :
    checkTwoStageCert carryIncMPO.L (mpoTraceTM carryIncMPO) carryIncMPO.R cert_carryInc = true := by decide

theorem thm_carry_inc_trace (w : Nat) :
    sumNat (2 ^ (w + 1)) (fun x => (-1 : Int) ^ carries (w + 1) x (modInc (w + 1) x)) = 2 := by
  have h := sound_twoStageCert check_carryInc w
  simp only [cert_carryInc, Int.mul_one, Int.one_mul] at h
  rw [transferSeq_one_dim] at h
  simp only [vec1, mat11, Int.one_pow, Int.mul_one, Int.one_mul] at h
  unfold transferSeq carryIncMPO at h
  rw [← mpo_hilbert_schmidt_eq_transfer (carryMPO (-1)) (mpoTranspose incMPO) (w + 1)] at h
  rw [← h]
  apply sumNat_congr; intro x _
  have hc : sumNat (2 ^ (w + 1)) (fun y => (carryMPO (-1)).eval (w + 1) x y * (mpoTranspose incMPO).eval (w + 1) y x) =
      sumNat (2 ^ (w + 1)) (fun y => (if y % (2 ^ (w + 1)) = (x + 1) % (2 ^ (w + 1)) then (1 : Int) else 0) * (-1 : Int) ^ carries (w + 1) x y) := by
    apply sumNat_congr; intro y _
    rw [carryMPO_eval, mpo_transpose_eq, incMPO_eval, Int.mul_comm]; rfl
  rw [hc, sumNat_single_mod]
  rfl

-- ----------------------------------------------------------------------------
-- THEOREM 6: Pointwise MPO-MPS & MPO Unitarity Gauge Identities (via `decide`!)
-- ----------------------------------------------------------------------------

-- 6a: Pointwise Carry*TM and Borrow*TM via `checkMPSGaugeLeftCert` (`decide`!)
def carryTMMPS : MPS 2 := mpoApplyMPS (carryMPO (-1)) tmMPS
def borrowTMMPS : MPS 2 := mpoApplyMPS (borrowMPO (-1)) tmMPS

def shiftMPS {D : Nat} (M : MPS D) (b0 : Bool) : MPS D :=
  { L := vecMat M.L (M.A b0), A := M.A, R := M.R }

theorem shiftMPS_eval {D : Nat} (M : MPS D) (w x : Nat) :
    M.eval (w + 1) x = (shiftMPS M (x % 2 == 1)).eval w (x / 2) := by
  have haux : ∀ n u a, M.evalAux n u a = (shiftMPS M (x % 2 == 1)).evalAux n u a := by
    intro n
    induction n with
    | zero => intro u a; rfl
    | succ n ih => intro u a; exact ih _ _
  exact haux w (vecMat M.L (M.A (x % 2 == 1))) (x / 2)

def constMPS_LR (l r : Int) : MPS 1 :=
  { L := vec1 l, A := fun _ => mat11 1, R := vec1 r }

theorem constMPS_LR_eval (l r : Int) (w x : Nat) : (constMPS_LR l r).eval w x = l * r := by
  unfold MPS.eval
  induction w generalizing x with
  | zero => simp [MPS.evalAux, constMPS_LR, vecDot, sumFin, vec1]
  | succ w ih =>
    simp only [MPS.evalAux]
    have hvm : vecMat (constMPS_LR l r).L ((constMPS_LR l r).A (x % 2 == 1)) = (constMPS_LR l r).L := by
      funext ⟨j, hj⟩
      match j with
      | 0 => simp [vecMat, sumFin, constMPS_LR, vec1, mat11]
      | _ + 1 => omega
    rw [hvm]; exact ih (x / 2)

theorem check_carryTM_even :
    checkMPSGaugeLeftCert (shiftMPS carryTMMPS false) (constMPS_LR 0 2)
      { d := 1, Q := matOfLists [[1, 1]] } = true := by decide

theorem check_carryTM_odd :
    checkMPSGaugeLeftCert (shiftMPS carryTMMPS true) (constMPS_LR 1 2)
      { d := 1, Q := matOfLists [[1, 1]] } = true := by decide

theorem check_borrowTM_even :
    checkMPSGaugeLeftCert (shiftMPS borrowTMMPS false) (constMPS_LR 1 2)
      { d := 1, Q := matOfLists [[1, 1]] } = true := by decide

theorem check_borrowTM_odd :
    checkMPSGaugeLeftCert (shiftMPS borrowTMMPS true) (constMPS_LR 0 2)
      { d := 1, Q := matOfLists [[1, 1]] } = true := by decide

theorem thm_carry_tm_pointwise (w x : Nat) :
    sumNat (2 ^ (w + 1)) (fun y => (-1 : Int) ^ carries (w + 1) x y * thueMorse (w + 1) y) =
    if x % 2 = 1 then 2 else 0 := by
  have heq : sumNat (2 ^ (w + 1)) (fun y => (-1 : Int) ^ carries (w + 1) x y * thueMorse (w + 1) y) =
      carryTMMPS.eval (w + 1) x := by
    unfold carryTMMPS
    rw [← mpo_apply_mps_eq]
    apply sumNat_congr; intro y _
    rw [carryMPO_eval, tmMPS_eval]
  rw [heq, shiftMPS_eval]
  have hx : x % 2 = 0 ∨ x % 2 = 1 := by omega
  rcases hx with hx | hx
  · have h := sound_mpsGaugeLeftCert check_carryTM_even w (x / 2)
    simp only [Int.one_mul, constMPS_LR_eval] at h
    simp [hx, h]
  · have h := sound_mpsGaugeLeftCert check_carryTM_odd w (x / 2)
    simp only [Int.one_mul, constMPS_LR_eval] at h
    simp [hx, h]

theorem thm_borrow_tm_pointwise (w x : Nat) :
    sumNat (2 ^ (w + 1)) (fun y => (-1 : Int) ^ borrows (w + 1) x y * thueMorse (w + 1) y) =
    if x % 2 = 0 then 2 else 0 := by
  have heq : sumNat (2 ^ (w + 1)) (fun y => (-1 : Int) ^ borrows (w + 1) x y * thueMorse (w + 1) y) =
      borrowTMMPS.eval (w + 1) x := by
    unfold borrowTMMPS
    rw [← mpo_apply_mps_eq]
    apply sumNat_congr; intro y _
    rw [borrowMPO_eval, tmMPS_eval]
  rw [heq, shiftMPS_eval]
  have hx : x % 2 = 0 ∨ x % 2 = 1 := by omega
  rcases hx with hx | hx
  · have h := sound_mpsGaugeLeftCert check_borrowTM_even w (x / 2)
    simp only [Int.one_mul, constMPS_LR_eval] at h
    simp [hx, h]
  · have h := sound_mpsGaugeLeftCert check_borrowTM_odd w (x / 2)
    simp only [Int.one_mul, constMPS_LR_eval] at h
    simp [hx, h]

theorem thm_carry_plus_borrow_tm (w x : Nat) :
    sumNat (2 ^ (w + 1)) (fun y => ((-1 : Int) ^ carries (w + 1) x y + (-1 : Int) ^ borrows (w + 1) x y) * thueMorse (w + 1) y) = 2 := by
  have hadd : sumNat (2 ^ (w + 1)) (fun y => ((-1 : Int) ^ carries (w + 1) x y + (-1 : Int) ^ borrows (w + 1) x y) * thueMorse (w + 1) y) =
      sumNat (2 ^ (w + 1)) (fun y => (-1 : Int) ^ carries (w + 1) x y * thueMorse (w + 1) y) +
      sumNat (2 ^ (w + 1)) (fun y => (-1 : Int) ^ borrows (w + 1) x y * thueMorse (w + 1) y) := by
    rw [← sumNat_add]
    apply sumNat_congr; intro y _
    exact Int.add_mul _ _ _
  rw [hadd, thm_carry_tm_pointwise, thm_borrow_tm_pointwise]
  omega

-- 6b: Two-Stage Pointwise MPO Unitarity Gauge Certificates (4 -> 2 -> 1 via `decide`!)
--     Inc_w * Inc_w^T = I_w  AND  Gray_w * Gray_w^T = I_w  (∀ w : Nat, ∀ x z : Nat!)
def incIncTMPO : MPO 4 := mpoCompose incMPO (mpoTranspose incMPO)
def incMidMPO : MPO 2 :=
  { L := vec2 0 1
    W := fun b1 b2 =>
      match b1, b2 with
      | false, false => mat22 1 0 1 0
      | true, true => mat22 1 0 0 1
      | _, _ => mat22 0 0 0 0
    R := vec2 1 1 }

theorem check_inc_unitary_stage1 :
    checkMPOGaugeLeftCert incIncTMPO incMidMPO
      { d := 1, Q := matOfLists [[1, 0, 0, 0], [0, 0, 0, 1]] } = true := by decide

theorem check_inc_unitary_stage2 :
    checkMPOGaugeRightCert incMidMPO idMPO
      { d := 1, P := matOfLists [[1], [1]] } = true := by decide

theorem thm_inc_unitary_pointwise (w x z : Nat) :
    sumNat (2 ^ w) (fun y =>
      (if y % (2 ^ w) = modInc w x then (1 : Int) else 0) *
      (if y % (2 ^ w) = modInc w z then (1 : Int) else 0)) =
    if x % (2 ^ w) = z % (2 ^ w) then 1 else 0 := by
  have h1 := sound_mpoGaugeLeftCert check_inc_unitary_stage1 w x z
  have h2 := sound_mpoGaugeRightCert check_inc_unitary_stage2 w x z
  simp only [Int.one_mul] at h1 h2
  have h3 : incIncTMPO.eval w x z = idMPO.eval w x z := h1.trans h2
  rw [idMPO_eval] at h3
  rw [← h3]
  unfold incIncTMPO
  rw [← mpo_compose_eq]
  apply sumNat_congr; intro y _
  rw [incMPO_eval, mpo_transpose_eq, incMPO_eval]

def grayGrayTMPO : MPO 4 := mpoCompose grayMPO (mpoTranspose grayMPO)
def grayMidMPO : MPO 2 :=
  { L := vec2 1 1
    W := fun b1 b2 =>
      match b1, b2 with
      | false, false => mat22 1 1 0 0
      | true, true => mat22 0 0 1 1
      | _, _ => mat22 0 0 0 0
    R := vec2 1 0 }

theorem check_gray_unitary_stage1 :
    checkMPOGaugeRightCert grayGrayTMPO grayMidMPO
      { d := 1, P := matOfLists [[1, 0], [0, 0], [0, 0], [0, 1]] } = true := by decide

theorem check_gray_unitary_stage2 :
    checkMPOGaugeLeftCert grayMidMPO idMPO
      { d := 1, Q := matOfLists [[1, 1]] } = true := by decide

theorem thm_gray_unitary_pointwise (w x z : Nat) :
    sumNat (2 ^ w) (fun y =>
      (if y % (2 ^ w) = grayCode w x then (1 : Int) else 0) *
      (if y % (2 ^ w) = grayCode w z then (1 : Int) else 0)) =
    if x % (2 ^ w) = z % (2 ^ w) then 1 else 0 := by
  have h1 := sound_mpoGaugeRightCert check_gray_unitary_stage1 w x z
  have h2 := sound_mpoGaugeLeftCert check_gray_unitary_stage2 w x z
  simp only [Int.one_mul] at h1 h2
  have h3 : grayGrayTMPO.eval w x z = idMPO.eval w x z := h1.trans h2
  rw [idMPO_eval] at h3
  rw [← h3]
  unfold grayGrayTMPO
  rw [← mpo_compose_eq]
  apply sumNat_congr; intro y _
  rw [grayMPO_eval, mpo_transpose_eq, grayMPO_eval]

-- ----------------------------------------------------------------------------
-- THEOREM 7: Exact Chiral Anti-Symmetry & All-Odd-Moment Vanishing of C_w
--   ∀ w ≥ 1, ∀ k : Nat, Tr(C_w^{2k+1}) = 0  (ALL odd powers simultaneously!)
-- ----------------------------------------------------------------------------

def msbFlip (w x : Nat) : Nat :=
  if x < 2 ^ w then x + 2 ^ w else x - 2 ^ w

def msbSign (w x : Nat) : Int :=
  if x < 2 ^ w then 1 else -1

private theorem carriesAux_msb_split :
    ∀ (w c x y : Nat),
      carriesAux c (w + 1) x y =
      carriesAux c w x y + ((x / (2 ^ w) % 2 + y / (2 ^ w) % 2 + (x % (2 ^ w) + y % (2 ^ w) + c) / (2 ^ w)) / 2) := by
  intro w
  induction w with
  | zero =>
    intro c x y
    simp [carriesAux, Nat.mod_one]
  | succ w ih =>
    intro c x y
    have hstepL : carriesAux c (w + 2) x y =
        (x % 2 + y % 2 + c) / 2 + carriesAux ((x % 2 + y % 2 + c) / 2) (w + 1) (x / 2) (y / 2) := rfl
    have hstepR : carriesAux c (w + 1) x y =
        (x % 2 + y % 2 + c) / 2 + carriesAux ((x % 2 + y % 2 + c) / 2) w (x / 2) (y / 2) := rfl
    rw [hstepL, ih ((x % 2 + y % 2 + c) / 2) (x / 2) (y / 2), hstepR]
    have hdiv : ∀ a : Nat, a / 2 / 2 ^ w = a / 2 ^ (w + 1) := by
      intro a; rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]
    have hcarry : (x / 2 % 2 ^ w + y / 2 % 2 ^ w + (x % 2 + y % 2 + c) / 2) / 2 ^ w =
        (x % 2 ^ (w + 1) + y % 2 ^ (w + 1) + c) / 2 ^ (w + 1) := by
      have hp : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
      have hx : x % (2 ^ (w + 1)) = x % 2 + 2 * (x / 2 % 2 ^ w) := by
        rw [hp, mod_two_mul]
      have hy : y % (2 ^ (w + 1)) = y % 2 + 2 * (y / 2 % 2 ^ w) := by
        rw [hp, mod_two_mul]
      rw [hx, hy, hp, ← Nat.div_div_eq_div_mul]
      congr 1
      omega
    rw [hdiv x, hdiv y, hcarry]
    omega

theorem thm_carry_chiral_antisym (w x y : Nat) (hx : x < 2 ^ (w + 1)) (hy : y < 2 ^ (w + 1)) :
    msbSign w x * msbSign w y * (-1 : Int) ^ carries (w + 1) (msbFlip w x) (msbFlip w y) =
    -((-1 : Int) ^ carries (w + 1) x y) := by
  unfold carries msbSign msbFlip
  rw [carriesAux_msb_split, carriesAux_msb_split]
  have hp : 2 ^ (w + 1) = 2 ^ w + 2 ^ w := by rw [Nat.pow_succ]; omega
  have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
  have hmod_add : ∀ a, a < 2 ^ w → (a + 2 ^ w) % 2 ^ w = a % 2 ^ w := by
    intro a _; exact Nat.add_mod_right a (2 ^ w)
  have hmod_sub : ∀ a, 2 ^ w ≤ a → a < 2 ^ (w + 1) → (a - 2 ^ w) % 2 ^ w = a % 2 ^ w := by
    intro a h1 _
    rw [← Nat.add_mod_right (a - 2 ^ w) (2 ^ w), Nat.sub_add_cancel h1]
  have hcarries_mod : ∀ a b c d, a % 2 ^ w = c % 2 ^ w → b % 2 ^ w = d % 2 ^ w →
      carriesAux 0 w a b = carriesAux 0 w c d := by
    intro a b c d ha hb
    have hgen : ∀ k s a1 b1 c1 d1, a1 % 2 ^ k = c1 % 2 ^ k → b1 % 2 ^ k = d1 % 2 ^ k →
        carriesAux s k a1 b1 = carriesAux s k c1 d1 := by
      intro k
      induction k with
      | zero => intro s _ _ _ _ _ _; rfl
      | succ k ihk =>
        intro s a1 b1 c1 d1 ha1 hb1
        have hp' : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
        rw [hp', mod_two_mul, mod_two_mul] at ha1 hb1
        have ha_lsb : a1 % 2 = c1 % 2 := by omega
        have hb_lsb : b1 % 2 = d1 % 2 := by omega
        have ha_div : a1 / 2 % 2 ^ k = c1 / 2 % 2 ^ k := by omega
        have hb_div : b1 / 2 % 2 ^ k = d1 / 2 % 2 ^ k := by omega
        simp only [carriesAux, ha_lsb, hb_lsb]
        rw [ihk _ _ _ _ _ ha_div hb_div]
    exact hgen w 0 a b c d ha hb
  have hdiv1 : ∀ a, 2 ^ w ≤ a → a < 2 ^ (w + 1) → a / 2 ^ w % 2 = 1 := by
    intro a ha1 ha2
    have h1 : (a - 2 ^ w + 2 ^ w) / 2 ^ w = 1 := by
      rw [Nat.add_div_right _ hpos, Nat.div_eq_of_lt (by omega)]
    rw [Nat.sub_add_cancel ha1] at h1
    rw [h1]
  have hcb : (x % 2 ^ w + y % 2 ^ w + 0) / 2 ^ w = 0 ∨ (x % 2 ^ w + y % 2 ^ w + 0) / 2 ^ w = 1 := by
    have hxm0 : x % 2 ^ w < 2 ^ w := Nat.mod_lt x hpos
    have hym0 : y % 2 ^ w < 2 ^ w := Nat.mod_lt y hpos
    have hle : (x % 2 ^ w + y % 2 ^ w + 0) / 2 ^ w < 2 := by
      rw [Nat.div_lt_iff_lt_mul hpos]; omega
    generalize (x % 2 ^ w + y % 2 ^ w + 0) / 2 ^ w = q at hle
    omega
  by_cases hxw : x < 2 ^ w <;> by_cases hyw : y < 2 ^ w
  · simp only [hxw, hyw, ↓reduceIte]
    have hxm : (x + 2 ^ w) % 2 ^ w = x % 2 ^ w := hmod_add x hxw
    have hym : (y + 2 ^ w) % 2 ^ w = y % 2 ^ w := hmod_add y hyw
    rw [hcarries_mod _ _ x y hxm hym, hxm, hym]
    have hxd1 : (x + 2 ^ w) / 2 ^ w % 2 = 1 := hdiv1 (x + 2 ^ w) (by omega) (by omega)
    have hyd1 : (y + 2 ^ w) / 2 ^ w % 2 = 1 := hdiv1 (y + 2 ^ w) (by omega) (by omega)
    have hxd0 : x / 2 ^ w % 2 = 0 := by rw [Nat.div_eq_of_lt hxw]
    have hyd0 : y / 2 ^ w % 2 = 0 := by rw [Nat.div_eq_of_lt hyw]
    rw [hxd1, hyd1, hxd0, hyd0]
    rcases hcb with hcb | hcb <;> rw [hcb] <;> simp [Int.pow_add]
  · simp only [hxw, hyw, ↓reduceIte]
    have hxm : (x + 2 ^ w) % 2 ^ w = x % 2 ^ w := hmod_add x hxw
    have hym : (y - 2 ^ w) % 2 ^ w = y % 2 ^ w := hmod_sub y (by omega) hy
    rw [hcarries_mod _ _ x y hxm hym, hxm, hym]
    have hxd1 : (x + 2 ^ w) / 2 ^ w % 2 = 1 := hdiv1 (x + 2 ^ w) (by omega) (by omega)
    have hyd0 : (y - 2 ^ w) / 2 ^ w % 2 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
    have hxd0 : x / 2 ^ w % 2 = 0 := by rw [Nat.div_eq_of_lt hxw]
    have hyd1 : y / 2 ^ w % 2 = 1 := hdiv1 y (by omega) hy
    rw [hxd1, hyd0, hxd0, hyd1]
    simp [Nat.add_comm]
  · simp only [hxw, hyw, ↓reduceIte]
    have hxm : (x - 2 ^ w) % 2 ^ w = x % 2 ^ w := hmod_sub x (by omega) hx
    have hym : (y + 2 ^ w) % 2 ^ w = y % 2 ^ w := hmod_add y hyw
    rw [hcarries_mod _ _ x y hxm hym, hxm, hym]
    have hxd0 : (x - 2 ^ w) / 2 ^ w % 2 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
    have hyd1 : (y + 2 ^ w) / 2 ^ w % 2 = 1 := hdiv1 (y + 2 ^ w) (by omega) (by omega)
    have hxd1 : x / 2 ^ w % 2 = 1 := hdiv1 x (by omega) hx
    have hyd0 : y / 2 ^ w % 2 = 0 := by rw [Nat.div_eq_of_lt hyw]
    rw [hxd0, hyd1, hxd1, hyd0]
    simp [Nat.add_comm]
  · simp only [hxw, hyw, ↓reduceIte]
    have hxm : (x - 2 ^ w) % 2 ^ w = x % 2 ^ w := hmod_sub x (by omega) hx
    have hym : (y - 2 ^ w) % 2 ^ w = y % 2 ^ w := hmod_sub y (by omega) hy
    rw [hcarries_mod _ _ x y hxm hym, hxm, hym]
    have hxd0 : (x - 2 ^ w) / 2 ^ w % 2 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
    have hyd0 : (y - 2 ^ w) / 2 ^ w % 2 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
    have hxd1 : x / 2 ^ w % 2 = 1 := hdiv1 x (by omega) hx
    have hyd1 : y / 2 ^ w % 2 = 1 := hdiv1 y (by omega) hy
    rw [hxd0, hyd0, hxd1, hyd1]
    rcases hcb with hcb | hcb <;> rw [hcb] <;> simp [Int.pow_add]

private theorem sumNat_msbFlip_inv (w : Nat) (f : Nat → Int) :
    sumNat (2 ^ (w + 1)) (fun x => f (msbFlip w x)) = sumNat (2 ^ (w + 1)) f := by
  have hp : 2 ^ (w + 1) = 2 ^ w + 2 ^ w := by rw [Nat.pow_succ]; omega
  have hsplit : ∀ a b (g : Nat → Int), sumNat (a + b) g = sumNat a g + sumNat b (fun i => g (a + i)) := by
    intro a b g
    induction b with
    | zero => simp [sumNat]
    | succ b ih =>
      have : a + (b + 1) = (a + b) + 1 := by omega
      rw [this]; simp only [sumNat]; rw [ih]; omega
  rw [hp, hsplit, hsplit]
  have h1 : sumNat (2 ^ w) (fun x => f (msbFlip w x)) = sumNat (2 ^ w) (fun i => f (2 ^ w + i)) := by
    apply sumNat_congr; intro x hx
    simp only [msbFlip, hx, ↓reduceIte, Nat.add_comm]
  have h2 : sumNat (2 ^ w) (fun i => f (msbFlip w (2 ^ w + i))) = sumNat (2 ^ w) f := by
    apply sumNat_congr; intro i _
    have hnot : ¬(2 ^ w + i < 2 ^ w) := by omega
    simp only [msbFlip, hnot, ↓reduceIte]
    have hsub : 2 ^ w + i - 2 ^ w = i := by omega
    rw [hsub]
  rw [h1, h2, Int.add_comm]

theorem carryMatPow_chiral (w k : Nat) :
    ∀ x y, x < 2 ^ (w + 1) → y < 2 ^ (w + 1) →
      msbSign w x * msbSign w y * carryMatPow (w + 1) k (msbFlip w x) (msbFlip w y) =
      (-1 : Int) ^ k * carryMatPow (w + 1) k x y := by
  induction k with
  | zero =>
    intro x y hx hy
    simp only [carryMatPow, Int.pow_zero, Int.one_mul]
    have hinj : (msbFlip w x = msbFlip w y) ↔ (x = y) := by
      unfold msbFlip
      by_cases hxw : x < 2 ^ w <;> by_cases hyw : y < 2 ^ w <;> simp [hxw, hyw] <;> omega
    simp only [hinj]
    by_cases hxy : x = y
    · subst hxy; simp [msbSign]; split <;> rfl
    · simp [hxy]
  | succ k ih =>
    intro x y hx hy
    simp only [carryMatPow]
    rw [← sumNat_mul_left, ← sumNat_msbFlip_inv w]
    rw [← sumNat_mul_left]
    apply sumNat_congr; intro z hz
    have hflip_z : msbFlip w z < 2 ^ (w + 1) := by
      unfold msbFlip
      have hp : 2 ^ (w + 1) = 2 ^ w + 2 ^ w := by rw [Nat.pow_succ]; omega
      split <;> omega
    have hsq : msbSign w z * msbSign w z = 1 := by unfold msbSign; split <;> rfl
    have hc1 := thm_carry_chiral_antisym w x z hx hz
    have hc2 := ih z y hz hy
    calc msbSign w x * msbSign w y *
          ((-1 : Int) ^ carries (w + 1) (msbFlip w x) (msbFlip w z) *
           carryMatPow (w + 1) k (msbFlip w z) (msbFlip w y))
      _ = (msbSign w x * msbSign w z * (-1 : Int) ^ carries (w + 1) (msbFlip w x) (msbFlip w z)) *
          (msbSign w z * msbSign w y * carryMatPow (w + 1) k (msbFlip w z) (msbFlip w y)) := by
          have : msbSign w x * msbSign w y = (msbSign w x * msbSign w z) * (msbSign w z * msbSign w y) := by
            calc msbSign w x * msbSign w y
              _ = msbSign w x * (1 * msbSign w y) := by simp
              _ = msbSign w x * ((msbSign w z * msbSign w z) * msbSign w y) := by rw [hsq]
              _ = (msbSign w x * msbSign w z) * (msbSign w z * msbSign w y) := by grind
          grind
      _ = (-((-1 : Int) ^ carries (w + 1) x z)) * ((-1 : Int) ^ k * carryMatPow (w + 1) k z y) := by
          rw [hc1, hc2]
      _ = (-1 : Int) ^ (k + 1) * ((-1 : Int) ^ carries (w + 1) x z * carryMatPow (w + 1) k z y) := by
          rw [Int.pow_succ]; grind

-- Theorem 7: ALL odd spectral moments of C_w vanish for ALL w ≥ 1 and ALL k : Nat!
theorem thm_carry_all_odd_traces_zero (w k : Nat) :
    sumNat (2 ^ (w + 1)) (fun x => carryMatPow (w + 1) (2 * k + 1) x x) = 0 := by
  have hneg : sumNat (2 ^ (w + 1)) (fun x => carryMatPow (w + 1) (2 * k + 1) (msbFlip w x) (msbFlip w x)) =
      -(sumNat (2 ^ (w + 1)) (fun x => carryMatPow (w + 1) (2 * k + 1) x x)) := by
    have hpow : (-1 : Int) ^ (2 * k + 1) = -1 := by
      induction k with
      | zero => rfl
      | succ k ih =>
        have : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
        rw [this, Int.pow_succ, Int.pow_succ, ih]; rfl
    have hstep : ∀ x, x < 2 ^ (w + 1) →
        carryMatPow (w + 1) (2 * k + 1) (msbFlip w x) (msbFlip w x) =
        (-1 : Int) * carryMatPow (w + 1) (2 * k + 1) x x := by
      intro x hx
      have hc := carryMatPow_chiral w (2 * k + 1) x x hx hx
      have hsq : msbSign w x * msbSign w x = 1 := by unfold msbSign; split <;> rfl
      rw [hsq, Int.one_mul, hpow] at hc
      exact hc
    rw [sumNat_congr hstep, sumNat_mul_left]
    omega
  have hinv := sumNat_msbFlip_inv w (fun x => carryMatPow (w + 1) (2 * k + 1) x x)
  rw [hinv] at hneg
  omega

-- ============================================================================
-- PART 6: Sharpness Counterexamples, Negative Mutation Tests & Non-Vacuity
-- ============================================================================

-- A. Kernel-Checked Sharpness Counterexamples (where relaxing hypotheses breaks the law!)
theorem sharp_rs_inc_fails_at_w1 :
    sumNat (2 ^ 1) (fun x => rudinShapiro 1 x * rudinShapiro 1 (modInc 1 x)) = 2 := by decide

theorem sharp_carryInt_trace3_fails_at_w1 :
    sumNat (2 ^ 1) (fun x => sumNat (2 ^ 1) (fun y => sumNat (2 ^ 1) (fun z =>
      (-1 : Int) ^ carriesInt 1 x y * (-1 : Int) ^ carriesInt 1 y z * (-1 : Int) ^ carriesInt 1 z x))) = 8 := by decide

theorem sharp_carry_borrow_fails_at_q0 :
    sumNat (2 ^ 1) (fun x => sumNat (2 ^ 1) (fun y =>
      (0 : Int) ^ carries 1 x y * (0 : Int) ^ borrows 1 y x)) = 2 := by decide

theorem sharp_borrow_hadamard_fails_at_q0 :
    borrowHadamardTrace 0 1 = 1 := by decide

theorem sharp_carry_inc_fails_at_w0 :
    sumNat (2 ^ 0) (fun x => (-1 : Int) ^ carries 0 x (modInc 0 x)) = 1 := by decide

theorem sharp_borrow_inc_not_const :
    sumNat (2 ^ 4) (fun x => (-1 : Int) ^ borrows 4 x (modInc 4 x)) = 6 := by decide

-- B. Kernel-Checked Negative / Mutation Tests (broken certificates MUST be rejected!)
theorem neg_d_zero_rejected :
    checkTwoStageCert carryMPO4.L (mpoTraceTM carryMPO4) carryMPO4.R
      { cert_carryTrace4 with stage1 := { cert_carryTrace4.stage1 with d := 0 } } = false := by decide

theorem neg_bad_recurrence_coeff_rejected :
    checkRecurrenceCert carryMPO4.L (mpoTraceTM carryMPO4) carryMPO4.R
      cert_carryTrace4 (vec2 65 4) = false := by decide

theorem neg_bad_P_entry_rejected :
    checkRightReductionCert carryMPO4.L (mpoTraceTM carryMPO4) carryMPO4.R
      { cert_carryTrace4.stage1 with u_r := vec3 1 8 95 } = false := by decide

theorem neg_wrong_shift_w0_rejected :
    checkOrthogonalityCert
      (kronVec rsMPS.L (mpoApplyMPS incMPO rsMPS).L)
      (mpsInnerTM rsMPS (mpoApplyMPS incMPO rsMPS))
      (kronVec rsMPS.R (mpoApplyMPS incMPO rsMPS).R)
      { rsIncCert with w0 := 1 } = false := by decide

theorem neg_bad_gauge_matrix_rejected :
    checkMPOGaugeLeftCert incIncTMPO incMidMPO
      { d := 1, Q := matOfLists [[1, 1, 0, 0], [0, 0, 0, 1]] } = false := by decide

theorem neg_bad_mps_gauge_rejected :
    checkMPSGaugeLeftCert (shiftMPS carryTMMPS true) (constMPS_LR 1 1)
      { d := 1, Q := matOfLists [[1, 1]] } = false := by decide

-- C. Non-Vacuity Witnesses (proving every certificate checker hypothesis is genuinely inhabited)
example : Nonempty { c : TwoStageCert 16 3 2 //
    checkRecurrenceCert carryMPO4.L (mpoTraceTM carryMPO4) carryMPO4.R c (vec2 64 4) = true } :=
  ⟨⟨cert_carryTrace4, check_carryTrace4⟩⟩

example : Nonempty { c : RightReductionCert 8 1 //
    checkOrthogonalityCert (kronVec rsMPS.L (mpoApplyMPS incMPO rsMPS).L)
      (mpsInnerTM rsMPS (mpoApplyMPS incMPO rsMPS))
      (kronVec rsMPS.R (mpoApplyMPS incMPO rsMPS).R) c = true } :=
  ⟨⟨rsIncCert, check_rsInc_orthogonal⟩⟩

example : Nonempty { c : MPOGaugeRightCert 4 2 //
    checkMPOGaugeRightCert grayGrayTMPO grayMidMPO c = true } :=
  ⟨⟨{ d := 1, P := matOfLists [[1, 0], [0, 0], [0, 0], [0, 1]] }, check_gray_unitary_stage1⟩⟩

end SiliconTensorEngine

-- D. Axiom Verification Receipts



