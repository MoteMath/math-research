/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BitwiseSmithNormalFormLifter.Defs

/-!
# Theorems (`bitwise-smith-normal-form-lifter`)

Full proofs of the headline infinite theorems of Exact Smith Normal Form Bit-Slice Lifting Engine.
-/

namespace SiliconSNF

theorem sumFin_sub {n : Nat} (f g : Fin n → Int) :
    sumFin n (fun i => f i - g i) = sumFin n f - sumFin n g := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih =>
    simp only [sumFin]
    rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc)]
    omega

theorem sumFin_swap {n : Nat} (a b : Fin n) (f : Fin n → Int) :
    sumFin n (fun i => f ((Perm.swap a b).toFun i)) = sumFin n f := by
  by_cases hab : a = b
  · subst hab
    apply sumFin_congr; intro i
    simp only [Perm.swap]
    by_cases h : i = a <;> simp [h]
  · have hdiff : ∀ i : Fin n,
        f ((Perm.swap a b).toFun i) =
        f i + (if i = a then f b - f a else 0) + (if i = b then f a - f b else 0) := by
      intro i
      simp only [Perm.swap]
      by_cases h1 : i = a
      · subst h1; simp [hab]; omega
      · by_cases h2 : i = b
        · subst h2; simp [h1]; omega
        · simp [h1, h2]
    rw [sumFin_congr hdiff, sumFin_add, sumFin_add, sumFin_single, sumFin_single]
    omega

/-- Reindexing a finite sum along any bijection `Perm n`. -/
theorem sumFin_perm {n : Nat} (p : Perm n) (f : Fin n → Int) :
    sumFin n (fun i => f (p.toFun i)) = sumFin n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let k := p.invFun (Fin.last n)
    let q : Perm (n + 1) := Perm.comp p (Perm.swap k (Fin.last n))
    have hq_last : q.toFun (Fin.last n) = Fin.last n := by
      simp only [q, Perm.comp, Perm.swap, k]
      split
      · rename_i h
        exact (congrArg p.toFun h).trans (p.right_inv _)
      · simp [p.right_inv]
    have hq_lt : ∀ i : Fin n, (q.toFun i.castSucc).1 < n := by
      intro i
      have hne : q.toFun i.castSucc ≠ Fin.last n := by
        intro heq
        have := congrArg q.invFun heq
        rw [q.left_inv] at this
        have hlast_inv : q.invFun (Fin.last n) = Fin.last n := by
          calc q.invFun (Fin.last n) = q.invFun (q.toFun (Fin.last n)) := by rw [hq_last]
            _ = Fin.last n := q.left_inv _
        rw [hlast_inv] at this
        have := congrArg Fin.val this
        simp [Fin.last] at this
        omega
      have hlt := (q.toFun i.castSucc).isLt
      have : (q.toFun i.castSucc).1 ≠ n := fun h => hne (Fin.ext h)
      omega
    have hqi_lt : ∀ i : Fin n, (q.invFun i.castSucc).1 < n := by
      intro i
      have hne : q.invFun i.castSucc ≠ Fin.last n := by
        intro heq
        have := congrArg q.toFun heq
        rw [q.right_inv, hq_last] at this
        have := congrArg Fin.val this
        simp [Fin.last] at this
        omega
      have hlt := (q.invFun i.castSucc).isLt
      have : (q.invFun i.castSucc).1 ≠ n := fun h => hne (Fin.ext h)
      omega
    let q' : Perm n := {
      toFun := fun i => ⟨(q.toFun i.castSucc).1, hq_lt i⟩
      invFun := fun i => ⟨(q.invFun i.castSucc).1, hqi_lt i⟩
      left_inv := fun i => by
        apply Fin.ext; dsimp
        rw [q.left_inv]; rfl
      right_inv := fun i => by
        apply Fin.ext; dsimp
        rw [q.right_inv]; rfl
    }
    have hswap := sumFin_swap k (Fin.last n) (fun i => f (p.toFun i))
    rw [← hswap]
    have hq_eq : sumFin (n + 1) (fun i => f (p.toFun ((Perm.swap k (Fin.last n)).toFun i))) =
                 sumFin (n + 1) (fun i => f (q.toFun i)) := rfl
    rw [hq_eq]
    simp only [sumFin, hq_last]
    have hrec : sumFin n (fun i => f (q.toFun i.castSucc)) =
                sumFin n (fun i => f (q'.toFun i).castSucc) := by
      apply sumFin_congr; intro i; rfl
    rw [hrec, ih q' (fun i => f i.castSucc)]

-- ============================================================================
-- Integer Matrix Operations
-- ============================================================================

theorem matMul_add {n : Nat} (A B C : Mat n) :
    matMul A (matAdd B C) = matAdd (matMul A B) (matMul A C) := by
  apply matExt; intro i j
  simp only [matMul, matAdd]
  rw [← sumFin_add]
  apply sumFin_congr; intro k; exact Int.mul_add _ _ _

theorem add_matMul {n : Nat} (A B C : Mat n) :
    matMul (matAdd A B) C = matAdd (matMul A C) (matMul B C) := by
  apply matExt; intro i j
  simp only [matMul, matAdd]
  rw [← sumFin_add]
  apply sumFin_congr; intro k; exact Int.add_mul _ _ _

theorem matMul_smul {n : Nat} (c : Int) (A B : Mat n) :
    matMul A (matSmul c B) = matSmul c (matMul A B) := by
  apply matExt; intro i j
  simp only [matMul, matSmul]
  rw [← sumFin_mul_left]
  apply sumFin_congr; intro k
  rw [← Int.mul_assoc, Int.mul_comm (A i k) c, Int.mul_assoc]

theorem smul_matMul {n : Nat} (c : Int) (A B : Mat n) :
    matMul (matSmul c A) B = matSmul c (matMul A B) := by
  apply matExt; intro i j
  simp only [matMul, matSmul]
  rw [← sumFin_mul_left]
  apply sumFin_congr; intro k; exact Int.mul_assoc _ _ _

theorem matVec_mul {n : Nat} (A B : Mat n) (v : Fin n → Int) :
    matVec (matMul A B) v = matVec A (matVec B v) := by
  funext i; simp only [matVec, matMul]
  calc sumFin n (fun k => sumFin n (fun r => A i r * B r k) * v k)
      = sumFin n (fun k => sumFin n (fun r => (A i r * B r k) * v k)) := by
        apply sumFin_congr; intro k; rw [← sumFin_mul_right]
    _ = sumFin n (fun r => sumFin n (fun k => (A i r * B r k) * v k)) := sumFin_comm _
    _ = sumFin n (fun r => sumFin n (fun k => A i r * (B r k * v k))) := by
        apply sumFin_congr; intro r; apply sumFin_congr; intro k; exact Int.mul_assoc _ _ _
    _ = sumFin n (fun r => A i r * sumFin n (fun k => B r k * v k)) := by
        apply sumFin_congr; intro r; rw [sumFin_mul_left]

theorem matVec_id {n : Nat} (v : Fin n → Int) : matVec (matId n) v = v := by
  funext i; simp only [matVec, matId]
  have h : sumFin n (fun j => (if i = j then 1 else 0) * v j) =
           sumFin n (fun j => if i = j then v j else 0) := by
    apply sumFin_congr; intro j; by_cases hj : i = j <;> simp [hj]
  rw [h, sumFin_single_symm]

theorem matVec_zero {n : Nat} (A : Mat n) : matVec A (fun _ => 0) = fun _ => 0 := by
  funext i; simp only [matVec, Int.mul_zero]; exact sumFin_zero n

theorem matVec_smul {n : Nat} (A : Mat n) (c : Int) (v : Fin n → Int) :
    matVec A (fun j => c * v j) = fun i => c * matVec A v i := by
  funext i; simp only [matVec]
  rw [← sumFin_mul_left]
  apply sumFin_congr; intro j
  rw [← Int.mul_assoc, Int.mul_comm (A i j) c, Int.mul_assoc]

-- ============================================================================
-- Constructive Unimodular Group GL_n(Z), Equivalence, and Canonical SNF
-- ============================================================================

theorem UnimodEquiv.refl {n : Nat} (A : Mat n) : UnimodEquiv A A :=
  ⟨Unimod.id n, Unimod.id n, by simp only [Unimod.id]; rw [matId_mul, mul_matId]⟩

theorem UnimodEquiv.of_unimod {n : Nat} (U : Unimod n) : UnimodEquiv U.val (matId n) :=
  ⟨U.symm, Unimod.id n, by simp only [Unimod.symm, Unimod.id]; rw [U.inv_mul, mul_matId]⟩

theorem UnimodEquiv.neg_right {n : Nat} {A B : Mat n} (h : UnimodEquiv A B) :
    UnimodEquiv A (matNeg B) := by
  apply UnimodEquiv.trans h
  refine ⟨signUnimod (fun _ => -1) (fun _ => by decide), Unimod.id n, ?_⟩
  simp only [Unimod.id]
  rw [mul_matId]
  apply matExt; intro i j
  simp only [matMul, signUnimod, diagMat, matNeg]
  have h1 : sumFin n (fun k => (if i = k then -1 else 0) * B k j) =
            sumFin n (fun k => if i = k then -B k j else 0) := by
    apply sumFin_congr; intro k; by_cases hk : i = k <;> simp [hk]
  rw [h1, sumFin_single_symm]

theorem UnimodEquiv.neg_left {n : Nat} {A B : Mat n} (h : UnimodEquiv A B) :
    UnimodEquiv (matNeg A) B := by
  have h1 : UnimodEquiv (matNeg A) A := ((UnimodEquiv.refl A).neg_right).symm
  exact h1.trans h

theorem UnimodEquiv.smul_both {n : Nat} (c : Int) {A B : Mat n} (h : UnimodEquiv A B) :
    UnimodEquiv (matSmul c A) (matSmul c B) := by
  rcases h with ⟨U, V, hUV⟩
  refine ⟨U, V, ?_⟩
  rw [matMul_smul, smul_matMul, hUV]

theorem UnimodEquiv.diag_abs {n : Nat} (d : Fin n → Int) :
    UnimodEquiv (diagMat d) (diagMatNat (fun i => (d i).natAbs)) := by
  let s : Fin n → Int := fun i => if d i < 0 then -1 else 1
  have hs : ∀ i, s i * s i = 1 := by
    intro i; simp only [s]; split <;> decide
  refine ⟨signUnimod s hs, Unimod.id n, ?_⟩
  simp only [Unimod.id]
  rw [mul_matId]
  apply matExt; intro i j
  simp only [matMul, signUnimod, diagMat, diagMatNat]
  have h1 : sumFin n (fun k => (if i = k then s i else 0) * (if k = j then d k else 0)) =
            sumFin n (fun k => if i = k then (if k = j then s i * d k else 0) else 0) := by
    apply sumFin_congr; intro k
    by_cases h1 : i = k
    · subst h1; by_cases h2 : i = j <;> simp [h2]
    · simp [h1]
  rw [h1, sumFin_single_symm]
  by_cases hij : i = j
  · subst hij; simp only [↓reduceIte, s]
    split <;> omega
  · simp [hij]

theorem UnimodEquiv.diag_perm {n : Nat} (d : Fin n → Nat) (p : Perm n) :
    UnimodEquiv (diagMatNat d) (diagMatNat (fun i => d (p.toFun i))) := by
  refine ⟨permUnimod p, permUnimod p.symm, ?_⟩
  simp only [permUnimod]
  rw [permMat_mul_left, mul_permMat_symm]
  apply matExt; intro i j
  simp only [diagMatNat]
  have hiff : p.toFun i = p.toFun j ↔ i = j := by
    constructor
    · intro h; have := congrArg p.invFun h; simpa [p.left_inv] using this
    · intro h; rw [h]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, mt hiff.mp hij]

/-- If `HasSNF M d` and `∀ i, d i = 1`, then `M` is unimodular (`M ∈ GL_n(Z)`). -/
theorem HasSNF.unimod_of_all_one {n : Nat} {M : Mat n} {d : Fin n → Nat}
    (h : HasSNF M d) (hall : ∀ i, d i = 1) : ∃ U : Unimod n, U.val = M := by
  rcases h.1 with ⟨U, V, hUV⟩
  have hdiag : diagMatNat d = matId n := by
    apply matExt; intro i j; simp only [diagMatNat, matId, hall]; rfl
  rw [hdiag] at hUV
  have hM : M = matMul U.inv V.inv := by
    calc M = matMul (matId n) (matMul M (matId n)) := by rw [mul_matId, matId_mul]
      _ = matMul (matMul U.inv U.val) (matMul M (matMul V.val V.inv)) := by
          rw [U.inv_mul, V.mul_inv]
      _ = matMul U.inv (matMul (matMul (matMul U.val M) V.val) V.inv) := by
          simp only [matMul_assoc]
      _ = matMul U.inv (matMul (matId n) V.inv) := by rw [hUV]
      _ = matMul U.inv V.inv := by rw [matId_mul]
  exact ⟨Unimod.mul U.symm V.symm, hM.symm⟩

/-- If `HasSNF M d` and `d i = 0`, then `M` has an explicit nonzero integer kernel vector! -/
theorem HasSNF.zero_entry_kernel {n : Nat} {M : Mat n} {d : Fin n → Nat}
    (h : HasSNF M d) (i : Fin n) (hi : d i = 0) :
    ∃ v : Fin n → Int, (∃ j, v j ≠ 0) ∧ matVec M v = fun _ => 0 := by
  rcases h.1 with ⟨U, V, hUV⟩
  let ei : Fin n → Int := fun j => if j = i then 1 else 0
  let v := matVec V.val ei
  refine ⟨v, ?_, ?_⟩
  · by_cases hnz : ∃ j, v j ≠ 0
    · exact hnz
    · exfalso
      have hv0 : v = fun _ => 0 := by
        funext j
        by_cases hj : v j = 0
        · exact hj
        · exfalso; exact hnz ⟨j, hj⟩
      have h1 : matVec V.inv v = ei := by
        simp only [v, ← matVec_mul, V.inv_mul, matVec_id]
      rw [hv0, matVec_zero] at h1
      have h2 := congrFun h1 i
      simp only [ei, ↓reduceIte] at h2
      omega
  · have hdiag : matVec (diagMatNat d) ei = fun _ => 0 := by
      funext r; simp only [matVec, diagMatNat, ei]
      have hz : sumFin n (fun j => (if r = j then (d r : Int) else 0) * (if j = i then 1 else 0)) =
                sumFin n (fun _ => 0) := by
        apply sumFin_congr; intro j
        by_cases h1 : r = j
        · subst h1
          by_cases h2 : r = i
          · subst h2; simp [hi]
          · simp [h2]
        · simp [h1]
      rw [hz, sumFin_zero]
    have hUMv : matVec U.val (matVec M v) = fun _ => 0 := by
      rw [← matVec_mul, ← matVec_mul, hUV, hdiag]
    calc matVec M v = matVec (matId n) (matVec M v) := (matVec_id _).symm
      _ = matVec (matMul U.inv U.val) (matVec M v) := by rw [U.inv_mul]
      _ = matVec U.inv (matVec U.val (matVec M v)) := matVec_mul _ _ _
      _ = matVec U.inv (fun _ => 0) := by rw [hUMv]
      _ = fun _ => 0 := matVec_zero _

/-- If `HasSNF M d` and `d i > 1`, then `M` has an explicit cokernel torsion witness of order `d i`:
    a vector `b ∉ im(M)` such that `(d i) • b ∈ im(M)`. -/
theorem HasSNF.torsion_obstruction {n : Nat} {M : Mat n} {d : Fin n → Nat}
    (h : HasSNF M d) (i : Fin n) (hi : d i > 1) :
    ∃ b : Fin n → Int, (∀ x, matVec M x ≠ b) ∧ (∃ x, matVec M x = fun j => (d i : Int) * b j) := by
  rcases h.1 with ⟨U, V, hUV⟩
  let ei : Fin n → Int := fun j => if j = i then 1 else 0
  let b := matVec U.inv ei
  refine ⟨b, ?_, ?_⟩
  · intro x hx
    let y := matVec V.inv x
    have hy : matVec (diagMatNat d) y = ei := by
      calc matVec (diagMatNat d) y
          = matVec (matMul (matMul U.val M) V.val) (matVec V.inv x) := by rw [hUV]
        _ = matVec (matMul (matMul U.val M) (matMul V.val V.inv)) x := by
            rw [← matVec_mul, matMul_assoc (matMul U.val M) V.val V.inv]
        _ = matVec (matMul U.val M) x := by rw [V.mul_inv, mul_matId]
        _ = matVec U.val (matVec M x) := matVec_mul _ _ _
        _ = matVec U.val b := by rw [hx]
        _ = matVec (matMul U.val U.inv) ei := by rw [← matVec_mul]
        _ = ei := by rw [U.mul_inv, matVec_id]
    have hcomp := congrFun hy i
    simp only [matVec, diagMatNat, ei, ↓reduceIte] at hcomp
    have hdiag_i : sumFin n (fun j => (if i = j then (d i : Int) else 0) * y j) =
                   (d i : Int) * y i := by
      have hs : sumFin n (fun j => (if i = j then (d i : Int) else 0) * y j) =
                sumFin n (fun j => if i = j then (d i : Int) * y j else 0) := by
        apply sumFin_congr; intro j; by_cases hj : i = j <;> simp [hj]
      rw [hs, sumFin_single_symm]
    rw [hdiag_i] at hcomp
    have hdiv : ((d i : Int)) ∣ 1 := ⟨y i, hcomp.symm⟩
    have hle : d i ≤ 1 := by
      have hnat := Int.natAbs_dvd_natAbs.mpr hdiv
      simpa using Nat.le_of_dvd (by omega) hnat
    omega
  · refine ⟨matVec V.val ei, ?_⟩
    have hdiag_ei : matVec (diagMatNat d) ei = fun r => (d i : Int) * ei r := by
      funext r; simp only [matVec, diagMatNat, ei]
      have hs : sumFin n (fun j => (if r = j then (d r : Int) else 0) * (if j = i then 1 else 0)) =
                sumFin n (fun j => if r = j then (if j = i then (d r : Int) else 0) else 0) := by
        apply sumFin_congr; intro j
        by_cases h1 : r = j
        · subst h1; by_cases h2 : r = i <;> simp [h2]
        · simp [h1]
      rw [hs, sumFin_single_symm]
      by_cases hri : r = i
      · subst hri; simp
      · simp [hri]
    calc matVec M (matVec V.val ei)
        = matVec (matId n) (matVec M (matVec V.val ei)) := (matVec_id _).symm
      _ = matVec (matMul U.inv U.val) (matVec M (matVec V.val ei)) := by rw [U.inv_mul]
      _ = matVec U.inv (matVec U.val (matVec M (matVec V.val ei))) := matVec_mul _ _ _
      _ = matVec U.inv (matVec (matMul (matMul U.val M) V.val) ei) := by
          rw [matVec_mul (matMul U.val M) V.val ei, matVec_mul U.val M (matVec V.val ei)]
      _ = matVec U.inv (matVec (diagMatNat d) ei) := by rw [hUV]
      _ = matVec U.inv (fun r => (d i : Int) * ei r) := by rw [hdiag_ei]
      _ = fun j => (d i : Int) * b j := matVec_smul U.inv (d i : Int) ei

/-- If `HasSNF M d` and `∀ i, d i ≠ 0`, then `M` is injective on `Z^n`. -/
theorem HasSNF.injective_of_ne_zero {n : Nat} {M : Mat n} {d : Fin n → Nat}
    (h : HasSNF M d) (hnz : ∀ i, d i ≠ 0) :
    ∀ x : Fin n → Int, matVec M x = (fun _ => 0) → x = (fun _ => 0) := by
  intro x hx
  rcases h.1 with ⟨U, V, hUV⟩
  let y := matVec V.inv x
  have hy0 : matVec (diagMatNat d) y = fun _ => 0 := by
    calc matVec (diagMatNat d) y
        = matVec (matMul (matMul U.val M) (matMul V.val V.inv)) x := by
          rw [← hUV, ← matVec_mul, matMul_assoc (matMul U.val M) V.val V.inv]
      _ = matVec U.val (matVec M x) := by rw [V.mul_inv, mul_matId, matVec_mul]
      _ = matVec U.val (fun _ => 0) := by rw [hx]
      _ = fun _ => 0 := matVec_zero _
  have hy_eq : y = fun _ => 0 := by
    funext i
    have hcomp := congrFun hy0 i
    simp only [matVec, diagMatNat] at hcomp
    have hs : sumFin n (fun j => (if i = j then (d i : Int) else 0) * y j) =
              (d i : Int) * y i := by
      have h1 : sumFin n (fun j => (if i = j then (d i : Int) else 0) * y j) =
                sumFin n (fun j => if i = j then (d i : Int) * y j else 0) := by
        apply sumFin_congr; intro j; by_cases hj : i = j <;> simp [hj]
      rw [h1, sumFin_single_symm]
    rw [hs] at hcomp
    have hdi : (d i : Int) ≠ 0 := Int.ofNat_ne_zero.mpr (hnz i)
    exact (Int.mul_eq_zero.mp hcomp).resolve_left hdi
  calc x = matVec (matId n) x := (matVec_id _).symm
    _ = matVec (matMul V.val V.inv) x := by rw [V.mul_inv]
    _ = matVec V.val y := matVec_mul _ _ _
    _ = matVec V.val (fun _ => 0) := by rw [hy_eq]
    _ = fun _ => 0 := matVec_zero _

-- ============================================================================
-- PART II: FIVE REUSABLE BIT-SLICE UNIMODULAR LIFTING ENGINES
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Dimension Transport Helpers
-- ----------------------------------------------------------------------------

theorem unimodEquiv_cast {m n : Nat} (h : m = n) {A B : Mat m}
    (heq : UnimodEquiv A B) : UnimodEquiv (castMat h A) (castMat h B) := by
  subst h; exact heq

theorem hasSNF_cast {m n : Nat} (h : m = n) {M : Mat m} {d : Fin m → Nat}
    (hsnf : HasSNF M d) :
    HasSNF (castMat h M) (fun i => d ⟨i.1, h ▸ i.isLt⟩) := by
  subst h; exact hsnf

-- ----------------------------------------------------------------------------
-- 2x2 Block Matrix Algebra on Mat (m + m)
-- ----------------------------------------------------------------------------

theorem unimodEquiv_blockDiag {m : Nat} {A A' D D' : Mat m}
    (hA : UnimodEquiv A A') (hD : UnimodEquiv D D') :
    UnimodEquiv (blockMat A (matZero m) (matZero m) D)
                (blockMat A' (matZero m) (matZero m) D') := by
  rcases hA with ⟨UA, VA, hUA⟩
  rcases hD with ⟨UD, VD, hUD⟩
  refine ⟨blockDiagUnimod UA UD, blockDiagUnimod VA VD, ?_⟩
  simp only [blockDiagUnimod, blockMat_mul, matZero_mul, mul_matZero,
             matAdd_zero_right, matAdd_zero_left, hUA, hUD]

theorem matSmul_zero (c : Int) (m : Nat) : matSmul c (matZero m) = matZero m := by
  apply matExt; intro i j; simp [matSmul, matZero]

theorem blockDiag_diagMatNat {m : Nat} (d1 d2 : Fin m → Nat) :
    blockMat (diagMatNat d1) (matZero m) (matZero m) (diagMatNat d2) =
      diagMatNat (fun i : Fin (m + m) => if h : i.1 < m then d1 ⟨i.1, h⟩ else d2 ⟨i.1 - m, by omega⟩) := by
  apply matExt; intro i j
  simp only [blockMat, diagMatNat, matZero]
  split
  · rename_i hi
    split
    · rename_i hj
      by_cases hij : i = j
      · subst hij; simp
      · have hne : (⟨i.1, hi⟩ : Fin m) ≠ ⟨j.1, hj⟩ := fun h => hij (Fin.ext (Fin.mk.inj h))
        simp [hij, hne]
    · rename_i hj
      have hij : i ≠ j := fun h => hj (h ▸ hi)
      simp [hij]
  · rename_i hi
    split
    · rename_i hj
      have hij : i ≠ j := fun h => hi (h.symm ▸ hj)
      simp [hij]
    · rename_i hj
      by_cases hij : i = j
      · subst hij; simp
      · have hne : (⟨i.1 - m, by omega⟩ : Fin m) ≠ ⟨j.1 - m, by omega⟩ := by
          intro h; have hval := Fin.mk.inj h; exact hij (Fin.ext (by omega))
        simp [hij, hne]

/-- 2x2 block row1 -= row0 and col1 -= col0: eliminates corner `[[A, B], [C, D]]`. -/
theorem unimodEquiv_block_sub_lower {m : Nat} (A B C D : Mat m) :
    UnimodEquiv (blockMat A B C D)
      (blockMat A (matSub B A) (matSub C A) (matSub (matSub D B) (matSub C A))) := by
  refine ⟨blockLowerElemUnimod (matNeg (matId m)), blockUpperElemUnimod (matNeg (matId m)), ?_⟩
  simp only [blockLowerElemUnimod, blockUpperElemUnimod, blockMat_mul, matId_mul, mul_matId,
             matZero_mul, mul_matZero, neg_matMul, matMul_neg, matAdd_zero_right]
  apply matExt; intro i j
  simp only [blockMat, matAdd, matSub, matNeg]
  split <;> split <;> omega

theorem unimodEquiv_block_corner_lower {m : Nat} (A D : Mat m) :
    UnimodEquiv (blockMat A A A D) (blockMat A (matZero m) (matZero m) (matSub D A)) := by
  have h := unimodEquiv_block_sub_lower A A A D
  have hzero : matSub A A = matZero m := by apply matExt; intro i j; simp [matSub, matZero]
  have hsub0 : matSub (matSub D A) (matZero m) = matSub D A := by
    apply matExt; intro i j; simp [matSub, matZero]
  rw [hzero, hsub0] at h
  exact h

/-- 2x2 block row0 -= row1 and col0 -= col1: eliminates corner `[[A, D], [D, D]]`. -/
theorem unimodEquiv_block_corner_upper {m : Nat} (A D : Mat m) :
    UnimodEquiv (blockMat A D D D) (blockMat (matSub A D) (matZero m) (matZero m) D) := by
  refine ⟨blockUpperElemUnimod (matNeg (matId m)), blockLowerElemUnimod (matNeg (matId m)), ?_⟩
  simp only [blockUpperElemUnimod, blockLowerElemUnimod, blockMat_mul, matId_mul, mul_matId,
             matZero_mul, mul_matZero, neg_matMul, matMul_neg, matAdd_zero_left]
  apply matExt; intro i j
  simp only [blockMat, matAdd, matSub, matNeg, matZero]
  split <;> split <;> omega

-- ----------------------------------------------------------------------------
-- LIFTER 1: Exact Integer Divisibility Block-Schur Elimination (Left & Right)
-- ----------------------------------------------------------------------------

theorem nat_mul_div_of_dvd {a b : Nat} (h : a ∣ b) : a * (b / a) = b := by
  rcases Nat.eq_zero_or_pos a with rfl | hpos
  · rcases h with ⟨k, rfl⟩; simp
  · exact Nat.mul_div_cancel' h

/-- Exact Integer Divisibility Block-Schur Lifter (Lower Block):
    If `A ~ diag(d)` and EVERY invariant factor `d j` divides `L`, then ANY lower-left
    block `C = L • C'` is annihilated unimodularly over `Z` without rational arithmetic:
    `[[A, 0], [L • C', E]] ~ [[A, 0], [0, E]]`. -/
theorem unimodEquiv_blockSchur_lower {m : Nat} {A E C' : Mat m} {d : Fin m → Nat} {L : Nat}
    (hA : UnimodEquiv A (diagMatNat d)) (hdvd : ∀ j, d j ∣ L) :
    UnimodEquiv (blockMat A (matZero m) (matSmul (L : Int) C') E)
                (blockMat A (matZero m) (matZero m) E) := by
  rcases hA with ⟨U, V, hUV⟩
  let CV : Mat m := matMul C' V.val
  have h1 : UnimodEquiv (blockMat A (matZero m) (matSmul (L : Int) C') E)
                        (blockMat (diagMatNat d) (matZero m) (matSmul (L : Int) CV) E) := by
    refine ⟨blockDiagUnimod U (Unimod.id m), blockDiagUnimod V (Unimod.id m), ?_⟩
    simp only [blockDiagUnimod, Unimod.id, blockMat_mul, matId_mul, mul_matId, matZero_mul,
               mul_matZero, matAdd_zero_right, matAdd_zero_left, hUV, smul_matMul, CV]
  let Q : Mat m := fun i j => ((L / d j : Nat) : Int) * CV i j
  have hQ_cancel : matAdd (matMul (matNeg Q) (diagMatNat d)) (matSmul (L : Int) CV) =
                   matZero m := by
    apply matExt; intro i j
    simp only [matAdd, matMul, matNeg, diagMatNat, matSmul, matZero, Q]
    have hs : sumFin m (fun k => -(((L / d k : Nat) : Int) * CV i k) *
                                  (if k = j then (d k : Int) else 0)) =
              sumFin m (fun k => if k = j then -(((L / d k : Nat) : Int) * CV i k * (d k : Int)) else 0) := by
      apply sumFin_congr; intro k
      by_cases hk : k = j
      · subst hk; simp [Int.neg_mul]
      · simp [hk]
    rw [hs, sumFin_single_eq]
    have hmul : (d j : Int) * ((L / d j : Nat) : Int) = (L : Int) := by
      rw [← Int.natCast_mul, nat_mul_div_of_dvd (hdvd j)]
    have hprod : ((L / d j : Nat) : Int) * CV i j * (d j : Int) =
                 (L : Int) * CV i j := by
      calc ((L / d j : Nat) : Int) * CV i j * (d j : Int)
          = ((d j : Int) * ((L / d j : Nat) : Int)) * CV i j := by
            rw [Int.mul_comm (((L / d j : Nat) : Int) * CV i j) (d j : Int),
                ← Int.mul_assoc]
        _ = (L : Int) * CV i j := by rw [hmul]
    rw [hprod]; omega
  have h2 : UnimodEquiv (blockMat (diagMatNat d) (matZero m) (matSmul (L : Int) CV) E)
                        (blockMat (diagMatNat d) (matZero m) (matZero m) E) := by
    refine ⟨blockLowerElemUnimod (matNeg Q), Unimod.id (m + m), ?_⟩
    simp only [blockLowerElemUnimod, Unimod.id, mul_matId, blockMat_mul, matId_mul, matZero_mul,
               mul_matZero, matAdd_zero_right, matAdd_zero_left, hQ_cancel]
  have h3 : UnimodEquiv (blockMat (diagMatNat d) (matZero m) (matZero m) E)
                        (blockMat A (matZero m) (matZero m) E) :=
    unimodEquiv_blockDiag ⟨U.symm, V.symm, by
      simp only [Unimod.symm]; rw [← hUV]
      rw [← matMul_assoc, ← matMul_assoc, U.inv_mul, matId_mul, matMul_assoc, V.mul_inv, mul_matId]⟩
      (UnimodEquiv.refl E)
  exact (h1.trans h2).trans h3

/-- Exact Integer Divisibility Block-Schur Lifter (Upper Block):
    If `A ~ diag(d)` and EVERY invariant factor `d i` divides `L`, then ANY upper-right
    block `B = L • B'` is annihilated unimodularly over `Z`:
    `[[A, L • B'], [0, E]] ~ [[A, 0], [0, E]]`. -/
theorem unimodEquiv_blockSchur_upper {m : Nat} {A E B' : Mat m} {d : Fin m → Nat} {L : Nat}
    (hA : UnimodEquiv A (diagMatNat d)) (hdvd : ∀ i, d i ∣ L) :
    UnimodEquiv (blockMat A (matSmul (L : Int) B') (matZero m) E)
                (blockMat A (matZero m) (matZero m) E) := by
  rcases hA with ⟨U, V, hUV⟩
  let UB : Mat m := matMul U.val B'
  have h1 : UnimodEquiv (blockMat A (matSmul (L : Int) B') (matZero m) E)
                        (blockMat (diagMatNat d) (matSmul (L : Int) UB) (matZero m) E) := by
    refine ⟨blockDiagUnimod U (Unimod.id m), blockDiagUnimod V (Unimod.id m), ?_⟩
    simp only [blockDiagUnimod, Unimod.id, blockMat_mul, matId_mul, mul_matId, matZero_mul,
               mul_matZero, matSmul_zero, matAdd_zero_right, matAdd_zero_left, hUV, matMul_smul, UB]
  let R : Mat m := fun i j => ((L / d i : Nat) : Int) * UB i j
  have hR_cancel : matAdd (matMul (diagMatNat d) (matNeg R)) (matSmul (L : Int) UB) =
                   matZero m := by
    apply matExt; intro i j
    simp only [matAdd, matMul, matNeg, diagMatNat, matSmul, matZero, R]
    have hs : sumFin m (fun k => (if i = k then (d i : Int) else 0) *
                                  -(((L / d k : Nat) : Int) * UB k j)) =
              sumFin m (fun k => if i = k then -((d i : Int) * (((L / d k : Nat) : Int) * UB k j)) else 0) := by
      apply sumFin_congr; intro k
      by_cases hk : i = k
      · subst hk; simp [Int.mul_neg]
      · simp [hk]
    rw [hs, sumFin_single_symm]
    have hmul : (d i : Int) * ((L / d i : Nat) : Int) = (L : Int) := by
      rw [← Int.natCast_mul, nat_mul_div_of_dvd (hdvd i)]
    rw [← Int.mul_assoc, hmul]; omega
  have h2 : UnimodEquiv (blockMat (diagMatNat d) (matSmul (L : Int) UB) (matZero m) E)
                        (blockMat (diagMatNat d) (matZero m) (matZero m) E) := by
    refine ⟨Unimod.id (m + m), blockUpperElemUnimod (matNeg R), ?_⟩
    simp only [blockUpperElemUnimod, Unimod.id, matId_mul, blockMat_mul, mul_matId, matZero_mul,
               mul_matZero, matAdd_zero_right, matAdd_zero_left, hR_cancel]
  have h3 : UnimodEquiv (blockMat (diagMatNat d) (matZero m) (matZero m) E)
                        (blockMat A (matZero m) (matZero m) E) :=
    unimodEquiv_blockDiag ⟨U.symm, V.symm, by
      simp only [Unimod.symm]; rw [← hUV]
      rw [← matMul_assoc, ← matMul_assoc, U.inv_mul, matId_mul, matMul_assoc, V.mul_inv, mul_matId]⟩
      (UnimodEquiv.refl E)
  exact (h1.trans h2).trans h3

-- ----------------------------------------------------------------------------
-- LIFTER 2: LSB Bit-Stride Permutation (Coupled-State Bit-Slice Engine)
-- ----------------------------------------------------------------------------

theorem extGcd_spec (a b : Nat) :
    (Nat.gcd a b : Int) = (a : Int) * (extGcd a b).1 + (b : Int) * (extGcd a b).2 := by
  by_cases hb : b = 0
  · subst hb; unfold extGcd; simp
  · unfold extGcd
    simp only [hb, ↓reduceDIte]
    have ih := extGcd_spec b (a % b)
    have hgcd_step : Nat.gcd a b = Nat.gcd b (a % b) := by
      rw [Nat.gcd_comm a b, Nat.gcd_rec, Nat.gcd_comm]
    rw [hgcd_step, ih]
    have hdiv : (a : Int) = ((a / b : Nat) : Int) * (b : Int) + ((a % b : Nat) : Int) := by
      have hnat : b * (a / b) + a % b = a := Nat.div_add_mod a b
      have hint : (b : Int) * ((a / b : Nat) : Int) + ((a % b : Nat) : Int) = (a : Int) := by
        rw [← Int.natCast_mul, ← Int.natCast_add, hnat]
      rw [Int.mul_comm ((a / b : Nat) : Int) (b : Int)]
      exact hint.symm
    let u := (extGcd b (a % b)).1
    let v := (extGcd b (a % b)).2
    show (b : Int) * u + ((a % b : Nat) : Int) * v =
         (a : Int) * v + (b : Int) * (u - ((a / b : Nat) : Int) * v)
    rw [hdiv, Int.add_mul, Int.mul_sub]
    have hmul : ((a / b : Nat) : Int) * (b : Int) * v = (b : Int) * (((a / b : Nat) : Int) * v) := by
      rw [Int.mul_comm ((a / b : Nat) : Int) (b : Int), Int.mul_assoc]
    rw [hmul]
    omega
termination_by b
decreasing_by exact Nat.mod_lt a (Nat.pos_of_ne_zero hb)

theorem emb2Mat_id {n : Nat} (p q : Fin n) (hpq : p ≠ q) : emb2Mat p q 1 0 0 1 = matId n := by
  apply matExt; intro i j; simp only [emb2Mat, matId]
  by_cases hip : i = p
  · subst hip
    by_cases hjp : j = i
    · subst hjp; simp
    · by_cases hjq : j = q
      · subst hjq; simp [hjp, Ne.symm hjp]
      · simp [hjp, hjq, Ne.symm hjp]
  · by_cases hiq : i = q
    · subst hiq
      by_cases hjp : j = p
      · subst hjp; simp [hip]
      · by_cases hjq : j = i
        · subst hjq; simp [hip]
        · simp [hip, hjp, hjq, Ne.symm hjq]
    · simp [hip, hiq]

theorem emb2Mat_mul {n : Nat} (p q : Fin n) (hpq : p ≠ q)
    (x00 x01 x10 x11 y00 y01 y10 y11 : Int) :
    matMul (emb2Mat p q x00 x01 x10 x11) (emb2Mat p q y00 y01 y10 y11) =
    emb2Mat p q (x00 * y00 + x01 * y10) (x00 * y01 + x01 * y11)
                (x10 * y00 + x11 * y10) (x10 * y01 + x11 * y11) := by
  apply matExt; intro i j
  simp only [matMul, emb2Mat]
  by_cases hip : i = p
  · subst hip
    simp only [↓reduceIte]
    have hsum : sumFin n (fun k =>
        (if k = i then x00 else if k = q then x01 else 0) *
        (if k = i then (if j = i then y00 else if j = q then y01 else 0)
         else if k = q then (if j = i then y10 else if j = q then y11 else 0)
         else if k = j then 1 else 0)) =
        sumFin n (fun k =>
          (if k = i then x00 * (if j = i then y00 else if j = q then y01 else 0) else 0) +
          (if k = q then x01 * (if j = i then y10 else if j = q then y11 else 0) else 0)) := by
      apply sumFin_congr; intro k
      by_cases hkp : k = i
      · subst hkp; simp [hpq]
      · by_cases hkq : k = q
        · subst hkq; simp [Ne.symm hpq]
        · simp [hkp, hkq]
    rw [hsum, sumFin_add, sumFin_single, sumFin_single]
    by_cases hjp : j = i
    · subst hjp; simp
    · by_cases hjq : j = q
      · subst hjq; simp [hjp]
      · simp [hjp, hjq]
  · by_cases hiq : i = q
    · subst hiq
      simp only [hip, ↓reduceIte]
      have hsum : sumFin n (fun k =>
          (if k = p then x10 else if k = i then x11 else 0) *
          (if k = p then (if j = p then y00 else if j = i then y01 else 0)
           else if k = i then (if j = p then y10 else if j = i then y11 else 0)
           else if k = j then 1 else 0)) =
          sumFin n (fun k =>
            (if k = p then x10 * (if j = p then y00 else if j = i then y01 else 0) else 0) +
            (if k = i then x11 * (if j = p then y10 else if j = i then y11 else 0) else 0)) := by
        apply sumFin_congr; intro k
        by_cases hkp : k = p
        · subst hkp; simp [hpq]
        · by_cases hkq : k = i
          · subst hkq; simp [Ne.symm hpq]
          · simp [hkp, hkq]
      rw [hsum, sumFin_add, sumFin_single, sumFin_single]
      by_cases hjp : j = p
      · subst hjp; simp
      · by_cases hjq : j = i
        · subst hjq; simp [hjp]
        · simp [hjp, hjq]
    · simp only [hip, hiq, ↓reduceIte]
      have hsum : sumFin n (fun k =>
          (if i = k then 1 else 0) *
          (if k = p then (if j = p then y00 else if j = q then y01 else 0)
           else if k = q then (if j = p then y10 else if j = q then y11 else 0)
           else if k = j then 1 else 0)) =
          sumFin n (fun k => if i = k then (if k = j then 1 else 0) else 0) := by
        apply sumFin_congr; intro k
        by_cases hik : i = k
        · subst hik; simp [hip, hiq]
        · simp [hik]
      rw [hsum, sumFin_single_symm]

/-- Constructive 2×2 Bezout elimination on ANY two distinct diagonal indices `p ≠ q` of `diagMat d`:
    replaces `(d p, d q)` by `(gcd(|d p|, |d q|), lcm(|d p|, |d q|))` while keeping all other
    diagonal entries unchanged. Works for ALL `a, b : Int` (including `0`)! -/
theorem unimodEquiv_diag_bezout_pair {n : Nat} (d : Fin n → Int) (p q : Fin n) (hpq : p ≠ q) :
    UnimodEquiv (diagMat d)
      (diagMat (fun i =>
        if i = p then (Nat.gcd (d p).natAbs (d q).natAbs : Int)
        else if i = q then (Nat.lcm (d p).natAbs (d q).natAbs : Int)
        else d i)) := by
  let a : Nat := (d p).natAbs
  let b : Nat := (d q).natAbs
  let s : Fin n → Int := fun i =>
    if i = p then (if d p < 0 then -1 else 1)
    else if i = q then (if d q < 0 then -1 else 1)
    else 1
  have hs : ∀ i, s i * s i = 1 := by
    intro i; simp only [s]
    by_cases h1 : i = p
    · simp only [h1, ↓reduceIte]; by_cases hlt : d p < 0 <;> simp [hlt]
    · by_cases h2 : i = q
      · subst h2; simp only [h1, ↓reduceIte]; by_cases hlt : d i < 0 <;> simp [hlt]
      · simp [h1, h2]
  let d1 : Fin n → Int := fun i => if i = p then (a : Int) else if i = q then (b : Int) else d i
  have hstep1 : UnimodEquiv (diagMat d) (diagMat d1) := by
    refine ⟨signUnimod s hs, Unimod.id n, ?_⟩
    simp only [Unimod.id, mul_matId]
    apply matExt; intro i j
    simp only [matMul, signUnimod, diagMat, d1]
    have hsum : sumFin n (fun k => (if i = k then s i else 0) * (if k = j then d k else 0)) =
                sumFin n (fun k => if i = k then (if k = j then s i * d k else 0) else 0) := by
      apply sumFin_congr; intro k
      by_cases h1 : i = k
      · subst h1; by_cases h2 : i = j <;> simp [h2]
      · simp [h1]
    rw [hsum, sumFin_single_symm]
    by_cases hij : i = j
    · subst hij; simp only [↓reduceIte, s, a, b]
      by_cases hip : i = p
      · subst hip; simp only [↓reduceIte]; split <;> omega
      · by_cases hiq : i = q
        · subst hiq; simp only [hip, ↓reduceIte]; split <;> omega
        · simp [hip, hiq]
    · simp [hij]
  apply UnimodEquiv.trans hstep1
  by_cases ha : a = 0
  · refine ⟨permUnimod (Perm.swap p q), permUnimod (Perm.swap p q).symm, ?_⟩
    simp only [permUnimod]
    rw [permMat_mul_left, mul_permMat_symm]
    apply matExt; intro i j
    simp only [diagMat]
    have hgcd : Nat.gcd (d p).natAbs (d q).natAbs = b := by
      change Nat.gcd a b = b; rw [ha, Nat.gcd_zero_left]
    have hlcm : Nat.lcm (d p).natAbs (d q).natAbs = 0 := by
      change Nat.lcm a b = 0; rw [ha, Nat.lcm_zero_left]
    rw [hgcd, hlcm]
    have hiff : (Perm.swap p q).toFun i = (Perm.swap p q).toFun j ↔ i = j := by
      constructor
      · intro h; have := congrArg (Perm.swap p q).invFun h; simpa [(Perm.swap p q).left_inv] using this
      · intro h; rw [h]
    by_cases hij : i = j
    · subst hij; simp only [↓reduceIte, d1, Perm.swap]
      by_cases hip : i = p
      · subst hip; simp [Ne.symm hpq]
      · by_cases hiq : i = q
        · subst hiq; simp [hip, ha]
        · simp [hip, hiq]
    · simp [hij, mt hiff.mp hij]
  · by_cases hb : b = 0
    · have hgcd : Nat.gcd (d p).natAbs (d q).natAbs = a := by
        change Nat.gcd a b = a; rw [hb, Nat.gcd_zero_right]
      have hlcm : Nat.lcm (d p).natAbs (d q).natAbs = 0 := by
        change Nat.lcm a b = 0; rw [hb, Nat.lcm_zero_right]
      have heq : diagMat d1 = diagMat (fun i =>
          if i = p then (Nat.gcd (d p).natAbs (d q).natAbs : Int)
          else if i = q then (Nat.lcm (d p).natAbs (d q).natAbs : Int)
          else d i) := by
        apply matExt; intro i j; simp only [diagMat, d1, hgcd, hlcm, hb]
      rw [heq]; exact UnimodEquiv.refl _
    · let g : Nat := Nat.gcd a b
      have hg_pos : g > 0 := Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha)
      let a' : Int := ((a / g : Nat) : Int)
      let b' : Int := ((b / g : Nat) : Int)
      let u : Int := (extGcd a b).1
      let v : Int := (extGcd a b).2
      have hbez : (g : Int) = (a : Int) * u + (b : Int) * v := extGcd_spec a b
      have ha_eq : (a : Int) = (g : Int) * a' := by
        show (a : Int) = (g : Int) * ((a / g : Nat) : Int)
        rw [← Int.natCast_mul, Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)]
      have hb_eq : (b : Int) = (g : Int) * b' := by
        show (b : Int) = (g : Int) * ((b / g : Nat) : Int)
        rw [← Int.natCast_mul, Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)]
      have huv1 : u * a' + v * b' = 1 := by
        have hmul : (g : Int) * (u * a' + v * b') = (g : Int) * 1 := by
          calc (g : Int) * (u * a' + v * b')
              = (g : Int) * (u * a') + (g : Int) * (v * b') := Int.mul_add _ _ _
            _ = ((g : Int) * a') * u + ((g : Int) * b') * v := by
                congr 1
                · rw [Int.mul_comm u a', ← Int.mul_assoc]
                · rw [Int.mul_comm v b', ← Int.mul_assoc]
            _ = (a : Int) * u + (b : Int) * v := by rw [← ha_eq, ← hb_eq]
            _ = (g : Int) := hbez.symm
            _ = (g : Int) * 1 := (Int.mul_one _).symm
        exact Int.eq_of_mul_eq_mul_left (by omega) hmul
      have hlcm_eq : (Nat.lcm a b : Int) = (g : Int) * a' * b' := by
        have hgl_int : (g : Int) * (Nat.lcm a b : Int) = (a : Int) * (b : Int) := by
          rw [← Int.natCast_mul, ← Int.natCast_mul, Nat.gcd_mul_lcm a b]
        have hmul : (g : Int) * (Nat.lcm a b : Int) = (g : Int) * ((g : Int) * a' * b') := by
          calc (g : Int) * (Nat.lcm a b : Int) = (a : Int) * (b : Int) := hgl_int
            _ = ((g : Int) * a') * ((g : Int) * b') := by rw [ha_eq, hb_eq]
            _ = (g : Int) * (a' * ((g : Int) * b')) := Int.mul_assoc _ _ _
            _ = (g : Int) * ((g : Int) * a' * b') := by
                congr 1
                rw [← Int.mul_assoc, Int.mul_comm a' (g : Int)]
        exact Int.eq_of_mul_eq_mul_left (by omega) hmul
      let U : Unimod n := {
        val := emb2Mat p q u v (-b') a'
        inv := emb2Mat p q a' (-v) b' u
        mul_inv := by
          rw [emb2Mat_mul p q hpq]
          have h1 : u * a' + v * b' = 1 := huv1
          have h2 : u * (-v) + v * u = 0 := by rw [Int.mul_neg, Int.mul_comm u v]; omega
          have h3 : (-b') * a' + a' * b' = 0 := by rw [Int.neg_mul, Int.mul_comm b' a']; omega
          have h4 : (-b') * (-v) + a' * u = 1 := by
            rw [Int.neg_mul_neg, Int.mul_comm b' v, Int.mul_comm a' u]; omega
          rw [h1, h2, h3, h4, emb2Mat_id p q hpq]
        inv_mul := by
          rw [emb2Mat_mul p q hpq]
          have h1 : a' * u + (-v) * (-b') = 1 := by
            rw [Int.neg_mul_neg, Int.mul_comm a' u]; exact huv1
          have h2 : a' * v + (-v) * a' = 0 := by rw [Int.neg_mul, Int.mul_comm v a']; omega
          have h3 : b' * u + u * (-b') = 0 := by rw [Int.mul_neg, Int.mul_comm u b']; omega
          have h4 : b' * v + u * a' = 1 := by rw [Int.mul_comm b' v]; omega
          rw [h1, h2, h3, h4, emb2Mat_id p q hpq]
      }
      let V : Unimod n := {
        val := emb2Mat p q 1 (-(v * b')) 1 (u * a')
        inv := emb2Mat p q (u * a') (v * b') (-1) 1
        mul_inv := by
          rw [emb2Mat_mul p q hpq]
          have h1 : 1 * (u * a') + -(v * b') * (-1) = 1 := by
            rw [Int.one_mul, Int.neg_mul_neg, Int.mul_one]; exact huv1
          have h2 : 1 * (v * b') + -(v * b') * 1 = 0 := by rw [Int.one_mul, Int.mul_one]; omega
          have h3 : 1 * (u * a') + u * a' * (-1) = 0 := by rw [Int.one_mul, Int.mul_neg, Int.mul_one]; omega
          have h4 : 1 * (v * b') + u * a' * 1 = 1 := by rw [Int.one_mul, Int.mul_one]; omega
          rw [h1, h2, h3, h4, emb2Mat_id p q hpq]
        inv_mul := by
          rw [emb2Mat_mul p q hpq]
          have h1 : u * a' * 1 + v * b' * 1 = 1 := by rw [Int.mul_one, Int.mul_one]; exact huv1
          have h2 : u * a' * -(v * b') + v * b' * (u * a') = 0 := by
            rw [Int.mul_neg, Int.mul_comm (u * a') (v * b')]; omega
          have h3 : (-1) * 1 + 1 * 1 = 0 := by decide
          have h4 : (-1) * -(v * b') + 1 * (u * a') = 1 := by
            rw [Int.neg_mul_neg, Int.one_mul, Int.one_mul]; omega
          rw [h1, h2, h3, h4, emb2Mat_id p q hpq]
      }
      refine ⟨U, V, ?_⟩
      have hUD : matMul U.val (diagMat d1) = fun r k => U.val r k * d1 k := by
        apply matExt; intro r k
        simp only [matMul, diagMat]
        have hs : sumFin n (fun t => U.val r t * (if t = k then d1 t else 0)) =
                  sumFin n (fun t => if t = k then U.val r t * d1 t else 0) := by
          apply sumFin_congr; intro t; by_cases ht : t = k <;> simp [ht]
        rw [hs, sumFin_single_eq]
      rw [hUD]
      apply matExt; intro i j
      simp only [matMul, U, V, emb2Mat, diagMat, d1]
      by_cases hip : i = p
      · subst hip
        simp only [↓reduceIte]
        have hsum : sumFin n (fun k =>
            ((if k = i then u else if k = q then v else 0) *
              (if k = i then (a : Int) else if k = q then (b : Int) else d k)) *
            (if k = i then (if j = i then 1 else if j = q then -(v * b') else 0)
             else if k = q then (if j = i then 1 else if j = q then u * a' else 0)
             else if k = j then 1 else 0)) =
            sumFin n (fun k =>
              (if k = i then (u * (a : Int)) * (if j = i then 1 else if j = q then -(v * b') else 0) else 0) +
              (if k = q then (v * (b : Int)) * (if j = i then 1 else if j = q then u * a' else 0) else 0)) := by
          apply sumFin_congr; intro k
          by_cases hkp : k = i
          · subst hkp; simp [hpq]
          · by_cases hkq : k = q
            · subst hkq; simp [Ne.symm hpq]
            · simp [hkp, hkq]
        rw [hsum, sumFin_add, sumFin_single, sumFin_single]
        by_cases hjp : j = i
        · subst hjp; simp only [↓reduceIte, Int.mul_one]
          rw [Int.mul_comm u (a : Int), Int.mul_comm v (b : Int), ← hbez]
        · by_cases hjq : j = q
          · subst hjq; simp only [hjp, Ne.symm hjp, ↓reduceIte]
            rw [ha_eq, hb_eq, Int.mul_neg]
            have heq0 : u * ((g : Int) * a') * (v * b') = v * ((g : Int) * b') * (u * a') := by
              calc u * ((g : Int) * a') * (v * b')
                  = (g : Int) * (u * a') * (v * b') := by
                    rw [Int.mul_comm u ((g : Int) * a'), Int.mul_assoc (g : Int) a' u, Int.mul_comm a' u]
                _ = (g : Int) * ((u * a') * (v * b')) := Int.mul_assoc _ _ _
                _ = (g : Int) * ((v * b') * (u * a')) := by rw [Int.mul_comm (u * a') (v * b')]
                _ = (g : Int) * (v * b') * (u * a') := (Int.mul_assoc _ _ _).symm
                _ = v * ((g : Int) * b') * (u * a') := by
                    rw [Int.mul_comm v ((g : Int) * b'), Int.mul_assoc (g : Int) b' v, Int.mul_comm b' v]
            rw [heq0]; omega
          · simp [hjp, hjq, Ne.symm hjp]
      · by_cases hiq : i = q
        · subst hiq
          simp only [hip, ↓reduceIte]
          have hsum : sumFin n (fun k =>
              ((if k = p then -b' else if k = i then a' else 0) *
                (if k = p then (a : Int) else if k = i then (b : Int) else d k)) *
              (if k = p then (if j = p then 1 else if j = i then -(v * b') else 0)
               else if k = i then (if j = p then 1 else if j = i then u * a' else 0)
               else if k = j then 1 else 0)) =
              sumFin n (fun k =>
                (if k = p then ((-b') * (a : Int)) * (if j = p then 1 else if j = i then -(v * b') else 0) else 0) +
                (if k = i then (a' * (b : Int)) * (if j = p then 1 else if j = i then u * a' else 0) else 0)) := by
            apply sumFin_congr; intro k
            by_cases hkp : k = p
            · subst hkp; simp [hpq]
            · by_cases hkq : k = i
              · subst hkq; simp [Ne.symm hpq]
              · simp [hkp, hkq]
          rw [hsum, sumFin_add, sumFin_single, sumFin_single]
          by_cases hjp : j = p
          · subst hjp; simp only [↓reduceIte, Int.mul_one, hip]
            rw [ha_eq, hb_eq, Int.neg_mul]
            have hba : b' * ((g : Int) * a') = a' * ((g : Int) * b') := by
              rw [Int.mul_comm b' ((g : Int) * a'), Int.mul_assoc, Int.mul_comm a' b',
                  ← Int.mul_assoc, Int.mul_comm ((g : Int) * b') a']
            rw [hba]; omega
          · by_cases hjq : j = i
            · subst hjq; simp only [hjp, ↓reduceIte]
              rw [ha_eq, hb_eq, hlcm_eq]
              have ht1 : (-b') * ((g : Int) * a') * -(v * b') = ((g : Int) * a' * b') * (v * b') := by
                rw [Int.neg_mul, Int.neg_mul_neg, Int.mul_comm b' ((g : Int) * a')]
              have ht2 : a' * ((g : Int) * b') * (u * a') = ((g : Int) * a' * b') * (u * a') := by
                congr 1
                rw [← Int.mul_assoc, Int.mul_comm a' (g : Int)]
              rw [ht1, ht2, ← Int.mul_add, Int.add_comm (v * b') (u * a'), huv1, Int.mul_one]
            · simp [hjp, hjq, Ne.symm hjq]
        · simp only [hip, hiq, ↓reduceIte]
          have hsum : sumFin n (fun k =>
              ((if i = k then 1 else 0) * (if k = p then (a : Int) else if k = q then (b : Int) else d k)) *
              (if k = p then (if j = p then 1 else if j = q then -(v * b') else 0)
               else if k = q then (if j = p then 1 else if j = q then u * a' else 0)
               else if k = j then 1 else 0)) =
              sumFin n (fun k => if i = k then (if k = j then d i else 0) else 0) := by
            apply sumFin_congr; intro k
            by_cases hik : i = k
            · subst hik
              by_cases hij : i = j
              · subst hij; simp [hip, hiq]
              · simp [hip, hiq, hij]
            · simp [hik]
          rw [hsum, sumFin_single_symm]

-- ----------------------------------------------------------------------------
-- LIFTER 4: Additive Rank-1 Bit-Slice Lifter
-- ----------------------------------------------------------------------------

/-- The all-ones matrix `J_m` is unimodularly equivalent to `diag(1, 0, ..., 0)`. -/
theorem unimodEquiv_onesMat (m : Nat) :
    UnimodEquiv (onesMat m) (diagMatNat (fun i => if i.1 = 0 then 1 else 0)) := by
  refine ⟨subRow0Unimod m, (subRow0Unimod m).transpose, ?_⟩
  have h1 : matMul (subRow0Unimod m).val (onesMat m) = fun i _ => if i.1 = 0 then 1 else 0 := by
    apply matExt; intro i j
    simp only [matMul, subRow0Unimod, onesMat, Int.mul_one]
    by_cases hi0 : i.1 = 0
    · have hs : sumFin m (fun k => if i = k then (1 : Int) else if k.1 = 0 then -1 else 0) =
                sumFin m (fun k => if i = k then (1 : Int) else 0) := by
        apply sumFin_congr; intro k
        by_cases hik : i = k
        · simp [hik]
        · have hk0 : k.1 ≠ 0 := fun h => hik (Fin.ext (hi0.trans h.symm))
          simp [hik, hk0]
      rw [hs, sumFin_single_symm]; simp [hi0]
    · have hm : 0 < m := Nat.pos_of_ne_zero (fun h => by omega)
      let z0 : Fin m := ⟨0, hm⟩
      have hne0 : i ≠ z0 := fun h => hi0 (congrArg Fin.val h)
      have hs : sumFin m (fun k => if i = k then (1 : Int) else if k.1 = 0 then -1 else 0) =
                sumFin m (fun k => (if k = i then (1 : Int) else 0) + (if k = z0 then (-1 : Int) else 0)) := by
        apply sumFin_congr; intro k
        by_cases hki : k = i
        · subst hki; simp [hne0]
        · by_cases hkz : k = z0
          · subst hkz; have hz0 : z0.1 = 0 := rfl; simp [hne0, Ne.symm hne0, hz0]
          · have hk0 : k.1 ≠ 0 := fun h => hkz (Fin.ext h)
            simp [Ne.symm hki, hki, hkz, hk0]
      rw [hs, sumFin_add, sumFin_single, sumFin_single]; simp [hi0]
  rw [h1]
  apply matExt; intro i j
  simp only [matMul, Unimod.transpose, matTranspose, subRow0Unimod, diagMatNat]
  by_cases hi0 : i.1 = 0
  · simp only [hi0, ↓reduceIte, Int.one_mul]
    by_cases hj0 : j.1 = 0
    · have hij : i = j := Fin.ext (hi0.trans hj0.symm)
      have hs : sumFin m (fun k => if j = k then (1 : Int) else if k.1 = 0 then -1 else 0) =
                sumFin m (fun k => if j = k then (1 : Int) else 0) := by
        apply sumFin_congr; intro k
        by_cases hjk : j = k
        · simp [hjk]
        · have hk0 : k.1 ≠ 0 := fun h => hjk (Fin.ext (hj0.trans h.symm))
          simp [hjk, hk0]
      rw [hs, sumFin_single_symm]; simp [hij]
    · have hij : i ≠ j := fun h => hj0 (h ▸ hi0)
      have hm : 0 < m := Nat.pos_of_ne_zero (fun h => by omega)
      let z0 : Fin m := ⟨0, hm⟩
      have hne0 : j ≠ z0 := fun h => hj0 (congrArg Fin.val h)
      have hs : sumFin m (fun k => if j = k then (1 : Int) else if k.1 = 0 then -1 else 0) =
                sumFin m (fun k => (if k = j then (1 : Int) else 0) + (if k = z0 then (-1 : Int) else 0)) := by
        apply sumFin_congr; intro k
        by_cases hkj : k = j
        · subst hkj; simp [hne0]
        · by_cases hkz : k = z0
          · subst hkz; have hz0 : z0.1 = 0 := rfl; simp [hne0, Ne.symm hne0, hz0]
          · have hk0 : k.1 ≠ 0 := fun h => hkz (Fin.ext h)
            simp [Ne.symm hkj, hkj, hkz, hk0]
      rw [hs, sumFin_add, sumFin_single, sumFin_single]; simp [hij]
  · simp only [hi0, ↓reduceIte, Int.zero_mul]
    rw [sumFin_zero]
    by_cases hij : i = j <;> simp [hij]

-- ----------------------------------------------------------------------------
-- LIFTER 5: Kronecker Bit-Slice Lifter & Unimodular Selection-Sort Canonicalizer
-- ----------------------------------------------------------------------------

theorem unimodEquiv_kron {m n : Nat} {A A' : Mat m} {B B' : Mat n}
    (hA : UnimodEquiv A A') (hB : UnimodEquiv B B') :
    UnimodEquiv (kronMat A B) (kronMat A' B') := by
  rcases hA with ⟨UA, VA, hUA⟩
  rcases hB with ⟨UB, VB, hUB⟩
  refine ⟨kronUnimod UA UB, kronUnimod VA VB, ?_⟩
  simp only [kronUnimod]
  rw [kronMat_mul, kronMat_mul, hUA, hUB]

theorem argMax_ge (n : Nat) (f : Fin (n + 1) → Nat) :
    ∀ i : Fin (n + 1), f i ≤ f (argMax n f) := by
  induction n with
  | zero =>
    intro i; have : i = ⟨0, by omega⟩ := Fin.ext (by omega); subst this; exact Nat.le_refl _
  | succ n ih =>
    intro i
    simp only [argMax]
    split
    · rename_i hle
      by_cases hi : i.1 < n + 1
      · have h1 := ih (fun j => f j.castSucc) ⟨i.1, hi⟩
        have heq : (⟨i.1, hi⟩ : Fin (n + 1)).castSucc = i := Fin.ext rfl
        rw [heq] at h1
        exact Nat.le_trans h1 hle
      · have heq : i = Fin.last (n + 1) := Fin.ext (by simp [Fin.last]; omega)
        rw [heq]; exact Nat.le_refl _
    · rename_i hgt
      by_cases hi : i.1 < n + 1
      · have h1 := ih (fun j => f j.castSucc) ⟨i.1, hi⟩
        have heq : (⟨i.1, hi⟩ : Fin (n + 1)).castSucc = i := Fin.ext rfl
        rw [heq] at h1; exact h1
      · have heq : i = Fin.last (n + 1) := Fin.ext (by simp [Fin.last]; omega)
        rw [heq]; omega

theorem sortPerm_mono (n : Nat) (f : Fin n → Nat) :
    ∀ i j : Fin n, i.1 ≤ j.1 → f ((sortPerm n f).toFun i) ≤ f ((sortPerm n f).toFun j) := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    intro i j hij
    simp only [sortPerm, Perm.comp, Perm.extendLast]
    let k := argMax n f
    let sw := Perm.swap k (Fin.last n)
    have hlast_max : ∀ x : Fin (n + 1), f (sw.toFun x) ≤ f (sw.toFun (Fin.last n)) := by
      intro x
      have hsw_last : sw.toFun (Fin.last n) = k := by
        simp only [sw, Perm.swap]
        by_cases h : Fin.last n = k
        · simp [h]
        · simp [h]
      rw [hsw_last]
      exact argMax_ge n f (sw.toFun x)
    by_cases hj : j.1 < n
    · have hi : i.1 < n := by omega
      simp only [hi, hj, ↓reduceDIte]
      exact ih (fun r => f (sw.toFun r.castSucc)) ⟨i.1, hi⟩ ⟨j.1, hj⟩ hij
    · have hj_last : ¬(j.1 < n) := hj
      simp only [hj_last, ↓reduceDIte]
      split
      · exact hlast_max _
      · exact Nat.le_refl _

theorem countFin_eq_sumFin (n : Nat) (P : Fin n → Bool) :
    (countFin n P : Int) = sumFin n (fun i => if P i then 1 else 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [countFin, sumFin]
    rw [Int.natCast_add, ih (fun i => P i.castSucc)]
    cases P (Fin.last n) <;> simp

/-- Every permutation preserves exact multiplicity histograms (`countFin`)! -/
theorem countFin_perm {n : Nat} (p : Perm n) (P : Fin n → Bool) :
    countFin n (fun i => P (p.toFun i)) = countFin n P := by
  have h : (countFin n (fun i => P (p.toFun i)) : Int) = (countFin n P : Int) := by
    rw [countFin_eq_sumFin, countFin_eq_sumFin]
    exact sumFin_perm p (fun i => if P i then 1 else 0)
  exact Int.ofNat.inj h

-- ============================================================================
-- PART III: FOUR INFINITE EXACT SNF THEOREM FAMILIES
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Shared Bitwise Primitives & Kummer Carry Identity
-- ----------------------------------------------------------------------------

theorem popcount_zero : popcount 0 = 0 := by unfold popcount; simp

theorem popcount_step (n : Nat) : popcount n = n % 2 + popcount (n / 2) := by
  by_cases h : n = 0
  · subst h; simp [popcount_zero]
  · conv => lhs; unfold popcount
    simp [h]

theorem popcount_two_mul_add (q b : Nat) (hb : b < 2) :
    popcount (2 * q + b) = b + popcount q := by
  rw [popcount_step (2 * q + b)]
  have hmod : (2 * q + b) % 2 = b := by omega
  have hdiv : (2 * q + b) / 2 = q := by omega
  rw [hmod, hdiv]

/-- Kummer's Carry Identity: for all `x, y < 2^k` and `c ≤ 1`,
    `carriesK k x y c` equals the exact full binary carry count
    `popcount(x) + popcount(y) + c - popcount(x + y + c)`. -/
theorem carriesK_kummer (k : Nat) :
    ∀ x y c : Nat, x < 2 ^ k → y < 2 ^ k → c ≤ 1 →
      carriesK k x y c + popcount (x + y + c) = popcount x + popcount y + c := by
  induction k with
  | zero =>
    intro x y c hx hy hc
    have hx0 : x = 0 := by simp at hx; omega
    have hy0 : y = 0 := by simp at hy; omega
    subst hx0; subst hy0
    simp only [carriesK, Nat.zero_add, popcount_zero]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl
    · simp [popcount_zero]
    · rw [popcount_step 1]; simp [popcount_zero]
  | succ k ih =>
    intro x y c hx hy hc
    simp only [carriesK]
    have hx' : x / 2 < 2 ^ k := by rw [Nat.pow_succ] at hx; omega
    have hy' : y / 2 < 2 ^ k := by rw [Nat.pow_succ] at hy; omega
    have hcout : (x % 2 + y % 2 + c) / 2 ≤ 1 := by omega
    have hsum_eq : x + y + c = 2 * (x / 2 + y / 2 + (x % 2 + y % 2 + c) / 2) +
                               (x % 2 + y % 2 + c) % 2 := by omega
    have hpop_sum : popcount (x + y + c) =
        (x % 2 + y % 2 + c) % 2 + popcount (x / 2 + y / 2 + (x % 2 + y % 2 + c) / 2) := by
      rw [hsum_eq, popcount_two_mul_add _ _ (by omega)]
    have hpop_x : popcount x = x % 2 + popcount (x / 2) := popcount_step x
    have hpop_y : popcount y = y % 2 + popcount (y / 2) := popcount_step y
    have hih := ih (x / 2) (y / 2) ((x % 2 + y % 2 + c) / 2) hx' hy' hcout
    omega

theorem pow2_pos (k : Nat) : 0 < 2 ^ k := Nat.pow_pos (by decide)

theorem fin_mk_ne {m a b : Nat} {ha : a < m} {hb : b < m} (h : a ≠ b) :
    (⟨a, ha⟩ : Fin m) ≠ ⟨b, hb⟩ :=
  fun heq => h (Fin.mk.inj heq)

theorem carrySignMat_eq_affine (k : Nat) :
    carrySignMat k = affineCarryParMat k 1 (-2) := by
  apply matExt; intro x y
  simp only [carrySignMat, affineCarryParMat, carryParMat]
  have hmod : carriesK k x.1 y.1 0 % 2 = 0 ∨ carriesK k x.1 y.1 0 % 2 = 1 := by omega
  rcases hmod with h | h <;> simp [h]

/-- Exact LSB 2×2 block decomposition of `C_{k+1}^(0)`. -/
theorem lsb_carryParMat_zero (k : Nat) :
    matMul (matMul (permMat (lsbPerm (2 ^ k))) (castMat (pow2_add_self k).symm (carryParMat (k + 1) 0)))
           (permMat (lsbPerm (2 ^ k)).symm) =
    blockMat (carryParMat k 0) (carryParMat k 0)
             (carryParMat k 0) (matSub (onesMat (2 ^ k)) (carryParMat k 1)) := by
  rw [lsbPerm_conj_eq_blockMat]
  apply matExt; intro i j
  simp only [blockMat, castMat, carryParMat, matSub, onesMat]
  split <;> split
  · have h := carriesK_succ_bit k i.1 j.1 0 0 0 (by decide) (by decide)
    simp only [Nat.add_zero] at h; rw [h]; simp
  · have h := carriesK_succ_bit k i.1 (j.1 - 2 ^ k) 0 1 0 (by decide) (by decide)
    simp only [Nat.add_zero] at h; rw [h]; simp
  · have h := carriesK_succ_bit k (i.1 - 2 ^ k) j.1 1 0 0 (by decide) (by decide)
    simp only [Nat.add_zero] at h; rw [h]; simp
  · have h := carriesK_succ_bit k (i.1 - 2 ^ k) (j.1 - 2 ^ k) 1 1 0 (by decide) (by decide)
    rw [h]; simp only [show (1 + 1 + 0) / 2 = 1 by rfl]; omega

/-- Exact LSB 2×2 block decomposition of `C_{k+1}^(1)`. -/
theorem lsb_carryParMat_one (k : Nat) :
    matMul (matMul (permMat (lsbPerm (2 ^ k))) (castMat (pow2_add_self k).symm (carryParMat (k + 1) 1)))
           (permMat (lsbPerm (2 ^ k)).symm) =
    blockMat (carryParMat k 0) (matSub (onesMat (2 ^ k)) (carryParMat k 1))
             (matSub (onesMat (2 ^ k)) (carryParMat k 1)) (matSub (onesMat (2 ^ k)) (carryParMat k 1)) := by
  rw [lsbPerm_conj_eq_blockMat]
  apply matExt; intro i j
  simp only [blockMat, castMat, carryParMat, matSub, onesMat]
  split <;> split
  · have h := carriesK_succ_bit k i.1 j.1 0 0 1 (by decide) (by decide)
    simp only [Nat.add_zero] at h; rw [h]; simp
  · have h := carriesK_succ_bit k i.1 (j.1 - 2 ^ k) 0 1 1 (by decide) (by decide)
    simp only [Nat.add_zero] at h; rw [h]; simp only [show (0 + 1 + 1) / 2 = 1 by rfl]; omega
  · have h := carriesK_succ_bit k (i.1 - 2 ^ k) j.1 1 0 1 (by decide) (by decide)
    simp only [Nat.add_zero] at h; rw [h]; simp only [show (1 + 0 + 1) / 2 = 1 by rfl]; omega
  · have h := carriesK_succ_bit k (i.1 - 2 ^ k) (j.1 - 2 ^ k) 1 1 1 (by decide) (by decide)
    rw [h]; simp only [show (1 + 1 + 1) / 2 = 1 by rfl]; omega

/-- Unordered diagonalization of `affineCarryParMat k a b` for ALL `k ≥ 0`, `a b : Int`:
    `a J + b C_k^(0) ~ diag(a, b, b, ..., b)`. -/
theorem affineCarryParMat_diag_equiv (k : Nat) (a b : Int) :
    UnimodEquiv (affineCarryParMat k a b) (diagMat (fun i => if i.1 = 0 then a else b)) := by
  induction k with
  | zero =>
    have heq : affineCarryParMat 0 a b = diagMat (fun i : Fin (2 ^ 0) => if i.1 = 0 then a else b) := by
      apply matExt; intro i j
      have hi : i = ⟨0, by decide⟩ := Fin.ext (by omega)
      have hj : j = ⟨0, by decide⟩ := Fin.ext (by omega)
      subst hi; subst hj
      simp [affineCarryParMat, carryParMat, carriesK, diagMat]
    rw [heq]; exact UnimodEquiv.refl _
  | succ k ih =>
    -- Conjugate by lsbPerm (2^k) after casting to 2^k + 2^k
    have hlsb : matMul (matMul (permMat (lsbPerm (2 ^ k)))
                               (castMat (pow2_add_self k).symm (affineCarryParMat (k + 1) a b)))
                       (permMat (lsbPerm (2 ^ k)).symm) =
        blockMat (affineCarryParMat k a b)
                 (affineCarryParMat k a b)
                 (affineCarryParMat k a b)
                 (matAdd (matSmul a (onesMat (2 ^ k)))
                         (matSmul b (matSub (onesMat (2 ^ k)) (carryParMat k 1)))) := by
      rw [lsbPerm_conj_eq_blockMat]
      have hc0 := lsb_carryParMat_zero k
      rw [lsbPerm_conj_eq_blockMat] at hc0
      apply matExt; intro i j
      have h0ij := congrFun (congrFun hc0 i) j
      simp only [blockMat, castMat, affineCarryParMat, matAdd, matSmul, matSub, onesMat] at h0ij ⊢
      split
      · rename_i hi
        split
        · rename_i hj; simp only [hi, hj, ↓reduceDIte] at h0ij; rw [h0ij]
        · rename_i hj; simp only [hi, hj, ↓reduceDIte] at h0ij; rw [h0ij]
      · rename_i hi
        split
        · rename_i hj; simp only [hi, hj, ↓reduceDIte] at h0ij; rw [h0ij]
        · rename_i hj; simp only [hi, hj, ↓reduceDIte] at h0ij; rw [h0ij, Int.mul_one]
    have hstep1 : UnimodEquiv (castMat (pow2_add_self k).symm (affineCarryParMat (k + 1) a b))
        (blockMat (affineCarryParMat k a b) (matZero (2 ^ k)) (matZero (2 ^ k))
                  (matSmul (-b) (carryCouplingMat k))) := by
      have hperm : UnimodEquiv (castMat (pow2_add_self k).symm (affineCarryParMat (k + 1) a b))
          (blockMat (affineCarryParMat k a b) (affineCarryParMat k a b) (affineCarryParMat k a b)
                    (matAdd (matSmul a (onesMat (2 ^ k)))
                            (matSmul b (matSub (onesMat (2 ^ k)) (carryParMat k 1))))) :=
        ⟨permUnimod (lsbPerm (2 ^ k)), permUnimod (lsbPerm (2 ^ k)).symm, hlsb⟩
      have hcor := unimodEquiv_block_corner_lower (affineCarryParMat k a b)
        (matAdd (matSmul a (onesMat (2 ^ k)))
                (matSmul b (matSub (onesMat (2 ^ k)) (carryParMat k 1))))
      have hdiff : matSub (matAdd (matSmul a (onesMat (2 ^ k)))
                                  (matSmul b (matSub (onesMat (2 ^ k)) (carryParMat k 1))))
                          (affineCarryParMat k a b) =
                   matSmul (-b) (carryCouplingMat k) := by
        apply matExt; intro i j
        simp only [matSub, matAdd, matSmul, onesMat, affineCarryParMat, carryCouplingMat]
        rw [Int.mul_one, Int.mul_sub, Int.mul_one, Int.neg_mul, Int.mul_sub, Int.mul_add, Int.mul_one]
        omega
      rw [hdiff] at hcor
      exact hperm.trans hcor
    -- Lower-right block (-b) * S_k ~ (-b) * I ~ b * I
    have hSk_equiv : UnimodEquiv (matSmul (-b) (carryCouplingMat k)) (diagMat (fun _ => b)) := by
      let ⟨Sk, hSk⟩ := carryCouplingUnimod k
      have h1 : UnimodEquiv (carryCouplingMat k) (matId (2 ^ k)) := by
        rw [← hSk]; exact UnimodEquiv.of_unimod Sk
      have h2 := h1.smul_both (-b)
      have h3 : UnimodEquiv (matSmul (-b) (matId (2 ^ k))) (matNeg (matSmul (-b) (matId (2 ^ k)))) :=
        (UnimodEquiv.refl _).neg_right
      have h4 : matNeg (matSmul (-b) (matId (2 ^ k))) = diagMat (fun _ => b) := by
        apply matExt; intro i j
        simp only [matNeg, matSmul, matId, diagMat]
        by_cases hij : i = j
        · subst hij; simp
        · simp [hij]
      rw [h4] at h3
      exact h2.trans h3
    have hdiag_blk := unimodEquiv_blockDiag ih hSk_equiv
    have hcomb := hstep1.trans hdiag_blk
    have hblk_eq : blockMat (diagMat (fun i : Fin (2 ^ k) => if i.1 = 0 then a else b))
                            (matZero (2 ^ k)) (matZero (2 ^ k))
                            (diagMat (fun _ : Fin (2 ^ k) => b)) =
                   castMat (pow2_add_self k).symm (diagMat (fun i : Fin (2 ^ (k + 1)) => if i.1 = 0 then a else b)) := by
      apply matExt; intro i j
      simp only [blockMat, diagMat, matZero, castMat]
      split
      · rename_i hi
        split
        · rename_i hj
          by_cases hij : i = j
          · subst hij; simp
          · have hval : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
            simp [fin_mk_ne hval]
        · rename_i hj
          have hval : i.1 ≠ j.1 := by omega
          simp [fin_mk_ne hval]
      · rename_i hi
        split
        · rename_i hj
          have hval : i.1 ≠ j.1 := by omega
          simp [fin_mk_ne hval]
        · rename_i hj
          by_cases hij : i = j
          · subst hij
            have hne0 : i.1 ≠ 0 := by have := pow2_pos k; omega
            simp [hne0]
          · have hval : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
            have hval2 : i.1 - 2 ^ k ≠ j.1 - 2 ^ k := by omega
            simp [fin_mk_ne hval, fin_mk_ne hval2]
    rw [hblk_eq] at hcomb
    have hfinal := unimodEquiv_cast (pow2_add_self k) hcomb
    have hcast_id : ∀ (A : Mat (2 ^ (k + 1))),
        castMat (pow2_add_self k) (castMat (pow2_add_self k).symm A) = A := by
      intro A; apply matExt; intro i j; rfl
    rw [hcast_id, hcast_id] at hfinal
    exact hfinal

/-- **THEOREM 1 (Exact Canonical SNF of the 2-Parameter Affine Carry-Parity Matrix Family)**:
    For ALL `k ≥ 1` and ALL `a, b : Int` (zero side conditions!),
    `a + b · (carries(x, y) mod 2)` has exact canonical Smith Normal Form diagonal
    `(gcd(|a|, |b|)^1, |b|^{2^k - 2}, lcm(|a|, |b|)^1)`. -/
theorem snf_affine_carry_parity (k : Nat) (hk : 1 ≤ k) (a b : Int) :
    HasSNF (affineCarryParMat k a b) (affineCarrySNFDiag k a b) := by
  have h2k : 2 ≤ 2 ^ k := by
    have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
    simpa using this
  let p : Fin (2 ^ k) := ⟨0, by omega⟩
  let q : Fin (2 ^ k) := ⟨2 ^ k - 1, by omega⟩
  have hpq : p ≠ q := by intro h; have := congrArg Fin.val h; simp [p, q] at this; omega
  constructor
  · have h1 := affineCarryParMat_diag_equiv k a b
    have h2 := unimodEquiv_diag_bezout_pair (fun i : Fin (2 ^ k) => if i.1 = 0 then a else b) p q hpq
    have h3 := UnimodEquiv.diag_abs (fun i : Fin (2 ^ k) =>
      if i = p then (Nat.gcd (if p.1 = 0 then a else b).natAbs (if q.1 = 0 then a else b).natAbs : Int)
      else if i = q then (Nat.lcm (if p.1 = 0 then a else b).natAbs (if q.1 = 0 then a else b).natAbs : Int)
      else if i.1 = 0 then a else b)
    have hfin : diagMatNat (fun i : Fin (2 ^ k) =>
        (if i = p then (Nat.gcd (if p.1 = 0 then a else b).natAbs (if q.1 = 0 then a else b).natAbs : Int)
         else if i = q then (Nat.lcm (if p.1 = 0 then a else b).natAbs (if q.1 = 0 then a else b).natAbs : Int)
         else if i.1 = 0 then a else b).natAbs) =
        diagMatNat (affineCarrySNFDiag k a b) := by
      apply matExt; intro i j
      simp only [diagMatNat, affineCarrySNFDiag]
      by_cases hij : i = j
      · subst hij; simp only [↓reduceIte]
        have hp0 : p.1 = 0 := rfl
        have hq0 : q.1 ≠ 0 := by simp [q]; omega
        by_cases hi0 : i.1 = 0
        · have hip : i = p := Fin.ext hi0
          simp [hip, hp0, hq0]
        · have hip : i ≠ p := fun h => hi0 (congrArg Fin.val h)
          by_cases hiq : i.1 + 1 = 2 ^ k
          · have heqq : i = q := Fin.ext (by simp [q]; omega)
            subst heqq
            simp [Ne.symm hpq, hp0, hq0, hiq]
          · have hneq : i ≠ q := fun h => hiq (by have := congrArg Fin.val h; simp [q] at this; omega)
            simp [hip, hneq, hi0, hiq]
      · simp [hij]
    rw [hfin] at h3
    exact (h1.trans h2).trans h3
  · -- Canonical divisibility chain: gcd(|a|,|b|) | |b| | lcm(|a|,|b|) (and gcd | lcm when k=1)
    intro i hi
    simp only [affineCarrySNFDiag]
    by_cases hi0 : i.1 = 0
    · simp only [hi0, ↓reduceIte, show ¬((0 : Nat) + 1 = 0) by omega]
      by_cases hlast : (0 : Nat) + 1 + 1 = 2 ^ k
      · simp only [hlast, ↓reduceIte]
        exact Nat.dvd_trans (Nat.gcd_dvd_left a.natAbs b.natAbs) (Nat.dvd_lcm_left a.natAbs b.natAbs)
      · simp only [hlast, ↓reduceIte]
        exact Nat.gcd_dvd_right a.natAbs b.natAbs
    · have hnotlast : i.1 + 1 ≠ 2 ^ k := by omega
      have hnext0 : i.1 + 1 ≠ 0 := by omega
      simp only [hi0, hnotlast, hnext0, ↓reduceIte]
      by_cases hlast : i.1 + 1 + 1 = 2 ^ k
      · simp only [hlast, ↓reduceIte]
        exact Nat.dvd_lcm_right a.natAbs b.natAbs
      · simp only [hlast, ↓reduceIte]
        exact Nat.dvd_refl _

/-- **COROLLARY 1a (Exact SNF of the Binary Carry-Parity Matrix `C_k^(0)`)**:
    For ALL `k ≥ 1`, `C_k^(0)(x, y) = carries(x, y, 0) mod 2` has exact canonical SNF
    `(1, 1, ..., 1, 0)` (rank `2^k - 1`, unimodular nonzero block!). -/
theorem snf_carry_parity_zero (k : Nat) (hk : 1 ≤ k) :
    HasSNF (carryParMat k 0) (fun i : Fin (2 ^ k) => if i.1 + 1 = 2 ^ k then 0 else 1) := by
  have h := snf_affine_carry_parity k hk 0 1
  have hmat : affineCarryParMat k 0 1 = carryParMat k 0 := by
    apply matExt; intro i j; simp [affineCarryParMat]
  have hdiag : affineCarrySNFDiag k 0 1 = fun i : Fin (2 ^ k) => if i.1 + 1 = 2 ^ k then 0 else 1 := by
    funext i; simp only [affineCarrySNFDiag]
    have h2k : 2 ≤ 2 ^ k := by
      have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk; simpa using this
    by_cases hi0 : i.1 = 0
    · have h1ne : (1 : Nat) ≠ 2 ^ k := by omega
      simp [hi0, h1ne]
    · by_cases hl : i.1 + 1 = 2 ^ k <;> simp [hi0, hl]
  rw [hmat, hdiag] at h
  exact h

/-- **COROLLARY 1b (Flat SNF of Binary Carry-Parity Sign Matrix `(-1)^{carries(x, y)}`)**:
    For ALL `k ≥ 1`, `(-1)^{carries(x, y)}` has FLAT canonical SNF `(1, 2, 2, ..., 2)`
    (contrasting starkly with Walsh-Hadamard `(-1)^{popcount(x & y)}` whose SNF grows up to `2^k`). -/
theorem snf_carry_sign_flat (k : Nat) (hk : 1 ≤ k) :
    HasSNF (carrySignMat k) (fun i : Fin (2 ^ k) => if i.1 = 0 then 1 else 2) := by
  have h := snf_affine_carry_parity k hk 1 (-2)
  rw [← carrySignMat_eq_affine] at h
  have hdiag : affineCarrySNFDiag k 1 (-2) = fun i : Fin (2 ^ k) => if i.1 = 0 then 1 else 2 := by
    funext i; simp only [affineCarrySNFDiag]
    by_cases hi0 : i.1 = 0
    · simp [hi0]
    · by_cases hl : i.1 + 1 = 2 ^ k <;> simp [hi0, hl]
  rw [hdiag] at h
  exact h

/-- **THEOREM 1c (Carry-In Parity Dichotomy for `C_k^(1) = carries(x, y, 1) mod 2`)**:
    For ALL `k ≥ 0`:
    - When `k` is ODD, `C_k^(1)` is UNIMODULAR (`HasSNF = [1^{2^k}]`, `∈ GL_{2^k}(Z)`);
    - When `k` is EVEN, `C_k^(1)` has corank 1 (`HasSNF = [1^{2^k - 1}, 0]`). -/
theorem snf_carry_parity_one_coupled (k : Nat) :
    HasSNF (carryParMat k 1)
      (fun i : Fin (2 ^ k) => if k % 2 = 1 then 1 else if i.1 + 1 = 2 ^ k then 0 else 1) ∧
    HasSNF (matSub (onesMat (2 ^ k)) (carryParMat k 1))
      (fun i : Fin (2 ^ k) => if k % 2 = 0 then 1 else if i.1 + 1 = 2 ^ k then 0 else 1) := by
  induction k with
  | zero =>
    constructor
    · constructor
      · have h0 : carryParMat 0 1 = diagMatNat (fun _ : Fin (2 ^ 0) => 0) := by
          apply matExt; intro i j
          have hi : i = ⟨0, by decide⟩ := Fin.ext (by omega)
          have hj : j = ⟨0, by decide⟩ := Fin.ext (by omega)
          subst hi; subst hj; simp [carryParMat, carriesK, diagMatNat]
        have hd : (fun i : Fin (2 ^ 0) => if 0 % 2 = 1 then 1 else if i.1 + 1 = 2 ^ 0 then 0 else 1) =
                  (fun _ : Fin (2 ^ 0) => 0) := by
          funext i; have : i.1 = 0 := by omega
          simp [Nat.pow_zero]
        rw [h0, hd]; exact UnimodEquiv.refl _
      · intro i hi; omega
    · constructor
      · have h1 : matSub (onesMat (2 ^ 0)) (carryParMat 0 1) = diagMatNat (fun _ : Fin (2 ^ 0) => 1) := by
          apply matExt; intro i j
          have hi : i = ⟨0, by decide⟩ := Fin.ext (by omega)
          have hj : j = ⟨0, by decide⟩ := Fin.ext (by omega)
          subst hi; subst hj; simp [matSub, onesMat, carryParMat, carriesK, diagMatNat]
        have hd : (fun i : Fin (2 ^ 0) => if 0 % 2 = 0 then 1 else if i.1 + 1 = 2 ^ 0 then 0 else 1) =
                  (fun _ : Fin (2 ^ 0) => 1) := by funext i; simp
        rw [h1, hd]; exact UnimodEquiv.refl _
      · intro i hi; omega
  | succ k ih =>
    rcases ih with ⟨ihC1, ihJC1⟩
    let ⟨Sk, hSk⟩ := carryCouplingUnimod k
    have hSk_id : UnimodEquiv (carryCouplingMat k) (diagMatNat (fun _ : Fin (2 ^ k) => 1)) := by
      have hid : diagMatNat (fun _ : Fin (2 ^ k) => 1) = matId (2 ^ k) := by
        apply matExt; intro i j; simp [diagMatNat, matId]
      rw [hid, ← hSk]; exact UnimodEquiv.of_unimod Sk
    have hdvd_chain : ∀ (n : Nat) (b : Bool),
        ∀ (i : Fin n) (hi : i.1 + 1 < n),
          (if b then 1 else if i.1 + 1 = n then 0 else 1) ∣
          (if b then 1 else if i.1 + 1 + 1 = n then 0 else 1) := by
      intro n b i hi
      cases b
      · have hnl : i.1 + 1 ≠ n := by omega
        simp only [Bool.false_eq_true, ↓reduceIte, hnl]; exact Nat.one_dvd _
      · simp
    have hC1_step : UnimodEquiv (castMat (pow2_add_self k).symm (carryParMat (k + 1) 1))
        (blockMat (carryCouplingMat k) (matZero (2 ^ k)) (matZero (2 ^ k))
                  (matSub (onesMat (2 ^ k)) (carryParMat k 1))) := by
      have hperm : UnimodEquiv (castMat (pow2_add_self k).symm (carryParMat (k + 1) 1))
          (blockMat (carryParMat k 0) (matSub (onesMat (2 ^ k)) (carryParMat k 1))
                    (matSub (onesMat (2 ^ k)) (carryParMat k 1))
                    (matSub (onesMat (2 ^ k)) (carryParMat k 1))) :=
        ⟨permUnimod (lsbPerm (2 ^ k)), permUnimod (lsbPerm (2 ^ k)).symm, lsb_carryParMat_one k⟩
      have hcor := unimodEquiv_block_corner_upper (carryParMat k 0)
                    (matSub (onesMat (2 ^ k)) (carryParMat k 1))
      have hdiff : matSub (carryParMat k 0) (matSub (onesMat (2 ^ k)) (carryParMat k 1)) =
                   carryCouplingMat k := by
        apply matExt; intro i j; simp only [matSub, onesMat, carryCouplingMat]; omega
      rw [hdiff] at hcor
      exact hperm.trans hcor
    have hJC1_step : UnimodEquiv (castMat (pow2_add_self k).symm (matSub (onesMat (2 ^ (k + 1))) (carryParMat (k + 1) 1)))
        (blockMat (matNeg (carryCouplingMat k)) (matZero (2 ^ k)) (matZero (2 ^ k))
                  (carryParMat k 1)) := by
      have hlsb_jc1 : matMul (matMul (permMat (lsbPerm (2 ^ k)))
                                     (castMat (pow2_add_self k).symm (matSub (onesMat (2 ^ (k + 1))) (carryParMat (k + 1) 1))))
                             (permMat (lsbPerm (2 ^ k)).symm) =
          blockMat (matSub (onesMat (2 ^ k)) (carryParMat k 0))
                   (carryParMat k 1) (carryParMat k 1) (carryParMat k 1) := by
        rw [lsbPerm_conj_eq_blockMat]
        have hc1 := lsb_carryParMat_one k
        rw [lsbPerm_conj_eq_blockMat] at hc1
        apply matExt; intro i j
        have h1ij := congrFun (congrFun hc1 i) j
        simp only [blockMat, castMat, matSub, onesMat] at h1ij ⊢
        split
        · rename_i hi
          split
          · rename_i hj; simp only [hi, hj, ↓reduceDIte] at h1ij; omega
          · rename_i hj; simp only [hi, hj, ↓reduceDIte] at h1ij; omega
        · rename_i hi
          split
          · rename_i hj; simp only [hi, hj, ↓reduceDIte] at h1ij; omega
          · rename_i hj; simp only [hi, hj, ↓reduceDIte] at h1ij; omega
      have hperm : UnimodEquiv (castMat (pow2_add_self k).symm (matSub (onesMat (2 ^ (k + 1))) (carryParMat (k + 1) 1)))
          (blockMat (matSub (onesMat (2 ^ k)) (carryParMat k 0))
                    (carryParMat k 1) (carryParMat k 1) (carryParMat k 1)) :=
        ⟨permUnimod (lsbPerm (2 ^ k)), permUnimod (lsbPerm (2 ^ k)).symm, hlsb_jc1⟩
      have hcor := unimodEquiv_block_corner_upper (matSub (onesMat (2 ^ k)) (carryParMat k 0))
                    (carryParMat k 1)
      have hdiff : matSub (matSub (onesMat (2 ^ k)) (carryParMat k 0)) (carryParMat k 1) =
                   matNeg (carryCouplingMat k) := by
        apply matExt; intro i j; simp only [matSub, onesMat, matNeg, carryCouplingMat]; omega
      rw [hdiff] at hcor
      exact hperm.trans hcor
    constructor
    · constructor
      · have hdiag := hC1_step.trans (unimodEquiv_blockDiag hSk_id ihJC1.1)
        rw [blockDiag_diagMatNat] at hdiag
        have hcast := unimodEquiv_cast (pow2_add_self k) hdiag
        have hEq1 : castMat (pow2_add_self k) (castMat (pow2_add_self k).symm (carryParMat (k + 1) 1)) =
                    carryParMat (k + 1) 1 := by apply matExt; intro i j; rfl
        have hEq2 : castMat (pow2_add_self k) (diagMatNat (fun i : Fin (2 ^ k + 2 ^ k) =>
            if h : i.1 < 2 ^ k then 1
            else if k % 2 = 0 then 1 else if (i.1 - 2 ^ k) + 1 = 2 ^ k then 0 else 1)) =
            diagMatNat (fun i : Fin (2 ^ (k + 1)) =>
              if (k + 1) % 2 = 1 then 1 else if i.1 + 1 = 2 ^ (k + 1) then 0 else 1) := by
          apply matExt; intro i j
          simp only [castMat, diagMatNat]
          by_cases hij : i = j
          · subst hij
            have hpow := pow2_add_self k
            simp only [↓reduceIte]
            by_cases hkpar : k % 2 = 0
            · have hk1 : (k + 1) % 2 = 1 := by omega
              simp [hkpar, hk1]
            · have hk1 : (k + 1) % 2 ≠ 1 := by omega
              simp only [hkpar, hk1, ↓reduceIte]
              by_cases hi : i.1 < 2 ^ k
              · have hnl : i.1 + 1 ≠ 2 ^ (k + 1) := by omega
                simp [hi, hnl]
              · have hiff : (i.1 - 2 ^ k + 1 = 2 ^ k) ↔ (i.1 + 1 = 2 ^ (k + 1)) := by omega
                by_cases hl : i.1 + 1 = 2 ^ (k + 1)
                · simp [hi, hl, hiff.mpr hl]
                · simp [hi, hl, mt hiff.mp hl]
          · have hval : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
            simp [hij, fin_mk_ne hval]
        rw [hEq1, hEq2] at hcast
        exact hcast
      · intro i hi
        have h := hdvd_chain (2 ^ (k + 1)) (decide ((k + 1) % 2 = 1)) i hi
        simpa using h
    · constructor
      · have hdiag := hJC1_step.trans (unimodEquiv_blockDiag hSk_id.neg_left ihC1.1)
        rw [blockDiag_diagMatNat] at hdiag
        have hcast := unimodEquiv_cast (pow2_add_self k) hdiag
        have hEq1 : castMat (pow2_add_self k) (castMat (pow2_add_self k).symm (matSub (onesMat (2 ^ (k + 1))) (carryParMat (k + 1) 1))) =
                    matSub (onesMat (2 ^ (k + 1))) (carryParMat (k + 1) 1) := by apply matExt; intro i j; rfl
        have hEq2 : castMat (pow2_add_self k) (diagMatNat (fun i : Fin (2 ^ k + 2 ^ k) =>
            if h : i.1 < 2 ^ k then 1
            else if k % 2 = 1 then 1 else if (i.1 - 2 ^ k) + 1 = 2 ^ k then 0 else 1)) =
            diagMatNat (fun i : Fin (2 ^ (k + 1)) =>
              if (k + 1) % 2 = 0 then 1 else if i.1 + 1 = 2 ^ (k + 1) then 0 else 1) := by
          apply matExt; intro i j
          simp only [castMat, diagMatNat]
          by_cases hij : i = j
          · subst hij
            have hpow := pow2_add_self k
            simp only [↓reduceIte]
            by_cases hkpar : k % 2 = 1
            · have hk1 : (k + 1) % 2 = 0 := by omega
              simp [hkpar, hk1]
            · have hk1 : (k + 1) % 2 ≠ 0 := by omega
              simp only [hkpar, hk1, ↓reduceIte]
              by_cases hi : i.1 < 2 ^ k
              · have hnl : i.1 + 1 ≠ 2 ^ (k + 1) := by omega
                simp [hi, hnl]
              · have hiff : (i.1 - 2 ^ k + 1 = 2 ^ k) ↔ (i.1 + 1 = 2 ^ (k + 1)) := by omega
                by_cases hl : i.1 + 1 = 2 ^ (k + 1)
                · simp [hi, hl, hiff.mpr hl]
                · simp [hi, hl, mt hiff.mp hl]
          · have hval : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
            simp [hij, fin_mk_ne hval]
        rw [hEq1, hEq2] at hcast
        exact hcast
      · intro i hi
        have h := hdvd_chain (2 ^ (k + 1)) (decide ((k + 1) % 2 = 0)) i hi
        simpa using h

theorem snf_carry_parity_one_dichotomy (k : Nat) :
    HasSNF (carryParMat k 1)
      (fun i : Fin (2 ^ k) => if k % 2 = 1 then 1 else if i.1 + 1 = 2 ^ k then 0 else 1) :=
  (snf_carry_parity_one_coupled k).1

-- ============================================================================
-- THEOREM 2 (FLAGSHIP NON-KRONECKER #2):
-- ADD-XOR CARRY-DIFFERENCE MATRIX `D_k`, `T_k^(1) = (x+y+1) ^^^ x`, AND
-- EXACT HALF-RANK TRUNCATION COLLAPSE VIA DIVISIBILITY BLOCK-SCHUR LIFTING
-- ============================================================================

/-- Exact column-difference identity: `T_k^(1) · Δ = D_k` (so `T_k^(1) ~ D_k` in 1 line!). -/
theorem T1Mat_mul_delta (k : Nat) :
    matMul (T1Mat k) (deltaUnimod (2 ^ k)).val = DMat k := by
  apply matExt; intro x y
  simp only [matMul, T1Mat, DMat, deltaUnimod]
  by_cases hy0 : 0 < y.1
  · let prev : Fin (2 ^ k) := ⟨y.1 - 1, by omega⟩
    have hne : prev ≠ y := by intro h; have := congrArg Fin.val h; simp [prev] at this; omega
    have hsum : sumFin (2 ^ k) (fun r => (((x.1 + r.1 + 1) ^^^ x.1 : Nat) : Int) *
                                          (if r = y then 1 else if r.1 + 1 = y.1 then -1 else 0)) =
                sumFin (2 ^ k) (fun r => (if r = y then (((x.1 + y.1 + 1) ^^^ x.1 : Nat) : Int) else 0) +
                                         (if r = prev then -(((x.1 + prev.1 + 1) ^^^ x.1 : Nat) : Int) else 0)) := by
      apply sumFin_congr; intro r
      by_cases hry : r = y
      · subst hry; simp [Ne.symm hne]
      · by_cases hrp : r = prev
        · subst hrp; have hadd : prev.1 + 1 = y.1 := by simp [prev]; omega
          simp [hne, hadd]
        · have hrval : r.1 + 1 ≠ y.1 := fun h => hrp (Fin.ext (by simp [prev]; omega))
          simp [hry, hrp, hrval]
    rw [hsum, sumFin_add, sumFin_single, sumFin_single]
    have hprev_add : x.1 + prev.1 + 1 = x.1 + y.1 := by simp [prev]; omega
    rw [hprev_add]; omega
  · have hyz : y.1 = 0 := by omega
    have hsum : sumFin (2 ^ k) (fun r => (((x.1 + r.1 + 1) ^^^ x.1 : Nat) : Int) *
                                          (if r = y then 1 else if r.1 + 1 = y.1 then -1 else 0)) =
                sumFin (2 ^ k) (fun r => if r = y then (((x.1 + y.1 + 1) ^^^ x.1 : Nat) : Int) else 0) := by
      apply sumFin_congr; intro r
      by_cases hry : r = y
      · subst hry; simp
      · have hrval : r.1 + 1 ≠ y.1 := by omega
        simp [hry, hrval]
    rw [hsum, sumFin_single, hyz]
    simp

/-- Exact truncated column-difference identity: `T_{k,mod}^(1) · Δ = D_{k,mod}`. -/
theorem T1ModMat_mul_delta (k : Nat) :
    matMul (T1ModMat k) (deltaUnimod (2 ^ k)).val = DModMat k := by
  apply matExt; intro x y
  simp only [matMul, T1ModMat, DModMat, deltaUnimod]
  by_cases hy0 : 0 < y.1
  · let prev : Fin (2 ^ k) := ⟨y.1 - 1, by omega⟩
    have hne : prev ≠ y := by intro h; have := congrArg Fin.val h; simp [prev] at this; omega
    have hsum : sumFin (2 ^ k) (fun r => ((((x.1 + r.1 + 1) ^^^ x.1) % 2 ^ k : Nat) : Int) *
                                          (if r = y then 1 else if r.1 + 1 = y.1 then -1 else 0)) =
                sumFin (2 ^ k) (fun r => (if r = y then ((((x.1 + y.1 + 1) ^^^ x.1) % 2 ^ k : Nat) : Int) else 0) +
                                         (if r = prev then -((((x.1 + prev.1 + 1) ^^^ x.1) % 2 ^ k : Nat) : Int) else 0)) := by
      apply sumFin_congr; intro r
      by_cases hry : r = y
      · subst hry; simp [Ne.symm hne]
      · by_cases hrp : r = prev
        · subst hrp; have hadd : prev.1 + 1 = y.1 := by simp [prev]; omega
          simp [hne, hadd]
        · have hrval : r.1 + 1 ≠ y.1 := fun h => hrp (Fin.ext (by simp [prev]; omega))
          simp [hry, hrp, hrval]
    rw [hsum, sumFin_add, sumFin_single, sumFin_single]
    have hprev_add : x.1 + prev.1 + 1 = x.1 + y.1 := by simp [prev]; omega
    rw [hprev_add]; omega
  · have hyz : y.1 = 0 := by omega
    have hsum : sumFin (2 ^ k) (fun r => ((((x.1 + r.1 + 1) ^^^ x.1) % 2 ^ k : Nat) : Int) *
                                          (if r = y then 1 else if r.1 + 1 = y.1 then -1 else 0)) =
                sumFin (2 ^ k) (fun r => if r = y then ((((x.1 + y.1 + 1) ^^^ x.1) % 2 ^ k : Nat) : Int) else 0) := by
      apply sumFin_congr; intro r
      by_cases hry : r = y
      · subst hry; simp
      · have hrval : r.1 + 1 ≠ y.1 := by omega
        simp [hry, hrval]
    rw [hsum, sumFin_single, hyz]
    simp

/-- MSB bit-split XOR lemma: for `u, v < 2^k`,
    `(A * 2^k + u) ^^^ (B * 2^k + v) = (A ^^^ B) * 2^k + (u ^^^ v)`. -/
theorem nat_xor_msb_split (k A B u v : Nat) (hu : u < 2 ^ k) (hv : v < 2 ^ k) :
    (A * 2 ^ k + u) ^^^ (B * 2 ^ k + v) = (A ^^^ B) * 2 ^ k + (u ^^^ v) := by
  have hlt : u ^^^ v < 2 ^ k := Nat.xor_lt_two_pow hu hv
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor]
  have htb : ∀ (Q r : Nat), r < 2 ^ k →
      (Q * 2 ^ k + r).testBit i = if i < k then r.testBit i else Q.testBit (i - k) := by
    intro Q r hr
    rw [Nat.mul_comm Q (2 ^ k), Nat.testBit_two_pow_mul_add _ hr]
  rw [htb A u hu, htb B v hv, htb (A ^^^ B) (u ^^^ v) hlt]
  split
  · rw [Nat.testBit_xor]
  · rw [Nat.testBit_xor]

theorem nat_xor_mod_two_pow (k A B u v : Nat) (hu : u < 2 ^ k) (hv : v < 2 ^ k) :
    ((A * 2 ^ k + u) ^^^ (B * 2 ^ k + v)) % 2 ^ k = u ^^^ v := by
  rw [nat_xor_msb_split k A B u v hu hv]
  have hlt : u ^^^ v < 2 ^ k := Nat.xor_lt_two_pow hu hv
  rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- Key entrywise MSB block formula for `D_{k+1}`:
    for `a, b ∈ {0, 1}` and `x', y' < 2^k`, `D_{k+1}(a·2^k + x', b·2^k + y')` differs from
    `D_k(x', y')` ONLY on the anti-diagonal `x' + y' = 2^k - 1`, by `0, 0, +2^{k+1}, -2^{k+1}`! -/
theorem DMat_msb_entry (k a b x y : Nat) (ha : a < 2) (hb : b < 2)
    (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    ((((a * 2 ^ k + x) + (b * 2 ^ k + y) + 1) ^^^ (a * 2 ^ k + x) : Nat) : Int) -
    ((((a * 2 ^ k + x) + (b * 2 ^ k + y)) ^^^ (a * 2 ^ k + x) : Nat) : Int) =
    (((x + y + 1) ^^^ x : Nat) : Int) - (((x + y) ^^^ x : Nat) : Int) +
    if x + y = 2 ^ k - 1 then
      (if a = 0 then 0 else if b = 0 then (2 ^ (k + 1) : Int) else -(2 ^ (k + 1) : Int))
    else 0 := by
  have hN : 0 < 2 ^ k := pow2_pos k
  have h2k1 : (2 ^ (k + 1) : Int) = 2 * (2 ^ k : Int) := by
    have : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
    exact_mod_cast this
  by_cases hlt : x + y + 1 < 2 ^ k
  · have hne : x + y ≠ 2 ^ k - 1 := by omega
    have hlt0 : x + y < 2 ^ k := by omega
    have h1 : (a * 2 ^ k + x) + (b * 2 ^ k + y) + 1 = (a + b) * 2 ^ k + (x + y + 1) := by
      rw [Nat.add_mul]; omega
    have h0 : (a * 2 ^ k + x) + (b * 2 ^ k + y) = (a + b) * 2 ^ k + (x + y) := by
      rw [Nat.add_mul]; omega
    rw [h1, h0, nat_xor_msb_split k (a + b) a (x + y + 1) x hlt hx,
        nat_xor_msb_split k (a + b) a (x + y) x hlt0 hx]
    simp only [hne, ↓reduceIte, Int.add_zero]; omega
  · by_cases heq : x + y = 2 ^ k - 1
    · have h1 : (a * 2 ^ k + x) + (b * 2 ^ k + y) + 1 = (a + b + 1) * 2 ^ k + 0 := by
        rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]; omega
      have h0 : (a * 2 ^ k + x) + (b * 2 ^ k + y) = (a + b) * 2 ^ k + (2 ^ k - 1) := by
        rw [Nat.add_mul]; omega
      have hrhs1 : x + y + 1 = 1 * 2 ^ k + 0 := by omega
      have hrhs0 : x + y = 0 * 2 ^ k + (2 ^ k - 1) := by omega
      have hm1lt : 2 ^ k - 1 < 2 ^ k := by omega
      rw [h1, h0, nat_xor_msb_split k (a + b + 1) a 0 x hN hx,
          nat_xor_msb_split k (a + b) a (2 ^ k - 1) x hm1lt hx]
      have hbase1 : (x + y + 1) ^^^ x = (1 ^^^ 0) * 2 ^ k + (0 ^^^ x) := by
        rw [hrhs1]
        have hx0 : x = 0 * 2 ^ k + x := by simp
        conv => lhs; rhs; rw [hx0]
        exact nat_xor_msb_split k 1 0 0 x hN hx
      have hbase0 : (x + y) ^^^ x = (0 ^^^ 0) * 2 ^ k + ((2 ^ k - 1) ^^^ x) := by
        rw [hrhs0]
        have hx0 : x = 0 * 2 ^ k + x := by simp
        conv => lhs; rhs; rw [hx0]
        exact nat_xor_msb_split k 0 0 (2 ^ k - 1) x hm1lt hx
      rw [hbase1, hbase0]
      simp only [heq, ↓reduceIte, h2k1]
      have ha_cases : a = 0 ∨ a = 1 := by omega
      have hb_cases : b = 0 ∨ b = 1 := by omega
      rcases ha_cases with rfl | rfl <;> rcases hb_cases with rfl | rfl <;>
        (simp; try omega)
    · have hge : 2 ^ k ≤ x + y := by omega
      have hu0 : x + y - 2 ^ k < 2 ^ k := by omega
      have hu1 : x + y + 1 - 2 ^ k < 2 ^ k := by omega
      have h1 : (a * 2 ^ k + x) + (b * 2 ^ k + y) + 1 = (a + b + 1) * 2 ^ k + (x + y + 1 - 2 ^ k) := by
        rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]; omega
      have h0 : (a * 2 ^ k + x) + (b * 2 ^ k + y) = (a + b + 1) * 2 ^ k + (x + y - 2 ^ k) := by
        rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]; omega
      have hrhs1 : x + y + 1 = 1 * 2 ^ k + (x + y + 1 - 2 ^ k) := by omega
      have hrhs0 : x + y = 1 * 2 ^ k + (x + y - 2 ^ k) := by omega
      rw [h1, h0, nat_xor_msb_split k (a + b + 1) a (x + y + 1 - 2 ^ k) x hu1 hx,
          nat_xor_msb_split k (a + b + 1) a (x + y - 2 ^ k) x hu0 hx]
      have hbase1 : (x + y + 1) ^^^ x = (1 ^^^ 0) * 2 ^ k + ((x + y + 1 - 2 ^ k) ^^^ x) := by
        have hsp := nat_xor_msb_split k 1 0 (x + y + 1 - 2 ^ k) x hu1 hx
        rw [← hrhs1] at hsp; simpa using hsp
      have hbase0 : (x + y) ^^^ x = (1 ^^^ 0) * 2 ^ k + ((x + y - 2 ^ k) ^^^ x) := by
        have hsp := nat_xor_msb_split k 1 0 (x + y - 2 ^ k) x hu0 hx
        rw [← hrhs0] at hsp; simpa using hsp
      rw [hbase1, hbase0]
      simp only [heq, ↓reduceIte, Int.add_zero]
      omega

theorem antiDiagPerm_mat_entry (m : Nat) (x y : Fin m) :
    permMat (antiDiagPerm m) x y = if x.1 + y.1 = m - 1 then 1 else 0 := by
  simp only [permMat, antiDiagPerm]
  have hiff : ((⟨m - 1 - x.1, by omega⟩ : Fin m) = y) ↔ (x.1 + y.1 = m - 1) := by
    constructor
    · intro h; have := congrArg Fin.val h; dsimp at this; omega
    · intro h; apply Fin.ext; dsimp; omega
  by_cases h : x.1 + y.1 = m - 1
  · simp [h, hiff.mpr h]
  · simp [h, mt hiff.mp h]

/-- Exact MSB 2×2 block decomposition of `D_{k+1}`:
    `D_{k+1} = [[D_k, D_k], [D_k + 2^{k+1} P_anti, D_k - 2^{k+1} P_anti]]`. -/
theorem DMat_msb_blocks (k : Nat) :
    castMat (pow2_add_self k).symm (DMat (k + 1)) =
      blockMat (DMat k) (DMat k)
               (matAdd (DMat k) (matSmul ((2 ^ (k + 1) : Nat) : Int) (permMat (antiDiagPerm (2 ^ k)))))
               (matSub (DMat k) (matSmul ((2 ^ (k + 1) : Nat) : Int) (permMat (antiDiagPerm (2 ^ k))))) := by
  apply matExt; intro i j
  simp only [castMat, DMat, blockMat, matAdd, matSub, matSmul]
  split
  · rename_i hi
    split
    · rename_i hj
      rfl
    · rename_i hj
      have hj' : j.1 - 2 ^ k < 2 ^ k := by omega
      have h := DMat_msb_entry k 0 1 i.1 (j.1 - 2 ^ k) (by decide) (by decide) hi hj'
      have hjeq : 1 * 2 ^ k + (j.1 - 2 ^ k) = j.1 := by omega
      rw [Nat.zero_mul, Nat.zero_add, hjeq] at h
      simpa using h
  · rename_i hi
    have hi' : i.1 - 2 ^ k < 2 ^ k := by omega
    split
    · rename_i hj
      rw [antiDiagPerm_mat_entry]
      have h := DMat_msb_entry k 1 0 (i.1 - 2 ^ k) j.1 (by decide) (by decide) hi' hj
      have hieq : 1 * 2 ^ k + (i.1 - 2 ^ k) = i.1 := by omega
      rw [Nat.zero_mul, Nat.zero_add, hieq] at h
      by_cases had : i.1 - 2 ^ k + j.1 = 2 ^ k - 1
      · have hite : (if i.1 - 2 ^ k + j.1 = 2 ^ k - 1 then
            (if (1 : Nat) = 0 then (0 : Int) else if (0 : Nat) = 0 then (2 ^ (k + 1) : Int) else -(2 ^ (k + 1) : Int))
            else 0) = (2 ^ (k + 1) : Int) := by simp [had]
        rw [hite] at h
        have hperm : (if (⟨i.1 - 2 ^ k, hi'⟩ : Fin (2 ^ k)).1 + (⟨j.1, hj⟩ : Fin (2 ^ k)).1 = 2 ^ k - 1 then (1 : Int) else 0) = 1 := by
          simp [had]
        rw [hperm, Int.mul_one]; exact_mod_cast h
      · have hite : (if i.1 - 2 ^ k + j.1 = 2 ^ k - 1 then
            (if (1 : Nat) = 0 then (0 : Int) else if (0 : Nat) = 0 then (2 ^ (k + 1) : Int) else -(2 ^ (k + 1) : Int))
            else 0) = 0 := by simp [had]
        rw [hite, Int.add_zero] at h
        have hperm : (if (⟨i.1 - 2 ^ k, hi'⟩ : Fin (2 ^ k)).1 + (⟨j.1, hj⟩ : Fin (2 ^ k)).1 = 2 ^ k - 1 then (1 : Int) else 0) = 0 := by
          simp [had]
        rw [hperm, Int.mul_zero, Int.add_zero]; exact h
    · rename_i hj
      rw [antiDiagPerm_mat_entry]
      have hj' : j.1 - 2 ^ k < 2 ^ k := by omega
      have h := DMat_msb_entry k 1 1 (i.1 - 2 ^ k) (j.1 - 2 ^ k) (by decide) (by decide) hi' hj'
      have hieq : 1 * 2 ^ k + (i.1 - 2 ^ k) = i.1 := by omega
      have hjeq : 1 * 2 ^ k + (j.1 - 2 ^ k) = j.1 := by omega
      rw [hieq, hjeq] at h
      by_cases had : i.1 - 2 ^ k + (j.1 - 2 ^ k) = 2 ^ k - 1
      · have hite : (if i.1 - 2 ^ k + (j.1 - 2 ^ k) = 2 ^ k - 1 then
            (if (1 : Nat) = 0 then (0 : Int) else if (1 : Nat) = 0 then (2 ^ (k + 1) : Int) else -(2 ^ (k + 1) : Int))
            else 0) = -(2 ^ (k + 1) : Int) := by simp [had]
        rw [hite] at h
        have hperm : (if (⟨i.1 - 2 ^ k, hi'⟩ : Fin (2 ^ k)).1 + (⟨j.1 - 2 ^ k, hj'⟩ : Fin (2 ^ k)).1 = 2 ^ k - 1 then (1 : Int) else 0) = 1 := by
          simp [had]
        rw [hperm, Int.mul_one, h]
        have hpow : ((2 ^ (k + 1) : Nat) : Int) = (2 ^ (k + 1) : Int) := by simp
        rw [hpow]; omega
      · have hite : (if i.1 - 2 ^ k + (j.1 - 2 ^ k) = 2 ^ k - 1 then
            (if (1 : Nat) = 0 then (0 : Int) else if (1 : Nat) = 0 then (2 ^ (k + 1) : Int) else -(2 ^ (k + 1) : Int))
            else 0) = 0 := by simp [had]
        rw [hite, Int.add_zero] at h
        have hperm : (if (⟨i.1 - 2 ^ k, hi'⟩ : Fin (2 ^ k)).1 + (⟨j.1 - 2 ^ k, hj'⟩ : Fin (2 ^ k)).1 = 2 ^ k - 1 then (1 : Int) else 0) = 0 := by
          simp [had]
        rw [hperm, Int.mul_zero, Int.sub_zero]; exact h

/-- Divisibility property of `addXorSNFDiag`: every entry for `i < 2^k` divides `2^{k+1}`. -/
theorem addXorSNFDiag_dvd_pow2 (k i : Nat) (hi : i < 2 ^ k) :
    addXorSNFDiag i ∣ 2 ^ (k + 1) := by
  simp only [addXorSNFDiag]
  split
  · exact Nat.one_dvd _
  · rename_i hne
    have hlt : Nat.log2 i < k := by
      have h1 : 2 ^ Nat.log2 i ≤ i := Nat.log2_self_le hne
      have h2 : 2 ^ Nat.log2 i < 2 ^ k := Nat.lt_of_le_of_lt h1 hi
      exact Classical.byContradiction fun hge => by
        have hge' : k ≤ Nat.log2 i := by omega
        have h3 : 2 ^ k ≤ 2 ^ Nat.log2 i := Nat.pow_le_pow_right (by decide) hge'
        omega
    exact Nat.pow_dvd_pow 2 (by omega)

theorem addXorSNFDiag_dvd_succ (i : Nat) : addXorSNFDiag i ∣ addXorSNFDiag (i + 1) := by
  simp only [addXorSNFDiag]
  by_cases hi : i = 0
  · subst hi; simp
  · have hi1 : i + 1 ≠ 0 := by omega
    simp only [hi, hi1, ↓reduceIte]
    have hle : Nat.log2 i ≤ Nat.log2 (i + 1) := by
      have h1 : 2 ^ Nat.log2 i ≤ i := Nat.log2_self_le hi
      have h2 : 2 ^ Nat.log2 i ≤ i + 1 := by omega
      exact (Nat.le_log2 hi1).mpr h2
    exact Nat.pow_dvd_pow 2 (by omega)

theorem addXorSNFDiag_upper_half (k i : Nat) (hlo : 2 ^ k ≤ i) (hhi : i < 2 ^ (k + 1)) :
    addXorSNFDiag i = 2 ^ (k + 2) := by
  have hne : i ≠ 0 := by have := pow2_pos k; omega
  simp only [addXorSNFDiag, hne, ↓reduceIte]
  have hge : k ≤ Nat.log2 i := (Nat.le_log2 hne).mpr hlo
  have hlt : Nat.log2 i < k + 1 := by
    have h1 : 2 ^ Nat.log2 i ≤ i := Nat.log2_self_le hne
    exact Classical.byContradiction fun hcontra => by
      have hle : k + 1 ≤ Nat.log2 i := by omega
      have h2 : 2 ^ (k + 1) ≤ 2 ^ Nat.log2 i := Nat.pow_le_pow_right (by decide) hle
      omega
  have heq : Nat.log2 i = k := by omega
  rw [heq]

/-- **THEOREM 2a (Exact Stabilizing SNF of Add-XOR Carry-Difference `D_k`)**:
    For EVERY `k ≥ 0`, `D_k(x, y) = ((x + y + 1) ^^^ x) - ((x + y) ^^^ x)` has exact canonical
    SNF diagonal `d(0) = 1`, `d(i) = 2^{⌊log2 i⌋ + 2}` for `1 ≤ i < 2^k`
    (i.e. `1, 4, 8^2, 16^4, ..., (2^{k+1})^{2^{k-1}}`). Proved via MSB Divisibility Block-Schur Lifting! -/
theorem snf_DMat (k : Nat) : HasSNF (DMat k) (fun i : Fin (2 ^ k) => addXorSNFDiag i.1) := by
  constructor
  · induction k with
    | zero =>
      have heq : DMat 0 = diagMatNat (fun i : Fin (2 ^ 0) => addXorSNFDiag i.1) := by
        apply matExt; intro i j
        have hi : i = ⟨0, by decide⟩ := Fin.ext (by omega)
        have hj : j = ⟨0, by decide⟩ := Fin.ext (by omega)
        subst hi; subst hj; simp [DMat, diagMatNat, addXorSNFDiag]
      rw [heq]; exact UnimodEquiv.refl _
    | succ k ih =>
      -- Step 1: MSB block decomposition + block_sub_lower -> [[D_k, 0], [2^{k+1} P_anti, -2^{k+2} P_anti]]
      have h1 : UnimodEquiv (castMat (pow2_add_self k).symm (DMat (k + 1)))
          (blockMat (DMat k) (matZero (2 ^ k))
            (matSmul ((2 ^ (k + 1) : Nat) : Int) (permMat (antiDiagPerm (2 ^ k))))
            (matSmul (-((2 ^ (k + 2) : Nat) : Int)) (permMat (antiDiagPerm (2 ^ k))))) := by
        rw [DMat_msb_blocks k]
        have hsub := unimodEquiv_block_sub_lower (DMat k) (DMat k)
          (matAdd (DMat k) (matSmul ((2 ^ (k + 1) : Nat) : Int) (permMat (antiDiagPerm (2 ^ k)))))
          (matSub (DMat k) (matSmul ((2 ^ (k + 1) : Nat) : Int) (permMat (antiDiagPerm (2 ^ k)))))
        have h01 : matSub (DMat k) (DMat k) = matZero (2 ^ k) := by
          apply matExt; intro i j; simp [matSub, matZero]
        have h10 : matSub (matAdd (DMat k) (matSmul ((2 ^ (k + 1) : Nat) : Int) (permMat (antiDiagPerm (2 ^ k)))))
                          (DMat k) =
                   matSmul ((2 ^ (k + 1) : Nat) : Int) (permMat (antiDiagPerm (2 ^ k))) := by
          apply matExt; intro i j; simp only [matSub, matAdd]; omega
        have h11 : matSub (matSub (matSub (DMat k) (matSmul ((2 ^ (k + 1) : Nat) : Int) (permMat (antiDiagPerm (2 ^ k)))))
                                  (DMat k))
                          (matSub (matAdd (DMat k) (matSmul ((2 ^ (k + 1) : Nat) : Int) (permMat (antiDiagPerm (2 ^ k)))))
                                  (DMat k)) =
                   matSmul (-((2 ^ (k + 2) : Nat) : Int)) (permMat (antiDiagPerm (2 ^ k))) := by
          apply matExt; intro i j
          simp only [matSub, matAdd, matSmul]
          have hpow2 : ((2 ^ (k + 2) : Nat) : Int) = 2 * ((2 ^ (k + 1) : Nat) : Int) := by
            have : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
            exact_mod_cast this
          rw [hpow2, Int.neg_mul, Int.mul_assoc]
          omega
        rw [h11, h01, h10] at hsub
        exact hsub
      -- Step 2: Apply Exact Integer Divisibility Block-Schur Lifter (`L = 2^{k+1}`)!
      have h2 := unimodEquiv_blockSchur_lower
        (C' := permMat (antiDiagPerm (2 ^ k)))
        (E := matSmul (-((2 ^ (k + 2) : Nat) : Int)) (permMat (antiDiagPerm (2 ^ k))))
        (L := 2 ^ (k + 1)) ih
        (fun j => addXorSNFDiag_dvd_pow2 k j.1 j.isLt)
      -- Step 3: Reduce bottom-right `-2^{k+2} P_anti` to `diag(2^{k+2})`
      have hbr : UnimodEquiv (matSmul (-((2 ^ (k + 2) : Nat) : Int)) (permMat (antiDiagPerm (2 ^ k))))
                             (diagMatNat (fun _ : Fin (2 ^ k) => 2 ^ (k + 2))) := by
        have hp : UnimodEquiv (permMat (antiDiagPerm (2 ^ k))) (matId (2 ^ k)) :=
          UnimodEquiv.of_unimod (permUnimod (antiDiagPerm (2 ^ k)))
        have hs := (hp.smul_both (-((2 ^ (k + 2) : Nat) : Int))).neg_right
        have heq : matNeg (matSmul (-((2 ^ (k + 2) : Nat) : Int)) (matId (2 ^ k))) =
                   diagMatNat (fun _ : Fin (2 ^ k) => 2 ^ (k + 2)) := by
          apply matExt; intro i j
          simp only [matNeg, matSmul, matId, diagMatNat]
          by_cases hij : i = j
          · subst hij; simp
          · simp [hij]
        rw [heq] at hs; exact hs
      have h3 := unimodEquiv_blockDiag ih hbr
      rw [blockDiag_diagMatNat] at h3
      have hcomb := (h1.trans h2).trans h3
      have hcast := unimodEquiv_cast (pow2_add_self k) hcomb
      have hEq1 : castMat (pow2_add_self k) (castMat (pow2_add_self k).symm (DMat (k + 1))) = DMat (k + 1) := by
        apply matExt; intro i j; rfl
      have hEq2 : castMat (pow2_add_self k) (diagMatNat (fun i : Fin (2 ^ k + 2 ^ k) =>
          if h : i.1 < 2 ^ k then addXorSNFDiag i.1 else 2 ^ (k + 2))) =
          diagMatNat (fun i : Fin (2 ^ (k + 1)) => addXorSNFDiag i.1) := by
        apply matExt; intro i j
        simp only [castMat, diagMatNat]
        by_cases hij : i = j
        · subst hij
          simp only [↓reduceIte]
          by_cases hi : i.1 < 2 ^ k
          · simp [hi]
          · simp only [hi, ↓reduceDIte]
            exact congrArg Int.ofNat (addXorSNFDiag_upper_half k i.1 (by omega) i.isLt).symm
        · have hval : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
          simp [hij, fin_mk_ne hval]
      rw [hEq1, hEq2] at hcast
      exact hcast
  · intro i _; exact addXorSNFDiag_dvd_succ i.1

/-- **THEOREM 2b (Exact Stabilizing SNF of Add-XOR Matrix `T_k^(1)(x, y) = (x + y + 1) ^^^ x`)**:
    For EVERY `k ≥ 0`, `T_k^(1)` has the exact same stabilizing canonical SNF as `D_k`! -/
theorem snf_T1Mat (k : Nat) : HasSNF (T1Mat k) (fun i : Fin (2 ^ k) => addXorSNFDiag i.1) := by
  have hTD : UnimodEquiv (T1Mat k) (DMat k) :=
    ⟨Unimod.id (2 ^ k), deltaUnimod (2 ^ k), by simp only [Unimod.id, matId_mul]; exact T1Mat_mul_delta k⟩
  exact ⟨hTD.trans (snf_DMat k).1, (snf_DMat k).2⟩

/-- Entrywise MSB block identity for truncated `D_{k+1, mod}` (dropping bit `k+1`):
    both top and bottom halves are identical, with right block equal to `D_k - 2^{k+1} P_anti`. -/
theorem DModMat_msb_entry (k a b x y : Nat) (ha : a < 2) (hb : b < 2)
    (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    (((((a * 2 ^ k + x) + (b * 2 ^ k + y) + 1) ^^^ (a * 2 ^ k + x)) % 2 ^ (k + 1) : Nat) : Int) -
    (((((a * 2 ^ k + x) + (b * 2 ^ k + y)) ^^^ (a * 2 ^ k + x)) % 2 ^ (k + 1) : Nat) : Int) =
    (((x + y + 1) ^^^ x : Nat) : Int) - (((x + y) ^^^ x : Nat) : Int) -
    if x + y = 2 ^ k - 1 then (if b = 0 then 0 else (2 ^ (k + 1) : Int)) else 0 := by
  have hN : 0 < 2 ^ k := pow2_pos k
  have h2k1_nat : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
  have h2k1 : (2 ^ (k + 1) : Int) = 2 * (2 ^ k : Int) := by exact_mod_cast h2k1_nat
  have hmod_split : ∀ (Q r : Nat), r < 2 ^ k →
      (Q * 2 ^ k + r) % 2 ^ (k + 1) = (Q % 2) * 2 ^ k + r := by
    intro Q r hr
    rw [h2k1_nat]
    have hq : Q = 2 * (Q / 2) + Q % 2 := (Nat.div_add_mod Q 2).symm
    have hlt : (Q % 2) * 2 ^ k + r < 2 * 2 ^ k := by
      have : Q % 2 ≤ 1 := by omega
      have hmul : (Q % 2) * 2 ^ k ≤ 1 * 2 ^ k := Nat.mul_le_mul_right _ this
      omega
    have hrew : Q * 2 ^ k + r = ((Q % 2) * 2 ^ k + r) + (2 * 2 ^ k) * (Q / 2) := by
      conv => lhs; rw [hq]
      rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (Q / 2) (2 ^ k), ← Nat.mul_assoc]
      omega
    rw [hrew, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  by_cases hlt : x + y + 1 < 2 ^ k
  · have hne : x + y ≠ 2 ^ k - 1 := by omega
    have hlt0 : x + y < 2 ^ k := by omega
    have h1 : (a * 2 ^ k + x) + (b * 2 ^ k + y) + 1 = (a + b) * 2 ^ k + (x + y + 1) := by
      rw [Nat.add_mul]; omega
    have h0 : (a * 2 ^ k + x) + (b * 2 ^ k + y) = (a + b) * 2 ^ k + (x + y) := by
      rw [Nat.add_mul]; omega
    rw [h1, h0, nat_xor_msb_split k (a + b) a (x + y + 1) x hlt hx,
        nat_xor_msb_split k (a + b) a (x + y) x hlt0 hx,
        hmod_split _ _ (Nat.xor_lt_two_pow hlt hx),
        hmod_split _ _ (Nat.xor_lt_two_pow hlt0 hx)]
    simp only [hne, ↓reduceIte, Int.sub_zero]; omega
  · by_cases heq : x + y = 2 ^ k - 1
    · have h1 : (a * 2 ^ k + x) + (b * 2 ^ k + y) + 1 = (a + b + 1) * 2 ^ k + 0 := by
        rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]; omega
      have h0 : (a * 2 ^ k + x) + (b * 2 ^ k + y) = (a + b) * 2 ^ k + (2 ^ k - 1) := by
        rw [Nat.add_mul]; omega
      have hrhs1 : x + y + 1 = 1 * 2 ^ k + 0 := by omega
      have hrhs0 : x + y = 0 * 2 ^ k + (2 ^ k - 1) := by omega
      have hm1lt : 2 ^ k - 1 < 2 ^ k := by omega
      rw [h1, h0, nat_xor_msb_split k (a + b + 1) a 0 x hN hx,
          nat_xor_msb_split k (a + b) a (2 ^ k - 1) x hm1lt hx,
          hmod_split _ _ (Nat.xor_lt_two_pow hN hx),
          hmod_split _ _ (Nat.xor_lt_two_pow hm1lt hx)]
      have hbase1 : (x + y + 1) ^^^ x = (1 ^^^ 0) * 2 ^ k + (0 ^^^ x) := by
        rw [hrhs1]
        have hx0 : x = 0 * 2 ^ k + x := by simp
        conv => lhs; rhs; rw [hx0]
        exact nat_xor_msb_split k 1 0 0 x hN hx
      have hbase0 : (x + y) ^^^ x = (0 ^^^ 0) * 2 ^ k + ((2 ^ k - 1) ^^^ x) := by
        rw [hrhs0]
        have hx0 : x = 0 * 2 ^ k + x := by simp
        conv => lhs; rhs; rw [hx0]
        exact nat_xor_msb_split k 0 0 (2 ^ k - 1) x hm1lt hx
      rw [hbase1, hbase0]
      simp only [heq, ↓reduceIte, h2k1]
      have ha_cases : a = 0 ∨ a = 1 := by omega
      have hb_cases : b = 0 ∨ b = 1 := by omega
      rcases ha_cases with rfl | rfl <;> rcases hb_cases with rfl | rfl <;>
        (simp; try omega)
    · have hge : 2 ^ k ≤ x + y := by omega
      have hu0 : x + y - 2 ^ k < 2 ^ k := by omega
      have hu1 : x + y + 1 - 2 ^ k < 2 ^ k := by omega
      have h1 : (a * 2 ^ k + x) + (b * 2 ^ k + y) + 1 = (a + b + 1) * 2 ^ k + (x + y + 1 - 2 ^ k) := by
        rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]; omega
      have h0 : (a * 2 ^ k + x) + (b * 2 ^ k + y) = (a + b + 1) * 2 ^ k + (x + y - 2 ^ k) := by
        rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]; omega
      have hrhs1 : x + y + 1 = 1 * 2 ^ k + (x + y + 1 - 2 ^ k) := by omega
      have hrhs0 : x + y = 1 * 2 ^ k + (x + y - 2 ^ k) := by omega
      rw [h1, h0, nat_xor_msb_split k (a + b + 1) a (x + y + 1 - 2 ^ k) x hu1 hx,
          nat_xor_msb_split k (a + b + 1) a (x + y - 2 ^ k) x hu0 hx,
          hmod_split _ _ (Nat.xor_lt_two_pow hu1 hx),
          hmod_split _ _ (Nat.xor_lt_two_pow hu0 hx)]
      have hbase1 : (x + y + 1) ^^^ x = (1 ^^^ 0) * 2 ^ k + ((x + y + 1 - 2 ^ k) ^^^ x) := by
        have hsp := nat_xor_msb_split k 1 0 (x + y + 1 - 2 ^ k) x hu1 hx
        rw [← hrhs1] at hsp; simpa using hsp
      have hbase0 : (x + y) ^^^ x = (1 ^^^ 0) * 2 ^ k + ((x + y - 2 ^ k) ^^^ x) := by
        have hsp := nat_xor_msb_split k 1 0 (x + y - 2 ^ k) x hu0 hx
        rw [← hrhs0] at hsp; simpa using hsp
      rw [hbase1, hbase0]
      simp only [heq, ↓reduceIte, Int.sub_zero]; omega

/-- **THEOREM 2c (Exact Half-Rank Truncation Collapse of `D_{k+1, mod}` and `T_{k+1, mod}^(1)`)**:
    Dropping ONLY the single top carry-out bit `k + 1` collapses the entire upper half of the SNF
    from `(2^{k+2})^{2^k}` to `0^{2^k}`, leaving exact canonical SNF
    `[addXorSNFDiag(0), ..., addXorSNFDiag(2^k - 1), 0, ..., 0]`! -/
theorem snf_DModMat_collapse (k : Nat) :
    HasSNF (DModMat (k + 1))
      (fun i : Fin (2 ^ (k + 1)) => if i.1 < 2 ^ k then addXorSNFDiag i.1 else 0) := by
  constructor
  · have hblocks : castMat (pow2_add_self k).symm (DModMat (k + 1)) =
        blockMat (DMat k)
                 (matSub (DMat k) (matSmul ((2 ^ (k + 1) : Nat) : Int) (permMat (antiDiagPerm (2 ^ k)))))
                 (DMat k)
                 (matSub (DMat k) (matSmul ((2 ^ (k + 1) : Nat) : Int) (permMat (antiDiagPerm (2 ^ k))))) := by
      apply matExt; intro i j
      simp only [castMat, DModMat, DMat, blockMat, matSub, matSmul]
      split
      · rename_i hi
        split
        · rename_i hj
          have h := DModMat_msb_entry k 0 0 i.1 j.1 (by decide) (by decide) hi hj
          simpa using h
        · rename_i hj
          rw [antiDiagPerm_mat_entry]
          have hj' : j.1 - 2 ^ k < 2 ^ k := by omega
          have h := DModMat_msb_entry k 0 1 i.1 (j.1 - 2 ^ k) (by decide) (by decide) hi hj'
          have hjeq : 1 * 2 ^ k + (j.1 - 2 ^ k) = j.1 := by omega
          rw [Nat.zero_mul, Nat.zero_add, hjeq] at h
          by_cases had : i.1 + (j.1 - 2 ^ k) = 2 ^ k - 1
          · have hite : (if i.1 + (j.1 - 2 ^ k) = 2 ^ k - 1 then
                (if (1 : Nat) = 0 then (0 : Int) else (2 ^ (k + 1) : Int)) else 0) = (2 ^ (k + 1) : Int) := by
              simp [had]
            rw [hite] at h
            have hperm : (if (⟨i.1, hi⟩ : Fin (2 ^ k)).1 + (⟨j.1 - 2 ^ k, hj'⟩ : Fin (2 ^ k)).1 = 2 ^ k - 1 then (1 : Int) else 0) = 1 := by
              simp [had]
            rw [hperm, Int.mul_one]; exact_mod_cast h
          · have hite : (if i.1 + (j.1 - 2 ^ k) = 2 ^ k - 1 then
                (if (1 : Nat) = 0 then (0 : Int) else (2 ^ (k + 1) : Int)) else 0) = 0 := by simp [had]
            rw [hite, Int.sub_zero] at h
            have hperm : (if (⟨i.1, hi⟩ : Fin (2 ^ k)).1 + (⟨j.1 - 2 ^ k, hj'⟩ : Fin (2 ^ k)).1 = 2 ^ k - 1 then (1 : Int) else 0) = 0 := by
              simp [had]
            rw [hperm, Int.mul_zero, Int.sub_zero]; exact h
      · rename_i hi
        have hi' : i.1 - 2 ^ k < 2 ^ k := by omega
        split
        · rename_i hj
          have h := DModMat_msb_entry k 1 0 (i.1 - 2 ^ k) j.1 (by decide) (by decide) hi' hj
          have hieq : 1 * 2 ^ k + (i.1 - 2 ^ k) = i.1 := by omega
          rw [Nat.zero_mul, Nat.zero_add, hieq] at h
          simpa using h
        · rename_i hj
          rw [antiDiagPerm_mat_entry]
          have hj' : j.1 - 2 ^ k < 2 ^ k := by omega
          have h := DModMat_msb_entry k 1 1 (i.1 - 2 ^ k) (j.1 - 2 ^ k) (by decide) (by decide) hi' hj'
          have hieq : 1 * 2 ^ k + (i.1 - 2 ^ k) = i.1 := by omega
          have hjeq : 1 * 2 ^ k + (j.1 - 2 ^ k) = j.1 := by omega
          rw [hieq, hjeq] at h
          by_cases had : i.1 - 2 ^ k + (j.1 - 2 ^ k) = 2 ^ k - 1
          · have hite : (if i.1 - 2 ^ k + (j.1 - 2 ^ k) = 2 ^ k - 1 then
                (if (1 : Nat) = 0 then (0 : Int) else (2 ^ (k + 1) : Int)) else 0) = (2 ^ (k + 1) : Int) := by
              simp [had]
            rw [hite] at h
            have hperm : (if (⟨i.1 - 2 ^ k, hi'⟩ : Fin (2 ^ k)).1 + (⟨j.1 - 2 ^ k, hj'⟩ : Fin (2 ^ k)).1 = 2 ^ k - 1 then (1 : Int) else 0) = 1 := by
              simp [had]
            rw [hperm, Int.mul_one]; exact_mod_cast h
          · have hite : (if i.1 - 2 ^ k + (j.1 - 2 ^ k) = 2 ^ k - 1 then
                (if (1 : Nat) = 0 then (0 : Int) else (2 ^ (k + 1) : Int)) else 0) = 0 := by simp [had]
            rw [hite, Int.sub_zero] at h
            have hperm : (if (⟨i.1 - 2 ^ k, hi'⟩ : Fin (2 ^ k)).1 + (⟨j.1 - 2 ^ k, hj'⟩ : Fin (2 ^ k)).1 = 2 ^ k - 1 then (1 : Int) else 0) = 0 := by
              simp [had]
            rw [hperm, Int.mul_zero, Int.sub_zero]; exact h
    have h1 : UnimodEquiv (castMat (pow2_add_self k).symm (DModMat (k + 1)))
        (blockMat (DMat k)
          (matSmul ((2 ^ (k + 1) : Nat) : Int) (matNeg (permMat (antiDiagPerm (2 ^ k)))))
          (matZero (2 ^ k)) (matZero (2 ^ k))) := by
      rw [hblocks]
      have hsub := unimodEquiv_block_sub_lower (DMat k)
        (matSub (DMat k) (matSmul ((2 ^ (k + 1) : Nat) : Int) (permMat (antiDiagPerm (2 ^ k)))))
        (DMat k)
        (matSub (DMat k) (matSmul ((2 ^ (k + 1) : Nat) : Int) (permMat (antiDiagPerm (2 ^ k)))))
      have h01 : matSub (matSub (DMat k) (matSmul ((2 ^ (k + 1) : Nat) : Int) (permMat (antiDiagPerm (2 ^ k)))))
                        (DMat k) =
                 matSmul ((2 ^ (k + 1) : Nat) : Int) (matNeg (permMat (antiDiagPerm (2 ^ k)))) := by
        apply matExt; intro i j; simp only [matSub, matSmul, matNeg, Int.mul_neg]; omega
      have h10 : matSub (DMat k) (DMat k) = matZero (2 ^ k) := by
        apply matExt; intro i j; simp [matSub, matZero]
      have h11 : matSub (matSub (matSub (DMat k) (matSmul ((2 ^ (k + 1) : Nat) : Int) (permMat (antiDiagPerm (2 ^ k)))))
                                (matSub (DMat k) (matSmul ((2 ^ (k + 1) : Nat) : Int) (permMat (antiDiagPerm (2 ^ k))))))
                        (matSub (DMat k) (DMat k)) = matZero (2 ^ k) := by
        apply matExt; intro i j; simp [matSub, matZero]
      rw [h11, h01, h10] at hsub; exact hsub
    -- Apply Upper Exact Integer Divisibility Block-Schur Lifter (`L = 2^{k+1}`)!
    have h2 := unimodEquiv_blockSchur_upper
      (B' := matNeg (permMat (antiDiagPerm (2 ^ k))))
      (E := matZero (2 ^ k))
      (L := 2 ^ (k + 1)) (snf_DMat k).1
      (fun i => addXorSNFDiag_dvd_pow2 k i.1 i.isLt)
    have hzero_diag : matZero (2 ^ k) = diagMatNat (fun _ : Fin (2 ^ k) => 0) := by
      apply matExt; intro i j; simp [matZero, diagMatNat]
    have h3 : UnimodEquiv (blockMat (DMat k) (matZero (2 ^ k)) (matZero (2 ^ k)) (matZero (2 ^ k)))
        (blockMat (diagMatNat (fun i : Fin (2 ^ k) => addXorSNFDiag i.1))
                  (matZero (2 ^ k)) (matZero (2 ^ k))
                  (diagMatNat (fun _ : Fin (2 ^ k) => 0))) := by
      rw [← hzero_diag]
      exact unimodEquiv_blockDiag (snf_DMat k).1 (UnimodEquiv.refl _)
    rw [blockDiag_diagMatNat] at h3
    have hcast := unimodEquiv_cast (pow2_add_self k) ((h1.trans h2).trans h3)
    have hEq1 : castMat (pow2_add_self k) (castMat (pow2_add_self k).symm (DModMat (k + 1))) = DModMat (k + 1) := by
      apply matExt; intro i j; rfl
    have hEq2 : castMat (pow2_add_self k) (diagMatNat (fun i : Fin (2 ^ k + 2 ^ k) =>
        if h : i.1 < 2 ^ k then addXorSNFDiag i.1 else 0)) =
        diagMatNat (fun i : Fin (2 ^ (k + 1)) => if i.1 < 2 ^ k then addXorSNFDiag i.1 else 0) := by
      apply matExt; intro i j
      simp only [castMat, diagMatNat]
      by_cases hij : i = j
      · subst hij; simp
      · have hval : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
        simp [hij, fin_mk_ne hval]
    rw [hEq1, hEq2] at hcast; exact hcast
  · intro i hi
    by_cases h1 : i.1 + 1 < 2 ^ k
    · have h0 : i.1 < 2 ^ k := by omega
      simp only [h0, h1, ↓reduceIte]; exact addXorSNFDiag_dvd_succ i.1
    · simp only [h1, ↓reduceIte]; exact Nat.dvd_zero _

theorem snf_T1ModMat_collapse (k : Nat) :
    HasSNF (T1ModMat (k + 1))
      (fun i : Fin (2 ^ (k + 1)) => if i.1 < 2 ^ k then addXorSNFDiag i.1 else 0) := by
  have hTD : UnimodEquiv (T1ModMat (k + 1)) (DModMat (k + 1)) :=
    ⟨Unimod.id (2 ^ (k + 1)), deltaUnimod (2 ^ (k + 1)),
     by simp only [Unimod.id, matId_mul]; exact T1ModMat_mul_delta (k + 1)⟩
  exact ⟨hTD.trans (snf_DModMat_collapse k).1, (snf_DModMat_collapse k).2⟩

-- ============================================================================
-- THEOREM 3: DIVISIBILITY-WEIGHTED BITWISE-AND ADDITIVE SNF FAMILY (∀ k ≥ 1)
-- (Unifying `popcount(x & y)` and `x & y` via Additive Rank-1 Bit-Slice Lifting)
-- ============================================================================

/-- MSB bit-split AND lemma: for `u, v < 2^k`,
    `(A * 2^k + u) &&& (B * 2^k + v) = (A &&& B) * 2^k + (u &&& v)`. -/
theorem nat_and_msb_split (k A B u v : Nat) (hu : u < 2 ^ k) (hv : v < 2 ^ k) :
    (A * 2 ^ k + u) &&& (B * 2 ^ k + v) = (A &&& B) * 2 ^ k + (u &&& v) := by
  have hlt : u &&& v < 2 ^ k := Nat.and_lt_two_pow u hv
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and]
  have htb : ∀ (Q r : Nat), r < 2 ^ k →
      (Q * 2 ^ k + r).testBit i = if i < k then r.testBit i else Q.testBit (i - k) := by
    intro Q r hr
    rw [Nat.mul_comm Q (2 ^ k), Nat.testBit_two_pow_mul_add _ hr]
  rw [htb A u hu, htb B v hv, htb (A &&& B) (u &&& v) hlt]
  split
  · rw [Nat.testBit_and]
  · rw [Nat.testBit_and]

theorem popcount_msb_split (k : Nat) :
    ∀ (Q r : Nat), r < 2 ^ k → popcount (Q * 2 ^ k + r) = popcount Q + popcount r := by
  induction k with
  | zero =>
    intro Q r hr
    have hr0 : r = 0 := by simp at hr; omega
    subst hr0; simp [popcount_zero]
  | succ k ih =>
    intro Q r hr
    have hr' : r / 2 < 2 ^ k := by rw [Nat.pow_succ] at hr; omega
    have hpow : Q * 2 ^ (k + 1) + r = 2 * (Q * 2 ^ k + r / 2) + r % 2 := by
      have h1 : Q * 2 ^ (k + 1) = 2 * (Q * 2 ^ k) := by
        rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (Q * 2 ^ k) 2]
      rw [h1]; omega
    rw [hpow, popcount_two_mul_add _ _ (by omega), ih Q (r / 2) hr', popcount_step r]
    omega

theorem lt_two_pow (k : Nat) : k < 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih => rw [Nat.pow_succ]; omega

/-- **THEOREM 3 (Exact Canonical SNF of Divisibility-Weighted Bitwise-AND Matrix)**:
    For ANY weight sequence `w : Nat → Nat` forming a divisibility chain
    `∀ r, r + 1 < k → w r ∣ w (r + 1)`, `weightedAndMat k w` has exact canonical SNF
    `(w 0, w 1, ..., w (k - 1), 0, ..., 0)` for ALL `k ≥ 0`! -/
theorem snf_weightedAndMat (k : Nat) (w : Nat → Nat)
    (hdvd : ∀ r, r + 1 < k → w r ∣ w (r + 1)) :
    HasSNF (weightedAndMat k w) (fun i : Fin (2 ^ k) => if i.1 < k then w i.1 else 0) := by
  constructor
  · induction k with
    | zero =>
      have heq : weightedAndMat 0 w = diagMatNat (fun i : Fin (2 ^ 0) => if i.1 < 0 then w i.1 else 0) := by
        apply matExt; intro i j; simp [weightedAndMat, matZero, diagMatNat]
      rw [heq]; exact UnimodEquiv.refl _
    | succ k ih =>
      have ih' := ih (fun r hr => hdvd r (by omega))
      -- Block corner elimination: [[M, M], [M, M + w_k J]] ~ [[M, 0], [0, w_k J]]
      have hcor := unimodEquiv_block_corner_lower (weightedAndMat k w)
        (matAdd (weightedAndMat k w) (matSmul (w k : Int) (onesMat (2 ^ k))))
      have hdiff : matSub (matAdd (weightedAndMat k w) (matSmul (w k : Int) (onesMat (2 ^ k))))
                          (weightedAndMat k w) =
                   matSmul (w k : Int) (onesMat (2 ^ k)) := by
        apply matExt; intro i j; simp only [matSub, matAdd]; omega
      rw [hdiff] at hcor
      -- Reduce w_k J ~ diag(w_k, 0, ..., 0)
      have hJ : UnimodEquiv (matSmul (w k : Int) (onesMat (2 ^ k)))
                            (diagMatNat (fun i : Fin (2 ^ k) => if i.1 = 0 then w k else 0)) := by
        have h1 := (unimodEquiv_onesMat (2 ^ k)).smul_both (w k : Int)
        have heq : matSmul (w k : Int) (diagMatNat (fun i : Fin (2 ^ k) => if i.1 = 0 then 1 else 0)) =
                   diagMatNat (fun i : Fin (2 ^ k) => if i.1 = 0 then w k else 0) := by
          apply matExt; intro i j
          simp only [matSmul, diagMatNat]
          by_cases hij : i = j
          · subst hij; by_cases hi0 : i.1 = 0 <;> simp [hi0]
          · simp [hij]
        rw [heq] at h1; exact h1
      have hdiag := hcor.trans (unimodEquiv_blockDiag ih' hJ)
      rw [blockDiag_diagMatNat] at hdiag
      -- Swap index `k` (currently 0, since `k < 2^k`) with index `2^k` (currently `w k`)!
      have hk_lt : k < 2 ^ k := lt_two_pow k
      let p : Fin (2 ^ k + 2 ^ k) := ⟨k, by omega⟩
      let q : Fin (2 ^ k + 2 ^ k) := ⟨2 ^ k, by have := pow2_pos k; omega⟩
      have hperm := UnimodEquiv.diag_perm
        (fun i : Fin (2 ^ k + 2 ^ k) =>
          if h : i.1 < 2 ^ k then (if i.1 < k then w i.1 else 0)
          else (if i.1 - 2 ^ k = 0 then w k else 0))
        (Perm.swap p q)
      have hcomb := hdiag.trans hperm
      have hcast := unimodEquiv_cast (pow2_add_self k) hcomb
      have hEq2 : castMat (pow2_add_self k) (diagMatNat (fun i : Fin (2 ^ k + 2 ^ k) =>
          let j := (Perm.swap p q).toFun i
          if h : j.1 < 2 ^ k then (if j.1 < k then w j.1 else 0)
          else (if j.1 - 2 ^ k = 0 then w k else 0))) =
          diagMatNat (fun i : Fin (2 ^ (k + 1)) => if i.1 < k + 1 then w i.1 else 0) := by
        apply matExt; intro i j
        simp only [castMat, diagMatNat]
        by_cases hij : i = j
        · subst hij
          simp only [↓reduceIte, Perm.swap]
          have hilt_cast : i.1 < 2 ^ k + 2 ^ k := by have := pow2_add_self k; omega
          let ii : Fin (2 ^ k + 2 ^ k) := ⟨i.1, hilt_cast⟩
          by_cases hik : i.1 < k
          · have hnep : ii ≠ p := fun h => by have := Fin.mk.inj h; omega
            have hneq : ii ≠ q := fun h => by have := Fin.mk.inj h; omega
            have hilt : i.1 < 2 ^ k := by omega
            have hik1 : i.1 < k + 1 := by omega
            simp [ii, p, q, hnep, hneq, hilt, hik, hik1]
          · by_cases heqk : i.1 = k
            · have hqlt : ¬(2 ^ k < 2 ^ k) := Nat.lt_irrefl _
              simp [p, q, hqlt, heqk]
            · by_cases heq2k : i.1 = 2 ^ k
              · have hk_ne : 2 ^ k ≠ k := by omega
                have hnotlt : ¬(2 ^ k < k + 1) := by omega
                simp [p, q, hk_lt, hk_ne, heq2k, hnotlt]
              · have hnep : ii ≠ p := fun h => by have := Fin.mk.inj h; omega
                have hneq : ii ≠ q := fun h => by have := Fin.mk.inj h; omega
                have hik1 : ¬(i.1 < k + 1) := by omega
                by_cases hilt : i.1 < 2 ^ k
                · simp [ii, p, q, hnep, hneq, hilt, hik, hik1]
                · have hsub : i.1 - 2 ^ k ≠ 0 := by omega
                  simp [ii, p, q, hnep, hneq, hilt, hsub, hik1]
        · have hval : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
          simp [hij, fin_mk_ne hval]
      rw [hEq2] at hcast
      exact hcast
  · intro i hi
    by_cases h1 : i.1 + 1 < k
    · have h0 : i.1 < k := by omega
      simp only [h0, h1, ↓reduceIte]; exact hdvd i.1 h1
    · simp only [h1, ↓reduceIte]; exact Nat.dvd_zero _

/-- Concrete identification: `weightedAndMat k (fun _ => 1)` IS `popcount(x &&& y)`. -/
theorem weightedAndMat_one_eq_popcount_and (k : Nat) :
    weightedAndMat k (fun _ => 1) = fun x y : Fin (2 ^ k) => (popcount (x.1 &&& y.1) : Int) := by
  induction k with
  | zero =>
    apply matExt; intro i j
    simp [weightedAndMat, matZero, popcount_zero]
  | succ k ih =>
    apply matExt; intro i j
    simp only [weightedAndMat, castMat, blockMat, matAdd, matSmul, onesMat, ih]
    split
    · rename_i hi
      split
      · rename_i hj; rfl
      · rename_i hj
        have hj' : j.1 - 2 ^ k < 2 ^ k := by omega
        have hjeq : j.1 = 1 * 2 ^ k + (j.1 - 2 ^ k) := by omega
        have hieq : i.1 = 0 * 2 ^ k + i.1 := by simp
        conv => rhs; rw [hieq, hjeq, nat_and_msb_split k 0 1 i.1 (j.1 - 2 ^ k) hi hj']
        simp
    · rename_i hi
      have hi' : i.1 - 2 ^ k < 2 ^ k := by omega
      split
      · rename_i hj
        have hieq : i.1 = 1 * 2 ^ k + (i.1 - 2 ^ k) := by omega
        have hjeq : j.1 = 0 * 2 ^ k + j.1 := by simp
        conv => rhs; rw [hieq, hjeq, nat_and_msb_split k 1 0 (i.1 - 2 ^ k) j.1 hi' hj]
        simp
      · rename_i hj
        have hj' : j.1 - 2 ^ k < 2 ^ k := by omega
        have hieq : i.1 = 1 * 2 ^ k + (i.1 - 2 ^ k) := by omega
        have hjeq : j.1 = 1 * 2 ^ k + (j.1 - 2 ^ k) := by omega
        have hlt : (i.1 - 2 ^ k) &&& (j.1 - 2 ^ k) < 2 ^ k := Nat.and_lt_two_pow _ hj'
        conv => rhs; rw [hieq, hjeq, nat_and_msb_split k 1 1 (i.1 - 2 ^ k) (j.1 - 2 ^ k) hi' hj',
                         popcount_msb_split k (1 &&& 1) _ hlt]
        have hp1 : popcount (1 &&& 1) = 1 := by
          change popcount 1 = 1; rw [popcount_step 1]; simp [popcount_zero]
        rw [hp1]; omega

/-- Concrete identification: `weightedAndMat k (fun r => 2 ^ r)` IS `(x &&& y)`. -/
theorem weightedAndMat_pow2_eq_and (k : Nat) :
    weightedAndMat k (fun r => 2 ^ r) = fun x y : Fin (2 ^ k) => ((x.1 &&& y.1 : Nat) : Int) := by
  induction k with
  | zero =>
    apply matExt; intro i j
    simp [weightedAndMat, matZero]
  | succ k ih =>
    apply matExt; intro i j
    simp only [weightedAndMat, castMat, blockMat, matAdd, matSmul, onesMat, ih]
    split
    · rename_i hi
      split
      · rename_i hj; rfl
      · rename_i hj
        have hj' : j.1 - 2 ^ k < 2 ^ k := by omega
        have hjeq : j.1 = 1 * 2 ^ k + (j.1 - 2 ^ k) := by omega
        have hieq : i.1 = 0 * 2 ^ k + i.1 := by simp
        conv => rhs; rw [hieq, hjeq, nat_and_msb_split k 0 1 i.1 (j.1 - 2 ^ k) hi hj']
        simp
    · rename_i hi
      have hi' : i.1 - 2 ^ k < 2 ^ k := by omega
      split
      · rename_i hj
        have hieq : i.1 = 1 * 2 ^ k + (i.1 - 2 ^ k) := by omega
        have hjeq : j.1 = 0 * 2 ^ k + j.1 := by simp
        conv => rhs; rw [hieq, hjeq, nat_and_msb_split k 1 0 (i.1 - 2 ^ k) j.1 hi' hj]
        simp
      · rename_i hj
        have hj' : j.1 - 2 ^ k < 2 ^ k := by omega
        have hieq : i.1 = 1 * 2 ^ k + (i.1 - 2 ^ k) := by omega
        have hjeq : j.1 = 1 * 2 ^ k + (j.1 - 2 ^ k) := by omega
        conv => rhs; rw [hieq, hjeq, nat_and_msb_split k 1 1 (i.1 - 2 ^ k) (j.1 - 2 ^ k) hi' hj']
        have h11 : 1 &&& 1 = 1 := rfl
        rw [h11, Nat.one_mul, Int.mul_one]; omega

/-- **COROLLARY 3a**: `popcount(x &&& y)` has exact canonical SNF `(1^k, 0^{2^k - k})` ∀ k ≥ 0. -/
theorem snf_popcount_and (k : Nat) :
    HasSNF (fun x y : Fin (2 ^ k) => (popcount (x.1 &&& y.1) : Int))
           (fun i : Fin (2 ^ k) => if i.1 < k then 1 else 0) := by
  rw [← weightedAndMat_one_eq_popcount_and k]
  exact snf_weightedAndMat k (fun _ => 1) (fun _ _ => Nat.dvd_refl 1)

/-- **COROLLARY 3b**: `x &&& y` has exact canonical SNF `(1, 2, 4, ..., 2^{k-1}, 0^{2^k - k})` ∀ k ≥ 0. -/
theorem snf_bitwise_and (k : Nat) :
    HasSNF (fun x y : Fin (2 ^ k) => ((x.1 &&& y.1 : Nat) : Int))
           (fun i : Fin (2 ^ k) => if i.1 < k then 2 ^ i.1 else 0) := by
  rw [← weightedAndMat_pow2_eq_and k]
  exact snf_weightedAndMat k (fun r => 2 ^ r) (fun r _ => Nat.pow_dvd_pow 2 (by omega))

-- ============================================================================
-- THEOREM 4: KRONECKER BIT-SLICE SNF FOR `q ^ popcount(x & y)` (∀ k ≥ 0)
-- (Unifying unimodular `2^popcount(x & y)` and Walsh-Hadamard `(-1)^popcount(x & y)`
--  with exact binomial multiplicity `Nat.choose k j`)
-- ============================================================================

theorem baseQMat_unimodEquiv (q : Int) :
    UnimodEquiv (baseQMat q) (diagMat (fun i : Fin 2 => if i.1 = 0 then 1 else q - 1)) := by
  let U : Unimod 2 := {
    val := fun i j => if i = j then 1 else if i.1 = 1 ∧ j.1 = 0 then -1 else 0
    inv := fun i j => if i = j then 1 else if i.1 = 1 ∧ j.1 = 0 then 1 else 0
    mul_inv := by
      apply matExt; intro i j
      rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
      have hi2 : i = 0 ∨ i = 1 := by omega
      have hj2 : j = 0 ∨ j = 1 := by omega
      rcases hi2 with rfl | rfl <;> rcases hj2 with rfl | rfl <;>
        simp [matMul, sumFin, matId]
    inv_mul := by
      apply matExt; intro i j
      rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
      have hi2 : i = 0 ∨ i = 1 := by omega
      have hj2 : j = 0 ∨ j = 1 := by omega
      rcases hi2 with rfl | rfl <;> rcases hj2 with rfl | rfl <;>
        simp [matMul, sumFin, matId]
  }
  refine ⟨U, U.transpose, ?_⟩
  apply matExt; intro i j
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
  have hi2 : i = 0 ∨ i = 1 := by omega
  have hj2 : j = 0 ∨ j = 1 := by omega
  rcases hi2 with rfl | rfl <;> rcases hj2 with rfl | rfl <;>
    (simp [matMul, sumFin, U, Unimod.transpose, matTranspose, baseQMat, diagMat]; try omega)

theorem two_mul_pow2 (k : Nat) : 2 * 2 ^ k = 2 ^ (k + 1) := by
  rw [Nat.pow_succ, Nat.mul_comm]

/-- Exact Kronecker factorization `qPopAndMat (k+1) q = baseQMat q ⊗ qPopAndMat k q`. -/
theorem qPopAndMat_kron (k : Nat) (q : Int) :
    castMat (two_mul_pow2 k).symm (qPopAndMat (k + 1) q) = kronMat (baseQMat q) (qPopAndMat k q) := by
  apply matExt; intro i j
  simp only [castMat, qPopAndMat, kronMat, baseQMat, finDiv, finMod]
  have hN := pow2_pos k
  have hi_split : i.1 = (i.1 / 2 ^ k) * 2 ^ k + i.1 % 2 ^ k := by
    have h := Nat.div_add_mod i.1 (2 ^ k)
    rw [Nat.mul_comm (2 ^ k) (i.1 / 2 ^ k)] at h; exact h.symm
  have hj_split : j.1 = (j.1 / 2 ^ k) * 2 ^ k + j.1 % 2 ^ k := by
    have h := Nat.div_add_mod j.1 (2 ^ k)
    rw [Nat.mul_comm (2 ^ k) (j.1 / 2 ^ k)] at h; exact h.symm
  have hi_lt : i.1 % 2 ^ k < 2 ^ k := Nat.mod_lt _ hN
  have hj_lt : j.1 % 2 ^ k < 2 ^ k := Nat.mod_lt _ hN
  have hand : i.1 &&& j.1 = ((i.1 / 2 ^ k) &&& (j.1 / 2 ^ k)) * 2 ^ k + (i.1 % 2 ^ k &&& j.1 % 2 ^ k) := by
    conv => lhs; rw [hi_split, hj_split]
    exact nat_and_msb_split k _ _ _ _ hi_lt hj_lt
  have hpop : popcount (i.1 &&& j.1) =
      popcount ((i.1 / 2 ^ k) &&& (j.1 / 2 ^ k)) + popcount (i.1 % 2 ^ k &&& j.1 % 2 ^ k) := by
    rw [hand, popcount_msb_split k _ _ (Nat.and_lt_two_pow _ hj_lt)]
  rw [hpop, Int.pow_add]
  have hdi : i.1 / 2 ^ k = 0 ∨ i.1 / 2 ^ k = 1 := by
    have hlt2 : i.1 / 2 ^ k < 2 := Nat.div_lt_of_lt_mul (Nat.mul_comm 2 (2 ^ k) ▸ i.isLt)
    match h : i.1 / 2 ^ k with
    | 0 => exact Or.inl rfl
    | 1 => exact Or.inr rfl
    | _ + 2 => rw [h] at hlt2; omega
  have hdj : j.1 / 2 ^ k = 0 ∨ j.1 / 2 ^ k = 1 := by
    have hlt2 : j.1 / 2 ^ k < 2 := Nat.div_lt_of_lt_mul (Nat.mul_comm 2 (2 ^ k) ▸ j.isLt)
    match h : j.1 / 2 ^ k with
    | 0 => exact Or.inl rfl
    | 1 => exact Or.inr rfl
    | _ + 2 => rw [h] at hlt2; omega
  have hp0 : popcount 0 = 0 := popcount_zero
  have hp1 : popcount 1 = 1 := by rw [popcount_step 1]; simp [popcount_zero]
  rcases hdi with hi0 | hi1 <;> rcases hdj with hj0 | hj1
  · simp [hi0, hj0, hp0]
  · simp [hi0, hj1, hp0]
  · simp [hi1, hj0, hp0]
  · simp [hi1, hj1, show (1 &&& 1) = 1 from rfl, hp1, Int.pow_one]

/-- Unordered Kronecker diagonalization of `q ^ popcount(x & y)`:
    `qPopAndMat k q ~ diag(|q - 1| ^ popcount(i))` for ALL `k ≥ 0`, `q : Int`! -/
theorem qPopAndMat_diag_equiv (k : Nat) (q : Int) :
    UnimodEquiv (qPopAndMat k q) (diagMatNat (fun i : Fin (2 ^ k) => (q - 1).natAbs ^ popcount i.1)) := by
  induction k with
  | zero =>
    have heq : qPopAndMat 0 q = diagMatNat (fun i : Fin (2 ^ 0) => (q - 1).natAbs ^ popcount i.1) := by
      apply matExt; intro i j
      have hi : i = ⟨0, by decide⟩ := Fin.ext (by omega)
      have hj : j = ⟨0, by decide⟩ := Fin.ext (by omega)
      subst hi; subst hj; simp [qPopAndMat, diagMatNat, popcount_zero]
    rw [heq]; exact UnimodEquiv.refl _
  | succ k ih =>
    have hbase : UnimodEquiv (baseQMat q) (diagMatNat (fun i : Fin 2 => if i.1 = 0 then 1 else (q - 1).natAbs)) := by
      have h1 := baseQMat_unimodEquiv q
      have h2 := UnimodEquiv.diag_abs (fun i : Fin 2 => if i.1 = 0 then 1 else q - 1)
      have heq : diagMatNat (fun i : Fin 2 => (if i.1 = 0 then (1 : Int) else q - 1).natAbs) =
                 diagMatNat (fun i : Fin 2 => if i.1 = 0 then 1 else (q - 1).natAbs) := by
        apply matExt; intro i j; simp only [diagMatNat]
        by_cases hij : i = j
        · subst hij; by_cases hi0 : i.1 = 0 <;> simp [hi0]
        · simp [hij]
      rw [heq] at h2; exact h1.trans h2
    have hkron := unimodEquiv_kron hbase ih
    rw [← qPopAndMat_kron k q] at hkron
    have hdiag_kron : kronMat (diagMatNat (fun i : Fin 2 => if i.1 = 0 then 1 else (q - 1).natAbs))
                              (diagMatNat (fun i : Fin (2 ^ k) => (q - 1).natAbs ^ popcount i.1)) =
                      castMat (two_mul_pow2 k).symm
                              (diagMatNat (fun i : Fin (2 ^ (k + 1)) => (q - 1).natAbs ^ popcount i.1)) := by
      apply matExt; intro i j
      simp only [kronMat, diagMatNat, castMat]
      by_cases hij : i = j
      · subst hij
        simp only [↓reduceIte]
        have hN := pow2_pos k
        have hi_split : i.1 = (i.1 / 2 ^ k) * 2 ^ k + i.1 % 2 ^ k := by
          have h := Nat.div_add_mod i.1 (2 ^ k)
          rw [Nat.mul_comm (2 ^ k) (i.1 / 2 ^ k)] at h; exact h.symm
        have hpop : popcount i.1 = popcount (i.1 / 2 ^ k) + popcount (i.1 % 2 ^ k) := by
          conv => lhs; rw [hi_split]
          exact popcount_msb_split k _ _ (Nat.mod_lt _ hN)
        have hdi : i.1 / 2 ^ k = 0 ∨ i.1 / 2 ^ k = 1 := by
          have hlt2 : i.1 / 2 ^ k < 2 := Nat.div_lt_of_lt_mul (Nat.mul_comm 2 (2 ^ k) ▸ i.isLt)
          match h : i.1 / 2 ^ k with
          | 0 => exact Or.inl rfl
          | 1 => exact Or.inr rfl
          | _ + 2 => rw [h] at hlt2; omega
        have hp1 : popcount 1 = 1 := by rw [popcount_step 1]; simp [popcount_zero]
        simp only [finDiv, finMod]
        rcases hdi with h0 | h1
        · simp [h0, hpop, popcount_zero]
        · simp only [h1, show (1 : Nat) ≠ 0 by decide, ↓reduceIte, hpop, hp1]
          rw [← Int.natCast_mul, Nat.pow_add, Nat.pow_one, Nat.mul_comm]
      · have hval : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
        simp only [fin_mk_ne hval, ↓reduceIte]
        by_cases hdiv : finDiv i = finDiv j
        · have hmod : finMod i ≠ finMod j := by
            intro hm; apply hij; apply Fin.ext
            have hd : i.1 / 2 ^ k = j.1 / 2 ^ k := congrArg Fin.val hdiv
            have hmd : i.1 % 2 ^ k = j.1 % 2 ^ k := congrArg Fin.val hm
            rw [← Nat.div_add_mod i.1 (2 ^ k), ← Nat.div_add_mod j.1 (2 ^ k), hd, hmd]
          simp [hmod]
        · simp [hdiv]
    rw [hdiag_kron] at hkron
    have hcast := unimodEquiv_cast (two_mul_pow2 k) hkron
    have hcast_id : ∀ (A : Mat (2 ^ (k + 1))),
        castMat (two_mul_pow2 k) (castMat (two_mul_pow2 k).symm A) = A := by
      intro A; apply matExt; intro i j; rfl
    rw [hcast_id, hcast_id] at hcast
    exact hcast

/-- Exact binomial popcount histogram: `#{x < 2^k : popcount(x) = j} = binom k j`. -/
theorem countFin_popcount_eq_choose (k : Nat) :
    ∀ j : Nat, countFin (2 ^ k) (fun i : Fin (2 ^ k) => decide (popcount i.1 = j)) = binom k j := by
  induction k with
  | zero =>
    intro j
    simp only [Nat.pow_zero, countFin, Fin.last, popcount_zero]
    cases j with
    | zero => simp [binom]
    | succ j => simp [binom]
  | succ k ih =>
    intro j
    have hsum : (countFin (2 ^ (k + 1)) (fun i : Fin (2 ^ (k + 1)) => decide (popcount i.1 = j)) : Int) =
                (countFin (2 ^ k) (fun i : Fin (2 ^ k) => decide (popcount i.1 = j)) : Int) +
                (countFin (2 ^ k) (fun i : Fin (2 ^ k) => decide (popcount (2 ^ k + i.1) = j)) : Int) := by
      rw [countFin_eq_sumFin, countFin_eq_sumFin, countFin_eq_sumFin]
      rw [sumFin_cast (pow2_add_self k).symm, sumFin_split]
    have hhi : ∀ i : Fin (2 ^ k), popcount (2 ^ k + i.1) = 1 + popcount i.1 := by
      intro i
      have h1 : 2 ^ k + i.1 = 1 * 2 ^ k + i.1 := by simp
      rw [h1, popcount_msb_split k 1 i.1 i.isLt]
      have hp1 : popcount 1 = 1 := by rw [popcount_step 1]; simp [popcount_zero]
      rw [hp1]
    have hcast_nat : countFin (2 ^ (k + 1)) (fun i : Fin (2 ^ (k + 1)) => decide (popcount i.1 = j)) =
                     countFin (2 ^ k) (fun i : Fin (2 ^ k) => decide (popcount i.1 = j)) +
                     countFin (2 ^ k) (fun i : Fin (2 ^ k) => decide (1 + popcount i.1 = j)) := by
      have hcongr : countFin (2 ^ k) (fun i : Fin (2 ^ k) => decide (popcount (2 ^ k + i.1) = j)) =
                    countFin (2 ^ k) (fun i : Fin (2 ^ k) => decide (1 + popcount i.1 = j)) := by
        have : (fun i : Fin (2 ^ k) => decide (popcount (2 ^ k + i.1) = j)) =
               (fun i : Fin (2 ^ k) => decide (1 + popcount i.1 = j)) := by
          funext i; rw [hhi i]
        rw [this]
      rw [hcongr] at hsum
      exact Int.ofNat.inj (by simpa [Int.natCast_add] using hsum)
    rw [hcast_nat, ih j]
    cases j with
    | zero =>
      have hz : countFin (2 ^ k) (fun i : Fin (2 ^ k) => decide (1 + popcount i.1 = 0)) = 0 := by
        have : (countFin (2 ^ k) (fun i : Fin (2 ^ k) => decide (1 + popcount i.1 = 0)) : Int) = 0 := by
          rw [countFin_eq_sumFin]
          calc sumFin (2 ^ k) (fun i => if decide (1 + popcount i.1 = 0) then (1 : Int) else 0)
              = sumFin (2 ^ k) (fun _ => 0) := by apply sumFin_congr; intro i; simp
            _ = 0 := sumFin_zero _
        exact Int.ofNat.inj this
      rw [hz]; simp [binom]
    | succ j =>
      have hpred : (fun i : Fin (2 ^ k) => decide (1 + popcount i.1 = j + 1)) =
                   (fun i : Fin (2 ^ k) => decide (popcount i.1 = j)) := by
        funext i
        have hiff : 1 + popcount i.1 = j + 1 ↔ popcount i.1 = j := by omega
        by_cases h : popcount i.1 = j
        · simp [h, Nat.add_comm]
        · simp [h, mt hiff.mp h]
      rw [hpred, ih j]; simp only [binom]; omega

/-- **THEOREM 4 (Exact Canonical SNF + Binomial Multiplicities of `q ^ popcount(x & y)`)**:
    For ALL `k ≥ 0` and ALL `q : Int`, `qPopAndMat k q` has canonical sorted SNF
    `d(i) = |q - 1| ^ popcount(π(i))` where `π = sortPerm (2^k) popcount`, with exact binomial
    exponent multiplicity `#{i : popcount(π(i)) = j} = binom k j`! -/
theorem snf_qPopAndMat (k : Nat) (q : Int) :
    let π := sortPerm (2 ^ k) (fun i : Fin (2 ^ k) => popcount i.1)
    HasSNF (qPopAndMat k q) (fun i : Fin (2 ^ k) => (q - 1).natAbs ^ popcount (π.toFun i).1) ∧
    (∀ j, countFin (2 ^ k) (fun i => decide (popcount (π.toFun i).1 = j)) = binom k j) := by
  intro π
  refine ⟨⟨(qPopAndMat_diag_equiv k q).trans (UnimodEquiv.diag_perm _ π), ?_⟩, ?_⟩
  · intro i hi
    have hmono := sortPerm_mono (2 ^ k) (fun r : Fin (2 ^ k) => popcount r.1) i ⟨i.1 + 1, hi⟩ (Nat.le_succ i.1)
    exact Nat.pow_dvd_pow (q - 1).natAbs hmono
  · intro j
    rw [countFin_perm π (fun i : Fin (2 ^ k) => decide (popcount i.1 = j))]
    exact countFin_popcount_eq_choose k j

/-- **COROLLARY 4a**: `2 ^ popcount(x &&& y)` is UNIMODULAR (`HasSNF = [1^{2^k}]`) ∀ k ≥ 0! -/
theorem snf_two_pow_popcount_and_unimod (k : Nat) :
    HasSNF (qPopAndMat k 2) (fun _ : Fin (2 ^ k) => 1) := by
  have h := (snf_qPopAndMat k 2).1
  have h1 : (fun i : Fin (2 ^ k) => ((2 : Int) - 1).natAbs ^ popcount ((sortPerm (2 ^ k) (fun r => popcount r.1)).toFun i).1) =
            (fun _ : Fin (2 ^ k) => 1) := by funext i; simp
  rw [h1] at h; exact h

/-- **COROLLARY 4b (Walsh-Hadamard Binomial SNF — Contrast with Flat Carry-Parity Sign SNF)**:
    `(-1) ^ popcount(x &&& y)` has sorted SNF diagonal `2^j` with exact multiplicity `binom k j`! -/
theorem snf_walsh_hadamard_binomial (k : Nat) :
    let π := sortPerm (2 ^ k) (fun i : Fin (2 ^ k) => popcount i.1)
    HasSNF (qPopAndMat k (-1)) (fun i : Fin (2 ^ k) => 2 ^ popcount (π.toFun i).1) ∧
    (∀ j, countFin (2 ^ k) (fun i => decide (popcount (π.toFun i).1 = j)) = binom k j) := by
  have h := snf_qPopAndMat k (-1)
  simpa using h

-- ============================================================================
-- PART IV: NON-VACUITY WITNESSES, SHARPNESS COUNTEREXAMPLES, AND AXIOM RECEIPTS
-- ============================================================================

-- 1. Non-Vacuity Witnesses (constructive inhabitants of every theorem family)

example : HasSNF (affineCarryParMat 3 3 5) (affineCarrySNFDiag 3 3 5) :=
  snf_affine_carry_parity 3 (by decide) 3 5

example : HasSNF (carrySignMat 4) (fun i : Fin (2 ^ 4) => if i.1 = 0 then 1 else 2) :=
  snf_carry_sign_flat 4 (by decide)

example : HasSNF (carryParMat 3 1) (fun _ : Fin (2 ^ 3) => 1) := by
  simpa using snf_carry_parity_one_dichotomy 3

example : HasSNF (T1Mat 3) (fun i : Fin (2 ^ 3) => addXorSNFDiag i.1) :=
  snf_T1Mat 3

example : HasSNF (T1ModMat 3) (fun i : Fin (2 ^ 3) => if i.1 < 4 then addXorSNFDiag i.1 else 0) :=
  snf_T1ModMat_collapse 2

example : HasSNF (weightedAndMat 3 (fun r => 2 ^ r)) (fun i : Fin (2 ^ 3) => if i.1 < 3 then 2 ^ i.1 else 0) :=
  snf_weightedAndMat 3 (fun r => 2 ^ r) (fun r _ => Nat.pow_dvd_pow 2 (by omega))

example : HasSNF (qPopAndMat 3 2) (fun _ : Fin (2 ^ 3) => 1) :=
  snf_two_pow_popcount_and_unimod 3

-- 2. Kernel-Checked Sharpness Counterexample 1:
--    Carry-In Parity Dichotomy sharpness: `C_2^(1)` (even k=2) is NOT unimodular (explicit nonzero kernel vector!)

theorem sharpness_carry_in_even_not_unimod :
    ¬ (∃ U : Unimod (2 ^ 2), U.val = carryParMat 2 1) := by
  intro ⟨U, hU⟩
  -- Explicit nonzero kernel vector v = (1, 0, -1, 1)? Check: C_2^(1) = [[0,1,0,1],[1,1,1,0],[0,1,1,0],[1,0,0,0]]?
  -- Wait: use HasSNF.zero_entry_kernel directly from our proved Theorem 1c!
  have hsnf := snf_carry_parity_one_dichotomy 2
  have hzero : (if 2 % 2 = 1 then 1 else if (⟨3, by decide⟩ : Fin (2 ^ 2)).1 + 1 = 2 ^ 2 then 0 else 1) = 0 := by
    decide
  rcases hsnf.zero_entry_kernel ⟨3, by decide⟩ hzero with ⟨v, ⟨j, hj⟩, hMv⟩
  have hv0 : v = fun _ => 0 := by
    calc v = matVec (matId (2 ^ 2)) v := (matVec_id v).symm
      _ = matVec (matMul U.inv U.val) v := by rw [U.inv_mul]
      _ = matVec U.inv (matVec (carryParMat 2 1) v) := by rw [hU, matVec_mul]
      _ = matVec U.inv (fun _ => 0) := by rw [hMv]
      _ = fun _ => 0 := matVec_zero _
  exact hj (congrFun hv0 j)

-- 3. Kernel-Checked Sharpness Counterexample 2:
--    Truncation Collapse sharpness: dropping bit `k` makes `T1ModMat 2` singular (explicit kernel vector),
--    whereas untruncated `T1Mat 2` is strictly injective on `Z^4`!

theorem sharpness_T1Mat_injective_vs_T1ModMat_singular :
    (∀ x : Fin (2 ^ 2) → Int, matVec (T1Mat 2) x = (fun _ => 0) → x = fun _ => 0) ∧
    (∃ v : Fin (2 ^ 2) → Int, (∃ j, v j ≠ 0) ∧ matVec (T1ModMat 2) v = fun _ => 0) := by
  constructor
  · refine (snf_T1Mat 2).injective_of_ne_zero ?_
    have hall : ∀ i : Fin (2 ^ 2), addXorSNFDiag i.1 ≠ 0 := by decide
    exact hall
  · refine (snf_T1ModMat_collapse 1).zero_entry_kernel ⟨2, by decide⟩ (by decide)

theorem sumFin4 (f : Fin 4 → Int) :
    sumFin 4 f = f ⟨0, by decide⟩ + f ⟨1, by decide⟩ + f ⟨2, by decide⟩ + f ⟨3, by decide⟩ := by
  simp only [sumFin, Fin.castSucc, Fin.last, Fin.castAdd, Int.zero_add]
  rfl

theorem sharpness_mod3_refutes_unimod_nonzero :
    ¬ HasSNF carriesMod3Mat2 (fun i : Fin 4 => if i.1 + 1 = 4 then 0 else 1) := by
  intro ⟨⟨U, V, hUV⟩, _⟩
  have hmod3 : ∀ y : Fin 4 → Int, (matVec carriesMod3Mat2 y ⟨1, by decide⟩ -
                                   matVec carriesMod3Mat2 y ⟨2, by decide⟩ +
                                   matVec carriesMod3Mat2 y ⟨3, by decide⟩) % 3 = 0 := by
    intro y
    simp [matVec, sumFin4, carriesMod3Mat2, carriesK]
    omega
  have hb0 : ∀ y : Fin 4 → Int, matVec carriesMod3Mat2 y ⟨0, by decide⟩ = 0 := by
    intro y
    simp [matVec, sumFin4, carriesMod3Mat2, carriesK]
  have hcol_in_im : ∀ k : Fin 4, k.1 < 3 → ∃ y : Fin 4 → Int,
      matVec carriesMod3Mat2 y = fun r => U.inv r k := by
    intro k hk
    let ek : Fin 4 → Int := fun j => if j = k then 1 else 0
    refine ⟨matVec V.val ek, ?_⟩
    have hdiag : matVec (diagMatNat (fun i : Fin 4 => if i.1 + 1 = 4 then 0 else 1)) ek = ek := by
      funext r; simp only [matVec, diagMatNat, ek]
      have hs : sumFin 4 (fun j => (if r = j then ((if r.1 + 1 = 4 then 0 else 1 : Nat) : Int) else 0) *
                                   (if j = k then 1 else 0)) =
                sumFin 4 (fun j => if r = j then (if j = k then ((if r.1 + 1 = 4 then 0 else 1 : Nat) : Int) else 0) else 0) := by
        apply sumFin_congr; intro j
        by_cases h1 : r = j
        · subst h1; by_cases h2 : r = k <;> simp [h2]
        · simp [h1]
      rw [hs, sumFin_single_symm]
      by_cases hrk : r = k
      · subst hrk
        have hne : r.1 + 1 ≠ 4 := by omega
        simp [hne]
      · simp [hrk]
    have hMV : matVec carriesMod3Mat2 (matVec V.val ek) = matVec U.inv ek := by
      calc matVec carriesMod3Mat2 (matVec V.val ek)
          = matVec (matId 4) (matVec carriesMod3Mat2 (matVec V.val ek)) := (matVec_id _).symm
        _ = matVec (matMul U.inv U.val) (matVec carriesMod3Mat2 (matVec V.val ek)) := by rw [U.inv_mul]
        _ = matVec U.inv (matVec (matMul (matMul U.val carriesMod3Mat2) V.val) ek) := by
            rw [matVec_mul, matVec_mul (matMul U.val carriesMod3Mat2) V.val ek, matVec_mul]
        _ = matVec U.inv (matVec (diagMatNat (fun i : Fin 4 => if i.1 + 1 = 4 then 0 else 1)) ek) := by rw [hUV]
        _ = matVec U.inv ek := by rw [hdiag]
    rw [hMV]
    funext r; simp only [matVec, ek]
    have hs : sumFin 4 (fun j => U.inv r j * (if j = k then 1 else 0)) =
              sumFin 4 (fun j => if j = k then U.inv r j else 0) := by
      apply sumFin_congr; intro j; by_cases hj : j = k <;> simp [hj]
    rw [hs, sumFin_single_eq]
  rcases hcol_in_im ⟨0, by decide⟩ (by decide) with ⟨y0, hy0⟩
  rcases hcol_in_im ⟨1, by decide⟩ (by decide) with ⟨y1, hy1⟩
  rcases hcol_in_im ⟨2, by decide⟩ (by decide) with ⟨y2, hy2⟩
  have hz0 : U.inv ⟨0, by decide⟩ ⟨0, by decide⟩ = 0 := by rw [← congrFun hy0 ⟨0, by decide⟩]; exact hb0 y0
  have hz1 : U.inv ⟨0, by decide⟩ ⟨1, by decide⟩ = 0 := by rw [← congrFun hy1 ⟨0, by decide⟩]; exact hb0 y1
  have hz2 : U.inv ⟨0, by decide⟩ ⟨2, by decide⟩ = 0 := by rw [← congrFun hy2 ⟨0, by decide⟩]; exact hb0 y2
  have hm0 : (U.inv ⟨1, by decide⟩ ⟨0, by decide⟩ - U.inv ⟨2, by decide⟩ ⟨0, by decide⟩ + U.inv ⟨3, by decide⟩ ⟨0, by decide⟩) % 3 = 0 := by
    rw [← congrFun hy0 ⟨1, by decide⟩, ← congrFun hy0 ⟨2, by decide⟩, ← congrFun hy0 ⟨3, by decide⟩]; exact hmod3 y0
  have hm1 : (U.inv ⟨1, by decide⟩ ⟨1, by decide⟩ - U.inv ⟨2, by decide⟩ ⟨1, by decide⟩ + U.inv ⟨3, by decide⟩ ⟨1, by decide⟩) % 3 = 0 := by
    rw [← congrFun hy1 ⟨1, by decide⟩, ← congrFun hy1 ⟨2, by decide⟩, ← congrFun hy1 ⟨3, by decide⟩]; exact hmod3 y1
  have hm2 : (U.inv ⟨1, by decide⟩ ⟨2, by decide⟩ - U.inv ⟨2, by decide⟩ ⟨2, by decide⟩ + U.inv ⟨3, by decide⟩ ⟨2, by decide⟩) % 3 = 0 := by
    rw [← congrFun hy2 ⟨1, by decide⟩, ← congrFun hy2 ⟨2, by decide⟩, ← congrFun hy2 ⟨3, by decide⟩]; exact hmod3 y2
  have hI00 := congrFun (congrFun U.inv_mul ⟨0, by decide⟩) ⟨0, by decide⟩
  have hI01 := congrFun (congrFun U.inv_mul ⟨0, by decide⟩) ⟨1, by decide⟩
  have hI11 := congrFun (congrFun U.inv_mul ⟨1, by decide⟩) ⟨1, by decide⟩
  have hI21 := congrFun (congrFun U.inv_mul ⟨2, by decide⟩) ⟨1, by decide⟩
  have hI31 := congrFun (congrFun U.inv_mul ⟨3, by decide⟩) ⟨1, by decide⟩
  simp only [matMul, sumFin4, matId] at hI00 hI01 hI11 hI21 hI31
  rw [hz0, hz1, hz2] at hI00 hI01
  have hU31_zero : U.val ⟨3, by decide⟩ ⟨1, by decide⟩ = 0 := by
    have h00' : U.inv ⟨0, by decide⟩ ⟨3, by decide⟩ * U.val ⟨3, by decide⟩ ⟨0, by decide⟩ = 1 := by
      simpa using hI00
    have h01' : U.inv ⟨0, by decide⟩ ⟨3, by decide⟩ * U.val ⟨3, by decide⟩ ⟨1, by decide⟩ = 0 := by
      simpa using hI01
    have hne : U.inv ⟨0, by decide⟩ ⟨3, by decide⟩ ≠ 0 := by
      intro h; rw [h, Int.zero_mul] at h00'; omega
    exact (Int.mul_eq_zero.mp h01').resolve_left hne
  rw [hU31_zero] at hI11 hI21 hI31
  have hcomb :
      (U.inv ⟨1, by decide⟩ ⟨0, by decide⟩ - U.inv ⟨2, by decide⟩ ⟨0, by decide⟩ + U.inv ⟨3, by decide⟩ ⟨0, by decide⟩) * U.val ⟨0, by decide⟩ ⟨1, by decide⟩ +
      (U.inv ⟨1, by decide⟩ ⟨1, by decide⟩ - U.inv ⟨2, by decide⟩ ⟨1, by decide⟩ + U.inv ⟨3, by decide⟩ ⟨1, by decide⟩) * U.val ⟨1, by decide⟩ ⟨1, by decide⟩ +
      (U.inv ⟨1, by decide⟩ ⟨2, by decide⟩ - U.inv ⟨2, by decide⟩ ⟨2, by decide⟩ + U.inv ⟨3, by decide⟩ ⟨2, by decide⟩) * U.val ⟨2, by decide⟩ ⟨1, by decide⟩ = 1 := by
    have h11 : U.inv ⟨1, by decide⟩ ⟨0, by decide⟩ * U.val ⟨0, by decide⟩ ⟨1, by decide⟩ +
               U.inv ⟨1, by decide⟩ ⟨1, by decide⟩ * U.val ⟨1, by decide⟩ ⟨1, by decide⟩ +
               U.inv ⟨1, by decide⟩ ⟨2, by decide⟩ * U.val ⟨2, by decide⟩ ⟨1, by decide⟩ = 1 := by
      simpa using hI11
    have h21 : U.inv ⟨2, by decide⟩ ⟨0, by decide⟩ * U.val ⟨0, by decide⟩ ⟨1, by decide⟩ +
               U.inv ⟨2, by decide⟩ ⟨1, by decide⟩ * U.val ⟨1, by decide⟩ ⟨1, by decide⟩ +
               U.inv ⟨2, by decide⟩ ⟨2, by decide⟩ * U.val ⟨2, by decide⟩ ⟨1, by decide⟩ = 0 := by
      simpa using hI21
    have h31 : U.inv ⟨3, by decide⟩ ⟨0, by decide⟩ * U.val ⟨0, by decide⟩ ⟨1, by decide⟩ +
               U.inv ⟨3, by decide⟩ ⟨1, by decide⟩ * U.val ⟨1, by decide⟩ ⟨1, by decide⟩ +
               U.inv ⟨3, by decide⟩ ⟨2, by decide⟩ * U.val ⟨2, by decide⟩ ⟨1, by decide⟩ = 0 := by
      simpa using hI31
    simp only [Int.add_mul, Int.sub_mul]
    omega
  have hdvd3 : ∀ x y : Int, x % 3 = 0 → (x * y) % 3 = 0 := by
    intro x y hx
    have : ∃ k : Int, x = 3 * k := ⟨x / 3, by omega⟩
    rcases this with ⟨k, rfl⟩
    rw [Int.mul_assoc]; omega
  have ht0 := hdvd3 _ (U.val ⟨0, by decide⟩ ⟨1, by decide⟩) hm0
  have ht1 := hdvd3 _ (U.val ⟨1, by decide⟩ ⟨1, by decide⟩) hm1
  have ht2 := hdvd3 _ (U.val ⟨2, by decide⟩ ⟨1, by decide⟩) hm2
  omega

theorem sharpness_blockSchur_requires_divisibility :
    HasSNF nonDivSchurMat (fun i : Fin (2 + 2) => if i.1 = 0 then 1 else if i.1 = 1 then 2 else 0) := by
  let Uval : Mat 4 := fun i j =>
    if i.1 = 0 then (if j.1 = 0 then 1 else 0)
    else if i.1 = 1 then (if j.1 = 3 then 1 else 0)
    else if i.1 = 2 then (if j.1 = 0 then -2 else if j.1 = 2 then 1 else 0)
    else (if j.1 = 1 then 1 else if j.1 = 3 then -2 else 0)
  let Uinv : Mat 4 := fun i j =>
    if i.1 = 0 then (if j.1 = 0 then 1 else 0)
    else if i.1 = 1 then (if j.1 = 1 then 2 else if j.1 = 3 then 1 else 0)
    else if i.1 = 2 then (if j.1 = 0 then 2 else if j.1 = 2 then 1 else 0)
    else (if j.1 = 1 then 1 else 0)
  let U : Unimod 4 := {
    val := Uval
    inv := Uinv
    mul_inv := by
      have h : ∀ i j : Fin 4, matMul Uval Uinv i j = matId 4 i j := by decide
      exact matExt h
    inv_mul := by
      have h : ∀ i j : Fin 4, matMul Uinv Uval i j = matId 4 i j := by decide
      exact matExt h
  }
  constructor
  · refine ⟨U, Unimod.id 4, ?_⟩
    have h : ∀ i j : Fin 4,
        matMul (matMul Uval nonDivSchurMat) (matId 4) i j =
        diagMatNat (fun i : Fin (2 + 2) => if i.1 = 0 then 1 else if i.1 = 1 then 2 else 0) i j := by
      decide
    exact matExt h
  · have h : ∀ (i : Fin 4) (hi : i.1 + 1 < 4),
        (if i.1 = 0 then 1 else if i.1 = 1 then 2 else 0) ∣
        (if i.1 + 1 = 0 then 1 else if i.1 + 1 = 1 then 2 else 0) := by decide
    exact h

end SiliconSNF
