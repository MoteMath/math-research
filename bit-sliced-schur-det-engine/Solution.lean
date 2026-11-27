import BitSlicedSchurDetEngine

namespace BitSlicedSchurDetEngineChallenge

open BitSlicedSchur

theorem det_mul {R : Type u} [CRing R] {R : Type u} [CRing R] {R : Type u} [CRing R] {R : Type u} [CRing R] {n : Nat} (A B : Mat R n) : det (matMul A B) = CRing.mul (det A) (det B) :=
  _root_.BitSlicedSchur.det_mul A B

theorem det_block_schur_left_unimodular {R : Type u} [CRing R] {R : Type u} [CRing R] {R : Type u} [CRing R] {R : Type u} [CRing R] {n : Nat} (A B C D L : Mat R n)
    (hLA : matMul L A = C) :
    det (blockMat A B C D) = CRing.mul (det A) (det (matSub D (matMul L B))) :=
  _root_.BitSlicedSchur.det_block_schur_left_unimodular A B C D L hLA

theorem det_block_schur_right_scaled {R : Type u} [CRing R] {R : Type u} [CRing R] {R : Type u} [CRing R] {R : Type u} [CRing R] {n : Nat} (A B C D U : Mat R n) (s : R)
    (hAU : matMul A U = matSmul s B) :
    CRing.mul (CRing.pow s n) (det (blockMat A B C D)) =
    CRing.mul (det A) (det (matSub (matSmul s D) (matMul C U))) :=
  _root_.BitSlicedSchur.det_block_schur_right_scaled A B C D U s hAU

theorem det_bitSliced_schur_zero_iff {R : Type u} [CRing R] {R : Type u} [CRing R] {R : Type u} [CRing R] {R : Type u} [CRing R] {R : Type u} [IntDomain R]
    {P : Nat → Type v}
    (M : ∀ k, P k → Mat R (pow2 k))
    (base : P 0 → R)
    (step : ∀ k, P (k + 1) → P k × P k)
    (hbase : ∀ p : P 0, det (M 0 p) = base p)
    (hstep : ∀ k (p : P (k + 1)),
      det (M (k + 1) p) = CRing.mul (det (M k (step k p).1)) (det (M k (step k p).2)))
    (k : Nat) (p : P k) :
    det (M k p) = CRing.zero ↔ ∃ s : Fin (pow2 k), evalBitTree base step k p s = CRing.zero :=
  _root_.BitSlicedSchur.det_bitSliced_schur_zero_iff M base step hbase hstep k p

theorem det_msbAnd_closed_form {R : Type u} [CRing R] {R : Type u} [CRing R] {R : Type u} [CRing R] {R : Type u} [CRing R] {R : Type u} [CRing R] (k : Nat) (f : Nat → R) :
    det (msbAndMat k f) =
    if k = 0 then f 0
    else if k = 1 then CRing.mul (f 0) (CRing.sub (f 1) (f 0))
    else CRing.neg (CRing.mul (f 0) (prodFin k (fun j => CRing.pow (CRing.sub (f (j.val + 1)) (f 0)) (pow2 (k - 1 - j.val))))) :=
  _root_.BitSlicedSchur.det_msbAnd_closed_form k f

theorem det_subsetDisjMat_closed_form {R : Type u} [CRing R] {R : Type u} [CRing R] {R : Type u} [CRing R] {R : Type u} [CRing R] {R : Type u} [CRing R] {R : Type u} [CRing R] (k : Nat) (a c : R) :
    det (subsetDisjMat (k + 1) a c) =
    CRing.pow (CRing.sub (CRing.mul a a) (CRing.mul c c)) (pow2 k) :=
  _root_.BitSlicedSchur.det_subsetDisjMat_closed_form k a c

theorem witness_zmod6_zero_divisors {R : Type u} [CRing R] {R : Type u} [CRing R] {R : Type u} [CRing R] {R : Type u} [CRing R] {R : Type u} [CRing R] {R : Type u} [CRing R] :
    CRing.mul (⟨2, by omega⟩ : ZMod 5) ⟨3, by omega⟩ = CRing.zero ∧
    det (hcbMat (R := ZMod 5)
          (fun m => if m = 1 then ⟨2, by omega⟩ else ⟨3, by omega⟩)
          (fun m => if m = 1 then ⟨5, by omega⟩ else ⟨2, by omega⟩)
          (fun _ => ⟨1, by omega⟩)
          (fun _ => ⟨2, by omega⟩)
          2 (fun j => if j = 1 then ⟨2, by omega⟩ else ⟨1, by omega⟩)) =
    ⟨1, by omega⟩ :=
  _root_.BitSlicedSchur.witness_zmod6_zero_divisors

theorem counterexample_bool_plus_superset_breaks {R : Type u} [CRing R] {R : Type u} [CRing R] {R : Type u} [CRing R] {R : Type u} [CRing R] {R : Type u} [CRing R] {R : Type u} [CRing R] :
    det (R := Int) (fun x y : Fin (pow2 1) =>
      (if (x.val &&& y.val) = x.val then (1 : Int) else 0) +
      (if (x.val &&& y.val) = y.val then 1 else 0) +
      (if (x.val &&& y.val) = 0 then 1 else 0)) = 2 ∧
    det (R := Int) (fun x y : Fin (pow2 2) =>
      (if (x.val &&& y.val) = x.val then (1 : Int) else 0) +
      (if (x.val &&& y.val) = y.val then 1 else 0) +
      (if (x.val &&& y.val) = 0 then 1 else 0)) = 0 :=
  _root_.BitSlicedSchur.counterexample_bool_plus_superset_breaks

end BitSlicedSchurDetEngineChallenge
