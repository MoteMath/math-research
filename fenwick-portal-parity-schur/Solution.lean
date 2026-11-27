import FenwickPortalParitySchur

namespace FenwickPortalParitySchurChallenge

open SpecMat7

theorem portalTuple_perturb {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] {n : Nat} (M : Mat (n + 2) R) (p q1 q2 r : R) :
    portalTuple (perturb M p q1 q2 r) = stepPerturb (portalTuple M) p q1 q2 r :=
  _root_.SpecMat7.portalTuple_perturb M p q1 q2 r

theorem bordered_schur_inv {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] {n : Nat}
    (B Binv : Mat n R) (u : Fin n → R) (σ : R)
    (hBinv : matMul B Binv = matId n)
    (_hBsym : ∀ i j, B i j = B j i)
    (hBinvSym : ∀ i j, Binv i j = Binv j i)
    (hσ : sumFin (fun k : Fin n => u k *ᵣ sumFin (fun r : Fin n => Binv k r *ᵣ u r)) = σ) :
    let w : Fin n → R := fun i => sumFin (fun r : Fin n => Binv i r *ᵣ u r)
    let A : Mat (n + 1) R := fun i j =>
      if hi : i.val = 0 then
        if hj : j.val = 0 then zᵣ else u ⟨j.val - 1, by omega⟩
      else
        if hj : j.val = 0 then u ⟨i.val - 1, by omega⟩
        else B ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩
    let J : Mat (n + 1) R := fun i j =>
      if hi : i.val = 0 then
        if hj : j.val = 0 then -ᵣeᵣ else w ⟨j.val - 1, by omega⟩
      else
        if hj : j.val = 0 then w ⟨i.val - 1, by omega⟩
        else σ *ᵣ Binv ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩ -ᵣ
             w ⟨i.val - 1, by omega⟩ *ᵣ w ⟨j.val - 1, by omega⟩
    matMul A J = fun i j => if i = j then σ else zᵣ :=
  _root_.SpecMat7.bordered_schur_inv B Binv u σ hBinv _hBsym hBinvSym hσ

theorem fenwickUQ_unimodular {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] (c : R) (k : Nat) (hk : 2 ≤ k) :
    det (minor (fenwickUQAdj (R := R) k c) ⟨0, Nat.zero_lt_succ _⟩ ⟨0, Nat.zero_lt_succ _⟩) = eᵣ :=
  _root_.SpecMat7.fenwickUQ_unimodular c k hk

theorem fenwickUQLap_charpoly_fps {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] (k : Nat) (hk : 1 ≤ k) :
    det (fenwickUQLapChar (R := FPS) k FPS.X) = (lapCharState FPS.X (k - 1)).d0 :=
  _root_.SpecMat7.fenwickUQLap_charpoly_fps k hk

theorem fenwickUQLap_spanning_tree_square {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] (k : Nat) (hk : 1 ≤ k) :
    det (minor (fenwickUQLap (R := Int) (k + 1)) ⟨0, Nat.zero_lt_succ _⟩ ⟨0, Nat.zero_lt_succ _⟩) =
    (tauSeq k + dSeq k) * (tauSeq k + dSeq k) :=
  _root_.SpecMat7.fenwickUQLap_spanning_tree_square k hk

theorem inOrderHeap_charpoly_factorization {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] (x : R) (k : Nat) (hk : 1 ≤ k) :
    det (inOrderHeapChar (R := R) k x) = chebT x k *ᵣ heapR x (k - 1) :=
  _root_.SpecMat7.inOrderHeap_charpoly_factorization x k hk

theorem witness_dyadic_inv_k2 {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] :
    matMul (fenwickUQAdj (R := Int) 2 1) (fenwickUQDyadicInv 2 (by omega)) =
    fun i j => if i = j then (4 : Int) else 0 :=
  _root_.SpecMat7.witness_dyadic_inv_k2

theorem sharpness_asymmetric_weights_k2 :
    let st1 : PortalState Int := ⟨0, -4, -1, 0, 2, 2⟩
    let st1L := stepPerturb st1 0 1 1 0
    let st1R := stepPerturb st1 0 2 2 0
    (stepGlue st1L st1R 0).d0 = -24 ∧ (stepGlue st1L st1R 0).d0 ≠ -4 :=
  _root_.SpecMat7.sharpness_asymmetric_weights_k2

end FenwickPortalParitySchurChallenge
