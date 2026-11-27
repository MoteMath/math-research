import FenwickPortalParitySchur.Defs

namespace FenwickPortalParitySchurChallenge

open SpecMat7

theorem portalTuple_perturb {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] {n : Nat} (M : Mat (n + 2) R) (p q1 q2 r : R) :
    portalTuple (perturb M p q1 q2 r) = stepPerturb (portalTuple M) p q1 q2 r := by
  sorry

/-- Bordered Dyadic/Scaled Inverse Lemma (Theorem B2): If `A` is a symmetric bordered matrix `[[0, u^T], [u, B]]` of size `n + 1`, `B * Binv = I_n`, `w = Binv * u`, and `u^T * w = σ`, then `J = [[-1, w^T], [w, σ * Binv - w * w^T]]` satisfies `A * J = σ * I_{n+1}`! -/
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
    matMul A J = fun i j => if i = j then σ else zᵣ := by
  sorry

/-- Theorem 1b (Unimodularity): Deleting portal `0` yields `det(A(G_k(c)) \ {0}) = 1` for ALL `k ≥ 2`! -/
theorem fenwickUQ_unimodular {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] (c : R) (k : Nat) (hk : 2 ≤ k) :
    det (minor (fenwickUQAdj (R := R) k c) ⟨0, Nat.zero_lt_succ _⟩ ⟨0, Nat.zero_lt_succ _⟩) = eᵣ := by
  sorry

/-- Theorem 2d (Exact Laplacian Polynomial-Ring `Z[X]` Instantiation via `FPS`): -/
theorem fenwickUQLap_charpoly_fps {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] (k : Nat) (hk : 1 ≤ k) :
    det (fenwickUQLapChar (R := FPS) k FPS.X) = (lapCharState FPS.X (k - 1)).d0 := by
  sorry

/-- Theorem 4b (Spanning-Tree Perfect-Square Law): By Kirchhoff's Matrix-Tree Theorem, the spanning-tree count `τ(G_{k+1}) = det(L(G_{k+1}) \ {0})` is ALWAYS a perfect square `(tauSeq k + dSeq k)^2` for ALL `k ≥ 1`! -/
theorem fenwickUQLap_spanning_tree_square {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] (k : Nat) (hk : 1 ≤ k) :
    det (minor (fenwickUQLap (R := Int) (k + 1)) ⟨0, Nat.zero_lt_succ _⟩ ⟨0, Nat.zero_lt_succ _⟩) =
    (tauSeq k + dSeq k) * (tauSeq k + dSeq k) := by
  sorry

/-- Theorem 6b (Binary Heap `H_k` Characteristic Polynomial Factorization over ANY `CRing R`, `∀ k ≥ 1`): -/
theorem inOrderHeap_charpoly_factorization {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] (x : R) (k : Nat) (hk : 1 ≤ k) :
    det (inOrderHeapChar (R := R) k x) = chebT x k *ᵣ heapR x (k - 1) := by
  sorry

/-- Witness 6: Exact 1/4-dyadic inverse `A(G_2) * J_2 = 4 * I_5` and `A(G_3) * J_3 = 4 * I_9`. -/
theorem witness_dyadic_inv_k2 {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] {R : Type} [CRing R] :
    matMul (fenwickUQAdj (R := Int) 2 1) (fenwickUQDyadicInv 2 (by omega)) =
    fun i j => if i = j then (4 : Int) else 0 := by
  sorry

/-- Counterexample 3 (query/update weights `1`/`2` instead of equal weights): giving query edges `(i, i - lowbit i)` weight `1` and update edges `(i, i + lowbit i)` weight `2` gives `det = -24 ≠ -4` already at `k = 2` (`5 × 5`)! -/
theorem sharpness_asymmetric_weights_k2 :
    let st1 : PortalState Int := ⟨0, -4, -1, 0, 2, 2⟩
    let st1L := stepPerturb st1 0 1 1 0
    let st1R := stepPerturb st1 0 2 2 0
    (stepGlue st1L st1R 0).d0 = -24 ∧ (stepGlue st1L st1R 0).d0 ≠ -4 := by
  sorry

end FenwickPortalParitySchurChallenge
