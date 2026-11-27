import ShellWalshNestedJoinSpectra

namespace ShellWalshNestedJoinSpectraChallenge

open ShellWalshEngine

theorem det_mul {n : Nat} (A B : Mat n) : det (matMul A B) = det A * det B :=
  _root_.ShellWalshEngine.det_mul A B

theorem orthogonal_eigenbasis_kirchhoff {m : Nat} (L Q : Mat (m + 1)) (d lam : Fin (m + 1) -> Int)
    (hrow : ∀ i, sumFin (m + 1) (fun j => L i j) = 0)
    (hcol : ∀ j, sumFin (m + 1) (fun i => L i j) = 0)
    (horth : matMul (matTranspose Q) Q = matDiag d)
    (hd : ∀ i, d i ≠ 0)
    (hcol0 : ∀ i, Q i ⟨0, Nat.zero_lt_succ m⟩ = 1)
    (hlam0 : lam ⟨0, Nat.zero_lt_succ m⟩ = 0)
    (hdiag : matMul L Q = matMul Q (matDiag lam)) :
    ((m + 1 : Nat) : Int) * det (minor00 L) = prodFin m (fun j => lam j.succ) :=
  _root_.ShellWalshEngine.orthogonal_eigenbasis_kirchhoff L Q d lam hrow hcol horth hd hcol0 hlam0 hdiag

theorem shellLaplacian_kirchhoff (k : Nat) (c : Nat -> Int) (phi : Nat -> Nat -> Int) :
    ((2 ^ k : Nat) : Int) *
      det (minor00 (cast (congrArg Mat (pow2_eq_pred_succ k)) (shellLaplacian k c phi))) =
    prodFin (2 ^ k - 1) (fun j => shellEig k c phi ⟨j.val + 1, by have := j.isLt; have := Nat.two_pow_pos k; omega⟩) :=
  _root_.ShellWalshEngine.shellLaplacian_kirchhoff k c phi

theorem carryXorLaplacian_kirchhoff (k : Nat) (h : Nat -> Nat -> Int) :
    ((2 ^ k : Nat) : Int) *
      det (minor00 (cast (congrArg Mat (pow2_eq_pred_succ k)) (carryXorLaplacian k h))) =
    prodFin (2 ^ k - 1)
      (fun j => shellEig k (carryXorC h) (carryXorPhi h)
        ⟨j.val + 1, by have := j.isLt; have := Nat.two_pow_pos k; omega⟩) :=
  _root_.ShellWalshEngine.carryXorLaplacian_kirchhoff k h

theorem dyadic_spanning_trees (k : Nat) (hk : 1 ≤ k) :
    det (minor00 (cast (congrArg Mat (pow2_eq_pred_succ k)) (dyadicLaplacian k))) =
    dyadicTau k :=
  _root_.ShellWalshEngine.dyadic_spanning_trees k hk

theorem evenSum_kirchhoff (k : Nat) :
    ((2 ^ k : Nat) : Int) *
      det (minor00 (cast (congrArg Mat (pow2_eq_pred_succ k)) (evenSumLaplacian k))) =
    prodFin (2 ^ k - 1)
      (fun j => shellEig k (carryXorC evenSumH) (carryXorPhi evenSumH)
        ⟨j.val + 1, by have := j.isLt; have := Nat.two_pow_pos k; omega⟩) :=
  _root_.ShellWalshEngine.evenSum_kirchhoff k

theorem sharpness_c3_charpoly (x : Int) :
    det (matSub (matScale x (matId 4)) shifted3Laplacian) =
    x * (x - 2) * (x * x - 4 * x + 2) :=
  _root_.ShellWalshEngine.sharpness_c3_charpoly x

theorem witness_nonvacuous_engine :
    Nonempty { p : (k : Nat) × (Fin (2 ^ k) -> Int) × (Fin (2 ^ k) -> Int) //
      p.1 = 2 ∧
      matMul (matTranspose (shellQ p.1)) (shellQ p.1) = matDiag p.2.1 ∧
      (∀ i, p.2.1 i ≠ 0) ∧
      matMul (dyadicLaplacian p.1) (shellQ p.1) = matMul (shellQ p.1) (matDiag p.2.2) } :=
  _root_.ShellWalshEngine.witness_nonvacuous_engine

end ShellWalshNestedJoinSpectraChallenge
