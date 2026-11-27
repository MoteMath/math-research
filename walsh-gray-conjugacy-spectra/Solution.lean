import WalshGrayConjugacySpectra

namespace WalshGrayConjugacySpectraChallenge

open SiliconSpectral

theorem walsh_perm_conj {k : Nat} (A : LinIso k) :
    mulMat (walshMat k) (permMat A.fwd) =
    mulMat (permMat A.adjInv) (walshMat k) :=
  _root_.SiliconSpectral.walsh_perm_conj A

theorem spectral_period_lift {k : Nat} (A : LinIso k) (d : Nat)
    (hord : ∀ x : Vec k, iterFn A.defect.fwd d x = x) :
    matPow (mulMat (walshMat k) (permMat A.fwd)) (2 * d) =
    smulMat ((2 : Int) ^ (k * d)) (idMat k) :=
  _root_.SiliconSpectral.spectral_period_lift A d hord

theorem even_symmetric_projectors {r : Nat} (A : LinIso (2 * r))
    (hsym : ∀ x, A.fwd x = A.adj x) :
    let M := mulMat (walshMat (2 * r)) (permMat A.fwd)
    let s : Int := (2 : Int) ^ r
    let PiPlus := addMat (smulMat s (idMat (2 * r))) M
    let PiMinus := subMat (smulMat s (idMat (2 * r))) M
    mulMat PiPlus PiMinus = zeroMat (2 * r) ∧
    mulMat M PiPlus = smulMat s PiPlus ∧
    mulMat M PiMinus = smulMat (-s) PiMinus ∧
    traceMat PiPlus = s * (2 : Int) ^ (2 * r) + traceMat M ∧
    traceMat PiMinus = s * (2 : Int) ^ (2 * r) - traceMat M :=
  _root_.SiliconSpectral.even_symmetric_projectors A hsym

theorem hyperplane_even_trace_lift {k n r : Nat} {A : LinIso k}
    (C : HyperplaneRotCert k n r A) (m : Nat) :
    let g := Nat.gcd m n
    let q := n / g
    traceMat (matPow (mulMat (walshMat k) (permMat A.fwd)) (2 * m)) =
    (2 : Int) ^ (k * m + r + (if q % 2 = 0 then g else g - 1)) :=
  _root_.SiliconSpectral.hyperplane_even_trace_lift C m

theorem walsh_gray_mod4_antisym (r : Nat) :
    let k := 4 * r + 1
    let b := altVec k
    let U := weylOp ((grayIso k).fwd b) b
    let M := mulMat (walshMat k) (permMat (grayIso k).fwd)
    mulMat U U = negMat (idMat k) ∧
    mulMat U M = negMat (mulMat M U) ∧
    (∀ m : Nat, traceMat (matPow M (2 * m + 1)) = 0) ∧
    (∀ (lam : Int) (v : Vec k -> Int),
      applyVec M v = (fun x => lam * v x) ->
      applyVec M (applyVec U v) = (fun x => (-lam) * applyVec U v x)) :=
  _root_.SiliconSpectral.walsh_gray_mod4_antisym r

theorem walsh_bitrev_parity_dichotomy_odd (r : Nat) :
    let k := 2 * r + 1
    matPow (mulMat (walshMat k) (permMat (bitrevIso k).fwd)) 2 =
      smulMat ((2 : Int) ^ k) (idMat k) ∧
    traceMat (mulMat (walshMat k) (permMat (bitrevIso k).fwd)) = 0 :=
  _root_.SiliconSpectral.walsh_bitrev_parity_dichotomy_odd r

theorem walsh_gray_rot_period (k : Nat) (hk : 2 ≤ k) :
    matPow (mulMat (walshMat k) (permMat (grayRotIso k).fwd)) (2 * k) =
    smulMat ((2 : Int) ^ (k * k)) (idMat k) :=
  _root_.SiliconSpectral.walsh_gray_rot_period k hk

theorem sharp_nonlinear_inc2_not_scaled_perm :
    ∀ f : Vec 2 -> Vec 2,
      matPow (mulMat (walshMat 2) (permMat inc2Vec)) 2 ≠ smulMat 4 (permMat f) :=
  _root_.SiliconSpectral.sharp_nonlinear_inc2_not_scaled_perm

end WalshGrayConjugacySpectraChallenge
