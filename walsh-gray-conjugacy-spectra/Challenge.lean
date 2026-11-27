import WalshGrayConjugacySpectra.Defs

namespace WalshGrayConjugacySpectraChallenge

open SiliconSpectral

/-- Contragredient Law: W_k P_A = P_{A^{-T}} W_k (exact over ℤ, ∀ k). -/
theorem walsh_perm_conj {k : Nat} (A : LinIso k) :
    mulMat (walshMat k) (permMat A.fwd) =
    mulMat (permMat A.adjInv) (walshMat k) := by
  sorry

/-- Finite-to-Infinite Periodicity Lift: if Δ(A)^d = id on V_k, then (W_k P_A)^{2d} = 2^{kd} I. -/
theorem spectral_period_lift {k : Nat} (A : LinIso k) (d : Nat)
    (hord : ∀ x : Vec k, iterFn A.defect.fwd d x = x) :
    matPow (mulMat (walshMat k) (permMat A.fwd)) (2 * d) =
    smulMat ((2 : Int) ^ (k * d)) (idMat k) := by
  sorry

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
    traceMat PiMinus = s * (2 : Int) ^ (2 * r) - traceMat M := by
  sorry

/-- Pillar 3c: Exact Even-Power Necklace Trace Formula! For any HyperplaneRotCert k n r A (n ≥ 1) and any m ∈ ℕ, letting g = gcd(m, n) and q = n / g: Tr((W_k P_A)^{2m}) = 2^{km + r + (if q % 2 = 0 then g else g - 1)}. -/
theorem hyperplane_even_trace_lift {k n r : Nat} {A : LinIso k}
    (C : HyperplaneRotCert k n r A) (m : Nat) :
    let g := Nat.gcd m n
    let q := n / g
    traceMat (matPow (mulMat (walshMat k) (permMat A.fwd)) (2 * m)) =
    (2 : Int) ^ (k * m + r + (if q % 2 = 0 then g else g - 1)) := by
  sorry

/-- THEOREM A4 (Gray–Walsh Mod-4 Spectral Symmetry & Odd-Trace Vanishing): ∀ r ∈ ℕ, at width k = 4r + 1, the explicit Weyl–Heisenberg operator U = D_{G_k b} T_b (with alternating b) anticommutes with W_k P_{G_k}, forcing Tr((W_k P_{G_k})^{2m+1}) = 0 ∀ m ∈ ℕ and E_λ ≅ E_{-λ}. -/
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
      applyVec M (applyVec U v) = (fun x => (-lam) * applyVec U v x)) := by
  sorry

/-- THEOREM C1 (Bit-Reversal Spectral Parity Dichotomy): (W_k P_{R_k})^2 = 2^k I ∀ k, with: - Odd width k = 2r + 1: balanced (Tr = 0 via Weyl–Heisenberg anticommutator); - Even width k = 2r (r ≥ 1): asymmetric by 2^r, with exact integer projector traces giving m_+ = 2^{2r-1} + 2^{r-1} and m_- = 2^{2r-1} - 2^{r-1}. -/
theorem walsh_bitrev_parity_dichotomy_odd (r : Nat) :
    let k := 2 * r + 1
    matPow (mulMat (walshMat k) (permMat (bitrevIso k).fwd)) 2 =
      smulMat ((2 : Int) ^ k) (idMat k) ∧
    traceMat (mulMat (walshMat k) (permMat (bitrevIso k).fwd)) = 0 := by
  sorry

/-- THEOREM D1 (Gray ∘ Butterfly-Rotation 2k-Cycle Periodicity): ∀ k ≥ 2, (W_k P_{G_k C_k})^{2k} = 2^{k^2} I_{2^k}. -/
theorem walsh_gray_rot_period (k : Nat) (hk : 2 ≤ k) :
    matPow (mulMat (walshMat k) (permMat (grayRotIso k).fwd)) (2 * k) =
    smulMat ((2 : Int) ^ (k * k)) (idMat k) := by
  sorry

theorem sharp_nonlinear_inc2_not_scaled_perm :
    ∀ f : Vec 2 -> Vec 2,
      matPow (mulMat (walshMat 2) (permMat inc2Vec)) 2 ≠ smulMat 4 (permMat f) := by
  sorry

end WalshGrayConjugacySpectraChallenge
