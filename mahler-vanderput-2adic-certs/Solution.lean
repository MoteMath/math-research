import MahlerVanderput2adicCerts

namespace MahlerVanderput2adicCertsChallenge

open Z2CertEngine

theorem vdp_reconstruct (f : Nat → Int) (w : Nat) (x : BitVec w) :
    vdpEval f w x = f x.toNat :=
  _root_.Z2CertEngine.vdp_reconstruct f w x

theorem z2_density_identity {F G : Z2 → Z2}
    (hF : IsContinuous F) (hG : IsContinuous G)
    (hNat : ∀ n : Nat, F (Z2.ofNat n) = G (Z2.ofNat n)) :
    ∀ x : Z2, F x = G x :=
  _root_.Z2CertEngine.z2_density_identity hF hG hNat

theorem q_gray_alternating_duality_even (q : Int) (hq : (2 : Int) ∣ q) :
    ∀ x : Z2, thetaZ2 q hq ((2 * x) ^^^ x) = -(Z2.ofInt (q - 1)) * phiZ2 q hq x :=
  _root_.Z2CertEngine.q_gray_alternating_duality_even q hq

theorem theta2_bitwise_inverse_Z2 :
    ∀ x : Z2, thetaZ2 2 (by decide) ((2 * (-x)) ^^^ (-x)) = x :=
  _root_.Z2CertEngine.theta2_bitwise_inverse_Z2

theorem triadic_holder_2_3_sharp {F : Z2 → Z2} {μ : Nat → Nat}
    (hMod : HasModulus μ F) (hExt : ∀ n, F (Z2.ofNat n) = Z2.ofInt (dotVec u_tri (g_tri n))) (k : Nat) :
    μ (3 * k) ≤ 2 * k :=
  _root_.Z2CertEngine.triadic_holder_2_3_sharp hMod hExt k

theorem shear_carry_1lipschitz_sharp {F : Z2 → Z2} {μ : Nat → Nat}
    (hMod : HasModulus μ F) (hExt : ∀ n, F (Z2.ofNat n) = Z2.ofInt (dotVec u_sc (g_sc n))) (k : Nat) :
    μ (2 * k) ≤ 2 * k :=
  _root_.Z2CertEngine.shear_carry_1lipschitz_sharp hMod hExt k

theorem exp2c_neg_one_inv (c : Int) :
    exp2cZ2 c (-1) * Z2.ofInt (1 + 2 * c) = 1 :=
  _root_.Z2CertEngine.exp2c_neg_one_inv c

theorem nonvacuity_all_compilers :
    (∃ c : LatticeContractCert 3 3 3 2, c.Valid (vdpCoeffVec g_tri 1)) ∧
    (∃ c : LatticeContractCert 2 2 1 1, c.Valid (vdpCoeffVec g_sc 1)) ∧
    (∃ sc : SharpHolderCert cert_tri u_tri, sc.Valid) ∧
    (∃ sc : SharpHolderCert cert_sc u_sc, sc.Valid) ∧
    (∃ kc : KernelIdCert 4 2, kc.Valid v0_gray4) :=
  _root_.Z2CertEngine.nonvacuity_all_compilers

end MahlerVanderput2adicCertsChallenge
