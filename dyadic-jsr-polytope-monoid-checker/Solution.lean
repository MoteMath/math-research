import DyadicJsrPolytopeMonoidChecker

namespace DyadicJsrPolytopeMonoidCheckerChallenge

open DyadicMonoidEngine CertifiedApplications

theorem switched_polytope_sound {d m Q K : Nat} (cert : SwitchedPolytopeCert d m Q K)
    (hchk : checkSwitchedPolytopeCert cert = true)
    (q0 qn : Fin Q) (w : List (Fin m)) (hrun : runDFA cert.step q0 w = some qn)
    (p : Fin d) :
    Dyad.le (dyadicRowAbsSum (dyadicWordProd (fun b => scaleDyadicMat cert.scaleShift (cert.A b)) w) p)
              (Dyad.mul (Dyad.ofNat cert.C_const) (Dyad.pow ⟨(cert.lamNum : Int), cert.lamShift⟩ w.length)) :=
  _root_.DyadicMonoidEngine.switched_polytope_sound cert hchk q0 qn w hrun p

theorem convex_hull_infinite_alphabet_sound {d m K : Nat} (cert : SwitchedPolytopeCert d m 1 K)
    (hchk : checkSwitchedPolytopeCert cert = true)
    (hall : ∀ b : Fin m, cert.step 0 b = some 0)
    (ws : List (DyadicConvexStep m)) (hvals : ∀ st ∈ ws, st.valid) (p : Fin d) :
    Dyad.le (dyadicRowAbsSum (convexDyadicProd cert.scaleShift cert.A ws) p)
              (Dyad.mul (Dyad.ofNat cert.C_const) (Dyad.pow ⟨(cert.lamNum : Int), cert.lamShift⟩ ws.length)) :=
  _root_.DyadicMonoidEngine.convex_hull_infinite_alphabet_sound cert hchk hall ws hvals p

theorem periodic_eigen_sound {d m : Nat} (cert : PeriodicEigenCert d m)
    (hchk : checkPeriodicEigenCert cert = true) (k : Nat) :
    ∃ p : Fin d,
      Dyad.le (Dyad.pow ⟨iabs cert.eig, cert.scaleShift * cert.word.length⟩ k)
                (dyadicRowAbsSum
                  (dyadicWordProd (fun b => scaleDyadicMat cert.scaleShift (cert.A b))
                                  (repeatWord cert.word k)) p) :=
  _root_.DyadicMonoidEngine.periodic_eigen_sound cert hchk k

theorem thm1_convex_hull_contraction (ws : List (DyadicConvexStep 2))
    (hvals : ∀ st ∈ ws, st.valid) (p : Fin 2) :
    Dyad.le (dyadicRowAbsSum (convexDyadicProd 2 thm1_A ws) p)
              (Dyad.mul (Dyad.ofNat 4) (Dyad.pow ⟨15, 4⟩ ws.length)) :=
  _root_.CertifiedApplications.thm1_convex_hull_contraction ws hvals p

theorem thm1_sharpness_unbounded (B : Nat) :
    ∃ (k : Nat) (p : Fin 2),
      Dyad.lt (Dyad.ofNat B)
                (dyadicRowAbsSum
                  (dyadicWordProd (fun b => scaleDyadicMat 2 (thm1_sharp_A b))
                                  (repeatWord cert1_sharp.word k)) p) :=
  _root_.CertifiedApplications.thm1_sharpness_unbounded B

theorem thm3_signed_cone_subradius (w : List (Fin 2)) :
    Dyad.le
      (Dyad.mul ⟨1, 0⟩ (Dyad.pow ⟨5, 2⟩ w.length))
      (dyadicVecDot (fun i => Dyad.ofInt (cert3.u i))
        (dyadicMatVec (dyadicWordProd (fun b => scaleDyadicMat 2 (thm3_A b)) w)
                      (fun j => Dyad.ofInt (cert3.x0 j)))) :=
  _root_.CertifiedApplications.thm3_signed_cone_subradius w

theorem thm4_unconstrained_lower (k : Nat) :
    ∃ p : Fin 2,
      Dyad.le (Dyad.pow ⟨5, 2⟩ k)
                (dyadicRowAbsSum
                  (dyadicWordProd (fun b => scaleDyadicMat 2 (thm4_A b))
                                  (repeatWord cert4_explode.word k)) p) :=
  _root_.CertifiedApplications.thm4_unconstrained_lower k

theorem mut8_bad_naf_dfa_rejected : checkSwitchedPolytopeCert bad_cert4_unconstrained_dfa = false :=
  _root_.CertifiedApplications.mut8_bad_naf_dfa_rejected

end DyadicJsrPolytopeMonoidCheckerChallenge
