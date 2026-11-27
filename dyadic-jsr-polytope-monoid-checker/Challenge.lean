import DyadicJsrPolytopeMonoidChecker.Defs

namespace DyadicJsrPolytopeMonoidCheckerChallenge

open DyadicMonoidEngine CertifiedApplications

/-- **MAIN SOUNDNESS META-THEOREM 1 (DFA-Switched Exact Dyadic Operator-Norm Contraction):** If `checkSwitchedPolytopeCert cert = true`, then for EVERY word `w` of arbitrary length accepted by the DFA (`runDFA cert.step q0 w = some qn`) and EVERY row `p : Fin d`, the exact `Z[1/2]` row `ℓ_1` norm of `dyadicWordProd M w` satisfies: `‖(dyadicWordProd M w)_p‖_1 ≤_{Z[1/2]} C_const * (lamNum / 2^lamShift)^/w/`. -/
theorem switched_polytope_sound {d m Q K : Nat} (cert : SwitchedPolytopeCert d m Q K)
    (hchk : checkSwitchedPolytopeCert cert = true)
    (q0 qn : Fin Q) (w : List (Fin m)) (hrun : runDFA cert.step q0 w = some qn)
    (p : Fin d) :
    Dyad.le (dyadicRowAbsSum (dyadicWordProd (fun b => scaleDyadicMat cert.scaleShift (cert.A b)) w) p)
              (Dyad.mul (Dyad.ofNat cert.C_const) (Dyad.pow ⟨(cert.lamNum : Int), cert.lamShift⟩ w.length)) := by
  sorry

/-- **MAIN SOUNDNESS META-THEOREM 2 (Infinite-Alphabet Dyadic Convex-Hull Contraction):** One finite polytope certificate checked by `decide` on `m` vertex matrices AUTOMATICALLY certifies uniform exponential contraction for ALL arbitrary-length, time-varying products drawn from the ENTIRE INFINITE dyadic convex hull `conv_{Z[1/2]}(M_0, ..., M_{m-1})`! -/
theorem convex_hull_infinite_alphabet_sound {d m K : Nat} (cert : SwitchedPolytopeCert d m 1 K)
    (hchk : checkSwitchedPolytopeCert cert = true)
    (hall : ∀ b : Fin m, cert.step 0 b = some 0)
    (ws : List (DyadicConvexStep m)) (hvals : ∀ st ∈ ws, st.valid) (p : Fin d) :
    Dyad.le (dyadicRowAbsSum (convexDyadicProd cert.scaleShift cert.A ws) p)
              (Dyad.mul (Dyad.ofNat cert.C_const) (Dyad.pow ⟨(cert.lamNum : Int), cert.lamShift⟩ ws.length)) := by
  sorry

/-- **MAIN SOUNDNESS META-THEOREM 4 (Exact Periodic Eigen-Witness JSR Lower Bound):** If `checkPeriodicEigenCert cert = true`, then for EVERY `k : Nat`, the `k`-fold repeated word `w_0^k` (length `/w_0/ * k`) attains exact `ℓ_∞` operator norm at least `(/eig/ / 2^(s * /w_0/))^k`! -/
theorem periodic_eigen_sound {d m : Nat} (cert : PeriodicEigenCert d m)
    (hchk : checkPeriodicEigenCert cert = true) (k : Nat) :
    ∃ p : Fin d,
      Dyad.le (Dyad.pow ⟨iabs cert.eig, cert.scaleShift * cert.word.length⟩ k)
                (dyadicRowAbsSum
                  (dyadicWordProd (fun b => scaleDyadicMat cert.scaleShift (cert.A b))
                                  (repeatWord cert.word k)) p) := by
  sorry

/-- **THEOREM 1C (Infinite-Alphabet Dyadic Convex-Hull Contraction):** Every arbitrary-length sequence of time-varying dyadic convex combinations of `M0, M1` has every row absolute sum at most `4 * (15/16)^n` (n = number of steps; an upper bound only). -/
theorem thm1_convex_hull_contraction (ws : List (DyadicConvexStep 2))
    (hvals : ∀ st ∈ ws, st.valid) (p : Fin 2) :
    Dyad.le (dyadicRowAbsSum (convexDyadicProd 2 thm1_A ws) p)
              (Dyad.mul (Dyad.ofNat 4) (Dyad.pow ⟨15, 4⟩ ws.length)) := by
  sorry

theorem thm1_sharpness_unbounded (B : Nat) :
    ∃ (k : Nat) (p : Fin 2),
      Dyad.lt (Dyad.ofNat B)
                (dyadicRowAbsSum
                  (dyadicWordProd (fun b => scaleDyadicMat 2 (thm1_sharp_A b))
                                  (repeatWord cert1_sharp.word k)) p) := by
  sorry

/-- **THEOREM 3A (Strict Positivity & Exponential Subradius `≥ 5/4` for Signed-Entry Matrices):** -/
theorem thm3_signed_cone_subradius (w : List (Fin 2)) :
    Dyad.le
      (Dyad.mul ⟨1, 0⟩ (Dyad.pow ⟨5, 2⟩ w.length))
      (dyadicVecDot (fun i => Dyad.ofInt (cert3.u i))
        (dyadicMatVec (dyadicWordProd (fun b => scaleDyadicMat 2 (thm3_A b)) w)
                      (fun j => Dyad.ofInt (cert3.x0 j)))) := by
  sorry

theorem thm4_unconstrained_lower (k : Nat) :
    ∃ p : Fin 2,
      Dyad.le (Dyad.pow ⟨5, 2⟩ k)
                (dyadicRowAbsSum
                  (dyadicWordProd (fun b => scaleDyadicMat 2 (thm4_A b))
                                  (repeatWord cert4_explode.word k)) p) := by
  sorry

theorem mut8_bad_naf_dfa_rejected : checkSwitchedPolytopeCert bad_cert4_unconstrained_dfa = false := by
  sorry

end DyadicJsrPolytopeMonoidCheckerChallenge
