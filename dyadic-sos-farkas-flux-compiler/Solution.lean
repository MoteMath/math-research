/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DyadicSosFarkasFluxCompiler

/-!
# Verified Solutions (`dyadic-sos-farkas-flux-compiler`)
-/

namespace DyadicSosFarkasFluxCompilerChallenge

open DyadicSOS

theorem farkasSOS_sound (target : DyadicPoly) (ineqs eqs : List DyadicPoly) (cert : FarkasSOSCert)
    (hchk : FarkasSOS.check target ineqs eqs cert = true)
    (env : Nat → DyadicSOS.Dyadic)
    (hineq : ∀ g ∈ ineqs, Dyadic.Nonneg (DyadicPoly.eval g env))
    (heq : ∀ h ∈ eqs, Dyadic.IsZero (DyadicPoly.eval h env)) :
    Dyadic.Nonneg (DyadicPoly.eval target env) :=
  DyadicSOS.FarkasSOS.sound target ineqs eqs cert hchk env hineq heq

theorem cyclic_flux_sound_int (paramCount : Nat) (stencil : DyadicPoly)
    (localIneqs localEqs : List DyadicPoly) (cert : CyclicFluxCert)
    (hchk : checkCyclicFlux paramCount stencil localIneqs localEqs cert = true)
    (n : Nat) (hn : 1 ≤ n) (params x : Nat → Int)
    (hineq : ∀ i, i < n → ∀ g ∈ localIneqs,
      0 ≤ Poly.evalInt g.poly (fun v => if v < paramCount then params v else x ((i + (v - paramCount)) % n)))
    (heq : ∀ i, i < n → ∀ h ∈ localEqs,
      Poly.evalInt h.poly (fun v => if v < paramCount then params v else x ((i + (v - paramCount)) % n)) = 0) :
    0 ≤ sumInt (fun i => Poly.evalInt stencil.poly
      (fun v => if v < paramCount then params v else x ((i + (v - paramCount)) % n))) n :=
  DyadicSOS.cyclic_flux_sound_int paramCount stencil localIneqs localEqs cert hchk n hn params x hineq heq

theorem thm1_asym_skew_quartic_cyclic_int (n : Nat) (hn : 1 ≤ n) (x : Nat → Int) :
    0 ≤ sumInt (asymSkewTerm x n) n :=
  DyadicSOS.thm1_asym_skew_quartic_cyclic_int n hn x

theorem thm3b_hypercube_asym_3pattern (n : Nat) (hn : 1 ≤ n) (x : Nat → DyadicSOS.Dyadic)
    (h01 : ∀ k, Dyadic.Nonneg (x k) ∧ Dyadic.Le (x k) Dyadic.one) :
    Dyadic.Nonneg (sumDyadic (fun i => DyadicPoly.eval thm3b_stencil (cyclicWin 0 n x x i)) n) :=
  DyadicSOS.thm3b_hypercube_asym_3pattern n hn x h01

theorem thm4_boolean_frustrated_triangle (n : Nat) (hn : 1 ≤ n) (b : Nat → Bool) :
    0 ≤ sumInt (frustratedTriTerm b n) n :=
  DyadicSOS.thm4_boolean_frustrated_triangle n hn b

theorem thm5a_parametric_biharmonic_cyclic_int (n : Nat) (hn : 1 ≤ n) (t : Int) (x : Nat → Int) :
    0 ≤ sumInt (biharmonicParamTerm t x n) n :=
  DyadicSOS.thm5a_parametric_biharmonic_cyclic_int n hn t x

theorem thm5b_open_biharmonic_stabilized_int (n : Nat) (x : Nat → Int) :
    0 ≤ 2 * (x 0 ^ 2 + x 1 ^ 2) + sumInt (openBiharmonicTerm x) n + 2 * (x n ^ 2 + x (n + 1) ^ 2) :=
  DyadicSOS.thm5b_open_biharmonic_stabilized_int n x

theorem thm6_nonlinear_farkas_refutation (x y : DyadicSOS.Dyadic) :
    ¬ (Dyadic.Nonneg (DyadicPoly.eval thm6_g0 (fun i => if i = 0 then x else y)) ∧
       Dyadic.Nonneg (DyadicPoly.eval thm6_g1 (fun i => if i = 0 then x else y))) :=
  DyadicSOS.thm6_nonlinear_farkas_refutation x y

end DyadicSosFarkasFluxCompilerChallenge
