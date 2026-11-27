import DyadicBallContractionCompiler

namespace DyadicBallContractionCompilerChallenge

open DyadicCompiler

theorem checkParamTree_sound (e : Expr) (P B0 : DyadicBall) (qNum qExp : Nat) (t : ParamTree)
    (hchk : checkParamTree e P B0 qNum qExp t = true)
    (p : ExactQ) (hp : P.contains p) :
    IsSelfMappedLipschitz e p B0 B0 (ExactQ.ofDyadic (qNum : Int) qExp) :=
  _root_.DyadicCompiler.checkParamTree_sound e P B0 qNum qExp t hchk p hp

theorem contraction_fixed_point_unique (cert : ParamContractionCert)
    (hchk : checkParamContraction cert = true)
    (p : ExactQ) (hp : cert.p0.contains p)
    (xs ys fxs fys : ExactQ) (hxs : cert.b0.contains xs) (hys : cert.b0.contains ys)
    (hfx : evalQ cert.expr p xs = some fxs) (heqx : fxs.equiv xs)
    (hfy : evalQ cert.expr p ys = some fys) (heqy : fys.equiv ys) :
    xs.equiv ys :=
  _root_.DyadicCompiler.contraction_fixed_point_unique cert hchk p hp xs ys fxs fys hxs hys hfx heqx hfy heqy

theorem bring_quintic_residual_decay (p : ExactQ) (hp : certBring.p0.contains p)
    (x0 x1 : ExactQ) (hx0 : certBring.b0.contains x0) (hx1 : evalQ exprBringNewton p x0 = some x1) :
    ∀ n : Nat, ∀ xn,
      iterQ exprBringNewton p n x0 = some xn →
      (bringPoly p xn).abs.le ((ExactQ.ofInt 7).mul (((ExactQ.ofDyadic 7 3).pow n).mul (x1.dist x0))) :=
  _root_.DyadicCompiler.bring_quintic_residual_decay p hp x0 x1 hx0 hx1

theorem bring_direct_oscillatory_contraction (x0 y0 : ExactQ)
    (hx0 : certBringAlt.b0.contains x0) (hy0 : certBringAlt.b0.contains y0) :
    (∀ n : Nat, ∃ xn, iterQ exprBringDirect (ExactQ.ofInt 0) n x0 = some xn ∧ certBringAlt.b0.contains xn) ∧
    (∀ n : Nat, ∀ xn yn,
      iterQ exprBringDirect (ExactQ.ofInt 0) n x0 = some xn →
      iterQ exprBringDirect (ExactQ.ofInt 0) n y0 = some yn →
      (xn.dist yn).le (((ExactQ.ofDyadic 63 6).pow n).mul (x0.dist y0))) :=
  _root_.DyadicCompiler.bring_direct_oscillatory_contraction x0 y0 hx0 hy0

theorem certHalley_valid : checkParamContraction certHalley = true :=
  _root_.DyadicCompiler.certHalley_valid

theorem certBringAlt_valid : checkParamContraction certBringAlt = true :=
  _root_.DyadicCompiler.certBringAlt_valid

theorem mutation_reject_halley_no_subdivision :
    checkParamContraction { certHalley with tree := .pleaf (.leaf 14 true) } = false :=
  _root_.DyadicCompiler.mutation_reject_halley_no_subdivision

theorem mutation_reject_bring_alt_expanding_region :
    checkParamContraction { certBringAlt with b0 := ⟨17, 5, 1⟩ } = false :=
  _root_.DyadicCompiler.mutation_reject_bring_alt_expanding_region

end DyadicBallContractionCompilerChallenge
