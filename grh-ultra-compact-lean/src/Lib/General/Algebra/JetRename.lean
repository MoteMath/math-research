import Lib.General.Algebra.JetChainRule
import Lib.Weil.Fock.EntireTheta
lemma jet_rename {σ τ R} (e : σ ↪ τ) [CommRing R] {P Q} (h : .rename e P = Q) F : jet R Q (F.rename e) = jet R P F := h ▸ P.induction_on' (by
 simp [MvPolynomial.rename_monomial, ← Finsupp.embDomain_eq_mapDomain, Finsupp.prod]) (by aesop)
