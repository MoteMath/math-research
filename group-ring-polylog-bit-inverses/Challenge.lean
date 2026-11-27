import GroupRingPolylogBitInverses.Defs

namespace GroupRingPolylogBitInversesChallenge

open SpecMat13

/-- **Core Engine Theorem 3 (Exact Parseval / Plancherel Duality):** `∑_ω wht(f)(ω) * wht(g)(ω) = 2^k * ∑_x f(x) * g(x)`. -/
theorem parseval_plancherel : {k : Nat} → (f g : GR k) →
    sumBVec (fun ω => wht f ω * wht g ω) = (2 : Int) ^ k * sumBVec (fun x => f x * g x) := by
  sorry

/-- **Obstruction Theorem 1 (Pure-Silicon Higman Rigidity):** In `Z[F_2^k]` for ALL `k ≥ 0`, every exact `Z`-unit (`f * g = δ_0`) satisfies `∑_x f(x)^2 = 1`, i.e., `f = ± δ_a` (no non-trivial `Z`-units exist). -/
theorem higman_rigidity {k : Nat} {f g : GR k}
    (hinv : ∀ x, conv f g x = scaleDelta 1 x) : sumSq f = 1 := by
  sorry

/-- **Obstruction Theorem 5 (Pure `{0, 1}` Self-Inversion Impossibility):** No non-negative binary element `f : BVec k → {0, 1}` with `/supp(f)/ ≥ 2` can satisfy `f * f = c • δ_0` for ANY integer `c`. -/
theorem binary01_no_self_inverse {k : Nat} {f : GR k} {c : Int}
    (hb : IsBinary01 f) (hself : ∀ x, conv f f x = scaleDelta c x) :
    suppCount f ≤ 1 := by
  sorry

/-- **Theorem A.1 (Dual Multiplexer Tree WHT Law):** Every single Walsh coefficient of `treeElem d` is `2^d * spectralSign d ω ∈ {-2^d, +2^d}`. -/
theorem treeElem_wht : (d : Nat) → (ω : BVec (treeWidth d)) →
    wht (treeElem d) ω = (2 : Int) ^ d * spectralSign d ω := by
  sorry

theorem treeElem_polylog_identity (d : Nat) :
    4 * suppCount (treeElem d) = (treeWidth d + 2) ^ 2 := by
  sorry

theorem asymTree_non_self_inverse (d : Nat) :
    asymTreeP d ≠ asymTreeQ d ∧ (∃ x, asymTreeP d x ≠ - asymTreeQ d x) := by
  sorry

/-- **Sharpness 2 (`k = 3` Dyadic Inversion Impossibility — Exact Gap at `k = 3`):** NO full-affine-spanning ternary element on `F_2^3` is dyadically invertible (`f * g = 2^m • δ_0`). Combined with Theorem C (`∀ k ≥ 2, k ≠ 3`) and `baseA3` (`k = 3, D = 3`), this proves the `k ≠ 3` exclusion in Theorem C is 100% sharp. -/
theorem k3_no_spanning_ternary_dyadic {m : Nat} {f g : GR 3}
    (ht : IsTernary f) (hspan : AffineSpan f)
    (hinv : ∀ x, conv f g x = scaleDelta ((2 : Int) ^ m) x) : False := by
  sorry

theorem unshiftedLift_breaks_ternary :
    ¬ IsTernary (unshiftedLift (treeElem 1) (treeElem 1)) := by
  sorry

end GroupRingPolylogBitInversesChallenge
