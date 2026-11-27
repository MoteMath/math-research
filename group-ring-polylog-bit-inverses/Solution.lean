import GroupRingPolylogBitInverses

namespace GroupRingPolylogBitInversesChallenge

open SpecMat13

theorem parseval_plancherel : {k : Nat} → (f g : GR k) →
    sumBVec (fun ω => wht f ω * wht g ω) = (2 : Int) ^ k * sumBVec (fun x => f x * g x) :=
  _root_.SpecMat13.parseval_plancherel

theorem higman_rigidity {k : Nat} {f g : GR k}
    (hinv : ∀ x, conv f g x = scaleDelta 1 x) : sumSq f = 1 :=
  _root_.SpecMat13.higman_rigidity hinv

theorem binary01_no_self_inverse {k : Nat} {f : GR k} {c : Int}
    (hb : IsBinary01 f) (hself : ∀ x, conv f f x = scaleDelta c x) :
    suppCount f ≤ 1 :=
  _root_.SpecMat13.binary01_no_self_inverse hb hself

theorem treeElem_wht : (d : Nat) → (ω : BVec (treeWidth d)) →
    wht (treeElem d) ω = (2 : Int) ^ d * spectralSign d ω :=
  _root_.SpecMat13.treeElem_wht

theorem treeElem_polylog_identity (d : Nat) :
    4 * suppCount (treeElem d) = (treeWidth d + 2) ^ 2 :=
  _root_.SpecMat13.treeElem_polylog_identity d

theorem asymTree_non_self_inverse (d : Nat) :
    asymTreeP d ≠ asymTreeQ d ∧ (∃ x, asymTreeP d x ≠ - asymTreeQ d x) :=
  _root_.SpecMat13.asymTree_non_self_inverse d

theorem k3_no_spanning_ternary_dyadic {m : Nat} {f g : GR 3}
    (ht : IsTernary f) (hspan : AffineSpan f)
    (hinv : ∀ x, conv f g x = scaleDelta ((2 : Int) ^ m) x) : False :=
  _root_.SpecMat13.k3_no_spanning_ternary_dyadic ht hspan hinv

theorem unshiftedLift_breaks_ternary :
    ¬ IsTernary (unshiftedLift (treeElem 1) (treeElem 1)) :=
  _root_.SpecMat13.unshiftedLift_breaks_ternary

end GroupRingPolylogBitInversesChallenge
