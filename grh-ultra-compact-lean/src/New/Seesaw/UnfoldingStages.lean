import New.Seesaw.AdmissibleComb
import Lib.Weil.Periods.DegreeOfT
import Lib.Weil.Periods.UnfoldingStep
import New.Filling.LatticeChart
import New.Columns.TwistedHeckeType
import New.Trace.LabelRigidity
import New.Filling.FillingAdmissible
section
open Fintype Matrix Valued Space WithZero MatMul
variable {E X ι : Type} [Field E] [CMType E] [Fintype ι] {ε s N} {V : Space E ι ε} (e : X ⊕ Fin s ≃ ι) (Y : Grading V N X s) (y : Gf E ι)
private def k7 i := (e.symm i).elim (fun _ ↦ 2 * s) (4 * ·.1 + 1)
attribute [local simp] blockTriangular_inv_of_blockTriangular ideleLogVal mul_assoc v_inv
private lemma q4 {e : X ⊕ Fin s ≃ ι} {R} [CommRing R] {A B} (h : BlockTriangular (R := R) A (k7 e)) (h' : BlockTriangular B (k7 e)) a : letI i := e (.inr a); (A * B) i i =
    A i i * B i i := sum_eq_single _ ((reindex_equiv e).1.2 (by grind [k7, BlockTriangular]))
structure Grading.IsAdaptedBasis (x b : GL ι (𝔸f E)) (β : _ → (𝔸f E)ˣ) where
  triangular : b.1.BlockTriangular (k7 Y.indexEquiv)
  integral : b⁻¹ * x ∈ intGL ι (Ô E)
  diag_eq i : b (Y.indexEquiv (.inr i)) (Y.indexEquiv (.inr i)) = β i
abbrev Grading.IsAdaptedAt := Y.IsAdaptedBasis (V.xFin * y)
def Grading.HasNearLines a (Q : Finset _) (n k : ℕ) x := ∃ b β, Y.IsAdaptedAt x b β ∧ ∀ i w,
  |ideleLogVal (β i) w - ideleLogVal ((a / star a) ^ n * ite (Odd s) 1 (ite (2 * i < s) a⁻¹ (star a))) w| ≤ ite (w ∈ Q ∨ star w ∈ Q) ↑k 0
lemma Grading.k4 : ∃ b β, Y.IsAdaptedAt y b β := (isValuationPair_Ohat.exists_isPrimitiveMatrix_mul ⟨_, (V.xFin * y).mul_inv⟩ _).imp fun b H ↦ ⟨(.mkOfMulEqOne _ _ <| by rw [← q4 H.1 _ ·, b.3] <;> aesop), H.1,
  inv_mem_iff.1 (exists_eq_right.1 (mod_cast isPrimitiveMatrix_iff.1 H.2)), by simp⟩
variable {w} {Y : Grading V N X s} {y : Gf E ι} {b β g g' b' β'} (h : Y.IsAdaptedBasis g b β) (h' : Y.IsAdaptedBasis g' b' β')
lemma Grading.IsAdaptedAt.p1 [Fintype X] (h : Y.IsAdaptedAt y b β) i j (hj : j ≤ i.rev) : letI k := (b⁻¹ * (V.xFin * y))⁻¹.1
  letI f := Y.indexEquiv ∘ .inr; (kᴴ * k) (f i) (f j) = V.J (f i) (f j) • (star (β i) * β j).1 := by
  erw [← mul_one _ᴴ, gram_mul_of_gram_eq (gram_inv_of_gram_eq (gram_mul_of_gram_eq V.gram_xFin y.2)) (mul_assoc ..), Y.2, mul_apply, sum_eq_single (Y.indexEquiv (.inr i))] <;>
    simp [↓map_gradedGram_mul_apply, gradedGram, stringReversal, reindex_equiv Y.indexEquiv]
    <;> grind [IsAdaptedBasis, k7, BlockTriangular, star_zero, Algebra.smul_def]
lemma Grading.IsAdaptedBasis.inv (h : Y.IsAdaptedBasis g b β) : Y.IsAdaptedBasis b⁻¹ b⁻¹ β⁻¹ := ⟨by simp [h.1], by simp, (Units.eq_inv_of_mul_eq_one_right <| by simp [← h.3 ·, ← q4, h.1])⟩
include h h'
lemma Grading.IsAdaptedBasis.b4 (e : IsIntMatrix v.integer
  ((g⁻¹ * g').map (evalAt w)).1) i : ideleLogVal (β' i) w ≤ ideleLogVal (β i) w := by
  simpa [q4 h.inv.1 h'.1, h.inv.3, h'.3, field, zero_lt_iff, -coe_units_inv] using (v.valuationSubring.1.comap (evalAt w)).matrix.mul_mem
    (mul_mem (mem_intGL_Ô.1 h.2 w).isIntMatrix e) (mem_intGL_Ô.1 h'.2 w).isIntMatrix_inv
    (Y.indexEquiv (.inr i)) (Y.indexEquiv (.inr i))
lemma Grading.IsAdaptedBasis.f6 (e : g.map (evalAt w) = g'.map (evalAt w)) i :
  ideleLogVal (β' i) w = ideleLogVal (β i) w := by
  apply_rules [le_antisymm, b4] <;> simp [e, IsIntMatrix.one]
omit h h'
lemma Grading.IsAdaptedAt.m1 {E X ι} [Field E] [CMType E] [Fintype ι] [Fintype X]
  {ε s N} {V : Space E ι ε} [StablyUnram E] {Y : Grading V N X s} {x x' b b' β β'} (h : Y.IsAdaptedAt x b β) (h' : Y.IsAdaptedAt x' b' β') (l : ∀ i w, i ≤ i.rev → ideleLogVal (β' i) w =
  ideleLogVal (β i) w) : ∃ k ∈ Kf E ι, x' * k * x⁻¹ ∈ Y.besselFin := by
  let γ a := ite (a ≤ a.rev) β β' a
  have ⟨b', h'⟩ : ∃ b', Y.IsAdaptedAt x' b' γ := ⟨b' * diagGL ((1 ⊕ᵥ β'⁻¹ * γ) ∘ Y.indexEquiv.symm), by constructor <;> simp_all [h'.1 _, BlockTriangular, ← map_inv, diagonal_apply, h'.3, mul_assoc, mul_mem, h'.2, γ, mem_intGL, reindex_equiv Y.indexEquiv, mem_Ô, ← log_le_log, v_inv, ideleLogVal, apply_ite, ite_apply]⟩
  let f (a : {a // a ≤ a.rev}) := Y.indexEquiv (.inr a.1)
  let P {g} (h : g ∈ intGL ι (Ô E)) : IsPrimitiveMatrix (Ô E) (submatrix (Units.inv g) id f) := (mem_intGL.1 h).symm.imp (by tauto) fun H ↦ ⟨g.1.submatrix f id, fun i ↦ H (f i),
      (g.3 ▸ submatrix_one f (by aesop_cat) : (g.1 * g.inv).submatrix f f = 1)⟩
  peel witt_Ô (P h.2) (P h'.2) (by ext; erw [h.p1, h'.p1] <;> grind) with g n e
  refine Y.mem_besselGroup_iff_sub_one.2 (Y.indexEquiv.surjective.forall₂.2 fun _ _ _ _ ↦ ?_)
  have q {i} c : (V.ratCoordMatrixFin (x' * g * x⁻¹) * b) i (f c) = b' i (f c) := by
    simpa [submatrix_mul (e₂ := id), ratCoordMatrixFin] using! congr(((V.xFin * x').1 * $e) i _)
  erw [sub_eq_zero, ratCoordMatrix_inr, ← b.mul_inv_cancel_right (V.ratCoordMatrixFin _), mul_apply, Finset.sum_congr rfl ((reindex_equiv Y.indexEquiv).1.2 _), ← mul_apply, b.mul_inv]
  apply apply_ite₂
  grind (splits := 20) [q ⟨_, _⟩, h.inv, gradeOf_inl, k7, gradeOf_inr, BlockTriangular, IsAdaptedBasis]
end
section
open Matrix Gf WithZero Space Kronecker Valued Fintype WeilData MatMul Algebra
variable {E ι ι' X X' : Type} [Field E] [CMType E] [Fintype ι] [Fintype ι'] [Fintype X] {s s' N ε ε'} {V : Space E ι ε} {V' : Space E ι' ε'} {Y : Grading V N X s}
attribute [local simp] gradedGram ite_apply division_def v_inv smul_smul atPlace
lemma Grading.IsAdaptedAt.f7 {x b β P π} [StablyUnram E] (h : Y.IsAdaptedAt x b β) (q : IsSplitSquarefree P N π) (hg : Odd s → ∀ᵉ (n ∈ Y.besselFin) (w : P), ¬∀ a ∈ maxCompactAt X w, (n * x)⁻¹ * (Y.inclXFin a * (n * x)) ∈ maxCompactAt ι w)
  i w : ideleLogVal (β i) w + ideleLogVal (β i.rev) (star w) ≤ 0 := by
  have G {x b β} (h : Y.IsAdaptedAt x b β) i := by simpa [apply_ite, -ite_mul, Y.2, q.1, smul_def, ← log_le_log, ← ideleLogVal.eq_1] using mem_Ô.1 (h.p1 i _ le_rfl ▸
    h.2.isIntMatrix_inv.isInt_conjTranspose.mul h.2.isIntMatrix_inv _ _ :)
  have K w : ideleLogVal π w = ite (w ∈ P) (-1) 0 := by simp [ideleLogVal, q.2, apply_ite]
  wlog p : star w ≠ w ∧ Odd s ∧ i.rev = i ∧ w ∈ P generalizing w; grind [star_star, q.2 w]
  have L a w : ideleLogVal (star β⁻¹ a) w = -ideleLogVal (β a) (star w) := by simp [ideleLogVal]
  let γ a := ite (a ≤ i) (β a) (star β⁻¹ a.rev)
  let d := diagGL ((1 ⊕ᵥ γ) ∘ Y.indexEquiv.symm)
  have D : Y.IsAdaptedBasis d d γ := by constructor <;> simp [d]
  have ⟨y, o, e⟩ : ∃ y ∈ supportedOn ι {w}, d.map (evalAt w) = (V.xFin * ↑(y * x)).map (evalAt w) := ⟨atSplit p.1 (.map (evalAt w) (V.xFin⁻¹ * d / x)), by simp +contextual [atSplit, evalAt_star_locGL, p]⟩
  have ⟨_, _, h'⟩ := Y.k4 (y * x); contrapose! hg
  obtain := D.f6 h' e, (h.f6
    h' <| by simpa using mem_supportedOn.1 o · · ·), h'.b4 D (w := star w) (by
    simp_rw [GeneralLinearGroup.val_map_apply, Units.val_mul, coe_units_inv, inv_eq_left_inv (gram_mul_of_gram_eq gram_xFin (y * x).2), Matrix.map_mul, @id (_ᴴ.map _ = _) (evalAt_star_GL rfl _), ← e]
    simp [d, reindex_equiv Y.indexEquiv, Y.2, apply_ite, -evalAt_apply, q.1, IsIntMatrix, v.mem_integer_iff]
    simp [← log_le_log, ← ideleLogVal.eq_1]; grind [star_star])
  refine (h.m1 h' (by grind [star_star, q.2 w])).elim fun _ ⟨k, r⟩ ↦ ⟨p.2.1, _, r, ⟨w, p.2.2.2⟩, fun A ⟨⟨B, a⟩, l⟩ ↦ (and_congr_left mem_Kf_iff_of_supportedOn).2 ⟨?_,
    mem_supportedOn.2 fun u b c ↦ by simpa [mul_eq_one_iff_eq_inv] using
    (Units.ext (congr($(Y.ratCoordMatrixFin_inclXFin A).map _).trans (by simp_all [-evalAt_apply, Units.ext_iff, ← submatrix_map])) : (V.xFin * _ * _).map _ = 1)⟩⟩
  simpa [e, mul_assoc] using mem_intGL_Ô.1 (mul_mem (inv_mem k) (mul_mem (a := MulAut.conj (d⁻¹ * V.xFin) _) ⟨reindexGL Y.indexEquiv (blockGL (B, 1)), by simp [Units.ext_iff, ← ext_iff, d, reindex_equiv Y.indexEquiv, diagGL, ← ratCoordMatrixFin.eq_1, -Matrix.mul_assoc, -coe_units_inv, ratCoordMatrixFin_inclXFin, ← @id (_ = A.1) a, apply_ite]⟩ k)) w
attribute [-simp] coe_units_inv in
lemma Grading.HasNearLines.step {Y' : Grading V' N X' s'} [WeilData E] {μ f a m m' Q k x x' t} (hx : Y.HasNearLines a Q m k x.2) (hm : m = m' + ite (Odd s) 0 1) (hs : s' + 1 = s) (ha : ∀ w, v ((Y.c : 𝔸f E) w) = v ((a * star a.1) w)) (n : Y.constTermAtT Y' μ (integrated _ t f) x x' ≠ 0) b (hb : ∀ w, ideleLogVal (star (α / a)) w ≤ ideleLogVal b w + ite (w ∈ Q) 1 0) (hf : ∀ y ∈ stdLattice E _, finHeisOp _ (b.1 • y) f = f) (hg : ∀ {b β}, Y'.IsAdaptedAt x'.2 b β → ∀ i w, ideleLogVal (β i) w + ideleLogVal (β i.rev) (star w) ≤ 0) : Y'.HasNearLines a Q m' (k + 1) x'.2 := by
  obtain ⟨⟨B, γ, p, _⟩, rfl, rfl⟩ := hx, hs, hm
  peel Y'.k4 x'.2 with B' γ' q
  have H i : ite (Odd s' ↔ i ≤ Fin.rev i) Y.c.1 1 • (star (b / γ i.rev.succ) / α / γ' i).1 ∈ Ô E := ?_
  simp [apply_ite ideleLogVal, ↓ite_smul, ite_mem, mem_Ô, smul_def] at *; unfold ideleLogVal at *
  simp [ha, ← log_le_log, ← ideleLogVal.eq_1, abs_le] at *
  grind [star_star]
  choose _ _ _ D _ P L using Y.exists_splitting_constTerm Y'.gradeOf_stringReversal
  let g := (G.onHom (x, x')).2
  obtain ⟨l, hl, e⟩ := s22_m3 D (b.1 • g) (star b⁻¹.1 • g) (n <| by
    simp [L, pairWeil, omega_integrated]; rw [((s22_j5 D).2 ..).choose_spec, ·]
    simp) (by simp [← U.inv_val_eq_conjTranspose]) (by simpa using congrArg (ω _ g) <| hf · ·)
  rw [show _ᴴ = (D.kᴴ * (V.hom V').J).map (algebraMap _ (𝔸f E)) * (V.hom V').xFin.1 by
    simp [← gram_inv_of_gram_eq gram_xFin, Splitting.kAdelic, ← RingHom.coe_snd]
    congr with; simp, ← mulVec_mulVec, (rfl : (xFin _).1 = V'.xFin ⊗ₖ V.xFin⁻¹.1ᵀ), finCoord_homAtPoint, G.onHom_snd, smul_mulVec, mulVec_sub, mulVec_smul] at e
  have h i j (h : Y'.gradeOf i < Y.gradeOf j) := by
    simpa [← Matrix.map_mul, ↓P, matToVec, ↓vecToMat_matToVec, coe_units_inv, ← mul_assoc, ← star_mul, mul_sub, h, ↓kronecker_mulVec_eq_matToVec] using congr(star b * (((V.hom V').J⁻¹ * D.k).map (↑) *ᵥ $e) (i, j))
  generalize o : V'.xFin.1 * (_ : Matrix ι' ι (𝔸f E)) = W at h
  convert (by simpa [← o, coe_units_inv, ← U.inv_val_eq_conjTranspose, inv_eq_left_inv gram_xFin, ← Matrix.map_mul, ← (V.J.map _).mul_assoc] using (q.2.isIntMatrix.mul (N := vecToMat l) (hl ⟨·, ·⟩)).mul p.2.isIntMatrix.isInt_conjTranspose : IsIntMatrix _ (B'⁻¹.1 * W * (V.J⁻¹.map (↑) * B⁻¹.1ᴴ))) (Y'.indexEquiv (.inr i)) (Y.indexEquiv (.inr i.rev.succ))
  clear * - h p q; simp [stringMap, reindex_equiv Y.indexEquiv, reindex_equiv Y'.indexEquiv] at h
  simp only [Y.J_inv_eq_gradedGram, ↓map_gradedGram_mul_apply, mul_apply, Finset.sum_mul]
  rw [← sum_prod_type', sum_eq_single (Y.indexEquiv (.inr i.castSucc), Y'.indexEquiv (.inr i)) (by
    simp [reindex_equiv Y.indexEquiv, reindex_equiv Y'.indexEquiv, stringReversal]
    grind (splits := 20) [p.inv, q.inv, IsAdaptedBasis, BlockTriangular, k7, star_zero])]
  simp [stringReversal, algebraMap_eq_smul_one, ← h.2]
  grind [Y.N_spec, p.inv.3, q.inv.3, Pi.inv_apply]
end
section
open Filling Matrix Space
variable {E X ι} [Field E] [CMType E] [Fintype ι] [Fintype X] {ε s N} {V : Space E ι ε} (Y : Grading V N (X ⊕ _) s) {a π}
attribute [local simp] mul_assoc k7 BlockTriangular gradedLatticeBasis diagonal coe_divStar division_def
lemma Grading.g1 {x Q K n} (hL : Y.Q0 a π (divStar a ^ n)) (l : K ≤ Kf ..)
    (H : ∃ r ∈ Y.besselFin, r * x ∈ K) : Y.HasNearLines a Q n 0 x := by
  obtain ⟨⟨k, h, e⟩, r, hr, hk⟩ := hL, inv_surjective.exists.1 H
  refine ⟨_ * r * _ * (V.xFin * k⁻¹), _, ⟨.mul (M := V.ratCoordMatrixFin r) ?t ?g, by
    simpa using mul_mem h (l hk), (q4 ?t ?g · |>.trans ?_)⟩, fun _ _ ↦ by rw [sub_self]; simp⟩ <;> simp [besselFin, mem_besselGroup_iff, ratCoordMatrix_inr, apply_ite, ↓reindex_equiv Y.indexEquiv] at hr <;> simp [reindex_equiv Y.indexEquiv, apply_ite Units.val, *] <;> grind
lemma Grading.d5 {P u h} (hL : Y.Q0 a π u) (p : IsSplitSquarefree P N π)
    (H : h.1 ∈ congruenceGL (Ô E ∙ ↑π) .inr) : Y.inclXFin h ∈ Kf .. := hL.elim fun _ a ↦ by
  have r : IsIntMatrix _ (of _) := (a.1.isIntMatrix <| Y.indexEquiv <| .inl ·)
  by_cases Odd s <;> [have := isIntMatrix_scaleAt_sub_one π (Sum.inr ()) (by grind [IsSplitSquarefree]) H; have := H.1.isIntMatrix.sub .one] <;> simpa [show (Y.inclXFin h).1.1 =
    V.xFin⁻¹ * (V.ratCoordMatrixFin (Y.inclXFin h) - 1) * V.xFin + 1 by simp [ratCoordMatrixFin, sub_mul, mul_sub], mul_apply, ratCoordMatrixFin_inclXFin, Y.2, gradedGram, ↓inv_eq_left_inv gram_xFin, (reindex_equiv Y.indexEquiv).2, IsIntMatrix, apply_ite star, Matrix.mul_assoc, mem_Kf, *] using (r.isInt_conjTranspose.mul (this.mul r)).add .one
end
namespace Data
open MeasureTheory Function UniqueFactorizationMonoid Multiset IsDedekindDomain.HeightOneSpectrum Space Grading stdLattice Prod Modulus
variable {P} {D : Data P} (ϑ : D.TameChar) (φ : D.Column) (ξ : ∀ k, GInf D.E (D.signsY k)) (y : ∀ k, Gf D.E (D.Y k))
noncomputable def s22_z2 : ∀ k ≤ 2 * D.ϱ + 2, ∀ {X s} [Fintype X], Grading (D.spaceY k) D.N X s
  → _root_.G D.E (D.signsY k) → ℂ | 0, _ => (D.filling_fits.poincare (D.columnCoords φ) ·.ratBessel) | k + 1, l => ((D.q6 k).unfoldStep · (rankTwist
  (D.chainChar ϑ (k + 1))) (datumY ϑ k) (s22_z2 k (by lia) (D.q6 k)) (ξ k, y k))
lemma f3 {l} s t k hk (h : k ≤ l) : @s22_z2 _ D ϑ φ (update ξ l s) (update y l
  t) k hk = @s22_z2 _ D ϑ φ ξ y k hk := by induction k <;> simp (disch := lia) [s22_z2, *]
lemma s22_w7 : ∀ k l, (D.q6 k l).IsGeneric (s22_z2 ϑ φ ξ y k l.step (D.q6 k))
  | 0, _ => D.filling_fits.c4 _ (by simp [q6, filling, gProd, field])
  | _ + 1, _ => isGeneric_unfoldStep (s22_w7 ..) rfl
lemma g8 i (h : 2 * i < 2 * D.ϱ + 1) {X q s} [Fintype X] [Fintype q]
    {Y : Grading _ _ X s} (R : ArrowPair _ q (D.q6 _ h.le) (D.q6 _ h) Y) (e : D.n2 i = R.m9) x : ∃ t, ∀ ϑ φ y, y 0 ∈ D.chosenLevel → ∀ g, s22_z2 ϑ φ ξ y (2 * i + 2) (by lia) Y (Y.inclX g * (x, y
  _)) = algFormCoeff 1 t (chain₂ (D.liftKernel ϑ) (z0 ϑ y) (i + 1) φ) (R.embX g) := by
  induction' i using Nat.strongRec with i H generalizing X q s
  obtain ⟨t, a⟩ : ∃ t, ∀ ϑ φ y b g, _ = _
  swap
  choose u _ using (s22_j5 R.splitting).2
  choose _ _ using R.f9
  have L {i} : IsThetaLift _ _ _ _ (D.liftKernel · i |>.lift) := isThetaLift_thetaKernel (by simp)
  refine .imp (fun _ H o φ y b g ↦ .trans ?_ (H o ..)) (h6 (@L (2 * i)) L ((?z : ℂ) • ?v) t)
  simp_rw [z0, e, R.m6]
  simp +instances [s22_z2, Grading.unfoldStep, *, s22_w7, constTermAtT, ← integral_mul_const, ← mk_mul_mk, arrowProduct, pairWeil_integrated_all (ξ _), Std.map_integrated, boxProd_integrated]
  refine .trans congr(∫ g, $(a o φ y b g) * _ ∂_) (by rfl)
  cases i; exacts [⟨(dotProductBilin ℂ ℂ).flip _ ∘ₗ D.filling_fits.weylBesselEquiv.1.1, fun ϑ φ y a g ↦ by simpa [simpleRootSum_eq_zero_of_mem_besselH] using! (D.filling_fits.j0 (D.centralRep (D.latticeScale 0) φ) (one_mem _) g (x := (_, _)) a).trans congr(_ * D.filling_fits.weylBesselEquiv.1 (conjWeylRep _ _ _
    (φ.1.1 $(inv_mul_cancel_right ..))) ⬝ᵥ _)⟩, H _ .refl _ _ (dite_eq_left (by omega)) _]
lemma s22_y9 : z0 ϑ (fun k ↦ (y k : _ ⧸ levelY ϑ k).out) =
  z0 ϑ y := by
  choose u e using (QuotientGroup.mk_out_eq_mul (levelY ϑ _) <| y ·)
  simp [funext_iff, z0, z7, e, ← mk_mul_mk]
  congr! <;> simp [v9 ϑ _ (mem_levelOf.1 (u _).2).2 (mem_levelOf.1 (u _).2).2 fun _ ↦ (@Matrix.mul_one _ _ _ _ _ (_) _).symm]
lemma s22_k3 (φ : D.ramifiedColumns) (y₀ : y 0 ∈ chosenLevel) k hk g (e : s22_z2 ϑ φ ξ y k hk.step (q6 k hk) g ≠ 0) :
  (D.q6 k).HasNearLines D.ideleA ϑ.Q ((D.m - k + 1) / 2) k g.2 := by
  induction' k with k ih
  · exact g1 _ (D.z4 ..) levelOf_le_Kf
      (D.filling_fits.q9 _ e)
  let 𝔪 := D.𝔪 ϑ 1
  refine (exists_ne_zero_of_integral_ne_zero e).rec fun r l ↦ (ih _ _ (left_ne_zero_of_mul l)).step
    (by clear * - hk; grind) (by omega) D.k2
    (right_ne_zero_of_mul l) 𝔪.generator (fun w ↦ ?_)
    (fun x o ↦ ?_) (·.f7 D.piIdele_spec fun o n m w H ↦ e ?_)
  · erw [ideleLogVal, ideleLogVal, 𝔪.valued_generator, multiplicity_mul w.prime (.of_prime_left w.prime 𝔪.2), ← span_piGBar, ← count_normalizedFactors_eq_multiplicity (right_ne_zero_of_mul 𝔪.2), ϑ.Q.prod_coe_sort, Finset.prod, normalizedFactors_prod_of_prime] <;> simp [ideleA, chosenIdele, valued_generator, prime, count_map_eq_count', asIdeal_injective, count_eq_of_nodup ϑ.Q.2]
  · obtain ⟨z, a, d⟩ : IsAdmissibleComb _ _ 1 _ _ 0 (f2 ϑ k).1 := isAdmissibleComb_name _ _ (g := 0) (by simp) (by simp
      [ite_mem]) id (projOn_vacElem _) ⟨⟨_, 𝔪.generator_spec.1⟩, by simp [𝔪, generator_spec]⟩
    rw [d, map_finsuppSum, Finsupp.sum_congr fun t e ↦ ?_]
    simp [finHeisOp_comm, finHeisOp_vacElem
      (smul_mem_stdLattice 𝔪.generator_spec.1 o), by simpa using (mem_stdLattice_iff_psi₀.1
      o (star 𝔪.generator.1 • t) fun i ↦ mem_Ô.2 (a.1 t e i · (mod_cast Ideal.one_notMem _)))]
  obtain ⟨⟨j, rfl⟩ : Odd k, ⟨u, hu, a, d⟩, ψ, f⟩ := ⟨k / 2, o.elim (by omega)⟩,
    exists_unipotent_mul_inclX _ (inv_mem (x := (1, n)) m), D.exists_eq_sub_centralGen w φ.2
  choose t ht using g8 (update ξ _ g.1) j _ _ (dite_eq_left (by omega)) g.1
  replace ht := by simpa only [f3, update_self, le_rfl, ← s22_y9 _ (update _ _ _), (apply_update fun _ ↦ QuotientGroup.mk)] using fun ψ x ↦ ht ϑ ψ (update y (2 * j + 2) x) y₀
  have := by simpa [s22_z6, liftKernel_ω, pairWeilFinite_scalarFin, (D.charUnramifiedAt_rankTwist_of_N_mem _ _ _ _ (D.isSplitLevel_piPlaces.natCast_mem _ w.2)).det_maxCompactAt_eq_one (D.isSplitLevel_piPlaces.star_notMem _ w.2 <| ·.symm ▸ w.2) (D.scalarFin_centralGen_mem ..)] using c6 (liftKernel ϑ) fun _ ↦ scalarFin _ (D.centralGen w)
  rw [← inv_mul_cancel_left _ g, d, mul_assoc, (s22_w7 ..).unipotent_mul _ u hu (hasDegreeGe_two_of_odd _ o hu)]
  simpa [c3, algFormCoeff_apply, inclX_inr, mul_assoc, mul_def _ g, *, ← QuotientGroup.eq.2
    (maxCompactAt_le_levelOf (by simp [levelPlaces, range_chosen]; clear * - w; grind [not_isChosen_of_N_mem, D.isSplitLevel_piPlaces.natCast_mem_iff, → levelNorm_mem_and_notMem_of_mem_Q]) (H _ (D.scalarFin_centralGen_mem ..)) : _ ∈ levelY ϑ _)]
    using! (ht ψ (n * g.2) (a * (1, scalarFin _ (D.centralGen w))) :)
