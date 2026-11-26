import Lib.Weil.DualPair.PairSumNegation
open Matrix Fintype G Int stdLattice MvPolynomial NumberField Sgn Std WeilData
attribute [-simp] matToVec_smul
variable {E : Type} [Field E] [CMType E] [WeilData E] {n a : Type}
  [Fintype n] [Fintype a] {s t t'} {c : (Ô E)ˣ} (hc : star c.1.1 * c = -1) (ht : t' = -t)
  (V : Space E a t) (W : Space E n s)
@[simps! -isSimp val] noncomputable def flipIdele (c : (Ô E)ˣ) (t : ℤˣ) :
    (𝔸 E)ˣ := MulEquiv.prodUnits.symm (t.map (castRingHom _).1, c.map (Ô E).subtype * α * star α⁻¹)
attribute [local simp] sum_prod_type Matrix.mul_assoc Prod.ext_iff starCoordEquiv _root_.funext_iff
  pairSign realVac val_flipIdele pairWeil
noncomputable def flipCoords : Std E (.id ℂ) (homSigns t s) (homSigns s t') := by
  use starCoordEquiv (.prodComm ..) (flipIdele c ∘ homSigns t s),
    starCoordEquiv (.prodCongr 1 (.prodComm ..)) (.map (castRingHom ℂ) <| homSigns t s ·.2),
    starCoordEquiv (.prodComm ..) fun _ ↦ c.map (Ô E).subtype
  any_goals intro; erw [Submodule.smul_mem_iff' _ c]
  repeat simp_all [adelicSum, val_scaleIdele_fst, val_scaleIdele_snd, realHeis, signMatrix,
    intVectors, Finset.sum_comm (γ := a), mul_right_comm _ _ (star c.1.1), ← mul_assoc, ← cast_mul,
    mul_comm, ← psi₀_star, stdLattice, dotProduct] <;> grind [star_mul', star_one, α.mul_inv,
    star_star, star_mem_Ô]
lemma flipCoords_apply x : (flipCoords (s := s) hc ht).φ x = matToVec ((flipIdele c 1).1 • (stdForm
  E s * (vecToMat x)ᴴ * stdForm E t)) := by simp [flipCoords, stdForm, matToVec, vecToMat, field]
lemma flipCoords_map_omega {V'} g h f : (flipCoords hc rfl).map ((V.hom W).ω (onHom (g, h)) f) =
  pairChar (upsilonU1 ^ card n)
  (upsilonU1 ^ card a) (h, g) • (W.hom V').ω (onHom (h, .neg g)) ((flipCoords hc rfl).map f) := by
  apply ω_map <;> simp [↓onHom_mulVec, flipCoords_apply, mat_inv]
  convert weilMultiplier_neg _ (onHom (g, h))⁻¹.mat_neg; iterate 2 simp [← adelicAction_Δ,
    det_onHom]
  rw [weilMultiplier, finMultiplier, ((saturatingElem _).2.map_of_le_comap
    (reindexRingEquiv _ (.prodComm ..)).toRingHom (by tauto)).glMultiplier_transpose]
  congr 2 with
  rw [realMultiplier, ← principalMinor_submatrix (.prodComm ..), ← principalMinor_transpose]; congr
  any_goals (try ext); apply_rules [mul_comm, det_reindex_self]
  simp [mul_comm]
@[simps -isSimp] noncomputable def flipSpace : Space E _ (-t) := ⟨-V.J, .scalar _
  (star (flipIdele Weil.normNegOne 1)) * V.x, by simp [Matrix.map_neg, V.gram_point, stdForm,
            ← smul_eq_diagonal_mul, ← diagonal_smul]; grind [star_normNegOne_mul_self, star_mul,
  star_one, α.mul_inv]⟩
lemma exists_pairTheta_flip V' (l : G E t') (hl : V'.x.1 * l.mat = star (flipIdele c 1).1 • V.x) b :
  ∃ z, ‖z‖ = 1 ∧ ∀ a' f g h g', g'.mat = l.mat * g.mat → pairTheta W V' (b⁻¹ * upsilonU1 ^ card n)
  (a'⁻¹ * upsilonU1 ^ card a) ((flipCoords hc ht).map f) (h, g') =
  z * pairTheta V W a' b f (g, h) :=
  have ⟨z, k, H⟩ := (flipCoords hc ht).exists_theta_omega_map (V.hom W) (W.hom V') (onHom (1, l))
    fun _ ↦ W.mem_ratVectors_hom.2 ∘ .imp' (V.J⁻¹ * ·ᴴ * W.J)
    (by simp_all [← conjTranspose_map_toAdele, V.map_J_inv, W.map_J, flipCoords_apply,
    ← V'.x.1.mul_assoc, conjTranspose_nonsing_inv, ↓onHom_mulVec]) ∘ V.mem_ratVectors_hom.1
  ⟨(b⁻¹ * upsilonU1 ^ card n).1 l.det / z, by simpa, by
    cases ht; intros; have : z ≠ 0 := by grind [norm_zero]
    simp [ext_mat (g' := l * .neg _) (by simpa), *, pairTheta, field, flipCoords_map_omega,
    rep_apply_apply, ← onHom.map_mul, mul_pow]⟩
noncomputable def flipPoly t s := bind₁ fun p :
    InfinitePlace E × n × a ↦ (homSigns (-t) s p.2 : ℂ) • X (R := ℂ) (p.1, p.2.swap)
lemma realMap_flipCoords_polyVector P : (flipCoords (s := s) hc ht).realMap (polyVector _ P) =
  polyVector _ (flipPoly t' s P) := by
  ext; simp [realMap, ← aeval_eq_eval, aeval_bind₁, ↓vac_realEquiv, flipPoly]
  congr; aesop (add simp [holCoord_eq, flipCoords, mul_comm])
