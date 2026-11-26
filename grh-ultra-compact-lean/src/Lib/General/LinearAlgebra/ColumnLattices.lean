import Lib.General.LinearAlgebra.AdelicRingDefs
import Lib.Adelic.Hecke.HeckeBasic
open Matrix Submodule Fintype GeneralLinearGroup
lemma IsValuationPair.smith_normal_form {A n} [CommRing A] {R} [Fintype n] (val : @IsValuationPair A _ R) y : ∃ᵉ (k ∈ intGL n R) (k' ∈ intGL n R) (d), y = k.1 * diagonal d * k'.1 := by
  simp [intGL, -val_map_apply]
  induction' h : card n with _ ih generalizing n
  · simp_all [card_eq_zero_iff, ← ext_iff]
  obtain ⟨p⟩ := Finset.card_eq_succ.1 h
  let B (c : Fin 2 → GL n R) := map R.subtype (c 0) * y * map R.subtype (c 1)
  choose c H using (id fun c d ↦ (val (B c p p) (B d p p)).elim fun e h ↦ ⟨c * cutGL (Subtype.ext h.1) ∘ (c⁻¹ * d), by simp [B, cutGL, mul_add, add_mul, Matrix.map_smul, Matrix.map_add, R.smul_def] at h ⊢; grind⟩ : Directed LE.le (R ∙ B · p p)).finite_le (.swap _ p ∘ ·)
  choose w W using (mem_span_singleton (x := B c · ·).1 (Set.mem_of_eq_of_mem (dotProduct_comm ..) (by (repeat apply @sum_smul_mem R; intros); simpa [B, -val_map_apply] using H ![_, _])))
  let e := Equiv.sumCompl (· = p)
  choose k l d E using ih ((B c - of (w · p • B c p)).toBlock (· ≠ p) _) (by simp_all)
  use c⁻¹ 0 * .mk'' (reindex e e (fromBlocks 1 0 (of (w · ·)) k)) (by simp), .mk'' (reindex e e (fromBlocks 1 (of (w · ·)) 0 l)) (by simp) * c⁻¹ 1, ((B c p ·.1) ⊕ᵥ d) ∘ e.2
  simp [mul_assoc, Units.eq_inv_mul_iff_mul_eq, -coe_units_inv]
  simp_all only [← mul_assoc, Units.eq_mul_inv_iff_mul_eq, R.smul_def, smul_eq_mul]
  apply (B c).ext; simp [e.surjective.forall₂, e, entrywise, ← e.sum_comp, apply_ite, ↓mul_diagonal] at E ⊢; grind-linarith
open MatMul QuotientGroup Units
section
variable {A l n μ} [CommRing A] {R : Subring A} {M : Matrix l μ A} [Fintype n] {𝔰 : Shape} {k}
lemma Membership.mem.isIntMatrix : k ∈ intGL n R → IsIntMatrix R k.1 := (mem_intGL.1 ·|>.1)
lemma Membership.mem.isIntMatrix_inv : k ∈ intGL n R → IsIntMatrix R k⁻¹.1 := (inv_mem ·|>.isIntMatrix)
lemma mulVec_mem_intVectors_iff (h : k ∈ intGL n R) {w} : k *ᵥ w ∈ intVectors R n ↔ w ∈ intVectors R n := ⟨(by simpa using h.isIntMatrix_inv.mulVec ·), h.isIntMatrix.mulVec⟩
variable {u} [StarRing A] {J : Matrix n n A} {T : 𝔰.Form A} {x}
lemma IsIntMatrix.isInt_conjTranspose [i : IsStarStable R] : IsIntMatrix R M → IsIntMatrix R Mᴴ := i.rec (by tauto)
lemma unitaryLevel_one_le_normalizer {y} : y ∈ unitaryLevel R 1 J → x ∈ unitaryLevel R u J → y * x * y⁻¹ ∈ unitaryLevel R u J | ⟨h, _⟩ => .imp (by aesop) (by simpa using h.isIntMatrix.mul · |>.mul h.isIntMatrix_inv)
lemma mem_besselU : x ∈ T.besselU ↔ ∀ i j, FI.level j ≤ FI.level i → x.1 i j = (1 : Matrix ..) i j := .rfl
attribute [local simp] IsIntMatrix splitGram IsUnimodular unitaryLevel mem_intGL
omit [StarRing A] in
lemma IsIntMatrix.neg : IsIntMatrix R M → IsIntMatrix R (-M) := by simp
omit [StarRing A] in
lemma splitGram_mul {T'} : T * T' = 1 → T.splitGram * T'.splitGram = 1 := by aesop
lemma unitaryLevel_one : unitaryLevel R 1 J = (intGL n R).subgroupOf _ := by aesop
lemma IsUnimodular.isIntMatrix : IsUnimodular R J → IsIntMatrix R J := by aesop
lemma IsUnimodular.isUnit_det_and_isIntMatrix_inv : IsUnimodular R J → IsUnit J.det ∧ IsIntMatrix R J⁻¹ := by aesop
lemma IsUnimodular.mem_unitaryLevel [IsStarStable R] (H : IsUnimodular R J) (hu : u.1 ∈ R) (h : IsIntMatrix R (u⁻¹ • (x.1.1 - 1))) : x ∈ unitaryLevel R u J := have i := (by simpa [← u.smul_def] using (h.smul hu).add .one); ⟨by simpa [i, ← U.form_mul_inv_eq, H.isUnit_det_and_isIntMatrix_inv] using H.isUnit_det_and_isIntMatrix_inv.2.mul (.mul (.isInt_conjTranspose i) H.isIntMatrix), h⟩
lemma IsUnimodular.splitGram : IsUnimodular R T → IsUnimodular R T.splitGram := .imp (by simp) fun ⟨u, _⟩ ↦ ⟨⟨_, _, splitGram_mul u.3, splitGram_mul u.4⟩, by aesop⟩
end
section
variable {n} [Fintype n] {R} [CommRing R] {O : Subring R}
noncomputable def invTransposeGL := (⟨.mk (transposeGL ·⁻¹) (transposeGL ·⁻¹), by simp [← val_inj]⟩ : GL n R ≃* _)
@[simp] lemma invTransposeGL_mem_intGL k : invTransposeGL k ∈ intGL n O ↔ k ∈ intGL n O := by simp_rw [mem_intGL]; tauto
lemma exists_invTransposeGL_inv_eq (h : IsValuationPair O) g : ∃ k ∈ intGL n O, invTransposeGL g⁻¹ = invTransposeGL k * g * k := let ⟨k, _, l, _, _, _⟩ := h.smith_normal_form g; ⟨l⁻¹ * transposeGL k, by simp_all [mul_mem, mem_intGL, invTransposeGL, transposeGL, ← val_inj, mul_assoc, -coe_units_inv]⟩
variable {A W W' F} [CommSemiring A] [AddCommMonoid W] [Module A W] [AddCommMonoid W'] [Module A W'] [Field F] {O : ValuationSubring F} {π π'} {f f' : GL n F → A} {v : W} (hb : IsBiInvariant (intGL n O.1) f) (h' : IsBiInvariant (intGL n O.1) f') {σ : A →+* A} {Z} [AddCommMonoid Z] [Module A Z] (B : W →ₛₗ[σ] W' →ₗ[A] Z) {v'} (h1 : v ∈ levelSpace (A := A) π (intGL n O.1))
include h1 hb
lemma IsBiInvariant.heckeFun_adjoint (hB : ∀ g x y, B (π g x) (π' g y) = B x y) : letI K := intGL n O.1; v' ∈ levelSpace π' K → IsBiInvariant K (σ <| f ·⁻¹) ∧ B (heckeFun π K f v) v' = B v (heckeFun π' K (σ <| f ·⁻¹) v') := fun h ↦ by choose b _ using fun q : _ ⧸ intGL n O.1 ↦ exists_invTransposeGL_inv_eq (isValuationPair_valuationSubring O) q.out⁻¹; simp_all [heckeFun_eq_sum_pullback _ h hb.1.toFinset invTransposeGL (fun _ ↦ ⟨invTransposeGL⁻¹ ·, _⟩) (by grind [=_ invTransposeGL_mem_intGL]), ← fun g y ↦ hB g⁻¹ v (π' g y), IsBiInvariant, heckeFun_sum]
include h'
lemma IsBiInvariant.heckeFun_comm : letI T := heckeFun π (intGL n O.1); T f (T f' v) = T f' (T f v) := by
  choose b _ using exists_invTransposeGL_inv_eq (n := n) (isValuationPair_valuationSubring O)
  simp_all [↓heckeFun_heckeFun, ← finsum_eq_sum_of_support_subset, not_imp_not]; congr with x
  convert! finsum_comp_equiv (Quotient.congr (invTransposeGL.1.trans (.mulLeft (x * b x))) _) with _ q
  erw [← q.out_eq, (mk_out_eq_mul (intGL ..) (_ * _)).choose_spec, (_ : ∀ g, f' g = f' (invTransposeGL g⁻¹))]
  all_goals simp_all [leftRel_apply, ← mul_assoc] <;> simp_all [mul_assoc] <;> grind [=_ invTransposeGL_mem_intGL]
end
variable {A} [CommRing A] {R : Subring A} {m n} [Fintype n] {M : Matrix m n A}
noncomputable def liftIntegralFn {B} (π : R → B) [Fintype m] := IsLinearMap.mk' (R := ℂ) (fun (f : _ → ℂ) (S : Matrix m n A) ↦ if h : ∀ i j, S i j ∈ R then f (of (π ⟨_, h · ·⟩)) else 0) ⟨by aesop, by aesop⟩
lemma isOpen_intVectors [TopologicalSpace A] (h : @IsOpen A _ R := by tauto) : IsOpen (intVectors R n).carrier := isOpen_pi_iff'.2 (by tauto)
lemma colLattice_le {L} (h : ∀ j, M.col j ∈ L) : colLattice R M ≤ L | _, ⟨_, y, rfl⟩ => by simpa [mulVec_eq_sum] using! L.sum_smul_mem (⟨_, y ·⟩) (by tauto)
lemma liftIntegralFn_mul {B} [CommRing B] (π : R →+* B) [Fintype m] f (a : GL n R) (b : GL m R) : liftIntegralFn π f ((b.map R.subtype).1 * M * (a.map R.subtype).1) = liftIntegralFn π (f <| (b.map π).1 * · * (a.map π).1) M := by
  wlog h : IsIntMatrix R M
  · exact (dite_eq_right fun H ↦ h (by simpa [liftIntegralFn, ← Matrix.mul_assoc, H, -GeneralLinearGroup.val_map_apply] using! this π 1 a⁻¹ b⁻¹ H)).trans (.symm (dite_eq_right h))
  rw [show M = (of (⟨_, h · ·⟩)).map R.subtype by rfl]; simp [liftIntegralFn, ← Matrix.map_mul, -Subring.coe_subtype, ← Matrix.map.eq_1, -of_apply]
omit [Fintype n] in
lemma single_mem_intVectors j : Pi.single j 1 ∈ intVectors R n := by aesop_cat
lemma col_mem_colLattice j : M.col j ∈ colLattice R M := ⟨_, single_mem_intVectors j, by simp⟩
