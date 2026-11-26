import Lib.Adelic.CuspForms.DeltaForms
import Lib.General.LinearAlgebra.BlockMatrices
import Lib.ClassField.HeckeCharacter.LevelModulus
section
variable {Φ n : Type} [Fintype Φ] [Fintype n]
def HasWeightNormLe (p : Prop) κ F b := ∃ ξ, toPoly (Φ := Φ) n κ ξ = F ∧ (p → weylNormSq ξ ≤ b)
lemma HasWeightNormLe.prod {p ι} {s : Finset ι} {κ F b} :
  (∀ i ∈ s, @HasWeightNormLe Φ n _ _ p (κ i) (F i) (b i)) → HasWeightNormLe p (s.sum κ) (s.prod F) (s.prod b) := s.induction_on (by simpa using ⟨weylEval _
  _ 0, by simp [weylKernel, highestPoly, tableauPoly, weylNormSq, PolyRep.star_weylEval]⟩) <| by
  simp_intro _ _ _ i; apply_rw [i]
  exact fun ⟨_, e⟩ ⟨_, f⟩ ↦ e.1 ▸ f.1 ▸ (range_toPoly.ge (by simp [SetLike.mul_mem_graded, diagramWeight_add, nablaFam, ← range_toPoly])).imp fun _ z ↦
    ⟨z, by grind [(weylNormSq_le_mul_of_toPoly_eq z).trans, weylNormSq_nonneg, mul_le_mul]⟩
end
section
open Matrix
variable {R S r a c N : Type} [CommRing R] [CommRing S] [Fintype r] [Fintype N] (χ : MulChar R ℂ) (φ : R →+* S) (w : Matrix c N S) (e : r ↪ N)
abbrev FixesColsOff z := z * (1 - inclMatrix R e * (inclMatrix R e)ᵀ) = 1 - inclMatrix R e * (inclMatrix R e)ᵀ
noncomputable def rowStabilizer : Subgroup (GL N R) := .copy (s := {A | FixesColsOff e A.1 ∧ w * A.1.map φ = w}) (MulAction.stabilizer .. ⊓ ((MulAction.stabilizer _ w.row).comap Units.opEquiv.symm.toMonoidHom).unop.comap (GeneralLinearGroup.map φ)) rfl
noncomputable def columnDatum σ := ite (w * map σ φ = w * inclMatrix S e) (χ (submatrix σ e id).det) 0
lemma columnDatum_mul_ite_eq {F : _ → ℂ} (hF : ∀ A ∈ rowStabilizer φ w e, ∀ y, F (A.1 * y) = F y)
  (y : Matrix N a R) z : columnDatum χ φ w e (z.submatrix id e) * ite (FixesColsOff e z) (F y) 0 =
  ite (∃ Z ∈ rowStabilizer φ w e, Z = z) (χ z.det * F (z⁻¹ * y)) 0 := by
  have K (c : FixesColsOff e z) : columnDatum χ φ w e (z.submatrix id e) = ite (w * z.map φ =
    w) (χ z.det) 0 := (by grind [Matrix.mul_assoc, mul_sub, sub_mul] : z = 1 + (z - 1) * inclMatrix
    R e * (inclMatrix R e)ᵀ) ▸ by simp [columnDatum, ← mul_inclMatrix, ← inclMatrix_transpose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc _ _ᵀ, map_inclMatrix, det_one_add_mul_comm _ᵀ, Matrix.map_add, transpose_map, ← w.mul_assoc, (mul_left_injective_of_inv _ _ (inclMatrix_transpose_mul_self e)).eq_iff' (Matrix.zero_mul _)]
  obtain ⟨z, rfl⟩ | _ := em (IsUnit z) <;> simp_all [χ.map_nonunit, isUnit_iff_isUnit_det, Units.val_inj, rowStabilizer] <;> grind [mul_inv_cancel_left_of_invertible]
end
noncomputable section
open Matrix NumberField ComplexConjugate Fintype Subgroup Space WeilData Sum MatMul
section
variable {E r n : Type} [Field E] [NumberField E] [IsCMField E] [Fintype r] [Fintype n] (S : LevelPlaces E) (u : r ↪ n)
abbrev LevelPlaces.ChosenGL (r : Type) [Fintype r] := ∀ i, GL r (ResField (S.chosenPlace i))
attribute [local irreducible] IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers
def firstBlockHom : S.ChosenGL r →* ∀ i, GL n (ResField (S.placeAt i)) := .pi (rec ((extendGL u).comp <| Pi.evalMonoidHom _ ·) fun _ ↦ 1)
def auxLevel : Subgroup (∀ i, GL n (ResField (S.placeAt i))) := pi .univ (rec (fun i ↦ MulAction.stabilizer _ (inclMatrix (ResField (S.placeAt (inl i))) u).col) fun _ ↦ rangeParabolic u)
end
variable (E r n : Type) [Field E] [CMType E] [Fintype r] [Fintype n] (S : LevelPlaces E) (u : r ↪ n) [WeilData E]
structure AuxPair extends LevelPlaces E where
  signs : r → _
  W : Space E r signs
  incl : r ↪ n
  ord : r → ℕ
  (colsPlus colsMinus : InfinitePlace E → ℕ → ℕ) μ : AutChar E
  (weight ψ) hasWeight : μ.HasWeight weight ψ
  tame_eq_one : ∀ w ∉ toLevelPlaces.places, ψ w = 1
  rank_lt : card r < card n
namespace AuxPair
attribute [instance] hasWeight
variable {E r n} (O : AuxPair E r n)
abbrev levelGroup := levelOf _ (auxLevel O.1 O.incl)
def resDetDatum (X : ∀ i, Matrix n r (ResField (O.placeAt i))) := if ∀ i, X (inl i) =
  inclMatrix _ O.incl then ∏ i, O.ψ _ ((X (inr i)).submatrix O.incl id).det else 0
abbrev κ := mixedWeight n O.colsPlus O.colsMinus
abbrev detExp τ := -((∑ i ∈ .Ico 1 (card n), O.colsMinus τ i :) : ℤ)
def auxLevelChar : auxLevel O.1 O.incl →* ℂ := ⟨⟨fun g ↦ ∏ i, O.ψ⁻¹ _ ((g.1 (inr i)).1.submatrix O.incl O.incl).det,
  by bound⟩, fun g ↦ by simp [submatrix_mul_of_mem_rangeParabolic _ (g.2 (.inr _) ⟨⟩), -elim_inr]⟩
abbrev levelChar := O.auxLevelChar.comp (levelOf.reduction ..)
abbrev FormV := O.LevelForm _ O.auxLevelChar O.κ O.detExp
def chosenGLRep {W} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ _ W) :
  Representation ℂ (O.ChosenGL r) (levelSpace π _ O.levelChar) := ⟨⟨fun g ↦ (∏ i, O.ψ _ (g i).1.det) • levelRep π _ (firstBlockHom _ O.incl) (by
  delta auxLevelChar firstBlockHom auxLevel LevelPlaces.placeAt Sum.elim
  simp [mem_pi, ↓mem_stabilizer_col_iff, inv_mul_eq_iff_eq_mul_of_invertible]
  simp_all [← Matrix.mul_assoc]) g, by simp⟩, by simp [← smul_mul_smul]⟩
def formAction : Representation ℂ (O.ChosenGL r) O.FormV := chosenGLRep ..
def c1 := Fintype.linearCombination ℂ fun p : WeylIndex n _ × WeylIndex n _ ↦ letterPoly O.signs O.ord 1 O.colsPlus (Pi.single p.1 1) * letterPoly O.signs O.ord (-1)
  O.colsMinus (Pi.single p.2 1)
omit [WeilData E] in
@[simp] lemma tensorPoly_vecMulVec a b : O.c1 (vecMulVec b a).vec =
  letterPoly O.signs O.ord 1 _ a * letterPoly O.signs O.ord (-1) _ b
  := by rw [pi_eq_sum_univ' a, pi_eq_sum_univ' b]; simp [c1, linearCombination_apply, sum_prod_type, sum_mul_sum, vecMulVec_apply, mul_smul]
def harmonicPoly := O.c1 ∘ₗ ((mixedCartan ..).1.map (↑)).mulVecLin
abbrev a : AutChar E := upsilonU1 ^ negCount O.signs
abbrev b := rankTwist O.μ n
abbrev pairThetaKernel := pairThetaKer O.W (stdSpace E n) O.a O.b
def auxDatum := delta% vacuumDatum O.W (stdSpace ..) (O.levelModulus 2)
  (O.resDetDatum fun i ↦ ·.map (levelResidueAt i))
@[simp] abbrev fockDatum ξ := integrated _ (O.harmonicPoly ξ) O.auxDatum.1
def conjKernel g h := IsLinearMap.mk' (R := ℂ) (fun ξ ↦ conj
  (pairTheta _ _ O.a O.b (O.fockDatum (star ξ)) (g, 1, h))) (by constructor <;> simp [pairTheta])
def θ : O.FormV →ₗ[ℂ] G E O.signs → ℂ := by use ⟨fun Ξ g ↦ stdClassSum O.levelGroup fun h ↦
  O.conjKernel g h (Ξ h), ?_⟩ <;> simp [apply_eq_evalForm, classSum, Finset.mul_sum, funext_iff]
variable {w : FinPlace E} (hw : _ ≠ w) (hS : w ∉ O.places.conjClosure)
def heckePolyOnForms (X : ℂ) : Module.End ℂ O.FormV := (heckePolyOp (algFormRep ..) hw X).restrict fun _ h ↦ have := (heckeSplit_mem_levelSpace hw · (LevelPlaces.LevelForm.mem_sphericalAt ⟨_, h⟩ hS) levelOf_le_Kf h)
  by simp [heckePolyOp, heckePolyEval, sum_mem, Submodule.smul_mem, *]
omit [WeilData E] in
lemma heckePolyOnForms_eq_smul {y p} (h : IsSphericalWith (rightRegular ..) hw p y.1.1) X :
  O.heckePolyOnForms hw hS X y = p X • y := Subtype.ext
  (Subtype.ext ((map_heckePolyOp (Submodule.subtype _) _).trans (h.2 X)))
abbrev rankDiff (_ : AuxPair E r n) := card n - card r
def testValue w := (O.a.frobValue r w * w.q ^ (O.rankDiff - 1))⁻¹
def Lifts (y : O.FormV) (z : _ → _) := ∀ w (hw : _ ≠ w), w ∉ O.places.conjClosure → IsSphericalWith (rightRegular ..) hw (fun T ↦ trivialHecke w.q O.rankDiff (O.a.frobValue r w * T) * heckePolyEval r w (z w) (w.q ^ O.rankDiff * O.a.frobValue r w / O.b.frobValue n w * T)) y.1.1
end AuxPair
open Ideal Modulus Set Gf LevelPlaces Quotient MvPolynomial Finset
section
variable {E r n N m a : Type} [Field E] [NumberField E] [IsCMField E] [Fintype r] [Fintype n] [Fintype N] [Fintype m] {S : LevelPlaces E}
abbrev LevelPlaces.chosenModulusSq (S : LevelPlaces E) := S.levelModulus 2 false
lemma map_block_eq_blockGL {R} [CommRing R] f ε (k : Kf E N) (l : Kf E m) : ∃ h, Kf.map (S := R) n f
  ⟨U.block ε (k, l), h⟩ = reindexGL ε (blockGL (Kf.map N f k, Kf.map m f l)) := by simp [mem_Kf, mem_Kf.1, Units.ext_iff, ← ext_iff, reindex_equiv ε, ← ZeroMemClass.zero_def]
lemma levelModulus_ideal_le : (S.levelModulus 2).ideal ≤ S.chosenModulusSq.ideal := mul_mono_right (by simp)
lemma places_levelModulus_false {c} [NeZero c] : (S.levelModulus c false).places =
  Set.range S.chosenPlace := Set.ext (by simp [Modulus.places, levelModulus, IsPrime.pow_le_iff NeZero.out, _root_.prod_places_le_iff])
abbrev reduceToR₀ : (S.levelModulus 2).ResRing →+* S.chosenModulusSq.ResRing := factor levelModulus_ideal_le
lemma liftMod_mem_supportedOn (B : GL n S.chosenModulusSq.ResRing) : ↑(liftMod B) ∈ supportedOn n
  (Set.range S.chosenPlace) := by grind [places_levelModulus_false, liftMod]
end
variable {E r n : Type} (N m a : Type) [Field E] [CMType E] [Fintype r] [Fintype n] [Fintype N] [Fintype m] {S : LevelPlaces E} (O : AuxPair E r n)
lemma atPlace_twistPlace_eq_one {k} (h : k ∈ supportedOn n (Set.range S.chosenPlace)) i :
  k.atPlace (S.twistPlace i) = 1 := S.7.rec (by simp_all [eq_comm])
structure DividedSplitting (z : r ↪ m) extends ε : N ⊕ m ≃ n where
  ε_ι i : ε (inr (z i)) = O.incl i
  (fixedEmb : r ↪ N) (dividedEmb : a ↪ N) low : HasColumnsBelow n N O.colsPlus ∧
    HasColumnsBelow n m O.colsMinus
def AuxPair.genIdele := (O.levelModulus 1 false).generator
abbrev AuxPair.genIntAdele : Ô E := ⟨O.genIdele, (generator_spec _).1⟩
variable {N} {m} {a} {O} {z : r ↪ m} (V : DividedSplitting N m a O z)
lemma genIdele_apply_of_notMem {w} : w ∉ Set.range O.chosenPlace → O.genIdele.1 w = 1 := by simp_all [generator_spec, AuxPair.genIdele, places_levelModulus_false]
lemma reduction_levelModulus_eq_zero_iff {c x} : (O.levelModulus c false).reduction x = 0 ↔ O.genIdele⁻¹.1 ^ c * x ∈ Ô E := by have := (O.levelModulus 1).2; simp_all [↓generator_spec, mem_Ô, v_inv, AuxPair.genIdele, valued_generator, levelModulus, FiniteMultiplicity.multiplicity_pow, FiniteMultiplicity.of_prime_left, (_ : FinPlace E).prime]
namespace DividedSplitting
abbrev genResidue (_ : DividedSplitting N m a O z) := O.chosenModulusSq.reduction O.genIntAdele
lemma genResidue_smul_eq_iff {k c} (S : Matrix k c (O.levelModulus 2).ResRing) u :
    V.genResidue • S.map reduceToR₀ = V.genResidue • inclMatrix _ u ↔ ∀ i, S.map (levelResidueAt (inl i)) = inclMatrix _ u := by
  choose X e using fun a b ↦ (add_left_surjective (inclMatrix _ u a b)).comp (reduction_surjective _) (S a b)
  simpa [inclMatrix, apply_ite (_ : _ →+* _), ← ext_iff, ← e, ← map_mul, reduction_levelModulus_eq_zero_iff, sq, mul_add, mul_assoc, -elim_inl] using! matrix_ext_modulusResidue O.isConjApart_chosenPlace.1 (x := (of X).map (O.levelModulus 1 false).reduction) (y := 0)
end DividedSplitting
section
variable {Φ l n n' : Type} [Fintype l] [Fintype n'] (τ : Φ) (η : Matrix l n ℂ) (j : l ⊕ n' → n) (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E]
def stackedDet := (((η.map C).fromRows (of fun a b ↦ X (τ, a, b))).submatrix id j).det
abbrev unitModulus : Modulus E := ⟨⊤, top_ne_bot, (by simp [·.2.1])⟩
end
variable {Φ l n n' : Type} [Fintype l] [Fintype n'] (τ : Φ) (j : l ⊕ n' → n) (E : Type) [Field E] [CMType E] [WeilData E] (m : ℕ)
def carrierForm := Space.lift (pairThetaKer (stdSpace ..).neg (signedSpace E (1 ⊕ᵥ -1 : Fin (2 * m) ⊕ Fin m → _)) (upsilonU1 ^ m) 1)
  (modDatum _ _ (unitModulus E) 1 (polyVector _ (∏ τ, letterMinor τ .inr id ^ (2 * m)))) fun _ ↦ 1
variable {E}
def carrierXi c h := stdClassSum (Kf E (Fin m)) (modKernelI (n' := n') (stdSpace ..) c 1 (unitModulus E) 1 1 ⟨1, ·⟩ h)
variable {Φ a L N : Type} [Fintype a] [Fintype N] [Fintype L] (e : a ⊕ N ≃ L) {p : ℕ} [Fintype Φ] {ι : Φ → Type} [∀ τ, Fintype (ι τ)] (M : ∀ τ, ι τ → _) (c : Φ → Matrix N N ℂ) (g : Φ → Matrix L L ℂ)
lemma s22_m5 (e : L ≃ a ⊕ N) Z : ∃ (Y : Matrix a L ℂ) (γ : ℂ), (∀ X, ((fromCols X Z).submatrix id e).det = γ * (Y * X)ᵀ.det) ∧ ‖γ‖ ^ 2 * ‖(Y * Yᴴ).det‖ ≤ ‖(Zᴴ * Z).det‖ := (isValuationPair_top.exists_mul_clear_cols Zᴴ (.trans .inr e.symm.toEmbedding)).elim fun V _ ↦ by
  let U := V.1.submatrix id e.symm
  have G W X := ((U.toCols₁.fromCols W).submatrix id e)ᴴ.det_mul ((fromCols X Z).submatrix id e)
  simp [↓det_conjTranspose, ← submatrix_mul, ↓det_transpose, mul_comm, (conjTranspose_injective (by aesop) : U.toCols₁ᴴ * Z = 0)] at *
  have H X := by simpa [← eq_div_iff, U, mul_div_right_comm] using (G U.toCols₂ X).symm
  exact ⟨_, _, H, by cases (by simpa [H, ← mul_assoc, U] using congr(‖$(G Z U.toCols₁)‖)) <;>
    simp [*, field]⟩
abbrev s22_v7 := aeval (R := ℂ) fun (τ, a, b) ↦ ∑ i, ∑ j, (c τ i a * g τ b j) • @X ℂ _ _ (τ, i, j)
def inFirstCols := aeval (R := ℂ) fun (τ, a, b) ↦ (Sum.elim (X ⟨⟨τ, a⟩, @Fin.val p ·⟩) (C <| @X ℂ (Φ × N × L) _ ⟨τ, a, ·⟩) b : MatrixPoly (Σ _, N) _)
def stackedDetProd := ∏ τ, ∏ k, stackedDet τ (M τ k) e
lemma twoSidedSubst_stackedDetProd : s22_v7 c g (stackedDetProd e fun τ k ↦ M τ k * (g τ)ᵀ) =
    (∏ τ, ((c τ).det * (g τ).det) ^ card (ι τ)) • stackedDetProd e M := funext (by
  simp [-prod_mul_distrib, stackedDetProd, stackedDet, ← prod_smul, ← card_univ, smul_prod, hom_bind₁, ↓RingHom.map_det]; congr!
  rw [show ∀ M, _ * det M = det (fromBlocks 1 0 0 _ᵀ * (M * _ᵀ.submatrix e e)) by simp [field]]
  congr 1 with ⟨⟩ <;> simp [mul_apply, mul_sum, ← submatrix_map]; ac_nf)
def s22_z3 κ F l := (hookNumber κ (rankAt N) : ℂ)⁻¹ • fockPairing _ (@inFirstCols Φ L N p F) (nablaBasis _ _ κ l)
lemma s22_v3 {F F'} {s : ℂ} (H : s22_v7 c (fromBlocks 1 0 0 <| g ·) F' = s • F) κ l : s22_v7 c g (∑ l', schur κ c l l' • s22_z3 κ F' l') =
  s • s22_z3 (p := p) κ F l := by
  obtain ⟨_, H⟩ := map_fockPairing (s22_v7 c g).1 (inFirstCols F'), congr(s22_z3 κ $H l)
  rw [s22_z3, comp_aeval_apply, (MvPolynomial.algHom_ext (by simp [inFirstCols, rowSubst, ← C_mul']) : aeval _ = ((rowSubst fun τ ↦ ((c τ).map C)ᵀ).restrictScalars ℂ).comp ((mapAlgHom (s22_v7 c g)).comp inFirstCols))] at H
  simp_all [fockPairing_rowSubst, schur_map, C_mul', s22_z3, smul_comm _ _⁻¹, smul_sum]
