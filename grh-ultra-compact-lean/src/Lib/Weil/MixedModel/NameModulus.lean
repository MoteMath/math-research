import Lib.Weil.Construction.Projections
import Lib.General.Algebra.LatticeComplement
noncomputable section
namespace Space
open NumberField MeasureTheory stdLattice Finset Complex AddChar Matrix IsSchwartzBruhat
variable {E} [Field E] [CMType E] [WeilData E] {n} [Fintype n] {s} {S : Set (FinPlace E)} (hS : S.IsConjDisjoint) (V : Space E n s) {Ψ Ψ' : (n → _) → ℂ}
attribute [-simp] map_add
def heisenbergComb S := Finsupp.lift _ ℂ _ fun y ↦ V.ϱ (finVec (idem S.conjClosure • y)) ∘L V.projOn S
def name S := V.heisenbergComb S ∘ₗ (exists_generalized_inverse (schrodingerComb S)).choose
attribute [local simp] finHeisOp idem_apply mem_integralBox idem_mul_self localInner Set.indicator Finsupp.sum smul_smul idem_mul_mem_Ô heisenbergComb schrodingerAct_schrodingerAct mem_stdLattice star_idem integral_finsetSum integrable_finsetSum mul_sum sum_mul finVec.eq_1
lemma integrated_name v f : V.integrated v (V.name S Ψ f) = V.name S Ψ (V.integrated v f) := by simp [name, rho_integrated]
lemma name_projOn f : V.name S Ψ (V.projOn S f) = V.name S Ψ f := by simp [name, ← projOn_union]
lemma smul_name (c : ℂ) f : c • V.name S Ψ f = V.name S (c • Ψ) f := by simp
lemma projOn_name_vacElem {T} (hT : Disjoint S.conjClosure T) : V.projOn T (V.name S Ψ V.vacElem) = V.name S Ψ V.vacElem := by simp (disch := simp; grind [star_star]) [name]
lemma localInner_boxIndicator_mulVec (g : GL n _) : localInner S (boxIndicator n S) (boxIndicator n S <| g.1 *ᵥ ·) = (‖glMultiplier (cutGL (idem_mul_self S) g)‖ ^ 2 :)⁻¹ := by erw [← latticeMeasure_inter_eq_glMultiplier, ← integral_indicator_one (isOpen_stdLattice.preimage_of_continuous.inter isOpen_stdLattice).measurableSet, ← integral_complex_ofReal, localInner, ← integral_indicator isOpen_integralBox.measurableSet]; simp [mem_Ô, cutGL, ↓idem_mul_mem_Ô, apply_ite, ite_apply]; grind
lemma fourier_boxIndicator {F : _ → ℂ} m z c (h : ∀ x, boxIndicator n S (x + m) * psi₀ E (star z ⬝ᵥ idem S • (x + m)) * c * boxIndicator n S z = F x) : ∫ x in integralBox n Sᶜ, F x ∂latticeMeasure E n = boxIndicator n S.conjClosure z * c := by
 have := integral_psi₀_stdLattice (star (idem S) • z); rw [← setIntegral_add_mem (m := idem S • -m), ← funext h] <;> simp_all [↓integral_mul_const, ← integralBox_compl_inter (S := S), ← setIntegral_indicator isOpen_integralBox.measurableSet]
 grind
include hS
attribute [local simp ←] heisRep_right_rho add_assoc map_neg_eq_inv map_add_eq_mul inv_eq_conj
lemma dataInner_heisenbergComb c c' f f' : V.dataInner (V.heisenbergComb S c f) (V.heisenbergComb S c' f') = localInner S (schrodingerComb S c) (schrodingerComb S c') * V.dataInner (V.projOn S f) (V.projOn S f') := by
 simp [mul_mul_mul_comm, (integrableOn (continuous_conj.comp' (locally_constant S).continuous)).const_mul]; congr! 2 with z - y; obtain ⟨z, rfl⟩ := add_left_surjective y z; rw [← dataInner_rho _ (finVec (idem S.conjClosure • -y)), fourier_boxIndicator y z (schrodingerAct S (-y) (schrodingerAct S (y + z) (boxIndicator n S)) 0)]; by_cases hy : z ∈ integralBox n S.conjClosure; nth_rw 4 [← V.finHeisOp_projOn hy]; have := congrFun (schrodingerAct_boxIndicator hS hy) 0; simp_all; grind; have := V.projOn_finHeisOp (S.union_self ▸ V.projOn_union f').symm (idem S.conjClosure • z)
 any_goals simp_all [dataInner_projOn, schrodingerAct, integralBox, -mem_stdLattice, apply_ite]
 grind [add_mem_cancel_left]
lemma name_schrodingerComb c f : V.name S (schrodingerComb S c) f = V.heisenbergComb S c f := sub_eq_zero.1 (V.eq_zero_of_dataInner_self (by grind [name, dataInner_heisenbergComb, LinearMap.comp_apply]))
@[local simp] lemma name_schrodingerAct_boxIndicator y f : V.name S (schrodingerAct S y (boxIndicator n S)) f = V.ϱ (finVec (idem S.conjClosure • y)) (V.projOn S f) := by simpa using V.name_schrodingerComb hS (.single y 1) f
lemma name_boxIndicator : V.name S (boxIndicator n S) = V.projOn S := by simpa [schrodingerAct] using funext (V.name_schrodingerAct_boxIndicator hS 0)
variable [IsSchwartzBruhat S Ψ]
lemma ϱ_name y f : V.ϱ (finVec (idem S.conjClosure • y)) (V.name S Ψ f) = V.name S (schrodingerAct S y Ψ) f := by cases exists_schrodingerComb_eq hS ‹_›; aesop
lemma dataInner_name [IsSchwartzBruhat S Ψ'] f f' : V.dataInner (V.name S Ψ f) (V.name S Ψ' f') = localInner S Ψ Ψ' * V.dataInner (V.projOn S f) (V.projOn S f') := by grind [name_schrodingerComb, dataInner_heisenbergComb, → exists_schrodingerComb_eq, LinearMap.mem_range]
attribute [irreducible] name
end Space
end
noncomputable section
open NumberField Finset RingHom MeasureTheory Ideal Quotient Function Space stdLattice
structure Modulus E [Field E] [NumberField E] [IsCMField E] where
 ideal : Ideal (𝓞 E)
 ne_bot : ideal ≠ ⊥
 not_le_star (w : FinPlace E) : ideal ≤ w → ¬ideal ≤ star w
variable {E : Type _} [Field E] [CMType E] [WeilData E]
namespace Modulus
section
variable {E : Type _} [Field E] [NumberField E] [IsCMField E] (𝔪 : Modulus E)
abbrev ResRing := _ ⧸ 𝔪.ideal
instance : Fintype 𝔪.ResRing := @.ofFinite _ (Ideal.finiteQuotientOfFreeOfNeBot _ 𝔪.ne_bot)
def places := {w : FinPlace E | 𝔪.ideal ≤ w}
instance : _root_.Finite 𝔪.places := by simpa [Ideal.dvd_iff_le] using! Ideal.finite_factors 𝔪.ne_bot
def reduction : Ô E →+* 𝔪.ResRing := (exists_reduction_and_idele_generator 𝔪.ne_bot).choose
@[simps -isSimp] def liftFn {n : Type _} : ((n → 𝔪.ResRing) → ℂ) →ₗ[ℂ] (n → 𝔸f E) → ℂ := ⟨⟨fun Ψ x ↦ if h : ∀ i, idem 𝔪.places * x i ∈ _ then Ψ (𝔪.reduction ⟨_, h ·⟩) else 0, by aesop⟩, by aesop⟩
end
variable {n n' : Type} [Fintype n] [Fintype n'] {s : n → ℤˣ} {s' : n' → ℤˣ} (S : Space E n s) (T : Space E n' s') (𝔪 : Modulus E)
def _root_.modDatum Ψ v := (S.hom T).integrated v (Space.name _ (𝔪.places) (𝔪.liftFn (Ψ ∘ vecToMat)) (Space.vacElem _))
def _root_.modKernel a b 𝔪 Ψ P := (pairTheta S T a b (modDatum S T 𝔪 Ψ (polyVector _ P)) ⟨·, ·⟩)
section
variable {E : Type _} [Field E] [NumberField E] [IsCMField E] {n : Type _} [Fintype n] (𝔪 : Modulus E) (Ψ : (n → _) → ℂ) (x : ↥(Ô E))
def generator := (exists_reduction_and_idele_generator 𝔪.2).choose_spec.2.2.choose
attribute [local grind] reduction places not_le_star generator
lemma disjoint_places_star : 𝔪.places.IsConjDisjoint := by grind
@[simp] lemma reduction_algebraMap a : 𝔪.reduction (algebraMap (𝓞 E) _ a) = a := by grind
lemma reduction_surjective : Surjective 𝔪.reduction := Quot.ind (⟨_, reduction_algebraMap _ ·⟩)
lemma isValuationPair_resRing : @IsValuationPair 𝔪.ResRing _ ⊤ := 𝔪.reduction_surjective.forall₂.2 (isValuationPair_Ohat.top _ · · |>.imp' (⟨𝔪.reduction ·.1, ⟨⟩⟩) fun _ ↦ by simp; grind)
lemma generator_spec : ↑𝔪.generator ∈ Ô E ∧ (∀ w ∉ 𝔪.places, 𝔪.generator.1 w = 1) ∧ ∀ x, 𝔪.reduction x = 0 ↔ 𝔪.generator⁻¹.1 * x ∈ Ô E := by grind
lemma valued_generator w : Valued.v (𝔪.generator.1 w) = .exp (-multiplicity w.1 𝔪.ideal) := by grind
attribute [local simp] generator_spec liftFn_apply mul_add mul_mem mem_integralBox add_mem_cancel_left idem_apply
lemma reduction_eq_zero_iff {z} : 𝔪.reduction z = 0 ↔ z ∈ 𝔪.ideal.map (algebraMap ..) := by grind
lemma reduction_congr {x y} (h : ∀ w ∈ 𝔪.places, x.1 w = y.1 w) : 𝔪.reduction x = 𝔪.reduction y := by rw [← sub_eq_zero, ← map_sub, 𝔪.generator_spec.2.2, 𝔪.generator.inv_mul_eq_iff_eq_mul (c := idem 𝔪.placesᶜ * (x - y)).2] <;> aesop
lemma reduction_idem_mul : 𝔪.reduction (⟨_, idem_mem_Ô 𝔪.places⟩ * x) = 𝔪.reduction x := 𝔪.reduction_congr (by aesop)
omit [Fintype n] in
lemma liftFn_one : 𝔪.liftFn 1 = boxIndicator n 𝔪.places := by aesop
lemma liftFn_single (x₀ : n → _) : 𝔪.liftFn (Pi.single (𝔪.reduction ∘ x₀) 1) = cosetIndicator 𝔪.places 𝔪.generator (x₀ ·) := by simpa [funext_iff, ← 𝔪.reduction_idem_mul (x₀ _), ← sub_mem_ker_iff, -map_sub, -map_mul, mul_left_comm (idem _), mul_sub] using fun _ ↦ (⟨·, (mul_mem 𝔪.generator_spec.1).mt <| by simpa [sub_eq_neg_add] using ·⟩)
lemma apply_reduction_eq_of_algebraMap {S} [CommRing S] {f : 𝔪.ResRing →+* S} {g : _ →+* S} (h : ∀ a : 𝓞 E, f a = g (algebraMap _ _ a) := by aesop) : f (𝔪.reduction x) = g x := have ⟨_, a, d⟩ := 𝔪.ideal.ne_bot_iff.1 𝔪.2; (exists_dvd_sub_algebraMap d x).rec fun _ ⟨_, e⟩ ↦ sub_eq_iff_comm.1 e ▸ by simp_all [← h, eq_zero_iff_mem.2]
@[simp] lemma factor_reduction {𝔫} h : factor h (reduction 𝔫 x) = 𝔪.reduction x := apply_reduction_eq_of_algebraMap ..
end
attribute [local grind] reduction places not_le_star generator
attribute [local simp] generator_spec liftFn_apply mul_add mul_mem mem_integralBox add_mem_cancel_left idem_apply
variable {E : Type _} [Field E] [CMType E] {n : Type _} [Fintype n] (𝔪 : Modulus E) (Ψ : (n → _) → ℂ) (x : ↥(Ô E)) [WeilData E]
instance isSchwartzBruhat_liftFn : IsSchwartzBruhat 𝔪.places (𝔪.liftFn Ψ) := ⟨by simp [← mul_assoc, idem_mul_self, mem_Ô], pi_eq_sum_univ' Ψ ▸ (map_sum ..).substr (sum_induction _ _ .add (.const 0) (by simpa [𝔪.reduction_surjective.comp_left.forall, liftFn_single] using! fun _ ↦ (IsSchwartzBruhat.locally_constant 𝔪.places).comp (_ * ·))), isSchwartzBruhat_boxIndicator (S := 𝔪.places).3.imp (by aesop)⟩
lemma localInner_liftFn Ψ' : localInner 𝔪.places (𝔪.liftFn Ψ) (𝔪.liftFn Ψ') = star Ψ ⬝ᵥ Ψ' / Fintype.card (n → 𝔪.ResRing) := by
 let F := star Ψ * Ψ'; have := (fourier_boxIndicator 0 0 (univ.sum F) (by simp [(AddGroup.addRight_bijective _).sum_comp])).symm.trans ((integral_finsetSum ⊤ fun y _ ↦ (isSchwartzBruhat_liftFn _ (F <| y + ·)).integrableOn continuous_one).trans (sum_eq_card_nsmul (𝔪.reduction_surjective.comp_left.forall.2 fun y ↦ by
  simpa [Pi.add_def, ← 𝔪.reduction_idem_mul (y _), ← map_add, -map_mul] using! setIntegral_add_mem (𝔪.liftFn F) (m := (y ·)) (by simp))))
 simp_all [localInner, F, dotProduct]
def primAddChar := (exists_primitive_residue_addChar ⟨𝔪.reduction_surjective, 𝔪.generator_spec.2.2⟩ forall_psi₀_mul_eq_one_iff).choose
@[simp] lemma primAddChar_reduction : 𝔪.primAddChar (𝔪.reduction x) = psi₀ E (𝔪.generator⁻¹ * x) := by grind [primAddChar]
lemma isPrimitive_primAddChar : 𝔪.primAddChar.IsPrimitive := by grind [primAddChar]
lemma name_char_eq_translate_projOn {s} (V : Space E n s) {f} u : V.name 𝔪.places (𝔪.liftFn (𝔪.primAddChar <| · ⬝ᵥ 𝔪.reduction ∘ u)) f = V.ϱ (finVec (star (idem 𝔪.places • 𝔪.generator⁻¹.1 • (↑) ∘ u))) (V.projOn 𝔪.places f) := by rw [star_smul, (by aesop : star _ = idem 𝔪.places.conjClosure * star (idem 𝔪.places)), mul_smul, ← name_schrodingerAct_boxIndicator, IsSchwartzBruhat.schrodingerAct_star] <;> congr! <;> simp [disjoint_places_star, dotProduct, ← map_mul, ← map_sum, mul_sum]; ac_nf
