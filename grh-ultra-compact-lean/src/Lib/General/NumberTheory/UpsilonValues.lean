import Lib.ClassField.HeckeCharacter.CharacterDefs
import Lib.Adelic.Unitary.CongruenceLevel
open Ideal NumberField Valued WithZero IsDedekindDomain.HeightOneSpectrum
variable (E) [Field E] [CMType E]
class SplittingChar where
  υ : HeckeChar E
  υ_unit x : x.map (.snd ..) ∈ (Ô E).units → υ.1 x = ∏ w, x.1.1 w / ‖x.1.1 w‖
  υ_star x : υ.1 (star x) = (υ.1 x)⁻¹
class WeilData extends StablyUnram E, SplittingChar E where
  j : E
  star_j : star j = -j
  im_pos w : 0 < (Φ w j).im
  α : (𝔸f E)ˣ
  self_dual w : v ((j * α.1 * star ↑α) w) = .exp (multiplicity w.1 (differentIdeal ℤ _))
  isIntegral_traceOne : IsIntegral ℤ ((1 - j⁻¹) / 2)
  υ_inert w : star w = w → υ.atUnif w = -1
attribute [simp] WeilData.star_j
namespace WeilData
export SplittingChar (υ υ_unit υ_star)
variable [WeilData E]
@[simps! -isSimp val_fst val_snd] noncomputable def scaleIdele : (𝔸 E)ˣ := MulEquiv.prodUnits.symm
  (MulEquiv.piUnits.symm fun w ↦ .mk0 ↑(√(2 * .pi * _))⁻¹ (mod_cast by positivity [im_pos w]), α)
variable {E}
def traceOne : E := (1 - j⁻¹) / 2
@[grind .] lemma j_ne_zero : (j : E) ≠ 0 := by cases ‹_›; aesop
attribute [local simp] mem_span_singleton dvd_def locFullIdele
lemma _root_.exists_reduction_and_idele_generator {E : Type*} [Field E] [NumberField E] {I} (hI : I ≠ ⊥) : ∃ ρ : Ô E →+* _ ⧸ I, (∀ a, ρ (algebraMap (𝓞 E) _ a) = a) ∧ (∀ {x}, ρ x = 0 ↔ x ∈ I.map (algebraMap ..)) ∧ ∃ t : _ˣ, (t.1 ∈ Ô E ∧ (∀ w, ¬I ≤ ↑w → t.1 w = 1) ∧ ∀ x, ρ x = 0 ↔ t⁻¹.1 * x ∈ Ô E) ∧ (∀ w, v (t.1 w) = .exp (-multiplicity w.1 I)) ∧ ∀ y, (∀ c ∈ I, c • y ∈ Ô E) ↔ t.1 * y ∈ Ô E := by
  obtain ⟨⟨t, _⟩, a, ha, h⟩ := exists_idele_eq_uniformizer_zpow (-multiplicity ·.1 I)
   ((finite_factors hI).subset fun w hw ↦ by_contra fun h ↦
   hw (by simp [multiplicity_eq_zero_of_not_dvd h])), I.ne_bot_iff.1 hI
  have k : under _ (span {(⟨t, ?m⟩ : Ô E)}) = _ := .trans (ext (by simp [*, Subtype.ext_iff, exists_eq_mul_iff_v_le, maxPowDividing_eq_pow_multiplicity, valuation_of_algebraMap, ← intValuation_le_pow_iff_mem])) (iInf_maxPowDividing_eq hI); have := k ▸ map_under_Ô h (k.ge ha)
  use (RingEquiv.ofBijective _ (bijective_quot_Ô h k ha)).symm.toRingHom.comp (Ideal.Quotient.mk
   _), ?_, ?_, t, ?_, ?_, fun y ↦ by simpa [map_le_iff_le_comap] using! congr($this ≤
   (Subalgebra.toSubmodule ⟨_, (·.2)⟩).comap (.toSpanSingleton ..))
  all_goals simp +contextual [*, RingEquiv.symm_apply_eq, ← dvd_iff_le, multiplicity_eq_zero_of_not_dvd, mem_Ô, Quotient.eq_zero_iff_mem, ← t.inv_mul_eq_iff_eq_mul, ← log_le_log]
variable {E : Type*} [Field E] [CMType E] [SplittingChar E] (x : Eˣ) (w : FinPlace E)
lemma _root_.upsilon_toAdele : υ.1 (x.map (toAdele (E := E)) : (𝔸 E)ˣ) = 1 := υ.2 _ ⟨x, rfl⟩
lemma _root_.upsilon_eq_prod_mul_of_v_eq {x : (𝔸 E)ˣ} y (h : ∀ w, v (x.1.2 w) = v (y.1 w)) : υ.1 x = (∏ w, x.1.1 w / ‖x.1.1 w‖) * υ.1 (finIdeleIncl y) := by
  simpa [mul_inv_eq_iff_eq_mul₀] using υ_unit (x * finIdeleIncl y⁻¹) (coe_idelesUnitOff_empty.le
   (by simpa [idelesUnitOff, Units.ext_iff, field]))
lemma _root_.upsilon_eq_atUnif_zpow {x : (𝔸 E)ˣ} (h : ∀ u ≠ w, v (x.1.2 u) = 1) : υ.1 x = (∏ w, x.1.1 w / ‖x.1.1 w‖) * υ.atUnif w ^ (-log (v (x.1.2 w))) := by simpa using! upsilon_eq_prod_mul_of_v_eq (locIdele w (_⁻¹ ^ (v (ideleAt w (x.map (.snd ..))).1).log)) (by simp +contextual [← and_forall_ne w, h, -map_inv]; rfl)
lemma _root_.upsilon_atUnif_mul_star : υ.atUnif w * υ.atUnif (star w) = 1 :=
  have := upsilon_eq_atUnif_zpow (star w) (x := star (locFullIdele w (uniformizer w))); by simp_all
   [υ_star, star_singleAdele, HeckeChar.atUnif, HeckeChar.finPart, locIdele, field]
