import Lib.GaloisRep.Main.AvatarCompatibility
import New.Exchange.TriangleLevelExponent
open Matrix.GeneralLinearGroup Polynomial Units AlgHeckeChar WeilData AutChar.HasWeight
variable {P} (D : Data P) (ℓ) [ThePrime ℓ]
noncomputable instance : UnramCMField D.E := {((cycloField _).val.comp P.toCycloField).toAlgebra with}
lemma Data.z9 x : algebraMap D.E Ω x ∈ cycloField D.cycloConductor := Subtype.prop _
abbrev AbsGal := Gal(Ω/D.E)
def placesAboveG := {v : FinPlace D.E | ∃ i, ↑(D.g i) ∈ v.1}
noncomputable def badPlaces := (finite_natCast_mem (K := D.E) (ℓ * (D.gProd * D.N))).toFinset
@[grind .] lemma placesDividing_union_subset_badPlaces w : w ∈ placesDividing _ ℓ ∪ placesAboveG D → w ∈ badPlaces D ℓ := by simp_all [badPlaces, placesAboveG, placesDividing, Data.gProd, w.2.mul_mem_iff_mem_or_mem, or_imp]
variable {D ℓ}
@[simp, grind =] lemma star_mem_placesAboveG {v} : star v ∈ placesAboveG D ↔ v ∈ placesAboveG D := by simp [placesAboveG]
lemma s23_z8 {x y : PadicAlgCl ℓ} {N : ℕ} : x ^ N = 1 → y ^ N = 1 → x ≠ y → ‖(N : PadicAlgCl ℓ)‖ ≤ ‖x - y‖ := by grind [=_ valuation_intQpBar_le_iff, eq_of_pow_eq_one_of_val_sub_lt]
@[fun_prop] lemma continuous_cycInv : Continuous (cycInv ℓ D.E (PadicAlgCl ℓ)) := continuous_coe_inv.comp continuous_cycCharIn
lemma s23_w6 (x : FrobeniusDatum D.E) (h : ↑ℓ ∉ x.w.1) : cycInv ℓ _ (PadicAlgCl ℓ) x.frob = x.w.q := by simp_all [cycInv, ← map_inv, x.isFrob.cycChar_eq ℓ, x.isPlaceOver.valuation_natCast_eq_one_iff]
variable [PadicIso ℓ] {a : AutChar D.E} {e ψ} (h : a.HasWeight e ψ) (k j : ℤ)
noncomputable def Data.TameChar.invAvatar (ϑ : D.TameChar) : AbsGal D →* PadicAlgCl ℓ := (coeHom _).comp (ϑ.hasWeight.inv.toAlgebraic 0 0).avatar
lemma g6 : ∀ g, let μ := (h.toAlgebraic k j).avatar
  μ (conjGal g) * μ g = cycCharIn _ Ω ℓ g ^ (2 * j - k) := (dense_of_mostFrobenii (eventually_mostFrobenii (eventually_notMem_star_notMem ℓ h.1.toFinset) fun x _ ↦ by
  obtain _ := upsilon_atUnif_mul_star (star x.w), x.isFrob, x.isFrob.conjPlace_conjGal, @h.atUnif_star
  simp_all [← val_inj, avatar_frob _ x.isPlaceOver, avatar_frob _ x.isPlaceOver.conjPlace_star, charUnramifiedAt_toAlgebraic, congr(ψ $(star_star x.w) = 1)]
  simp [toAlgebraic, HeckeChar.atUnif, heckeCoeff] at *; simp [*, field, sq, ← mul_zpow, ← map_mul, ← Complex.ofReal_mul, ← s23_w6, cycInv])).induction (fun _ ↦ id) (by apply isClosed_eq <;> fun_prop)
lemma f7 {w A f} (b : ψ (star w) = 1) (c : w.IsSplit) : let T := faithfulChar (ResField w); IsLabelledAt A T f (PolyKillsAt ((scalar (Fin 1)).comp (h.toAlgebraic k j).avatar) A) (X - C (charName T (ψ w)).1) := fun s y hy ↦ by
  choose x a b H using (avatarCompatAt_of_stablyUnram (h.toAlgebraic k j) hy.1).2.2 s 0 bot_le (inv_mem hy.2.2.1); simpa [*, hy.pow_apply_charName _ a b, toAlgebraic, baseChange_finPart_locIdele, charUnramifiedAt_upsilon ..] using H
lemma s23_q2 {P} {D : Data P} {ϑ L} (h : L = D.levelPlaces ϑ) i : D.IsChosen (L.chosenPlace i) ∧ ϑ.ψ (L.chosenPlace i) = 1 ∧ L.chosenPlace i ∈ placesAboveG D := by rcases L, h with ⟨⟨⟩, ⟨⟩⟩; grind [Data.chosen, placesAboveG, → D.levelNorm_mem_and_notMem_of_mem_Q, Data.IsChosen, ϑ.5]
