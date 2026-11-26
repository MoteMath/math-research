import Lib.GaloisRep.Main.SphericalAllRanks
noncomputable section
open NumberField Filter Submodule Set Gf Algebra Classical Fintype Module NormedField
section
variable {ℓ} [ThePrime ℓ] [PadicIso ℓ]
def EllAdicIntegers : Type := intQpBar ℓ deriving CommRing, Algebra _ (PadicAlgCl ℓ)
instance : Algebra EllAdicIntegers ℂ := (ιℓ.symm.toRingHom.domRestrict _).toAlgebra
lemma iota_ell_algebraMap a : ιℓ (algebraMap EllAdicIntegers _ a) = algebraMap EllAdicIntegers _ a := ιℓ.right_inv _
def endPreserving {W} [AddCommGroup W] [Module ℂ W] [Module EllAdicIntegers W] [IsScalarTower EllAdicIntegers ℂ W] (M : Submodule EllAdicIntegers W) : Subalgebra EllAdicIntegers (Module.End ℂ W) := by use! {T | ∀ f ∈ M, T f ∈ M} <;> aesop
variable {E n} [Field E] [CMType E] [Fintype n] {V : Space E n 1} {κ}
def localGroupAlgebra (w : FinPlace E) := adjoin EllAdicIntegers (V.formTranslation κ '' supportedOn n {w})
variable (V κ)
def eigenformsAt w (t : ℕ → ℂ) := ⨅ hw, sphericalAt (V.formTranslation κ) w ⊓ ⨅ j, (heckeSplit (V.formTranslation κ) (w := w) hw j).eqLocus (t j • .id)
def Isotypic := {x : Submodule ℂ _ // ∃ t : _ → _, ∀ f, f ∈ x ↔ ∀ᶠ w in cofinite, f ∈ eigenformsAt V κ w (t w)}
variable {V κ S a f v w t} (x : Isotypic V κ)
lemma commute_of_mem_localGroupAlgebra (ha : a ∈ localGroupAlgebra w) {y} (h : y ∈ trivialOn n {w}) : Commute (V.formTranslation κ y) a := commute_of_mem_adjoin_of_forall_mem_commute ha fun | _, ⟨_, m, rfl⟩ => (commute_supportedOn_trivialOn m h).symm.map _
lemma heckeFun_mem_localGroupAlgebra {G} [Group G] hw (θ : G →* _) {K s} : heckeFun (((V.formTranslation κ).comp (atSplit (w := w) hw)).comp θ) K (indicator s 1) ∈ localGroupAlgebra w := by apply finsum_induction <;> simp_all [indicator, localGroupAlgebra, ← range_atSplit] <;> bound
lemma hasHeckePolyAt_of_mem_eigenformsAt (h : f ∈ eigenformsAt V κ w t) hw : HasHeckePolyAt f.1 w hw (heckePoly w.q (card n) t) := by simp_all [hasHeckePolyAt_iff, eigenformsAt]; lia
lemma exists_isotypic_of_isSphericalOff {P} (h : IsSphericalOff S f.1 P) : ∃ x : Isotypic V κ, f ∈ x.1 ∧ f ≠ 0 := by choose! _ _ _ t _ using (by simpa [IsSphericalOff, hasHeckePolyAt_iff, -mem_levelSpace] using h); use ⟨.ofLinearComb {f | ∀ᶠ w in cofinite, f ∈ eigenformsAt V κ w (t w)} ⟨0, by simp⟩ fun _ a _ b _ _ ↦ a.out.mp (.mono b (by bound)), t, by tauto⟩, (eventually_notMem_star_notMem 1 S).mono (by simp_all [eigenformsAt, -mem_levelSpace])
namespace Isotypic
abbrev heckeEigenvalues := x.2.choose
abbrev heckePolyAt w := heckePoly w.q (card n) (x.heckeEigenvalues w)
def galRep [Algebra E Ω] := epsilon (Attached (n := n) x.heckePolyAt)
variable {x}
lemma mem_iff_eventually : f ∈ x.1 ↔ ∀ᶠ w in cofinite, f ∈ eigenformsAt V κ w (x.heckeEigenvalues w) := by grind
lemma map_mem (ha : a ∈ localGroupAlgebra v) (h : f ∈ x.1) : a f ∈ x.1 := mem_iff_eventually.2 (by peel (mem_iff_eventually.1 h).and (eventually_notMem_star_notMem 1 {star v}); have C g (m : g ∈ supportedOn n {‹_›}) : _ = V.formTranslation κ g _ := congr($(commute_of_mem_localGroupAlgebra ha (by simp_all [eq_comm])) f).symm; simp_all [eigenformsAt, ← map_heckeSplit _ _ a, ← C])
lemma isEigenform [StablyUnram E] (h : f ∈ x.1) (h0 : f ≠ 0) : IsEigenform f.1 x.heckePolyAt := ⟨by simpa, (mem_iff_eventually.1 h).mono fun _ h ↦ (⟨isSplit_of_q_prime ·, hasHeckePolyAt_of_mem_eigenformsAt h _⟩)⟩
lemma iSupIndep_val {s : Set (Isotypic V κ)} : iSupIndep (·.1.1 : s → _) := let I := iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero; (I _).2 fun s v h ↦ (I _).1 (.comp (.iInf _ fun w : Subtype _ ↦ .iInf _ (heckeSplit (V.formTranslation κ) w.2.1 · |>.eigenspaces_iSupIndep)) (f := (·.1.heckeEigenvalues ·.1)) fun x y e ↦ x.ext (x.1.ext (ext fun _ ↦ (mem_iff_eventually.iff mem_iff_eventually).2 (eventually_congr ((s.eventually_all.2 (mem_iff_eventually.1 ∘ h ·)).mono fun w h ↦ congr(_ ∈ $(iInf_congr (congrFun e ⟨w, And.intro · h⟩ ▸ rfl)))))))) s v (by simp_all [eigenformsAt])
lemma attached_galRep [Algebra E Ω] [Nonempty n] [V.IsStd] [WeilData E] (h : f ∈ x.1) (h0 : f ≠ 0) : Attached x.heckePolyAt x.galRep := epsilon_spec (sphericalCompat_std ofNonempty (‹V.IsStd›.eq_stdSpace ▸ f.2) (isEigenform h h0)).1
end Isotypic
end
variable {ℓ} [ThePrime ℓ] [PadicIso ℓ] (E J : Type) {n} [Field E] [CMType E] [Fintype n] (V : Space E n 1) (κ m)
structure TaylorWilesPlaces (E J : Type) [Field E] [NumberField E] [IsCMField E] (m : _) [Algebra E Ω] where
 frobData : J → FrobeniusDatum E
 apart : IsConjApart (frobData · |>.w)
 dvd_q_sub_one j : m ∣ (frobData j).w.q - 1
variable {E J}
abbrev TaylorWilesPlaces.w {E J : Type} [Field E] [NumberField E] [IsCMField E] {m} [Algebra E Ω] (Q : TaylorWilesPlaces E J m) j := (Q.frobData j).w
attribute [instance] TaylorWilesPlaces.apart
structure BaseLevel where
 S : Finset (FinPlace E)
 Y : Submodule ℂ (V.forms κ)
 map_mem_Y T : (∀ k : Kf E n, Commute (V.formTranslation κ (componentOn n S k)) T) → Y ≤ Y.comap T
 exists_level : ∃ K χ, K.IsOpen ∧ Y ≤ levelSpace (.comp (V.formTranslation κ) (componentOn n S)) K χ
 card_aut_dvd g : Nat.card (classAut V.Γf (Kf ..) g) ∣ m
variable {V κ m} {D : BaseLevel V κ m} (L : J → _)
namespace BaseLevel
def ellIntegralForms : Submodule EllAdicIntegers (V.forms κ) := by use! {f | ∀ g ∈ integralAbove n ℓ, ∀ i, ιℓ (f.1 g i) ∈ valuation.integer} <;> simp_all [add_mem, Algebra.smul_def, iota_ell_algebraMap]; exact fun c _ _ h _ m _ ↦ mul_mem c.2 (by tauto)
lemma localGroupAlgebra_le_endPreserving {w} (l : ↑ℓ ∉ w.1) : localGroupAlgebra w ≤ endPreserving (W := V.forms κ) ellIntegralForms := adjoin_le fun | _, ⟨_, _, rfl⟩, _, h, _ => h _ ∘ by simp_all [localLevel, (· ▸ l : _ = w → _).mt]
abbrev repOff := (V.formTranslation κ).comp (componentOn n (.conjClosure D.S)ᶜ)
abbrev formsOfLevel := D.Y ⊓ levelSpace D.repOff (levelOf L ⊥)
def Eigensystem := {x : Isotypic .. | ∃ f ∈ x.1 ⊓ D.formsOfLevel L, f ≠ 0}
def IsOffLevel {ℓ} [ThePrime ℓ] w := w ∉ D.S ∧ star w ∉ D.S ∧ ↑ℓ ∉ w.1 ∧ ∀ x ∈ D.Eigensystem L, x.1 ⊓ D.formsOfLevel L ≤ eigenformsAt V κ w (x.heckeEigenvalues w)
lemma repOff_eq_of_mem_trivialOn k (h : k ∈ trivialOn n D.S) : D.repOff k = V.formTranslation κ k := .symm (congrArg _ (k.ext (by simp_all [← supportedOn_compl])))
@[reducible] def FormEnd {ℓ} [ThePrime ℓ] [PadicIso ℓ] := End ℂ (D.formsOfLevel L) deriving Semiring, Ring, Algebra EllAdicIntegers
abbrev integralEnd : Subalgebra EllAdicIntegers (D.FormEnd L) := endPreserving (ellIntegralForms.comap ((formsOfLevel L).subtype.restrictScalars EllAdicIntegers))
lemma formsOfLevel_base_le : D.formsOfLevel ![] ≤ D.formsOfLevel L := by aesop_cat (add simp mem_levelOf)
