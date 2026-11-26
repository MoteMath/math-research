import Lib.Adelic.Unitary.SpaceDefs
noncomputable section
open Filter Gf Matrix MonoidHom
variable {E : Type*} [Field E] [NumberField E] {n : Type*} [Fintype n] (w : FinPlace E)
lemma exists_congruenceGL_subset {s} (h : s ∈ nhds 1) : ∃ M ≠ 0, ∀ g ∈ congruenceGL (Ô E ∙ M.cast) (@_root_.id n), g ∈ s := ((((nhds 0).hasBasis_smallSets.comap _).frequently_iff.2 fun _ ↦ .imp (by aesop_cat) ∘ mem_nhds_zero_finAdele_iff.1).and_eventually (eventually_congruenceGL_subset map_comap_le h)).exists
attribute [local simp] trivialOn supportedOn cutGL mem_intGL
lemma map_evalAt_cutGL S [Decidable (w ∈ S)] (g : GL n _) : (cutGL (idem_mul_self S) g).map (evalAt w) = ite (w ∈ S) (g.map (evalAt w)) 1 := by aesop
lemma mem_intGL_Ô {g} : g ∈ intGL n (Ô E) ↔ ∀ w, g.map (evalAt w) ∈ Kw .. := by simp_all [Ô, ← map_inv, iff_def]
lemma isOpen_Kw : (Kw n w).IsOpen := isOpen_intGL (Valued.isOpen_integer _)
lemma isCompact_Kw : IsCompact (SetLike.coe (Kw n w)) := isCompact_intGL (isCompact_LocInt w)
variable [NumberField.IsCMField E] (hw : _ ≠ w) (g : GL n (LocField w)) (S : Set (FinPlace E)) {g k : Gf E n}
abbrev Set.conjClosure := S ∪ star ⁻¹' S
lemma Set.Finite.cj (h : S.Finite) : S.conjClosure.Finite := h.union h.star
abbrev Set.IsConjDisjoint := Disjoint S (star ⁻¹' S)
namespace Gf
@[fun_prop] lemma continuous_atPlace : Continuous (atPlace (n := n) w) := by simp [atPlace]; fun_prop
@[ext] lemma ext : (∀ w, g.atPlace w = k.atPlace w) → g = k := Subtype.ext ∘ GL_ext_evalAt
lemma atPlace_star {u} {w : FinPlace E} (h : star u = w) : g.atPlace w = ((g.atPlace u)⁻¹.1.map (conjLoc h))ᵀ := congr($(U.inv_val_eq_conjTranspose g⁻¹).map _).trans (evalAt_star_GL ..)
lemma eventually_atPlace_mem_Kw : ∀ᶠ w in cofinite, g.atPlace w ∈ Kw .. := by simpa [-eventually_cofinite, -coe_units_inv] using ⟨(g.1 · · |>.2), (g.1⁻¹ · · |>.2)⟩
lemma _root_.mem_Kf_iff : g ∈ Kf .. ↔ ∀ w, g.atPlace w ∈ Kw .. := mem_intGL_Ô
variable {S : Set (FinPlace E)} {g k : Gf E n} {w w' : FinPlace E}
@[simp] lemma atPlace_star_mem_iff : g.atPlace (star w') ∈ Kw .. ↔ g.atPlace w' ∈ Kw .. := by simp_all [iff_def, ← map_inv, atPlace_star, mem_LocInt]
@[simp low] lemma mem_supportedOn : g ∈ supportedOn n S ↔ ∀ w ∉ S, star w ∉ S → g.atPlace w = 1 := by simp
@[simp low] lemma mem_trivialOn : g ∈ trivialOn n S ↔ ∀ w ∈ S, g.atPlace w = 1 := by simp
lemma atPlace_star_eq_one_iff : g.atPlace (star w') = 1 ↔ g.atPlace w' = 1 := by aesop (add safe Units.ext, simp [(atPlace_star (star_star w')), atPlace_star])
attribute [local grind .] atPlace_star_eq_one_iff mem_trivialOn mem_supportedOn one_mem IsConcreteLE.le_iff mem_Kf_iff star_star
lemma supportedOn_mono {T} : S ⊆ T → supportedOn n S ≤ supportedOn n T := by grind
lemma atPlace_eq_one_or : g ∈ supportedOn n S → k ∈ trivialOn n S → ∀ u, g.atPlace u = 1 ∨ k.atPlace u = 1 := by grind
lemma supportedOn_compl : supportedOn n S.conjClosureᶜ = trivialOn n S := by grind +extAll
lemma commute_supportedOn_trivialOn (hg : g ∈ supportedOn n S) (hk : k ∈ trivialOn n S) : Commute g k := ext (by grind)
lemma eq_of_supportedOn : g ∈ supportedOn n S → k ∈ supportedOn n S → (∀ w ∈ S, g.atPlace w = k.atPlace w) → g = k := by grind +extAll [atPlace_star]
lemma mem_Kf_iff_of_supportedOn : g ∈ supportedOn n S → (g ∈ Kf .. ↔ ∀ w ∈ S, g.atPlace w ∈ Kw ..) := by grind [atPlace_star_mem_iff]
@[simp] lemma _root_.star_idem_conjClosure : star (idem S.conjClosure) = idem S.conjClosure := by simp [star_idem, S.union_comm]
variable (n S) in
def componentOn : Gf E n →* Gf E n := U.cutAt (idem_mul_self S.conjClosure) star_idem_conjClosure
@[simp] lemma atPlace_componentOn : (componentOn n S g).atPlace w' = ite (w' ∈ S.conjClosure) (g.atPlace w') 1 := map_evalAt_cutGL ..
lemma componentOn_mem_supportedOn : componentOn n S g ∈ supportedOn n S := by aesop
lemma componentOn_mem_Kf : g ∈ Kf .. → componentOn n S g ∈ Kf .. := by grind [atPlace_componentOn]
lemma exists_supportedOn_mul_trivialOn S g : ∃ a ∈ supportedOn n S, ∃ b ∈ trivialOn n S, g = a * b ∧ (g ∈ Kf E n → a ∈ Kf .. ∧ b ∈ Kf ..) := ⟨componentOn n S g, by aesop, componentOn n S g⁻¹ * g, by simp_all [componentOn_mem_Kf, mul_mem]⟩
lemma mem_of_Kf_le_of_supportedOn_le {H} (hK : Kf E n ≤ H) (hw : ∀ w, supportedOn n {w} ≤ H) g : g ∈ H := by
 have ⟨S, f, h⟩ := hasBasis_cofinite.eventually_iff.1 g.eventually_atPlace_mem_Kw
 induction S, f using Set.Finite.induction_on generalizing g
 exact hK (by grind)
 grind [g.exists_supportedOn_mul_trivialOn {‹_›}, atPlace_eq_one_or, mul_mem, -mem_supportedOn]
end Gf
variable {S : Finset (FinPlace E)} (hS : ∀ w ∈ S, star w ∉ S) {w : FinPlace E} (hw : _ ≠ w) (g : GL n (LocField w)) {u : FinPlace E}
@[local simp] lemma atPlace_atSplit_of_ne : u ≠ w → star u ≠ w → (atSplit hw g).atPlace u = 1 := by simp_all [atSplit, atPlace, evalAt_star_locGL]
@[simp] lemma atSplit_mem_supportedOn : atSplit hw g ∈ supportedOn n {w} := by aesop
lemma range_atSplit : (atSplit hw).range = supportedOn n {w} := le_antisymm (by aesop_cat) (⟨·.atPlace w, eq_of_supportedOn (by aesop) · (by simp)⟩)
@[simp] lemma atSplit_mem_Kf : atSplit hw g ∈ Kf .. ↔ g ∈ Kw .. := by simp [mem_Kf_iff_of_supportedOn (S := {w}), -supportedOn]
@[fun_prop] lemma continuous_atSplit : Continuous (atSplit (n := n) hw) := .subtype_mk (by simp [Units.continuous_iff, locGL, Function.comp_def, -coe_units_inv]; use ?_ <;> fun_prop) _
def atSplits := noncommPiCoprod (fun w : S ↦ atSplit (n := n) (w := w.1) (by grind)) fun _ _ _ _ _ ↦ commute_supportedOn_trivialOn (atSplit_mem_supportedOn _ _) (by simp (disch := grind))
@[simp] lemma atPlace_atSplits g (w : S) : (atSplits (n := n) hS g).atPlace w = g w := by erw [noncommPiCoprod_apply, ← Finset.mul_noncommProd_erase (a := w)] <;> simp; apply (MonoidHom.ker _).noncommProd_mem; aesop (add safe atPlace_atSplit_of_ne)
lemma atSplits_mem_supportedOn g : atSplits hS g ∈ supportedOn n S := (noncommPiCoprod_range _).trans_le (by simp [range_atSplit, -supportedOn]; grind [mem_supportedOn, IsConcreteLE.le_iff]) ⟨g, rfl⟩
lemma atSplits_mem_Kf g : atSplits hS g ∈ Kf .. ↔ ∀ w, g w ∈ Kw n _ := (mem_Kf_iff_of_supportedOn (atSplits_mem_supportedOn _ _)).trans (Subtype.forall'.trans (by simp))
