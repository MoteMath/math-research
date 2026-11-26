import Lib.Adelic.Adeles.IdeleHilbert90
import Lib.Adelic.Adeles.AdeleSelfDual
open Set QuotientAddGroup Rat MeasureTheory IsDualFamily
variable {E} [Field E] [NumberField E] [NumberField.IsTotallyComplex E] [PlaceEmbedding E]
instance : Infinite (FinPlace E) := .of_surjective _ (HeightOneSpectrum.primesEquiv.surjective.comp (FinPlace.comap_surjective (castHom _)))
noncomputable abbrev idemAdele S := ((0, idem S) : 𝔸 E)
private lemma sa {S} (h : S.Nonempty) x : x ∈ (toAdele (E := E).toAddMonoidHom.coprod (.mul (idemAdele S))).range.topologicalClosure := have := @AddSubgroup.isClosed_topologicalClosure; (eq_zero_iff x).1 (by_contra (separatesPoints_continuous_of_t35Space · |>.rec fun f ⟨a, b⟩ ↦ by
 have k p y := congrArg f (mk_add_of_mem y (subset_closure ⟨p, rfl⟩))
 have := isDualFamily_ratAdeles.eq_zero_of_coeff (F := fun x ↦ f (mk x) - ⨍ q : _ ⧸ ratAdeles E, ↑(f q.out) ∂.addHaarMeasure ⊤) ⟨by continuity, by simpa [ratAdeles, add_comm] using (k ⟨·, 0⟩)⟩ fun i e ↦ by simp [by simpa [h.some_mem] using congr(Valued.v ($(eq_zero_of_forall_stdAddChar_eq_one fun u ↦ Circle.ext (mul_rotate' u .. ▸ e _ 1 (by simpa using k (0, u)) :)).2 h.some)), quotMean, integral_sub_average]
 simpa -dsimp [b, ← this 0] using this x))
lemma denseRange_Φ : DenseRange (.pi Φ : E →+* _) := (MapsTo.closure (by aesop) continuous_fst <| sa univ_nonempty ⟨·, 0⟩)
lemma denseRange_rat_matrix_add {E m n : Type*} [Field E] [CMType E] [Fintype n] {S} (h : S.Nonempty) (x : GL n (𝔸 E)) : DenseRange fun p : Matrix n m E × _ ↦ x⁻¹.1 * p.1.map toAdele + idemAdele (E := E) S • p.2 := (x.1.invOf_mul_cancel_left · ▸ map_mem_closure (by fun_prop) (DenseRange.piMap (fun _ ↦ .piMap fun _ ↦ sa h) _) fun | _, ⟨_, rfl⟩ => ⟨(_, _), ((x.2.mul_add ..).trans (congrArg _ (x.2.mul_smul ..))).symm⟩)
