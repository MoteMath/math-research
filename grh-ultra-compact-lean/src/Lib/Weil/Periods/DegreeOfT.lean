import Lib.Weil.Periods.FiniteBesselGroup
noncomputable def ideleLogVal {E} [Field E] [NumberField E] (x : (𝔸f E)ˣ) w := (Valued.v (x.1 w)).log
attribute [-instance] IsAddTorsionFree.of_isDomain_charZero instCharZeroOfIsSemireal
attribute [local simp] HasDegreeGe Grading.stringMap Grading.mem_besselGroup_iff entrywise
variable {E ι ι' X X' : Type} [Field E] [CMType E] [Fintype ι] [Fintype ι'] [Fintype X] [Fintype X'] {s ε ε' N} {V : Space E ι ε} {V' : Space E ι' ε'} (Y : Grading V N X s) {Y' : Grading V' N X' (s - 1)}
omit [Fintype X] [Fintype X'] in
lemma Grading.hasDegreeGe_neg_one_stringMap : HasDegreeGe Y'.gradeOf Y.gradeOf (-1) (Y.stringMap Y') := by simp [reindex_equiv Y.indexEquiv, reindex_equiv Y'.indexEquiv]; lia
lemma Grading.hasDegreeGe_zero_mul_stringMap_mul_sub {g δ} : g ∈ Y.besselGroup → δ ∈ Y'.besselGroup → HasDegreeGe Y'.gradeOf Y.gradeOf 0 (V'.ratCoordMatrix δ * (Y.stringMap Y' * V.ratCoordMatrix g) - Y.stringMap Y') := by
 simp [reindex_equiv Y.indexEquiv, reindex_equiv Y'.indexEquiv]
 repeat' first | intro _ | constructor | grind [Finset.sum_eq_zero] | rw [Fintype.sum_eq_single ‹_›]
lemma Grading.formAdjoint_stringMap_mul_stringMap : V.formAdjoint V' (Y.stringMap Y') * Y.stringMap Y' = Y.shift ∧ (Y'.c = Y.c → Y.stringMap Y' * V.formAdjoint V' (Y.stringMap Y') = Y'.shift) := by
 cases s <;> simp [reindex_equiv Y.indexEquiv, reindex_equiv Y'.indexEquiv, Fin.sum_univ_castSucc, shift, ne_of_lt, apply_ite toAdele, Fin.forall_fin_succ', Fin.val_inj]
 simp [Y.formAdjoint_apply Y', apply_ite star, gradedGram, stringReversal]; grind -etaStruct (splits := 20) [Y.3]
