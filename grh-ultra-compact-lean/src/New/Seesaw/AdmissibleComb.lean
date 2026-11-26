import Lib.CM.Sigma.PadicSeriesDefs
import Lib.Weil.Periods.DegreeAndUnipotent
import Lib.Adelic.CuspForms.ClassReps
import Lib.ClassField.HeckeCharacter.SplittingCharOnU1
import Lib.Weil.DualPair.PairSplitting
import Lib.Weil.DualPair.TwoEdgesOnePair
section
open Matrix
noncomputable def gradedLatticeBasis {R X' ι : Type*} {s} [CommRing R] [StarRing R] (e : (X' ⊕ Unit) ⊕ Fin s ≃ ι) (a π : Rˣ) (u : unitary R) := reindex e e (fromBlocks (ite (Odd s) (diagonal (1 ⊕ᵥ fun _ ↦ (star π)⁻¹.1)) 1) 0 (of fun b ↦ 0 ⊕ᵥ fun _ ↦ ite (b = b.rev) (u * (star π * π)⁻¹.1) 0) (diagonal fun b ↦ u * ite (Odd s) 1 (ite (2 * b < s) a⁻¹.1 (star a))))
variable {E X' ι : Type*} [Field E] [CMType E] (q : ℕ)
def Grading.Q0 [Fintype ι] {ε s N} {V : Space E ι ε} (Y : Grading V N (X' ⊕ _) s) a π u := ∃ k ∈ intGL ι (Ô E), V.xFin.1 = gradedLatticeBasis Y.indexEquiv a π u * k.1
def integralAway n := (by use! {z | ∀ l [Fact l.Prime], l.Coprime n → ∀ ι : _ →+* ℂ_[l], ‖ι z‖ ≤ 1} <;> simp <;> grind [mul_le_one₀, IsUltrametricDist.norm_add_le_max] : Subring ℂ)
structure IsAdmissibleCoeffs {X} (A : Set X) (n d : ℕ) (p : Prop) B (r : X →₀ ℂ) where
  support_subset : ∀ x ∈ r.support, x ∈ A
  integral x : d * r x ∈ integralAway n
  size_le : p → ∀ σ : ℂ ≃+* ℂ, r.sum (fun _ ↦ (‖σ ·‖)) ≤ B
section
variable {E ι : Type*} [Field E] [NumberField E] (q : ℕ)
def s22_q1 (d : ι → 𝔸f E) : AddSubgroup (ι → 𝔸f E) := ⟨⟨⟨{x | ∀ i (w : FinPlace E), ↑q ∉ w.1 → Valued.v
  ((d i * x i) w) ≤ 1}, by simp_all [-map_mul, mul_add, Valued.v.map_add_le]⟩, by simp⟩, by simp⟩
abbrev translations ι q d := s22_q1 (E := E) q fun _ : ι ↦ d
end
def IsSplitSquarefree (P : Finset (FinPlace E)) (N : E) (π : (𝔸f E)ˣ) := ↑N = π * star π.1 ∧ ∀ w, Valued.v (π.1 w) = ite (w ∈ P) (.exp (-1)) 1 ∧ (w ∈ P → star w ∉ P)
end
section
variable {E} [Field E] [CMType E] {q l c d k : ℕ} {n} [Fintype n] [Fact l.Prime] {ι : ℂ →+* ℂ_[l]} {g : Gf E n}
lemma div_mem_integralAway (h : c ∣ d * q ^ k) : (d / c : ℂ) ∈ integralAway q := fun l _ c ↦ by
  simp [by simpa [c.norm_natCast_eq_one] using congr(‖($h.choose_spec : ℂ_[l])‖)]; bound
    [natCast_mem (valRingCp l)]
omit [Fact l.Prime] in
lemma w8 (hl : l.Coprime q) : localLevel n {w : FinPlace E
  | ↑q ∉ w.1} ≤ integralAbove n l := fun _ h w ↦ h w ∘ w.2.notMem_of_isCoprime_of_mem hl.cast
lemma Parameters.norm_finMultiplier_eq_one [WeilData E] (hg : g ∈ integralAbove n l) : ‖ι
  (finMultiplier g)‖ = 1 := by simp_all (maxDischargeDepth := 4) [finMultiplier, glMultiplier, WeilData.norm_map_chiFin, localLevel, Gf.atPlace, (norm_adeleExtension_eq_iff _ 1).2, Sat.v_det_saturatingElem rfl ∘ .of_mem, mem_subring_matrix_iff, mem_intGL]
lemma AutChar.HasWeight.norm_padic_det {a : AutChar E} {e ψ s} [ha : a.HasWeight e ψ] (hg :
  g ∈ integralAbove n l) : ‖ι (a.1 (detFin s g))‖ = 1 := by simp [ha.norm_padic_eq_prod, funext_iff, ↓(norm_adeleExtension_eq_iff _ 1).2, mem_intGL_iff_det.1 (hg ..)]
end
section
open Finsupp Function
variable {α α' Z Z'} [AddCommGroup Z] [Module ℂ Z] [AddCommGroup Z'] [Module ℂ Z'] (v : α → Z)
def IsAdmissibleComb A n d p B z := ∃ r, IsAdmissibleCoeffs A n d p B r ∧ z = r.sum fun x ↦ (· • v x)
namespace IsAdmissibleComb
variable {v A} {A' : Set α'} {n d p B z v' d' B' z' s} (h : IsAdmissibleComb v A n d p B z)
attribute [local simp] single_apply smul_smul smul_sum IsAdmissibleCoeffs.mk
lemma of_sum {c : α → ℂ} (hc : ∀ i ∈ s, d * c i ∈ integralAway n) (hB : p → ∀ σ : ℂ ≃+* ℂ, ∑ i ∈ s, ‖σ (c i)‖ ≤ B) : IsAdmissibleComb v s n d p B (∑ i ∈ s, c i • v i) := ⟨indicator s (fun _ ↦ c ·), by simp_all [↓sum_indicator_index, apply_ite]⟩
lemma single x (hx : x ∈ A) : IsAdmissibleComb v A n d p 1 (v x) := ⟨.single x 1, by simp_all [apply_ite]⟩
include h
lemma bind {e C} d' B' (H : ∀ x ∈ A, IsAdmissibleComb v' A' n d' p B' (v x)) (hd :
  d * d' ∣ e := by simp) (hB : p → B * |B'| ≤ C := by simp) : IsAdmissibleComb v' A' n e p C z := by
  obtain ⟨⟨c, hc, ⟨⟩⟩, ⟨⟩⟩ := h, hd; choose! r hr e using H
  use c.support.sum (⇑c • r), ⟨?_, ?_, ?_⟩ <;> intros <;> simp_all [↓← @linearCombination_apply α', sum, hc.1, Finset.mul_sum] <;> (try apply sum_mem) <;> try grind [IsAdmissibleCoeffs, Finset.sum_eq_zero, mul_mem, natCast_mem, mul_comm, mul_assoc]
  grw [← hB, ← hc.3 ⟨⟩, sum_mul, sum, ← le_abs_self, norm_sum_le, Finset.sum_comm, norm_mul_le]
  gcongr
  grw [← (hr _ (hc.1 _ ‹_›)).3 ⟨⟩, mul_sum, ← Finset.sum_filter_ne_zero, sum]; gcongr; aesop_cat
lemma map (L : Z →ₗ[ℂ] Z') : IsAdmissibleComb (L ∘ v) A n d p B (L z) := h.imp (by simp_all [sum])
lemma smul {c} (hc : c ∈ integralAway n) (hc' : p → ∀ σ : ℂ ≃+* ℂ, ‖σ c‖ ≤ 1) :
  IsAdmissibleComb v A n d p B (c • z) := (h.map (c • 1)).bind 1 1
  (fun _ ↦ ⟨.single · c, by simp_all [apply_ite]⟩)
lemma q5 {ζ : ℂ} (o : ζ = 0 ∨ IsOfFinOrder ζ) : IsAdmissibleComb v A n
  d p B (ζ • z) := have {R} [NormedField R] (f : ℂ →+* R) := o.elim (by aesop) (f.1.isOfFinOrder ·
    |>.norm_eq_one.le); h.smul (by tauto) fun _ σ ↦ this σ.toRingHom
lemma of_eq_isOfFinOrder_smul : (∀ x ∈ A, ∃ ζ : ℂ, IsOfFinOrder ζ ∧ ∃ y ∈ A', v x = ζ • v' y) → IsAdmissibleComb v' A' n d p B z := (h.bind 1 1 ·) ∘ by grind [q5, single]
lemma map_bilinear {W} [AddCommGroup W] [Module ℂ W] (b : Z →ₗ[ℂ] Z' →ₗ[ℂ] W) (g : IsAdmissibleComb v' A' n d' p B' z') : IsAdmissibleComb (fun x ↦ b (v x.1) (v' x.2)) (A ×ˢ A') n (d * d') p (B * |B'|) (b z z') := (h.map (b.flip _)).bind d' B' fun _ a ↦ (g.map _).bind 1 1 fun _ ↦ (single (_, _) ⟨a, ·⟩)
lemma smul_mem {l} [Fact l.Prime] [PadicPlace l] (hq : l.Coprime n) {M : Submodule embValRing Z}
    (hv : ∀ x ∈ A, v x ∈ M) : (d : ℂ) • z ∈ M := by
  obtain ⟨r, h, ⟨⟩⟩ := h
  simpa using! sum_mem (M.smul_mem ⟨_, h.2 _ l hq _⟩ ∘ hv · ∘ h.1 _)
omit h
lemma pure {α F : ℕ → _} [∀ j, AddGroup (α j)] [∀ j, AddCommGroup (F j)] [∀ j, Module ℂ (F j)] {v : ∀ i, α (2 * i) × α (2 * i + 1) → F i} {A : ∀ _, AddSubgroup _} {f} d B m :
  (∀ i < m, IsAdmissibleComb (v i) (A _ ×ˢ A _) n d p B (f i)) → IsAdmissibleComb (fun y : ∀ _, _ ↦ TensorChain.pure (v · (y _, y _)) m) {y | ∀ j, y j ∈ A j} n (d ^ m) p (|B| ^ m) (TensorChain.pure
  f m) := m.rec (single 0 ∘ by simp) fun m i h ↦ ((i (by grind)).map_bilinear (TensorProduct.mk
  ..).flip (h m .refl)).of_eq_isOfFinOrder_smul fun (s, t, u) _ ↦ ⟨1, .one, update (update s _ t) _
  u, by grind [SetLike.mem_coe], congr($(by simp) ⊗ₜ $(TensorChain.pure_congr (by grind)))⟩
lemma normUnit_smul {C : ℂ} a (hd : d ≠ 0) : IsAdmissibleComb (C • v ·) A n d p B z → IsAdmissibleComb v A n 1 p (d * B) ((normUnit (a * C / d)).1 • a • z) := by
  rintro ⟨r, ⟨⟩, ⟨⟩⟩; convert q5 (ζ := normalize (a * C / d)) ⟨d • r, _, rfl⟩ _ using 1 <;> simp_all
    [sum_smul_index', ← mul_sum, hd.pos, or_iff_not_imp_left, normalize]; field_simp
end IsAdmissibleComb
end
section
open Matrix Complex AddSubgroup Finset
lemma s22_y6 {E n : Type} [Field E] [CMType E] [WeilData E] [Fintype n]
  {s} (V : Space E n s) {q g x A p d C c} (e : c * C = finMultiplier g) (I : ∀ y ∈ stdLattice E n, g *ᵥ (x + y) ∈ A) (hc : (d : ℕ) * (c / ‖finMultiplier g‖ ^ 2) ∈ integralAway q) (hp : p → ∀ σ : ℂ ≃+* ℂ, ‖σ c‖ ≤ 1) : IsAdmissibleComb (C • V.finHeisOp
  · V.vacElem) A q d p 1 (V.ω (1, g) (V.finHeisOp x V.vacElem)) := by
  have := fintypeOfIndexNeZero
    (mod_cast norm_finMultiplier_sq g ▸ pow_ne_zero 2 (by simp [finMultiplier_ne_zero]))
  simp [V.omega_vacElem_sum, e ▸ mul_div_right_comm .., mul_smul, smul_sum, V.finHeisOp_finHeisOp, ← mulVec_add]
  refine .of_eq_isOfFinOrder_smul (.of_sum ?_ ?_) fun y _ ↦ ⟨_, isOfFinOrder_ψf _, _, I _ y.out.2, smul_comm ..⟩ <;> simp_all [relIndex, index, ← ofReal_pow, norm_finMultiplier_sq, field]
end
noncomputable section
section
open stdLattice MatMul Matrix Prod Space
attribute [local simp ←] Matrix.map_mul RingHom.coe_snd Splitting.mixedTerm_zero
attribute [local simp] semichar Splitting.frameAt Splitting.finFrameVector omega_integrated mulVec_finVec finVec.eq_1 rep_apply_apply
variable {E n n₀ p : Type} [Field E] [CMType E] [Fintype n] [Fintype n₀] [Fintype p] {s s₀} {V : Space E n s} {V₀ : Space E n₀ s₀} [WeilData E] (D : V.Splitting V₀ p)
@[local simp] private def z1 := D.zeroTerm ∘L V.integrated (realWeil (blockU (D.exists_isAdapted_and_frame_eq 1).choose.1) vacVector)
unseal finitePart in
lemma s22_j5 : (∀ f ∈ V.finitePart, z1 D f ∈ V₀.finitePart) ∧ ∀ y v, ∃ v₀, ∀ f, D.zeroTerm (V.ϱ y (V.integrated v f)) = V₀.integrated
  v₀ (z1 D (V.finHeisOp (finCoord y) f)) := by
  have h := (D.exists_isAdapted_and_frame_eq 1).choose_spec.1; set g := Exists.choose _
  cases h.mixedTerm_omega_vacElem
  use fun f hf ↦ ((D.zeroTerm ∘L V.ω g).1.map_span_le ..).2
    (by aesop (add simp [rho_finVec_mem_finitePart, finHeisOp,
    ω_ϱ])) ⟨_, omega_mem_finitePart g.2⁻¹ (projReal_of_mem_finitePart hf ▸ hf), by simp [g]⟩,
    (V.exists_rho_integrated_eq · · |>.imp' _ fun w e f ↦ by simpa [e, g] using
    (V.omega_integrated g⁻¹ w _ ▸ (h.exists_real_zeroTerm D.isMixedLaw_mixedTerm).choose_spec .. :))
private lemma q7 b {z w} (h : z = D.finFrameVector 1 1 0 w b) f :
    z1 D (V.finHeisOp z f) = V₀.finHeisOp w (z1 D f) := h ▸ by simp [finHeisOp, ↓Splitting.star_dot_finFrameVector, ← rho_integrated]
lemma s22_m3 M M' {f y} (h : z1 D (V.finHeisOp y f) ≠ 0) (m : M * M'ᴴ = 1)
  (hf : ∀ x ∈ stdLattice E n, V.finHeisOp (M *ᵥ x) f = f) : ∃ l ∈ stdLattice E n, (D.kAdelic.map snd)ᴴ *ᵥ (y - M' *ᵥ l) = 0 := (isValuationPair_Ohat.exists_isPrimitiveMatrix_mul (X := M'ᴴ * D.kAdelic.map snd) ⟨D.kCoord.map snd * M, by simp [← M.mul_assoc, m]⟩).elim fun t ⟨_, hK, L, hL,
  eL⟩ ↦ ⟨_, hL.isInt_conjTranspose.mulVec (mem_stdLattice_iff_psi₀.2 fun x hx ↦ smul_left_injective
  ℂ h (by simpa [by simpa using q7 D (t *ᵥ x) (w := 0) rfl, star_mulVec_dotProduct, m, finHeisOp.eq_1 V₀, ← M.mul_assoc] using congrArg (z1 D) (hf _
  (hK.mulVec hx) ▸ V.finHeisOp_comm y .. :).symm)), mulVec_injective_of_isUnit t.isUnit.star (by
    simpa [mulVec_sub, ← mulVec_mulVec] using! congr($eLᴴ *ᵥ _).symm)⟩
lemma s22_n5 g (c : Matrix p _ (𝔸f E)) {B} (e : B = D.iAdelic.map snd * g.1.1 + D.kAdelic.map snd * c) (hB : IsIntMatrix (Ô E) B) : ∃ C, ∀ y, ∃ ζ, (ζ = 0 ∨ IsOfFinOrder ζ) ∧ z1 D (V.finHeisOp y V.vacElem) = (ζ * C : ℂ) • V₀.ω (1, g) (V₀.finHeisOp (Bᴴ *ᵥ y) V₀.vacElem) := .imp (fun C hC y ↦ by_contra fun H ↦ by
  choose l hx o using by simpa using s22_m3 D 1 1 (H ⟨0, by simpa using ·⟩) (by simp)
                           (by simp_all)
  choose a w b e' using D.exists_eq_finFrameVector 1 1 (y - l)
  obtain ⟨⟨-, rfl⟩, a₂⟩ := by simpa [Sum.elim_eq_iff, o] using
    (e' ▸ Splitting.adjoint_mulVec_finFrameVector .. :)
  exact H ⟨_, .inr ((isOfFinOrder_ψf _).mul (isOfFinOrder_ψf _)), by
    nth_rw 1 [← finHeisOp_vacElem (neg_mem hx), finHeisOp_finHeisOp, map_smul, ← sub_eq_add_neg, q7 D _ e', hC, map_smul, ← show g *ᵥ Bᴴ *ᵥ (y - l) =
      w by simp [e, ← mulVec_mulVec, o, a₂]; simp [← U.inv_val_eq_conjTranspose], ← omega_finHeisOp _ (1, g), ← finHeisOp_vacElem (hB.isInt_conjTranspose.mulVec hx), finHeisOp_finHeisOp]
    simp [mulVec_sub, smul_comm C, mul_smul]; rfl⟩)
  (exists_eq_smul_omega_vacElem ((s22_j5 D).1 _ vacElem_mem_finitePart) fun x
  hx ↦ by rw [← q7 D (c *ᵥ x), finHeisOp_vacElem (hB.mulVec hx)]; simp [e, add_comm])
end
open Finset Fintype Grading Kronecker Matrix Space Splitting
attribute [-simp] Unitary.mul_star_self_of_mem
variable {E ι ι' ι'' X X' X'' X₀ q : Type} [Field E] [CMType E] [WeilData E] [Fintype ι] [Fintype ι'] [Fintype ι''] [Fintype X] [Fintype X'] [Fintype X''] [Fintype X₀] [Fintype q] {ε ε' ε'' s s' s''} {V : Space E ι ε} {V' : Space E ι' ε'} {V'' : Space E ι'' ε''} {N p} (Y : Grading V N X s) (Y' : Grading V' N X' s') {Y'' : Grading V'' N X₀ s''} {w : ι → ℤ} (Y'' : Grading V'' N X₀ s'')
structure GradeZeroPart (V : Space E ι ε) (V'' : Space E _ ε'') (wt : ι → ℤ) where
  index : ι'' ↪ _
  mem_range_index incl : incl ∈ Set.range index ↔ wt incl = 0
  incl : Matrix ι _ E
  incl_eq_zero a b : wt a ≠ 0 → incl a b = 0
  gram_incl : inclᴴ * V.J * incl = V''.J
  grade_add a b : V.J a b ≠ 0 → wt a + wt b = 0
omit [WeilData E] in
lemma c2 g : (V.sum V').ratCoordMatrix (.sum g) = fromBlocks
  (V.ratCoordMatrix g.1) 0 0 (V'.ratCoordMatrix g.2) := by simp [ratCoordMatrix_eq, sum, blockGL]
attribute [local simp] Fintype.card_subtype ratCoordMatrix_inclX diagonal_apply det_inclX entrywise inclMatrix c2
def GradeZeroPart.splitting (Z : GradeZeroPart V V'' w) : V.Splitting V'' {i // 0 < w i} :=
  have := congr((fun M ↦ (trace M, M * V.J⁻¹)) (V.J⁻¹ * $(show diagonal (if 0 < w · then 1 else 0) * V.J = V.J * diagonal fun i ↦ 1 - ite (0 < w i) 1 0 - ite (w i = 0) 1 0 by simp; grind
    [GradeZeroPart])))
  by use inclMatrix E (↑), V.J⁻¹ * inclMatrix E (@Subtype.val ι _), Z.incl <;> simp [↓gram_incl, Matrix.mul_assoc, Z.mem_range_index, V.isHermitian_J.inv.eq, ← @Nat.cast_inj E, ← Fintype.card_range Z.index, trace_mul_comm] at * <;>
    grind [GradeZeroPart, incl_eq_zero, star_zero, Fintype.sum_eq_zero]
def GradeZeroPart.hom (Z : GradeZeroPart V V'' w) (hs' : Even s') (hw : ∀ i, Even (w i)) :
    GradeZeroPart (V'.hom V) ((stdSpace E X').hom V'') fun r ↦ w r.1 - Y'.gradeOf r.2 := by
  use Z.index.prodMap (.trans .inl Y'.indexEquiv.toEmbedding), ?_, Z.incl ⊗ₖ inclMatrix E
    (Y'.indexEquiv ∘ .inl) <;> simp [gram_incl, hom_J, Y'.J_inv_eq_gradedGram] <;> simp [gradedGram, reindex_equiv Y'.indexEquiv] <;> grind [incl_eq_zero, GradeZeroPart]
def s22_v4 := fromRows (V.formAdjoint V' (Y.stringMap Y')) (Y'.stringMap Y'')
def s22_k6 := finCoord (V'.homAtPoint (flipSum V V'') (s22_v4 Y Y' Y''))
omit [WeilData E] in
lemma s22_z5 g g' : V'.ratCoordMatrix (Y'.inclX g') * Y.stringMap Y' * V.ratCoordMatrix (Y.inclX g)⁻¹ = Y.stringMap Y' := by
  simp [← map_inv, stringMap, reindex_equiv Y.indexEquiv, reindex_equiv Y'.indexEquiv]
variable (X'' q) in
structure ArrowPair where
  zeroPart : GradeZeroPart (flipSum V V'') (hypSum q (flipSum (stdSpace E X) (stdSpace E X'')))
    (Y.gradeOf ⊕ᵥ Y''.gradeOf)
  string_spec : Odd s ∧ s' = s - 1 ∧ s'' = s' - 1 ∧ Y'.c = Y.c
  even_card_add : Even (Fintype.card ι + Fintype.card ι'')
  embX : G (n := X₀) E 1 →* G (n := X'') E 1
  det_embX k : (embX k).det = k.det
  intertwines g k : fromBlocks (V.ratCoordMatrix (Y.inclX g)) 0 0
    (V''.ratCoordMatrix (Y''.inclX k)) * zeroPart.incl.map toAdele =
    zeroPart.incl.map toAdele * (G.sum (s := hypSigns q) (1, .sum (g.neg, embX k))).mat
  gradeOne : q ↪ {l // Y'.gradeOf l = 1}
  stackedT_apply a l : s22_v4 Y Y' Y'' (zeroPart.index a) l = ∑ k,
    ite (l = gradeOne k) ↑(zeroPart.incl (zeroPart.index a) (.inl (.inr k)) * Y'.c) 0
variable {Y Y' Y''} (D : ArrowPair X'' q Y Y' Y'')
def ArrowPair.z9 := D.zeroPart.hom Y' (by grind [ArrowPair])
  (by simp [reindex_equiv Y.indexEquiv, reindex_equiv Y''.indexEquiv]; grind [ArrowPair])
def ArrowPair.splitting := D.z9.splitting.comp ((removePlanes q _).homTarget _)
def ArrowPair.m9 := arrowTensor.leftInverse ∘ₗ (z1 D.splitting ∘L finHeisOp _ (s22_k6 Y Y' Y'')).1
lemma ArrowPair.m6 (Φ Ψ : finitePart _) : arrowTensor (D.m9 (arrowProduct Φ Ψ.1)) = z1 D.splitting (finHeisOp _ (s22_k6 Y Y' Y'') (arrowProduct Φ.1 Ψ)) := Function.LeftInverse.rightInvOn_range leftInverse_arrowTensor (range_arrowTensor.ge ((s22_j5 _).1 _ (finHeisOp_mem_finitePart _ (range_arrowTensor.le ⟨Φ ⊗ₜ Ψ, rfl⟩))))
lemma ArrowPair.y3 a b g g' k f :
    D.splitting.zeroTerm (tripleWeil a b (Y.inclX g, Y'.inclX g', Y''.inclX k) f) =
  tripleWeil a b (g, g', D.embX k) (D.splitting.zeroTerm f) := by
  obtain ⟨j, rfl⟩ := D.string_spec.2.1 ▸ D.string_spec.1.tsub_odd odd_one; let w := Y.gradeOf ⊕ᵥ Y''.gradeOf
  let x := G.sum ((Y.inclX g).neg, Y''.inclX k); have : ∀ i l, w i ≠ 0 ∨ w l ≠ 0 → (flipSum V V'').ratCoordMatrix x i l =
    ite (i = l) 1 0 := by simp [w, x, reindex_equiv Y.indexEquiv, reindex_equiv Y''.indexEquiv]
  have Z := zeroTerm_omega_of_inclMatrix D.z9.splitting rfl (g := .onHom (Y'.inclX g', x))
    (g₀ := .onHom (g', .sum (1, .sum (g.neg, D.embX k)))) (u := (g.det * k.det) ^ j * g'.det⁻¹ ^ #{i
    | 0 < w i}) (C := blockDiagonal (if Y'.gradeOf · < 0 then (flipSum V V'').ratCoordMatrix x else 1) * (blockDiagonal (if 0 < w · then (V'.ratCoordMatrix (Y'.inclX g'⁻¹))ᵀ else 1)).submatrix
    .swap .swap) ?_ ?_ (by simp [(det_classical _).symm.trans (det_blockDiagonal _), x, w, ↓reindex_equiv Y'.indexEquiv, ↓@prod_sum_type X', ↓Fin.prod_univ_add, prod_ite, ite_eq_right, ← two_mul, apply_ite Matrix.det, det_ratCoordMatrix, ← Equiv.coe_prodComm, -inv_pow]) ?_
  rcases D.zeroPart.splitting.card_eq, card_congr Y'.indexEquiv, D.2, D.3
  have R r := (removePlanes q (flipSum (stdSpace E X) (stdSpace E X''))).homTarget_zeroTerm_pairWeil
    (stdSpace E X') 1 1 (.sum (1, r)) _ 1 ?_
    (.trans (congrArg _ ?_) ((coord_mul_frame_mul _).2.1 r.mat).2.1)
  simp_all [x, w, pairWeil, inv_smul_eq_iff₀, splitting, zeroTerm_comp, tripleWeil, smul_smul, det_embX, rankTwist, Odd, Even]
  congr 1; exact mod_cast congrArg _ (Additive.ofMul.injective (by simp; match_scalars <;> omega))
  iterate 2 simp [kAdelic, iAdelic, Space.ratMap, removePlanes, hypSum, sum, blockGL, -coe_units_inv]
  all_goals simp [-Sum.forall, ↓reindex_equiv Y'.indexEquiv, ↓@Sum.forall X', ← map_inv, sum_prod_type, HasDegreeGe, blockDiagonal_apply, Matrix.ite_apply, GradeZeroPart.splitting, GradeZeroPart.hom, apply_ite toAdele, -sum_sum_type, z9]
  grind; grind; simp [x, hypSum, ← sum_mul, ← mul_right_comm _ (toAdele _), ← mul_assoc,
    by simpa [-Sum.forall] using D.intertwines g k]
lemma ArrowPair.d2 a b {g g' k k' x} (hx : Y''.inclXFin k = x) (e : D.embX (1, k) = (1, k')) Φ Φ' : D.m9 (arrowProduct (liftWeilFin a (Y.inclXFin g, Y'.inclXFin g') Φ).1 (liftWeilFin b (Y'.inclXFin g', x) Φ').1) = .map (liftWeilFin a (g, g'))
  (liftWeilFin b (g', k')) (D.m9 (arrowProduct Φ Φ')) := by
  erw [← hx, ← leftInverse_arrowTensor (.map _ _ _), arrowTensor_map_liftWeilFin, m6, ← e, ← D.y3, (?_ : Function.Commute (tripleWeil ..) (integrated _ _))]
  simp [m9, z1, finHeisOp, show finVec (s22_k6 Y Y' Y'') = V'.homAtPoint (flipSum V V'') (fromRows (V.formAdjoint V' (((0, 1) :
    𝔸 E) • Y.stringMap Y')) (((0, 1) : 𝔸 E) • Y'.stringMap Y'')) by ext <;> simp [finVec, s22_k6, homAtPoint, matToVec, s22_v4, formAdjoint, Prod.fst_sum, Prod.snd_sum], homHeisOp_arrowProduct, ← arrowProduct_twistedPairWeil, pairWeil_homHeisOp, s22_z5, -ratCoordMatrix_inclX, ← inclX_inr]
  intro; simp [tripleWeil, omega_integrated, inclX_inr, G.onHom_eq, G.sum, G.neg, ← Pi.one_def, MulEquiv.prodCongr]
attribute [local simp ←] Function.Embedding.toFun_eq_coe
attribute [local simp] Function.Injective G.blockEmb stringMap stringReversal Subtype.ext_iff s22_v4 flipSpace gradedGram hypSum
variable (Y Y' Y'') (H : Odd s ∧ s' = s - 1 ∧ s'' = s' - 1 ∧ Y'.c = Y.c) (H' : Even (Fintype.card ι + Fintype.card ι''))
def c3 (h : s ≠ 1) :
  ArrowPair X₀ Unit Y Y' Y'' := let z _ := Sum.inl (Y.indexEquiv (.inr ⟨s / 2, by grind⟩))
  let z' _ := Sum.inr (Y''.indexEquiv (.inr ⟨s'' / 2, by grind⟩))
  let j := Sum.map (Y.indexEquiv ∘ .inl) (Y''.indexEquiv ∘ .inl)
  by use ⟨⟨z ⊕ᵥ z' ⊕ᵥ j, ?_⟩, ?_, fromCols (fromCols ((2 * N)⁻¹ • (inclMatrix E z - inclMatrix E
    z')) (inclMatrix E z + inclMatrix E z')) (inclMatrix E j), ?_, ?_, ?_⟩, H, H', .id _, ?_, ?_, ⟨fun _ ↦ ⟨Y'.indexEquiv (.inr ⟨s'' / 2, by grind⟩), ?_⟩, ?_⟩ <;> simp +zetaDelta
    [↓reindex_equiv Y.indexEquiv, ↓reindex_equiv Y'.indexEquiv, Y.2, ↓reindex_equiv Y''.indexEquiv, ↓Y.formAdjoint_apply Y', Y''.2, apply_ite star] <;> grind [Y.3]
def s22_d6 (e : p * star p = N) (h : s = 1) : ArrowPair (X₀ ⊕ Unit) Empty Y Y' Y'' := let j := isEmptyElim ⊕ᵥ (Sum.inl ∘ Y.indexEquiv ∘ .inl ⊕ᵥ (.inr ∘ Y''.indexEquiv ∘ .inl ⊕ᵥ fun _ ↦ .inl (Y.indexEquiv (.inr ⟨0, h.ge⟩))))
  by use ⟨⟨j, ?_⟩, ?_, of fun a b ↦ ite (a = j b) (ite (b = .inr (.inr (.inr ()))) p⁻¹ 1) 0, ?_, ?_,
    ?_⟩, H, H', .comp (G.blockEmb (e := .refl _) Sum.elim_one_one.symm) (.inl ..), ?_, ?_, .ofIsEmpty <;> simp [j, ↓reindex_equiv Y.indexEquiv, ↓reindex_equiv Y'.indexEquiv, Y.2, ↓reindex_equiv Y''.indexEquiv, ↓Y.formAdjoint_apply Y', Y''.2, apply_ite star, univ_eq_empty] <;> grind [Y.3]
