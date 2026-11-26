import Lib.Weil.Fock.EntireTheta
open IsLocallyConstant Matrix Submodule
variable {E} [Field E] [CMType E] [WeilData E] {n}
  [Fintype n] {s} {V : Space E n s} {f} (x)
namespace Space
noncomputable def finitePart (V : Space E n s) := span ℂ (.range (V.finHeisOp · V.vacElem))
@[simp] lemma vacElem_mem_finitePart : V.vacElem ∈ V.finitePart := subset_span ⟨0, by simp⟩
lemma finHeisOp_mem_finitePart : f ∈ V.finitePart → V.finHeisOp x f ∈ V.finitePart := by
  apply span_induction <;> aesop (add simp [finHeisOp_finHeisOp, finitePart])
attribute [local simp] add_mem stdLattice.semichar projOn_finHeisOp integrated_finHeisOp
  finHeisOp_mem_finitePart smul_mem
lemma rho_finVec_mem_finitePart : f ∈ V.finitePart → V.ϱ (finVec x) f ∈ V.finitePart :=
  (smul_mem_iff _ (Circle.coe_ne_zero _)).1 ∘ finHeisOp_mem_finitePart x
@[simp] lemma projReal_of_mem_finitePart : f ∈ V.finitePart → V.projReal f =
  f := by apply span_induction <;> aesop
lemma isLocallyConstant_rho_finVec : f ∈ V.finitePart → IsLocallyConstant fun x ↦
  V.ϱ (finVec x) f := by
  apply span_induction <;> simp_all [of_constant, comp₂]
  refine fun z ↦ (iff_exists_open _).2 fun x ↦
    ⟨_, (stdLattice.isOpen_stdLattice.preimage_of_continuous (f := (x - ·))).and
    ((isLocallyConstant_psi₀ {_}).preimage ?_), ⟨by simp, rfl⟩, fun d h ↦ by
    nth_rw 1 [← finHeisOp_vacElem h.1]
    simp [finHeisOp, ↓rho_finVec, smul_smul, ← AddChar.map_add_eq_mul]
    rw [h.2]; ring⟩
  fun_prop
lemma projOn_mem_finitePart {S} : f ∈ V.finitePart →
  V.projOn S f ∈ V.finitePart := by apply span_induction <;> aesop
lemma omega_mem_finitePart g : f ∈ V.finitePart → V.ω (1, g) f ∈ V.finitePart := by
  apply span_induction <;> simp_all (maxDischargeDepth := 5) [omega_vacElem_sum, finsum_induction]
lemma exists_eq_smul_omega_vacElem {g} (hf : f ∈ V.finitePart) (h : ∀ y ∈ stdLattice E n,
  V.finHeisOp (g.1.1 *ᵥ y) f = f) : ∃ c : ℂ, f =
  c • V.ω (1, g) V.vacElem := ⟨V.dataInner V.vacElem (V.ω g⁻¹ f), by simp +contextual [← map_smul,
  dataInner_vacElem_smul_vacElem, hf, map_projOn_eq_const, omega_mem_finitePart,
  rep_apply_apply, by simpa using (congrArg (V.ω g⁻¹) <| h · ·)]⟩
lemma eventually_omega_eq_self : f ∈ V.finitePart → ∀ᶠ k in nhds 1, V.ω (1, k) f = f := by
  apply span_induction <;> simp <;> intros <;> try apply Filter.EventuallyEq.comp₂ <;> tauto
  filter_upwards [((isLocallyConstant_rho_finVec V.vacElem_mem_finitePart).comp_continuous (f :=
    (·.1.1 *ᵥ ‹_›)) (by fun_prop)).eventually_eq 1, isOpen_Kf.mem_nhds (by simp)]
  simp_all [finHeisOp, @ω_of_mem_Kf (S := ⊤)]
attribute [irreducible] finitePart
