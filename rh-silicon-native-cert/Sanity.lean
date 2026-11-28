import Defs
import Solution

namespace SiliconNativeCert

theorem sanity_diag_dom_2x2 :
    IsStrictlyScaledDiagDom (fun i j : Fin 2 => if i = j then 10 else 3) 10 := by
  have h : ∀ i : Fin 2, rowAbsResidual (fun i j => if i = j then 10 else 3) 10 i < 10 := by decide
  exact ⟨by omega, h⟩

theorem sanity_non_pd_rejected :
    ¬ IsStrictlyScaledDiagDom (fun i j : Fin 2 => if i = j then 10 else 12) 10 := by
  intro ⟨_, h⟩
  have h0 := h ⟨0, by omega⟩
  have hf : ¬ (rowAbsResidual (fun i j : Fin 2 => if i = j then 10 else 12) 10 ⟨0, by omega⟩ < 10) := by decide
  exact hf h0

theorem sanity_carry_split_witness :
    isSplitPair 3 2 7 = true ∧ isSplitPair 1 2 3 = false := by
  decide

theorem sanity_psync_inv :
    checkPsyncInv4 tAdd tXorPlusTwiceAnd 0x61 = true := by
  decide

end SiliconNativeCert
