import Lib.General.LinearAlgebra.BlockMatrices
import Lib.Weil.DualPair.PairReal
lemma exists_level_pairWeil {E n n' s s'} [Field E] [CMType E] [WeilData E] [Fintype n] [Fintype n']
    {S : Space E n s} {T : Space E n' s'} a b {f} (hf : f ∈ (S.hom T).finitePart) :
    ∃ K K' : OpenSubgroup _, ∀ᵉ (k ∈ K) (k' ∈ K'), pairWeil S T a b ((1, k), 1, k') f = f := by
  let j : _ →ₜ* G E s × G E s' := .prodMap (.inr ..) (.inr ..)
  peel NonarchimedeanGroup.prod_subset ((char_eventually_eq_one (.comp (.coprod (b⁻¹.1.1.comp G.det)
    (a.1.1.comp G.det)) j.1) (by simp [Function.comp_def]; fun_prop)).and
    ((G.continuous_onHom.comp j.2).snd.tendsto' _ _ (by simp) (Space.eventually_omega_eq_self hf)))
  simp_all [pairWeil_apply, pairChar, j, ← G.onHom_fin, Set.subset_def]
