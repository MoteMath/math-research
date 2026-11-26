import Lib.CM.Sigma.PadicSeriesDefs
import Lib.DiscreteSeries.CuspKernel.BesselSchurBound
import Lib.Weil.Periods.DegreeOfT
lemma index_pi_univ {I G} [Fintype I] [∀ i, Group (G i)] H : (@Subgroup.pi I G _ .univ H).index = ∏ i, (H i).index := (Nat.card_congr (QuotientGroup.leftRel_pi H ▸ Setoid.piQuotientEquiv _) ▸ Nat.card_pi :)
