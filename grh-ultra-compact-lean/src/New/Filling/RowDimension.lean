import New.Trace.GoodFormTransfer
import New.Rows.Separation
lemma Data.decrPosition_paramW {P} (D : Data P) v i : decrPosition (D.paramW v) i=D.basisNumber i:=D.card_filter_basisNumber 0 _ (by simp [paramW_lt_iff]) (by simp)
