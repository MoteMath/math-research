import Lib.Adelic.Unitary.SpaceGram
variable {E} [Field E] [NumberField E] [NumberField.IsCMField E] {n} [Fintype n] {s : n → _}
noncomputable def G.ofMat m h := (toUnitary.symm (U.of isUnit_stdForm m h) : G E s)
@[simp] lemma G.mat_ofMat m h : (ofMat m h : G E s).mat = m := rfl
