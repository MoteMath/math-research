import Lib.ClassField.HeckeL.AutCharLFunction
noncomputable def AutChar.frobValue {E : Type} [Field E] [CMType E] [WeilData E] (a : AutChar E) n [Fintype n] w := (a.spaceChar (Fintype.card n)).atUnif w * √w.q ^ Fintype.card n
