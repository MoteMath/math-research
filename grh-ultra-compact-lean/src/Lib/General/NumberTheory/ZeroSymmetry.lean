import Lib.General.Algebra.SumOverUnits
open Complex DirichletCharacter CharZero Nat.Prime
variable {N} [NeZero N] (χ : DirichletCharacter ℂ N)
omit [NeZero N] in
lemma prod_euler_factor_ne_zero {M : ℕ} {s : ℂ} (h0 : s.re ≠ 0) : ∏ p ∈ M.primeFactors, (1 - χ p * p ^ (-s)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun p h e ↦ by
  obtain := congr(Real.logb p ‖$(χ.star_apply' p)‖), show χ p = p ^ s by grind [cpow_neg]
  simp_all [norm_natCast_cpow_of_pos, χ.inv_apply_eq_inv', pos, ne_one]
lemma exists_isPrimitive_changeLevel_eq : ∃ M f ψ, NeZero M ∧ IsPrimitive ψ ∧ changeLevel (f : M ∣ N) ψ = χ := ⟨_, _, _, ⟨χ.conductor_ne_zero⟩, χ.primitiveCharacter_isPrimitive, χ.changeLevel_primitiveCharacter⟩
lemma LFunction_one_sub_eq_zero s (h0 : s.re ≠ 0) (h1 : s ≠ 1) (hs : LFunction χ s = 0) : χ.gammaFactor s = 0 ∨ LFunction χ⁻¹ (1 - s) = 0 := by obtain ⟨M, f, ψ, _, h, rfl⟩ := exists_isPrimitive_changeLevel_eq χ; have := ψ.changeLevel_eq_cast_of_dvd f (-1); simp_all [LFunction_changeLevel, ← map_inv, gammaFactor, prod_euler_factor_ne_zero, s.ext_iff, @LFunction_eq_completed_div_gammaFactor M, @eq_comm ℂ 1, DirichletCharacter.Even, IsPrimitive.completedLFunction_one_sub (ψ.conductor_inv.trans h)]; lia
