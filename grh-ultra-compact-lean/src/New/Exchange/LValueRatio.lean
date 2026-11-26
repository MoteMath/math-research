import New.Seesaw.IndexTypes
variable {P : Parameters} {D : Data P}
instance Data.finite_pair : Finite (@Pair P D) := .of_injective (β := Set.Iic (fun _ ↦ ⌊_⌋₊) × Set.Icc 1 _ × AutChar.tameChars D.finite_isChosen.toFinset) (fun p ↦ ⟨⟨_, id (Nat.le_floor <| p.9 ·)⟩, ⟨_, p.7⟩, (_, _), id ⟨by simpa [Set.apply_rangeSplitting Pair.c] using p.hasWeight.mul (Set.rangeSplitting Pair.c ⟨_, p, rfl⟩).hasWeight.inv, by simp_all [Pair.ψ_eq_one]⟩⟩) (by rintro ⟨⟩ ⟨⟩; aesop)
noncomputable def Data.TameChar.pow ϑ n := @mk P D (toAutChar ϑ ^ n) _ (ϑ.ψ ^ n) (mod_cast ϑ.hasWeight.zpow n) (by simp_all [ϑ.5]) ϑ.6 ϑ.7
structure Data.MFoldTwist (D : Data P) extends D.Twist where pow_ne_one : ∀ n ∈ D.LiftIndex, ∀ w ∈ Q, ψ w ^ n ≠ 1
noncomputable abbrev Data.chainChar (D : Data P) ϑ j := D.liftChar (.pow ϑ j) j
noncomputable instance Data.instOneTws (D : Data P) : One D.MFoldTwist := ⟨1, nofun⟩
instance Data.instCoeTwsTwist (D : Data P) : Coe D.MFoldTwist D.Twist := ⟨MFoldTwist.toTwist⟩
noncomputable def Data.MFoldTwist.powTwist ϑ (n : LiftIndex D) := Twist.mk (ϑ.pow n) (@pow_ne_one P D ϑ n n.2)
lemma Data.twist_one_spec : ((1 : D.Twist).toAutChar = 1 ∧ (1 : D.MFoldTwist).1 = 1) ∧ (1 : D.Twist).Q = ∅ := by tauto
noncomputable def Data.Pair.ratio (p : D.Pair) (ϑ : D.TameChar) (s : ℤˣ := 1) := (‖(p.ν * ϑ.toAutChar ^ s.1)⁻¹.L ({w | D.IsChosen w} ∪ ϑ.Q) p.z‖ / ‖p.ν⁻¹.L {w | D.IsChosen w} p.z‖ : ℂ)
