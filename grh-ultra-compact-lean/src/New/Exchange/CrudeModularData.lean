import New.Curve.ConjugatesOfJets
import New.Columns.ColumnDefs
noncomputable section
open Finset Fintype Function Ideal
attribute [local grind] Data.card_X Data.n
variable {P} {D : Data P} (ϑ : D.TameChar) {p : ℕ} [Fact p.Prime] [PadicPlace p] (σ : D.Φ) (Λ : Finset (FinPlace D.E)) {s} {𝔪 : Modulus (Parameters.E P s)}
lemma Data.isLiftWeight_kappa (j : ℕ) : IsLiftWeight (D.X j) (D.X (j + 1)) D.κ ((Fintype.card (D.X (j + 1)) / 2 : ℕ) - D.w (j + 1) ·) (D.lastEntry j) := ⟨fun _ ↦ ⟨by grind, fun h ↦ by
    have := @Nat.not_dvd_of_lt_of_lt_mul_succ (D.t + 1) j (h - D.k)
    grind [κ]⟩, by grind, by cases j <;> simp [funext_iff, ↓card_X, n, κ, lastEntry] <;> grind⟩
abbrev Data.homX (j : ℕ) := (stdSpace D.E (D.X j)).hom (stdSpace _ (D.X (j + 1)))
@[simps! -isSimp ω] def Data.liftKernel (j : ℕ) : Kernel _ (D.X (j + 1)) D.κ (D.lastEntry j)
  (D.lastEntry (j + 1)) (D.columnLevel j) (D.homX j).finitePart := by
  obtain h : (D.chainChar ϑ j.succ).HasWeight .. := D.hasWeight_liftChar
  apply thetaKernel (D.isLiftWeight_kappa j) (star ↑D.piG * P.jetScale D.s)
    (by convert h.hasWeight_rankTwist (n := D.X j); grind [lastEntry]) h.hasWeight_rankTwist
abbrev Data.Translations := ∀ j, D.X (j + 1) × D.X j → 𝔸f D.E
def Data.translateDatum (x : D.Translations) j := (homX j).heisFinPart (x j) ⟨P.intVacuum _, SMulMemClass.smul_mem _ (by simp)⟩
abbrev Data.chainComb (Ψ : D.Translations →₀ ℂ) (Φ : _ → ∀ _, _) j := Ψ.sum fun x ↦ (· • chain (liftKernel ϑ) (Φ x) j)
def Data.Bμ Ψ := D.restrictToY ∘ₗ chainComb ϑ Ψ translateDatum _ ∘ₗ D.Column.subtype
lemma span_piGBar (D : Data P) : .span {D.piGBar} = ∏ i, (D.chosen i).1 := by
  ext; simpa [mem_prod_finPlace_iff D.isConjApart_chosen.1, mem_span_singleton, ← dvd_iff_Ô D.piGBar_ne_zero, D.range_chosen, dvd_iff_reduceAt_eq_zero fun h ↦ (D.isChosen_iff.1 h).rec fun _ ↦ (Parameters.intValuation_eq_of_mul_star (D.g_modEq_one _) ·.2 D.exists_cofactor h)] using! Set.forall_mem_range (f := D.chosen)
def Data.inducedPlace := placeOfEmb (ιₚ.comp (Φ σ))
structure Data.IsMarked where
  star_notMem : ∀ l ∈ Λ, star l ∉ Λ
  served : Λ.Nonempty → D.IsServed p
  served_top : ∀ l ∈ Λ, ∃ τ ∈ D.tops, inducedPlace τ = l
  nonsplit : D.IsSmallNonsplit p
structure Data.IsFullMark extends D.IsMarked Λ where
  cover : ∀ τ ∈ D.tops, inducedPlace τ ∈ Λ ∨ star (inducedPlace τ) ∈ Λ
abbrev Data.integralColumns := (integralFormsAt D.Column 1).comap (D.Column.subtype.restrictScalars _)
abbrev Data.evenPlaces : Finset D.Φ := {σ | inducedPlace σ ∈ Λ}
def Data.markExponent l := D.a * #{τ ∈ D.tops | inducedPlace τ = l}
def Data.lowColumns j τ := ∑ h ∈ range (D.n (j + 1)), ite (h = 1) 0 (D.κ τ h)
def Data.lowBoxes j τ := ∑ h ∈ range (D.n (j + 1)), h * ite (h = 1) 0 (D.κ τ h)
attribute [local simp↓] absNorm_span_natCast NumberField.RingOfIntegers.rank finrank_eq_two_mul_card_infinitePlace pow_mul
lemma Modulus.card_resRing_le {k : ℕ} (h : ↑k ∈ 𝔪.ideal) (p : 0 < k) : .card 𝔪.ResRing ≤ k ^ (2 * numInfPlaces (P.E s)) := Nat.le_of_dvd (by bound) ((map_dvd absNorm (dvd_span_singleton.2 h)).trans (by simp))
variable {n n' : Type} [Fintype n] [Fintype n'] {𝔪 : Modulus (Parameters.E P s)} {Ψ : Matrix n' n 𝔪.ResRing → ℂ}
lemma Parameters.smul_vacuumDatum_mem_standardData {N q l : ℕ} [Fact l.Prime] [PadicPlace l] (hd : ↑(q * N) ∈ 𝔪.ideal) (hΨ : ∀ x, Ψ x ∈ integralAway q) (hl : l.Coprime q) : ((N ^ (2 * numInfPlaces (P.E s) * Fintype.card (n' × n)) : ℕ) : ℂ) • P.vacuumScale s ^ Fintype.card (n' × n) • (vacuumDatum (stdSpace ..) (stdSpace ..) 𝔪 Ψ).1 ∈ standardData _ N := by
  simpa [intVacuum, comp_def, vacuumDatum] using (isAdmissibleComb_name (g := N) (u := intVacuum _) _ _ (by grind [mul_comm]) (hΨ <| vecToMat ·) le_ciSup rfl).smul_mem (M := standardData ..) hl fun y x ↦ Submodule.subset_span ⟨y, by simpa [integralAfter] using (x · · ∘ IsPrime.notMem_of_isCoprime_of_mem hl.cast), by simp [intVacuum]⟩
lemma Parameters.isAdmissibleComb_vacuumDatum M (hM : ∀ (σ : ℂ ≃+* ℂ) x, ‖σ (Ψ x)‖ ≤ M) : IsAdmissibleComb (Space.finHeisOp _ · (intVacuum _)) .univ 0 0 True (Fintype.card (n' × n → 𝔪.ResRing) * M)
  (P.vacuumScale s ^ Fintype.card (n' × n) • (vacuumDatum (stdSpace ..) (stdSpace ..) 𝔪 Ψ).1) := by
  erw [← map_smul]
  exact .bind (isAdmissibleComb_name (g := 0) _ _ (by simp) (fun _ _ ⟨p⟩ ↦ by aesop) (fun _ _ ↦ by
    grw [comp_def, hM]) rfl) 1 1 (by simp [IsAdmissibleComb.single, intVacuum])
