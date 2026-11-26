import New.Trace.BadShare
import New.Data.Weights
noncomputable section
open Ideal Nat AutChar Finset Fint MulChar NeZero NumberField Parameters Polynomial
variable {P} (D : Data P) {w : FinPlace D.E} (a n j : ℕ) {S T α : Type}
namespace Data
instance hasLogBound_varpi (v : D.Φ) (u) :
  D.HasLogBound u (v (P.ϖ D.s)) (ite u 12 10 * D.logX) := by
  obtain ⟨hz, e⟩ := isPrimitiveRoot_zeta.map_of_injective v.embedding.injective, v.pos_iff.2 (P.relDifferentGen_ne_zero _)
  simp [↓infinitePlace_apply_varpi, ← v.norm_embedding_eq, ← eval_map_apply, ← expand_towerDeg_cyclotomic, ← derivative_map, derivative_expand, hz.norm'_eq_one out, pos, -norm_pos_iff] at *
  exact Real.exp_log e ▸ .of_mem_Icc (a := by grind [Data, c, single_le_sum, (mem_primitiveRoots one_le).2 (hz.pow one_le (mul_comm ..))])
instance hasLogBound_rootDisc (u) : D.HasLogBound u D.rootDisc (ite u 12 10 * D.logX) := have := (D.hasLogBound_varpi · u |>.1); ⟨by split <;> apply le_of_pow_le_pow_left₀ (ne D.f) <;> simp_all [↓pow_abs, ↓← prod_varpi_eq_rootDiscr_pow, abs_prod, ← Finset.card_univ, ← prod_const, prod_le_prod₀, Real.exp_pos, rootDiscr_pos, le_of_lt]⟩
abbrev piGBar := star (algebraMap _ (𝓞 D.E) D.piG)
def IsChosen (w : FinPlace D.E) := D.piGBar ∈ w.1
protected abbrev ChosenPlace i := {w : FinPlace _ // D.piGBar ∈ w.1 ∧ ↑(D.g i) ∈ w.1}
lemma piGBar_mul_star : D.piGBar * star D.piGBar = D.gProd := by
  ext; simpa [gProd, map_star_CM, mul_comm] using! congr(algebraMap P.K D.E $D.norm_piG)
@[simp] lemma piG_ne_zero : D.piG ≠ 0 := (by simpa [·, ne] using D.norm_piG)
lemma piGBar_ne_zero : D.piGBar ≠ 0 := by simp
lemma exists_cofactor {i} : ∃ c : ℕ, D.piGBar * star D.piGBar = D.g i * c ∧ (D.g i).Coprime c := ⟨D.g i.rev, by rw [piGBar_mul_star, gProd]; grind [coprime_primes, g_prime, g_injective]⟩
lemma isChosen_iff : D.IsChosen w ↔ ∃ i, D.IsChosen w ∧ ↑(D.g i) ∈ w.1 := by
  simpa using (w.2.2 <| mod_cast D.piGBar_mul_star ▸ mul_mem_right _ _ ·)
lemma q_eq_g {i} {w : FinPlace D.E} : ↑(D.g i) ∈ w.1 → w.q = D.g i := q_eq_of_modEq_one (g_modEq_one ..)
lemma finite_isChosen :
  {w | D.IsChosen w}.Finite := by simp [IsChosen, ← dvd_span_singleton, finite_factors]
lemma v6 (h : D.IsChosen w) : ∃ T : MulChar (ResField w) ℂ, orderOf T =
  P.Mω D.s ^ 2 := exists_mulChar_orderOf _ (by grind [isChosen_iff, q_eq_g, dvd_g_sub_one, card_ResField, card_eq_fintype_card]) (Complex.isPrimitiveRoot_exp _ out)
def ω w := if h : D.IsChosen w then (D.v6 h).choose ^ P.Mω D.s else 1
lemma orderOf_ω (h : D.IsChosen w) : orderOf (D.ω w) = P.Mω D.s := by
  simp [ω, orderOf_pow, (v6 ..).choose_spec.trans (sq _), *, ne]
@[simp] lemma omega_eq_one_of_not_isChosen : ¬D.IsChosen w → D.ω w = 1 := (dite_eq_right ·)
lemma omega_zpow_mul_pow_eq_one {ψ} (n : ℤ) (h : ψ w = 1) : (D.ω ^ n * ψ) w ^ P.Mω D.s = 1 := by
  by_cases D.IsChosen w <;> simp_all [← @orderOf_ω _ _ w]
lemma p8 : ∃ μ, HasWeight μ (-a * D.w 0 ·) (D.ω ^ n) := exists_hasWeight_of_prod_eq_one (S := D.finite_isChosen.toFinset) (by aesop) fun ⟨_, _⟩ U ↦ by
  obtain ⟨_, -, rfl⟩ := exists_zeta_pow_eq
    (.of_pow ((pow_torsionOrder_eq_one _ (algebraMap_mem_Ô.1 U)).substr .one) out)
  simp_all [↓← map_pow, w, b₁, b₂, ω, prod_eq_one, ↓zpow_mul, ↓zpow_natCast, pow_add, roundUp, pow_mul, pow_right_comm, ← Submonoid.one_def, pow_apply', ne, pow_right_comm _ _ D.N₁, isPrimitiveRoot_zeta.1, ↓inv_pow, pow_eq_pow_of_modEq N₁_mul_d_dvd_M_omega.modEq_zero_nat]
  simp [↓prod_phi_eq_norm, isPrimitiveRoot_zeta.norm_eq_one (by grind [Parameters] : D.N₁ ≠ 2) (irreducible_cyclotomic ..)]
def muFlat := (D.p8 1 0).choose
def χ := (D.p8 0 1).choose
lemma h5 : D.muFlat.HasWeight (-D.w 0 ·) 1 := by grind [muFlat, pow_zero]
lemma chi_hasWeight : D.χ.HasWeight 0 D.ω := by rw [Pi.zero_def]; grind [χ, pow_one]
structure Pair where
  ν : AutChar D.E
  c : D.Φ → ℕ
  (ψ z) hasWeight : ν.HasWeight (-c ·) ψ
  ψ_eq_one w : ¬D.IsChosen w → ψ w = 1
  z_mem : z ∈ Set.Icc 1 D.t
  le_c v : z ≤ c v
  c_le v : c v ≤ 4 * D.b
def rowParameter v i := ite (i + 1 < D.k) (D.k / 2 - 1 - i : ℤ) (D.h₂ - D.w (i + 2 - D.k) v)
instance {u} : D.HasLogBound u (P.bigOmega D.s) (ite u 0 (-13 * D.logX)) := bigOmega.eq_1 .. ▸ .of_mem_Icc (a := by grind [Data, c, sum_nonneg])
def logLevelTarget := D.m * ((∑ v, .log (D.nominalWeight v)) / D.f) + (D.m - 1) * .log
  (D.gProd * D.rootDisc / (2 * .pi)) - 15 / 2 * D.logB
lemma p0 : D.logLevelTarget ∈ Set.Icc (D.m * D.logB) (29 * D.m * D.logB) := by
  constructor <;> [grw [logLevelTarget, ← (D.le_of_hasLogBound : D.b ^ 2 ≤ _ * _ / _), ← (D.le_of_hasLogBound : 1 ≤ D.nominalWeight _)]; grw [logLevelTarget, (D.le_of_hasLogBound : _ * _ / _ ≤ D.b ^ 27), (D.le_of_hasLogBound : D.nominalWeight _ ≤ D.b ^ 2)]] <;>
    simp [HasLogBound.pos D] <;> grind [Data, (D.le_of_hasLogBound : 99 * D.logB ≤ D.m * D.logB)]
def N := (D.exists_prime_window _ (Set.Icc_subset_Icc D.le_of_hasLogBound D.le_of_hasLogBound D.p0)).choose
lemma N_prime : D.N.Prime := by grind [N]
lemma N_modEq_one : D.N ≡ 1 [MOD D.cycloConductor] := by grind [N, ModEq.of_dvd, N₁_mul_d_dvd_M_omega, sq]
lemma log_N_mem_window :
  .log D.N ∈ Set.Icc D.logLevelTarget (D.logLevelTarget + √D.logB) := by grind [N]
lemma log_N_mem_Icc : .log D.N ∈ Set.Icc (D.m * D.logB) (30 * D.m * D.logB) := by
  grind [N, D.p0, (D.le_of_hasLogBound : √D.logB ≤ D.m * D.logB)]
instance {u} : D.HasLogBound u (.log D.N) (D.logX / 2 + D.logB.log + ite u 32 0) := .of_mem_Icc _ _ D.log_N_mem_Icc
instance : Fact D.N.Prime := ⟨D.N_prime⟩
instance : D.HasLogLower D.N (101 * D.logB) := ⟨(Real.le_log_iff_exp_le (HasLogBound.pos D)).1 D.le_of_hasLogBound⟩
lemma c5 : ∃ π : 𝓞 D.E, π * star π = D.N := (Prime.sq_add_sq ((D.N_modEq_one.of_dvd (by grind [Parameters])).trans_ne nofun)).rec fun a ⟨b,
  h⟩ ↦ StablyUnram.exists_i_c₀.imp' (a + b * ·) (h ▸ by simp; grind)
def π := D.c5.choose
lemma π_mul_star : D.π * star D.π = D.N := by grind [π]
structure TameChar where
  toAutChar : AutChar D.E
  Q : Finset _
  (ψ) hasWeight : toAutChar.HasWeight 0 ψ
  ψ_eq_one : ∀ w ∉ Q, ψ w = 1
  star_notMem : ∀ w ∈ Q, star w ∉ Q
  coprime : (D.gProd * D.N).Coprime (∏ w ∈ Q, w.q)
abbrev TameChar.levelNorm {D} (ϑ : @TameChar P D) := ∏ w ∈ ϑ.Q, w.q
structure Twist extends D.TameChar where psi_ne_one : ∀ w ∈ Q, ψ w ≠ 1
instance : One D.Twist := by use! 1, ∅, 1, .one <;> simp
instance : Coe D.Twist D.TameChar := ⟨Twist.toTameChar⟩
abbrev TameChar.one {D} : @TameChar P D := Twist.toTameChar 1
def μ₀ := D.muFlat * (WeilData.upsilonU1 ^ (-D.h : ℤ) * D.χ) ^ j
lemma mu₀_hasWeight : (D.μ₀ j).HasWeight (-D.w j ·) (D.ω ^ (j : ℤ)) := by
  convert! D.h5.mul
    (((WeilData.hasWeight_upsilonU1_zpow _).mul D.chi_hasWeight).zpow j) <;> simp; grind
def liftChar ϑ j := D.μ₀ j * TameChar.toAutChar ϑ
def liftTamePart ϑ (j : ℕ) := D.ω ^ (j : ℤ) * TameChar.ψ ϑ
instance hasWeight_liftChar {ϑ j} : (D.liftChar ϑ j).HasWeight (-D.w j ·)
  (D.liftTamePart ϑ j) := by simpa using! (mu₀_hasWeight ..).mul ϑ.hasWeight
abbrev LiftIndex := Set.Icc 1 D.m
@[instance_reducible] def _root_.BlockIndex (S T : Type) | 0 => S | j + 1 => BlockIndex S T j ⊕ T
def _root_.BlockIndex.firstBlock : ∀ j, S ↪ BlockIndex S T j | 0 => .refl _ | j + 1 => (BlockIndex.firstBlock j).trans .inl
def _root_.BlockIndex.equivSum (ν : S ≃ α) : ∀ j, BlockIndex S T j ≃ α ⊕ Fin j × T
  | 0 => ν.trans (.symm (.sumEmpty ..))
  | j + 1 => (Cardinal.eq.1 (by simp! [(BlockIndex.equivSum ν j).cardinal_eq]; ring)).some
variable [Fintype S] [Fintype T] {P : Parameters} (D : Data P) (j : ℕ)
instance _root_.instFintypeYT :
    ∀ j, Fintype (BlockIndex S T j) | 0 => ‹_› | j + 1 => @instFintypeSum _ T (instFintypeYT j) _
@[simp] lemma _root_.BlockIndex.card : Fintype.card (BlockIndex S T j) = Fintype.card S + j * Fintype.card T := by simp [Fintype.card_congr (BlockIndex.equivSum (.refl _) j)]
def ϱ := D.m / 2 - 1
abbrev InitIndex := Fin (D.n j - 1)
abbrev X := D.InitIndex j ⊕ Unit
abbrev shape : Shape := ⟨D.ϱ, D.X 0, .inr ()⟩
@[reducible] def RowIndex := D.shape.BesselIndex deriving DecidableEq, Fintype
abbrev Y := BlockIndex D.RowIndex (Fin D.t) j
lemma card_rowIndex : Fintype.card D.RowIndex = D.r := by simp; grind [ϱ, n]
instance {u l} [D.HasLogBound u D.r l] : D.HasLogBound u (Fintype.card D.RowIndex) l := D.card_rowIndex ▸ ‹_›
def basisNumber := Fintype.equivFinOfCardEq D.card_rowIndex
def paramW τ i := 2 * D.rowParameter τ (D.basisNumber i)
def entrySign : ℕ → ℕ → ℕ → ℤˣ | o + 1, 0, a => -entrySign o 0 a | o, j, a => (-1) ^ (o + a + min (a - o) j)
lemma ite_odd_eq_sub_emod (y : ℤ) : ite (j % 2 = 1) (y - 1) y = y - j % 2 := by lia
def signsW i := ite (D.posRank j ≤ D.basisNumber i) (-1 : ℤˣ) 1
def chosen (x : Σ i, D.ChosenPlace i) := x.2.1
abbrev G := ∀ x, GL D.RowIndex (ResField (D.chosen x))
instance (i) : Fintype (D.ChosenPlace i) := (D.finite_isChosen.sep _).fintype
def goodTupleFamilies := (Fintype.piFinset fun _ ↦ goodTuples (P.Mω D.s) (Fintype.card D.RowIndex)).map
  (Equiv.piCurry fun i w ↦ Polynomial (ResField (D.chosen ⟨i, w⟩))).symm.toEmbedding
def e₀ := ∑ c ∈ D.goodTupleFamilies, tupleIdem D.RowIndex c
