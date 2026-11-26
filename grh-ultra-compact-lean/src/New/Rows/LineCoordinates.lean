import Lib.LocalGL.TraceFormula.TraceComparison
import Lib.Adelic.Hecke.ClassSumBounds
import New.Trace.GoodIdempotent
import New.Rows.MemberKernels
seal Finset.univ Finset.sum Finset.prod
noncomputable section
open Finset Complex ComplexOrder Equiv Fintype PolyRep Ideal Matrix MvPolynomial LevelPlaces Sum WeilData Matrix.Module
namespace Data
abbrev untwistedModulus {P : Parameters} (D : Data P) := (D.𝔪 .one · false)
lemma ideal_untwistedModulus_eq_span {P : Parameters} (D : Data P) {c} : (D.untwistedModulus
  c).ideal = span {D.piGBar ^ c} := by simp [levelModulus, ← span_singleton_pow, span_piGBar]; rfl
instance {P : Parameters} (D : Data P) : NeZero D.m := .of_gt D.le_m
abbrev CarrierIndex {P : Parameters} (D : Data P) := Fin (2 * D.m) ⊕ Fin D.m
abbrev Q3 {P : Parameters} (D : Data P) := Fin (6 * D.m + 1)
abbrev SmallIndex {P : Parameters} (D : Data P) := D.RowIndex ⊕ Fin (D.t - 9 * D.m - 1 - D.r)
abbrev SmallClasses {P : Parameters} (D : Data P) := StdClasses (principalLevel D.SmallIndex (D.piGBar ^ 2))
variable {P : Parameters} (D : Data P) in
def basisVec i := D.basisNumber.symm ⟨i ⊓ (D.r - 1), by grind⟩
variable {P} (D : Data P) (ϑ : D.TameChar) (j : D.LiftIndex) (h : ℕ)
abbrev Q6 := StdClasses (principalLevel D.Q3 (D.piGBar ^ 2)) × (D.Φ → Fin D.reducedHalfGap → Fin (2 * D.m) → D.Q3)
def n0 (i : D.Q6) := (Space.exists_short_basis_stdSpace P.cycloConductor_mem_different i.1.out).choose.1ᵀ
variable {D}
def twistedChi := D.χ ^ j.1 * ϑ.toAutChar
lemma twistedChi_hasWeight : (twistedChi ϑ j).HasWeight 0 (D.liftTamePart ϑ j) := (D.chi_hasWeight.zpow j).mul ϑ.hasWeight
abbrev Q5 := Fin j ⊕ Fin (2 * D.m + (D.m - j))
abbrev BigIndex := (D.RowIndex ⊕ Q5 j) ⊕ D.Q3
abbrev f4 := (D.signsW j ⊕ᵥ (-1 ⊕ᵥ 1) : _ ⊕ Q5 j → _)
def h3 (i : Fin D.m) := if h :
  _ then @inr _ (Q5 j) (inl ⟨i, h⟩) else inl (D.basisVec (D.posRank i))
def n6 i := ite (h + i.1 < D.posRank j) (@inl _ (Q5 j) (D.basisVec (h + ↑i))) (inr (inr (.castAdd _ i)))
abbrev untwistedAuxPair := D.auxPair .one j
abbrev DetIndex τ := (Σ h : Fin (D.posRank j), Fin ((untwistedAuxPair j).colsPlus τ h)) ⊕ Fin D.reducedHalfGap
def s22_n8 := ∏ τ, letterMinor τ (h3 j) inr ^
  (Fintype.card (DetIndex j τ) + Fintype.card (BigIndex j) + D.m) * ∏ h :
  Fin (D.posRank j), letterMinor τ (n6 j h) inl ^ (untwistedAuxPair j).colsPlus τ h
abbrev bigCharExp := j + (D.t + D.k - 1) / 2
def g4 := D.muFlat * upsilonU1 ^ (↑(D.m + bigCharExp j) - j * D.h : ℤ)
lemma s22_p9 : (g4 j).HasWeight (↑(D.m + bigCharExp j) - D.w j ·) 1 := by
  convert! D.h5.mul (hasWeight_upsilonU1_zpow _) <;> grind [Pi.add_def]
abbrev bigChar := D.liftChar ϑ j * upsilonU1 ^ bigCharExp j
abbrev MemberIndex := Matrix D.CarrierIndex (BigIndex j) (D.untwistedModulus 2).ResRing × D.Q6
def fNatural (i : MemberIndex j) g := ∫ x, carrierForm _ _ x * modKernel (signedSpace ..)
    (((D.spaceW j).sum ((stdSpace ..).neg.sum (stdSpace ..))).sum (stdSpace ..)) (upsilonU1 ^ D.m)
  (g4 j) _ (traceChar i.1) (renameRowsCols inl id (s22_n8 j) * renameRowsCols inr id (pairedDetProd (.X ⟨·, ·, inl ·⟩) fun w k ↦ ((D.n0 i.2).map (Φ w)).submatrix (i.2.2 w k) id)) x (.sum (.sum (g, 1), i.2.1.out)) ∂(signedSpace ..).quotMeasure
lemma card_detIndex_add_bigCharExp τ : Fintype.card (DetIndex j τ) + bigCharExp j = D.w j τ := by
    open Finset in simp [← sum_range]; zify; rw [Finset.sum_congr rfl, sum_range_sub' fun l ↦ D.rowParameter τ (l - 1) + l ⊔ 1] <;> grind [rowParameter, reducedHalfGap, auxPair]
abbrev Q1 := Fin (2 * D.m + (D.m - j)) ⊕ D.Q3 ⊕ D.CarrierIndex
def j6 : D.RowIndex ⊕ Fin j ⊕ Q1 j ≃ D.CarrierIndex ⊕ BigIndex j := ((sumComm ..).trans ((sumAssoc ..).trans ((sumAssoc ..).trans (sumCongr (.refl _) (sumAssoc ..))))).symm
def posEquiv : Fin (2 * D.m) ⊕ BigIndex j ≃ Fin (D.posRank j) ⊕ Q1 j := Fintype.equivOfCardEq (by simp [↓card_rowIndex]; grind)
def detRows i (Y : _ := D.n0 i) τ : DetIndex j τ → Matrix (Fin (2 * D.m)) (Fin (D.posRank j) ⊕ Q1 j) ℂ := (fun h ↦ (inclMatrix ℂ fun a ↦ dite _ (inl ⟨h.1 + a, ·⟩) fun _ ↦ inr (inl (a.castAdd _)))ᵀ) ⊕ᵥ fun k ↦ fromCols 0 (fromCols 0 (fromCols ((Y.map (Φ τ)).submatrix (i.2 τ k) id) 0))
abbrev linePolyCoords i (Y : _ := D.n0 i) := s22_z3 (untwistedAuxPair j).colsPlus (stackedDetProd (posEquiv j) (detRows j i Y))
abbrev s22_g3 : (D.𝔪 ϑ 2).ResRing →+* (D.untwistedModulus 2).ResRing := reduceToR₀
def h9 u (z : Matrix (BigIndex j) (Q1 j) _) := ite (z.submatrix id (.map id inl) = inclMatrix _ (.map (inr ∘ inr) id)) (∑ g : GL _ _, traceChar u (z.toCols₂.toCols₂.map (s22_g3 ϑ) * g.1)) 0
def lineMultiplier (i : MemberIndex j) h l := modKernelI (stdSpace ..).neg (upsilonU1 ^ j.1) (bigChar ϑ j) (D.𝔪 ϑ 2)
  (Pi.single (inclMatrix _ (inl ∘ inr ∘ inl)) 1) 1 1 h * stdClassSum (Kf ..) fun c ↦ carrierXi D.m
  (twistedChi ϑ j) c * modKernelI (stdSpace ..) (bigChar ϑ j) (bigChar ϑ j) _ (h9 ϑ j i.1)
  ((linePolyCoords j i.2) l) (1, U.blockSumOne (1, U.blockSumOne (i.2.1.out, c))) h
attribute [local grind .] reducedHalfGap auxPair rowParameter
attribute [local simp↓] card_rowIndex detRows Matrix.mul_apply inclMatrix ite_apply
lemma card_detIndex τ : card (DetIndex j τ) = (range (card (BigIndex j))).sum
  ((untwistedAuxPair j).colsPlus τ) ∧ card (DetIndex j τ) ≤ D.b₁ + D.b₂ + D.h + D.m * D.h := ⟨by simp [← sum_range]; rw [eq_comm, eventually_constant_sum (N := D.posRank j + 1),
  sum_range_succ] <;> grind, by grind [card_detIndex_add_bigCharExp j τ, mul_le_mul_left j.2.2 D.h]⟩
open Norms.L2Operator
variable (i : D.Q6) (Y : Matrix _ _ D.E) (φ : ℂ →+* ℂ)
lemma s22_v2 z : let y := φ ∘ eval z ∘ linePolyCoords j i Y; toPoly _ _ y =
    .map (φ.comp (eval z)) (inFirstCols (stackedDetProd (posEquiv j) (detRows j i Y))) ∧ (((∀ τ a b, ‖φ (Φ τ (Y a b))‖ ≤ D.gProd ^ 4) ∧ ∀ x, ‖φ (z x)‖ ≤ D.gProd ^ 4) → weylNormSq y ≤ ↑(D.gProd ^ 9) ^ (31 * D.m * ∑ τ, card (DetIndex j τ))) := by
  clear_aux_decl; refine (?_ : HasWeightNormLe ..).elim fun ξ h ↦ (?_ : _ ∘ _ = ξ) ▸ h
  simp_rw [stackedDetProd, map_prod, Fintype.card_eq_sum_ones, mul_sum, ← prod_pow_eq_pow_sum]
  convert HasWeightNormLe.prod (n := BigIndex j) fun τ _ ↦ .prod (κ := fun l : DetIndex j τ ↦ Pi.single τ (Pi.single (l.elim (·.1) fun _ ↦ D.posRank j) 1)) fun l _ ↦ ?_
  simp [funext_iff, Fintype.sum_sigma, sum_fin_eq_sum_range, ← mem_range]
  grind; generalize e : l.elim .. = h
  have ⟨H, A, B⟩ : h ≤ D.posRank j ∧ D.posRank j - h ≤ j ∧ h < card (BigIndex j) := by simp; grind [Fin, Sigma]
  let E := ((finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le H))).symm.sumCongr (.refl (Q1 j))).trans (.sumAssoc ..)
  let Z := of (φ <| (detRows j i Y τ l).fromRows (fromCols 0 (of (z ⟨τ, ·, ·⟩))) · <| E.symm <| .inr ·)
  choose Y γ d b using s22_m5 ((posEquiv j).trans E) Z
  use γ • weylEval _ _ fun (x, i) ↦ (List.ofFn (Yᵀ (.inr x.2)))[i]!, funext fun x ↦ .symm (.trans (by
    simp [stackedDet, AlgHom.map_det, RingHom.map_det]
    refine det_eq_of_eq_det_one_mul (fromBlocks 1 0 (of fun u a ↦ ite (h + a < D.posRank j) (x (⟨τ, u⟩, h + a)) 0) 1) (by simp) (Matrix.ext fun a ↦ (reindex_equiv ((posEquiv j).trans E).symm).1.2 ?_)
    cases l <;> cases a <;> simp [Z] at e ⊢ <;> simp +contextual [E, inFirstCols, e, Fin.cast]
    all_goals first | lia | intro b; rw [univ.sum_eq_single ⟨b, by grind⟩] <;> clear * - <;> grind)
    ((d (fromRows 0 (of (x ⟨⟨τ, ·⟩, ·⟩)))).trans ?_))
  refine fun q ↦ .trans ?_ (b.trans (by
    grw [norm_det_le_norm_pow, l2_opNorm_conjTranspose_mul_self, ← sq, l2_opNorm_le_of_apply (M := D.gProd ^ 4)
      (by cases l <;> simp [Z, E, apply_ite, q, NeZero.one_le, one_le_pow₀])]; norm_cast
    simp; exact pow_le_pow (by grw [A, Nat.sub_le, j.2.2]; exact D.nat_le_of_hasLogBound)
      D.nat_le_of_hasLogBound (by grw [A, Nat.sub_le, j.2.2]; grind)))
  grw [weylNormSq_smul, weylNormSq, re_le_norm, ← norm_det_le_norm_det_of_posSemidef (posSemidef_self_mul_conjTranspose
    Y.toCols₂) (by convert Y.toCols₁.posSemidef_self_mul_conjTranspose; ext; simp)]
  iterate 2 simp [star_weylEval, weylKernel, highestPoly, tableauPoly, minor, det_apply, rowSubst, ↓det_transpose, Fin.val_eq_val _ ⟨h, B⟩, -sum_sum_type, @sum_sum_type (Fin _)]
  simp [_root_.funext_iff, s22_z3, map_fockPairing, MvPolynomial.map_map, ← h.1]
lemma toPoly_linePolyCoords : toPoly _ _ (linePolyCoords j i Y) =
  inFirstCols (stackedDetProd (posEquiv j) (detRows j i Y)) := MvPolynomial.ext _ _ fun d ↦ funext
  fun z ↦ by
    simpa [← coeff_map] using! congr(($((s22_v2 j i Y 1 z).1)).coeff d)
lemma f1 : ∃ d ≤ 31 * D.m * ∑ τ, card (DetIndex j τ), ∃ H : ℤ, 0 < H ∧ H ≤ (d ^ d) ^ 3 ∧ ∀ i Y l,
  let Q := H • linePolyCoords j i Y l; (∀ c ≠ (0 : ℂ), aeval (c • .X ·) Q = c ^ d • Q) ∧ ∀ A : Subring ℂ, (∀ τ a b, Φ τ (Y a b) ∈ A) → Q ∈ (MvPolynomial.map A.subtype).range := by
  obtain ⟨J, K, a, -, c, -⟩ := exists_dual_isometry (κ := (untwistedAuxPair j).colsPlus) (rowPos (BigIndex j)) _ rfl (by tauto)
  have b i Y := congr((Kᵀ * $(c ▸ weylGram_mul_fockPairing) * Jᵀ)ᵀ • linePolyCoords j i Y); simp [← Matrix.mul_assoc, a, mul_smul, ↓Kᵀ.mul_smul, weylGram_isSymm.eq, Int.cast_smul_eq_zsmul, -zsmul_eq_mul, -card_sum] at b
  refine ⟨∑ τ, ∑ h ∈ range (card (BigIndex j)), (card (BigIndex j) - h) * (untwistedAuxPair j).colsPlus τ h, ?_, _, hookNumber_pos, hookNumber_le (sum_mono fun _ ↦ ?_), fun i Y l ↦ ⟨fun c h ↦ ?_, fun A hA ↦ (_root_.prod_mem fun τ _ ↦ _root_.prod_mem fun k _ ↦ IsIntMatrix.det_mem fun a b ↦ ?_ : _ ∈ (MvPolynomial.map (MvPolynomial.map A.subtype)).range.comap inFirstCols.1).elim fun F e ↦ congr($(b ..) l ∈ _).mp (_root_.sum_mem fun k _ ↦ zsmul_mem (coord_mem_of_coeff_mem (MvPolynomial.map A.subtype).range.toAddSubgroup 0
    (by simpa using e ▸ toPoly_linePolyCoords ..) (by simp [coeff_map]) _) _)⟩⟩
  simp [↓card_detIndex, mul_sum]; gcongr 2; grind [Nat.mul_lt_mul_right]
  grw [range_mono le_self_add, ← sum_flip]; grind only [sum_range_succ]
  simpa [schur_smul, Pi.smul_def, ↓card_detIndex, *, -detRows, sum_range, ← prod_pow_eq_pow_sum, pow_mul, pow_sub_of_lt, ← eq_inv_smul_iff₀, smul_smul, ← division_def, div_pow, inv_mul_eq_div, prod_ne_zero_iff] using congr(_ * $(s22_v3 (c • 1) 1 (twoSidedSubst_stackedDetProd _ (detRows j i Y) ..) _ l))
  cases a <;> simp [inFirstCols] <;> obtain b := posEquiv j b
  refine ⟨C (C ⟨_, ?_⟩), by simp; rfl⟩; revert k b; simp [apply_ite, hA]
  cases b; exacts [⟨_, map_X ..⟩, ⟨C (.X _), by simp; rfl⟩]
