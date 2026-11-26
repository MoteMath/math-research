import Lib.GLn.SchurModule.Nabla
import Lib.DiscreteSeries.Theta.OscillatorDefs
import Lib.DiscreteSeries.Rigidity.CasimirBound
import Lib.DiscreteSeries.FlenstedJensen.FlenstedJensenInvariance
open MvPolynomial Finset
section
noncomputable section
open InnerProductSpace Submodule Int Complex ComplexOrder Pi
section
variable {R C ι} [Fintype R] [Fintype C] {ε ε'} {T : @FockDualPair R C ε ε' ι} {l' a η i N G j ν b} {l : HCParam ε} {P Q : MvPolynomial ι ℂ}
lemma IsMatch.swap : IsMatch T l l' → IsMatch T.swap l' l := by grind [IsMatch, pairSign, Units.val_neg, units_natAbs, Units.val_mul]
lemma IsJointHarmonic.swap (h : IsJointHarmonic T l l' P) : IsJointHarmonic T.swap l' l P := ⟨h.1.swap, by grind [FockDualPair.IsJointHighest, T.sw2, h.2]⟩
namespace Fischer
attribute [scoped simp] raiseOp lowerOp GlModule.E units_ne_iff_eq_neg DFunLike.ite_apply HCParam.IsKHighest IsHarmonic mem_restrictSupport_iff Set.subset_def coeff_pderiv pairSign coeff_X_mul' ite_and fLap
lemma oEpS (q : ε a = ε b) : T.oscRows.E a b P = T.polR P a b 1 - T.polR P b a (-1) + ite (a = b) (T.vacuumWeight (ε a) : ℂ) 0 • P := by simp [q, oscRows]; split <;> simp +contextual [glOp, *, sum_ite, vacuumWeight, polR, ← C_mul'] <;> ring
scoped instance : NormedAddCommGroup (MvPolynomial ι ℂ) := Core.toNormedAddCommGroup (cd := ⟨⟨⟨(fockPairing ℂ <| map (starRingEnd ℂ) ·)⟩, by simp [map_fockPairing, fPC, map_leftInverse conj_conj _], by simp; grind [fockPairing_star_self_pos, zero_re, pos_iff], by simp, by simp [← C_mul']; simp [C_mul']⟩, by grind [fockPairing_star_self_pos, inner]⟩)
scoped instance : InnerProductSpace ℂ (MvPolynomial ι ℂ) := .ofCore _
@[scoped simp] lemma inner_X_mul : ⟪X b * P, Q⟫_ℂ = ⟪P, pderiv b Q⟫_ℂ ∧ ⟪P, X b * Q⟫_ℂ = ⟪pderiv b P, Q⟫_ℂ := by simp [inner, fockPairing_mul_X, mul_comm (X b), fPC (map _ _), pderiv_map]
def pDeg (j : ℤ) := @restrictSupport ι ℂ _ {d | d.degree ≤ j}
instance [Fintype ι] : Module.Finite ℂ (@pDeg ι j) := finiteDimensional_of_le
 (S₂ := restrictTotalDegree ..) (restrictSupport_mono _ fun _ ↦ toNat_le_toNat)
lemma gMP : P ∈ pDeg j → j + η a ≤ i + η b → glOp η a b P ∈ pDeg i := by intros; simp [glOp]; split_ifs <;>
  simp_all [pDeg] <;> grind [Finsupp.degree_single, Finsupp.sub_add_single_one_cancel]
abbrev pInD j G := (@pDeg ι j ⊓ G)ᗮ ⊓ pDeg j
lemma ezP (h : P ∈ pInD j N) : P ∈ N → P = 0 := by simpa using (h.1 P ⟨h.2, ·⟩)
lemma fLz (ih : ∀ k < j, pDeg k ≤ G) (h : P ∈ pInD j G) (o : ε a ≠ ε b) (s : Q = T.fLap a b P) (g : Q ∈ G → T.oscRows.E b a Q ∈ G) : Q = 0 := by
  simp [-pairSign] at s; have q : Q ∈ pDeg (j - 2) := s ▸ sum_mem fun _ _ ↦ gMP h.2 (by simp_all; lia); rw [← @inner_self_eq_zero ℂ, s, inner_sum, ← s, ← neg_zero, ← h.1 _ ⟨sum_mem _, by
    simpa [oscRows, o, eq_comm, smul_mem_iff, ne_of_apply_ne ε] using g (ih _ (by lia) q)⟩, sum_filter, sum_inner, ← sum_neg_distrib]; congr! 1; split; simp_all [glOp, -s]; rw [h.1]
  all_goals simp <;> grind [gMP, units_natAbs, Units.coe_neg_one, Units.ext_iff, IsConcreteLE.le_iff]
lemma fLzH (W : l.IsKHighest T.oscRows ν P) (H : ∀ a b, ε a ≠ ε b → l.IsKHighest T.oscRows (ν + single a 1 - single b 1) (T.fLap a b P) → T.fLap a b P = 0) : T.IRH P :=
 have C x z a b (h : ε x = ε z) : T.oscRows.E x z (T.fLap a b P) = T.fLap a b
  (T.oscRows.E x z P) + ite (z = a) (T.fLap x b P) 0 - ite (b = x) (T.fLap a z P) 0 := by simp +contextual [oscRows, h, glOp, canonical_commutation, -raiseOp, -lowerOp, -zsmul_eq_mul, apply_ite (raiseOp ..), apply_ite (lowerOp ..), sum_comm (t := univ)]; abel
 Prod.forall'.1 (Finite.int_weight_induction (fun i ↦ l i.2 - l i.1) fun i m o ↦ H _ _ o (by simp_all [add_smul, sub_smul, -fLap, -H]; grind))
lemma mTP (h : ε a = ε b) (S : N ≤ G.comap (T.oscRows.E b a)) : Set.MapsTo (T.oscRows.E a b) (pInD j G) (pInD j N) := fun y k ↦ by use fun z p ↦ .trans (by by_cases a = b <;> simp [oEpS, polR, *, eq_comm, mul_comm]) (k.1 _ ⟨?_, S p.2⟩) <;> simp_all [oscRows, ← cast_smul_eq_zsmul ℂ] <;> grind [sum_mem, smul_mem, gMP, pairSign, add_mem]
end Fischer
end
end
end
section
open Fintype (card)
variable {R C ι} [Fintype R] [Fintype C] [Fintype ι] {ε ε' l l'} {T : @FockDualPair R C ε ε' ι} (hm : IsMatch T l l')
@[local grind .] lemma iuV (x : ℤˣ) : x.1 = 1 ∨ x.1 = -1 := Int.isUnit_iff.1 x.isUnit
open InnerProductSpace ComplexOrder Fischer Int Units FockDualPair
attribute [local simp] sum_eq_zero_iff_of_nonneg IRH IsJointHighest coeff_sum glOp
omit [Fintype ι] in
lemma polCP {P} (hl : l.Injective) (h : T.oscRows.IsCompactPrimitive l P) (hP : T.swap.IRH P) a (s : ℤˣ) : (∀ b, ε a = ε b → s * l b < s * l a → T.polR P a b s = 0) ∧ (T.oscRows.E a a P = (l.lowestKType a : ℂ) • P → let k := s * T.rWt l a; 0 ≤ k → T.polR P a a s = (k : ℂ) • P ∧ ∀ c, T.varSign (a, c) = -s → pderiv (T.varEquiv (a, c)) P = 0) := by
 let u a p := -pderiv (T.varEquiv (a, Prod.fst p)) (pderiv (T.varEquiv (a, p.2)) P); let N a b := ∑ p ∈ .product {c | T.varSign (a, c) = 1} {c | T.varSign (a, c) = -1}, ⟪u a p, u b p⟫_ℂ
 have G s a b (q : ε a = ε b) : ⟪T.polR P b a (-s), T.polR P a b s⟫_ℂ = N a b := by
  fin_cases s <;> [skip; erw [sum_inner]] <;> simp +zetaDelta [-sum_add_distrib, polR, ↓sum_product, q, _root_.pderiv_comm] <;> congr! <;> grind [inner_zero_left, neg_units_ne_self]
 simp +contextual [oEpS] at h; replace hP a := (sum_eq_zero_iff_of_nonneg (s := {b | ε b = ε a}) (f := N a) (by
  unfold polR at *; grind [G 1, G (-1), neg_neg, sum_nonneg, CStarModule.inner_self_nonneg])).1 (sum_comm.trans (sum_eq_zero fun p k ↦ by
  rw [← inner_sum, inner_eq_zero_of_right]; specialize hP p.1 p.2
  cases iuV T.σ <;> simp_all [u, ↓sum_filter, ← _root_.eq_inv_mul_iff_mul_eq]))
 simp +contextual [hP] at G; use by fin_cases s <;> simp <;> grind [inner_self_eq_zero]
 intro w k o; specialize G s a a; have p : T.polR P a a s = T.polR P a a (-s) + (k : ℂ) • P := by fin_cases s <;> simp [k, sub_smul, ← w, oEpS]
 simp (disch := simp [polR] <;> positivity) [p, add_eq_zero_iff_of_nonneg] at G
 simp [*]; simpa [polR] using congr(⟪$(G.1), P⟫_ℂ)
omit [Fintype ι] in
lemma FockDualPair.IsJointHighest.isPreJointHarmonic {Φ ν} : T.IsJointHighest l l' Φ l.lowestKType ν → T.IsPreJointHarmonic l l' Φ := by simp_all [IsPreJointHarmonic, sum_eq_zero]
omit [Fintype ι] in
@[local grind .] lemma HCParam.HasGap.t2LV {h} r (g : l.HasGap h) : 2 * T.rWt l r = l r + ∑ j, ε r * ε j * (l j - l r).sign - (2 * T.γ - (card C - ∑ c, (T.varSign (r, c) : ℤ))) := by push_cast [two_mul_lowestKType, ← add_sub, vacuumWeight, mul_sub, twoRho, Fintype.card_eq_sum_ones, card_filter, ← sum_sub_distrib, mul_sum]; congr <;> simp [Units.ext_iff] <;> grind
include hm
lemma IsMatch.hasLargeGap {A} (h : A ≤ card ι := by simp) : l.HasLargeGap A := hm.1.mono (by grw [gapThreshold, h, ← Fintype.card_congr T.varEquiv]; norm_cast; simp; cases card C <;> lia)
section
omit [Fintype ι]
lemma IsMatch.sCSR (F : R → ℤ) (G : C → ℤ) (e : (∀ r c, T.IsMatchedPair l l' r c → G c ≤ F r) ∧ (∀ r, |T.centredParam l r| < card R - card C → 0 ≤ F r) ∧ ∀ c, |T.swap.centredParam l' c| < card C - card R → G c ≤ 0) : ∑ c, G c ≤ ∑ r, F r := by
 trans ∑ r, ∑ c, ite (T.IsMatchedPair l l' r c) (F r) 0; rw [sum_comm]
 all_goals gcongr; obtain ⟨⟨⟩⟩ := (by first | apply hm.3 ‹_› | apply hm.4 ‹_›) <;> (try rw [sum_eq_single ‹_›]) <;> grind [IsMatch, HasGap, sum_eq_zero]
lemma IsMatch.lVN {r c} (e : T.IsMatchedPair l l' r c) : T.rWt l r = -T.swap.rWt l' c := by have k s := (by simpa [← mul_sum, -pairSign] using hm.sCSR (fun j ↦ s * (T.swap.varSign (c, j) - ε r * ε j * (l j - l r).sign)) (fun d ↦ s * (ε' c * ε' d * (l' d - l' c).sign - T.varSign (r, d))) (by refine ⟨?_, ?_, ?_⟩ <;> grind [pairSign, val_mul, Units.val_neg])); grind [k 1, k (-1), IsMatch, hm.2.t2LV (T := T.swap)]
lemma IsMatch.smLN r (s : ℤˣ) (e : card C - card R < ↑s * T.centredParam l r) : 0 ≤ s * T.rWt l r := by
  have ⟨i, p, g⟩ := hm.1.mono (h' := card R) (mod_cast by cases card R <;> lia); norm_cast at g
  let v j := (s * T.centredParam l j + card R - card C) / 2; let S := Icc 0 (v r); have : #{j | v j ∈ S} ≤ #S := by apply card_le_card_of_injOn v <;> intro <;> grind
  specialize p r; grind [IsMatch, card_Icc, by simpa [← mul_sum, sum_ite, -pairSign] using hm.sCSR (fun j ↦ s * (ε r * ε j * (l j - l r).sign) + ite (v j ∈ S) 2 0 - 1) (s * T.varSign ⟨r, ·⟩ - 1) (by
      simp_all [Units.ext_iff]; grind)]
end
omit [Fintype ι] in
lemma IsMatch.unique {P Q} (hP : T.IsPreJointHarmonic l l' P) (hQ : T.IsPreJointHarmonic l l' Q) : ∃ c : ℂ, P = c • Q := by
  let f (x : ι → ℂ) := bind₁ (X + (.C <| x ·))
  let M := T.IsMatchedPair l l'; let x i : ℂ := ite (M.uncurry (T.varEquiv.symm i)) 1 0; have hf P i : f x (pderiv i P) = pderiv i (f x P) := by
    induction P using induction_on <;> simp_all [f, apply_ite]
  have N F : T.IsPreJointHarmonic l l' F → (f x F).coeff 0 ≠ 0 := fun ⟨o, L', D, ⟨W, L⟩, D'⟩ h ↦ by
    have ⟨n, p, z⟩ := (f x F).support.exists_min_image (·.degree) (support_nonempty.2 fun k ↦ by
      simpa [f, bind₁_bind₁, o] using congr(f (-x) $k))
    have ⟨(r, c), k⟩ := (reindex_equiv T.varEquiv).2.1.1 (n.ne_iff.1 (by grind : n ≠ 0)); obtain ⟨t, rfl⟩ := le_iff_exists_add'.1 (n.single_le_iff.2 k.pos); have K {κ S G} {a b : κ → ι} j (E : ∑ k ∈ S, X (a k) * pderiv (b k) F = G)
        (k' : (f x G).coeff t = 0 := by simp <;> grind [Finsupp.degree_single])
        (h : j ∈ S ∧ ∀ d, x (a d) ≠ 0 ↔ d = j) : b j ≠ T.varEquiv (r, c) := by
      simp [-sum_add_distrib, f, ← E, add_mul] at *; rw [sum_eq_single j] at k' <;> grind
        [coeff_pderiv, Finsupp.degree_single, t.sub_add_single_one_cancel, Nat.cast_add_one_ne_zero]
    let s := T.varSign (r, c); have V s := (polCP hm.1.1 L D' r s).2
      (W r) ∘ hm.smLN r s
    have : _ ∧ _ ∧ _ ∧ _ := ⟨fun d ↦ (K r <| (polCP hm.2.1 L' (by rwa [sw2]) d
      (-s)).1 c · ·), fun a ↦ (K c <| (polCP hm.1.1 L D' a s).1 r · ·), (K c <| V s · |>.1), fun g ↦ congr((f x $((V (-s) g).2 c (by simp [s]))).coeff t)⟩
    simp [hf, mem_support_iff.1 p, x] at this; clear * - this hm; cases hm.3 r <;> grind [pairSign, hm.4 c, val_mul, Units.ext, hm.1.1, hm.2.1]
  use (f x P).coeff 0 / (f x Q).coeff 0, by_contra (N _ ⟨sub_ne_zero.2 ·, by
    simp_all [IsPreJointHarmonic, smul_sub, smul_comm (_ / _), -fLap]⟩ (by simp [*]))
end
section
open Matrix Units Function Fischer
variable {L} [Fintype L] {I : L → Type} [∀ t, Fintype (I t)] {R C} [Fintype R] [Fintype C] {ε ε' ι} [Fintype ι] (T : @FockDualPair R C ε ε' ι) (l ν : HCParam ε) {l' ν'} (ρ κ : ∀ t, I t → _)
omit [Fintype R] in
lemma dPD (D : Derivation ℂ (MvPolynomial R ℂ) _) (N M : ∀ t, Matrix (I t) _ _) (h : ∀ t i k, D (M t k i) = ∑ j, N t i j • M t k j) : D (∏ t, det (M t)) = (∑ t, ∑ i, N t i i) * ∏ t, det (M t) := by
 have {t} : D (M t).det = ∑ i, N t i i • (M t).det := by
  have {s f} : D (s.prod f) = ∑ i ∈ s, s.prod (update f (i : I t) (D (f i))) := by
   induction s using cons_induction <;> simp_all [mul_sum, prod_update_of_notMem]
   grind [sum_congr]
  simp_all [det_apply', updateCol, ↓← det_updateCol_sum, update_apply, mul_sum, @sum_comm (I t)]
 induction @univ L _ using cons_induction <;> simp_all [← sum_mul]; ring
structure IsLayering where
 injective t : Injective (ρ t)
 sign_eq t u i j k m : ρ t i = ρ u j → ε' (κ t k) = ε' (κ u m)
 closed t i r : ε r = ε (ρ t i) → 0 < T.varSign (ρ t i, κ t i) * (l r - l (ρ t i)) → ∃ j, ρ t j = r
 weight_eq r : ν r = T.vacuumWeight (ε r) + ∑ t, ∑ i with ρ t i = r, (T.varSign (r, κ t i)).1
attribute [local grind] pairSign IsLayering iuV IsMatch HasGap sum_eq_zero val_mul Units.val_neg
variable {T l ν ρ κ} (H : IsLayering T l ν ρ κ) (hm : IsMatch T l l')
include H
omit [Fintype ι] in
lemma IsLayering.iKH {P} (hP : P = ∏ t, det (of fun i j ↦ X (T.varEquiv (ρ t i, κ t j)))ᵀ) : l.IsKHighest T.oscRows ν P ∧ T.swap.IsHarmonic P := by
  simp +contextual [-pairSign, ← C_mul', oEpS, polR, (by simpa [-sum_boole, -pairSign] using (fun a b (s : ℤˣ) (_ : a = b ∨ ε a = ε b ∧ s * l b < s * l a) ↦ hP ▸ dPD (.mk' (∑ c with T.varSign (b, c) = s, @X ℂ _ _ (T.varEquiv (a, c)) • (pderiv (T.varEquiv (b, c))).1) (by simp [mul_sum, ← sum_add_distrib]; grind))
    (fun t i j ↦ ite (ρ t i = b ∧ ρ t j = a ∧ T.varSign (b, κ t i) = s) 1 0) _ (by obtain ⟨_, rfl⟩ | _ := em <| ∃ j, ρ · j = a <;> simp [(H.1 _).eq_iff] <;>
    grind) :)), H.4, ← sub_mul, ← add_mul, ← sum_sub_distrib, -sum_boole, add_comm, sum_filter]
  use ⟨fun _ ↦ .inl (by congr!; split_ifs <;> simp_all), by grind⟩
  grind [_root_.pderiv_comm, units_ne_neg_self (R := ℤ), show ∀ x, (∀ t i j, (ρ t i, κ t j) ≠ x) → pderiv (T.varEquiv x) P = 0 by
    simp_all [dPD _ 0]]
omit [Fintype ι] in
lemma IsLayering.joint_highest_prod_det {ν'} (H' : IsLayering T.swap l' ν' κ ρ) {P} (hP : P = ∏ t, det (of fun i j ↦ X (T.varEquiv (ρ t i, κ t j)))) : T.IsJointHighest l l' P ν ν' := ⟨by simpa [*, prod_eq_zero_iff, det_apply] using (fun t ↦ (rename_injective _
  (T.varEquiv.injective.comp ((H.1 t).prodMap (H'.1 t)))).ne (det_mvPolynomialX_ne_zero _ ℂ)), and_assoc.1 ⟨H'.iKH hP, H.iKH (by simpa)⟩⟩
omit H
include hm
lemma IsMatch.iLay (s : Equiv.Perm _) {w} (hw : w = (fun (r, c) ↦ ite (T.IsMatchedPair l l' r c) (T.rWt l r).natAbs 0) ∘ T.varEquiv.symm) : IsLayering T l l.lowestKType (fun (t : Fin (univ.sup w) × _) (x : {x // t.1 < w x ∧ s ((T.varEquiv.symm x).map ε ε') = t.2}) ↦ (T.varEquiv.symm x).1) fun _ x ↦ (T.varEquiv.symm x).2 := by
 have := hm.1.isKDominant_lowestKType; simp_all [IsKDominant]; have {r} : T.rWt l r ≠ 0 → ∃ c, T.IsMatchedPair l l' r c ∧ T.varSign (r, c) = (T.rWt l r).sign := by grind [by simpa using And.intro (hm.smLN r 1) (hm.smLN r (-1))]
 constructor; rotate_right; intro r
 rw [sum_sigma', sum_of_injOn (·.1.1.1), sum_const (T.rWt l r).sign, card_range (T.rWt l r).natAbs]
 all_goals simp [*, reindex_equiv T.varEquiv, Injective, Set.InjOn, Set.MapsTo, Fin.exists_iff, Sigma.forall, Sigma.subtype_ext_iff]; grind [Units.ext, s.injective]
lemma IsMatch.exists_isJointHarmonic : ∃ Φ, IsJointHarmonic T l l' Φ := ⟨_, hm, (hm.iLay 1 rfl).joint_highest_prod_det (hm.swap.iLay (.prodComm ..) (by grind [lVN])) rfl⟩
end
